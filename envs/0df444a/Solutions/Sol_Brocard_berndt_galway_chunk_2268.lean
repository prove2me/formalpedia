-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2268
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:11:33.887222+00:00
-- url     : https://prove2.me/submissions/fa955cbe-d9f0-4bbd-b1bd-7a6d3e31f2b4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 407733812 ≤ n < 407913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 407735062 1250 407733812 407733827
    0x1103042904080d09031101020a0b190204050a030f0309060f050702100306080f0106050a0f0302130f0228020f0303060607060b0a0305030408160e15090421261501 71
    0x50203410940c0c20580c903684640e02c0e04075031007281c201082e840d4100380144082c81c0c03d14803910400744014942c528031070390b03400c2e11054064a02049040140c5c046c80b404002178040d280501805030030005015540d003048612800d1503070082e4042144c0ca08003043c82403060031050081007164036123a10300a402d50920807450a20300b030b10003c0640d610b078081201e80041c4500300c0540c2c2d6460001c9000b9081000308010364845a00600030b031002d521040005894659200105604445000807100819600c0001920480445400400354078440e8142d031121090102c0140ca40790f801ca440000008184954a10090ba86507030311100030702200b0005510340d0800043c8180241104114903030320754642c1c0c43c540144d04500c140b42c1003208804220480b00115100824031002a4045800c0c00700c003058050074800c1366940105042000981070000d5103149000180d41c10500000e0551141d0300108840b0b107001c28a82c06034035007009840c0c0006e8884055018480440346141c1303800340d410064500d01d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 407736312 1250 407735062 407735129
    0x100f090f0f03152a0201061410051b1e0c04050601050d18020306011508220602090d0c1e0b03040b060f01020a150f06090e0601030206210405030a110304 67
    0x40e0702c41c541d4440405140b04168160000038640d59608904c82e80080d00b507482c0398000c0c600c4100804000c050030b83c2c030595842014405810706580c3c80f04c0b00c0031460807208440c0c0030060f1038410b13030002200d00e0182c02d04000c0310801800541c0e01c00d0910404002c19a0b500b41c0b509030021340d05003c0b00e11001d14030360140424001c0c4042000103010660b020900740b1100341d205000120f0800160b458154000812179071050075101c0002d0100c000702c421540801d4854406040b590f408141141c40e621890503d210041c2c004100c1420590b9403250058142010000c3d54408194100e00040314001101502d020f42c1d0301503400400390b5103000521101d650911111411403180b5030380c400202d100c3d8012200742913000c1d800401c000078110300740010b80d409548004000e031310b04a0310020358407011842c2c6040d29030403103900355500710451081c0410b140003244048031820041c00d010030050b0000081454018948558400c0e0858a140985a0240323220704180503615651505c0700a00000308240203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 407737562 1250 407736312 407736353
    0x7030203180105010308090120070e0c1606060503010c02010b0a0b0f070f03080411090c0712230403060b19030f020102100509012310060e0d02100f090f0f03 69
    0x16109030701c0640703094400c2a4020384492000040c0c02081d941e12a040280142184904040c3c250b00113603242e0b035402c1d00c1e11504e91540074403004540c04000c20002c13201d0781a90150b40e01c0c2c4240e01414403c0040c03c4074441c0c54800d41ca0059203e25803801809804042403005114006c0300749000f00445040d80001480310383c0c000f04114100016003031001e000b00b0390703003c0da5864403945480c0c58a1900180315058040c801c6200d41c0401c51011031500c121400c0c0c660002460540ba000404195503002e103014241c4200000400d2006c06e103000741c005081100c0c01034a080c030502000c035060145c92580d440d550802054015800e001059448229640085c03043c8103c419925109002004846059078180032607516072030302107a0004030304c0e09000c3c441c2d00404111f00d00d0404503011a0002103903c1010144684000c003112127641d0220480080ca802802c8011012003441c0020724003040503003140007103601a180030070300640ca0388400b420b03503c07000e107000551811511400340c54290103024110 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 407738812 1250 407737562 407737591
    0x602040308030705120603011b050d1e0906140624160f050f1c2d03050115170a020f070f0501021b01020315060912010c2f0607030203 59
    0x1c0840d4000e51080700d140e6107064644040a1151003091805048144283e051101a0340700d20b01075403404006d1401414910703614000140210081d02100701e003100030403028007004c00d42d46100d40160600c0d48c41850100700308000110701030055030003600c030b080e000300d50008902e00244249801400e80302c1d01c0000c1c030341444410313009201c040c3d004100442c1d011220b4400402044002c104c4403000f05650300c00307040303404034503c41c0d070f0b003481d64814210003045420007800b0302000300c00304002c90f0701200024800130702c1e500c0103019000c1c20003807060715030603070510341050042d602c80c4600185085165403004420b07182d00c0b08040c042c1d02300070071403030803284208030702c0b0002108040040403613413060b000980c81d450040c0341176051401e000e882c407038280d0040081204d4016800c0e202c88100c0811a400d80d1101001d00106491030456241680598a40500c3ca0941a00601c03c1140000d8860381034105051181c1d8510310364010712403d400381d41c0800089024075001303030060b590240c00c8040c1c003813 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 407740062 1250 407738812 407738819
    0xd0f050c0a1d06270a0212060d0f170705031314060301030c0603021b030c07060210090b0609040302030f04090b0a0603020a201c080109050603010207081c091a270a030c060204 77
    0x301c80e5020f81c0d100101c5c55001494102181a0041240d80400202c429070041c42d500c0e1903401030900740d070344014004801803011a54030348005098800082d000030440ea02c803007054011031000c0c445401040709041e041b1084c2c2401c0c0c40c100044034181c03a800300101240516004060f00650000c414103615000c0b08801440040c108002404000b41c0f24401007200034502080641404550308900c4101e904000304034003c50107500146030003a0042d04c00d00754a1303649040403400e5004548007458411800580090042c0c0c01350400f14414a0868801248954030b00c003d408901c1048100400708a5201080703803e502850b41e60380545891605442c02c801e0100440800c401d09145002c002c120914014015491240b01c0d0650160301a07008501e0014161074030f65450007030382e6200c2c02c0100202101e401c1503815400501c0700e140c0c008040500040c4803005660600320480e500b0000c103c004205106c543c080e200400d01c05030654000e0144545180c400b01c511552039001034520b15000c01000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 407741312 1250 407740062 407740129
    0xb06150f0315060d140c041a0313021c1a040b0403031e0509031b0102090108190608070306021b010902090c0904020f0310080d0302030108030a0c020d0f050c0a1d06 72
    0x1003408102c0e003a0005002d180308628482c850345c020740300d0701c02c1d9001030200380101000b110100322100032a455440e140d0342c550074055040b060000b0000d422905128442189460180b400e082e6144240c003841645402305100001d0300b0300458024024819050205011900981c4616015403054860180d45410040d030f44003650340607120030714a5440007419080035584245404000510400254905006c000000b08440700203080c100341c0f40c0d45c941c4800d95100240d1710440081402d9401d40b00d00603620300300030000f9040100702c2c0f03511020340041c80592030740611402c50f2199000303000312005d44030b00400143c0c0b030300300751005500641d0030403088000c0550b220186204105030710f0b0140b0418107000d111810540800300002c1807500510060210301300100c10b4a40752001d5252926046540c0d00000380b511410280180c40300851044100c1807000106061483c2941a503401842680e204074122202850151a5111460070b10129500d45044901101c1c801400c4032103810054048801 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 407742562 1250 407741312 407741317
    0x302070b0c090a060203031b0c0f01060f0e0a0506150c010b120a1106190f120504060501140303040f050415260115080604141002070c030b06150f031506 67
    0x710101240c04100c0b44100e01e006034600003e007845102550450904403401700308411200000450303000c0110b00344110840821241e02c804240381c1c0203200c1680d5990560800c054540941c102c008019400aa140000740c0981c40c081c2402030700d902c103120252400e19640b03800c130b1142000e06540b103903c248801c2d50344850352242a200344016040c03280300e03450b201031082005103120340524030038010141c084200d0b00032103210421505203500000c100600c21201c110718010001c076882d107008140000d1203000c1d0f02803410307546550a01c40b1804100030405613a030186100b15107200103400c4080c003d50030301d604002910b061491041c0c0720140c441c0802058050869031651800c01c89403592180c080c03090041c0000d003104200d204002504140f034507500c03907000600282c0100013038848840c049404000d40e4410210b40c100454640d0054505605101c0003480107442c01207004011888516003200c5282c0d4070b8518120f041d18003000542d0840c1c5035000141600034401400c1da045401d510307141300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 407743812 1250 407742562 407742571
    0x9050a0b03160c080a0e0a0b0f0901030506010302090a050d0809030111031506071a0709030b0916080303011401080c091507031101110915090613291204030302070b 72
    0x54940302c0c03600b428900394914945681d041000055110000480c6407001280c00300142480c0c602144e02c080008140c0d5040e842c2c2c44500d0700b150000310040789480d600050048603a090340e043c803070390700c6800044081c0d008a440141e48159044000c00562034038a2a0501c0c01c2d200d420064200700703515001a00f143c0142d40492104140002000307003141100c600200d402c40c084070441e0070135089841e442442c08024044040e001c44400202d0001800303070b1200b01c0190343c440c100c0626072400c0d031102612960020311401b510400301c0702c0440d0015010054a060b07407070842d40807041c9070903080110790b80ba40207414203031552003c0000c080c580d128030310002c40c80a21190321699401c007914000702800403008403558ac80e49000d000c804565860412584442c1d000c86010f050104c81c0011103666104110f021640204001030040c00310020881d660300302c0c0c110491034151010030025a8410302807140300601840c0082200b03031006c0f82c0000d51141c2180c02440c3c01424183d09a690140300041500e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 407745062 1250 407743812 407743829
    0x6020d0509060f01030b070309081612140403110d1406070c03111b0105030613050f010806161e030207060513050c01020a110d060e100e0601060e10030b0109050a 71
    0x1020041c001038100440c5402c034014266090803503140d07071202044030002a06190400da1034900600c24443d101041d5461003e450350f1019402d001460f21403100d001c160710b0400440d58220940b100e4080b03d0301039034100c9030001e40240a2203600f4080001000e40824201c0b0304e0740325070700b0001c000b02040140d030b441600240c6500c2d0010b40f407410041c1440c0017003960283c29900500050b480710754800d40c0302031540703428203040c1c0c0c4940b244c0e00021807074422070301b11203445071401e01013000e08414544e11038101c1d084001a105240c40710703d541c240504d0b81c0b80d02d840c04a0f0355407400d2047e40801d13088013480a4000e107001030410b0000d55903001175446c05e45a484403910380e002c3c6202404400e0100c3c2c80c60755802d000a24010f040c076035403052001da1082420344580840b00048003401a250001601c2030b00301029a00840146a441b000408800c1100346852050070004285613004103007034a9060801480301c085a4000300d070880140200003070150402031491030000b5991101d441040107880b485 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 407746312 1250 407745062 407745071
    0x10e040b1f0206070e06040501020a0303050a0b0301020703080a0c080907140102100501081b040203220f02030f06040302010c080f0406020307020f030406120e06010609180e0a08040815010501020709020d0906020d 93
    0x241ca004245d014803035049071141404205c20050ba0b0b0b00069410400d961506000c1915620a00c008005100c000080390301035000007507034800c0690203400305114a1801c0010040710044180459030721204443d03811807507110780010f0140004c503503204c0501380414411103440e14014080601610400e034401d5406a0200e0440360a2400790a11018034600944085085180c00c114a40c02d050401084a200422802c0350009100c5061170000880744c000d02185e40080380e00740c030b0a9550b81e003210154015460161001026880360004e28001c47e142007103001240c071942c60f106c00079131001d4080415071040000a58103002c00340043c10003841c03a0b4681d1910301c0900001d11007a903504c0da54441a0740c2001c40107101c1d5136007005020342650b1400320300f000d01d8650303207003030b10300a01d44c8480720075480c400c5103004401c200d80800104140c81c0240141c0e20342031082200c191400c0070a014080c00341e0002c02080c000070f841d40e4080c081c400d081030320103d20f0f020283c86d90012648100030402d5401d07141c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 407747562 1250 407746312 407746321
    0x3020d05100617101a040b0102100e1608010203250c0b0c09100305010e0a0b190e061c030e130b061605010e0304031e0c05060d0b090c09010e040b1f0206 67
    0x11320a00030316070352500c1e040c40719a1115450a131011903401d01d540c401c69035000c012540d03034803c014000c020320504004005000300805050769920303040c0030b94a151003983d54045500d10040c02602c2c0503c0007555aa0140e8030942c0c820054584514076030001c0020403006007020488880350240034803043c0c1000c0d0b036100611401d0000c01c1e0199161642070504080040083ca0002041d43c0d40c0851081d01c00a41c0b03030070080004a00200f8801030400c0d41c14040d80c049002030030110b0f054000c4000b1034602c4c07880c40614845900c10040300b81c1c050046412aa040c0c812410440303015030108140c443c000820070043c50003d070300b41d003000054540007044550204c0400c8024410380c40c03600840d00040d801c00c1c3c41d40d907a1071150007444196240c0c5210911100d402c202c00021008050140200f045885032128040780d00117211158503d4428a00c1c1d402242400410400315000c40b10f06940ea941d422a0072008c4c0b002a11100344041c0d00000482e05401c10319066034880380c070407aa1640a851386003403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 407748812 1250 407747562 407747609
    0x70b18030d03051503070602071206021306091409060f0d020a080a03080a060e101e05120d030c180b091c0812010b130612110c030c100e0703020d051006 67
    0xc4c60082940030340d020940911440e5000241da00840b01d001140003035483c1d403440d00d20080c0c080c008981c5104410548003241c90b580040c41c1109840c0310500c241510100402001a10380c0c060f6101c54025245914000d19030803c40c1303903010054000b40030010b0050b0b907910780904e000c8510400740c002403220400c2c080403001c24041d080051446205070815400d203050502c0f60f07500c143c0300709180714103000d04100400000880180007020b00901004c920300e81004180d890f4116448180000317441c1482c10303415107000e448110300840040c07903190760560811300e40c40760682c0000441980f00f84503285a0000c00d0f4410740c2030b00f1180c030031250b8644816100c1101c810703c09068000b007281684c28043c04c68180c11801c1d4000c00c03244145002c1c0300f804000080700307000b000340d02184028038400061009001a00200414600928800700e4030009140099039044800001c2010b032581c21810080001d8605100510f100a004030280c940d400c011200d0081200d80942c0400e1001010325015100d030f11 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 407750062 1250 407748812 407748841
    0x90108010207030e03150c16021537030902011407030e090a05060f09070c0f1b060e180628060e06030601020d11071e0e06030f070b18030d0305 63
    0x3407082d0001c01540e000d1b00300c4d41da5a12002040c3c280019008600c0025508118007803482258001d0400c210000c4a01104030140e8072035070b50803202414070140401c40c108010140078911201d00400522241c0c490b008501900d44e4480580c10000f41941600c6986250801403141c148603444c1c1d40030342c2c40c41400b0b00c0100794000f000d81006515100402400b511a84041c1c1083e0400700e40554582d900c1c41c6041d55190500e1101070b22541c0c4c4000b1060401048048108000f01083c070000d411036a10303541100c2e10412a89205d0300904030050804c400d00c6a9041c042d000000202403105c80d022440114101c80411841084042c2281c1010091180c0204100e03441440c02d490651461401100107551200a105080200041d440900a03020000d001e040050002d0040140349445034604038a91003880b4060007102c0304002e40860901e160000b031020300c01d003000c406454154078000b07010720103400c01904042e02803110743c0011140d030340501401541580c0c0e43c800140c1410041400b83d101e4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 407751312 1250 407750062 407750087
    0x200609160f08070504200d05040606211202011b0f030501090504020f0906010915021c080f1501030908041701060614091203190c0302060a140a02070c030209010801020703 75
    0x1d0100660612041201241e40e000b81d98055802281000500300c2c403001c0b400100346005240500403900c3d000b2603885030080780c020350198a003840b10035150400224070345180c7c2080380e0443d004508040004a6401356006101e560b4000040c24522149520211210400c0044001040f002840140540503c1010b015000c80d080410451170103a021407602503c1c801c40d24401c002600000c2c40681c45502760381c01a20100d803112050300b5420380003035540c02c14040f01d600301c9001c072000c0c0d10409214400951280b03410a812108035140c00001c030b040c1e400300019241c101510f840c6100e0105400310010001000780c221201d0f603004004003607900f110a240c0200c420403210302801c0e81c1d10b00100050300c8080008440403a803403400e11610900e54400c3c040380c500900d02c401c03480440c107500103a41140c0c1c603021303800342c50460f80e43c50070010844000442c5880e014004c400880c00844c0c00d640a420700c075110b402100c2c2000d1301c903000520700c0c8000760302c840007581d00003540c3c1080650100b13010114 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 407752562 1250 407751312 407751329
    0x1e1006170d020309060d09110613050a0e071e031104030b04050c0f060d020a0e120109051002070803010e04050a02031002090f15030106051c020c0a21020d20060916 72
    0x101500c10300010b129205111b9009403550300c1d0112039090000b0070350b1501100390003d040b0f6544608841e20302c00a00100e04c1458400c1e80c0b500000185100c49045144c8145902d90362a0b0305132140c02e08651940b0000d132034000406984248440e100c1cdc0900008102450080200944a1500d0700d006441c1c0b5011664a601500c2c00108410342a16104141c0312078401c40e01001d40c49000c0400100c0d81072040e40c0c05141d0000e03045401044041043d440382408500900070381d011201004a8a0142d109100008120420030001041070884841c00c240d00180300340203840b01c0c0c1c9415000203251104042210080e998000390004403481c01802d03039125520700f41c2e818a0b8103a0b8a803000c400318001441903c061040000d0382d04c45c040c4075003070300031000c0320b28400c11502c1e50201c1964030b90302c19400f2403c0352060102c02d444842210002c0c407180c020034450780104421a400d41e022034419002010340c09816a2158004654640c00d2000d148140020f80003000c2c4554080e6003455505940d5005010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 407753812 1250 407752562 407752567
    0x2203150f2d0b04050c0403030f050304170a03021b060114010e01022508030a0207051804050c0d050f010c030e06070f0f05030c09060c01090303050115021e1006170d0203 74
    0x85107540c0200704110304280c950001d11000200091001d000a021010360080c9041d080243d84052840034001340c0380a903a881804240c42c0100b40c40d5444140c60190101084100014000e1401c400800c6c0c0b4000034030b005410501103212320415404401c041d00e1030f50300040018000c0000450603842110001d10340307c1c0b108043c080000c0e4851058440a100d000300600d006907042c403040c00100e00901d00c0b40100c03951000385140c0251649400d00400e445501d030066031802c0c2c408030f05003843c010741c1c104010300401242c0380b0800070740d401c2030082200c0a020b04900304120420a02c1203400000f425100401c2c0105041005400e000c4014104420310983c130100074055070b40540c01c584140c5c198100140c2e651542c1c64042101e0240808440c0c0c01280041d0248a18606410280480c0d1290b01c0034081e698a80300400180858101c2840040e4810701c405050200c0f01040e00d00300c0810081965400c1c25241e190f842038840640101a00941a007104441e1010400140c3d144040f540301a50 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 407755062 1250 407753812 407753831
    0xe090f0102160303020c0708030a09170601031101050a2007090516020a02010c0804090603061409010c020c060d06180b01170601020604020d0201050d05101e0e0601052203150f 77
    0x200d03070500b4040c1c080c08155002c60180e02c6880204100d602405074030b0100c945070740207008000d0404089000300c082000d800c4038100c4e040d1100080d0b041c1642d900115000b10078007d0001165103030400e0228004114452114070f06911090071412981d200400242403403038101880e03003082da90050800038414001600302c10b015035000c2003802080d80d091820100102030741c2030078031103405640c0000100f249808070000c00c00c50640c2c4154030005408904062a030340d1266010700700d03041e4141e81405a00104e00500c0549030a20040a01904214000460544540d040c0740240c0050380d2041384079948070000d503050f6801c142c0050080340b400e01c00d50000e181105c0000d40f06c0901910080c0a050500079560840e80200181d0f4036070140c404081006281051099010000030300c40c0d1107121040d00c0c08519a06c1e280c80c80740c016504000c28180064640d00011102e65100314010b44100100b4140c0c94030702140e201c0c140d401140908080400619a4010813017155200e031038000e8100d10307019142 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 407756312 1250 407755062 407755087
    0x106030e070b25260306011b020114090a120501020a020705190e0a0b06120723030c0702030a020d0602041a0414040c020f15010e10120807060908040e090f0102 70
    0x1e076075401d1440c4902c107148a49007103400207030403401050f02100c40501071000190b22001440c4120f400b45e0394101d003140400c0d40141c0040e4010700290002f0903000011100b02800002040341e0381d0090082a20950340b0120000f027110080400c843d070740d40015030300380307030030745c100000f401030002140c01d42e00d01c440341e024000740b40301c0610400c1120351b03215000490440450340302110408001d0314440da907a01c02407110741030000890301200402c03440e001240b408401282c003d5042d01042030840d10759110705440b000309410a1000700d9042c482c202030070006843c3c03c80a00c0c845403156401503225814801c0c4107155094a0004207200403040c8810400c0c8030b04e142d4441c074800c04c1079070009122550310404030300380702d00c000540030703541700300c0880892004031003020078101c0f03020b902d00340c4450312404004000410144070b00f562803900b00b5500700101d040d5034020724500d88580c000040c50841c55841d44c1954000f60700c115a588034000810080200600140000806801c003c510780341c00a60070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 407757562 1250 407756312 407756347
    0x12030219411b010b0111070e0702150c0d050c030603191707050601060e03031207050a0e041e110403020108042405070c0303150302030d0c02060c1b0117100b03070302120106030e070b 80
    0x50704000c580b00c40100d27070028003d101032065000c0d01515081c243c605180b45103000ea012842c80044546444000340b0000d0f0018181c9000d444010050251084280540300302c01c04028400da4a00c20302d543c0f0b209500c0818401410b11901c900301400c0958034111010380b4200082441601a80041103070b508022103243c3c40d170b5030000c0c00e42062900c1d0440800d04403482c0c11103c043c0d075001480d1407000d51800001501b56000c6081c5404180b10350f8402204200980c01184402404900018042400101107000740b00c03d80c1400c0c0045200c404d1b004803044c0540d50261070080104001d00202010315602d4050a003208018900e072008141ca5030b0301091741e40c044402c3c0b002c104100320301804c007156201c10031103010150280848405003640d402c0201a5440441e2003404510703020400d01006282038442ca205042c40540404800d242c4003000c08181d00042540c010540c0c00c10a002c007482d00003400b50701911640da00001e800030003068051400d0015000843da84106112030010040d00025 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 407758812 1250 407757562 407757569
    0x708030d0e01021c050a0f020c0a1e050106120b07020a150b010e040213050424030314121f210212010912030219411b010b011107 57
    0x1400110300d007100312414024011648076100305904c0d6200c50480b00260341080d4012064103204020b2180401075200880c41001020140ca402100341d05002c02c1405c8840b0305143c0407801400d900c5601541d54508485140d000802d900d14100c400c0d074280110030640907840300c11170000f4050030301e49866410108018404004501d40c8440050720aa446541180700004010740295110b5503c0c0151103807400180c0039481c000c910380006011103850f20654115043c01d0102811030781415610201c6480b8a0410215052101007010000078544be90041e8840c3e107601d05030f8010070100a071646241e0225500218000e01c0400c04107000c000b81021000042e90704403100d4601c401c400f03114a01400b05144007605034000c03038231000c09003600f40c2c00404c445247c90400829110400c00241c0303008071980030001c205e010340d280c03488200ba108178000b02d030045500c1041c00000215480404107611070740141c2e01003000c1211240104d0000d0144070710004090900c59900c40c3c0001109985510303520 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 407760062 1250 407758812 407758837
    0x120f0215041404230c270913030f05090f100c03080702013309021603020d0f0c020904050a0227090706080f0a1b0c0302160b04140a0504050901060e0702070803 70
    0x8045001c0b20886400c03910381d100014413450719192140c0320f16003600100886c0c5030103050341d5800100d0f9800d158007802c000c6036040d115815042c002007000c5440b5001b810200b504084040b48844c1c0c85e9541609058840b01c1c15030f034101400c901ca03c2c004112030703005004402035a050a070303c80d29600e19001c5511501e0b040001c6814a0040d401e00480440b20650002c20b006100017880310002054511104810303019800300c650f0b00245800898403141a0310380040050389440800c00180340c8800d046801a0040313003254003100042c0c000a548405c074030b590740d401000310200420318240d48100964000404030107040464036001c0060603c4400603c8540107000700c0c4002003801c2c107154415141690b8040b00010b000c51040d0001d450012100300a03409845104800c050650700503242005495400340030505040c83d00c80a08450061860b500c0e03440103104a01023555211445040c2c42001a9800404c071617190542d0007149800242c5001d04640107030805008400000085800340c46018 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 407761312 1250 407760062 407760131
    0x2c0105030c060d113106120207030e10080604140f04030507020303040e0c0304020109090e070315020919090506060a0206060d0201090b2206030b0a120f0215041404 72
    0x83c000c1d40c0061010b40581c080e02840480c44464800c0c1c0a0b81c50701c01c5409900c54030f5241110103980000c021054880c03600040c0310700001d1840701d081600035108580c03003420111074050024001801d00794094000a0000c1d1080040200d02c0c5028040d03020071030300c10104074613603080c400c074990000c9070010300140500c6000a5100d04544080080350000d00d80039040a8035030030580101744a5510544050340066558034000c1008040c80c030407642072040e4440101006480c5607038034000000c2d4843c00051880d8284640344241e190208003040076807031a0a800d003c5d904140b070010848002500090042d0030a100700e5913429000110940c0102c400c0720b1042000f040c80c0b00498010040c0d8121810828000c90b92440c5451400e0b9050003051001030100e1065840306070440c100c80b5102c003034a0380210300d85004c000c07441c04400c009105a00880801003c00440d4020401000e10303140c10048079000018100400e0401404e00c0d0b01000c0d0445061206280294941d094046105400000c150300d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 407762562 1250 407761312 407761327
    0x50d1a041b03050c040506010801050f011404150201051b0c0a0602030a1b030507110c1309080c06181b0d1407031b050306011401020a140a05072c0105030c06 69
    0x440e09007110720041076007118422a200d1500783d0712031454190781c0d0300590030403011420715802085401d040e541e020304a1044001c040004440329110140300d09086c00381044081251700b25516400c1107032419400109031424424a075207100c12062600300003501d01404002004003010611175a202d400c0716015803251a62500000200240c040e1041c1c1115400c5001441c1c5c0d825030002e83c8190380944450f03905161907804562649146008150b006010b200240301d011300550241c0c0c40d460252210506001250882c64030300081503d21503031003850200100e0f040c10041000c07650f000d101404c81003145d00c2c880c0105881352440d000082c4180218410808042000c0000358021500501e50800a421034401091924283d004090207802284004111249030202071815010184e0042c0603001a9448050801c00052500d26180c060b1803000804103604010130409414030080b0400d075585a41c08020120102807125170301c001032240100720b1940c0c0810965000041650065980e001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 407763812 1250 407762562 407762573
    0xf15081b04030303091103010605100c0528020312090a050d152405030604080d02130b04030302030316020a050d0503060114130602010e191209051216050d1a04 70
    0x4108040e00100c25010800005169040e00b1401140e03000c1c03404004200c88203401c2c1400d9920f1402001e420a40d58140300500314403c3d000c00300039a010343d00b5580100041200c2d41b42540c018602d04800b07850b01c84007031056203000d21079028000a8250395520300450540030903501c441e28400c852113802ca125948003032181c00450785031006150441000b201e21440ca0140340b291030b000032001d171960500008074550400041d920b0256800a0310305051803105070030741029511804074030320740d4200c603640060410310b00d40c003900140d0710a801075038a1b840c0541f0440d200446030000b8074210b61215003004040350022528081101c03003483c2c03041d0f0b203580c4c0d040140c0d0f131458403021703904100f80300180e059400b00718000f0000a45a040e07000b404100c2031280815a140a5119880318102c03000d4007503000564008050705010465040c100b80070759035140000d003201801ca81038102600303c5101184042141041000900401c41d9500801c0f4a2900c0d055001c04d02440d0180c484402500401d00344007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 407765062 1250 407763812 407763841
    0x907080411011b080d0f0f0b01080408031008030c0c03010b040603080904090302161409090c06182403072a1103012c0d0314060405060f09130209010f1508 68
    0x1904008240c2e555082c1504100c01400e6002c0e0746c192141c070b040c1c14121401d032030b8040e035048035030142c0d140d041d16201d03500c40703002070b0784041c181c003074942c4c903103074000508507424005030504e1805840500030411400c002d050035038a030300d149a4440c1d07180c14401d1000074401810794003014015600000c4004d22450141c0c50b050790582529103591050f8000980c0b03900d085004018184196415800f5071600f900c0c541d40c41200320030190b4011000e000c110540c604034076603030b00801b40041c1400e04410f020f601b08420100181c180ba160702074004200204030b40c03c030070b004100002c20402141c20120180e8031039038100305014002c042c0391061a1403440390742c0940089404c0e07100103880d48610180c0c410f0307900f02e200e400d1008003200d002d0400c240040b60f00034410105240a284c00c940003e540720420040100401003a20ba842000316540f9100b6480d180090340c0f042d450701041c442080018010029680c005a002e111a84850101401442002e60380140c0066440c10001e80b01d8840240d482ea205 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 407766312 1250 407765062 407765117
    0x20d06050a0807080123070c030c020a0b030406140115110a02060a050a022e0507021f0204050a090b06070b04030219051b100c150207020409060b090708041101 70
    0x600d0201000c2070005010801c1022601024001c00240d00d501506c2000844404101610101d030303900000c03071060181e0b00362101a84a442d0800407d0b942c4d80c00101c5000298110042d00c4030080204001c0116500c0f81d0a022070150568070b05a62403d00000981000507900030100010302d0b055058558040240e100780540c010030060701c90044000040c4181c10043c0b4000040c840d01c7c440c0d0b00014010003018038200c1d201c802500c01b82c10302d652030341c002e080040d1403541148201c4107007400806641c107040e035041c1d816040140c0c1e11407500040105000b00b071b8101c035036164076000c0c0361912903481c101101d21305540003000c3c58080d659401c0590409648000300200107107282000d0007081000700d0305801c40c581800c00700148051783d005000c00442501c2e81807003c00c24114003200842c0350095000b8003031a601002514020301d40d4042800c2c3c500150049450781c0e2500c9156106240c00840c40e80c1c400001d1815540500d01512061500500300440e03078148400403640840c0b4130351074501840c02 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 407767562 1250 407766312 407766319
    0x3110a080f010212060108010b04050904080d020a020a0201030510120b0408040e10060912050303073218010809193207050306070f0e06120c031504050c0d020d0605 72
    0xd010349001c114080d502400740007100030b82c0d0a001807425070289411a043e40c140800036820142008140300a07110060801e0303440103800e000c0d90300580c001e40020450a01c43c0d5020f0176040d040c6100260558001074140c2c0b07158104a00103000948284004081031a0040d003602c1c40b03920ba41c10034500780c1c0710340d80101003101100d00c2000381d00e803020041d840c111040c1e41e4074506550340d1541c40611103c01102c000f410f0360402c00200306038600c1545202c1884201200c00101300240380405814800400e840321115800441c0381020b000f00c42010850226003800e19010030314000340c1190700c90042c2c1100b20440a000389510040c40f801d0040924510442203c00c400c0500380c0a80781c0e00c005001d036201c101d600c2003102c0410b007030801081c0c15020f041c170340e1120031103000c02600644d0500c0f028110103411000034025824414150160580500d8005003080d503242040e0901c4090081d0b80c006550144d0709000c1400b40076a03011040305d2500a4203c0300582f00e40c9409555009820316500c096031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 407768812 1250 407767562 407767573
    0x607060903260403050304081809070c03020c090c04031209031703010503010e010b091812040e09060a110d02030a1503080a03150320030a0605130c0803090a03110a08 73
    0x10103400c4a07445481c07001c294801c042c0034400c45440303400e600c400c0700e00900081061022800180001e0082c041683c404908400e00300700040228007000801c44e40c210000e0707180601101456014007401d020b10a098880170b4440c0703405644142c8034881c0340310040000e8420040d0b1200e080c811400130b00556807029540c2700101180c0b1040350207420a0182c00d00c01d520300116400007420501c030780c00713009401410045441c4c1e0380d05200d01d40412a0120b09c100d500a181c0c040142d00384450041025146403172009500f403c0c50308116240242c000d10b6025114034040031210b1541c4044d003500c1400030030030070240e030300c2c0d80300d0b0041070240c86007a0721200001074115001c820003d0841c0034200030442603030104840c4030104001c40307052000380f2000d0000c490f0a4080c02c0b1030415414110f46a00000d0100c075040b11203645c588045400c12500703064940b0390b4480d401c0c01c1240422040c001495190300450030f10026400242c40801c440c40010724481d000407100c521504c7e904075010007071003014141c0b01c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 407770062 1250 407768812 407768831
    0x1b030a03020a030e03031014130f09110907091511010c08060f04021606020706020f0301080a0c050402040308031602160801020909010824040c0306051f090623060706 73
    0xa001e50030011050300403a0801a80303209100303000041e02d200e00b80300003000034540c1c0380524541004032402c0d845074008952403e6460423141d24080c0a40c15400c2c0c010018640c041c1d420301d00c00d9540802002841101014181700040d680010107509640140707032030221403405030b1026642c441d0b600c0c665600650810740040022600102d045103c0c1c8004d031044481001b841041000b00d101d1010710002c903400c10014000410010390103844400e104500051402d55000320350100c40d0026441540345500200d0380303d0801c01003000e0b0300b000700000d03070b402c0d4245411603442031884c0c0030003440e000645541052111411f44200100801c04030800040e2841c60b032603c0009020750301051210340640c0d03e0900000d80290002a44100030480d010703001300c06070980c180e0960702103024000303440f0810b4002e80400860203510a05019402101c0002045040a0521501c20f60300d907000064440c5009010003200310b20a040c501524183c0e0741340300201c43e0010010b007260142c440040c5c403461521040c45c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 407771312 1250 407770062 407770067
    0x31a09071d01051614070b070b180613061a060a0e03070807081c030603150b030613050c10030905030a05040f080a080904020f09040c26090d051b030a 66
    0x1201c010030795040e1000146649001500c140c0f04900090010f05403000400c000700d03106011034400032007a8000c0d00d014954410700b240d61a0466070b0180d03190f2904100384001c0810942c6819114115a80a40964507182c21411031100d510003020f01b03a20345580da0080f4400045d016101c0703408004258a0300c0ba403404a0003041a088051594080d200d640d0002c12940300c0003071100101d40040c80202099243c0c0028115020340f105e03003080500d5101c080110001380c49002c401410b0658410001e000c020050405d40780182c090059421884100c0700c020100f20b020a14150104060b140a4140140c0d043c0c214010040d101c40a02540004120b055002da032001c0100100c80801802501850b101c00321a5104da8400300c0080c1507403410001c110307a0341016006400900e20300f9013618204402c41012901f95010b402d94031700080c02d0a00750a64903609603132201141d1003846070200c01441c1102241d5507502c0309032140018071001050700301d0441140780711444101e40c10340075240c4400034000013 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 407772562 1250 407771312 407771327
    0x902010e30012c0318010507050d08161107030222050f2a03130303090f0f061107031227050a02090a0b0607030309020307050319120905030d031a0907 66
    0x1c42c0301d40c05404080701d00c851951001015541c0d18005507140042d0171601445034030358480f44d40d052000038010000030030424860b095070341510f9100c0c0300031403800014120802546500b06800d200c00945900980c000001c1c00006403603040c0c4242c5410b0300c0803101c105401c0d1001610007020350a0404110080340600b000354018032450f0380b807410180002c0d03012100301e14032001c1c040020301c050001607019200390741c689401c5070107402c0000d8502c0e01c5444695a01c00d1248054440d07030045d0520303504200d010711a41010781d80b0f42084500b0303d649030b50010700c0c441c45046040340460300e601441d091009542080c050f0701040c2c0c180700d100b00381c092070120b4659014140691085041d9000144800b015006400c1070a000801d0140740c41c0141e0b0b0107900038502001c0c180c0e01841104004600c1f900c042004403000b600783c16011070080c0152806404c40004032404400300b1205210800007906c000840145080c461700300800c0c901f94244c403000b0369402d24038031164407501210a0000c9035411010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 407773812 1250 407772562 407772581
    0x504021309060506270d12051c021e0904020c010207050a06450c09020c0f010b090c0c0111031e0603070e010b0f12070207050a090902010e3001 63
    0x781400455a5042004041d004450200c542024003000c3c0751149a2480307216409994010003c9040d200c0680b20388030580703800031845010940000e010015203503289c43c07540d6282d90a0700c055203083c02c0d1450324007541d40b41c12040c0d201d4200100d000c54403640d60380c060b5a03103070100000864030b0350f149003417165a64030015020f841c42c80c030b00041205035400000700040c1000180107800360030b10543c0030813844000008000f8200c3e4401c46a804001281025140000d202c034082c0541c0302c00f001a4507509020929800805580c904030b540b84007900c40000307040e48803250040340f64840003510720107400340c03254081c0354040c0c00000041184421a03420707405c0294006040000841d42d86405156686100380140850124a5801040700d42c1d10f07900140001c1b41c03001c1c0103038246003038800c414030170b420103944010260304604021b01c918242000144010514410b041c40b101c2e88a1b00040c01c903807481c803945401080c0082c4035418103101d207140c0c02040005202040e000940c40c0300c000303008084940 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 407775062 1250 407773812 407773829
    0x9021c0c090213050f1201050709080f070e06090c070b041b0509040b0f0a0605040603080405040e030f0f0a09120b0a0c1d0f1f0503011d040f0605060a05040213 70
    0x10004512948240300b0f5411101002044246584c1000b003044426840280e255601039441c0b1010380c0040030070b0040c41e01030300e51074891810172410940c07201e0500046e28130502c481e9000080402c280039024603032540041042c0c44161481c3c0b54800080e003107120703141c00070300f815100005000410004d20b103824205942d4200b250341968440041000051064501905c058034010206100d00c0100d091a07820441c468400030701c0658640100e020341c4d003e54000d64800002060401680c2400d01510100f4034600000d5458107004105030040780c0900072035042c240c3c402090380282640110145000b800c1c451103018940c01f1145001812858120748108031103040c0f06886d060742d0b01582041e840c170181c00d540d002c03104009d0303410f10940c0c8103109509584450090702d015001d0b03840b9440042d2000c8141c0c2c8007070340c960409a03140740045841540d009003907074640070440441c00c101140d21344039903c0000132966868210001e80220381e10340009922603c001850002c0190003c030902c01c42d107510 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 407776312 1250 407775062 407775083
    0x180108060105102606041d010902030105100807150c06050a021e0306060a1d0406080607020d020d05161103010509010b01090f061b03171512060402012109021c 70
    0x346000c54000d291068002013152803154001244015041e5207030b4070643c00b5000107006103982d1401c0340100100081910503075520716041041d800d0038000e076039002500140380ca104901d8440300e5a80c8074030900c90f4880f600170780c0c2c0c88040310390303c190f4402c424190405024800d80c181800620021b41c06440301c00f1411030f446102c3c003041d40743d13001601e1094800400751801c0c04090181540c0100302041e21a1280f402d5140200031940c403481154081d01c60743c4001e1083c0e14210702c1c041e15081e40b00e0010f00541d803100d401c00700030681c46800c64103007014107001582c141c102e901d81804150003145500360f041d401c10003040a200c0301540541440d0400b42d9a00400075603078880400308040c1405180d00042c5e00c983c41e010040c2442070040c0b5820f200b0303c0c0109890f003804020050050065030291180e2031a001c4910003032601120003c140030041010b00282d0403c1e900103040b1407801e1030386581c0300d5410f0004c2003146809030300c00440c80c2e130043c1c801c01c03402c0014540420000901328003119602c2c140d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 407777562 1250 407776312 407776339
    0x90c060807090f060c02120d090e2208070f0204060e0a060f050a0603090302030c1005061816270b0304060e06010b0d15120b060306090307030206040b06180108060105 73
    0x94106a030440c1c1038102a0f01015083c5501150403031071141003a6000901d020303209070210010092844019041d5480c45034250820f41404018040904801410310400341d0a0140740c9044c049070803403c3c0e20a004969601c810710700b00c00001c1c072032200a5482464144d0014292000e0509075110303003075a4904115098a6170400b1407000790764011030340c010014034420f00c42c0500942c0450710007402801200d0070050907580c0b00d4606004128140c02e41038450003070007454180140d45111594035050303000310354600b03c005034482c0c1411848010070440c2c1d2810042e01c515150140070102810703041044174050721040c103840b95500659003241c2d110316000110340319141c00f1400078143c03440a4406898a07030110002d0010303001e8005807108107004013400040b007101d15121a200240f0440e10403015203400350415050120080c911007440e0000c0120740002a80440c02c194441e5111101c03c07542d440d5030340400c86614504507485042207901d400410001d0001170014100c400445008081c01e80 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 407778812 1250 407777562 407777567
    0x60103060602060c0f1209030702040c0c0803150f04060b030f09010e100f060b031303020c09010f0e040c050d0515160503010b0d0b100905130e060402120a0204090c060807 75
    0x1068032074000160040d001056034800044d00410a8040c00303000d0608000da103024442103c02c0036940140e20307502c00120703002181402c1c024140c110813075042044848686454005061200501407003100740340702001a19680c0d9802c0002d800d40c0c01400802055840d000348088541c410341c0c00000c002d01d114000766020b00305002d030681090203400076010017100034580301c0c0a0b1101c0284296201c1e242c1c2c40104686810320013035485103900308024584080c65040181c240f03040c0c3c2e00c04500504a8000510a0249081c15841140e81d08000030a1641c0e1fa4140142d003050703980c0025902910202c00301080c07000000300e1849c100114181c26049468284103010000352051038040414404d000401c0f40c84072203000341105560101c008500e12110780d00040e1540503504001c40071540801c424802402c3c0080840502e070a0030742d0800c03d04c04000007143d0341d02002400288280031440c100300214905110000000354080d106100b90107892400c1000c414150240d0b5001500c0315002699561 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 407780062 1250 407778812 407778821
    0x906051306080c120f06160f0815120a1b03021008090c0d021c0320010b03070e13140c04050f15041a09241f05071a1302010206060103 59
    0xe480c00010b04403e003441d401c0c40103030b54048004c0c14841c000c1114102a4072001d004040c8a000c0c442d11205004890b040d000d0001c140e00803508040258080c10003141010092071051148801c0382c1d146000800441d4031703803408400b10780041c00a20052200c1001020f1038008000340c0b842260b00ca618401403203000c4540a00c101e6116260360f11103030566109007010b4045100550000c2c10043c610385000000303010496002900701c1c00201c1c811003400204400c04a800c80c001c008130028048168040700090380c40e9814004c01d816a010f09020500784070410002400465100551060b10004c9041091325030221007613484c010b5082a00041c0c034a8500c00525101e040c98403038090f40401110144070040c0414084e208540c4100012140c8503074a5640300c9204100b00c100c0c081502115411340700c08000d95002c1d442c055682076000e0101440e01d55041840d0a03c1440e0281d06c0e01132504080340c200c00401c1110007124030440034480c0c60468502c59800d000d0007a001c03160251170706001101184c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 407781312 1250 407780062 407780069
    0x1e050607050a020616080a0f020f07051503070207050319060c0e011e020c0d0c03020a05030c060307050a0201110c0a020102070e150f06120f041209030309060c020d08040906051306 79
    0x16084003028000514005000d042e00c061170b001a85055802641d03890b4155002d0381202e0301103481c1403c06090300d581000381041012880d030241a2582c54103000c50700c003013006550522040008800a444941b080040b1001040010101c4284098803020500021840c94003943d400e414291030280c83c81c02504039140003401a561401c004091070444140c0e41c0c02840300508600440c09480d0f910f0380c2d92414480000c0c00b8501001300c9030719510400c5103110b0503a0049000760070a40344540c0c00c5d03641c0d1090b20740c0494030341000c07680c40b140003004030300500145084240c440d4010071400c4401400190011109100303808941c1c0403502d40051040003641201c80d40701a0025240c502683d01b000701c2c0700441140c0280882d070410f450203502825072002201c88100c0c502003a010801442408044d0f15045015410492205c40c2142c80c001c1510550b809014148005a084e040864075a80ca05491040d0404095900c0c1c58171840340002070300d810300c1032030701c584102c10514252210520403078044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 407782562 1250 407781312 407781323
    0xf050403081e0f06010c060b1509040b0a060507031b0b010f1e031101051c02030109090c1d010e180109110102070902190e011209030c3e0402131e050607 67
    0x32076139a500115500e11149004450040c2c650061590350b0302c50350323048040d07006450724542e00ca0f1504000d000803182800c0d500c40c804c0891407410058140c002c0100c0d0002d40e01803800316800c039030f02c01c3c1c042900c14402c10b00810220b000800091103d54030f070f182c81c041c6c48100207a40055103c0d80140d42d103010082c00b02401441301031181300640d6000e80010041c0c1a003007801c12000142040c05081260002d034406030380d59403613a904400300400701d82014068070b1a1094001a5a20000d81034243d03101405840d006004e8900450080c10360480d0300740541d08940c1c02841b960040c2d26140d06808110b882031070242c410040c0104440c44180281d40340e06660381c1070030440d08050f110444120f80c0207055103040c00000c642c1507006080c00d020300000e032030103a01c440005112614104004001c100260b0703640c01010384ca100380740424051924000e680614061280324201d00c0000d000b407207081ca41d104201075501c2c00140c401c00c5584805400700c2c120640b4003030140c2d1b4105104003840780c0704c0c00510 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 407783812 1250 407782562 407782591
    0xf0a0212010902100810170c0102070807180b120a0f0b090c18070c0c1e0e06060a0c061107030806090c070b01061b1202030904050901060503100207060f050403081e 72
    0x68003449511307400c0e4040ca51103203c070022030355043d40300010030000300b041c040c0e074102c8c8081c010745580410135080140b5000f40201029485e001040003011104c04803c43c4081c0c659001480701c2d5991060000f4070a040c6082c1c070926012450603030840190120122080d52044001410b001d1000c2000c06600c0300c050a100d4041c0c0c0c4c948440203003074900421040900158a0580001c01d2680500c1c0000e804869030300740d41901140c5845061a0481d44043c0c10130103100c04116940d110b0303c0c29900d4a0342d0380d0a06007103414440c030f820b03805002000003a0307840c407001107522018954403020300c0d4026402511010501d40300e61201e0b40c030602c01c004002c4c1544030014010801c1b1381c4203102e13100058203510300e0b05140191a9842503648400342d0030700d0006a0010a08001905d41881183c1d00000484c00800c0310034541030101e81c40b10346c02400c240303a0035400f05200c1c0078800d480c0c01ca02869005c004080102e85000c1c0340c05406d0200c02c0d1200010300750444440381d040c504004c08180a003402020010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 407785062 1250 407783812 407783839
    0x2090117091204030318080c01200a1b090b06030403020a0f08041212030b191a09040606081b0901090e040602130b03220b010504110c0f0a0212010902 66
    0x9000c030001522104103071041d44408010441c0900143c000b0718429980c044a4020780a60010710182903041704038a030b0007050350711000d80e8000c550041c1a07140312841c00c0040c2d5051988900703040d803100028103590b1268085a0404440c444604251005c802081004107a2801801000d00045070000c0250340710741c1041010a0b03210380c014103518030401d2000d142c40d803a80002011100f89007003ca131503101e4004480720a98050086161130032041d2148802d90b0f030b1003202494043c9031441741032400d0602140d03260310003035440304549080c0c2010b001803004554401c0000c00744da40445a18521895401d44078110103441022903401607416900c0e4a006410b10114080000c0082c0c003c81380540d081000d08100000d4580d8034000b0151031003019180e00d0125858085640f4200030001d0310b200000340000065207000a040c15100191000506035420701c4060341c0d544682484011a4402c074990102021400141040001e10955045040003c0e0300c0c109800e07a1840e40c4020341c001800000f00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 407786312 1250 407785062 407785097
    0xc10110f2103100312031d0a020306011a04030c0b070b010512030d020d02072f060f0d090501110c10110301030f06050403120c0e0405100509010306020c03040302131e020901 76
    0xb160040c14104003020340e60760382c1d0f80790071801c200a0601c001081e01c60a502d10f914200c51014245400030320080c001e507103216030000741c5442c014012028084021117000a800b0507000036940590341c0b00301c5009445448005c0903d69070800304080350070074801c05c008100d83c1000849524030030102e00045040580c0c4144030030107900a185500c503201c0c0d09005d01030128040e14141a03000d8400a03005001c880000032822003500000303510b5019000401c80d1071502c140325022503411000000001403000300602c4c1c094090101e100c0c450520600104a1255481c8081400642d80d4580c100c05c106038452051154410300003440050468031a1003050404650b56810840d4420b1081c070700b40c02c500000303150030380c01c5542c0c004003c0c0c0080c0c590a0340303400604062044030740014070b410060303514030301d042e002400c181d505001c01044103170080b07145c010220003002036070080d582c000d00304a082d40d01c3c10402c07001002000b0b80c6d0791940e002c60000c211140c07201c2c0b084510b1380301c041c1e4420318007860301c0401 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 407787562 1250 407786312 407786317
    0x90f050301060b12150a090c0809031c0e0c040203070914010918020a140409060513050108060106050c010204230f0108090c0114040306050906060a06020d0804020907020c10110f21 79
    0x1040c07800c00000a00174425a0b0b6903040d6000f80101c1034002510290080d00100504e0000305180110350040007940252200404980300c14144000c0105501c07419508040c02c02d0410f00059801c1070003c0140400d050300b040401d826100c80409000c40511075000440e8101802d200350401881d144145410192594004142c0b00c52039080084903690400034500a6900c1750703001104c1d9650b5010180032070b1510030403e00700c00008060a20255041102e02503c41c43c062160a051000c0001c41080c070600079015107004206035003680c60550a0a40315402d80c10b801c20940e41315407140c89600382150300442020340140302040007400011007400041d034a111080c4c4c81d1032a000402d10001000a07120300170f071445645441c0143c5030a0a1400074880704d040a41c204a081d904005041040d440e4050a00740c1d000c0c2d0105d82c3c0d1484d603122440f0507802d040b413245000d60044000c180c000c0da259005003000b540d0800380001c98100004010314151541e4412440da002141c0c80c540c0b96508842c004c02 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 407788812 1250 407787562 407787571
    0x10e010608060d1b1a0f0409020714060708040c05040e1c0302070204050c0d110301150c031205090c03060115090b0a0201140708060906060a05090d21090f050301060b12 74
    0x4180c0c0101c1181c075152003801120301141c09940c00e0300720520580305d07114140c80740d0108418000c5d04004443d0505142401580502d00d40c61341c0c080342c50028001f140000000c1c5220440540d207580c103000c940185400d02c100c909440d54800c1d20400981820688030388600301290002400c0b00d00400b07101c1044001c0c4200c0c00b03d08264003400104056030b01c5104e2213006040d40e00381c4907510b079007544a02c010358205010040201209100400c0b035502c4900546444150760310b08a024110540f9041d5441c0c805410044101c1d49010200482e404001541048020044003150b0030381c1c5e600c00668040440c400401c0c800941c4004007040321345107440240069050500010407160720a01b00d103500314004495078400140604144041400c03c9244184c01c40c2c4e041d034034945440032003003010303015208010419010705118464182406101030b09140e0601c22940b98009203010709a004150204034000d00046000440b4001083c0c90144503c0048400b040c400341d007000c845442450341910001c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 407790062 1250 407788812 407788819
    0x4032d020627030706020313050d020121020d02030a020a030b04020c25030512073509131a09090606030715050c01020d0f0b03060f011215110408060c03010e01060806 73
    0x4211100d5980501c6060017400b2258011915000980c0030703401705000c150320490060f10701c41d84541c0941d03030188034401503440d4000708a5022140c00c0f0b07070794000d1003014854200c00b4404014170081002c15001482c44200955050003a0310208040204a10030540060110380c400411440400c0c0202114980240d01c0c03101007100702e940c2d4461300c1c1400c9048007406d81e0b440d0001000ea041000e200126200402c8010700c0290701c80030400b640c5e021021003040300c1140385001c962244643d490044005c0382803c0c0044c18001e0a6840110001c2c0d102c0c08a1203601c01c001400c0014840040000c1c4076114000040051044c0c5203081c003000400b42c83d0032030030707020810104100d1400d50300900081c466599485000107403002c5181c0c0c01e0085401051031188283c0015060090505111503c18150f40044210b226045400d01e050001c1c441c160321031150050401d83c00c8108440074002902c101c44000042e201c00e999132803c0300c4514442409134800c0c8540c0c00005000b414410b02800d94000d6024 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 407791312 1250 407790062 407790127
    0x6220b0105071506180c020c01140c0a06021b030702060f0309030403060510091d0d0315031502130e01030b07051312050609010b060c0703020405130804032d0206 71
    0x94071241c3c1000032180380e07111100e450781410095401108031140081111007000c0081e4403118030025201c0340c4107800300f030401000510701c88406c2d58950850703143c41158022190404400e00c0c0c004060f4115641813107090714070880300c840c0b00c200442110b41040c0d00030041480c08180790080c039190f40002c0c080e04850301c41408040001960751050501032105143c15680440c9044916003d0b507000940341c021813810f085090109007400540400840da45003008568000c10b1905005403c4466002501d1203072907502040840c3c0c1c0302c0d801800c0f94055200400c00058680643d0907030100f0a104c01410303900e0b502e0005480502c1440030301894041e503190400d44941d035120101d0310403c40002a20103401001c18402d50500920031031b000e0650075110359042014510f921900c442c03880c40080e000f9516080040e2a01c440d4102c0340c4c3c1c10350b074003844e82503d8a88138202080010345004995281f03206080c000d24880e00c0500b52082616402449c8038034048107085040e140d89508010400b00c401e89 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 407792562 1250 407791312 407791327
    0xe0906100906060e04230403020c13020c0a0b07051e0705010614060304110d290702010e070b030a0f180308070801050a1701060902030c071b050d08030903090301150302010806220b0105 81
    0xc0300c0c0103c1c05a400f0f54018185030b0000010401040f44001c00300d0201881048dc402200c10041481c942441e00001000916920400140c40511a100d40011016200500d9402c640714010150071035a02942c020030942d0385814400f20741780380858010307134026001e02c00500010703a1032550fa040702c035015101900d040441d0f5203c1500c1081e5583c12580784511a41c082d440e503080b12921588280c2034402401074000940f0010744643d042d02914800b2030300000000e80c0882c05811001c0e0381c41418604001c03404040308a80176412207450110b000031800c0000c6210640308940c554141c803401440c203000c55103410441c6c020303400c8209250a441d5225100001c500e1101c2c4055071258000d074402c0d6996101c10316107806c0358906c0070039040c07045000007014405502c45035051050b055022074043d5590712051011465030181183c42ca41c590300b441c10407111600180104400c8034800c3c0c880800070389034502005880d0511300c2400581c4241c40030f10074038030101500160482501814054545000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 407793812 1250 407792562 407792621
    0xe1032031b04050d062a09120203010b0d1113110f070f06140919081b0a21080c07020d02010f14070c170f07030f08040e0906100906060e04 61
    0x413010000d0b1601a50760691511120300d0b04c818000c1d1850b02c08076050301c1c00110340040c1c518003a900400c0c4100c09060b1002c01151401d5004242e120801042c0158150080c5046500000c045036518020800800c003076400c003c40c0c2c00f407190030806c44504c030340c1010700740d02e0f04a590750000d00c02070b80d240c0f0030b02c15000c5c0841c80750302c24142c1102c0e0a41700c0d02a1403900741502e510703146003510041c50328030301d50161320040707440320041d81d0085082c0283c03010b020000070070280c1742c524404000f514040c130406034411031550701c0303880d4819040c9603211420703242d942e01c0f10518a40241180603400500700d810041c0103610403412845055030505010042440c20b0304038a03943e4121030400c513a203032620f6030107000040740005e2680300a241207009100c8088042c2680ea100c00d010710000340641c95915502007080200c038103031006070034040e541c0c0b6000e02c0c003240802d80d07420050f20100741030005200049410460790041e00143e811549460400d51180d0081c04002c001c00444000c0307956403425007011225 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 407795062 1250 407793812 407793829
    0x1050f1b060114031203010506090d3815090403091205031206032d010902040e03030406050105030c1005030912040609060807081302010503070e1032031b0405 70
    0x114400024120756041c00103120000001c60309451003680074041070f041c0c441e60542240d06442081c1c400b1501d6542c62404200d20000303030200280582c9080c900c40b040f04075000c2c2c54410708030f0040c41c02c03183d20b6070218103000580030035144c2b0880880c001c0c0c812800c1e410110405a0010311a241010450f81e0310481e0505030303484148102c40f00d4000180b00c411100c1031138001c2e90086c600300e001d040100c0d1340700d02c244c08000750a4402080078060f80f2500c00081c2c403c1d4011018540c015005100c0101d421030307601c1d05d03540219003c803059444d0600105550500060720b21405402428003548184501819551904010002e041e00c0c03040002805525030a800039000601180e1603200040d4140040170700310b00d0004218100f04092041002000e0b601c00ca01d41080725020308015035643c644e40002c4503404000c154043d080250080003c0b0310b213a003d205501d40046d00041514540f1001e074400f01d4805400141a2802c2c50500100300c1643811001d04050480004200c0c610f00359aa0303002c41c0d00d45 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 407796312 1250 407795062 407795107
    0x9091a01061112030609160507021c0203060907140105090d15140f06010c0308041e12020f0c0a05041122050a0803210a0e01020c010504020f0307031101050f 69
    0x6180e44009400d4800c00304041e900c40100c54619a0a610302030300450321380000144190081c1d90b207d00c4420120b4010000c40300320b142c010303009260700240039004906000350900308034002d208100001d101035102046240035580300c0065052011048001111140c01106195900074010740d5114000313924221840c034080280c5078049181d200c02e403889480340303200620250115030000f08014060382d100003025075165060804a0068686092030a1100016082c1a442c3c0601958201c10b100720920a03c2980c10b165080361002c00d2000101600c641c0c040c6a019080340301030009221903c2d0035040a400f40c28014204c03810004585181d0b6030003017501010500c01001d405080c030441c05c03d917902c1c43c0034201c420001c6181c002c0f070781480c502c0b200765104008035041844012680c0d042440d00303c90000d40d01080255200c2140e80442802030a051300e0480c03080300c03801c0303035015030f0304010440714116070304245244803c2d120030005407a964804003049484035020400d50411004001c0c050010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 407797562 1250 407796312 407796317
    0xf0f0e01050402090f04080a0c06020c1b04060801110423130e0106050603040201121104050a03080405040617072903090a020a0f08100207050f070308070c120b0109091a0106 76
    0x2281800c3c0180708142e64080c24001029051004010110303110701c040b00c0c40000705141401080c02e150038001c00134002e54a0b20807981c02850003082302e0300d4500310200051074045400300312035582c8012040c201e4140009c0c5090f1024140010810fa03018120444904031081440ba408a2000b80000e48a050038120380803490f030f503455003462000c00034841d4030040c1c842550110701e14241a0000707021111550940415141c0b102c2c05404020b508000380e800506000e0080c00801e51039140c100e905400c64003440780960314001002555040c880c58a4041c0c14001001c0c2800750300740441280380c46011405680d07650201104800e00c20710000003540700b60000da02400e583c01c2684100004086980c0c880000010103c0c0e040c8010300c404258102d15540a1000594031492483d0480c00c2c05035544185080b4003e14070f000041c404004014061070744601c00709070303c40d07232a900c0d10003201410341e02c044c052074140401840403000d01d500c0f00103018081d6019062a100100304410010400d0b00013200 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 407798812 1250 407797562 407797571
    0x1180201032f04170703020108040b04020103090c17010e030406090e2a030f182d07062102070c1206020d050c19091202011404030614061002011a040f0f0e01 69
    0x4081c1801001d510b00007009130242c0440c0f40345400080900308090409440d07850074001007800c580c0643d001e01c040300d0303020740c461020995904c03001413404050400404c1c654240842c0300b52540012003100c1c2642c00d581c075640c1c01182000991204010014241041c02d45400d4041c0c15030b0408003490040e0303805806803540e80f481d1040304400c0c1c80b90064000c500c001282440d044175144040791080044001079440c21030000000b81070340340d24005c140d0860203409100c034042907050340001c4504500d80c0942ca0704205401d03821032a4100c0c410a1800740000e58054010301c82c07179408007110440e10b8080d480150070200040c0d104402c68000360bc3c80c04031414009104403c01c42040c2d40c0403216000c50622164880c90300400341c5d510103a40340001e0401105c0c0348c82004251000081d240a1130700004208503280f032041c200340c000c41c0103403400c5204000f03012815020f244140038852107030003140c50704000c0c1c0340043e00340006489500100144541c80b02c400c4c0030060550312445804d00e43c0c0500114 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 407800062 1250 407798812 407798819
    0x71b0804050a0506120613140901090501060f0b04061404051305090c0109030507090506030a1e02030c060307020d2f01050124080c07030201150e060406060201180201032f04 76
    0x1210014030341c0214080c80d02800f90440d03090360052055400901601c415605102143d0340f18014454940640a00b1808d081400345400781580004c001078800c8008101c1c07140c4404909010702c01610504c24201800c03c81403280c00e2041d491145829241b4000034217160312080015110f00b806222040216503607030070490203c2c0200115548030b102030921180c140c0c19034840c651a000c03107001c1ca1011030340300c86c04200b540e2000c00111280c20b0b0070444088140081a41d0403030245083c9905070301c64468060380c1c050030f1400340210303070040103284c00408090030032110950f00311346001040314003107032201c0064941d0460b460700c208140248c80000940740d818880c0040c01e41850740c0341e584803451042232042c5a0b5400843c0941c0044c141e04501d0349444252400300d01403c106020302c0f149130031005000031a4a15801801c2c0100021503050014503116441203007240c031104401e019402012500801550003030340314404000091306002c40b1641e6540c601d0760640562210030020768170018041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 407801312 1250 407800062 407800069
    0x3070f06020f0c040605010c170409240b090d020d0f08180102060108030a0f230a110c1806131103070e010906050a050a12180302030a090801110d0203071b080405 71
    0x510f81c10784202c81c00c0203042e06100c00205070020008005202070481c0006c2415806120141c1d0000c000c026010f0001c01105808000400704548402d42d00d41841034002c103401e1035103015a001c3c458060b01003a102403503038003000761040c0c0000342560210b030215079007004609044000c1c00d1442400c6540410002a0400240752a034141c8c04500c440d00203105c41e00d0f880b0790054604030146a245000c0600c002c3d44002c0c008480c002c03403007030844020005182800141c100740d16251454082080d5600e030845402440b600c8080000110903080391000025118601403076a01007203116082d0026114400d501442902c0c2c2c000d0751603c0100e690351780005042d43e07110507214094059450f01134102100d946000d00355014001c08002881a1100c101d2002902c961210b04c1d000024426140451540e04003c2d440e81d11680309003000454864000c40c0101050241d01464446824043c0c50900010440c100a40020f013180040100c0e52004003030400303040280b80803150098640c9a941c17860603081 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 407802562 1250 407801312 407801323
    0x604090201410708180109080a03080114061602040c020a0503180f18060d03050706022110030b04060b0a080a1101260a09022b0b0a060506070303020903070f06020f 72
    0x1004076815080007101c00003840b101c166481d500358a20b00c07801c90001c0e00010307107244006410608d000e108034010002456070040030325048030340102e0150056a9003005101080c890a0f040340001c141d418600d1005040c03552000703100e5055881940c00c4102940d80d50b50940c2e21070302c0740f40d80240c5c243d40c81c20320314a0f111620300d0416200301d501e00416411284440c02c040f80042a091040f1b4485a002040c54000c1044400c9a94049411592004220300ca005040e414401301e8110b0512440042c0303032040700004c14410341c5c2c3c00480c21603d943c3d880e03982d240030b03204800c805608000c0c450800221002e08004e0280503030320402d000b441d4090068001040c0c450340c0c0c403021112154079801c80d40340c5101d41407050382202180e40049420305c0d01d400826580c10b1001072503450200c08540c5420707282950a54001550700c58504016580c80380c801c082c4c20340b000e0b40513660f4864001c0043c100041e0195008000b202d00180958650513507815842e04014003650000c0e02581250490209a030024000b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 407803812 1250 407802562 407802677
    0xe1002012c0111070f24020d020a09090b010516020f190306050703020702090f06120d020c1201060311011d090a0b0f0909060703020a03110c070f120b0604090201 71
    0x8489007449a10b40385d401400f400d40902030b20051507100b00209480071620010380141030400d0640d90303050016080c0c0003e6001500c0380c1d000070714095010516510900580c2c0248105a58040c1071410340000d1003c40340c1c3d580d004a0748100359114255964031f907401c030001e14140c0c2c80b070f4030144140345007000015204000d00840415104210303600059407100b0007140c1140e00c4040703410b1260354110106141030040031656203140320744070000c45500e5001500949400d425240b400c030918410010509981581c080103061405186001c1259441a003086000c81c20541d5a1100290640003041e60500c003501c1d9070071515190310031220705080944014000030780a0790221f0b46450718855180e110307a00681108205a00000d140c00c21500c03d170400844100c0c44600107a644680788405590382e40640701d465880b82000d58000303010340c01204141103042e08952503a600e545c940042000902c032050080381401070048a8074409002c480c01d0b8000c003400c560742601d0482c0070f142050756882c4e640c0d2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 407805062 1250 407803812 407803841
    0x114031e0607144003060c090602070e16120603030c0618030c0210090e100e070203192607120501080703080d090c0816031104020a0e1002012c01 64
    0x102c1c0e85128414510b620034910301800300c4e260844072521440312412075044a40701054003030700000c000c1c4403141d03028401060640e114200301950b1a01c0c2a03032100300b24030032180b00500d03c2c80094810045060100c03540b84d82071412070800c01051070301d00c04403000c0d0b400540004080420342d20400215114074080d40700b80c40040400c0100594005004494156000b8052030421040c0318440d40110350050241440041a00f030310301d0040b03180c00005d02c41c1e00c0350308480f4201e1408140410f0011003241c032510b011980401d43e00000d2001582d610455001c401054485401c00c2540b100c107041c04030307000300d004c2d5030748030645064a126481a03546c1038110340200d800042d0100006440081100c00a1105440100d42c1c0341c8181001440c8040300c1c0c4c012010b034050a881d40d8030320302000300b2510a0341d204201e03003042e1201e42c8003808102e005e215000030101d00d44a2201d000c40c03034140001112038005100102c0e246122100707520101c0a0500440b000c000e1150210b86c9100d400e02405410181c040c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 407806312 1250 407805062 407805067
    0x3161401030902061806190e1008040309030803041a01080a030324030b1902040b0d0e010606090303030207052a03100203070c0f1e0c0518010602060114031e060714 72
    0x26000581e040c85661001d0380361105c60384800c01c1d2502e480c0c09131869403c42441e50804000c00400c05003840300103138191131050b0340c0c042d00000c03807902450640d402107405503a400302c02400c41e07403080d0546d40040c0041d5010751120a240010540401049020700401d2000d41840987d5103070240c1a116041c001e1210888081c8a00303034007076108806142281d1300315a540010b81c07101c03000c048000c80328503c40780303000703000180200e44504107000410b4a42c0c0380120070003160380c0350300b541c80c200e4549004400000c0c402000400119110b038015002080c0290292071000c11003045146903884040e031400409d40d482074004003a403800b0320221501c241601429407a61070700c10b200400c0446d0300d89000b4030540e01e03514a0024000e044112034112418074016201404041c00d15601f405114815184550407407000c4901040808854504031081d0340c004100a908026020070ba03500c00d52049501480764891010504034226048011051540068070729070821600080818005030340c0c41c103050104 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 407807562 1250 407806312 407806331
    0xf03050f0f1f0b06130611060405060f0a0f1a010f030510050103021b030406050403060c1b060f111c0b0306090a080706060b030a0c020d0f0503240316140103 69
    0x200b0a105820342d262030450403040c0c041c41c000d00900380300400c1c68010380003141039041c590040381208241c890503190621903d81c14440c1070f40c0c4031400c440007026a08820081440180407001075a0010245c0001240305689640084200c074509442c10381c081240061420803560868011600659946001d01051074030004500034080d2a100b018105907002035810750381d011086003080d071500c0c2c030307000d5076a160360300d600050082c0c0140c0001d0300c0461070050310310160350098a411064000c1030702014200c85003902e4a000034400360408040d202d840f07082241c01031040000810b0385000c00166440702c800d06003a80c0e411200d00714201c60080c3d22031000c0c418006400603514081d0395000c0c16040c3d0781c44091902d40090300380c5505c1440c03046008020300180070761903089409100d42c030350f08440d030380740e60341c03008447d0b903d00060982c01140040000c9421026102c1c00d90440c10701c040e81140442520b080400e14007403120350480d80310b6560480602411540321144404a0800d103824441c41d0780 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 407808812 1250 407807562 407807593
    0xb04031404050d080309030403171c020703080a0f1b030504050c030f0703080f12040303020c010c030c050f030612030f0a0305100302061c0b040c020a0309050a0317030c0708040f03050f 81
    0xf261802a00341c0b60040000b490b05002002102c000c0e540c00050380303910003110001c9007126002102a900440d9891b080300314020303182d1091315072458255a84c4007003034403003407024801044000c0c404034800d5103d407100d03404103032012081c0c030040041d682c00140926241c1803a504040740700340094441d801810b0031041c5240d00003031400c140c0e034210301c0c019580c2c101c14201c40e106100d001c036042078883d9000c040000341034040e40600070344420f0000921500340d0800007102140e03188142c00d80800da0600c441091140d04c40081d580c40107000e00110b103c40c1e60719130354500c2d54220440e0407040042c00140410340c6641405440c0d0089036051036148024119030004140e13016801d4403a5490003040c0c4e42d0304905400c3c1e080440004c10160042007000c2400000075129410a141035001c1a00c0c1e100000b0303d810204004001c0303940003010954807407101300c00c15900350320140c010814164103000302c0c0302040c04000204000e240c02c001790044145186001400c00d482c1e0b6400301d2071038000c1031300d00c0500003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 407810062 1250 407808812 407808829
    0x303050901050907150c0b18060718120303060f09020c0708010b031c1707080a15081e1005010803130509060f10090b0f0901080c07110607020d0f0b0403140405 70
    0x11509210b407150703900402c5e13048452101070b110180408081205009180c568801c0c010020883c41058071101e80d034003030040c1c60909001d048088018085642008090203600ea06910701c0e200342340c00b15201d039032a20410440b12041d000300c85029030028401c040b2030340800c0508005c0440e07000901000000100107521245641e000d00c1000000c0001c01d51258800ca050b1040c008085400e103166003000040106969011195062a5031415498110504540300194101c0c0c04d854010442c0c034030501820540d804200403002514880c90030040e070781d0086401424080c005100c01552200540c1c01360700d04400f465400507002c0c070b1400051058a0701c4809890301c540c5001d9410f48100502d00d00c0407902c03c03482c2d034009200c0203808a000c00d21000448020440c81030241d84606a50f00ca140300744440303209071500100090510400e0700b40d43d062002c068a8990300050a80107070b40300b55225400e48030741c010800c40d007035003088003003008064006401040076a0b90144076400d1600b8200821501e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 407811312 1250 407810062 407810069
    0x80304021509060304051024090e01060e0106020a060b011403040b0c0c15040c05030f0d0e03031308010e1203010f051c0f031707050f04090e100203130303050901050907 74
    0xa4030700c440c56010251800301203489440c00900001d5413850681007094a6025103d50b40141906000444a00048680919121244681030412640c0c41d000c041b2004009401c0c8048655403030344000684400090b000c00c1c0242180e4025058200e034510300102143d00580c000b5051200e1f46440446e002d8404003500e6100c0d0f4040b440110613110016151000e000c1c8990951032442a00c80b01c2080541042e0041d01440c45010040e00c0161070f04100341e01c40141402d1000303183d00400100d00c00700c0c0b040032000813160b00503042d01d10b041c91810a0110b070300003e4102031310342e039150204004414020400c15070305200c01128141194140a41802d140d00c10340f00d0f66109004810200b010170040800c440c4a040d030000440003280b110f0703e006841080609003201c0106021f00020b80b156009030101c0c1d420355604010381e440c0900b4208240001d000d4503240200c1886581d020030a489014802140180c95040b4640d103480d41d2480c00070140e81008003058490b904207003d112a03d000042d04c1000d8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 407812562 1250 407811312 407811319
    0x6100b03042003070902041706040201140d060519080d140405101403041407080c100c080d06030302030d0f151202060d0528020c070e280b01090f0308030402 69
    0x845208640b4921801d20520150b4503009042c0002014403040d402801296410300e0303540c00c411b010440040e111001250042d002c00c5640031703c101e2109120008101c00c0c0c1514030000707440c0d51a0001b042d8003104d500720001400710b40070018807244c1d2040095885003480b52070240940400c0b6801030010703001d14030415000301ca084104210160145d240c0740c08602284100c545ca07480c180c1400ca1100d6058060302c6a14003580c0c4010500000216903007040280103409480103851441089682c1c20600300240d81c421070510141942d4600760090100450182e402581c540100003056000c070395900d2900c0b114545068000b211007024420710200312403541218103546501400810030b2845000005284545840704101b85594002c807051000d8a0300810400300480107030805e001c910171040e003025564800c1d03400300a10140421941d45c4080c0c005ea03000502c03e0840f85003007a01c0c0102009010942d10340c104688103581c00000032004080c4003d070a40b07050f1071500c5111182c40042c101901 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 407813812 1250 407812562 407812583
    0x50708010f0203040b090619020a0e060f0405010f091a070201091701050402010e1804170c0d0c1b081005063006100303080f0a0207020a0303030504020a09060b0a0507050703051e06100b0304 83
    0x10080d00440d50400c2e1642f02a10b060740d130314420001c8951680c45802100e01048401030603820a900c50f80d41e034010f65004245030400384051040c0748059802214049040154200f008140030b1452110189014515000800c0038105031001600403502410114000c40074411040c0d503081d040d0035255002500105c0d44920402c45141040041c8986800d04010f441801c100d100c803960311035111015140a00f00340e018420407007a4104a81d500c620400405602060f59414808a154021904034000a000c80388200c2d628403e00035034a2080034002c504420525008822001800380d00e500484000e8500316481c156600640980b00107020070782001008000288000c000760304540d0341c290000c1070382d60201c0e62442c00030098142110704a0152800110004010255000b100190794161041909056182608881d19040b405055541e40320309000000452024001300d4501d00d60018220180740e0541403170f40ca03103040a13040c0556503450341e1041046000d40d1040d281c0055000c44100c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 407815062 1250 407813812 407813827
    0x90b0a0e0f030f1b03190e0405041709011709030d060504050426130f090b030d0509191d010510080103050d050a120509010507111902010309050708010f0203040b09061902 75
    0x79a0803e800130a800036200020700c4001c80341c1c445a080100140540d01c51050f568034900313000c160364082d00c00504030014a22071020101b5800041c00703040344e040c50410080c04c80c18004215040d815107002026800010760840c01c02c2c02c40c0620b0001e080705860038805814250744090401001120b4080058010f20464492060300e4045035090498440746001198440300c050440100b144104800d20b490240310010909001c01c48400d0402d580c0c07146800c006802080c0076171100b885c05070160b450048880441c1168404d80c100044100035a0921040c1d030400080c004000140e1005505202521004000250000440c05105a502e103006074540003261015180c0040f00c0c0c003241c000030f01740410400e076990305500261040c0c22944c1d44990124003141d101d5101c2100049405200c004603d080e00903500a41001083d00c1c411011905016034440d10542100c0304a080460915000000e000c1400f6205984a4204000c04081e201a082c08030040070b01c8072000622078400d580103c0c010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 407816312 1250 407815062 407815087
    0x150c0304020a2309071704080a020307020d0602030901050718060e18090a0c06140d0b060708040603090309150e040b0a12080705010c030203090601060c020f04090b0a0e0f030f 77
    0x900404000101001d01410784041d001403603034000d0701d540a130040b0800514040e12495000d500d5500103a50294191074688031075845c0e0340601d0318681940f00412250380141c030341c0e040c1e400d83d1900a00c4010b8990804516484c01d4400181c20141084504034508000d01d24202c5c1c44811542e00381420511b0600351800f242080024a40c60494280d000c410031880c0030003c80c2540407030f440344500740c030740c952151401c2c2c811040f05040285e5103207090100c143c040e9401c0e402004003c2c00180358600340704c2190345000a076030194000100294541c7d032890105500b2041041c041d12105001e445260b2844000611f0522442466885103803101103030b211035120b02c03010601600804032844a6412903041c45940d6902c484800c846641c60406501a0144a84260303401460400040d01c3c45928000d41261240080d03e400da900c01c828507200b90f417560300d510403580e041d4851400c91045141c2200c1030402c4507400e40082c8415040ba102e00c2000220110441c1d400340606062180c540300c10000c6c0d03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 407817562 1250 407816312 407816329
    0x30905040e0a0b0714042d03150b0f06030c13080f01060e0901150303050d02390f030d0207080408030705010504050616020a0602071a0c0417150c030402 67
    0xe400900e0003840e49a8400045400060180241c2000a0f96140c002040f1030055800030301082c030160900c810700c404440712a00302a05028000d0a0b900c079006980c50b007004400382d44c4211040c40700b4091010784114940507408a60030304036403980e40d0710007600100304a031100030052030f01908001080d034940c4401102c11b00141041604881580302c1080b2480d000b0121800f074070f00050742410014001100c1400340184c040d124500c0c10660601d903983c10b9801d81c0081524000c43d07502445450000c001c403036004044034080e1001e0004510510b004c54001101c1c1080e42d0719503810100500d4070b030b035200100310b4203018085d8030010f030354040c01c0c2051007490103130380c220901074080001c0410510105410890049000b03000340e0741c4645070b8602000f01d185c81d100200001da0040d940e0400840d00c640c0c05400054010400a580c4a283d82c594480340003086035000c900a801003002d00011a250113800e201201d40e50003095580e082c6000c0300c01028008000422a0100000180454681000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 407818812 1250 407817562 407817569
    0x1412130c0e010f0e040807080702010c080d0b09010e15130e070b0d0605060304050d0825020d03050a020a1d0102030702090c1905090d03032c0a05070f0815040309 71
    0x41041056403141420501c01e1020300c50f00201d2203001c903001c290300134211900341c019940304048903d0850342e50745041031604101000da0521060000c207402007a5680000d00f1601381c0c030000002c0082800042000c200f070180c000c0c022421910302081106800d034030490494220441d07000101d0340c84c41c5042e030064003a142e107c0d9214024510000b0b0481c03010401340c07805815130b01c424000b05072140103000c440c0c00120380160055001e4170300300c0601c90148a01c3c1e60882c40c0d4407802a411621901c1c0000340402c41100f02c001039001c11601120683d040c81076540014810b14298501031001c140240345c0404015000b4502d00c01c1041c00c01180c0c000c00c2290740891b40981442d0035450090402c40980e00600c01c5003052011408400407014403e1013250b01d400d00003402110001101d840c1100182842e410145203221000140c010b03d03c0a5046086044c00c50310041005043e00d2074102d0800210b640003040004813a00d060008000c0031800c00d4015201044000c0c441da250304048034009256403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 407820062 1250 407818812 407818823
    0x6010e0f03030c031c090b070f03020403060e0312070201060f1a0c01051003030e030a0c0e041704140f0415030201210603030e09060d0221250302030607141213 70
    0x3d0007080b00d000200c040c001d10030807050440c05260300800450159544500001c00322400000004c1c0024003d16404004031480d1030700600f411b440b50380e10300803640c0381800c7c400644d102250b000e5040040d04ca48651010180c4020f1005510f0038125400c82c15841c000c80f40714645031548803605200a00945024404c00b00c002d20031400c210f119500c255007113020690000790300c861320180c1400c00080254013903900c11130300310032145040b05445c0e40341400351003180d000c103410072102054034542020300301a01c403401c00c0c400303018031040800c50003144a101040c0620300345204850382007040401c003802c8179020b090554414054542c000c02403d144054ae4662928200c40482070603440b02d60b005905406072070b10341182d1210420822540c0d4000c83c020741c0a0343d074100c032000482920302c25541c004400e4003101c200e403280426002c0c00c0c210031401807603141c1501d01c1c20400e519081282a400c01083c1c24440072208800b000b81c1302e14131030003440c0c2120019103808210540409001180f82a0708038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 407821312 1250 407820062 407820067
    0x1416111b0103140115080a0c050417190305270d08030405030c012a11100e070305060a0911060f03150a0503030a0c030201050115020c0d111512180606010e0f0303 71
    0x110b1060b280031100145d4580010b1000700040d2240c1f1461080300f00c0c0c11016201d450509291a103000551008031403040c215000f0041004004120131050003400c1d40f282c2c072151388070010180d94040c001c03c21441e2404080d450403800340c4d540c4039005021886604421007039074941e61390420b2483c2d032240722035800c62503107031a841b091150341e0641407610340070085143d244024a01001146c581501e1088003107903800c2760071043c150b0011079111f59007140140003510100c0b0b41c2c0f51503060419400b00c4443c80419240c1116408205c03c1e408502602da0741110420301b0211084100700c06400018882a55508250040302e525510313485100c00400004003200c0d500d10300100700038145080c1e007000f1400356007008008241c031118440b00501c203a85076402020500d40c08406c02c45c1c045003c2009807002e048030348074040d0946552005104070030b05400c4195483d65007040503580318200802c0d0804500c05420210303805139020500c40e4100708240303060f44079500a8000a08420318121440f035051000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 407822562 1250 407821312 407821319
    0xc0b030c04081504031d011101020a0201020301090608030c1f060b07031e0e0310021b070b070327261911090105150c01060305011416111b01031401 65
    0x220020000d40301850183c560040401182c00004102540e000f07000c40e800302e900e034250003140c001c07096070140145810303102070404505890072a44009118001070b50004014000f080c8540910720081815a005616046042c106e044d1214000c40078104071250140c00d040e40740204da000f2070050204980301c960b070340c882440c0217051032040c0c44142c902403199102c1400c80e58001c81c074503d442b5402401500002091003c49002540f203003000c43c042070340c8180741040e0078038104281c02c050700f403a103441d9039140043c0c100507000328a144051280002c000400200c10946030040390100c621480e40b0003821384554100b5000c0c090742d00c0381c0052600c60700c100100e0b0000ea8501c0020700c00d00442280e80080c20308000d20041241c240034098002003400c0c984440f100301e04005142a580d042e0000034515240c1c0d950600359041444000740884984003030021200008070117040001207810401c480e0440203526503140e154181c52010100303180d4114801d0f0f80d010390024801e150300d41c000b95170603685 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 407823812 1250 407822562 407822581
    0x90705040f0504110306010f0504020703020f07030f03120b010f0c0203010207121d0103020c06220c03050d0815030c04021e0d0510170c041e020c010c080a1103040f0c0b03 75
    0x444040c0c13201c100c0ca08044005060204601f41610300400d1500005401c04060102940c800c041c101d085120b0009401604c0d88140b200c02c0c061842224405121030190600415100d014248081d0729490030a400c000f90713812216508030b1380000c0c1004000c1100e039000081c024003e411000e000800000c0c2c00c03010706076000045030007c2c01400c650120352070080004400302c0c00b602c1e040a80729806a4046540315072888021304115548103103035101c402d001da4418035000c80301d50007191142c1c031075402c0e51006c0750040d07200c1c1e903c06140c0001d200015a1007000954030001542c1440c05650b00103104948242d10705520034985a040c090340d80c2c1d500301d10045c0300c0101401c640b4080241c0b0000404910801049071040000402030002e060080b002400c21000b8000301d0b06c804e0248421059400e040c1050380042c04030495068000928408001405403d20000a2880c2d0800d480e06c102e003400040c00c0c0c820f0700d82141c3c10041c10300e0745075903e1400d804100300d19000f40c0c0c00c4075030220801c42d407082d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 407825062 1250 407823812 407823821
    0x1f0609020c061b12040620040b0a02060a2a02031608070611070f0611270406080d09060e0d020a0f091a0603010306020a0c060f0b24090603090705040f 66
    0x20b0a48840007040e410120080f07050240d0310004010704c0340800414049006d5410800340c030043d00100b95841c54210716200140c1d0b1081d840006642404219148810340500100340d000d4183d410900c14960040b101d02c4070b15050007017034840404040c0c06051014801c1041d07c0c215001c0b03c0c80d452843c40700741400341181d0071440d811500a801d21808205031071810003695212070f408045609041007a95a14010701410f40c0e441c4401a028840c0b101c0c10000c1c2031002c0f402c2081c0d00165180f200b01402800103454103600035030b01c0e40d8020020700c0348990b84200001e08880d024035280d6003c3c080c0200040f681c0c2000c40c0040c0d03015400c020302103021419121840704484000c9001c105030404505500c03c65002c100c420750f800042800100045003081e0024490303a0140d00d00b00320301e00007607510082124458808410202e5a507024110142000c2c4890f9441c1740404464600083c4c9000880c40140b08035012180190800300110313100510800803800034180041003409101d038503881120080 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 407826312 1250 407825062 407825071
    0x50c07080d110f0d0923100e030606041103060d02030c0a03060507090f05060f2104060218040e03180d06020c0309130209100305100b070b0717091f0609020c06 70
    0xd00a8446a90b20f4400000700c030360250030140c5508a015183c40c80400403100e032441c0d150a00424240c1d01d840366a1200c020b030f184c40266803640c450491044052501e80500241404d0082e450400e086162546034420740398440002c58000b203120046202107030a140400030200d40012180c04040304100140e00043d11525556558085c0556123100b5156050804d00c10150020410040002081c81910043c017003040010101404529274100c1660301c07038021641a9a030395808569105540e102e1002514094022039043c40031700c02d82d407487d41d2644100c003418200790a890070711003040d40b2038800801c00284c000704115120303200002440d85036480841004c1c4680b00c801100d60403a400b5100307440700010080c1c468103012100135816402854041c104000c2d1000b60900000d566290388000c0c8445403040880320054100128041c0c08040c00c40d011468410343c420422217500343c0000c181c46240303419025900400c1650510b10000d003400d4200d1440d080c000110803000b07000014500b4000c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 407827562 1250 407826312 407826347
    0x130e04030f021b0402030411030f0f010605030a03120b01020f0303070903020a0b03011511010b031f06170a061802090a050403021e0c01030e07170703170415050c07080d 74
    0x10545008a07100c551418420f030503c0c20400c001e11040c10158095680244104c00304801e400151000a282024554018503598031500340d24200a40a0007904d00030101600144840506642c000d4038102001503482c0c031a07582c8140100702a03100304035125481d20240d00343ea030740341011800242414024001640200300c06040024010b500f44100d904035031000e102120b20b4007000740211242d0002c05901742d80c0c2d6403910201e212540d01480344142c5201010344408140d00540680c10660f15a0b41c840702c0e084584620f00010050701080000380b01e50b01a00c00600480542001e207020250301030081d4000800000b0071020700600e80c003060003640644c0840f0021184c0368000343d400b1a401ca0800790503006005089400d5000c5d80040450f034083e0019568510b88030701600c0c2e07100c0b040c0c44070076490b03a002180c1001484606a200600b2030610120a0702d09401c1100d08000000c1140b48101005030000d00445000401e05c9007002505002054410190289400918880c14079480052 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 407828812 1250 407827562 407827577
    0x70b040501060b03060907180b040909030305010806060105041205030d11180f0a05010e13050901020a142502062206030c0215010608060d0c06021606050306090f060303130e0403 78
    0x4030000c3c040d05584c4030781001451010143c2d984001281ca0482119052001140543d40171503045d4040e406000a000301c2540060010142d060003800d0b07400681c890842500440c05115050740d21030b080f142560b08802c103007911440d803441c100d881c62284102ca0040c10b40380007034102c00b4401c40801407494000300720021295001440401049070300403980700d0303071040030b82d00708000d1540260070440046400038484c0c4001344109583c00305560003100c2c81c80e00e076540040c0c150505170704185000413030304411a0b2142041840c00c0304a045480501c06481c1a102525207102195a020103e894158600c04100002030000280b511440d94600407000400d0400c4000c49031303c0c0c03002074031120380c03440f15481e101664078029054449400c0070f40070980010040d5401c4000c5158003100100610f800d90080c0f81030382c0228410000400a0380281e01007210030030178070130030399036400c45d5640040088a900c07101d0f4a4000019241d4804d9942080c1031012781d607000a0211021b4088510960081c2c50306074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 407830062 1250 407828812 407828819
    0x5040b0103021303020f03030706020c06010f120305030a1e020c060118140609040201020a02090709080d08150111012304170408071202010504090603051e0304140103020c0111070b04050106 83
    0x103003039006043d004042c021400d4001c002600c3c000b03d05c0c210b0a070020b401c0c1c0e0b15003007541c1c80b02000d982c0980d0048407654844401089416801c0902d0320040820f920030300b942d8038099030010940d20001e41007840182d00c8041c03102084d020009030f10200c60700010215a2008141e417a142c4500d000d11909405002518818a04411034003644110711030031350080b50740341d694004103c442c1001070030903030442c40b601c1450001a10f0741c0b1381d19070040b60181c42e1002c000703143c03000c014a0608190000c2007084080d074240000001c69480c1421000b80900300302c1000c074200ca00190040003a50f22014402065000c5002605c00c1007102174000c1c3e000d2041d220300b11008001100c03080c85544a14021030748080070800000013200c800c54007580c0705140c181e00d4290344410a500740da805030020303036458010940301c2c8007144180c040c9942c8181c1e0040550b007003034540060702941c0d804040740e02d81070680001c6c5001644100394841d42c06040704040c01d54586406040c60005100e04845c222425840c6c605c010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 407831312 1250 407830062 407830067
    0x6060b031609080d050d090f020a030803011505072f0306010f1e030c0b030c070204050109141014280e0403140c07050105090f0904060e011401030206040611190302010605040b01 78
    0x11201a4465120f1626102241e038580b0014035480787e090382c803080b0041d15280107954280e21b120080d40603004641e200c1d410302c40248030b0040e01450714000d1150402c5884000b0787e1803d030020700314a00c009404c54000141826007003c6040c500e085616020f200008110740c40d400034800250362800807010700643d00c400401520075458040a8100b1090240810805580400a41e8018908106641060741c180d0105007983c50a070000f59000352121610305901d4003003071385598007000c0c1d103166524032850704402003403650310105518050000e03581d081c4900d401e150214018941c041c00c88008044c1d840840d0440c500701501d0840c00104420407449013040d0550039200c5102d0002d020744165807410005580550183c42e889401c400310005a510300e981d00814140300341e00811011550f42d110b280c10300d00b100c141d040d0200041c02c5902c01400036031520801d0350182c840500b441d0707440f800780c00042072504e2007860040d2407482d54070482e5010154190425000c5034010303907081c0300401525005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 407832562 1250 407831312 407831323
    0xf03030108070b0c061803041d0103061406090415090f0b01050108090303040804060507033005011203050319021204030e03010501090605091314070b04030210020706020a03030906060b03160908 85
    0x240d08140c0d2201000c030341b0500e0300c901d90139907091031b100459190680c3c40480745001428811072030300307002501004005010f080d000b91480340030304a6001181b0f10704a00082d18210000c2c001801c481d040019002002d85207a01c000541d135044814603140c42c010b4034101c0700c1d4030300034040ca500007251030300412100c02c2d0000a0341e008503403021031a810181030143c03c540c240c11109040d000c105e2010544490b540032019413951581c50500d801d8500741c000000ca00640364180d2110000c08001e010200119a2042c10b03290020125414680e0300302c1e61403641001303805004079440f80d128202d0140000c0641110401d5400c08065000b8030480c0c0c0c3c0e0340102000c6400c144a15900b0120b40400611407601d070503c0800710714401c000f088417202c659000c0350f107480c116400000d039410300000c0910661524803160b541d0341e141440103210b203d0800d030000b5154014035000805141c0c0b503040890400541b82c1000020f41004034050f902c1e0b1400e443c401d0f082d14203020142e408102d401c0004500d03640302060 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 407833812 1250 407832562 407832577
    0x721061d03120402191e0503030f04050402030a0e03030903040815060a29030c0c0c0613030f0f02102601050f0607050c03030a0302130603090308040809120f03030108070b 75
    0x99402c200300040940000d0780010812640226417034103040c9410142c0301010060b2190f00c3e480481d404005000418040042d0802d510990051240260400e4100200c0701680c81c01c0d140541c481d151210b10350302804462021100601010040106661000002e007044030300d50310880300d0004820f00407000000061724116002513142b64140103000391140215403802580c9032000580e807503042407803099007003038540380b0102c00c00081c2c10000769010803980c400444102d64444c07030010b1011040043c8016072000800203610703c071040c42408851940900041e4000c1c1030400c0005c2c030030000400c140c4001100155008e2001d1179101c030030000c14000b0b4142c91014155441d40c80300310f41085155040140c08540c64403d60307148024540b000e0014204040d101d450260b102d202d44140300c008209140c100c40105441d100d05440429403045801e50890781249003240e81300150408600c96a01d2620003917410b2150040c00600301e07200100a50480304101e0640e10469100c9114140901c01c5c0503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 407835062 1250 407833812 407833871
    0x4060c020a060e0a1a070b0115020d14040e06030304091103070305180a060b04021b0a12050a021209060c190b161707020f0d111501080d0e03072106 65
    0x2001031280c01c0c5e001c0c0341455500340c00811182816856036859000f807500760024071030a80b03010030700350445404114101c008405420208115400d02d4100c070307150f000e907110701508802028041109030303c0a104940103440c00410500c040c07140007954200690054800400292038040001d10192410b4101c1c1d11880c403050141c09404090f440320030281c00126415680582e00301300b003040000028400c144440e1000d805800038003d2401c0a10080015248a0061103400c2001001e900d50208040078070403149107035039840d0041640850b100c0d000b4002071014612a000001c000d441084600c4440e891091124408580c0c1e51040c80d40c80b03280c24070341c09000c14001c00c0a24a4081e034054450750004042c81214855030000482c0c1d441d000351355400c40c0c0130804801510220143c1484038203180128010404240d51400904c143c0c2e0381c13501140f40c003c2017400f411a5078265020f0001400400c0e21034030561600c00501072180c50000540781c1243c1d0300745410710b894800c4c00704103120211040c460 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 407836312 1250 407835062 407835079
    0x306150c1c05130e0612010603170a09031a1f0503190609240c0309030509060706060e070324210812070f020105060901030c060e031204060c020a060e 66
    0x4a40c038504100e160703a15801e015092054440600c44401804001c1c200081340284034100942800003001e07001c0c50b400d4669050420610200d80d164455440c2011001403c642c0c0b41c2c540701049400100c0d94200604544034204c800c000041c000003464090b6112204079050681c01d62140e40c1c1040f0288a1329401d6040300e9032881c0c400c90014569042140100000b00e92a4410380d241c051003403164140b980c9021034181111050340052090f00c1094009040401c2808081d86028055001ba010001e100740303000150380301080f44a410500050043d450203502905042c078015019000543e5480c1c0e0085a14411008901c0640c030404d045400500da04046001034102403030580300074200560b0990800c12444d454507284074582da01c40d4000d40c4e0f8000012402d524002d003562800741c20103100e400c981c00103101090300600041c00709c41142c2004414810314001203424400d00125080300b032200450700284d2290030a4803148460710032100c00c1c08168960500340c2e003d4900036421390304901c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 407837562 1250 407836312 407836333
    0x3030f020f060126100905030406080c070302070317190e03010f140103060c020a08120609060103140a0f14040f0b0c03070203040e060a0302041a03061819140601030303020306150c 79
    0x1d11306152001180e20003507801c10101140510701391165400202c44a5000242c10445250f10908054001038088500392400c222510000e545d48168040078100da04190b849100c010011000c07a081d96048070044a030114040e00d002d0003200f84000698080e5081c00e82e40c0b041012144100c2c1d001c2d190001d55655240d08640340d40d0024480e0518000a510800440d0808558614050911131824800340342d031500d0040c01340020343c000584914103041c00c202c0390140781303840e6200c8290301c208104070000e0100700c95103806000e000b405030803c480011020510060044d6100a508030740d01900380d0007125141d003031302141280b20071190f040c0180c00078082400110407803a46030ba00100020501518145c90ba00002e0031a10100d030303241c4501e80400607881040c1000c0c40b031076a011a09010140f8007540c0b40320503648421400400c0103071100714140407020003152108210481250000711a01e86d0b8403403074058003c0d80305503010741c400c2c00c0809a0b480320103a40c00c02c84010b021a8009084203000c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 407838812 1250 407837562 407837609
    0xd09080d0e09041217010803130e0f0a0504081303052b0504060f020c04061e0e06010509040b060c1501170307030c0b07030f0c020d09050d081b0a0c03030f020f0601 72
    0x6124418080080c00000d00b840517880c140d5440c086d0a098000d1940c5580c04009041c42e0f00c000d5004020181c3c00108001c5481d01e441c0794980d005908000c00309103591203280c42440b41c4510b0384a8040b202c4c000001006010300011030807500741e002003081d81c2c43c41034004002129040303004150700117072003000103002007440313805204030011702d500440312124a9500001c058034004d410025012321040b05031000c90a000700203600615000b4003100803414581e00007840e910078011414010b58407462142c01c191505000c40b002010100241c038201c118032268051840c00078130851100754036021080703103034010100c1290301d083da1644403a2610041c40e90340541c041c9004040300281356440c0210464600e46000d40c1c130303000310160b000c0c007642c1d001d10b103000d410050142c0090340640d071954041b00004400c0d40031914a000c195666105040c2008585480c0004009000f48450700f1a03800004047d044421403150700c92a8003516415101d90000940d1140c007403082d6807218024040c0004600c6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 407840062 1250 407838812 407838833
    0x736060507030c02150a080a14010902091c0605090708060f0f0a09050601030309170105060d020409020a03140c01030b010507020d021e0a0b030a1805101104080d09080d0e0904 77
    0x244281081103d20341c098000905030b4066800700c403a003103000140c0e018079540c0071900a80c40051148204042241101044041141400b8952507035500148440541e030714002c0b000684101350321445204942440c2c220090401580c07a0780041c402c1d500c01003547c0d80b0210b04140300702400d01c091212039541c4071a4078441540605240c80c41e61f42da2041c980482c90034888540031358002d84880d841c0e2071601c1d0603505950007080b000b0916924040c18031034940d079280580d000503901220b001c00c5040c45400018034a041941c401060302d18002c404001d506804541128404000d803010010811703a0001500c5510030204002d40c0300c600429005d0062900e1030791030781e510200e00c070304581d102107141c0032400d02030a40c0c05c003400507c4048108500300c0e040c2e001e0202440c000e18180d0701011010380d40e183c3d4400040d020f6019558a03004200c602480503010749000f010072104903203030031300b10740b60190010100d0300503c0194010708070849030483c09419038211040e805010b50b0411b03902e94aa100020 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 407841312 1250 407840062 407840077
    0x806040203130609030804020319082a10060503011a0d0b151009030b011d040b07020a06020d050603070512100207140105010f140123030a060b0307360605 68
    0x460b030001c0300c0114540703200d40e2142c0c070f2007078552040d43d04082c0100740c43d103042101d40c0c0c800c01142c0032560000a8605c000d80305050b80c0c01303c48903822450700c62644081204504180214416041140e4400080b03800c2203044400990080007003005018440701d010511521054024130a01203000c001102410b044d5800f02888524120a08034440015808416901800c0009191040520610414502507401056034400c5223041d80084480d400c14050000e001500c0006500005001079001b403003000540c941c04002150f5035000c654003e0300030003007520410b00902c640e074004150390501d02448420006244001c00c5103281c158240006540300400881d402615400c001c1c80c050400d000e101d02811000c02046909418403c1e0480002d1070320020038100180702c2d410101120412924491120220340c125079269580c070180c001030b082c2a80300c2e140d400000020031003980e90141c840000f0910720340010f07030303525995038054010540030005001c40c5034901100b0030046011b0303001410364 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 407842562 1250 407841312 407841331
    0xe010c0620040504271511030c04090b03010b01021209030102160507060f05210c070219060f0c0c0e04170708030103030e3f062e060806040203 63
    0x4407050003121003485940c1e030920000420000c103041c44145014000c0e100c03000300c626400d8110007031807402c0b2104028003036400782484c201c80384c0ca20564801900012000c00d0014200360303580c20948594540e0380c0c0580724040f05103107800d50b800220302e0107000b21040b84005a0081400b0f44101d4210400d60b403240c0314540e4599800c1007001803002010580ea40110b0088010300030142c54400c0c00b804130201020b41401300041088110135242031000901d070900b05e0340c4807a681641d220075030112903101e1650003035400081c0309040c1d500c0c02030007407442081d01d0450365480c41c21080100103035aa0002000c0080140b000307528240300c02e4001246442d8424003c0045682c081c0703900714000415404440c0a130303510800000180103250304039240300800d9009440e0004d0741d0321b04000d0440e40f69a05140c2c00d0180c00700d000070070154a000003ea220304072502003658a24200b121394014001c40074441101414050100b02060f0306100d4000300031100389845e02c040e42c3d5200420400250700040c90001d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 407843812 1250 407842562 407842571
    0x515040f03061b02030708040b070215070b15060703080c0306061909030c061103090108040303020c01020c0619050c03220f060c030b04050108030d0e01020405030609030406030507020705010e010c06 87
    0x2065000d40034124011401003800240c42d55455414518a5124480b21010b6600030007420000902107801c40b4100c178903041c103154583c100c5200141c4c88440c02101200420030100f42001803207001c8804038020b071548005000383e0503e80050200901030048083e000c2080c0f40c0c00a440c50b20704000a550100004041d1454803146074210003454030340e5405c80000442500080c42003054440315100681040d040000e00e4410510791307141d072032003091313007050401c030f0810082000c0600079015500700b540714034000d648460314000c0c9260749010072110005003009010008034011000d1142c2c1b0302401425a0061030341d5149111004148089051744605058150070600405e04060001510601c9a800464180410f40300101552a00f004003407041d4900710040004480c00000c0703034442c11100f1004514440320a00c400c0c0240110b07401075405029140400800540c00b00c020300642c1d1094800f000240c40300c44080ba0303141300c00e00074103000c1804104003251660190101c81380c4503201d49030126 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 407845062 1250 407843812 407843819
    0x2102030a020a06020d02011103040c0b0904290306060409081603051207121505030c010c0206040e0705030f07051305011220031603090f02060c150405061006031401051504 75
    0x1201000b1651020005030004105d42d80d0082d030a01172501810424901f43c1c2c154149912554000001442032900b00000003c2c0ca800d503840d40d401c4051504041c442c0e403440ca80501101000c030b00c10480b44207200e405050001801460288208038905802880c46820306012801183c11410142d4059041c001c00740204028000883c000c21b200d40c8035544e40d48041c2c0030400700c8400361180112422529070001d0814403d03520009081500880d00f441c02d0b10624401c4d00200b122445039030040380490323440d1800c014540760081c00542c050310382e64441d0501662613030300c00c0fa1280a100904da0a030074120000300041d40c8149042c0b60114841400080c202c5000590234005c104829107003180c102021003044051568101500007007401403c007400f0444481d03544030b20180030050f009208210221f030400e403499041140c0f00814003004410041030410313041040d0f0f03072401103a1075030f4128220074000c500c682c400e002e840103100541c4407030100ca9080c00e080115140d590b504150a0000a00000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 407846312 1250 407845062 407845069
    0x5030d0f05041e0c0b0c0312070e0102100f1107050c0f0108090a020621090109030908070e0c030a11070302160911270d03050403051005131212110c070501092102030a02 74
    0x90807103980b5031004581c1d4402c6660140001d00c8c00038802818400c01c11140e03021640c0203d4400418460307444000780c1c443c01281d00100a00306010081c80c00e55011581d40c0c100700c00001d144034411401c8582003811038034040112441001100c41c414503401403020100141040340c041c040c211061204801c0c441d940325030845a144c411110480107a44925510081c107801003220401303021480c0140202500b413500c01540344034050002c0003103010001c00554124450b130300200c8441e1039400329a58912160030002e6a911b0350382010400001c1c08035000520440d00e205086000e02ca4030f502d281800700c3c1080031041500c8548520090501c8001c07076140c0c0d955101e0100d0036491103615000d0f105c0341903003092032802018000301002146402d00b482040c1c51140e0740d2301d00c4079600400c5010141e161510848655403240000f0104038284544000210481341c00351180c4401c4100302c0b04000e40d64001101c070801e01c2d20403000309180c41141d500419000391406100b890025040700c00d041e1495020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 407847562 1250 407846312 407846317
    0xa0207060e01021201140d030804140303070f020609150105010c02010e030601080d0314150607140313090b01080f060d05161401170f0a05040302010f060305030d0f05041e0c0b 77
    0x1200c41d0b95001500002044000410034090400703103c891407030300e4200f80401c1100e4034449000d020312480d10b000808000c04141e5015040100b4000d0300c0c0c0f2410700500c00340081005001210160044200045a20070001070031240100c001003407421360703407030803005440104800e40164104426202104141c1c2c03003c02000d402451240f0003003409075010403004007160346400144102190400a01c4002483c11b641c4122000048410300d66a481d07034684020010b07440e6604034041c0c08049410032a1040d520341d500110b1b080c10707000740b1407540d40d21300440d4039940494274844c40b04914004246542051310791015a503101e842141d451422031078040c00020701a43c41040404021403a4950b076503402102280054101c421840c0e46040c00da0075929500001000601c025646100103030030b0501c00d40160717900903400b803000c0100c01c0c0c40341041d40d2079034070042c42001c0311381c01c07c0d40d40c20800000388540343c403846d04090f4109801c41500c0001c2d008603103d25013a41e010b401c40c00041045801d6200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 407848812 1250 407847562 407847581
    0xe0c031506030c0105071703070c0c03200301020a09140a08030d021b03031003080304030c0218070f0f0c201306030b07030903020c13060f0b310308030a020706 70
    0x210562601c1c10108052400180040044c10000d06100d0140003464400014021342040c03590142c481d65160b504452074a10f1820140400120390400024002000c1c45ca4490100c03414111400c03015400070300d0300703078898525110002034009104000030700504012030052523005080c3c480c5a60b8554405145030049451030fa00e2560000300405ca00181040e80c1c20310380300c030740050b5095190248800d44444000d02c0042e103401c400000042c100745c403c8540c000403e60050043c80c2c1d241118106002c3d501c01100d07920301241322440000c22481c0290f401070100e04450f96102039074085075945841c0500b5045c580c00080c0b500604600c1c65a031880040d1405a03541c11002940920318101104440c03009050201418648259440882e074040380104503400c041e548040700080e040c5501d002410070343e0180c20160034000010604201d040000c01d00d10390b441c55002c4854004640d900442520000001006030920740b081002a218101a44d0300001038103005003811301540f1b03802c0550f00b50b80c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 407850062 1250 407848812 407848843
    0x212070b0408010b040e010b0d110406180e0c1f1808034026010c18090c0807111510050915090612010209030d1e05130303030e0c03 58
    0x10420700e9503080c1032142c06c4a008000e4000e0001c519410041101e80c4e60100028209903010064105a521a41c000400910003482001d02d00301d10220940002c02e40420b40150500400c400c9041c20310301911103800440b1200071245402c1c2030320703205a0381707031140d00140302c1d02103110200092840070900103041840c0448515a01e80003100d50701c0b44080b107074040e06c403000d040c0c21180702e1841507031388401c00b0036100000d101c03c00829100079003c2054801c1100c051456082c82c0d030f04600140e00080078008400140741ca525107944405034002650b8044010b900041c140c80005800c0034400d900c402c100c0722401c3c00382d0300329420100e00c1d0116950211094008401220401c0007141418000258000310046461142d540344d100029924540036040a11907100003900c024480380a504660b02100c000382100e0b03040e60607030006001c1e80b80e0392810415440541c410001e00502032003c031080400d41001e05800641583e600b07400602022030400400e1083c9a00e1690940307080080201c05010030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 407851312 1250 407850062 407850071
    0x17010b0904090b1e0f0421020f0f0102180a05060f0307110a0b01060906170402130e15040204060614160314030406091502040b1905070813030501050c070503070212070b040801 77
    0xa04d03000c9909038050f2154007101400400c12000c5405100044c154820f080104126411403010407480c0c0395518040b18120300030341c401c190f50721105500600343c215400640c00e001004090400003404107605c01e00390800301c1080140303010328402000b5070b0310002504100c1d8074262a550060b00d462400c6000302c1712101010014800c01e90402e003040c0040840707162007000ca08103c10506040c250140c00207000740e0951600400740001900b00c9400148075004460009104524600d1000c0c030503141a80a40d01d0510045541da1141a40803041303020b05020310316200d03040c3d410340d1060308101410780420000700f0148801120b80c1e0f008500503801401c000c1190a800d061030f20b03c10b114010801c2c0e015104000070403402022100b030383c0807945034104034403a0b07041ca440182d49500c5503003802000114005440000b03a03000029807400e032800343d80200450f0390ba218079034109108810000d0000d038402c0c0071500c01031905400140c2400f0415007500c034101d613160700f074020a13086500402c0e4143d468 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 407852562 1250 407851312 407851351
    0x803010608090c0909190303062d1d0106080c0f04080a0204050108070f0b0d11070f05061b04050d020f04110703080f0f07051e0f04030b0717010b0904090b 68
    0xf0041843c083c0000c650036a61420b1100c0c209541d020407460031000700c402c0c000c010082c1406a4044802000c0c07403010080f00d43d44082e41c80300c1c409000d14101c84100e689140c086003001002000b41030805061441a400f030342002c40c1558008401401000e1204007007107001070720301c004809000100403400003800700c40f900344108419204160801c002c40d510114007040300c02d440000039801c4440c1040342030383d0b0340800d4107144090184405000d00300c0000184040c200308081c510070384028041c0040e078001d81c030b51003000c40c1100305803090b10200c4d52081c801405580303040c05c044407103181b004209034401d40092000c01c040d2100ca811907580b806012404000f807541050080e640700d1a840350011180c80c14004013211013038041c19120070003001103104112849408846009880704a883c0d94849903a0410800c09500a02003255803682d0000440c0d0428041c101d12059007901819032016a0b0070301c094405590000c4074856070013a141c0b50380380c02040170ba280190042040644030360320b9050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 407853812 1250 407852562 407852581
    0xa08130618060509150c0a0e030f03040f0e0609010b1605010c03050a0c0903080a0c0203150906041203020c0a0611130906050a150914061c1505030d02060a02030709030803010608 78
    0x2800c0104c02d030002d0310300364000c004041034182d211038100840c1c2d48a01d02d90408440121825820940612884144440081c0c0010103001152000c050f160011600c5003034000ca8607030295640ea030011554401030000e221171201800014580410b8081e066805880340d5094841c0303003400c0404660b0f01e50600660f2096405201c40101203030411080d13071491039940500e9403007006607600401840c032418a04541e002c3c0400003442284203010706107424030a080c00c0d1070b40d006840c00c994032848108484080d600900942d0105034211001e81a408500d44404001d07144010f0030380c00007407041040c0504200810312010107443c001000094070390410713044c004082081d40040320580b405800050351103510007071a101380c4014414421201c6904004204503000700c41c960030105e0f0f48032501e42d204548943c04000300070038030010311440a9482081c192109084101c01e4016080000001d51000450b00111b4004000e17281c49007070503a0340d80351050241c000f0381200000400d02002c1c041c03500d0303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 407855062 1250 407853812 407853821
    0x60d0827011404050427050313050a030f060908040b0409152108070309050d030305100e0106091e09090f05070b031e13021002070501110f030a0813061806 68
    0x5001e007000d980c51161040b008605020700c1c4242403296403250a0740d4082842a142144400002200800d0481082c40c010b40c0325080b01141442e22601d000e8000780c3c03071400b240d0440440390000d00200418071561201c0c0050504104103448022080100141101c0104003c10060040107000540f07102c081c0c140b00074401e0240e00c0900500c81e802c0d180d000005d00700300800e44881d0f000602d50b90b034406c245400c0e1018001c41d80030b50780c0440c60300c07040f0041c143c068110074425242084200c4403075071503e803403c62610080c0207100008400482c10b02014841c070041109650f0341100c60188503654201030b00035500316883c222000240c43c964141000307020081078010300040100c41e404c62905c558094050441d6081c0c16984142d84170201c0c000b80c5695240c0c10344c098000c0c00c00c4101a42c0004081d40d02c00346445060300103130450555001002000c16031440040c011009103150204040c0c0445900301e01038503004100e2044000d102c00603a5922409668042000000c9448003003410040102c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 407856312 1250 407855062 407855137
    0x50c120c030f06060609010f03060503070b0d0e07140f01090f030515090309030d031806091101110313090903050f0a0806090a020a090302041505030601080102040905070c1a060d08 79
    0x9a10480910843d03a882000303803030384801b00f0f1800341e420605404084014008951207141c045c029808045084d800d110010022462441c0c1e09100c4d42a12a18095450407144158683d06c050715010720403602e0030030b001210300e074014174110740b98544410740d003001e00403198422142030344507008400c1810001100b450388050000301560034001108017280d11408600022805c065a54043d00710290b00301c024106019000041005a40d001d031900200764512041c102e8042012040c44000306000001207911140600d440d0742d40c01440c01c2c81540280903902c604605100e024000c280c1c00080c080e002d00030b0381a40d50b442c0e84c1e1a08040c23080c0800204040d000854841c01040b0b1600000d802c200c481c01203070b5050701d000a83c07a00d00402e0f1803880c8205d40055505003d260000209050150068010707210707000810001520b401c1d07010741c4c101410381c5000340549106564265a055442c1607643e2000300940040c40c80303403d0395038440d080da10001c0d080085821b81c804110760301940312040c8128 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 407857562 1250 407856312 407856343
    0x706140414060106120f0e0d0207060e0a060e040c0203360a05011d041104090509070504051e0604020d090b0f0903030919020604030501060807140a150309050c120c03 73
    0x9550500800429400d0303440003105605844454130306d984200c07a4000c0d0f044581c0f142c02c1d100c050f000040001c5d100c2c0954405e040000300242d100e50780368548200f44100700c6160b611582190020f0b80244000341a81408800941c0001e2103485506000780640d0820031100b291a0030405204400205049041648503409164050307400c0c0110390f04010f10800104900d40000303100d42080c00050040c0102ca0030141c0d502e080402c002540307508030740100d03008007141030559203440e03113074010303c021600112030807041814481d12941c5200c0d01981070903001540600b01514281d002c080f10341c240c4100203021200c22a400c805c0142c03010074000740380d8010603018003a40c81d508001c8442c517611425680c00038156261210040c0c119a124822136000710760000003844115036070600d0a8480905200d00c4407540c108141340c17581860984110001d0b04d0f444c05103c0c1100545020882c01428456001c036440c7c85400c3c4141c030150f68100a5403000d5141800404120f084001072504160320031704078400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 407858812 1250 407857562 407857573
    0x9010612020415150c060b030a0f08032a0c0c0d0c1403070509040503030f1602031e0c060412020d23090d0611070309060e0108010302040209060706140414 68
    0x301205800448202680407100443c0507115902043c900b50301c1a0310621410811031940c1c45841e0304021140c599900400040120304800010b05440c0d04818000810000071810100000b030541c0d00a941c001d2a500b170200400101d03003550741c190181c08034075010f9000e00810122001e00d0200126014400c06644d100c01c0c9182907616403241e082d0342d002d40d21242d00c40c0c4007803003a2a142003280390004d0030700921628007400c0c2410255260780c030a40b140003c0069150008107050325002d0004202001d99000310719188803890306e00e82c003070a0032001d81540c1000b003001d00720030078041150038001ca01491800c07a001400003406031074914080591424041c030410b240780400320448840182c2c04c0c400c0c02840c2d9031b00f8603400194900c20b0108000380141d181c0311102e55110340340300c05041c1c00c0c1c0c8a6140c0d80589a110b00050361140713039203143c03140040c5000c001400181000d8018001000d0060b007051b0420003655103039815110640d1154421110490401050043c031068910495901d00050328 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 407860062 1250 407858812 407858819
    0x311190b011d15181f270f06090c08070e040b0a1403031903051506040e06010e040f091b0e01060c0b04031e0e01030c11030d0905150c040e090106 64
    0x5665000815000c0b40d40c01c440d910f40381e9030301c40781e080f614240801c6502020510344041500206251292400d00b0150b001402040b100d1501040032040030706904e010503007170000300d00e0001510b01600f01c0b000d91510b500e07000420b020340d40926000e40010307480e000038174580341074020f0001d04d1107182036201d642091400005034607401c04e4941a00c082e4039551042403801c0c07020a155114a0300103c40582d8402545001694164405401800d111181c214000551010411180250700882c050743d03a1160210300030350301401009014600280c00407c0650300caa07110000c942c1c4100c0151021881c0c000b09180c2242c0c1c04580b4405410424040c1042d541001e4000307004084410004044841d140d010030189801022015000c2070744a64402410a021000030314052510000b5404031b820700504040c018010100c0a030070300030b814029410207135559100b101030000300c1d03401e940728024203600c002e1401c00001d4007070ac9441042c03103150b9118608100c642c20850000c0c0040700e5645890420f0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 407861312 1250 407860062 407860109
    0xb0a0515030606120103080c1504020a15020c0406080d03050108280611070f03080a09031e090815010807090c0207031127072303060d0311190b01 64
    0x1410582000340580d4499540e8404500300d445485070001e680c04000000001b0003054074020305c0100c0300c850588043c900c09440360100420152402075100000794401c2c42000340c03440d10707170030200850b204036245603e1075000300d400c540103070308500e0060b0003850212801039014054980103000100080482e0b0000c2d801c1d00401e0540980d0301d036840c01031050140c091003240d4104c400c03040c1881ca441035540600b40744c1860106103a080850205207080002a40c514644c407450f490f46405440d000354003444a21000c0e42c0c684a01026401d000c480d10021550040801465a02e1701c007520900b2030315414041128900328459018404a601b031002000c1d610b45e000ca20075046a9021004400700d840311030020307200305030011144850030130604c030283c5440d440c4421203000f90141c3d11440e210716601201d0000380da160040e000794034041000451400d06100c0100558540a8600b40d20188810018030741400761040101507080c07550201182071200c0b540c1414010710280d103000040c1c007a0307146030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 407862562 1250 407861312 407861329
    0x20a020c09012306130e010603112119020309010917040b040905060103061503060501110705010813020f121006060f020c01030c09090903030204180507080f04020d1a0a0b0a05 77
    0x6888021061440801d0f03561511000d440d140c0c0c1800a004207441e0300c0703071207902d50f40c5001d10071440042e04040021344c603035110b001219200420000c0341d01e0138a40748810801c008001804030b210040d15a58040c0007011284082c41c000c0614030004900b08686050000034801103200c65005000104402c100d0588044101c400301c0d0741d5284040b5182d035900006900034030680e80150b082c43c10214025144a506500150650f003090b00c0d80802e48034102440e0380da54203075008250118200102062607115103500840035035100824000c551103030f120204c0c0203206640c0321400c13503a000ae80042008001401210003900c0b00745440f01c40c80700310b548025903c40c5081701c00d81c1130551304e00c02c030207000d840780d154140a080e12400c18000401e29141c001d00a6205104442e08026091030f100d102d20f15602805000d00740344c2d907607442103440b40400c40c10301c0e20000d0012a0710040700d8600030002518110807410217070360700e0030700d045500d09544a4002c0e81c139403001c068400c0440c210244420f030b485404 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 407863812 1250 407862562 407862599
    0x60111100902010c0b04080c0601081c030203040204150303091406091012090c06050d150b070209090115060305041a06130e19050a05070f0e0402090a0209100201020a020c0901 77
    0x10100e20481d090005980c052904880a003034000000108418810958001c20b07200c510303d0102d80b46680d881a54680340c4006d0f003441d0004484240b52507005622a07005150050300041c00001c12020300301c1c1c5080c617030000d603004401207003000c402044200c1d030843c40501c01d00800c7d154145880b4000d0000340c050343c0c41d8a0742109021149500340e04040280c1d0220044c694004000390809480d204040c1c080d800983d04400c0d50744c01c000c604440c10300c50078079030000ca841c00c07202d50382860711039401c03ca00351000501501d41036680e2020480002000b01442c001031196403000903881c101801c0980c00255040021850000d0007018009103849503031240d0f00085001c0000140c0070144001141011010300e002c1034021442e038800814070801060b5010098425411100c003203580d003110203010202c9105643c1c20000500004015041c13400c1c07d036034440100c0b1401443d00d51145e0005800340c90300d903090700052b9400304829107907540412038804102d00440f004000c640c945520200030780d04c0c000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 407865062 1250 407863812 407863843
    0x1202030f06220609150501054009020912030901090e0c070215040501031d03030a09110d0f0b06060c06190e0f16060302030402010e010806240c06060111 67
    0x5024034002c0110804001c071400041814462195102d0340b0350007070f0040d0720100540d2070880c1c0000500350b014804980c240c43d403990380400e1034003040c400004440d000810010148038144810304460001c0c14800d409408103072001622410b11000f03004e807001c502ca00300388060b0310410005102da0b03040740c1340e03408588a88040031490741d104050a1418002c1290094101d02c040303501c0301f1020564400342c400e03030703000f0383c0c080002000d80d00d20320001d8806840d4010080c0c1040010640d80c04942d0480070519002d41001b4044144600c08903084c4c0c0000841a11801c00c00d400d01010800000042900700c1c40880325542040065501c50ba181c600181c21f200c0d4000741580d9841e5142c15030781118940e030300f99101360380c202071100360a15100e0b100c0701d0b000804045541c0001c5500350080c82540e0141c3d4048e92002c46400c007100054a00110140c9007617400000d19012002081000a03400064010203019903190000c41102c645000310140c202e07410300c00c418100d01e0810308001491500c070745250 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 407866312 1250 407865062 407865079
    0x60906060e100504120302010b03060601030615050c03190201050601030b030102340f0f11010f050409051e01060e030c03070e2802030a0902090708040803071808031201061202030f06 80
    0x2400b003615035100301d50210400140240c800c1c1d09054041d417024240c202c3c107a090b1174440d918600110200c3d5000e0003800100e112030a150060144644041c1c80b034203000302d00f201c3c604180c1e016075940c40c1d550042e4140043c0e440b24200846942e141c040c000001031b0a82c000d50400030260607080e07610444c4c8600081020140215500900d50362004070542e03600407410500c0d0000b681444480350014403402c0e81c82d8a205140c241255101c0c494100c00c00303516544090526080041c048003a10b0054103408166986029002001c040509094020a5907417692110507011a060500f4003d441541c0c038420b4005440070007030340080c42a16a0312058194440c5420384545540218954500d4040c065051001c820801c0440302c684c483d246140c0200c41c00143ea41c0c400c02c080340c0700102240c000744080c1c402c0c800705003064000c50a41c15800540c03131400c203850341ca440f13100f4a55000f08041c008500840801000390359000808071004d100c485600350301c0c51034000561070512a000e009240900c5c42e0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 407867562 1250 407866312 407866339
    0x30902010203120702060708150f01051b0607110d1b2910090e0609101a03060a150b070c03030810090510091a090a0506030c060706020409060906060e 66
    0x20b01c00c84048510075035000c2c1180c203101c18003e40d40c000c1100d14102160780c11000c030b8003040000c90780c03400c8600000c1032001d185005500459142e08442c0d413101d145407403c1d03482c400d003031014060644240c8080d81c9100f91040d450114a2800e400c40c240801400444603800e450510243c2c03814042c030307401074040a000c00c0141d440401d00c04081d0440c10341e01900d40203002d0311041146400f011160003000c1801030b0f41d0048a841d4860800b5140842942d2002c0300f0b41001c000c40d5008807003511a0030740024074507000701002c03908041040301c8600c1c041d41e0b51900e0010f00500749032a84081c0c22030701c0307505042060342c1d5100e40d4104881e000140620100750002138962440e601d00401611a0a074240414140b070703400c44000e050140101c1d00000e0034510310500c04000f071000c0c5060504001c0240c615505d840d1041d0006080240480390140a0180c001c140d030349a07c0000d00f091407182c800141d50720300c0c0481d084203d91050700007070040c500380441040701d2944940e01c500044011507503500c0f100007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 407868812 1250 407867562 407867567
    0x1009081c1412010807060912030e03161412060105132a0e12030a0e190302030d020313060c0b0a05061201061203260c070515010909120801031203090201 67
    0x200d00c900e0303600c641d4001140c242c494520540c01c2d0483d8000380c110388129484032000c2d181c58110380681e040c2a0304640ca1400440e00c1004021100a0301a0603241d8542605010a40502c125003000a10792075003000b84241d1704110715400324000c0080040d081c5541020005154100c0050700d1081040e253300c0f0301e49264401c59444c050040100074086c1c40506c4d80c8401900c40c04c6828131952144404810741010018041304440c10b01e0b490355030f558085a2003500300848240d0245541c0c0540303107000d40110050f1410003c5200f5284190010350702c501c400c0d0305030081015a50071002c108501e448803000044e8075608180d030011500c07400800d00c3e684000c00f107a00c1c8020f6504000440d0300b40303100029900420706c98003100358082c2d51082001880c0d4038041d442d4098030822030122100c003100007602c01c1c02c41c0307001e85001489501a14441400703500040a40e0324203800019000d5600c204400400c4025013624000d0b50a609000400350b1650300d0300c0c109048600c588606158444100c44216071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 407870062 1250 407868812 407868827
    0xb0306150d021201060e031506150a0302040308120103050f0a030804060c11060f01091a0a03022b0c0e01090903020c0f060c011506180308090609010507050a111009081c 74
    0x1101109096250ba50704001840e203150301410502034050002342d40752400c0d01e02d4985104000c00340651307240c12001c80d0f41c1d0409a02a110400805500303202c00300c0002d18440060282d007196580940665045040040c20b050201050601a42c030541d0310800203900840d4195100e40c20142c00a0100e03400c3e01d00351000045407082c4011405020204411002140c003041e040e6941c40c071042004000c024041201010540d2540358001c0e510b5508100514041c0c0c035401151680b103142c49140c01c00080307a12140d02d401c91040350402c800b90400c0c46030b02080b044a41c01880c40c404140f122030b0701510080e4031750521501141c0585521114a00c060f01e400d0101e86c11800d4400003002041340c52815020f150019000340d100140c26500903422150090050106503504450320f42d207004110300410045a000400007030612170140284004510184900702069001e6040304081c0d04440d0100070024225040d04014415440740030f0000650020700c8840b10302000903010010960b0030002e542c501c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 407871312 1250 407870062 407870077
    0x1406040509070c03080912030402040c1e09050f0618040906061208040905180312060d081204121d0103020304080708041e05151602190803070b010b0306150d02 70
    0x14041d642442102039202000741d408900070707aa14061034450321811900e03880e45075003810082c44103002060152070302c0d502581000d8600e04005130488040d0760790030241040840400046684036804003d141444107803420380110071100603180242ca40103c0d4a06400807500760300480e92800c2c1c001c100003059203c003014080d0420300300c0520100340f41042c502d178894092901c8060524002c91020501224011f059150b19009181400400b41106801407402054590300c0f1000c0750000c004074080380000d044a40d07040710b0b061154505402c0598454210919142c02c01c00d0800c17468041849a40f010304c9035001c24a0056503940b034604040a850042c014040c09540c4000780000300b00e001d032480910141d078030102c45421f20307030351304100031485400b008441c050300000c0220114036203032003408101d9030f48002c0001119604206000720101c0190b0402149940001041070911911402c400e0040c10401d0080d031451510b400403d02d450000b441d8120003080104080a08400c0c907010364050 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 407872562 1250 407871312 407871319
    0x60906110c03120c0106051e060c0106180c020d020d0518010e04020412150b0a090908120c030703060911090103091a340e091e010807030309050604030c14060405 71
    0x212060342c2c50020313800090310000c50742c60400f00090301e050401020301c01009804482ca0144502810700501c1e80c442144140c06540c0d50030041900c42c0213040c41c3c10424880880020284030030040607182c248076001c558290352140c1d2000c8001540b01048a83c81d20210b020240d11101c00710040c0d503405013505206602c240041000700e00119182003135441e0350300903a2003205130046140c40400f16508100340c00c1d044000c1c80014030090880b9006840e941c0e01c01d02500d85020040c9102241c0c071f880a988041c0034a00000030700c8203031685400343c0005003c680000300712041c240601d48515204242c142418941c42d0300b100424405a40900703619101000400d02d0135240c9100a0151080c0102018021130800b0003500440b03815281c009264451546588000c6944401080a00e54000303008554a1015178000c00012800c0001c0c94028a403650081140c00c0c210314014000728801e42207940a8a410300c07007007011070400894a0101d480d58550005040d20104c080740c40c8bc855504015017 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 407873812 1250 407872562 407872573
    0x2040513120f1701170d2c01051b0109050c0a06080103060b1c06020c01050a0204030f060b063a051e060a05121e03160305031e0103031e020106060906110c03 69
    0x29214803115003184505d030309a090b540002c44002c81a10695001d03286000c2400c03a01c3c2124851800d03905400300c0c1c1d0030050404900300500d411800080e00c1d000d00c901402e0765180c9400d6010400d00f08074070040b22804a90450380e013800c010b002809403405100141600d034641c00c01803056180e5900098180c0600072100d00038105a060600181d88022520003d42d0329010000b0402e5055200351015603900618810444100741c8440300545020394032150700c500308000e51070343e441d02040302c0300003000700350200c0c2c40d50b41c0f01c000300c443d541103030b05040c0303035890b091074100082140c01c0c078003000320b0b80c0d08105044115200e540c040b0b10f080c82142c0080d50049950490303041a06400601e40881059111203e5a140b4006a140b62640201340218808003240d00020001038000c20256030f020003000080401c0c0304240d404403000500c02c0c0c1c010350200c1c6c60714000c5222490218010210540c1c580021320441e0b1a1040062081000d44034420410104050a40f44480140084006141c00808540 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 407875062 1250 407873812 407873819
    0x13020a030f030908030304021c061515090803121311042a020c030c01031a0a0312080703050f0106080630070e040f06021b10050402040513120f1701 65
    0x121a180d00708410307408516160000a4424400021070344036a502074400b1100423aa0a104240b48950104c200c42a9031039806000383d021340110b1341d000034120103030107075145002c3c0c040c00303440c48a164100e10240c0d00100203080c428403001a2090304540c400503010311002c1d01d0309040d0120107650107800d520504103c1e07030101c03c1c0b904000d4400100c441c1c100d003240d4018001c03016640c0d444462070342038141c0c1104284100941c0203600119140b003250301070440c21404000040d030420000d800449030720303e011034440d083e070b94444603003548121113007800c2081e41040700e05640310710014866441040413510001d81c2c01c0d21000c003500307000d81d4980181520020a1020b0701d810b000354216030b01e100c0c0301701e00c800199540d524192038041ca4002803603040540054031110042c1d402482c4c06100610185440141000b040000482400002c20300264605040c030402050b200043c084c108802010580140800c003016140500c0c100541091312001c040420b0035194800c1031000700b48900000000003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 407876312 1250 407875062 407875073
    0xd02030f01030209070e01120c12020d152106020d0b0402031017010212010509040c030c0803030a0b0a051818120415050309030301061218080c0d030c050d0513020a03 73
    0x80c1c1030700c0c4212101a81e56880c064111104404159020300103044504958039010841c0d100e1150041c462500c100740f852000092000d0342c1c04003145490b0207948d0703d00d5900c9144000d01c4040a0b01d0214645405a07149021514a16540200c05440030740d00050204d91000340358440424210050000d646034640042d07503100c022142d00c14140c00705142810000ca4003018421500d040031310346401d041342c0e404d00041c0700c0350000003001281c0080c41c8207408004505c1100407074001306003001c000d6a59160800c0807200b5904078030001c500644101c1c1041c005ca03520500265000c5091102c03c1e56540d640b1405607070145400c030781c8c803080c601071000070040b00826200188180c84000c11003013410b07901d00100301c41600c0201c6a04001e0340041c4014400c05200303d2250308168082c810100c2e0b03104032402c02c00f040c0d04c03004004584013000000c890303580c91030a0090131480100c42c2420404100a007034013030720911804d020001c80d603985400041c84046058005030301c0d590060480c1034000c0c2c8034a880d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 407877562 1250 407876312 407876341
    0x30c1203110d0f030b0a260c100918090b0c0c010e0d170c0f0f03011d01060f0c0f0b0703050402031c02030a0309051e0309040b030304050603010b0f0d0203 68
    0x1a80010703415121034440c544001991851580103603a01100102c07611001c4008045c60003015602440000c000034843d07140384180d0420007030900030001c182e407001e041c06181c85004040360780901040030340d080705560400e001780121001030690307106c08800903039190014208000300a01c4410490140520620340340040c2c072210710f80c1c4000f081150600b030b425540d107404e4100c55600064030020600c0342191203441c855002103014a0003420450a0760310348171580c00400301c0c0e0f4038140c0080010440c008855904000c000c400700901581941441002842c00e14480301d0303101801440f1078004100142c61140c1070ba142e4020003103400a0030200c100a01030501a44c0a034800d200300396000800003042c410b031040f004243e800075440c1145144042d809840e0741a0b0581d124002c50440303000b02d1000c10b000d038000b02d001102031540e9001c0101048210394907405064000d43c81030000b84115202e00040740e05403440e40b0401501c500108030801d40c54881d0001c40d910060010003880706100c407400d039 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 407878812 1250 407877562 407877599
    0x1f02031b03040f0f1208090114450609060405060c01060e09030a0206150a09090308010305070f080c130204050d0309140108240a080703200d0f1101020304030c 70
    0x85041e9940e42c0c1030b40846400e007174040c032001341201c28410b1001404400c01000700d000f06040502d00c440d200001c460160304641d88440e90400c102c84c11070308190400b0300c0d0500100c01041006141d00014500204409116102c54001c000015201504d55110340a880040c2001410b032031342c40d160014982c0c0680500d1052000025160000c117180b04400700c140e03540d0f04019401006199603000d214052100c107090307104e0b000174015001240902c5540a0350258600a0721030314019450f40c507101d450914694081420800c590805000b4402e000c03800402c0b1000031540303c0c80b407000c010700c004024407459001075408418045241d01301500600300348101c2c0d004100d0100e00d0061900150369204048805051882d58455156080d09030300304d1b00d031001000039000320300d040d0f1200c070700303a00e4840e042c1c1054410040e48001c080e5814454001d486019009885920304c01d12603a0320041144075119004102c03122202c0c024516034800c105890043d40c2280082c08259501c800360b050600d400c2c04e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 407880062 1250 407878812 407878829
    0x4050a060203070b041506030b15100207060906080903120910150605040b0c0f03031807080c0306040212150a090b1006082a0f0a1803021f02031b0304 66
    0x40014019001000f5a15500c2d0003151503202ea56942d034800204201848001004036660791010001c03d100121040c402c48903407540c00f151a0945040151f4a01d442496004560148005100303141d44070081c0360845800c3c0c148020291102000941907005038200000740c072000804100c0c8034100014041503408440604002d0301e1045003244046030040d02440d8042142044100400b480440c024441c4540110607200d400b440c5000003410b55006640040c208c04802024880c9408284000303c000c22a003c001c04003020b02001207030301da1f50b00400180c400d0b00588403440c0d409605002c0003650060844640d043c500c0c0520f680402480002e4040c3e40e000041d5002881000480d80504103582c181e0321400150781e02d600083c00d031402000720b20b9003004450b4440c000c1e0307100504003400b10308403011019a00d0b801040320007002e0101ea0b401c440300000001408102507101c400a4090b01c03042c401a0303204505840b01c05a1452080240d031003c80071450740e20242c440400b02c080c00a0368440c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 407881312 1250 407880062 407880079
    0x70306030b1b03070c0515070e0f121b120715271a0c01060306020d110301030b0a0504020a270509030403030210090c0f03141c1b21050405 61
    0x501201008240508024800d40b0304001040001e40208030a0b09082d1240c0d044886d40e0b0307540c0003056060801a9a9031002c06d41e190701104d03580c6410140940081d00580c1c030540004010360450ba80c400d849810f003450b8195020650b1000d44809081c0c0074040007000403103076110340d1000e028407140c170f907031a01200045400000500d580ca03405003140040301d040308901034190801148030b00c1c0d0021030300f81c80c0c000340040200d00013002e02030003144000c41c0103650040c0c440d8210038040c03054403c0c00d00c40040c0c031441000140001141d031200c5a800c1301c10305100162644d51403011601c00d01c0c072500103154040c2c0d401c8558a0050a4803a82440800503610920507500c13a00580c0d80c0c0d0340a40d010040240e00606409400c0c500f84d640078812842c052581c614400340d0307410302e0382d03289000703a081a201c07242000c013030380c3d9040c03010031540f100b21640300b490f2481d0882001009002100ca42090724070712480c04100c03418402e444854480e030810046030f4045002080001030304c11382c018404da50081082 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 407882562 1250 407881312 407881321
    0x40219050306100f080f1914090c01080403021213050d11120f030405011809060f0e0601080f010e0403020a05010e0a17030c0a050f040305070f08100501081c030b0603070306030b 78
    0x13904a00320b5a01e06034558200c25120403d41c401e00080c0244800d040ca40300c46284001715155004108980300d04d00d01080050400b11070490401405402c441c1c1408103100c24480002da0000b10800b212000d0140d01d42c580000c140035003a280c0007540300301d60040c40340d102c0c0000e02c580c242e65038004a400b165141015807480010b1070302c0e86103e0703400d04000d4106000802c040d50203400404202c0034001112800951240d43c650708440842c2c200b039450013400d034024030050002e00030b495004842402c011450380f6008502036041c1c6814040c0f440419444404581014001c00c10804042d50140083c81052101030319603a64101c1c0301002da8480700340c4403035040204086c004a82c090030742d1085591600b2030310070058901e603020b0002d401d10303c0d900f00700000c0400c034148140c0c4007825030203203040031481c60880300a180907030141d0013520707040c5000010004074400088080c812920f96210148031142c0041c140c000b4845989150303046000041040525070b49a0300403405e80c1d10511441019486 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 407883812 1250 407882562 407882567
    0x22b080901060303020705040f0f0903020f12090904080a0c0b011e050405040203030714070b070302070f0605180111120414210a020915030a060b01080a14040803040204021905030610 80
    0x182c51001401580003440c00703004604043e00580019044004042403c180c015203450803244039100990050b00094000745004d00d060140141c464110700b5001e0404103404001146908058030040030040b0004200d1110360088012401710b41c0c1180109085694030001215a0b500401c031020702800c40381000310b0340745864492240110b4000e070055003041e80c0c40d915035203070101e9200d41803403500c9044000222000d842c00140a5140300c0d602411200f8a40341401400b64210381008003030003420300262403081d1080c3c5842c26603101c01d18010f14800341200404c0d0070f081d074100c031000a8040008010825803e0301810341046034003a0703403400740200c5682c5c005412030500c1d10070360842d400400e0220050315101101d540c104054040747e0011450401c000707407030700c4010101114119183c00c24910310f5170700f024a035540203450400501c40311240d244060442c0800600081440d02c003c004074081d51181d50640b090403500882007204845032010281943c0c10840300d4501c00c03202d203100143c2e1a407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 407885062 1250 407883812 407883821
    0x180303060f12060209061c0b0a050405040f02090c0d110705070608040c0905041a0906060f1c03050f0912030d0501140d061808040933050907022b080901 67
    0x30038058000a16856a82c0d80078007940c00400c5659011b1001e0091550758001d6580301ca240007094800080c0c4400e00f201170100c03403446540003600c514548800c010210300c503000380141d4598111040704d038907542c80c48016051f000300a01102c007140b40c00c000e002d00004800007064014003810441d118030b40e0f1000f08952040003250000e1000c10440010030a903901c03500032542052050048020a42004103034540c10902200d450682c0c2d8032030002c4c010607060001e440f444003101a500000c14401260b841000e01a100710002c0400c00005410400e0031b4203071042e510f07140001004a4658004400102c3d41c030740040a401d0000341c600b10000480d840c91b00010368407440c1c00340c440c01448119444140041c6100c000300141e02d8805d80301318002a17000c0008002804c2000c00014000c1030030355110b040046020711964030900c0d2005200303410450100c2d0764088440445105010340d40e407020807810422400e407517001500002020007828140c0c00c81400d071144c030301d42d5031041942e9018001e038286c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 407886312 1250 407885062 407885069
    0xc0902040b040b34021e2206030203061021050d0503130b0a02030109060b0c03070f030c0b1017150f070c0f060b0910081203061201180303060f 63
    0x9141c200410490100c80102411a5a041002d41e60048421440b1000d0b070740380c1a0364030304002c411204d9600440c505070540030002c80490200031902c14140010809400c40d038030804040c80c0203c1d0100140310f881d9040040516805010745070300c5d0a00490948200d0828040c0c01072000c2501d0459481444017220300c101c0c5500071005020094842e501070701e29510242220103824030780243c1102051242d00380500489000600503139940c5030203175540440b4001d8110b000514000c0103000000000041a60159608010041c0703840c085032a050f1340310001600700921032802d000800070085034145c42042280d100225800c01c0c181c14000080d201d100461542c080020f519000c1440340c03500720310b059409140d9003044008414140c4910f00c424013010022141c2645580105060b03003400002c040c0c004600008001c1110b04003d0895203d81c05500d201c142c158012002696555130f13020710b0030080c01020000c00c14541d10190b50405a42003040540c082400c00ca030020310506c1c0b041c1c220048 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 407887562 1250 407886312 407886329
    0x50906060d0b010501052a0f0d0c0f0605060a05100e0f0d03020d11031c270807080d021b0f0d08010f121704080607170708071809180c090204 62
    0x200d03030910700152416040341c10107d1030012509000d859000110b15820080c404400041880c8028401403e01d08006a11303404100001142618001081035002c040c146601c1140481d1030303030395440801ca64550702d80c406a440000035a6110045800004080c401c10003a00d032008100100c5092001619480c200180182d01090b5000400c41c400c7c08013095084098045d68034221216400f10003240441c90300c1d40d00d0303503501c010800590300c407260365030040f000600071221402459103032010b07103001d4840090000321001035291101c508903070440720350f1842244055122402c0a19071075641c058480305410510880540802180c06440c149049030001d5201c00301042c180340703001c100040300d0342045401c0340700c41c61243c00c20448070000d44090070300440100400d00d4544001049031295000b0301910524401c18040039950106080e075108a107401c01101e400c1e03071001c041c42120034a03803141c0c2c807176813604059200204020b511a00d4240c000c09003070045a8403240300300200e21031b901c1403018 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 407888812 1250 407887562 407887583
    0x105130f03110a050d0924090308031e0f090f0a0506060d030203040f15080115020c01052101030303050106031a030c0d050a050609060615090a09020f0904060306050906060d 76
    0x24481e200d2980b0801d0a07400b42e40a1103169581c9514000007140392802142d000b0310140b240e04001201e8031401407108200e0400c0705546a0302a049800c5800060f00411000001480314800da5952801c110300c1c440503c9079503e4116104542080141c1d1034803002d01038075884505401c00001d100c1000d61b0000040c0a4130703180c403c100041c50600040440c190700041c0f00004d10118800c00800003090b003c01c20b41c1100d0b46440c00100920700c1600142d46980064008500c1c41da40003440c854649403c1c20101e0360b80d0030509400e10b61540c1010b8070403205070400008010168160400c5048074010346060081081c1d4403074114020540c51740481e016400041c1e0340000b03180070360035401660301038800d6501030704060b2101c5080040c102e42c20304181e0300c40414000782d4103140f000315011240017000300b4204040200018160042131240d29880360b00405c1c01d2140c0444041100c21a460042041000e1550382c50004080c050407200e032407160250100059050800d403509a0505d544010b002c0c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 407890062 1250 407888812 407888843
    0x3080714040b1c200d18050c030f030408070306051302040c0c110111030f071e031e031a090a06170606040f0e120d020712210605030307110f061b010513 67
    0x14070745c216a81d08a0046e8a07900c0c01503211075058400c02e50503009074050a6254680010f040c42c16148500004071544104010040b14001152010650f40d10010106068a44034034001c034249010001039807103850203804490701600704100225541c495000140914081d40065480280b1101145001e402c104403420584086030028080e40384201c104e0303008901410850b014400030041c0841c04a0302583c0501091038209140c55840e80e107078030b000e000c18420880040d20f440040c2c202107000710314141c089041c081640d00280c010b0588800d002ea4035035084038080b6652141601c1c2140a28a40b601c1034902d58042d02074441c001c051180140000620303101414020740c000302220300010750a01a1200040c0d002a200c02084501d50322400541600c1104000e034144c200d841a030040d260500400c09a1004819600c02c1c98200e070401c0d40d16070a880201e0118040740c18025030005000a40203078000c21708040511507420507000f005550356294800503c00d080720005001000000b140da1f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 407891312 1250 407890062 407890121
    0xb0915010510170c0d1b020c19030b04021f050405091503150a060e07051c060f0501110307050d020703120804031b150c030209032103010303080714040b1c 68
    0x110303008800a0b500901d040f17800540c803412100d0340c050701c81d60300c406103507040d100350340c10052401100021601042d41c500d4007440e2000d100420310000b091209180005029540c0c0d00c0320050641d0b400c203030307a07a00c00301488100800c2c0d540280142e81c8690714920121b8120b5807500050590b481002c4d005081032040b0300e00620100300b00901244040b0f072211400f080000d080010030340a9100780d15440c0d100c2c00d0500640c0d8040364694070035014985081e504108000306440070700101c85080c2840008400c0c64810706003980b16646014007980f16564030500b5503980052040200da0040100540c03200040600700c92010050b03802800044a402d403d01003461510103141507581721745071080c18068135800703080580da44155040f0200b0350200e1102013904052050b90a80f200d20003080f0801d0480801c200003a01040c08003904108454000a807610700961000c40c014444158440d2202e540720f9103080c0650000713001c182100c02603031840c5220039090141c44907102006403001451714140040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 407892562 1250 407891312 407891357
    0xc0903050a030809102d0207110f1809071505190e120d03090b0a0e030d05060102071a0a12110d0b040f061706011413020702030a0b0915010510 63
    0x2081945c0034101401c0540d0b1854032504201d0300e107901080c40c1c4003400c5507100304007400c00582d000b51240100000d000050481040240e0b407642201d00940f140e001e40045a4a40800d440203141c0c03161250030b10803040c50000714641111429004002c40c41503144045074103001d2040f1683c590181400341006040c01600c0e0600c0100d00582030001c006c408041e400c0c9060720b204034680c0800c1da908001d00070321260198041e4080c45100d014000410940402c0c3d9482c4140492411015500c802091150303109000140003130050110341d04140f4080e8803120801c3d40800c18220109903400c1800790020494043c00219203c032001d00c5d810b1003407074500c05010300300800e40e190344681d44a84a4200059511035000079150304003405170400d41c00340d0107514080040c0c010340c006ca200d0032230b004103540d1205251182803400e01e03000b6032141c840d0700c08649402d05190b0010100c555210420a561000141c4a14a0300c640454155a0303640c3d070003405401e218a00120000400302840c1e0300326031860505 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 407893812 1250 407892562 407892571
    0x30501051506033403050a0c050c0c0603131a1603060e0f0421030f061a031f15050702010f0c0b0a1109031002120f010e011a1c020406030c0903050a0308 67
    0x2400132100c600140d104030446000c24003000c282d8403018072052180520400000038085c0c24103610380a040d2400700d41d12000006a24030505001000841000098120b0101c503a8000340c0d05407200c03124622085100c4003211702481148142c2d50003500c4a11038001d1008942040042e113010381c6071910180c0c038120300204142d8860402c165103041845a0030030300c81c0c50141603074000072034460340080e42003521059401080000c81d4402c50707010950402040307030340011405112100d44e000c2603a008480d60100e0740300c070b02c600c002100175001e1580c10100419000703100340c3c1c0303d4980c0204040141c50346000b901005d8000c080c0100003030310ba00916806920700810703d00150381800540c000080c035044c00424102445900810110051417035054200e4008800e000f91044540c103105410300128414850316240764017080520b280f04907904202e604100c8105109252103948a802802a40c400c2c03040d0030000345881c60000c0700b148110b1040b000d0b07950003c0076200583d40b944048035007040161 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 407895062 1250 407893812 407893861
    0x71d10020a050609010b01180e06091f080a02010e04020c0d0e06070b13030206091f0b0d020622080f1e0111040603052205101a041503050105150603 65
    0x210000040780040015a204d880480e001194201d54030000628094000c0a05c00b9044501d0070141320b20007103003d6180d4132400a80700d0312615030720360401c8201c2c8038122012540100d200d8001080681c00481c0b00f64401d0b000b0703224100c81c848603c00340012849031120041c9a50011444d210f1014401ca048902e0b0714001845c41c1d040c440151100380383c02c1c200b66001072140b00422070800406030107200280d40b0510326405002c4c2c00c0400340483c000340408441420781c00b0fa03509421001d681e00c1144a60349aa00608182d07100d888408441d80f0100c1c0c901000001e068200303100140305100040e5410f09501da50002d043d030548801e4500b1882c8041440e12400c9540b00d82854801854040c050402000c0541e0003158a052034200036070403807204015015042c4682001d072000c144009841c8104c1c0546100018401d84003516480d84980d41d0400d940d0702c02c4c14506441d1080c1400c684c1d036000c2c2da01440c002c200580b182c59001c0c0f00c444001150b290850428000581e4440502c1c3c0d42175540103000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 407896312 1250 407895062 407895073
    0x5210c0309010c030909020c010e0606011803030e041d01020a030f0e030702040209060405121006141f090e0a0914010b010e0607050106090f0608161a1b01020c010e06071d1002 77
    0x3c09400c4160381089018950301c0e2b643e0034100985000170083c164229400713082c0009900c44181c3d07400c2900e51079001c007a017484012980048030351125400f2000340c0fa4165012500d140e203545985010354000c000e141c000038140102c000422800344503400c20091120011403400348075500348006508511074941d03014605000005564855400b1540c20b00c0e0b2050240c590124410310340c80132aa811780007082e1603040d041c65050700b5201c48084040b100000d0081d0f18188036901c0e4200c803203000a4100c01e0300c800c0c0b0241444584000740d00070855562140450046940c200701c030980c221566200124000b8090041d601e81604120006108480c0910008190741d074035410400c0c00e5510450745030b4292642c030101000900d03000d1024255480c0407240c220b03091032038403504103614203840303500c502e080400040140d0303444110b102500d01195050029502c40c03065903290b074002e00107503035485214052080055180ba2081c0311004801900e004d908100088100a0080c0146000c00c10303015403141 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 407897562 1250 407896312 407896319
    0x7050d0c03050a0507180209090105011d10090603060b120c0c1002031515030420120f010608370314071419031704170705210c0309010c0309 62
    0x140100e40300d45000710010b2607440d241444d04d0b5007401030404c011b04442d106000540721544e504404a0444209103403001080c0030b400d10000107a420f08418941c081502006000c4842d009800203085480310780382003143c0c590741c001d641158400c010103d01301040160006200c0041e00003e000880c1c4040116450b40c400707040544104d91064620550200003480b0903c0c0d1403906040b119013042d01410110f08505040d0f54405a00c0500c01e04805485444046140f8a03182c40c1d010060803202c80048402058100c885a402000c0c607014a6580b400f0301000f001001907020010b41d440f041c1000b14a030307518244e004001e0000c2003c40100c080080005494065144c60005011198002c203c01c1d100f880d0015109441d2500c0c0b800310540050212000711b010036006840c4030824030864007041c903207586500c1d040c480e81c10cc400010a01c2040807403580107100707000900052000380e849041c43d00d141d04a00780e05990182c92030b900e0241d482001021000c0d44107a80100142d031190400d903200a45 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 407898812 1250 407897562 407897573
    0x2306010f030c0501111f021306120506090103080a080a0f0e0c09240d0f02040e06090105060102120d0b03010603150903020111070c0e0c0f0a0f0e03060907050d0c03 72
    0x203034012640d03001000810300030701220a203800018102404d00500f2000e0202c4c13126100c00400b41c44608504000800e4100e41c045901220708000c240c10b146c4214a8540320f0180c120807081e407107210040c3c90031000424034140701c5880c505898000111904000040f034049420540040c01c44021540b243c0f0070703048d4201c19014207000801940040c00301d4108600610111040091501d13550710720171a10155080058110101c04440070303078290020708400e00705507081d210102c800070341043c42c00d05c0c210340808021030ac140c02043d05a000780402d841d401c004a0342d6407141c84108207030803000c208065100702c09502a0801d8507000e4004501c1e1542d03070315483d80d160303140b881c8400903c0c0c9485025080550a1003a5030000c0054461203080031010b464000204000d4058100c0c45181c8001007055203514000f0340c0c007010641d0b5200c5a4030840000300030008039000080c1c0020804111040c02607107408207c41d48250348910041442074604001c010034102210006d1b203c100c6200000700c013041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 407900062 1250 407898812 407898823
    0x61309020411040501120b01050a0f09030b18070803040b0d1d0d03050a06050108010b07120210050109090c060215042009310305040302010c0809031506120703030c23 73
    0xc02082c02d4556180000140414441e0f000c441d42c0c8030f00d08045203503a070382c204080d00c006e180d103481c10341d44003070403501c0035030f42c04030f4a8001030003110220f000c01505c0e00b2006400e2041c1c107248800e55481e5a80d80e40495641d0241c0d00886901e85020b0104405096140e07100d58541c1c54800c0c82402d403e043d892400703040845488060002940394010048504c9150203088002e05003807905585640c500100b070100c90080d402e0040800481804100d14a07208000c12408010144400c020075691400401d00030000850101e64030300c42d10400003034040c0081480315200c1c054070702d688510355403a610203401000712000314502121403240b622180e02c034078896902c28002030301840c0359070841e400811005081441c1d85c29603c91010302c9180001d0b03101e800e031412a9420300300442c1860792032134018203901800340e146030144503410341d000294058040d001c1c0104020fa41d00d041c40c6150340c4090713441c1c2c0501e01014010888120307000001034605200050103811041405551407103420000e8100f0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 407901312 1250 407900062 407900081
    0x1e060703151211191a07030504080d0504090c090e04020904050102040b07030509040e0a05070314070902070303050402040b010e060f090f040c26100510360503030901080613090204 79
    0x807a01854403080500781084011403031940013501202851134012100381465108508000380314000c01c504040501030010345026013040c1c030030b40790380440c285d170000c200d0f4000707225400c4030034202440346070414003518048080d01c41c9080c400010703550b0f94090100488000e00210b0342c0c0d6508200005444040038041e014030fa101b580e9607580c48040d6000c000907120220945d00603904031207070325030004200096407000c580d4003011155070541002012420048070740c1c0300c58002130000510a040541c154062885540b003100c0c1000003003600c3c401110300b03c8201e01810b8101070f00300447d658014501026054014006041217036441e0b0890110741a2800004241c001c1040100c02e01007280d9805c0200b00d101d68007060300800e5203040c070703004840d034203092003040e0058048680d00c0010750b01c1648268a2624102c1d100004002002d911514061a9070902d000030022404081110301c0d02000710b07006c603541696401d00c20b8545030300f0880301c3c0c0511041144101c1d43c2c2d0100e1001a02d950242c058107 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 407902562 1250 407901312 407901323
    0x60d290a09050601080c030a12140406170f01141201020f0f07150207080d0c12060f06140c21040801060e04030f05120c0c010207080c030405031e0607031512 69
    0x6070361075140a502d41030040e0070000d100e402c101d041c841d05450000d102a4510740060147d801d01400010030349000d90700122003c4c000c00000b50100f41250803032065020310010070b00203038180da2900d50f003404051080c018924581c054420096491070099019450107480301d00042c54201c08407590086540448845d241c4c00c04c000c1203040600105c1c05540b201c01c00410000e614003240c0390f9410301c1e28400c802d015240c3c1a48c5100340c0c40000c0c800d40c00d42c1c2d00e00b0468402041101d848241450b03050280c3d01c01d0100241e444801d0206100840c000e42c0e00d4000c8040c01080450f05500090709490521102c0f40c4280d607041c44002620f10003401030700e0040c00c80107034040542c01c0a060090501d001c03060320105000782007215960181110b40101c0d40222032104240d2290044c22419019210380d40002d4840c19021401840502c4084024011644101c0031641c884004804034022070804040c043c003950480030000d20341c0c40c080d401010051412622800e00591941a1407030305c2c865804040c0e0b00c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 407903812 1250 407902562 407902571
    0xc04050103150c02120f071103061311030c1516170a080105040b0907030e122101060206010e1303140703181a0a03090c0512061b03060d290a 62
    0x140c0810a200d08000308041e40b0150518a40c00103d48200e80700e0244686121000051074505000086074070b00300348c042c018181c9240b410305c00042032075106410405e49440780910340d950254540012600340440c0c001d410326000100880461a00b604029a24480b2110011a0000040c010400c48180b000a80803254803060480b000401d0150141c00c808e004901d40745e81c00130259968a20554800e102d03140100312011184905810300811644001c8043c0b800710325500008130081c0c80b100c3c01b8410396202032003070fa1781c0c920890365507000b0b202e4a403100585501240c0043e00e079101e071034103c0d4068100303d4490050002586404d030710500f402d90010310055010700a02c05030310040f500501030341c1c80d421f02414240e100310401d88a50381e088001d156035118008108800194000003c0c0b400030300000c0c2c1d032085650455280d00c400c9440f88050000701f09508207070b508030000e5a001360005040d119801030a0784e10b0342d0180003e8800700114507061040c1100e1841d4548035940315004d84a808107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 407905062 1250 407903812 407903843
    0x15070f05011b172a0a080a0b01090501110a020a090212100b0a03020a0c0b04030806090c25060e101a0301020c101503080a020c180609180c04050103 65
    0x1e08541510350408038689510b10302d1166640c0c40940100c4041c82e00b1050016620b038081d0070110485807250320070150030140c049113034203024403000c2c0c0b80f0001d00b030300c51010300e070740c1c0c1e010002c05c0310980c544d031a0105102a80500180d44541c00c41500314143c4c01c03c80ea05c81813142c0000d40d8000d40795002c00c500e190004dd04034080c44a41d40065004814010358240c05420103401c20060700500d25000704059012a080d903046114046d02103c05030004003a40d50340c2050f085c000e08401048990500400320200072071583c2c1c103a03404076550441c40143c20010403c09000c2910502e111810540300c0d6601c90381401c080050a100091b20308a07001000100c010291100f00c645640c03400b80548240d20502441144001c00300d01500c0000c0d104070002504a130003541001e001c0201c0c0c01c040c204800105030703a0080e58001444032180f80c8100d909862a994110b0900d00c071010480e0040c3e0000c50100204075034180c1101002c0124045200359480c003811000490200c0e0300c26403050700c0300d005210582 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 407906312 1250 407905062 407905073
    0x2d07031e1a040302120f04030c0e090607050f0406082706040b0c0a0806061e07080301032d020d110d0c050406060311250b0a14060a05011d15070f 64
    0x4800d0395192503201c8903480d150710069200c040810003035842480c00280078081010420440700034562105d0301000c41038460f0102c03504400c08072406080c80c0320720004a100503004a00f610b103104004280d02c1d19107420840201c030540310240c0350100e132168a26800702030032280b00c01815269503043c01040c0c1850682040301d036189025105111301c3c6410819a00600d510a00080d4031050954949589214041d984040704480051080307090380e01080c88820040150300460407a4020704c107240b40a404104103201a81c040316090f10141203951031900103050245101c0200c0e401550100081d01d10100881c045400d25001201c28003096001481186420302c42d05001d46410710781001040b43c08a52102c840c0b040e41b1411104a007180302d01d081780f80d0f9507448071a0302980404070b0405818401320721009030060000d00c42d0400b500800240b81c5003449a4684c0403104c0580d0750940200312101d1842260005110130742d04106504c4000f0000c0303148800078203015200d07a14020f079000c001c0c20031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 407907562 1250 407906312 407906333
    0x90d0b010b0a03061413090507050d0b0106020c0a0b160204090510140f01140d050a170a110f07180e1903110a1203020309030c011505040b032d07031e 66
    0x524424500d045c0c801080e41740c21800800c1002d031040009400d10365418014509a03881d8001a0702424886186d0104850307404410704843c4680c0860f01007440c50001c00041303800500070310880000071301100824008103c208910540003030320004201c40f482d04c800d0b00341003031003c0c0096042c0e25020000c024249102d50150310011134551620294100b8103400000150074607403512400440c03038000203000060156040ea00e0b413003510201c0024010410000710f401400c0264040340000d4900c500d4500c1c0441c800d0070800700140607008142c01d014400403400111500c503507034943c0c1caa442039500c00b0104100301c4d000c0d8001107501c050100718900207209040b0b00500031002e4104400d6031000600d014040c84005240c1d05003d81c072940c4c0c0011082c914044d4441c1521150b0910504100c4401401c4804064542c251000d00c00c94800005060340c1d603403200d188080016858004000d4258031004e42d81d28046501c040d00c2035555241c458559030b0820075541c4d200c806414192004018141c0792 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 407908812 1250 407907562 407907569
    0x60605130e0a0206071703070e0a1223070905010f0311031b060d0e1e060c0a0203030a02130503061e0f06010509092802120106180902090d0b010b0a0306 67
    0x52108002030350990b41c44455a800080c01404080b0f540c500300800500c0e07120308610117524a0741c407450089001801c111100b000799004109258000c10b082c10440c15094440f41c004c000070010b03201d02441c901401000e0b4120502a00030180c011601d00c0300f03401410b008014083c168400f050850408202c42c10340e0034100e07031280d030103806465850f600307505441c3c11018084494649407190700c203122001c0c0580907501e10303560080410544c08201410b0907401c0c05034141c3c088411070350703d0201f455200d10400380c0751405a801800090f802806503002004010349842c040640070b5074413400b02c2e00e0a5001c1c1d485203440941442070b4030b400c0c0500b03007017158030990300071001f043c90a1503c0080c00c1481091001802a07031349070000b030a4180740031003100303502c0011030b618515085201a410029042201d149a000d42004000521940b207203070510061020001000780b11440c0092100c002d41c402e104661304403031104141c2c03001c1943c0c400361600801842400603600c42806000404540b041d41 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 407910062 1250 407908812 407908849
    0x601020309010207060f1b030f08090d09030219030c2c010315150e1f050a0509010e0a0b21153702070305070201180e0406020906070f060605 62
    0x848040ea0b82c0010000100c51060510301e88402004008487e21101105c1c01038107802070307510079010194010700041110546a503810690744594440b90b8680d52070212460014202c11800d20140c0307090b4080d806090340325050741850b02d070340355585901b4882d694040051858982130300a03c5448a40300000071102c4510b82d11042d60540c1d03501110280c0d00e100d450400c5030744450330362292000c0f030fa0000c0500100f0003d03941504d0140340804e0015080035064081d01c140b00700005450602c0140c140603164000c20301a4281e003040c2241840c0e180040c08800c0c0c550315200c0641440d04c030b4400c2c1a40c00220b00601d8440181002c2d191403401d0b501d03c80811f00c4003260002c10900301d207031960981407182c40d03081028000018030003c2103080500c0c590f140043d480022100c00f015008002050458400e88605c0c00c1d180030040c00c5a22400c0c184030b8410004002d000203030002d81d8680c001c0003501c00017005942009a60788030000506403d59003101c0f55580c810050001e440c2552009590b440081c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 407911312 1250 407910062 407910067
    0x60108090d0801120609140106060908060114010f1b050601150206060d080a0525060c0c0f0807140d020d02011503030e1201091703010510030905061501020313090b030606010203 78
    0xa0703030042000e40144904261407403088032074010404903070401c1a550390800d00d414280314505120500900683c850303200400ca07072210004007210042011030403541040c40207040341c00d0000041d9007501550b4001d604000d441000842c6000300068038000c441e000b0300041c4103941c1403074161110094030740350350030a41d03010b94100b00c8035a0321240444010707580244910349640b074101058645008000694540b10394040545402c090700050301404c05029403000d000741400c0d46800c0d0341e0070030094000360807101004030100c0462403610042035400d20a0900c44d400204021402d42000340702c0010300e006800860032034820300c0e4240200c0c5007031002c21050800207440c66802030030201c4a008250b0050580005044075000b0a5000c45d040076042803040c46249440141c0c0c5005070b209002c0c80d4801d20044415008440c400d104680c41c5a0307000c0020415030b120080804108010381d044941140f008001400356030482202f1800109003c590108548840a00305420044000c0070241154004e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 407912562 1250 407911312 407911333
    0x504052706040203041e02012109021905090c070503250201020c04111e0c0102040618060827010605040216020a14030619060f0314010f0605101d0a0602010506010809 73
    0xc210051900111000400031b0400f910050b0b5030140920250341030012082214180001540c04c208590781c030842c0c000644c030318886869228000c0302e0041d181c020310f11500160304c1410800003000760718028411241004240b040344403014035000441e02080544092500443d42c040111804945045600f441035001419010245000c1c008103881c0610310b604048604800640860340c0c0607000c00c000303540d80d40d100d5801800008c2c0c000c0e289484e4444251001500621484010b4010740c611028411b941d483c040308044008440031200c1000d568854000596a03200c0c8000d00401e01460214030242c04540108111544598402c402c00702e000300240c2c01d0f0356030110f2102d6004d0425030485000c0031031810010000d00c1c0c15004525011a041804000d000c400b40000c0400350001703000b80300d0341024100c4481514880d03c5400d802c205051a5281034030302940903c01c1034861403e10403c400d104100041044055520510140c1d641d2014031549507448400d07980d0140e1000d0090610f51407 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 407913669 1107 407912562 407912573
    0x131104080106240509100e01020c100306080c06091305090a0503031e012301080601030213030f060b030d0801050906120f01050709050301060e0a0b01050405270604020304 75
    0x83c010100c048440e101c0c604807401ca003000b8200c403510600681c415035039154080f041034154054090840c400e0303210502000c060f80003031f640120317480346002078084c28201e201c01c030180100c4081202c20f2250329204118043c010780301000090350341e10300d4811402c144c0741200c004d000c5d000000901c00281d41a940b000c001e50b0040c0700010b0640d90310f043d40020b05943c0417210b0880c0d446a50100825070180413601e6000506040c05881d001048400c11104181908111900086000c030117040c40040d1040b046003100517001082c40d10080c20020b48842d0701482031903c0b41e0102e400141b5a621800b00c0c02c080d450710141150f40c10000000094040d020850300b910001d051000e000a1a00d414040c0e0030071500c0f5040700c111182c07608010343d07000d095115107440c180282044005550f444030700700b69031024941705a0312030b624041210010342a6019111034440c42c01841400080385 = true := by decide +kernel

theorem cover : BRFrame.Cov 407733812 407913669 := by
  have h0 := BRFrame.cov_init 407733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 407733812 ≤ n) (h2 : n < 407913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
