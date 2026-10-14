-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0544
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:21:28.546549+00:00
-- url     : https://prove2.me/submissions/96780f36-17e1-4193-811b-a4d21ab55ff0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 97661870 ≤ n < 97841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 97663120 1250 97661870 97661891
    0x1208070203040603110405060a0c11060c0304030b13021c0506070503070c060c02070b040f081c210b190e0f01030c14030c04050115090e06100c020609030a05010617120409 75
    0x12400d03030f8007a00c0000c203e0780c4e071054243c8009040c03407038084095807240d1900e466006c452030302c402103540340c00c8371030042c44c101407943d102c0c1a0480c00081c43c1025004001c20803a0042e0380e05c01d00440c8000001c000010312204909026260000003407041c000e00c0020418080b040f90040e03842202c03503a009c840800c02d80000281241896010f43c0301ca4200c0801080115880405014007810741d003012044139000360003205c414510710441e10f0300702c01288600410075070740e02c107050811030505080b000c003040c07068a03c1c000c1080c80a110a90a072415043c60040c40540c045004031608400407000b000010b505684030f003030340524188198844007152208006264405001e4094000380003001000340d981d41c2c0e009000329001c40c459810004500150100d8078121045005000ea80e000d4040003004403400c030140c402d81d80555060764060703c180038100311f6550402c628955940714600100b0010f15100c43c440c072510582d401c9a00603001440801070501c0c540c420380f0111212440301040a000d0b8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 97664370 1250 97663120 97663151
    0x2130e070507210f090b0a05070f1202060601030b0f0121060e040501020a02011b05030c0d02040902031005090702030703120b0a030c03050106030210050702030c010e040b03030c0a1208070203040603 87
    0x103041c0020200401d840324440c0001d003d1580c6011211940c031185900c020f040c204851a004034004c50500c00424404110007070302c50070180002921420030b54240c25440e4071001003299140000038010b80c080e5082020303e5a2500900c03241c0d00056510468040c1e001340040d0140030b48090300b01c402d00c0c1403508000e0781002500110000c02c2d00c501c18070f403a0b0415040c2a8040d5210181d06000f642c01d055856100c0c000003800e030400410255155401c548483d00a000e05611040c3c00d0004180c080c000801c201a242c4010b502419810440a07900d5142c4401c0c44014800109180c045d0742042c0506d03c0401d80007500b076060091038440c0000c0c031100b4803000032504c5000780c00c0075100d0407480300084200700c0154442016a07000715544074020501840489580c070405200a40640241440b10301e10b500902450518000041c4003280d08404503001c00e145422401ea00d440340d034004041c1205009a0540b1a40c0c0340b24507207081c290710302d00840c000c0d540348942d1017004201079032140440040541e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 97665620 1250 97664370 97664377
    0x40b06090c091002060406060e0601090b0c1f050603070614090904050f060f07030e01050c0405040209150f07030e03010b090609090709110c0d031a040f09050d02061902130e0705 78
    0x603d015140700008000039616903003110121941841c101c00412180b03866001d5921a545c169921802c990520b00860459080360082c0d0f46580300d40325a2204000024103c0300e020080c10b1300000303035032402d0b004044c5030003d1130740000f083c440c0d0041d480d443c0f1356100342105c0c60810182c8040010381c4071480c05910b0b088110f1004912401001c0510007640398441e0540e020304c0250b9028802041500202800c030f42c07084c1c2d240103401108010400139814160050030851030001c048000060301c02c0c0140b01c0f07035030004d100c14504403c0000d82c4020950448120003480a058000300640040040801c14200c0c01030319241c8510300f1400003410644080110310041c201c900310074003100403035414690301c50300914070450a50144a8144000510a1183c00894070700ca911462881d444002880010139a0500c80c454080e103c043e440c1c04150100030035003120400d58000c0c0650310305a42c45000081d40c106601c0d040303a0041000c01c071a4a442c10410007901c03651000001241c8480c2400c2d01c0920 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 97666870 1250 97665620 97665637
    0x2130e10020705210a020607090b030402010c330f02040506040905060303070501020a0f030e1603110a031e0c1703070b0c0909070815060703090b2b0902040b09040b06090c 75
    0x1004c00c030007015403400c2400580000c4401e0b07002c1321919200c9500a0700c500c00c2c103001c1c0700000c5d842400000c000d98450030b2070f090424000c46116041d5001c0c00c4052003070075a108040e400080038840340000090442c0f01c0c4001480d0705180c03c608080c2071000282c2c881c8280e20a0401c11074454010a0386c030741c0e040c0202e80c9095803080c0215a41ca8a001c1c000d42040800811000031070326203100210104800301c0d030b07d103205020800d00780034541903a940c210342d0300d03418040e142c0041a564002c000120700c44001811030603c00035003e442c1410346030070711118030079401807031442c411084918807506001007507408030741c0e00940d024000d07624070080ca801800f032070401607403083c010024081d00316007180c0418040c3c604030152035100d0080005010701d80c403460340020300151405404100121055010708180003044100c008031310501c1e2030070b210805002c0c029102c6199650405411880c19200b20007070100c082c0c420481c14074142d120b0055651004080034040c0c00d07484005200352984108079024034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 97668120 1250 97666870 97666903
    0x405060406030501030b0f0610030c09050607031701090e0703140a022d0108060a05040b0f060403050601171b040207060e01110406030b030304140d0807081602130e10020705 76
    0x12076685000a02400d400e210594140c183c20010840b20140c0c80740c0140703d0200649010452500f98204a001b04404400c01c000c00081c49000b19030759031281c1c000d00e2002c1c000d58800750840d000d414039000005041e0b02030301b2060320701091914518404541d95044a81101c41040315130f52950500e4100390950711300075403110390851601481e10360b10b11505401441180c0703140d10250074000665140070256081544070319110320402c410f20b0190851034035188090311344444501e19a01065540c0c01c21b401c1121a50440d00052101c0e64912015035911241e0800801c020400c1c3e015450007090502c050034040d5400081480901c0655041030254020882c02000013a0020902480302e80060040e000000c1c20080d005c036031031a001050745d080c2c80c000301e8102039003600102006a0340b901e0f01c0c0d00302d030014014080303100030414001c0a081100050801481030094a20410002e081c994212030303c060315120b0480f1000780e0000e4500c1d0706410461005942c2c0d000750510038030b88a510000c08004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 97669370 1250 97668120 97668127
    0xd06030c090510030b01090209010c15091e0201080703020a110d020d090501030e060703050402130509010605151305040b03030f040b0406181401031d0a110a061407020f010203040506 80
    0x80180040d003810455490a900304019150140b80074100c000d84e1001501c1c08000300014416800c05a00804686005040440303003207880340e0f41c0d0220715400c00f0410003529034070140311051100100045e0900c1c00c5116501003028071641c00688800c1000e0501c0f0100759020039403d9400380110390031441c001610040300c81072010305100950343c5800489410000303128540020707055010340541108108003201528140d40e80940443c01414014403d80c0e025860500000600b0074611469000d00c1200f40003081260520080c84610346c00d42908801c0c00004000b105404a40d4039294010780344c003210041404c83e8540000303032441c0200700e8000804640010f000400d031b4940001403003118680c0c1c072500c84515080350031840c011040e202d04000d441c00c0066140083d88aa4880c103508046211040c01c512001c9030f849180007415801100c02482c2640b0300c070180d1502043d043d006200c1413030081110803030700c0c11001e428007580000a0140c0c25500b803442190703000b4015a000703031801400d1143c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 97670620 1250 97669370 97669373
    0x304020a030f0b04061a060403110a03021906030b09070e0907020304080d03020405090901060e010623030106020c030c06090109060e030141040b19090c0603020702130b030a0305070302030d0603 85
    0x10350800613601100e000e45800c0700300b12030301301c859621402c01c40000d180a08203440c645401d51182c00b00b665241e802110b084000c00180d8507140700c808074140d050f045100d80c40c02c0141c05812038800c0e4044500c80c0101c80104540d0a620059043d441881929100082c1d120f50005078510300841d00004041d0065401c4001150b1381039000d001202e0b401c44000039152690300d00d4500300c0700e41c0c0c003640f19080104001030000300d000322140800109284404ca0100400388881c01850300217801100040e0031100c014082c1d487d080003c441d45a80c121650361604259038006080b098551142006200052289000c030b035400b035100341c14211080d01c0b90410b40a90013004c10003200d9407000000d1418a21031208400012184034a2050350b02c115003020580ba001c0706041301c4040da48400b16225203411000300001c1025035048010241c40c0c0f001b680312080d80c4100603404200d0820060b903280b40c440b20704050707603000622074103454050600d2561504c80b82000c07411407081004000c61a400d1050010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 97671870 1250 97670620 97670633
    0x30b0c0d2a09050a30020d03030608010507030b03070501030e0f0307050616140a0e030c120303070e181611010c2001020306130e0a0f110f1804080304020a030f 70
    0x6079082640e032282c480c0d035219001c01031800000d0040000c18114002a410750b600e906801000c011903240b24075101070001c2e0700281003060291030890000342c071044100320510b02402425004503080c201884140c00c1c2c800440d94801441c482c043c1059103e12a1410b82d482c01e100f166500c072101801e0b0785c0e5581c0350741415030b07840310117403100090035211442d280361503403180740341c480ca03601c1024a080c5070905549080710038009100d074080e45402200004003c560702d9425803191600b200016585030300c0d21030780103084002c41840e414084c0041003c0045200c400d2940c1507413040b4080860301c07400c00e00e130408807500d20542c509101650318160b0000801500201952130948845881995481158203907600307070b010507104290042c03041c410b00e07045140c003074010130811801d0900300c0d42e410f0004d4603505080c2e1104102030300d000200c580303a0505424800d15003070644000756001406600c1510a42841500c002c001522140c00803010504540d186a911401180c001400011031002c41c00d042 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 97673120 1250 97671870 97671941
    0x906060b12070507030906030b060903100501080d020a0b0604110c0604030e190e07080603010e010c03021b06090d110c12010219030b031203090309060c1b0406030b0c0d 74
    0x21004150700e0006100c480c0308004803000f0710340c103507a08040075142110641c0904440c0e0042075002c08207102450868408010000210304813031008511540f400da612400c0c038807104256411034110310340c0c0c2c0e00130609440e68070b90400c80548d0001584860004982014000c10420020a018480074802455400480510700800444021445058103216170082254030f00c2103030109080000000c1c3c0181c0546800b690106028001054448604d00050300b100c841c5082c06c0301080e404120a04c1c3d4200011040d03200f205040000c00b0039080c10080c56581e207020003245410044602c0500790440000c0c01802c440a401602d945060104641402d0103900a030910041140441001c6628a44a0701410021003000750242540e044501100f03030140e80300914007015480100f0281c034880d180c8200803d41201d400002c3c001c010b0300411101321600040d01040c2c4260308102c428004294100050740d00440c0c038000032a43c4051a139161400b9010710300340a000d0440d20350750403a4070351400865 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 97674370 1250 97673120 97673137
    0x52b02030708151012020603040615290f0f160606091a0406030816032f0f16053f0106080105190207050732040c12050a0906060b 57
    0x407100d543e03813060b0103032040001c1d6102d000c100b40c3c000c81d0b0b0000035092140041d07030130070301650000c6503001030a0b0f035014540c07c00b944555481c0c0501e0321054203102c0c4890030081140b0902c80e0140c03404410400d0441103004a4041191018001a550782d2007030f0000d4000984035407001c0c040c0426652848002c008000c2079000e02e013440d030141440da0b042e18051050109482e8000c14103414940300346504bd030814101c003000c4003803110058613035000039181c00c00240340c0070f00304a403144140c51001c542c0d0300701741c0d555045a8890344501c1d1154014168034030700344140c80c41136580461481d2141246d01c041140e00744200c403c600e036580070201c06102d070908494a5410140240011aa1040c54501b281c1d01110803511003030380700c12250317004996a002044024055011948210b0300c44d52900303c5d0302c204000c030700100c01e00d490035400182031410756112440070848007003212105144002c0c104501b414117030140550345100143d642c482d04e40c41031465a4008404120031612803118032441d5101111 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 97675620 1250 97674370 97674403
    0x306121c18060309031d0a0b030f06030c010807090e100e070c061506090302210607020d03060e2e080f010209130b1e04020d0903050714030301052b02030708 69
    0x1c0125406009000b0903160b25416554000d1424100081850025198059544c03042e01140d00207420321144005c1d50050801d003594400a0520004062401d601005402d043c01840010004c1280c4c0090b5100111707984204141116a500c0b444a5076452182e00701c00c1c006c404003000d1003411079110300508402c0b44120400c000c00c130214444034864038084d02c541000620050801d00040c1010381c0700c0040b0469020004841e00140d4045600f860341c11110b14005030b0005180c0c1c022198540510f00043c02e0081515070342d402d01440700e00b203030650b000703444e40d00d691180313052044121080000d41c0104240f8056070b440c40c80030440b2502035400003108a00c01c2683c50f90301307444500b00b07100d000c0c0c04010081040088002071010f41e80e00c54540c0740407641c040d40c00d0242c072a410b00240910002c0e244a80e44480d0384100d00e240060001116140d001030550062006006540710083e00303510b0900c26644c1116150303900c0074000380c00d200c1d090300290035014808001076880c100003118103020b004400d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 97676870 1250 97675620 97675667
    0x120302190c03090816051201020c06073b0918070b070308010e01240203160804180b0609041802030d02070807090c0e040915051801140c0306121c 64
    0x158000c0d40c0311455100c500a02d203511170104020310700304007030b00720b1035640000260500c0007a128090400c10203c4500b00030814410940c002900382e502400314001e80a4102a5401c0200c0441b044180485260f2070151300e40801080c20a9071061034005080790040842e29541d803541001c8619420581d012408543ced220008210900c1110072035050741c0c1901580d00141410b0099480a030070007208440640c00200998100c05c80e48041c00111240151503103595a86800d6886440b030040c190108806441c081030b004c0d555130313541d04544241d10202c9010600150400d03410703000101c0031400075031503c44c42030740028041d004501001210644002d17145507655403840032065075900d209450005410f500d16984070b141541c00b40003050f0140d0144044030780c040f0b4058040322030031394020900105403891000d542009000f410050314090490915a0a00690848260201074030552107180c8030034506066160402403082c030480d200300e031020034040044000e41100d4480485001180340403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 97678120 1250 97676870 97676879
    0x180b12060103121220070f080f041802030f07120e030705060a0b0907020309010f0504080d36030f0f020603040c0302011b080a030b0f03010908092704120302190c0309 73
    0x901c100301c42402e0840c10342018144001c05d10115034400c05049a00300f03082c06042d03000c9140100588451012207200c03070359603414070450403080b120900d54800d905004004001045041c0d007107064001e003503414114003800300f940038000900b0114404090358440800c000090080001d0120f00840032188104140b203060414410358000c00c40302c400c00b6920800003003015500c69120010700d2092440c100e400c0a840d002064200801c004c003400002c1c040305417a003100900990f50f20801602d44280c1f0104004403040e40541a02034840500300144e07451541d401d2080130301402d4032a5500038001c40e982e141602c0c00e2004d9400c2d9000580c00205440c0344a43e10300c40719015600c0050300420414240072100100f20081c00c0c50314541d58200c100080c4032502c40c1c81c03d0040d1300d101e030311071b0039503030b440b40c05443c14400c800590244800f101c0074801841c450b00809402d1132900a500840004502103441c041a40a803051002d41d1003800c454121145166621140a0409520071744e14025200d648 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 97679370 1250 97678120 97678157
    0x2a040207050d0507020303090a06050705012f0906070c03081c0605090a0b0103270506060a0b1603020120090111010e0615010c0501090506060a0f180b1206010312 71
    0x8000004180b0382c40310718800c2c12240158040d021091001301281c0c644030b103250114840da140741c0e000801081000c00d0b41020010b0a010341011944002d990003104644031403074103178801d03050342d0b06a440740300040c41203000e40b5001b0464070708a81202800f141240d891800254940c8490600b1400c400200d140d807489403a0f6005410880c3d00082c640780313554032002140001014101c0c0366606245d90307294041c50090800e0744e50300e403070403000c80c80c030305104013508100f801c004000701020320070302506206004404500084d86d041040740a4034000d80166490282c0c01498070109100e14000c3d41c845c1c2030b6820380b010f401000346040030380c1c903180b6881e16028072600707951105132802504d8000d80c0c001022844c90031000c030000c080501d0400c4900b07038162101400c4a501c10004e0340c55421100810009051115803613005000b0340316021162490001a0712991204803070010805880c1c4115100507524a841083d280ca440000c3d210030396941d10f000301502c3c0050031040086a0040510b15250f4407 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 97680620 1250 97679370 97679377
    0x30203100b090708090c1e1804050a06020a02070b040b04060f0318020402030a060b0c06091504051507030b130c020105010b070b0c03040302160602010e150702030a08090309032a0402 80
    0x4014100c0c40142e10749107003d481100c4c0041000919114154680fa680d580d84590003005010304009000d002849009201c4490b98100c80203658a0400c001d22000403400107c1368641c40e00040c0043e05d03030055000c100d0400000f0780c0048142c850124001c2113960340d040042c000c4818684401224446038601982511000d41008a0030841d6465040150406030021540100300080c0068001d480b070741c480c0c41c0c9420004500645a00c80400c0014522007082004113884001c0500007003840d085c1c0d00d80d55290080e45400d980300380000d011170702280c041d402240103044000e0a4811060310006103a005280f01c1c06da5800660a140c0002420a952400c440c056900002c000019941e034001d03140700c036071025004504601ca401142048860000e140e00d0143c01603500105003e8108800607180040007400b0008644840c824031603043c0d0000103c0311010103d051440050303450b13803030440c00c502801309843d4060013003ca038074803468102c100942e0b2800c10351044503100500802484100d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 97681870 1250 97680620 97680641
    0x11e030b0f400c090216051207050d030f1512150b0114091302030405060a0509030901050d1a030d03272a050d060c0e011701060e03030c01060f03020310 67
    0x1e140c1c541950207400b0000c0c810640e18042c40000180ea0740d81d0784030b4022688040d032a003954851110850082100501c0b50000008015404905080c2c403078071034036190805814100181540c428500c868040ca50b04525000340c1c501180001c9541c1d50311160200d524000021150312850231003040e200c2d106403184060040c0706031b448039a00c3c0e05120421010703a014000007503006804009005503041031380011403007580310314003820207810031020100684c1c0024127106100c9c0c0081c0b10b00383d0176036448004c3c0c0701a01614600400c1b40b00170300d141901c1d880102c07001690540925a0a1202c0603010380281d1994009582c50f060071000040f140094407100c0807004011408501d0b100044200448001c5c1d41028080ca800c4c101da55038400003070040200f00b800f11049a02c5071030a45416400400c0752445400a0900041c08144e68103103c031031220500402d010b0000100d241c0481d907d08009450904103600b00821017140c41d106154140c03181403200302d101e84105450750700406480d0260303d107810b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 97683120 1250 97681870 97681951
    0x6010807050904020f12010303020106050123120a0b0904030305090c0109180b0316030302070f0603050609010b03070201150815180d0c0602120a05010f0807050108011e030b0f 77
    0x70070b590003044044c0d440344800d90112181405400a1181d400700c20701d008600c00d40000511030b01c0c10740050b0501e8202546d000c144078407030003940d81400080084840b021030354003000803a41d5810790054014400003030110b0708040000c00f04005c06403d688918051a20340c02103504494568004580120031405030210b01c98480d020210b1015058101d05c0100034018191205d140a450360003c01e100d882e402500182d2000004105210002036504040c15842c41d05100c5450100b0108154000c103203d104444800040000c0c180b51007907000d4002e00d000000121087ca5640b40305c40d5030b071a041035044030844860fa000c10a10f0459024451150820a000d04110b0282e400c0513150b501e150101a18416000c10080c04443e0102c000a4030840b074905001a4550400c00c59003001c0c009a0481002a0700002c1d082c86140e0304848501d04640203000008000341540c0142c089101155100070104c080d02c0b0140011a0301c054001c80c800c0c0700b444030380040400c0301070b07000c010380b1012460707180c61 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 97684370 1250 97683120 97683127
    0xa080a0602030a090209131208010803070f0203011104080105060901050d02131a0901150905060f090919050702150702031303080903011113060e030a0206030708190f050406050601080705 82
    0x10310540c000c2c56218082d90000a000800c81c0c0220f07262041c1110004298071044e0224801c2005040c80081c0051091504140560410324041d40c0c0c0d100304103004c2e0040340c0489880085607800d41040071400034412006442c1ca07620500c00b400390a003a600c007071191200500220780c0e810003c07011800c2c0c5070014160742d994540c900c60b00b0010030350300084414841e4140d2541304d903134564801403402821408240c00700301c3c801d031000418000c1280c0015110705010402d4080701007110f41681c2801c00e0403070311040140c44108040d01f600440f603c010800314100410804100d801041121007c00e03001100e4400355608070049860740710780f01d0300c0006511180700a2000c84c0060000d0190000060700001b03020311303404010a001e80106d064100700110340c45046c881541d000d44070580c106d00c2500103103a0884d00b940060001c1c04000d000504003d41980000c04151a501413100ea941c100c240400511000b856203602924081324149c80e04d078148404511294856108a40318454559400c1d0a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 97685620 1250 97684370 97684373
    0x708030105060307090302040c050a0201200315010507050f1c050405061207020102070204050f060f01080417032703090a150906031107060e0d020106081b01030903030f02070c140a080a 81
    0x8a0f900058080c10400a00f030202100607141da202e141c80320000c40e11107a460345581c1000030b0a6803080d0000101e40c0c1034031480d1002011820090340e80100c0c6150303000101c03101c040f00490b660301072503001a2840c8a0044122200600030401c14010f628030b4000810102c138100c2c0c00d0303402e07200e148200303030b00034108010740c09050403d400560740241a9100241c64200c13550001810b94205680c4900020158002d208417841e00a25020420000b03007020201032070310b6262003d4031504003200c03507140c080000c005030701104a02c49070702c1c490303805c010440340d482800744400b9070b070303800c80043c0c240606240344020800171602d00d4410f0b640000c6a8401d062141080300883c060b020600c02070213407040a0061900141c220701070310234248022401004100100d15000b4203441c01075100c07211542285181d03480703030000000460f2a40c0402e01300070400c10303114581140240009141842240d102180340001c000503400a01c040319a1440d01070040312100d030411003c0700300c0b440351120f280e001d00400760 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 97686870 1250 97685620 97685629
    0x10b04051309140c03060a14040204050606130e0a050c040e0a09060b06072109030308160c12050702010909050702070909020d0f0515100e060d0c0506040609090608030708030105 78
    0x403a007011a000c0440d407142a0350700d0030400c034000e107400c44554025a610742e5403400c0800c0341c01e84c007010809060040c182c202c0d0002c2940a400390002e401340392210300090341d80e141e034011507045800240f01507280701d40d80c85440712428404d54000e18a5030a0a0204e000f41c9180000d079001c0d5201052210345944907980340800034032042204513011a00d0f0348045600780d4504014203142ca0281e0a0032045410b421100c0c10015100801c0713405100d81a402400403031380c08550150311503022030110100311955601500c08145c2c000008041c1d110545d036803420795500401500f4003901c00c1e00c40e05a429100e0107140e050740c10131a8018016800300600b0000c0021580003030741401d001412907a0b0340030080d01c40c03204e45a801c04003038503aa403118480c0806022403030a0183c0c03000c0403c0d001082c140c20000544041c10010702040e12940080002c9401d2000d10a034850003000f00901071035a0390b0345d40c02c020780780140e10711891000d00d10b000000958120040f007102e000742d81c85241c0300c2c5540c0c03c4c00c0800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 97688120 1250 97686870 97686889
    0x605030105060421060f020a0e040e060601110a0c0603090b09010507020613030e0a0608061503060105090108060f043206030307230102040f0311030f060a020c010902030304090204060314010b0405 86
    0x491460b0220310040101e1710701c2c032410030060b40ca65400b5a803003100c02d0029186502c001116070182d0710b403981191121101180c2150070241c24030b05030408640361101a890b02c000d15001800c00c0300440300000e5102d030103074800f03101319124285d5040c5580e6601440d500f00c1390111024405600311030000b90f87c031004480c565540c0751181c1802c0384681c80050106e40f4020301c5030004004118020240b010601d00705041c40d6040c03104010592451411000080039070140000040c188440c0c0c0b0301241050350b49030304904d010100030340b0410150b040e078413401c500d00196200c040740c0d0f00d203807100c4502c880a034608100d200300c03009801507241c00610354940e0046000903044d200c043d0291710b01107a000101b070000704001d18040ba802040103081d4103004260341ca1508800c0e200360300c604c0003034090310408101d49a101000110050721103070410f000b54090b202e0060b00030340c180000107020400031056406041542d190703540030000070082070713419040b0780802c2c020035510507410302003007102d443d103107860 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 97689370 1250 97688120 97688159
    0x8130e0a0b09010b1305090910050a05100b0a0905060702120d020c10051e0702010c050f03040810021804050c040b160b010503060717071701120209090303191a1203040305060106050301050604 84
    0x84890070314009d00b82d6030454030280e4040ea4000c0d25982440005040d240c0c440015111481005203420000e170400b9080800c1c501c039a0b4000e040c081000419561000c0c0782c600020a02c40540d030644080b040700039200e1950032522485100328031060301103a40300340c0984440002d603c00d0002484068480c030001900100b03000c03810403016040d4040025400c0c000001d00c40b1050000b161554200200780d418200850a001240d81c0305100b1080c041034044130100e01c01e0001e480c0042d040d01c030441c0f504028411a0040c00325607000184070308050030103025170403159000c1c03078211074540d0300d400801da242d64060f03030b400c000120383c40344410700140d594442542241c010300f4201016914207421803111030007644050b540060041d162025420600312940c1d009a403c0040c610310b140c40030301a11071000b80007890342440da48803120310300840c200144a5182d00000d1046403001258101c0c5940c0e40d10a0001b00c4040c007442000080039801101601e040c0cdd64000c10341d604181c1071520700115001d202c503c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 97690620 1250 97689370 97689373
    0xd0201080901110c0d0e031605060304110a080d08010b03040507210605010e07021006081015030231020901050f09030114090607020f0f0a08130e0a0b09010b13050909 73
    0x1560441d000d040024841c4503000d1029111740706a28802400c0701d01802d006c1d50003900822000c050b6a08601104019124200c07403013034803520741c5d042400d401414245916000071a00c1c07030114800348002000d42c0312106c1a44c6003415a82c0f075002c014003900058800501e43c1d44400800c0c0458040c50380f241003101398548000082600ca5100c40055944c04e0f4003002802d40c91105000d80306605100d4110704d20041c0754180525403500001d1681d03602d0491090000340e55920007021108070400c428801103130010040c00f0002483e0b441825540b82456012207002a40d24058035200c036280286c0c0c801c00c03016140d1905107424001440480d43c005540940d1556a8401000a00e800c1625032809054150f000b805a450605806480c110203081d2401c1c003980200075030034250400090740103e983d031018440d17465006031800e40c0c0410b015600400c801513080c80400600038000d500441441204591003207240c3d0f030360342c003c1c040c5218801c3c0050414240600034070680c00d01c1342d06143c100c0007900 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 97691870 1250 97690620 97690631
    0x207020d080301120b06041802130207080c010b040b1212030a0b030102070609030807021906092d1a0402130b150a0903050f030a02030d0b1c031116050d0201080901 72
    0x6441c4521540709810552200b110079900300240b0002000349071340321070150340070040c3d0b94000074604840e10032404024840c2c03a46007205014100b0b6501900d040c1076018921039200c8d00c0400d901d43c00380c10000c0c212030003149071200410903880c1c00c1c029411000d081c01c026120058003d11900007c0d40020071180030170b81c0300d00f000c1005803402d1000b0300005001c5c4030001400b0f020342c41c00400350034014103d0f204550040c2026100c12641c0c1c4011018650700c440300044045e041e140120b84880b03480d03299039004c05040042a0041c1407000c580403828468084000340340e00c91201000c05480958011350420110302045881420035804245c252200400c11414141d144594141d00e51100d6400c40010f502071400f081001820450303061103c5418002e1030501511800003980e81c010b03406281c0d1416240d02001c8010348031400701206848001803191540c114034100546444c0e480290174a5906c13070751034200304108100301c0030b0301900c078010040c1d03885020a400454910f03001801840d00340d540d0f030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 97693120 1250 97691870 97691873
    0x1e031205030717070302030f010e07090501180f081c030612021c1e0501050c0306011e1103030106080412020a05070501030c0324060206010b03090a060504230304090b03070e06040207020d 82
    0x1c1040d43e02c41c1120303175805a44c1e4070f001c0340150340303501d41a4070a40034041c14905114800760468054402d6500c00c1ca009580f4102c4024000e0309902c00703900c450b89138030202d1004a0700c120702103205200880c000e521b201c0c0550051000302c0c112440340c890000b80040c0358035420010301e05004a8405e010303083c00c000d20900d0881d03c88550a980180d4206440d84004654000b001800e001d000c0d0704c441d248614070304601d0310314006054103e042140340405d9006851040c1518014850b03840205446001c0320744030368540d04041d151510603901510003050007072508101c035200103280c0050b917030f100003e0107150703180034015406440d4211440061688580c08400c0f901c607560184442260145440520305140c40d102a0404c032041c1c00c1084c0d2034a003001000001d00c1c00107181c0e0f000c15485200000c450341c90f420200c0c03150030341c81465503401c00511781c01c00340380c2c0d00040540103503402480c04124614042d0b003055550990b500c40c0681644410000482d140b41950141100d01d001810051501c0000e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 97694370 1250 97693120 97693157
    0x203070f02061c2a09050901050402090303070c09020a080604090c060f020f0307050a030810230a0503010e0601050f0f0d17040312030f0f0b0603040221030d061e0312050307 76
    0x2d1001d000307441d5524916400c0c4c0150050645044c2d500a003844c1e049581072a0203e144954140607090240d41c0000f5111400d8508108445245411005941d203107629551400040c2d8010791003680003642d504081005031809100d503031122a402888000700c00e140400503106c045001c500a0b096004000300c00d840346100740002d0803245e1042c0301500715040e40d80340150041c1c401034030081c0020303612a010f00034039040901c0d0401082c1a4041d00070324108400c001002c42031075401c602d03095400d04410400c0c0100c00900382e0b058400480301c0c05507049440c02803005003141907007001c0d440140d51003078102141040910762a84200340503a40e141680340e03101c00d54035410020452000964800744282c11804074450550f400150940c14012031100e035000403624080600007900ca4840c041c0ea0303800c860340c402120302017a0707141010340380c40d416610880380040005104541501c10b800c640a440d254081822405072540603030304404071159801e00702c0d40c90300000c100c1018030180aa04025103401c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 97695620 1250 97694370 97694381
    0x30c020301150308120705031b130504020d09060c0311160203190302060a15050a05040c0c0209090a15020f04030b1005130b0310150b070f0c0e040308070203070f02061c 74
    0xb0713403016030380c80f0488515500c00013001010744003081414018811003140500011003400c0c45200704603107a91803001d0b05501d1041c503510031a4414070010700b605180920b034010754880341c028031041000030550f800507010388411042c203251b070700c408004250902030001801d00c445c42c005002ca407916103406e4544001e01e4054002500586d00c100100a80040c1c2405102c24411101084c0900b031480e12000c03c414007010b02400c0c0c85540c850061825192140b142c44101e00d0300100300002c01c1c2001140c80f9110182c0f80421385108205194584403014580200d94095404c0403004e80303010310310b40710b1058034070703001c0c10007004605070f494005460390b01c5100744031081c0e44d1040002169903568041500e4030110300180c40b110360030141da00c0c1428445828401c1102c50040308581e5070307403580c980b008100841c00c0703000305044403014020800c1c0c0c40c13102030b19215522030344134658540c40302c2c80d040ea03030b9000f0070320010016080d000207100103090000103044220010441000180c0d00a402d5105540 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 97696870 1250 97695620 97695623
    0xc0102070c0303110709060f0314010b13020d0b0f0d02040e0a0503030a0b041a0a062a0f0303060605120109090f02100e0f0a0e16020c1f09050406060804030c0203011503 74
    0x5440d510741113000241846000c0c02400c0c0b080c002c004003860509800c8516440d84000381c0740308580c0030b030502014001e40200c40301d02d1000b80030a00c00d800c045018002900034207214082c0d42d2174110680307241c0c1041c400000304c15100504050002c2015401c0101908c4241d201d080075001d00c0280000013641000514000c01411801041c00501c0d0801c1c0310031241070702e120311400b01c0c42c03040305001c58a64015030016101d00d4a0321221050760b031080c160b40165500183e5100d100d02620107030901c05003d42100c86540b09a6090001c44d82c2d1303040c125118050f42c407004a42c00325583c010090a4030070380c44442c0081c45110214100701c15500003030415020f00d40c1c4003001c0b941103800c0d0072007440c00001c1c5200c081c0044075980c10700c1d0700384886454004001403c4807846103c10100b0403030b02d0b00804c043c101100d0002c08590440a1007202c000c2d03200c0300d41d1440c10100b100d114000c03d903460b10780100c10640c0c0e42c82c0e460b446540e0315070710206c0e030003c004030342030383c05540e01c2c80200d1003540518100700145 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 97698120 1250 97696870 97696877
    0x20f0414070903110603130b060312070b01083a0212030112020f0415261c03060b07080d0203060f040f091103010b03190c090c030509100b060f0c0102070c0303 70
    0x140c0c43e6050000040d09440c2010344036400400400402c900018010114a1303000344450400f036a80d2004240341c07004000761800303440c60114541081142c605c031141c0c140c2d4a54000d540d84079038080c5103200188003d107802030500d040040d07080240c001c5401c0311180d0303000030720440d081d54031499043e940540c400c0c0c1001207240751900300e400940c02c11407011008400c1c1070350100003160b01d43c0405011000540280c1c0101141c50340390012a51111451003680d5200006680324602c5100200541c4428810500c1c00b10741895000940c0001c5001a901000d420031481c601c3d002218400200035440102407a1b40f000e82e10003c01403a8803184a04145003159800008903030945052118080001a2550748660305000305140c0986000c1950071840c0ba296580c11a0321046180c0061004101e811009a8900d0311a03400710f160b50542045008000080640728490f8202e01024280d41a04000c1a0440d10400180d29844c0c0d1042c020070100031694001800c01916a894503030310406980180c001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 97699370 1250 97698120 97698137
    0xf13022a011802010e0423090105010303081501020d030c0507060f050915060607110111100b09070c120f050c01090c0303030501080d140304060228020106060219020f041407 76
    0x40303600034482c46806851440c1d000c045002c0c5a4002072401244d1500c4078010f5840f420b0329560000144100190068080d0744010113123006c20289000300400d100942c000f501180110307903011180e540200311507406a010740204094040280c01505441400e4420804108001004070342c0600c0742c17034908540c6400118032400d0002c0b040745481101001c2c2c000c52075108041c00f910ba40d8a0f012941035035400320101800270351000068511a0040180200c01d000b11428119010390700e41c04408000c1d000c8400c02c07490307101d0740801c0300d82c0d243c0300d0380040c44584606ca01b06140760141311030710111300300c13071a0041c0f42c84440481d203820340300329600440d070792400f0001c140100f603014000c182c0503069a1004103403100729503034014200b22145540100350100000414148030381c5804540d5190001c42c2c0141c60303c5901228203924400384001d0000652a008000c40d0780d902c081105d40c401c0016020620b039582c0076808012441c0c0703110301090340c80ba950301200303a031454154001030b100d41c00c20f0325110755 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 97700620 1250 97699370 97699447
    0xa150509071706030d020a17070f1b09050c0d09050c1201060503010b06120403030c0905040e0d0f080601020d05030a0609050f0702010b0a030b0f041103030c0a06060e01050f1302 78
    0x610300207000e1510a400c8181020b10540d030020703d047e05542c120407941141440c0b5040381c082c1d481810300241886040c12031000600940d007500c001001c0380c0d81c2c81907120701e9490b800001154026030b018445104100140d841c00d4810f60462101103006900b5101c2480c04500060301100c1404520802039440f010100f000d45820b01c5038404001c8140c81f000d203442c0041071031099001d80140010241503407842001c0580b0700c60165117001d0f0901030000c020503290050465074505480b13030850001403c00e05c49994040c894200070f8000c1c40c042c0c00401c4151f2658800317070f80300c0e00001c09079210103a40e0040042d40d20818001d01c0c1c0120f00203107050400e42401080242900c2d040304606000d141c65078010000680c510103010f910103800e58424032580c8507890204410703cbd0001d4001d60611000c12410710700340010850001051042d8001c0005030313074030322000d6440b680034410654003548000345c18403182441080d104241c5c560f64001454203804500da1480755045030404600345041190b0180f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 97701870 1250 97700620 97700657
    0x10201050105240c120d02040e061207060c0314040f0e010626072102030612120a03020a180b03070f02030313030f020307060614270a15050907 63
    0x1409400203691450032000031503030242e0b40c00c0d0195200f021035580060130311080f0768144444081c4403500201d03595a10ba4030513540d4040d40040c06100045006c8a010510300d26041001b2101c1101150242044500e41941911740c1480850280d00b4008548598140c0101d10401880600321b4200e07210705440c00c5c00301d41400420142c000d4014000f00c0c200c01d01003d107000030606004a4102e2504003643d07106c1030203d41c583e10f00c08080c100702d504811011040d182c507402851044000380e45907102500843d104c1c550340d011414561481c007104000c4850810310035001010710810600300202500382c180821007040800c0c0c2d0002201400c04000d01c030300745610034488c40040d5a50310055080d4103040c0045c3c820b040700d05030010700740205051101481c40c028015107841613005201000100e030307140c103814414444420000d02c200140c0784c20b64100707804180e00300441c1d0202a40a481541c03000f400c50020b05008540d000300081510000502c1d43d81d46003028400c0300c190344c60a181042a09181 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 97703120 1250 97701870 97701881
    0x60408070f05030a0c150c02030a03020c0f060f03041b1a0904150303080613060807060909180b0f040503040b07030e01030b03061902070c2105070501081b03180d02010b010201 77
    0x768801e130043c080b80800b19800300365a41c10303120b11074819440015181800e0351b0020344404002e4250003680d4002052540202d0020812807050724140250415002044541c2c0301300182140c03c0542800440e01089503200c9a52000c034540000040d903030740b5040b06119242900001c0403031702d080001c0000300350415008042000345100c600d04d10140c103540d4080c0c0300c000010923640c000c0c542c0280c40340078a000c9070442c8006184440590381c03134a40310780c002014000d0500903c032146040c2140e992110442500d400c90aa80000030442241c840102480d0b940c03101400c151040c2c4070a000100e1003100000041581600c81d4551901280411001505842078903166601c01d810031010440d1940d00010019850201041c005a452180d4540b003411010160401a1800603a040e030010342d500300301d081181c03540200304855032165100c0044509900464070a0141500621101903070307056103001c0d5400011462080c03000591015440d0300e01603500c0341d4800180c0d100c011000303807940c080c440c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 97704370 1250 97703120 97703129
    0x90b060721030b010504180504050a020909070f080f0c3303060f0315060409030207090c11120301151b020325090b0303070201051303120206040314030603070e07030b060408070f 78
    0x340c03c0071f18204c8030300101444900c92412450b120000101089401c0c001c80030020760003440c8034800d00380541542e942c1c41090141003080300901c40b02288141000400d0580035a000c0000e04544c0c0034001440010040d40440f0f00220f800322042d01c50900d140701c80c080c2c0d688000080c0b66264a402d000b040212907a80403154041d40240c100d00f62030440303282040d86d119005440c00305ea0340015103000c03450f120b40c940c40100e290380382c041110400b036801651164903841d0401161407405000c01c01e0400c9110a120314800d210785005d1401c2014010403a505082d0005c2400d03141c130b00d00940100313003803105c0e0700003000005070700ea9030601000341300079414005003903c214100452901040403a50703901c120000039050200108507603003125030b201940c1c03015540c000138454100e030244034080c2d55201e080c0c03400c90104001200d210840704d6003500356442021700400401c0c04510700941240400c1b0040c00d031100701620351000002c180c172200004c000814584000300301440c034201c84800115070a402 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 97705620 1250 97704370 97704377
    0x61d010501050c0d080601200609010c1e1b051c0f0509030304120c051804050607081501030504050c060f130b030103020604031b18020a0201050c03010807090b060721030b01 76
    0x2255046000207101026000303900f802845915680c00581c0c08d15841003032540305031120340034080c0b210808500c503401103071101d0090000e8108a0010742c0d0701143d42c0101c2c0b12a80c4100c12603088148a03a183c1c00f03111034211034450242820340c03181400c10070316002c503d8510000da01c07100d00240e0b001c4202c1000219620b4504d040009920010b601c4e846148a41d801446002d081349003845501d0080c00300804004042c100d40031502040d080e0081400c64054402c0c3c00317035500241955000b5150288106c007401e04c9204031141010048d0300500c0c01420a546034426051019899203c020080808803180c1b030aa5403140740810b2820006103264215942240c4140700400041c3c41c0c5034291800d699000500c00408182000341c4240d00c1c130642c1c490340c0c4260311030744d003a55003d117241e0040c00d0040340340d40240096a1520401354075844288038410b0740c1d900800d07040003a442d15a002003802c040050803189414410f4540100c000a1002021302d0300b40303031902441500b90540316400c0351307040c2803c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 97706870 1250 97705620 97705627
    0x9060c0323100b09040b1f1b020109050111010e0609030912010606230f2b050708060f01030b0a060302041d010501120902030a060504110112020702030303070c02030709061d01050105 80
    0x103691201411030301c40d10703e01c100c02051200450780e65401c83c2d14200f1003d4075108442050401c5e020300c1d10348200c0c4040100e0140b0640c0398070031380a45003242c0001c1d010f849030714010b032a0400455030440d13183c0340805995610314031118099802d020850040181400031074840c1000010000501c580382c6407600f0750b81c54442d080045940140b002c0f1462512000201000b02e800306682a0520a80c0d40c011440345000400186185810b100400612540c02c41d61880b4807070344004404448098a5100101e41440f0014101d0319028446110992041c0f401107130000015011030a0a04584c224102003500400d0501c006e07034405000c1d88510078600351a03a41da5260400280008001c01a64a10355440300101801e40d00c0400c10b42601b20360140080050340f8060600c2081c07000051803c0740002c001e070045444800720307402903c02090b0014095072071070300c606105868441d0b15500407601401500300015120109100700300040c070b11003105141c0c0b00800030101e2000d1005810407414002c003070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 97708120 1250 97706870 97706881
    0x6020106260a0b070513060c110102010903080615040506030f04050609070b09010807110a03030e0616051206030a05030a09051005030708150402090303040807150912120309060c0323 80
    0xc8104446070415182182526181c0e0101d45600c646c200c3e00f0031074080c080002401e1a4054a0300b55010300070381000b1610000440124243ea10000d0003900180c000c1c0702007100d615041c00048040010881003030f103071030381e6880420341d182c004495810011030910200014402e041c4030035548410100080c092050401401041900908280a0400040d0000152040c0c0a60301a421050341242210300c400d0041c07400078060b1601e0b1920a00300c2c028040800c010040880420640c1e08075900c2e00c9003450740911121412a400410b5581d06104a8520300040f40d0107200610100c10599181c040060614041c0500c00941c0d00d111400c0100403c00c10000540c0502903e1b042540f114003003084203007110010f8049d00801c000c2941c035000018000404e00d07800a0b040084a02552041000840c0590160f5940c2d15a20442c08400200210400013400400d025410102c15050000e0003400580740d0a003240c1201c202c840c0800d40e03132214440c0c0003c901c50541c00c01d2010294007504c1e403070070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 97709370 1250 97708120 97708123
    0xe030415030b0a05040515010917070b070609020a06080a0c050f0306010509150f04080c100203090622030f021c02011e0c08070503040e0a060e0412180602010626 71
    0x2000c2202041569400107080c080c0c0d078001508000b002c00030000d1020341011080c020751090510380341d0f40401c0d0000d01c000340d10703250180002801264000034040007480e001202c8080d41c4040310465090390340d040c081d03005988442410001c0c007010b40c4e80c0c0520b81740281c02c00088441c009170340000d20100b480300324102c0c0c6122044940c40802841c0039034660044201040c01121418500c0140c1940450600200c00d801000b0b0003c83d91541c0494144c03460640500824071000c80f03103000141c004104404170f0b8280480241b1485004180b03c1e45820300318040141da4078402e800c1100c100517503040200552900160700840910001194040060039500103843d02c00c000362504041c3c00881d0181c0002e50050062804440e0011981640c500151500545980c010f00480000843d8140400c00c2c4690394400d41050725440c80d050070780354039a0b456600030300c42c0381104541000322040c0c501c290320041c40070190003401241c0011520078102800c00490307107440d1442c1010a0504d520203017083c0e40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 97710620 1250 97709370 97709399
    0x3030702060c160303020309031e0c06070c080313050a0e1504110909040809030106080601060c061e180312020f030103020402070611041508010909050d0f11010f020306040e0304 78
    0xd0449000c0d903500700e5401c009042c100c600ca500d00c1c4030290a03100005042d004070082c440080218280e4400b51500c01e030b0013500300d085901c08012540041d06402d00c40c10500300810045005116501000d41e881c028103180d5440030081850310b4074140b60802c05070400850700c001170702e010010054240340c4082c81c0021520040d00d224419034454030060400002201121225500504450311614003410714840e1984010720a0b80a50311702400010030481c0451172606803203445e40c825400e211507448440241581c900300001802ca03030315189500a510340314201c4400c503d800032404452050034058000c1d0040c03c07040c021140100405140300e1441400c490540e0f070304440050320340500d82080c4006003c000344040b142080000c012582121600b0310400c00451513490141c1030307803184600402d03074411000040c03081e44a803020005803030280300340301c524259a1070310150944503441c0180c2941c41204985948031350000c1400040e05041c06800c0d4050000401140760900d007200810a490 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 97711870 1250 97710620 97710623
    0x1150201050f060f0409110a06091703030f04290702011a03011107150b0a080f010b010c0210300222050a0b0706020705030f1c1b0f020f0303070521010302030307 71
    0xe60310484941000300320005107110050151000c40080d4440c2c4010303282c20168000d00c40300b04c0c0b00d01c6c1480c848bc1d20000849115040b00031841085440d1940d60040640b010110400000c00c01100000d040036245035480c070540c42d99001289903401c0d0021000d4042604202c24007907410403011020490900e0b0807140320b10384c0216400c0c0720701052040c280c0281641309050354000901040040c00701000102c1e40562403658000704410784d400c00054941803000d010094000c0314030302c0207540c00c5000c0c10407015540e80004104c00b40801c56528801c4032408103950b040710320342c0801d5454103d10390481c10b104001c4102d210702c1099041c07000003140540305100745060b808000504000b002095019034003d50b5220b0100c07900d1726190464000c160f04140810310500b102c19501c50048690381c004c1403011208103120002a00703103110304840d1996240151400e5124000641ea90060f0030002540700c0c0f07075940c0d20385442d07144e01094203041d503400564240da1407860781c0c01480980e80200c00c0707540d0507 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 97713120 1250 97711870 97711879
    0x201020c120102040e090309100206060a0b0708120421050909010b090613030606031205090f040e03070b100609060507030504122102060f1305060a0e011401150201050f060f 76
    0x203112036000203019200d5904405c044500301d80900c0910300c070000c0603121480003116030f5002401400c100b20307501d110880c2c03a40d5001d500f69008020044092008190321400303070480354900551808800c0c1d03240404e88085801d07091010303082d0720380030310320178207020a40c5107141c982e14048107900001c544a80600801b0041000003c2c485001d68a000840b1440e813103940c208400c0d00c1d41d90502200034095440280c865800c140110f401143c8200c040b281a0a00140885200d0030040c003400000c2c4051400c0d80340c80e1000300303e0030000c5613161041ea0702c1017440b01c289040c0d043c14418000c09207040b0754040b40038080d00303000b001c0029400c030091700c040d80c4d0f410310184101c001c0360a001840420003002c00c024408840e000c0e01310103a0214900e40b0803507982c0746520301e80d01d41da541440700c0d0799841c901810f1a0042c3c008038a0305c1400390441d0030210450800495240d00750414401c0300a030a03405070210001500d4480140d0341c0a02070b45900c0240c0019200140c5400804100404078041d00785105 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 97714370 1250 97713120 97713139
    0x81b0606040b03060402041a0307030302030a020601090606020d110c1302090411070c030b1302040608030a03150803041a04080d08040b0f0609040b04020109090509010b0118140d05010209130c08070c0201020c 91
    0xc11207548c1403201300908690480340d8a0401a480351b0041402d40d005004050003c00c405000340111005c4526580c0101140729030110111200082048035109274098004424220354480034028826000d0b00401a80d8001300b004100c211031600c0c141c0a0007060511640740407a288003090f00c11a80c000b21110900c1d510304003041c1c603c0703480c900000d621502d003540104410034000082c0107603a0080e107041100c174414040c90f0741c0010003172082040c194410482400303043c659901e443e87c03040007000001d05050701c42c40c1d401d0812071b140c0503880000d12034030708000500c00706030b1400303400140a0703e04003068180080400e00c1540014400743c5102c0c41d0101160442e440307012844002c058040d003c00103414a415040c0c043d00c40c4000c3d4a00049081c00c0301928112a4486001120300c4201820810034424013404015000d0600076a1555800d100050343c07500c4081ca5070000506582000440390704039040030f000300c140a0148400c004e00d100c0d000300141d0b0001110080c80c5401c4458164 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 97715620 1250 97714370 97714391
    0x31902060d0207051506190f06051c0204080a0b0a020705030301060507150501080106062303060d02131404021302120402040b03071d01031a0c0a0f0507081b0606040b0306040204 78
    0x1900c0780d048010b04e90b00c1040708540c402da06a48650380500c0301140e210180002400c5189100103e500861440164441082040034025401041c603030518014038507140c17010b00c852900300c0c1c009900940340c9402000b000720400c41e00108555109203119003c50600140b070319002c2d601d0005010f8001800400143c1606200d880c886042c40301d02440800d00481d07131192a01c3e40a0070b074a04c201c2c00841d65002100640014403408061902c503c0b00d0020300f165900401c000c01e024034400e0a83e003000c0c17025440d00f00c0c2401130040412405a0941c19003050600b4414032500240110a1160091040c41b9074034802c2102d40c4416003241d01100c1c0400c140b141c41000909181c00f0b940306d20b25100d60100340c02c600103000c12105049074010342c3c800308034100d55499050f40081c100c1d103209080314100b08481310140a0440c00a08051610b002d13030600002d60f4900c003456000b40c40601020b4488400082110010403071690b000c00d0a5409204600810001c01c2d903824025100900c40c60f05d4070034640 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 97716870 1250 97715620 97715647
    0x7030f1b0e1f06020c0105090922030306051c020303070f02040b2d01022407030914010b130e030d090203010b30060601050f0703140406030c0e03190206 67
    0x1030141c00022a03100c4142031440d6114a040003040502807500c100100000e071090020170414054803068403090b18102e15502044503181e40104004007012080091443d40c141030401c40b007a5600c80c0d01c00144035400c043c20441c0c10305400c0098800c6090010803000181c4010050320790340ca03400503c2d100c0e806400c0c030005024002024400d9001500c0000020050b41d01c110040081a440024a00c61340e01d440012a1542d8040108100c1c2855603800d140c000142c504005038015044c1c90000703811007080e6500c4042908101a03002240c1d1100101e070031034a00800e0000815000b00c1c02080186214042c0c141c0324055004150166a95030200740309640782900180d003511401040c110400090030145800404501d501c8091800b2054101040b4140002c130b890003030300e050715030a040c080304440d60401940a24000c50401c410074250054100258000e8005015551804500c0c1114078000a043d00b40c0280c2c0c86100380d0140125a038014881c0d4800034010343c05075811a0707207617043c410b01d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 97718120 1250 97716870 97716923
    0xd03030b030c0319060f020f03010b070302030904051612060f05011d0307060512010e0403020a0807081605030a1805090112140a1109070c0b15010306030b01240207030f 74
    0x303c0c0c144c012030f00d49450003038443c0c0301c44a505110b82c40c100f040c1300034491480101e01a0716518910104100b005100c0740d14403a018000c4036200e0300c100ca15000018010500381d801c00d486440c2d045d1191581c92003100d4002085800e450b0f4180020059641b07041400d0407445658405c0c2418011807000200c401d5108484405102c0380c060102c030281a03807960010826407198803411081d90301c400c0003092000d40042c802e805140c156000b440d250045480b2543c1e90762003010700310b4130b04204110400000098009240c0e016008401842d103d40c100310000c0e00c851441960880f4503030310000284000d6540881203410758a00095060b000c120304e01d003200e00344c114000221040d1090000700c81c1006400800100700d0001070382c607580360380c86180e010f0346d540001600040c01122420005051070600302000010703d24145030120714a584d80d00d8486096400703070005002044040007800d0700b0030003c1c105400c02c22561000303042c214a55150480300c41b802c00300c010160040f940e070024640007500d403034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 97719370 1250 97718120 97718143
    0x30a120c091e0602061807090b0d0b0a0e010b030a0c0e07020307080d02090f040606120e0715030905010b0904030f080a0204170a0c090b0a0515161b080c0d03030b03 72
    0x4245840840c100e1003601d0b941c144503601c014441d5200055400c0e40c0100844001c100100c005d000b09810006001b0180c424061155003080e88040d004000c503140300c20040c010700e0f090307000045010030b030301e0820b09464034141a00d0182d4030542184e00001d502c020703008111021550500c42a032241c00c8101e041d441000c03406032011700042800002519583d00030724064000b2500f90000000742010310081e58140c1c0305241c003241103800040c0840c40c1c0d40e000041382200c1301c0107035880b440d141e001e42d05050320308901e003c0c0017968480000080000c240b0842e0f403402c0e401c80d4070608901d482e61b0024042e1240b082e05108004802c004a94003880c00c2d01546e015041c015251080740e0038006609603a101c01d50b0040ea003506c10b00d000042d589146204180324040044c003640140d80c100740c1406a209141c0040c034007500010000410105800e034841c00003030b80302e030154042041c40c80e88281401c1c481c1e60070040c01c81e04011706921b181d0b03445840024074a58075003000703e03000c40814002410060303017024 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 97720620 1250 97719370 97719389
    0x4150207092702060f0316080133030e01020406031409010905030712090e0408030403120e030307030207020a030b07030b0307080c01170402010e0d03080a0c051e03090a0f0605060a08030a120c09 85
    0x24015441c00000e059148402c2c035592300c507041e81e42c4d8000c203000301d1700c0030303a00c1c802071203a20b0300080c2058407030034015030a60b403241004620481a41905406ca83c8183c1c0b1803000a07a4a14078030360200301181010307401c0140e4400910050341d0a841d00d9490340304030300f0028021030303034180110109401140c4108c01049501da40d58141d250600b030034603040d80121000c400042841c440c460502809124202c9940048402141503542d092010760080d800090b06036402903010700b00000040e010165284645140d940c04203140030094241480d0000302d40080000c1d81004000c0c0c075890740d00407108849240203e017100c8094442c0e00058036012004001e00740c1150001d42d8481c149a0002c108500500320807404020045181100300c0310b501400020300300c440e620040e290741c02c000f03510156421403004416201c801d91150f40d0420074004070181181c0d200d4440f400c01009140030f02100004007030200c05145000300020009004015006001c616103a81d410220001d40c861010400501608103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 97721870 1250 97720620 97720627
    0x7110109030201060617040b06120f120903011b050706020913020d050613090c030f0c0e01080c04050106030b06090904111005031005062a1204150207092702060f 71
    0x81c000e000e0840c50081e0317800b04003511009800346500308016889190803e68030b0380f01352245420840500300c000010a500d102d03039100d40b140c0420620009070360710b010080341950351081800785425500111b840c111000c608980486c40c20f50410304565007503602c0f5100596640c007100c0064079401c8035441140c55140b012509611101036a07002e980a1001103644509115034100010241d410000e03001300004856a0308100043c0040725a03502e19100785030348000140ca400d4001c0030040d003613104c1507880d80721801102c224281441703102d025105e546414044107840b0800700707600d0321642c010140112102400901840314a01c42c2000705100100b480100c0ca81d0044010115001134035905421a42c14000280310700d804000c958642c01c003416041303000341e40c41038800c0c2034030000c000e4500540150040c081500414400a00180607071812061303801d40e02e401b0081c07810a90380c00001c04140b40ca00c07001d0036503c10700243c6580070307505240e05d510030040d8804124280103c40000450030300c0032 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 97723120 1250 97721870 97721873
    0x70902040b0304060e0f0d05130e0903040312050301050906061b0d0302040503100203010e041b080a0b04060e07030507051018080102030f0906040b0403080903191206050d020a060807110109 83
    0x407000314000d6005201c240038102c5446555030301c40940e610855010b07401201810582409403000e00205820b240d4190034559440f01643c0c101942107074000390503000024140100012544220b01c024294a4000d00f55810a004280d030003a0103440b0510400020490f51040d2921341c0d00341804804007826102c07045900e00b03000e4003a401034018a0312a0080710250700c11106544282c3e8121511541541e81a8a071a1200300c01d007003a854220300002d00744407010680103000c000410040d481203100b04418941401d100007103a11140920426420948003000171500c002883e8003038500456200c00c84904415055406064480b51038070b020401400c00504424198017852040119007410a410b95408010b1500c4a004440040c00e804501003c90b0109224081003584400407504072860002c10210f902220000740f0b03904000242e00c07000c0c03030000c01c809000b5000102016030710070183d242640e0000303141c4c0006016460801c202000010030141c850900b151201079420001c0000140c4d5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 97724370 1250 97723120 97723139
    0xf0f0c0d1b060503060103060b120615040f080c0901120c06180504050903040303030b0a0e040b07090306021201030c080a050312060d1205091009260f031204050606040203070f030b0307090204 84
    0x2200c54501180c238040307000814a4a0004a40345003011040c1880c4a81d02d11003000549184c1003117a602d011000c2c040481d0720000c92030b03001c2c041d04080000b481240c41c0101004000c3d50143c22140c07002011044400000307800032009801d81d02e0380d0400a0259048800d00f078004000341c3d05c050b5216090109100d015100400240141c81c040d64051019020078000d07c442c040d0079104034802c0075441700010700420094126035402100a01d4082c804564079211901681c00c0111000b81070440d0b034004000308890b007103a0900520203103001d44409001d5454080d140d000c0d1040c0ba80d141a14540014035945d40e02e02c0e00c030f40681d404850034091003100318000380180c01542045009240d500c000c40402c038000d8200c00b088450000d0202c041c110f03040304801403400d0036501184a8841d02014002c1c030313102800a00b03420108a569000e144c501400c14902d407120282007540980e2041050100e66940b19211010f07a80f494100070400410101c0400e203072100740c1e4080d091040c40414080b903001003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 97725620 1250 97724370 97724377
    0x28060903050f030a021b0103020d0207030305060306090705030d03020318030f0408010c0c1101120b0909010f14060a21050709050f0603070608011802040e04080403050f0f0c0d1b0605 80
    0x750003181c001da101200207503603074030401a20740e0151384425000300304648500c05000c20308806140140c02c000c010200c04040e47c014400c202d0110382c4a100f04512800e007003018580c817500f05002050500d117002d02003500ca0200803001790030546c0000000d902c80b180c6c11418036542c00c544007220380e1903400c07110103141c68015005c0c0c14002d5080010b415402e0f40310780205164950012486403080190308015038003480380c002c543e01001e48600c500b086c02c0da51014010300c281d040c2d40021980d03007010400841201c280040405285c0c404101744040e540300c40300c6020036610000c1c0c07041200c05101c040d541e50384228503c0107215200d400c501003903030502a00081d00034074420f100071300c264480d2801c058030380015020320310000d0a45001040885c0000f905540b03110640c0310010325041d103503003200d800341c502110296011180000e0070010020308200340155603003918090820880710506040d05c0d1700d411700203588211201c1d800315090288050603512154070f814010013980e6561900070303150740c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 97726870 1250 97725620 97725623
    0x106050c0703050601060c030f02010c0e0d060f090c0609050118051002030c0f070f06020a021806011b060b09130b010302010302030a1e0c0e100203030a02030c120c120c0406080628060903 82
    0x2504e27003031160100ba005002c3c0c4652402c82c0e803550040160880e003840354100d000701066540c030f9142c903600100d009541c03141081840c0101c41c0e45481c00d0a000001c2d046840c1a0b01c02070400c6030300212440c0301d0400e50095000c1c1c480840c0e448004c072070400c000724550301030703058800150b025807010340d08196000588803003260303881d00c501ca040903074580080e81c0b58459a080690801500d980f058445a1025129680844141003010000e00705510b1078103400784082d81165030640e035240d41340039454800950b41d403000320407041083d07030300382ea58410608060600c0024103164001c008298507900ca0342001c420020300d500b441c26050840031680d0301070300c242c98911021a401845c3d89200d42030442118850721040d800652940c1c83d588000300081d4401484849002c0082c0242120581b80c2191203000d4540c840001d51101038086003030314460009002c1d2001603204100801800b03400c4006154807003000c03200b0210920040103e0201000303240950510109a440007094840d04504a0025a03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 97728120 1250 97726870 97726877
    0x80423030f090a0512060703050a1d07080601080d0507060203060117040b060a0801050c04050f060403020429061c05360c1207030b0a09080313030314010e0106050c0703050601060c03 80
    0x6030380c2e0780c09122442a44090000286d009000000c41c8680240c0001ea000001c0da00e00003a94044081c00301c0e0300c0203c0d00d040315110b80204e4010003180c84c0411400c2c1c090a4020054034a40e4080d0b17101030b015225804004040540100010302141e0060280c0c01e00c41000c2c815200151901d80b03042c1c1c500b10310480e143d5109054000700030500c0101485900d04c2582c4000d00180760a0501c400c00184100004001d42d000c1c13410040840161034901901d5000c0d40140d906103030380a01842045860b100750121180246014004000c200e41050810204051500c1e400a40c0c0d0301c4107600f1400c00000140c40507035840c0c40b031400e518005001c0c0c1c110004981900e050b42c0c4500c200004111200e28100d00307204041d80b04100c140082054820826080000c6520014115034540c5e1001d815400c1120003040d1258803510620905805000b01c1186040b0040812100d60504102940c410741c18003400b01004004070782c0c0c40080008002500203150000c084a03c1c45d0381d03540b0b0090504c11850002c9000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 97729370 1250 97728120 97728139
    0xd1104060215061c02031911010206010b090112111902030a120b060a141b16051917010e060c041d04050304060f030f0507120507020d080423030f09 65
    0x380c00d042e4107405001d0003000643c201584d00c00c4500e0102c1c1400040e82e05010f01803c01032a02403606003d080300384a140d2144440e2610400641450300580c0108070700f400401920b20140c1e44000c160782c0c20030800800080d1000411200c00d00c6006484a0722009040c2001009501c1e8001000d082800c0d01590740da111105200880f009461030900d00c1c0e90400c030188200003410380a0503821082c600a00840c1c1e05001f40d0540b40d0040d90920340030400c2c80e8014040242c01d00d20000031200142c030041e54076012542640910340e1500c4074038841c800b50024801c40c000001482034208480c40e10110003180c0c0c141c1000e4004907890380c4139200d0708404c50f0001001407210481c90584034484c981000256081514114051f500382403d54110410588d40e400c140149500610400707000300d29075075603000311000c5200620300f104c0001d0060000e42d4841501921565405075215a21a42c0549201c1d11014060302840c100c40f50301040d40501c0c01302095180603103520601a102c0b00c0d40c1190b40614 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 97730620 1250 97729370 97729393
    0x9060501030c050f0f0708181c02011205041104060605120a0e0d080705090405040602030a0b03070821120106050703030f0204061b050709020d090303060504180b07050d11040602 78
    0x881c0e0b88107500d800403c2d03052040c800034aa100b005041511000c44503a0b1034a4055a5a925282d000454400c060103072440d4620150900034134000442d0715072a00035110410342d40019141c08114a490300320b07180c035240014104020381328080d41d00c0c00080c00c14010715844e00f0b006801500400440c0d5810000800015003e0225002d441c07080300406010b0000000d15450495601d00010400c0050040400c5116459150361192901c5140107000040e02c130309008681100361400c60403102d2003540014000c0c807486e60081165200d6101e04101008600940c0c8000c80d11801000c013852020481c600001440c213810200070820307940300b07680030003494144040d18002c0740505e01a40c000202902c0c0c890014481c071440109040f80200d0489d05411b540359164810b03a0f21060034440081d40740d54400c2c0805805003e03050242408070b6052000051340480a946002d007581e000d440490100c0200c0d00c51030051088030000d0207004014400f072035015200c45410b5001d4401d0100610411030307580d8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 97731870 1250 97730620 97730627
    0x30206090a030c120302070c0b030618090303190f020a080f1014010509030307020301060f051c02032503050601060f08010608270102040b070b0610050f03060103020703141309060501 80
    0x44400b41e140c3c81e02c80e86201c081d11242025a0601c0804091690803c2030002081d90003100000508044d024a0b81d80e190800c14400b14000c0750783c90314110301149007403281d01c203004802e4950141d040050455144a0383d440076014000600c400360308107100041c51242d01d0b500c0440d49201e16030050410f0801d0311090031b2901c40c44428070822214050140d445640c0790711a000070310208d10003c00f16401d0400c5500060300310b55182d846500700010442081101e1b04110042d090300e034a1000014100805c19004a034440c1c0d8490041511403068803085941102001d1540c005141c000342222003940e1105005004d81003a40b00c40c5010405a800002d40940b16201d80c0f44607058562902050039400780d11500c50040c040d005400554080c00081899681003000e88511030088000c02554140101842103195030f00c00103200308682002900c41020b05c2d201201e411070820300c0c00517600d20b12410101d03905117411a6150b07801c0b000050b0b1440044002010006469200354100070190b980d10064 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 97733120 1250 97731870 97731883
    0x5010306051005120c2a010b03031608131208090112090f020111010e1002190801030b0f130b040501020904060f0f06050c0106050909030a080106020102041202061e0f0703020609 78
    0x800008804201301c04002103201c280f9074001070550140381c00e008441c07065244c520061006100350488040400c04552400d02600045c43c000303038050b518001c141250004a59240302c0c0260102c03070001240030707440b04071000c0d1030000c00c12680003a481030300d5450030711a164460040e00340001d003801c002426080262142c4111701d58000100c000c3c85120745d0040d40c4500f0841d800500740d55942d0314043c170000040c003035a84601c9100c00016926601901c4003003040c5604040c40d010810b0540052000800c810b42c1d00350400c03410300d01884c1a0303682c3c00d0701c2d40f4840494000108814143c40500c02045415000781441c549c0c2114184070b12512080c6007108280a8070504080d003c0c44401000582d025100070004110143c00114001c2c3d111400f00d01c601c0800d0380c1e0301c10980c0c000646410380725400b803441d50251000c5d100951400c3d20b0200c3d2500c1c0c0d09401c0d00041d01c2801c001801460310700e03d9400001c1e100d4081c210240e256103034520203803150f41200e242a0058024000001c480141c00708d60f8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 97734370 1250 97733120 97733149
    0x302030f01090b01140a0e090a0c02190f0c06090306050f19090201020f01051f1502030a0e040e07090204080c090415021e04030b0106140306011e09120c0501030605 72
    0x1410982c6803600070303809000112000f41c18441e10ba0024001034100c1c0b002840c050f104c03034480d00201c04020081c000e020320000c10038840c007403406c001a048141d001c1241444801c0340c10400380070032902e08250300c4480318810000c1c414000680c2c002040390b0440040c80032240200400c1165981d200c03c007003403100046514401c005060320b01144500625400303030b210640188100d541ba0122440280e0840e0010784103c141096030601030740150001c89440380180001c080c100d480c880ac00304019549000e00c2d5881e80c240b1580840c0c508a40e02c60b90302901c11242c41400b1148401d03aa00703031b944000d60040c01007821500900c01e41078034505002e1180c0f40140c1d44a11400705220208000a00035000104200749003010840c001c1103600d55113001c0c1010310701900c0012942d501d080c0010b0400201100c410b80c1c50300d01401007060982c0c000c5500c802114007811002c03140507684008448041403a044194010000e09914082c42076410f402c800f0b491081c0c800304161600c80c002c0140308001c1a58 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 97735620 1250 97734370 97734391
    0x6030501091a10090306180209062d011101021206120d0203031801020c0d08070206071103070b0c090d0c0f060203120103140703080307020d020705060309030d1d0307050303010f06030203 82
    0x60b541c4a4203140e8804107101c4001d01e845041a5103d65440007964000329240c85050b1070b4400400c250b00e052081c40f900031200301c9100d501e406280d4500030303007140e0805280341302113684100040c082c0d001d0401c2e0048020030300c0003103607100300345a481080194140c80300b0303010300c0720503140314400d000028055a084846070000c41c1150741d540c040349603401d4800b982002954091001c0b6403038190030800f40c045c0301e000b501ca8100c50300c3c0018000b0700c0c01c40c00801c05d02c200409400341d801c00d2640801290440c540016000a4643c0c607004450f900c0d2050900305600700c8010030000c0d06001d40101c1400650301c0c6408003907440c1d03684150403666802008a018210300a400040000405c201a11109000c40801f580c03a8280e9903100c2246581048039082c0250708201030041009506024007005401e04992803130440c200f000000d9a00d01800440e19451030340c40310205000d02512a002c03100e05007170800c407a43d03280c0c5881c0864a80e0401e102c0c410400030400c001040c0c01d40a4020f40388202920360 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 97736870 1250 97735620 97735661
    0x70504090203060307050a030506040b0a090c050409020d170702011706010206071d04051e2a0a03060b0406020d08091b01080c1b01051909050a02010e0102070905010306060603050109 80
    0x18030860081d4005020141d0504c983c010000300e82d02e4140f0008000e50050001c0c00151805003030061150400800e0174103001e01d800c11840c001188a0a26025144252000107180081c0e03c04500f10b50345140c0040c0202d4048480ea51240e04403c0c010704100d8400c1c2c1e0380302600c000f10021101d60300000d480c0940540c003e000003424451103910303000a80d00001c1c0018001425140c0454120340b000d0354100c0c0004201501c00ca00e00110491154005540303a04c81425100300d00c1d00d0100c0c0413a4008254601e0340006051907246100780c200b2006840a01c00290780c450703031080e0180d130320f120300b90303645010840c408000f41801e50b0120311002d8508001ca03105a07031040074001154a502c00901c40648108144007054046903000c00b25007040c03481400008070340c104143c645c10240e40312030b403c0c541142403400701c0c00020f1011560700d00c101d9082c28040c90010081c00182d05180c0070b60040310340d05d85040000001d00446811080844a1a032801c00081e40c81d06030100c252440105d80580300000c40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 97738120 1250 97736870 97736879
    0x15020a02100203010302180603030418020403031407200a080102030a020a0801170a08210901200f16020109150c02040510120b070e03100501030606060513210b1806010e070504 77
    0x585000e0b407203040227041d40c2c40c1c03540f84c00205d50b07811005036204113040d6000c1028020190000d000348541010266550f00381040b0385d41d8820503e44034230740c00c0c904400100d0000110340390b002d14200031b8030b0300380c00954892900d4030b9400b00035040002e828002500a07000003d140c0000031086808529090241044801d81d0722075681c1c6901010b49000e121654038202d283c80c201054506008048100011808460320483c28024649040c4109080c0008005580c880da42c40406c84a074040071000414004101c1e000580b00c0d0581035006a000e0283c2038800440a50b0090441c540c4502c02c0394104010b454604500703100c014240600d01081115003160408107011501050f802202c52906a200c18038040c04207007012042d0162981c0141c5500c01401000068001c01c070103001c0d12301d0b005080c901d0360360882c8513003040c0d8403450303e185801d010340b41070022002c0055004981c0140c00c0c44600d00303107440401010168540c4441542c06100c001240761120000d14a002d4021a074a0314109801c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 97739370 1250 97738120 97738159
    0x5011e02160803060f04090b1e0705070f110301020a080906070c0b22020a0f0801110306060a111203100501170603061609030b04110918030706110715020a02100203010302 75
    0x1800c8245d101e0300c0024510004da4407400350301c0c0500d02c512910141ca040c003c1206d80c0300c0d150713035640c1070036421203904100806610078180c0c0c06460b0428004e1400c0075080c00c04280011109000a0701940002088020a03410417401030141501740100c96141d81d40710003c0b84c628010140051450301c02001081085000d03109600c0304040245420909440681c0080d80703100c0380d544a220040c4800c42c080003480c00a01c2445101300f0400e401c1071a603d80303903000803214401c2000c14024042e46203000d14109400b0440304c81d84420b00240e007a520b0500c1041c0308150305941c424580000c7e40c84110551103081d180007907000e81000350091207070b5141c1c0c5512000daa25130312014410804083c400001280080813228041d500035105903504139a00b806000d00c0800081840101c024109040c821070000082100d5041d600084000307400303600789610095a21607040050001071320982507080110b002c0c0e008010b420843d0b0205ea041100071140300091340030074440a54000c1d020416420f10030784 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 97740620 1250 97739370 97739377
    0x305090616050f0c0a0308040303030c11010f09060606021b040216150c030b01090b030a050a09021305011503060302033007030206040b0f0906130302031605011e021608 74
    0x10040c441400c100100305950500c1c003512100780c0d45940840744031180c500013441001140403080c0c0da0261020304640304c80d01c2500c500d200050405507100c481c098590320820b1242c2c0d054807072034001d01c2440a50101d01001e80302000003036840610f03200e0006901030000030207161020030b01c01d5858a004020040000a400c40002c040520030343c40e030030500080584101811011100c01c0000c0c403c01e00060080c01c886000071700a040c480302110034002000d000c020b59078000034412012903642e031000c144c94003402461400a401c084003455800d80c4512a8200c0e505880f6244d8103030340c0d4220007840440036141240710194241d002080005205404080700018a00c1c2000c09140d801e5000144010380e5404000706400581107a000d200c10854105210360700209024084201403c11118143c3c4601c0d024194401c45da240c1809081014000e00a488400d0030842c480f024010960030103034081c100d11812075800044010b40304001520901c01d131aa001e08184902981c66040d540e2000d1651 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 97741870 1250 97740620 97740637
    0x60403110f03040b030108010f0c081306110f181507020910051c0501061d0f1503030d0b04110703080105010f03020904061d06040603020f010e0a150903050f03030f040305 75
    0x907204491030980c000c000600007404030b00e010b00c0d525803610381642d084410b80700c440c5a5a50a0003080d181e5541d1002c03517503804c08048405590803040c10f1078580020505186407440f143d40100c0c0e0703000c260100001802803019030741d080b1000074007081c08000544101b0007030b01c600504180544005400c000950a511101d541850785a0540b907000091000c519102c401080100c5e000d41441041800c1c0506c07030040ca54040d48103401011000741a88106005101801c2020014005403e00d400300d665007801c080c002d8103581e80c5001c0b9140b241e029181110489010350300f030029810303040c00c42030121030b042905903555207400d034280401103c515009150313880c00c05400303104003401a40d461042da0020079040c3c0c240c0300007410701c0c082130310b0076607009124620031881e00341c3c20005a00e6030401e08a00190034070b40889070440300c0b800201a4400398101070300090043c06485076031034016403460152402101101c070121500154650b0ba13200c100c1e80701c40c0144028000c900002c1c0507801804051 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 97743120 1250 97741870 97741873
    0x10b0c0709050109020c15060609040c031e0e01060b09060a0e0111031c060e040c0e06040f090507030c0f14040c0e030a0c090605060c060606090117130b0109050906040311 75
    0x220780d030384011070955400381c01c078440d0254000713044546000204403442d60100154801c40302850441c000400174003070040514040c0e5100c1400600c020320036030100b000e0703a050310a141c44803001591f1480c000c0104201d52612986440004100100e001007500c000c418001c11052802c02440000c88080b03c00d1b14200d410300c9400b03401031281590600240024041884485071050042d59011003903030125484000e4500e4000b040c400460b20440b42c0f1001d03100340e0b503048162511400301207030040c610024844c003002d15015541c800c008000c502c4100700ca003c0c1c09143c0b10a901d0b42020611025548125000454464090b581c181400d400081c2c60220394140b020000c40d41c4e40c042420007140110031a4881c0311000c0600510074203100c2e20b400350405881c410300f800a450101607440074003a0055108200200780303041a6841802d485020354524134244c0c4a40c00c01408408122401a00440310404000004100c43c8210b1280c0342c82011003a004100d15100c81d201910325480d03a0030f00c41805e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 97744370 1250 97743120 97743133
    0x20a02030c0d021f030203040605060a030201170403020325020a1a042702040603020d060609080a08090a09060b040801050903070f03051e040f0512010c050901080c0408060103030314070e0306010b0c 87
    0x24140340e0030007450213481d640c030b016a891901d4034110302183c00003002a4420340710b418040c07001d41d0340030403507a0004100d07100080803600c0d80d040aa240d4000c4460001540c03400900d04520000b5807001c0c60b003900d00c00d0715401d40780c07511501d0034012080921b41070703a00b40c00103000400403420500c00c040400d01e85800c03101644d4007504407410030b0340e100e80c002a01081e000100580b114009200d040c004203030500d08144c503d41052040b0341c035503001174005005200e000c140600586c0d100203a0328001e0140460800c089a500c01e250846034205226281c81c40d40790030f0009820b9007000c001c48203010384c0a0b01100660381c4646e01515107070001aa0300762041e000c1d06a100c9080b00143c0200b000c0c09103459510385181c6800204000003070094440c541a0341408072140116804c002503803140302007402c03d2207407540c540d16080f07818002d60f40302c0000352003640c00020900d909076001e00b609841c1c4070860540c9958922065880004031100036030181d119000401400e140800038000d141501016100e6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 97745620 1250 97744370 97744399
    0x7051603030216060c0809060403052a10051b09060702040e0a02090a1509063006050703020a030506041806050a0204031a0601020708061006051b1e01060501020a02030c0d02 76
    0x16440340041013211901d035541501012540c000080d5136026070100024552860180d03002402c6000b0b03a8541039442040c0d8101182c003e15210b4451000d55824046811a030304200900f00904002d942c101d0985a03807c01c2c603d11907584100315241e01c100500b403507243c203169600380401881c6c00107140c15140100e80700000140d0354800d01740d002d20002e42d000314019070070300c0c00c80640503143c2d0701076032409242c40800c110400c07520385042c5071300d1580303054204070034414407158207446401e0200074007042c545010031400b2a00b61780544100b03060360303800308415603e180510044030510300350012640b042c0c04039400007800c141c020302e61114400320050304140d5070380d807903030061070b826810680440d5180c0100120f95a04012035001041e055000342203c0c02c2c507282074181c0e2100c600543c0d040000c0020f6109103036407074014a030b00781055a402c4445014006c0300243d54210030101c2c5200d207500f001e00020702903100140d80d503910fa4008004e418085184c1040140d412210b43c0100d030030003081a0241d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 97746870 1250 97745620 97745647
    0x504140a1706090d0f0207030b0403020a050d02060108060a0204182406020c03061e0c0703031b020c040b04020405010e040209180f07020c15040b070c170c0909010203070516030302 79
    0x3151098244000c000b2420510030b550305050390030483d00c080028007540c0d050321590000d9520116600904686041c1e02c0300d0030f017241401180400a00184140000024003581c0050494100c0707880100b074070016280c54078040143d201c2c5110f40e44040032681580d00d0350b038041740d000354408507115022007070f001070018101503e40100e50200b40503030000f155141c1d0b0350400380440c5a000c07000201603c006824000f205611240c0642401718048020404404041c001c0c0c0c0080c1004945001644032444044002961008103c0405000c0c50406e0001e20803420940207903401d558058440841ca56a074106100c0203410205074680c0c004071044030b03400c0740f40c1010103090180500c040300311545c2c507107a100645844001e0380c00502510b046a40d4190080c0b10f41c06450070342d140e0b032000c039a880c0e45605000e00124050341050003640401152134051900004508800c00025166800c16698030b1400a0803030208a5495000c140200445102807070b0311149142c90380c2c4a81401800d1104c00d80404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 97748120 1250 97746870 97746899
    0x3110a05070b04050a0e0c16080c01060f031415070c0302011410060809030a0801030308060402221a0c0304091113062c031f060b0f1213030504140a 65
    0x8101c0d030320b00020f050040f07007800c8940401800b0300703007101c0c181810003048100584c8121281d52174070f0840e00030244100a403041c00c503458054840001c0c00446e844860380904040280701c04c440e640d61080592610440118006c051f104182c102600507641308030058a040c50b50040c103c3c110755032100c030158107600700080305000e480504c1524600307070300300880036142c07802c040c02401140d07000b480a0400c082d40107819905403585450f10402076120748000c20042c0c01151040880f03400035024621400c0c08000c2184200c03140d0f40103281c00000741d60340002c0b040c03190044420300c0340c0081005004003082e5410100241c07034031000c036500d003410555a605814141e0740001c000036241040f45048a17809614103080e0454042c2c2050341a0000030010341d0700d000a41c5001918040d14111400800c16540424010003011803034030350b211144641200583c0c0f18941d51507a440a00000c00c0c01d01740900500c464256050315030601d000d062420800300c900c09200307801c2d4481c0765044045010b40704010304 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 97749370 1250 97748120 97748129
    0xc0806010305101208031017060604020d09021f1407030206012d080f070905070c030c020324040203060108070806010603020c03090d080d060b03060105041415070b040b0f0c0703110a0507 82
    0x2411b07201d00740349100a814095651001d50590140c003034840348424080750b065040b40c012100140d44810403940000039100005020b9072180c41c1c80907030581800a0040d0161007542e603070381d40301000304000e4080d00a02414801800681c4602c3c0140511038071080c210801a20740051000ca0880001d000440c1e580c25030410001d039040510101007082c01004914003034080c016050091340350440c80189907103440900a400c201184584074150349081c040c0341848503803105850004070104680841c80354054508a019124000001038961030120307a1030140c4070340310064400743c0d19242d82203000e50000921424980001c0240304265074540b8165031201b8402c44000b9100c00e0420190821504107901a24885e4420001c00c2440da0b48079040b601540d2904844014522400d40440c2c1c0c0350107038030440d6042c010001020000e00080c4080c0301e1046100c5c020041103030752800014400e03100d00b5650b906046106111480000b401140b50300c001e503007460700316140c0030b000382c445619254442c3d00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 97750620 1250 97749370 97749383
    0x43b1207062711100f2001050106050703080a050108060103080f130e16210e030c0d081605040509220221010e010e030f070309180501050109090c08060103051012 71
    0x1180100050841c654850318812114084d611695520140031160f0b42c000300c03000c000c61004160721488542094117070104020000b006a0b42e1140c00c0500940d0000c3c00c20303030200d5403c1c400648246c0490081c2416282e81c08060a4242d11f16550b032000d070740080e030364044d424805116071030310700c00490844130040007540c3d05003081c1c4c00c02e0301001100381800701000b01044200c00c2904121202c1c2c0c650089181c484c00000519541d241e1509811800b4100d0344091030301076038000c42c50a580c01610300b0302400200c14501c02c4483e40d643e003624280324911a45410808100024400000a84002c41d48003100e10305c2c4140020341d40d0000b044c003004002d12403201d6808074212030044038244a16101c2407020f000030001252001940c59072401003031105138a6001c00107007002054422401c7c1e0004005005c2200c14012200d800310020b41b800740602c900144101000180d442d0060090391045002034450303038256100c1e900110090a0002d0900c45000460140003c080701c00100b0300142c0c038000d41 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 97751870 1250 97750620 97750691
    0x130812040308150306040305030a06031a060a050a0f12060b040903031a01020c0f04021b0d11060a0b010e0906060417032101080303180705043b120706 66
    0x3601a18840303000e00450740500f6000c40600c810344000807060382054050628a0b03d03a65100410000340c10160401841000c0461004c4081482c51030070600990007100c4800d0740b151604180445607602c0d108850031401c40c030804001a1703020800c54506c1d075020f2040410109151300214094440383c21044002980e91510101005c0e00c2107a005c501207000d202a00001c01c1c41c600090804c031407600c600384225400152040400740080550710016081c030141c80e41d40d00703188406005080340d080b001045018042c0041d0308807582e40705a0a040740c0507103448901d02c140000340189220000e090a802c410108004a1280102c04002c101d1040041c02941c0e911000c8000703804101c940000c1c0000c500320310005100a00700481034a07401900ba07241c0a40b1410700d198027a150a58a90291f6005031402c4001c0004c0001144401e000014803603003149081011117070350003008844001d2280540115032038241039034070013000b03003c15800341201080304c01e87e01001214803c2006130020510081c00c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 97753120 1250 97751870 97751873
    0x304180b040612020a08070b0901050c15010b030f010609060c061806051f09050403051b0a02090a0c03050f0103080d090204022502090c0705030301060309080c16090e0f0706050313081204 82
    0x45e407034040940410b00140507014a8541800c4840c0500611141404808104500303450020000ea006441100c0424a5296584c3d2500c9600e40d0050301c85050308003070b40001041203401040140101c0b246507a800c00e600c14103441e80b0005040000ca0801000040414480403500d5130103000d0180c1c0303840c4495070300c45c0600140070b802c40d90258413081c4254207140402000c2604038040e00c2d400c070554401142d10314180010181000c42c2054025030000c08075061042c1008158042c0c2c4803004280c90411540d141c400c5904040300003440010640103041210360315403891900301c0103c0320f20180015003032030701c140721032035040714891050003a4100c5c000100301075241030320f44c40b0382203108060220314200c0300391140d81d280d210500400c810b244d00c0b103a41c0802c01c00c418007110508904182610680c0d4405031551880e584e1602c0b030a0b034400e0901840507000c40001c1454080000700f00010f080491801e45c0988990300001c0001c0d10358807034008a800822600d8000b420f041e0003030050b01059282c0b9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 97754370 1250 97753120 97753129
    0x6020d02010b01080c040314030403061e060909020f120111070813050a0303081605040902030f0103110f0d060c050f07110102010501060c0f03080414010e0c0909010c020304180b04061202 82
    0x140140b181c1000041000d0000ca02050b008840560350454800010944c000f03017071503d980306542c4000d03c410301c3d0100191800c6060002610f0b600796081040c4280345d030384c142d088113603804004080c1d404411210300380340520b04500050001c483c1c44c8000b0403002002d03030380c81e04e907a04880d0090b00d030305030700144450088a0301c03604400079004c22100303205200d0460b00c0091501d42c0003400111200400791142d44018060826100140460801035569240100d5419001c0000380703c1120510401c690429491a0920800c104030760044d0110101130183e440310000361506071000000d000e000c00a05200d00c01c400001c1012a01440c02024554480b41c00203084410590000c0c04022940034010700240c030002d100e101168051401d4407071901c49040450b1900b020301c001d850b040d8641070606540a50114244803a00300417141c81e40a0f03510200d1213401d0325005021800103030400c00044c0310202030b6810b07408540e1450040000d0340c40c1a003010400311b5046400071041242600b41102c11443c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 97755620 1250 97754370 97754381
    0x90903020a05151303051e0d1409030a0c0803060a030206070308070e09010501050405040207020406090203090f1b0a0611030c1608010e0714061810080405060c042102060c060106020d0201 82
    0x403c20010001c80c0781c804030011801c203440c2c50040c100000000d00301400c1c0351074542e003070560011102c0180d482c40c2404607603004001400c03601c03401000080010b46104004400eaa2400049031100019113982d65102100750b0300c0104450b612504001e000300140e181c2d603014080e818800d0f260002c15060440d005043d00c02000500c034410010200140f1090341e102080c2d03003c480050724056110784480c40064058145500020406480442084050903001400d50489000441951070800000e10480400b0501000f429045520843c0401245110350035100c2c407902d06509480c103024000e40d089003040d4180c611850341841080c0103001d107110a1150410f1018040010451140b901040e0412810840e03901e901ca5440480c0c4601c01c24101c11204d01c08460061405148541580b40038040404c252000d880700c0c401d03c27001820114250b4111416900310002ca91040180130070076039503d6645c91001c80c1c10400600a458006008010381c50203446a0f4010340200341001100030708440 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 97756870 1250 97755620 97755643
    0x515040b060315011206021b250b130b0705030c0607020304090b01020303060907030b030c0d0602220f180e0610080c0301140a0f091a01031511090415090903020a05 72
    0x450000400004103c5105202a246c2c0b02d90f016844508407880140510028403000417039005440b040ca945514011450404464030140d10b55100c1c0c0702c500200f914051200d100c21040401001803200d030710300801030310310a03210b1000c5034608105641324908001d4203640180c0541e001150601140b0404d0190309a840b800b84010360a40c40e043c80000c0222501070640c0044c0365460203800596101806403c80400d0042e141d40504911440c0010095003e04881c00817403401d07007042005c21030741e1200c00701140c82e00c00c40c45001c2401c00710907100e444010584401210354a40c0f80d0400c0c0c100038014107200e1000400001c003102d103021b023640e040c00040c408903032007645041c04084411a0000030942c004a217a403000075003502220440d402007480203000340400c125215007403181f03e0808815070589105034616180711100046c0f01080d6800a28850040c01d41031044c00014203059204d5043e900701d02c40155079043d0340e118030a086441581013580143c000300002418040b04211448611 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 97758120 1250 97756870 97756903
    0x105010e130201080411220f0e032b0f0509070b0c0706031131090b09010b031302040609060e0c09010813050a201c02030c0d0515040b0603 61
    0x5140c107421441c0c114001c00d000a0600c107980000c5000e1007006c950000c400300c8050141c61008800f0000c81008090040c46460075508100e034801001ca00b034003d15418580384d8004505183c0c1c51101031481d0005c0c2d40401414405851020728101120700603c10307a004400350004150609200a908101003904641c00607242042030a4650000040c0a402c84015240010b080c2810300182d4600e88500070031482c000001c640d442c95444405041c0200c00c40081400c0d2000a41c0c8910000a6840071041207038486040310040081c00011402180c1c800031904185514000a500060444815801078120299261418030a486100002580081a03440c1a50921281d40c000800075240104020780750302c030301420300c010000d0801c0500b5040d6400b0465042d00178072035003005a180c1c009844a4130030005143c142d0448100114100201500640908400c10b03c0e101841030403461990215903910801040038250000c801d1a0b03801280300715601d940a085c40c4003018940245465240d004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 97759370 1250 97758120 97758149
    0xa0207060c03200d0b10021e07080a03030b030f0d03050106020c06190507020d050109030c11011d01050315040e01050a060b0a17072c030105090c091305010b0a0603020c010501 77
    0x43c400340d140b42221800c0d4001c115902e51000130300501400408000b960000c54110a8508458000c10b5591003541c07240041c0c2c1c10002c15251203660b079076085c0318005036500315143c0f42000c2403007900001518030b0068102c0c0e400d03502400031145055000040000069174610062150940c1445002840001220030f0f5040606211a03041c0800140480505100e00040d2000c21504d5a40d07140c0080c0760410000c00001c195410f01810080e9004c0d011110500074892004171036000c0c02c541314958400c44400c1056814460054640781d00142c170040c16000360341c000c02400d0361039018100610900c48008501070414840c10030664080303030400f0001000038005011403039407007038048071800031644c1e064030fa64840c0c1c902507403002c4c43e02050718150002e05000105010045045e8103a10405400801c510380d5072282c2c03946c603084a007081039400044103022a141449441d85044020301403000024042c1d90100041ca540c0c16591101c0003085d000300791440540b01c00e11032640100b2507034481040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 97760620 1250 97759370 97759391
    0x10804030c2a120c14032b020c0108090c042c0106090b01090602030d02070804050a0806090609030301050f24161202070302010c06021c050903070623070807170a0207060c03 76
    0x15144885c00b82e10580760044801c0b240c25a410444001c1e0541d1040b001501d10303a010b0383c04048408203800c000098415802004140c0d446143c41d24841c0c14084040c0a0050310082003001030f0901d40c00b500528101020303003c22003001c030282c43c4407450249000080312490040c0310416254036280f580c1c14801521403c20482d0380200840302101d016440050740d982d90713484e11000328000e680066400105c0903101152000700060210700a1880070100c82c072a0b48c800010940e01e2209000d00c54100c0e070703d4140425181441420300305a1000b0203200600400145410a501c1c0c01400c0300e81c8111405c50745800610208641c0440c0714401032010300344c3e090454001820311800014000d200d035600040c9501d0300c81c2d504074443d03581c0c1000d041c03d00503810501d40709640c030f4000c08016201c507858078100140c00500c006614010501808100300c5540e40c0354425141a200100b81e803081c4646820030860001014004c6441742c0c8900c40e0061f100c01c120b007840700499840915032411305261115004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 97761870 1250 97760620 97760633
    0x2031902060a050c0709020a0903030e09010b1603110a03021e01020c06010e0a021215040f09050d0302030c07050105010308070b150f0f0d020315040605101202010804030c2a12 77
    0x1caa040d583d040c003c1d0380f60f8818224915102d00c9500c00c0500510104041d1a141c1c2c5c07010701c01048a001c0d54900250010074410000c420f0401e01c030303c8202c00c1042000d040643d02030101124014040d042a4142d4080303a220603003044045d52003100160040349025203420790b480100c030003400c5403600031410060046e44a0f40d03101418003407a08580d112800050b02c01d017940d0101c07403002d031941608050354208600e0a400b0034821511030b511542c240040d82d803100394248683c03018a03402100030900b04000d01d4041e0000d50000c2d05002405004121003004103070b09010704c0f4005c52141c0c101640d030340307024101200c1108015203126107a40c00da400c4e8424a513220050321500e5503048407290440e0b030f014000204010303031030300009405020b4004050000800c500485e886940610401d00580e0303269003400860302d695000d0100182c5d803881c151005544100d4145034090710908103003d1240b0f4035114240e58245a4074640301c0740c3c003040000c0ca001044080d1030002004881c000080758030085d038810 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 97763120 1250 97761870 97761877
    0x180803010e040c15030e060c1201050603040201090308030c19030b0d0b09011d0619021e03060a03081207030b040b0d0602030c0d02070525050a0302040209031f090203190206 76
    0x80e020058034003050901c81c4420f4454000c0031101d036000c074030011a84001d0042c20200c00c0c014060301070000001c0402d648401260030058490585101c0307031307080404008894101030070a030304001c800400440042d15030750041d401102607820803070301d88500941c800d2001c200804560209420404140c51544840079608141540f1401644a96271030f0141c25004001aa0950800d0b80d05440322100e90340b00401d07075a014014582c0800c8600b11000c24070342c280e209060642c52010101030382444000c80140266402c804000c04140d0965a01c5d00c8060315a080003404003030340c40311601030002054061140800c11030b0180e03003d000144581300010010074030020701401e240d4000000170206141142215100b000c9120115280d408a040480e580c0c1269861214522042c1c14001e40d601c1a410040f400c445000f4820171591707041d5400d020281d0402540150507119142424003400c40e0701401c0a40303400c840304d0009a4444600406140c440001c4141c03440319032904031080944c8814044 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 97764370 1250 97763120 97763129
    0x90b01171302010e0301060609050111060f0606070c0302100f030b220b0105040302090f0106200c060f120c13050a21050f100f05090f0705131508070918080301 70
    0x102024040900041e24a106016804ca45c113503e000c90214a00390006d03901030681e00d080e602c0303842000c06030290644e00c5006440111400d2000b01c0000d0742403410000403d44a4802c001166520b541e0f41d0128014808107111200130a020350b85140120390f0602c11001c07005030840b40d6110351944800c011410f698a800d01e000c0c0f4a484020398022a40540d08440045074041c0600e030151030701026503950751500303020b83c2d4000792030510305c0042c0fa1060048003454651004c040c0112070142010032107c2c0d80899800c1c112642e080c41a1001c008000040601c281381545103169034030010180d142e00c060b8150051441540d9080d01407098640c43c203c0302003002a1180240e0101c4110704007207150408015141c590b40c822a04851800b9203181c00681400d1700305001444261544840f994540040110361186680311440411042c030781800110340300300020351b0000da41200c407444030702d100d5102d81040605030700032042004100540d01c5002da0b80c54003c0030300c280400041da20414548410b208 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 97765620 1250 97764370 97764391
    0xf01030b060c03030a09020114030f06060904060b0d0506150408071418010902090108251812061407020703030512060a0e1806090d12020d0207140304090b0117 70
    0x5032442141c444104684074603800b0022a034a030300e00700ba05100502401c85080780002c00300c0c1400040d180da4501564040d00e001c0c011003009036a8001800782d160003221400b68000c5e10340c2000035036944440000c0c045129041c0c0b000c00c452602e0400e1000c045610580760700203900800040001003000705551080d98610840f60600c1076088000034128040d2610400300340e459040000f1f038090080d8001e01744d000342a00d40701a0350342c071420070075a030910010307000100000980a0344449441b03100402c9140210b21070707518800341c480b200e490b100000f07031301d041b6407150f5103411905400305134400b0b03079621072103a1005020b05030071130f0750081c41806817002c0ca02d214100700300414010ba540c1c00341d08000d4a0b040540d10000d141004000d00503403607001c21405140a0840031030f0f040308000c41d19514101c22500c5400003d02041c004070025031183d401c60903290f50a0007a0000603405104030748268080307400442e126401d022106048401150b80141803183c0748c404c0000e031154502600d41d1081c00d554 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 97766870 1250 97765620 97765631
    0x60301081015080f07090b060f03010509040f060e07030c0905011214010603050307030504050907020d021902011b0b010807060c02010207090f0b04060b0a0909230402010203040b0705060708150f0103 87
    0x1201d94000c90b441d0403007005400b40c5a080c009403100091002c0468000340002c1c090710060100744400c91103442e00010303640724200010320190a0503042c440d0000c3c03052800c014469015203685040341c0c403858808000780c1004004006001a8182c410013405010604000e2549400c0d845184086603441c010000745685100303103840d58082d03100c1c100441d005002d50303595407401c0c980184981c2c498003c07140708821040208220901c000744404c07441401d50000e00346540d00300807060040d140d00d2407c074108404c1996441080752820340395000d0610405040c0282c0d414070140d181829541d810150421501403241c9016070303070018004088400c0f115000810003040801103000c0c00a0131a00c5400c00c0c102007000481c20148001084441031700e41d01d07020156101c52608094510f2035801082c4002c100000041540c00c000c0c4050b001841401100e03d42650398181000070303082820140c0c0d013600120204803200350040c01d42503010001707184004041000d1800504043d58443c500b604056840 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 97768120 1250 97766870 97766891
    0x90a0212030f0c100c0503100b0903032106010207061e120b100c03030b01030204060e1e090f01090c09030201021f06211208090607140904020403061a0603010810 71
    0x14012602d0601100605070750780d402100505907692007880840c180c007440d10300382d024290700c1881560301400a046042c0c10341031810b80104080c2d003002004640c03500041201106403030b6501311400e4103006941219105141c120000780c140910340e03001d60140401c015299210007075400e4039215411841c100001a0781d8510320381d800401c01030045580140e1600d4001c1c14250300040040d95241c0704e60f50034003141800200450a07070185108103404541007558200040c60050000d0248450303103070b0b1038202c0301182000a408210300703a9044443d000d010005000000345401081d151152034205401440d107945c5c0000d60b01c6400e24001170144d0f000076801d10110255070000c01c02840703c80c80e404014116046c54080e44007140f101101e286003a0b20400b0262402404d0091241008102820382070782d842e002a42d103240c820011501e403543c00c202d5890305555a00c0600f0203140501c0001074160741140f40098001c8861a4070740c031490042c07004012a04000402c504903440841d40418440041c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 97769370 1250 97768120 97768123
    0x3050a05090a0816060e030a0807110a0b07140705060901050c0703121101150b0f0a0203041206020405090a0506060306010c0c03020a0306140718141f03050105010f0206090a0212 78
    0x411481a5200b66100d1002070700410002d4148503076168014400041a9103140c00c0d60f00203045c00301243c0640204c050200030402c0b24010b002c0050040012a003c8100c08001441241e000e07009051904008034440042c00310031001000c02488000c011304205060034000b0302c0034000e491941d41005000190012261014840c285c0295031001c203540442880980180c882d032840b08501100350700e070050541260100c0320080003110303800700c45903140c80003401c0500c0003503209030798050641c84100b00000d00080988501189207000d84401a12281450100000b800004d440410158248003d019840d031fa00b5080b00c1d00304109090001a0668078540000c6066107540080d40c41501020000140251034002e000307440b0b42c45121581a5540800c10343c0c4a5000008007041d000318202c09115044040d1000855000c0042c03010104092113081d184002c0b206d81e10400000c1d0315440108a19604180c0003480081c0c2400501800d1400201143da0340c544803001070310654001c541001c04440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 97770620 1250 97769370 97769377
    0x50102031b0c0d051b0f1c14070b0d0608031305090604060305010906050a060519060503150409140d1103030408160209130c3201030f0c0c141903050a05 67
    0x4018100240d491041d0900c10380380d00075050b6030715000805086503c00d41c90061400604940002c0441c1c0e440b802e00d107d119504558803000b00d0718030071710001003180101c003003215800500c4040c1c1c0540d651291721a541c0d007940c00aa0210b0301a81c0f080c020303001c0d0010341040c00402e03220182d40d10078040c2c0d03c080026018122545c005481075107801380d40414404280c22542c41050f1400081c1b00d0750b0303a248184498142401e050305101c800b2242e043c80760b40e1141c0010341d00081108014588084400700040c00c0350b0081c202150459040038684000300400e0103034031451001350403c9010360540143c02c80d1a844002c0c001005501300040d1a070814002e41c44000c3c0240c1c010781441c40900d05948a8020102c0d031310b5040d80e440440d00b1b000500810300311141059401c03141c90810442040b116082e00c4480d038240c2050605444c0c0300c1e0041c0c142d030b030381c41a0000344200e69540c80c4581e6003400d18102c2c0d48001b10034ac24103034102c4100748034440c0c442e20030308510940c5403500503560308403110210381c10301 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 97771870 1250 97770620 97770643
    0x60b0d0e070b0d0b030d0206040506040b10170609070512070302060c012004090e0105072c06030915091b060313050102030406050108010c0c051f14070503010f0906050102031b 77
    0x200d001c649400d802c020b81d132160000c154140c040320803000c10a04140c2c0c0d80d0f00120b9000b010399124070300080004403403c84190300a066a044041082d4644c068104107034001041426264031207001c000320310504001040091405807000101c4030108603210b0780300c500600001c1e009210009440d01c118009500401c00121820040708403d400b0200c01c04499210b886203580131801c100c1c011042c03d00c10701c21035000700d00648502e58641030001040c55038036a01c29031100360005208410706e4a0300d81500642c480d085104c0505503144d1008496131103200050030001c10759101c00601803a0740d200b4030b0610341040086408680b65600c4940f01e02075060340f080c008105500200034042044556048035050780c2801c0000d10002424000c111203101c040c5034050450b80c4120b0400070300180700070f4844240e0321194008100107168070824013000303034180c0342030001900c004010400404e40721400005010028002e010b20b5203403000007583d07400350518000c0131004030441c5c18040301d400c0100e4444807 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 97773120 1250 97771870 97771889
    0x91403031501110115120602190e041119110f010903020a031b02090109050c070204061d010e0702030d05060d060906050a0f0204052206171c03060b0d0e07 68
    0x28984041415071a9400301001c40c0410120441d0380309140c018000c0001c40d4545011440c0400c0c9802001940940603003c01d451701a420464a01e91803130014a00780f854480f52101440030360703044103102c00c8400c224407100000c01e05101e00000c2c3c90a0080030038040c8510b240000d642c042c01c904040c03c10f02c1c0045100250342c41c2c02c501c24105500403a25402090290302c0d0342a08000358494071a5140001034000c0d809086c20740140028005548074542007841001800c1c1032000980c08502241d606801004180d000000d03070712050001c5400752809480d00c08100711460070b100350040c0d5240204020030202507140c0700021019100c500030040c90790b42144040c0004241030405400600003654501c070854101101107480c003500d802101d0868102078008420007090b09800381d0200381c1c0d012600051a100c82c1d0000c0c40395990001c60175080002d4015140c02041282c003580c00301d0074424840289400c10004106018041c41512019220702c240440c1c0e500b00458a1400e088651b08a11340d032 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 97774370 1250 97773120 97773127
    0x606140325170a2705030d0204031a1f060c0302120318071e0303030504020d0f05031c1404240507020708010b03030306030303070c080408060a0915050c0a03091403 72
    0xc154070401540100314100168441500c0710702042080da10034035254001e6092500c00312400d901204000a070045c051025203051280495103202a40d00030340c0103450840b002c2d005801c03021b00d800005a00903940300700e1510801e50801d0340c0c1030388407810701c10b030000d0040c200f407104103140c02406040c0554190600c1191340b46800030125081d035000001d10a1244543c1902140c02c4107070307160a0320a5035810b0889908645140d808070080c21000300b00f2038100d20505035000000f40314003500350a59204202031a01c1d440200c0043c108005542131944a0368185060b40504e4445118107a4000d900440b044d64040c0c00318000101008020700c0981c0c107103140004200c034150b0701045c5c020903621104000e22a03000580304041d40d07030005407456a03040d08100040b416250140e1142c4000070303c94880d09041658130310001d41800c00480354400c95a84803424801001810300041408501c6d80404001c0703030a0103030200020f4010080144203155640e1100c00c00e20a1b4142c00d014500c0e04981120303903 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 97775620 1250 97774370 97774441
    0x3020904032f0303151f02060105090703051003060e010207050d020601050f060403050601120201170f1b130308030703090b090a050f0d08040227070c021306061403 72
    0x852020307000480e41d40c040240203461a9000c01001502c50742080c4015415620f8039039461654401501096030f0001120303000308072080c1e07420280c900d40c16a03500640702a42c9000c040c0044074030018410001c25191100700161079030134a000c101600d4100c80700154601556030200d009200380d8002620f01d1003002c424403000c590000314103040c1c54040c4c820a0038112108184041d90081780001001038202d840188901a041c00c02c2a0f81e460051601418881c158981422105010760b02045415540020003d449450f481d4076012444819541481c0c0300160007501c0c4141014040100308800001c086480c452003900280c40f4150000000e80315814100e01c01903170f5540715041104c0074014002c0900c640007011a517019100103640f0f9020142d80c1e66800c1005001c10b81c1030341045600c28209210445900910040c0304e4105500c84421001e1207004011407a1001601e903040300b42000d0f81405080c6d4000561002a0006000c05840b9141d6100c0c03001407002003940b40f156900600c0341d208 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 97776870 1250 97775620 97775627
    0x4180902180f0405010e1b0418020d08090316060c020915040e0c031c0f08060607080409020703090503030412030309060905030703080a0501080601030809010f120c020304090b0405010608041502040302090403 91
    0x78000d62044c0c000f04901e07004c040c80b07685c680140e445c3e20008805607038040c0d40223040c00d40203003100c1180003d84043d4009150700241c0c031000044c5082d941850085628815420308004a04d00c550700c4d401c00d0107030603203803035001400c2c100c203000000e000385040c002186800d0805c0b00702d001c02601c020310a0064941c0b44400c9580c1c0c85480c605588244946207991350901101516a24074400c00d03270752504501c40c00b200c19900c02c14041c0190390840030411400c004940804040c2014041084000d66942401d003401012041507410040c8250070400c0108540080e0010b602280303949418041075440090500303030014511b0080140850100043d0b0f8810140d00c10300c030a110341203284041003580d803104a45581c03040240002040e84c00d0801540f0075940c0600714140c0610110f28004401141d10300c0c40c0d8061340e08205d10200541e001103001d00501e2080d001309041d0307000c1a0b40401c07840d0701d0308400078040c0c0790181c0f025003e4140c4030035804c200141a01110301854001c0e04a0030340b0f04003482c004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 97778120 1250 97776870 97776901
    0x31e1403090102070914010510050d02041710050c0a03090201020705090f10081501051509040e030a0f020c03030307032a09030606060c05150601030902090108210418090218 76
    0x40b40140a4000c0c04501198184188034101c0304458407804180c0c24241071100c1807040040540c02d00105000a42002ca400c0c00100301614a0010070100b00301d00d1131141d0b19103a400b4030703060005800c0c481007111111852082e500c60420900d0017184200c21400181d00308211504503a0b04440300b001000000030084a00c5c40c014515485c081c0c441170350b1811240d44401c40b094114007009013000040082d0b145c01c3d007030f203000714048505c10b502d05a04440044e08550408090701040c0e0030218084903e280c0000c1c05c00e0600d4400c0c0050a80030180c1400261603201c010f1200003415500d01581882000f01c8100003045142403514184407595684050844901c40c8021031b005410100045180c0f445410100f00441d4411300400d440c6148640c2680c40c450020a46410940d03680800f5015a480d498500e0082042001030210161507090900b40d1400004a52000100402c02001540c00074161910740741c50520380069210402e100040300921070709020701c4484084024458035400a2012 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 97779370 1250 97778120 97778137
    0x150f1815011406070f11150d09060506040207050604080c01061703040807060c050303040b0603010e031c0b0a0b03040b0702101a090f0105060702060d1d0d0f0203070804031e1403 78
    0x4864140210300100f0402c1c0c425100300402003455000345600040c107021044c0e200600041c111800c00b020210b1640300b680000d25000c0c1c9040d100c0c103239582400030070300c116030b08000700b80e0b410340c5804c5a50310f4150b62440301801c014941e00c000038603c41a40d80a500c11005483c0c103c02884080854600d5a596500180509111409403050018402d070003443c4000c00d0540c0039000e5800c503959611045070000c402402203816548482078014212402d20080004800f541e440c0c0310350541074503250b012100c44180c45400350407003c034180074030500401075940c403d034070282c10416941c921404a0509200c1e81c0ba2400c40760400c02051184d58200c080150300110547c0c402c4010b0b0b54001c50f0200c075403428481c454110b1010068640503042400080407449010540400e5030303a01c0e00040388010012a103d104240c000e480324411640d40100d5111024200d44002c40c185000c40e214440799100307921008004201d0101c040300089203120801d101643c002e50400e040c0d07141d00007016101d900c01d025 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 97780620 1250 97779370 97779389
    0x30f030905010527031c20120702090a020c010c090312030c050a0f0201020f040e040209010806040203060a0c020f0706030f06050a0315090c03080708071103150f181501 74
    0x8000c281d41d44104151018070200c00e203400c00d440080780b085440c65001c00a4645c04d4020b0781a5580c0c401d111134000055a882d50307440804c104160840c000160201000f00c8145400c22088260b4030355070b41c1e003554901a0101c8400180b511a136225000903c50080028825401c004e02c6c1d41c0300c140c03c00701c1941281c3c010000300ba030410a0550403402c0310400b00c240c40101d00280f049584042c460390702524640b01c0d41c00014035001d00058910034941069101419100412040008609240e02820300402490740180540d040135070029499490040041150b90368a10038400924400c005070300704052400700b5100c0b0070344c5401c4c00402a0180e080450090303400c1420008850600721154422030741c028070020411036130080d01030f01074803003e0000c4c0c4451140c58004808128008000e10f032091048850704d81d41d4103a4a41401c03d4100311fa40c461094003c5114040c82d8580809a0740d0b2041d1100c102050940e83c1c200c9030809030040400d1001755200e903e402600c07202d0300f5181d4a040c0e4107800c8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 97781870 1250 97780620 97780637
    0x40b0102030c15060109030b010e07020106050d030509060f0d180506070c020f060327030a03050112021c02060d0e010e1207030f031e09080306010e061303170d0204030f03 75
    0x500680e56403058100d1003100303038400d02c0d58004a03070a0560140d00701205241694509540e40c0358955170b65801c0c0c22120b01000300340144001e854091064600400054a41280618003524041c0042c0070742001315014030400200000e062811034100c071441684508208140e00e924400d192244c1030b90601118248a80b17000f0404a40c052546150320707590042a0900300400e000900405800151640300f50000004862862480400107100941c90000c011516083c03105001010b41d801a0300c00348996005820510242c3c03150501c80c00c0c00d145594502c021404a4804031310300c2d200f80d0b10444415442c2c0352800d11034240c19007200c0170503107804080314030a6801032040314a0b84a0b495004000c1540f848410034014040c1c0c0005201050b001100c00c80c04040760004000e595071854200c0307190780300008001e1150380102c0d85058000c810780c0c00c541084058500304032419901e000c0a000807032603e448000800521044801c42c0f1032002c2d080d9100d9a0305d241c203240c446c0624200b10003080400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 97783120 1250 97781870 97781891
    0x50603011e09020f03060108030a0c0c080d020a0501050c030112030323070509120c01020312130b040c03120801060e01050906160b061311160510060e010503010c0509090609060117040b040204 84
    0x281d901d0580d088000512b10b031103042c0400b600d82101c408001c542d04854100001142d603c288100c0c1e43c105c803582c0140500004502d029821a80014401c4081c10320500040c4000700046201da01100d606007000240840c0b1850a44100d0024060400144006108010a4030b40c0078014207001c4c0e805481c0070042d4840310302d006813140d41d0a5038090040e4001c2c48000e20308800450071541103200c01a500040291544031940d200c0c1d4121003e40d0110002c80040003013040d0403400c10000d012070702c1d0100055043c040f0060880a945580504120000c21510f0340c41e81d801c01100c0b0342540c803c140031404046843d00701d9040b00c04803030300d61240c40610204120b00300f072802045da82001000515103001542c1140a143d43e0400c1e200b81d130b040c0b0030b54a036204120501d10461000d0900701118441561500d001c0500707407100d034181e690030050b017444404030607150345030840d400c01011541c04095544080049500800a815101c284002d6070103104c00d00601c802101d01882c02a101409128041c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 97784370 1250 97783120 97783123
    0xf010b03100506030a1707050706030c080603010b1f0203040806130201030501120807060504060e030307080105241e0f0a03060603050f0906070e010e030102070b091915050603011e09020f03 83
    0x216080703605170700320f0f0f07240500082080c2d4030240c1d01d0100402c62400c1200c907407110703403030f00b00c0303541107200442d40d6150805032042d0091f05181d4041411402844000084ca0201e180044070310344441090110708070042c6410b00900c04d61f4050032680040f5540ba1411400018818242c000280c0c08030f4079041c00840e1a600c00b441c210403040d00f20b03150030b1901c2641d540c1e4030014040200291446070b40c030100c0001e84074052000358051215655440500e5042204026507081c076283c9100107808691042240411000195540e519000c0380b864101030510b4101c2c1041d00c540e0034042c956810004102c482280c141e403100b41610b03030f00e0b03408018a95828026101c02d04058500c452103502400009054034440d0107201e4440e80e040c07614a03110139007000071078260307003241008a4201044004101080b681000781c034075581d0308150405048001e90304c90024017054112080b01043c0c5440000780b0580302500200811562401d5074814600e80c402c17810001c0030001d400701d1180806400d203001c80d190 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 97785620 1250 97784370 97784381
    0x30e1206090303011401030b0d060b04060608091207020d02030a05100e0105060f09090106030206030108070509060d0201051e071a070e010207030b010510030b04060905070f030204030f0b040609050f010b0310 91
    0x14a070700114550303400c0c102210000000000302c28105621001444000d85440b200550a00e101c2c6001182414984041000386c4485801030410171580d5410880c641030002903105044491100a503a50b080310300118100741140b150103901031185038015810401d0009518507002c000c0f903410450b039141000e0660a8070001d6482da60b02009035240c2d80c26601e481024680c00030b03080800010095900c0c0e021824a0b0003d034071250a91300240701c01c116501306a900181c3c056800c460702d0401001d10390000c0c0040c090361030507804d4403450642038001076041004581a56800006118075000114800a00f0000c2142c0000004078507452a41940d400050100103036648008031802907801c0030244102e01c1c10342d6010804140c0c503102e1011581c6c446110701006040f04607804221031030100005485910102505010507104203c10804140c400c0d4110103010f900c0000340c40251903c2c18204068400100c01409500620380e400c900740105612070851464144e094440c100d804000c0801103d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 97786870 1250 97785620 97785631
    0x604030507020411090a090b010210141302032a041b08010b0903031b070302030d09030c090f09080a17130b1803070c0311040b04020309030d0b06090d030e1206 70
    0x8509000d64030052400e50065074502e00d49544c528142116980001d0303007440b0720360002c0701c1c00ba40d52081a509503414480400b81580d1500181b100340c0c090301c507502c41d50500501d00f241128003010010110359060290507070300041c4c0c2401981640c0800c0c212450307501034001480c0f00354a0004101d02d0100c5848000f9040c1d4110307120a8030f141c0c68403140c122264082d0080c250f060000f000514015160b03450300c0b503480f0b0302d00d030018a00c0c9400c520605103003036012030f0394005001c8107210420000700b0628440090340e0700c207200070801d4804007500f00041d20100304024954580821078480959001e501c03a581103011107128851510780e407000080701c400d071401c00742c9100005000982c0900340041001d0010f81301d0030440707240c41c1c0c058481e4500030180d6041101e4411041034480700501c0d25003e6088601003c80c1c04514600b42445555502e1041c070400e000c04546034000e1140302c1ea80c075003d5805624015102e003506030024540101000d60210905206007900360228211403070000328103201c0c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 97788120 1250 97786870 97786877
    0xf09190b100c0b0921030108070504060807030f020112050a090b0130020609061c050105042a0306081e0f01050103030e01080a061d09012f0c0f01050903070b0108060403 74
    0x30b542c1c0d44901030442d8000f0142c3c0c100344500b1000d02c0760b480e0048861042501028201030310307035051031003c0d810000994403203132066080c4401484002c2000c104102100e034004c01c0546ca2054500c01a100b8400c65001d011b00246000100300720140141c1001190750b204a0b982e4075142c0e01c0d500000d905011000d403203114600300c034000807032003007114400d0910603000401e210301342400500000e580c1d03482120300101ca100c00c14200544943d0703901a5501500c42142c040c414050100c03001006080030600e1080c01011507450760210794001d51080d406004d0000a503201071028080c884032413410182948500d1240d020030082114040c81418140ea900d90741c2d0040401d03138440115001c00001c1c142c00c02c025076480000506c0304021400c0000004114190b11641c40c05039250307400c40300f950002500c01203500c00321803c1042484190b50406500052003134488000c0810240f1303180300c2e280b14cc6025840c0c04180f0040c0100003001d02025481a040c0c5011aa00d5140d465140da41c00d4a009010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 97789370 1250 97788120 97788137
    0xb06090712020a030b03030a0905030607020304030b04030e130f2004030b0f1e090115090c0e15090a0b0301050a0f030b07080618100f0b0c0303150f09190b10 69
    0x5540c00703a0010008440c8038540030800ca055200000c2c103541c45680c0150104040e008100103c0c1402c0c4a020ba210b986800070310700b4945141c85219950000600c0241000005440e0707130500d642e140c52400da244400d0404010000040c0e4480c0b0081c8046040184c049211004804a0300031040403a130a13650300603900b003065200d0841c6041c00b00c070050110307459000d4a07100ca26034960040c10842c4512034100001c90181954801001c1418440e000b00c0041e0342031001e0050340a0f045a46044491015607054071459000d0304404e909003d1124141d0703101818503800940901d4000145050b42d10444004116a80d80c034041d01d0328202c03600c001400014400000750301e090017215210f600c0343c00030301b081d0828403034072072002c0c0c61031821203106005050300b03c0c040c080500d4424281c0050300d064101c803881c210741c5602003682c0e070200608144042a2402c09181d00b038444010640d04040c0140410700c20741461403080808041d040d811038202ea10301340031504646042801c0410700c0d42c05443e010035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 97790620 1250 97789370 97789397
    0xf040516050d1118040b0601090b090108040b04020a0b0a1809060609140a0f0b03180c0a030803060a1a0403031404060903030509030a05070909110904030806010c060b0405070302070b060907 83
    0xc01450781c0b030420f90007600058103401c1a204203540c1d61040f84500c1c0c43d83d1b420300e81200058121401500f00c420000801c0c042c01a070307640c00003c0e440d080383d00241c0c100604c3e5258070010f25100041c2d088658036500100340e0a42041c6c001120409400002c001282c01d01c0c1c58011039022242148100400030340c0c90941045601c982e0040801d40c540f001e003000c10301b42d4aa0006c0e04010307070b00c0d038803110980400000300045601d009143d90305040300342010b440c040e20040000741d00c51110b4040500180f00c0000812846d9580c031040e4401014407005800d03940502069901d40e0340c00601c41600401c0d240d8110701c0b9101382c0d241c103d0302074410644079100742034290f4904035905c3e000701040a07010320038200302c80003082c0100500d4000789542d83c00840c03a00760314504a01210b08403421076001d0001c100611000a40043c04168062001e103803000d2200011304201c0050002c00e229145c0182c941003d1050803a03140c0c0003001803d0062888851548545060100d1a0fa04072100c10008010902c0c1d243c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 97791870 1250 97790620 97790633
    0x51810062306041e08011103070e0114180d12020105040b010605190e030c0406091a0901050d120915090515130302040c0908070e0906070206070c0201050318060f040516050d 76
    0x8541214131004007102503182c0d4111803c40d4015144e0a1283d2408001c010030603a200c0b21503d400303c2c0a1800241507a807001214131140203005049803695001402c0d5810350700c03282180641e45411400c00b0410100010dc040e0081c031080d40d096821784103480000c5602c0b40100202d810180921803082108005c20204503481c440c0d0a4085505000301190b030b08450341c40d070180303501804c0e4202000545d0680d011400d104c41c40c1080305140650401c00042006544815a200560760010a080261422000219103902264011115022100c0680301c0041d0b480b0020405a403410b888101c04814901e02c3e4070042d020b04600802d40b15840441800107043c190001030b09a040390070010750480d1900510303800e000c2c1c1e907040500302c6940441000300d840700400c001303508508640003400f040c0c00c000030020041401214040e06004000000c0394011542c0d10a92614080d80410385005d0305004e440e003580c420003610150740ca80b09070004c800035071001d41c3c81c03c400c45038001d22030601600365130b0319035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 97793120 1250 97791870 97791899
    0x2010221030406090807020415080d0905030601050402090a0e0c0909100333020c0f070e0601080f0411040c260709060305090c040203090a0c1406070605181006230604 73
    0x1c46031710350240603d500589607400348105110700f000e070604001d41000481490007010318140010403001c0350007000301d0780300400c0b4a130541d20143c80240e034031b1308940c000c9842c4e002c05901c05411104000b00f0080041200000703094944400c131104002130704c4040359801a81000e000107484020070490b41c0f504420030143c0503c05070500c10344102c6c0710b003800340b804040b60000e81c4094500d4001c040c41c10b03030140003401458040c000c1030351011290b00740303140003c090140003011a00d00c00b081c840440c0074810600000d078606007009100384541d0070400b200901c0403600302c0000b41010b00b00407850310500c4800b030005100c0c001303503a00e01041d5840e0001c101c000d45809000d9980031300441d0846411a21540015489000078200a2681c004180b034800b6108642e54400340303144e07408140b035624554565040f20341c0144c000c20081407a0300c88101034401d1030000f001800325441480140c0c5032009940c1c000c2411500c580800d100701804000700e600e50070340b1001c0c1140d40220200010700ca01020354109 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 97794370 1250 97793120 97793123
    0xf0507090b0a0909140f0f0609030301031106070311010218120a1212020d1401170105070f111c031a0a050319170310090b100e010e13020301120201022103040609 71
    0x1151100c611440550305200c4440d001d509540c120385801051f050302041040c0d0441a03440c0110716640c9581c48104030800aa120340b0b201d0500044d8000030f040c030401e00102e0307482c0c1c0b40000715640c0725041c40508052821900c40c034011240e02c2d01c02540e00c83e02107198003650390407080d0f001280b400558202d40d985001908041c0c11a03003480380380c200d8100c92007180d041c001040307a2030a0a505203031040300c0b41c2034255038410050703041404000d005a030224501e031554206041c8890340014906945040002c60b485c07807209191046103c1820740d0341a0400211120b5404042c8071a540c0c8000740041401907000301501070707201c400d4241002e100403140d40310440c05030b012040b021ba480b4050b150194000d80301c0c2d0041226124060000082910032100b600c801224003002d03441c66210040d000d0410b03141c100303050225028100b042521910000d1413480c5c84107600319502c2d078451260b0340c0b070b0312140e09091740144108081d050070300302000e02101000c003ca1101c00e08540c2c40e41d4400d000b03000801c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 97795620 1250 97794370 97794383
    0x14031c03020307180306061d040309030f0305040803030928080405120106050303030a0b0f040509060406050702102f090a0909030201060e04121d010504030b0a180f0507090b0a0909 79
    0x600220034021106500614828a07001c0b0b200f616181f6900234003042100c1c050a481c0d4484140000203800c40310780003c032688001ca074005e50506003000d6a50780030b2a4811081408000100315200d4404510f10f83c41c01d080c2d99414000008011031095041c8565200a0081c002080144040e242c2200f070b010260065800119500703881e000401c3c210380060b5008500d19449442c40300e00b42c5000080c170103e041c01907804106900e07148a4080d911705001d4006019a5955030218004038030030702107aa00c83d141b40301c007405500045d04241d1012240c1c1d100180006842c140480c00c0940210200e44e444140108080b1030366041850840c000d003e200070407410356584000010303000fa5034144243c4120b000b03e02940b07070340030a0100a001d510426018242000c4900045000b50b0303080b00030798040c1c903005100c80c0e81c959901081c000c02440400084500c0310703a900b40400421414010404d680341c407600540b0440c640c1ca561400603100d002e1012031340108020010320140360360f6400300365101d0103184c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 97796870 1250 97795620 97795637
    0x13060e03030c0a03051206030109030f0f12060602150a0e030a18090c03140906040206031801140108010203190908070209040813030818030309030d0c170a050414031c03020307 77
    0x2c0c18070b803510500900841c00f00e4030114240382104c03818240181d10420650007070101021969000702100d814142da20144015500c0f8006014854006084d0080500c1003c00801da2201d8020350f40d20b008036000040340d498100007c031011014051030708064080002182040080d21058484800444d811401e044400c0f6000540070031500800b142904291130010301c41552003400554030000824200d101c2e400081840300603201c0f0f20440e58840c480c0f0207045d14408140c261503000d045642c60048031000107030700120f000308040d4000e501560f15803958000400074480e031034066a4000784050440001809002c0160a203078064550007882a40c4a52a201c854060340b10341400d9900141c1c0d030510701003600b032107a0300042030403c40844110020342c100300030301c0006030b0f440b50040c0e03001c001c0040c0b0f84200380c02c11006003403442e2080400c44107291240814100244190094030401c215005604010412801e0200b5010f80140d019110000ba14500480584c06544082c255104101a10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 97798120 1250 97796870 97796887
    0xc070201110d08060406090507020d1101020f0f09010e090115050f090d030207050f04021201090c030204050612090c181f050d03080412210506040209060304230313060e0303 76
    0x40c00b1900020403251902100d0b03061600900040752407a03002104140d141006104555800003801c040e0b040e01851b1503040d04644c0319130300d0701a02583c005800885804204100c003219102c4c0601720308182070307840a103044208410407280000a115807444428013505001e03000307104074000c0040040c65150325117003010100c045620007024010507001600054001d00c49480c02d01e48101090108603800e600309080030035444031200042c0720b1070044a070344038200f401c414080d80540d402404c0060032a034407480c2d84566101e003410115280886801115500071882c6095010628402203d02c08001d46984204040301032070542104031440030018080043d1554482a450341d0152199449000c54105846e05801c240700c2c07135005e102489155282c1e1071022106100001c0200001c9201080c11784071400032800900c206403510303400003000410003041c019031011a80800340318030300c421003400403e5000d40e124000d82c8501004048000b0041020500c16101c14103151002000d0303a1504070394 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 97799370 1250 97798120 97798123
    0x120807170a0503010b0c031e12242206030c15091211030703020a060c0b090d0203071502120c0c0c03011a011809020307090e1005030307080307110d120b01030b090c07020111 76
    0x703c3e181e116241c0c8e80040c640c845c8007501c0244035041074101c42c1700190100c900c80c4102451150f0340300c01b4000d00517103003188c40c8010241d50000402c03e40c00c1040058907101c1c00c0040074001e1a001d16001c981245010351411441500104c007211000840b015000075550b4035020724004402d030596242c401d400000c40580d407840344101c003c00d9280c1360070324030769024a840300306001c001784200030720342042c840140d00c950040100c600c2ea6a11503140030740c400e09240054001e005549080f01460907090800c00440c60781c40052110810500803078851140d020100350a9402c1604540b1050440d0100c0b04219400f40e41030700d6001c00324071807860105459680c24001c9070821200b40c000281842070821407110850314041d006000c40c00c51441040c2080c0202c0d03524800e4580080003000c00200103181d0070302c201240842d8415000a458220006500090450000c828a05195450800407040641c041d106d800e03910701c4050440100d50f55003090320704160300b000381d0130f905000700c0c0f20328103105132070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 97800620 1250 97799370 97799407
    0xc0d09021002010b0f150f2a011a03060420030a050a060609060608070906050d02040305030a0810060905092e06020d0917030d15120807170a0503010b0c03 68
    0x1c859000041c2042c0f07540c10480c80c2d8800c8100940a10303414915403004a040d401140c044c00c1c2007848550340c848090041b204c801d0103042c4880b400428420040303010003019003184000400b5400300c4071409141d003003003507160401560002c0802d10811a20a500e25500d000000c5201004007030f201190070a0704c906051480800080301e11a9458000b800021a2072183d0005401c1e540390514080c174290201503d1101a8029242130010100c3c0c01000c201c400d4040354041d40d0300800752610381d03508400180c40da480994a41902a01414001c1090381c828044841180c4004000e0401500c0c0c004060180c86202400f404400b0300031036001c0d80211240b0303115130080140d6801030841c1c00440c0c800030f202450541046041150218174000710210000036140080c840020020b01400d03041c0d0302c0511026554050000344400c915501c0504c0b01100140c509a400b46803241d20204058082c010640300c2c2ea1100c00c0400d030103000600004406c50090840765255104903442c01c140418035000c2c442 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 97801870 1250 97800620 97800649
    0x60c0709060312020c01050a0516020d12030b06031902090a050406080a062304020108060f030601180e010207020a060f0507020402070c06022b0c050a060c080426030c0d0902 76
    0xd45940e420403c02c01411100901e900319880544a44422000024030306d10407a0031035400c0100210b402c250390b0b00440c00520801c3d0380100a0118020300c0e01d40b400c56564001c0e07408022030703c1c0141600701c0d0304040c022070384610b00165064880c0401008064025001486c03442e80110040b00041001c1d01c0f07901c46c640c040c01680b401400e1101180c50044152150140e00e00b0a03000e0070f050321000d0001d95641242c01c2542400c02d6802580e400d00801c10703500c14000040e0789407148100004001e041111040342704a14050b081c0b041d4000680107600b030348100d175030007500014003031000c2242c3c500c5080203080c1d80d04640b400381c0ca014a9500000c0503600000400e81e044c0c40106010000c0035010000c4002c4503441e981e29801080d081100c45800120340b400000920110111190802c6000d01004580e181c0c86001046444202403005196400c22101114190b000e40c80008200c14031462600b00c400700360b80100d18564a9084113010f5402068142038083c0c1c6510741100140c1d5a50703840b00449 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 97803120 1250 97801870 97801889
    0x3121c0207061b0311030604020307020f1f18020d0b060604091a10030e0a141f0e0d08100510030e0f0a03080a0608060f060127050102060109021204030c02060c07 71
    0x36800300301042c410021120703116042c0f602e0030a010178210503a40580f6848501200c00580f20354800c0720982c28a541001d42d0ba12074011140b01c0c0d49a242014462240d501c10080304110085200601e00c07140f140001000c0e6011000a50100025002e00032995100c100903201b241003554502c00c41c07041c5c4a4403039156002c041e001e50340c1d4800f410010400d50030b250441c41d080c00444020425242c94480154003d00b0214101314030004c1035800704131501d062544070345813960321030b000d0340c8510080c0808090040540208641030384850300c1362449501584c48605040242803a02c0e04008a004440030500281500d4181c0c0200400051045910408030000540855070962070001c20320f9400521083c2e4043ca01001030044810000b206907000d100c1201a58442c0c40e03100040e01c1f141c12512200e0410b500e40540110081300d00560342003221001e070221260790b6201e611744d5050b4011b00038140792070031341d00c8006000300e031081f40e0941000c3e0003e404913203040079450025013000c0494100c1c035a403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 97804370 1250 97803120 97803131
    0x4020a051003020c161805090c0d05100612080307180b0d02030601020709060807050d11030303070c060f0c080606090a03060509070501090f060c02060d060e010e04061a03121c020706 80
    0x40a00600072030780c1c0c50802c10b940c04655410200117818400907804040030346c0d0350b5180010015901007002001c04200208131b00e0141031946012a43c54407000410303003643d0705001d000203001e80e0542c080c940c0b8a0340010700604680c0d81440403150b807182c0a4141041107042480092525060b10090010620b08040560360303150100019240131200e5000d0101140f41030380c2001600c1010403c90140c0301c045622484820f800e04001c7c0720020451070450385070200205024100d508049807030012442020148800143c2c0c07540c0c1c1c001c540302c0440d000049010000050780c035150190082918500003001c00000507100e440348421500226810140c40c2e002c40f00501883d0307000200c40300244100300700802c200d4188517000b8904241840000e004042c003184032010350f0390980000001c1c001c40f080e030414540e582c2c42c2d1b0450124040c1c5003078691528000c054066003910b000f0b140405080a0011310081c411075001803142d074400d0b1480b500c6480000052800794240e03000501c102030080c07401080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 97805620 1250 97804370 97804387
    0x10b0a09120c0611070803041502010b180402011209020a0e0c070f06060501020708060118020306060d090803180c03060c0d02070f05100e071a0901090810060e07020102040b070b04020a05100302 85
    0x2030441120403480c85c1d4403c042c1004a040c0000881c2c054415a0301c1250030f940041005902608031300d4a4654400300408214124641e40c0324010710950003680c4200c2c24900d000e458804840398090007079003080310180140001c2081800c09500b0400d009402d6280914540b15030840c954100710454035162030b004200705569040200341c029004000c040c1c2081e500d80340c042c0901240c0c071041c1a000e5500480080d903680d031181d040d1260400c40c1c0300c0c1804800064909003c00c0d038003c48130406400c1d807000500c0001080058014075a0b2800750003031038544c41d407100b4003402d030b0460030b422b414464081280800040394102c1d1074040074400d0004000e000344601501c0700392110000d0306025648141003c2140740d4404184001c2c02c4400031140395640012001203036509096003101406204034426012400c016501001c1240c903540e09403a60740d100c8070b82c228280d1049100d02d140882d01840034801044001111680141c4024008400ca544c0c0d50007088021070103241900119502003805075 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 97806870 1250 97805620 97805627
    0x240e1005120d020d051c090f02030307050c0343090c05090f010809060c0708040e1501030c08060a05061602030708060717040308040b0405010609020d1e050f010b0a09120c06 76
    0x201403105900b80a41402c92298082c1c255000c50300c00390005a40740c0031f845090102d00031118421030b03005015207580f0506801e040e9074440003980345900074402d10404804040c65010404641c00b100202d050030180e1602c040c44010743e020840340c5070900c00c0c40000038901200d00c80c00c0010003c41d01c5240c2c491010302c0401c440000405d60311814060408100035506001050b4550f22524020b446501d4450310700f001c825038021b642019051448103000c1c40303000c141c0c3c0240d80b841104240e83c02c0c0041142403004480560340ac0e0740103504802d07444420b014928003400034010850980002d540c07004101d4000a141854650000116800c0041803200e131310782c0203502e0003651707181c0d003d600a9410543d07801000e280000f040074212036141400304040203401e4105000500032102d095450f103154254101c002c048203030368140717201e03080180c01c0e000e84d070207004040c0719036201000c550450380b0301000c400d2664000081c9800b0002e40950200d003660038400e000f600e25001d451b0402e00d442c2400d1028 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 97808120 1250 97806870 97806883
    0xa020c01120603080f070f050a24060e130204090c090203040c14060f0309011401080c1009120f03090803040e011401030207020f10020a02030a060c03240e1005120d02 73
    0x2100604008043c0082a0050112801001d45102d0603903502600e05000312070044281000b001c2c2e0189145c00c00520160314900003203401510200442444100d5000c012510b00d48901c12100c156000000d48450020340040350880c000b61002c1034151543da650844542503411007030803150f011003071000740510070300044090404d40c07140d000b040b10341100048a601900a80c0d41032440b00000140030000f0a4000705506802400303094002d58695040c15103948140c030702140a20400003c2c2400340e44104d0210f822640e00031500300d078141c0f1316154600740200120b002c0e0140190004009403014040000b48010021140544010b5040002c101400c04140e40194100b500504c5000c002d682c8c2c080181359802000c4840c0410915282005e0f4140042141d0280d030600a040180c002d00429410008410000d9941000380075828008198283d03040020304100d0356840c941840003a40002c0900e40000140303c500c44050317690000107038554114200790540f500140044a8410b8040090 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 97809370 1250 97808120 97808147
    0x20c01050705030301090504060b03010e0a0b09010b011710030c140301060603090206090906032802040605010201110703080a0b040609020702030706020705130b120f030406090f0e18010b03030a020c01 88
    0x39141803a01e45a49980780818000c120708a680e54000c202000b0300d075485a1111076001d8004e22a4803038000700240c07030b0313020f1301c00070707240c0010501c000f4800941c18402e141e44200161a051610070f110024603441304001800c184003000c180401001148070f81520600074400c4004c44080d012078031085c90b0950301c0b660f000f00c0516003801404401a9181421350ba88440141c4003842c0c0360b658800028a0400b114021400c0048e140424031541d483e00d17038031011054001c0d2000d006407540d8000490807613810201076503081e4824031020002a204d205280d8008910b00000302d85242c03c50f002070108d40142d0301c001c14040d03000074070408604061210b100144003c3c005000c00d5454007001c900d0300e101455101100a0b615498058540c4d40c400003910049400c2d0222400c07162403162013962940a0701840001c20703950030b40043c0c0c12028480c0b1005451002c05880c0c03058659408245026a0022101c1e2240d521100345064a8078200003074044c104182d40103001885900d0000350400c1d207600c00c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 97810620 1250 97809370 97809377
    0x90b061b1f050c0406082a0703200a08070602070c0e07120c140c0106080307030513090915090203010b0904060614040b1011150f0f01050301020325090905040b07020c01 74
    0x4208003864002c055070b00712045403c0c600c5035962500054030010106d80c0240c075052440d87c14030140c04d84000c01505c403403442a02c4810075076080e007003010103a2151860092040c1c0c03101d20b00300001000180904003a0b4030070603000d4240406a42d49000040d03a5030801d6080c2c42e0120104180158400c0114600b0503045004100441d0640c100404405081c80407000401c400900110090380c00d50010005110140a8030340740d00491070000c0c4181d111010070725018080340300105079a8000d02ca5110303c55808a280d012a0341400d480380c01811103214203a0303042d542ca40280555071134807845244918400c00d800111103040c80507070b47c405150381941a0086260025240f43d84e1690f582c03065102240d418040710540320504114a00916030700440081d00c524400e02c041d0a2492080c81e02a07020200d1103010b46c0c2e01c510605080b03000403200c50551074108516800d813081116031400c2148250718244200b02e858545110581d03e0998003121110440c03001c100680307605000d10801d0100919 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 97811870 1250 97810620 97810631
    0x303020307020418020a0501050a051e2805030406050c0909090c03010e0a050c0d080f040308130504020f0d0506120102130e06010903020109030b0a020d06080307051b0a090b061b1f 79
    0x10041b903817940090051505001d000124180e82e580148199101565107040011030843c64181c044032940140d031050700b0801e0364200c0f8413490369005184c090100c025030f41e0142583d0300c079110140605005002641e090340c0c2000080c285071241c41030716114810000c0205080714540040c0341c02c4406501c108801900200546000a0070115003010203400c101e41c1c0200d422a030b400e02008030300c070740054112803041c0050000700b0070100c1b0300542804c030b0301540000203c6540303009100a174032800003411120031041040c4030321581507a008a400200141407812002078110205003240d02c584960340e1200350504040040c8242e154043d40d0065003072030107203200307495640060010741c000e010040c000880c440002e9a0b403200359060305c404490a440a11203d55a001c481d600e95020800a80e010f0007210b03100312020362200005000d58030041c201e1807031286000c090000411014140c0c0f54000300400c240707800c4032280030440e0b05590513040500b84043d85130342105102c48034114280825420034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 97813120 1250 97811870 97811873
    0xb010e0709031709030105040b07030501061409010c1a0c090a050f10120908190f0309110105070206041806081902010909091b03111207050a05010c08130303020307020418 75
    0x7000c00c8a510803000c0400c01c00800c0080c10070701138803030400c0c3c042d841d050030401400f0207601030314082e40c41520100002e0362985801c44d209101c007040c122210100300700d50911544141202c0c11000d01822140c58146142021014850803c0c3d4124010360380100c0c541c0981c1c41e03c24114801070000700da42c4e000034403a0b200455288941d80c44400c040c403c0c08010415034030095040b416007c0e40c080050b0355a4240b402d4206441042c805243d0006045000c00d55030303581c040d00c6070740d0001d900040d007110007202200044680741d002c240e049800c09014000010300c540d01c40b0030714400c4006c5110200c0e64909225010746840803004e51319200c514034000c2040540d801503800e07002e841084901040b1a03109041201c032081c1c015004130b20200000200205122032035078105480074003202c0d0b02191880e0708401d1a9510001c1c00707200d07440642c50004028a41c007070079200b001c7c1481244100c0c28030300345050050f2302c5d008981c01034001d03800000c4c49600710b00d024415502065069030402a034899607 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 97814370 1250 97813120 97813127
    0x3090d03020c10090512030108060708011203020705330c060609010303080610091206050603010c0212040b0a0219110a050a030803070c020102030c01020c0c09061008070e0402070b090a0b010e07 85
    0x60b80c2407520155613034103154050100601c01d1881552500c00030740e80d01c0d6925081c49558000803500707400010a40300010481048600313100441c0e540640c000e002003428002000040d1040c41c00313005001c0a0300004100184c2d4103040f403203c0c114180354164443c1c1140501743d041140083c6514400c90f0038800500001e5048810243c00000036559099204450b03a429911480303d03401000d542d518a0180d00200000c5410941c40382c4000d60090060303412441081c0d80d242c81c0080c0044a2050902040c01103070b1010000e0725913400d240c4100c500912800c071090f0711641000c0010b842a21400e8069140d500341014100010a4143c030101d00080c9140c403107800600010304440d082103840e8800c8000c1d603200b04166180100c150380210340c0c403001c40203030760790b107019000195024900d4a00002c14601e449101908060080d8462812035540e004045440080400c409684158203200d024007282d6055060b9203d80440d400405000e0683e0030925481c00059014500d039940d11030400401552 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 97815620 1250 97814370 97814383
    0x905030604030c020105070209040807060b0406230307030206040803030405010b030316140c0a090c0e030d0507140a060f06060825121404060903110706080c07050a061103090d03020c 80
    0x2c040c90002c810b14103030700c0100c98502c950b13030003e0340c045985018401449614801062418840c4c44108200340c40e502c00c1c00b0903140148102042103644030a80d641400489518806c03070400242170741d044036145d03800138500d9000781c1c20140d00313a0301c084108420071a00340710b03e102e228000c81c0114101044039425040b91810010f004000c40d01c0c03010780041040f000c0040c8440400300824208006494400c128010003510035030400040041450883c94200856075901d030b0349a543d10a86811100c0d244c1c52072110146802280711b100314910000401c2d020311450348882e00c030420100d001c81c81c04000030030188014102c1848282141d442c611050250000c410400d8010702b03101500030305003040640140f8150202c0c1075200901c40400003040199400f11805a00c0703034540312404010104010358402044c0990350210380354002040704d02d0700170300152425610400c21900e200c2840d079290001d4810300310780e8400e600c1c404001e21030003000511458a8440079072a04600707050f1601400c41e41c0d0391 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 97816870 1250 97815620 97815623
    0x8070503030301150e0a150f0309020a091104030501020309010603030807170a0f0b03030d0605091b160602090d0303090c170c06130806040b010603110306030307230f0a0507060905030604 82
    0x40c06110504c40440c021201140c442000070072196000c1d075140d14010041050135007000000d0340d00e071010000ca074003078851406c0311500a804c603166941018040401000e80c00036141048009000010002e40b00340011841640715030008100203155180c003a00903c0302070b0203142400481100301d03c8103140c11071029401760b402c00c00410041103031155440200b001648040e0540800540401003107840d400c40000c40300180e0f14000c0503903480006494401d040c4075030803001c403030810928402001304005801c0e801d002c0c010040c5064000c50001351103024400040300820380f146004820f124202901c0300013480c514480401d04074450038007a880e11402185684202008a4089103921078490300102400e4103e085540c00d05043c1000c00c0c0c4180c003449181c0009080c502c2c810030004a02090301e02880300a4000c42c140889a41d50324030200c1140600303072082d2040f0070301c2c5094090400075101c1c03a00703c240152405040c0ca0034114104025034000c0401d200b0303840b10400c0f031514000350742644079 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 97818120 1250 97816870 97816889
    0x120a1706090c03041101181e06030203060a0902030c0d0504110907030c02070303110f0703032304050105090d02010e10090315050906070804080d1407021c0203030a0905030714010903080108070503030301 89
    0x2c401702001621045000b98220007004c010784008038017000c1d00c640b001c440d96545100405950341d284811000d9200c03c645075a0009408481007110001c030b5000703141c010f9460000907007001480805501103e41c111420740d50030080c0d4071007103114280240580c2d04800e50303150501000c0116440a1b40e1441c0c148002001c0007610070054000000520418003458100c00554000a41d2170500801580031013000c10041162680c072a60f41c0d403488012903040718410385030f45051240110411502e07080e00360059050007844e04040c80141da035110428021070094440c402c0307072070440c02e00e012124910043c0708034640c0740005022a21070000b4804d03920402503d03140d50966102c2c64151040d0042c510202c100509100e03140d0900c1d0314800002b44102c00b250308503403c04011480c042d40700c0c210f81941001680007000495080d000784c1d040801182d0284e4100c0c0e00c1c007622a41c0782c509a069078120852565950040481010f9001c0e40d071a0040280790020a4800d0502c400a62a4481072040c40d405 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 97819370 1250 97818120 97818143
    0x308070306061b02060c01150e01140d0303050c0705010e010e010b060301030f0b190603050106030b0903120c090f0a030c09151503050a06030b0906060411181002120a1706090c0304 79
    0x210740d15170003112960101c12000b8080206d040300c0c21007050700719019050318280010000b05044a5280c401803000400070301910f2500d00b6520103900426015100140105c410022240464000d001c0e100002030030000019451000340012402c60724140c1000c0d224140c104010000f0840ba40d440210340703500056503400b5500c0b101a00c1600c124400348405c0d00c141031400c00400c0c80b00c19400b54003120b0140d80209420358440b044d0b16207910441c0c801450000340d18000c00c0505075190701801074000042c0807941108004000107201f20f00c1c5500c101c5014010789001c0c0070400050081d41180c04221442900c000d08184c1c0300c418140b814040311040503034940000d14040e0140e044400214ac008034940707242c0c1000301c0c6050300c40c0412515540124244500b184240300a8801c40344c0e401c2d4003410a000400c803180c2000050300c4411040e504610540321900c2c0070842c02d90007044090135584404d0380803c2d00706c00b00741e000d400c0100f826108465080402101c20810b4007125441030344400282c44 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 97820620 1250 97819370 97819373
    0x2130203070504050a09090201080a0b0108040f050c041508070801020702100e210604030e01090f0e250c03020f06010b041202191e050913030f0201110a0c0308070306061b 75
    0x1400d010729404107905c0107400400140041c49940403c04050007a0380b0241e5950f203401e10102502d0300038030300e81e0028841c10300040103c0e0703a90f80b103103500c0e0317204d13509990030040c00c40700080a841c8003411104d44001368000030001d88200b003007002e0040100c00c00940c109612070f00000d42007441c4825490070303c0040140c03000d690f40e902411042c40f090300c5803501c0c124035207491056901d2000701c404401040c03906800019941c081c00c8800100c81941d41070801d41414401c008a007001d014002c04007158012181c00c80514042c0013140180940e41d03503e440c44d03009400e000b031038150b2401601005800840062210351001407c40d000d48040e0341034084220060700c045440214948041c51664418032804a0a48140603402810307074455a4041b005a0b00c502c2001070216058407942c640407542514400000c1c000d417202c4002018900002031070b280c401214001c80e5105a180c41d0000e03282071820010580c102000b503400071000d10b01040300300c0c1002c101a0104030300d91400700300310021800260 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 97821870 1250 97820620 97820627
    0x150c071e1e0f0b0702030d0c05060c07030e040212060312040e010b0703210518010b032e0608060601090b0901020604021c150204080c01020318010f0903020d031d0d0213020307 77
    0x2400c0c01c0035100b100b20b9884940902d0790300701102c120310900a030640450618071442041d0034840d0000080e019503203410141c40c11581c0108011402e0110b0b400c4403500c10ba036188090034912207412003590712850044d040500f88016040c4220341010140024020a07206047e82d506550094000301d51b141001e0034291038104422a03119a481130b94420301317000b60104d411560042d807040c03194180c0c00800c90045030995800c264190340581c440382d00c0c4103040300700a680300c0196103d50101e504041800241c0340648660703800c204801d902c4030f01442410750384000d0f890010b0003400e11940c204560000000d480d00e502400c041d201d1080e605c16020030308440418040145d5201d14400740ca901e203040800007a4110344a4011140500600a403107540080111154030714204011044442c01100644448040340460003c0145200e070200050f190b02031ba507682103009071200c10200b4110121084103c07201d2003128000d80c0c0d08980310005841d1548200b00701092540302603140e80d08c161044 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 97823120 1250 97821870 97821929
    0x91a07060c030f0b041109041d030d050f0f01210311010c110c0f060409020c0a0210080609060a06050a0507150516020c0904030905040902030c150c071e 67
    0x40c00003071a1000101005030580d0100140c0c5520a4003400440300c100c00700320454540c0e400c1074680c404200000310403890203500c040321050081e242c036042c1ba01400c00c1d9514681010340001000c55455041c8210420f40c5079009a00800e8603060110070360501c20900c0c4500803600360b405807c004c10314110f0416000d000040e481880070002048102d440010003803900442d0118003034a070080c181c04140710704141c103e20300307d04e0f40074000034501480c0200d264020b41c40240071329198000c0554ad440107a82c2c1880da08000c1d01c4030b0303803010000e0600c50704002d5056000340c11030f4840c5201c95070030403101341c11400f40c030a81d801c2c80c14120348074000350070080400400c03211b00b070790010b151a04000c024000a0340421a403082c030360032507641c44814000c0c08841c21007501c020340429140507040100c3c2c5040d412164915101134160b402c05140d00c408030f608411514500105c0303050100340c0c1c000010b800c000000c004c001c2040d2202c801d6034035801c0c200400c003140c06020549401c6900e1333031103480420041c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 97824370 1250 97823120 97823123
    0x40f060507090303090504020c030306010f0201140a0902011814010c0507030c0b030f0708091009030201020d050c030a0c0e0d02270108010c140c070b1305130501030203011407091a07 80
    0x60016140410707009200b00d0840c0402c80c086a5541c40c04200d0b400d20784203031099071210300300131860b50301d0300e80c015251518181c140101315900c40c00c900d45500c40c180c9045010b40d51040e030104007001640300161005c4140980044100304404040041411424800001803401e0030200c0c44586a802c207107042440750380000c1c1c0310000301c4900150180c0c5030341c0114818081100011215150350600b114441d200f9505444594009500c4104280300307584040c039050310034000149032040d1035a0003002c1d608112000f0010304c50100c10404001764500031220000c1551810b42d4a05000c80006001009100d81c00703030007012020320740403101c04052000c8038180d02c0244880415030355550080e01034025108124001020001c00d43c801c1e45400d41580c46041440000d040d0141c20030700c14502c142c00c40d2071110004c1c980c0d900700240d280c0701c82c0081c1c0d02004004070701084560440c010701d800e51300e03c030b503c0350f80d00e03003c2c1420000007641c009121002d954550b410030703c07480140415520070307008a050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 97825620 1250 97824370 97824383
    0x5060403271403011107050c01121409010b0a050d15150806040b041b0b090103050a111308010e071d04020f12060a05060a0501050708030a02160c1e03080f03040f 71
    0x210390400300d28426003020b0400c0300240004c8030540c910344228010b00d840184a0b521003000702840b50f0151104d8840320711a588001404802a810b081806d6000d80b40007007107940d0b400d03d249090401e408118080d20003962255414074440e95100408010120214038283d0307207540c00090000b500c4205001043c3c5441290b04504080c101402031039025641147d41d01c00c0b800c40110700e4844000c062040f95280307807149060400200055020382001410304203003a584074004c42c4101800c00c081c0040c45690400e64031424241041182114200c4110b44090b5221020070032a42c00c4402064030240c003070700701c4102c041d26a0710120700c040c1da100e10215070000c01040b070800c3c448000a0020f01c556030b81e1409200b280c58203024000d801d0304d28029580000c07010031295001c28490340046800041c0c59200616210f6407140004040c1d162200403142d07038025210420041250b10542000c4d4000e81c2c00c581d0300c10785982e8400d00c8511481c80c01c9545004088002000e0150203600711000703d40104 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 97826870 1250 97825620 97825697
    0x1404090203070617160e040903020c03160815010f0b071e030512060117060d050f030f030405060c04060e0907030f0e0709060b0705060105040b06071b0e0a0905060403 73
    0xd00303080920200080e104a200e400500303a80d40c61170076510a61450345910122510f00c400b80009031843c0b942c10350951159405104064400700022200b04d90241c200212041c1400c80c0c1504204861003071501803500c0c0e00040c88009641a06541207901200c0d00940c1c9020900d4584074400181c0209101d00780c602c00d0000038181c12100070a502c1c1d0300d07100490340f0783d611500155180b480100c1c12035898113000c40011580c0c02c1c80c00010207028018011900e0f800000c801240c135650129a80d000c90f40e04c0071041c081003081c2003000e40e801101c03079403015050a0420100070070190191507000c0c4a800b121020035007141c0294812460b003003104809200007160f9404051f503811451092548841c900880024040296402e41c0c5915511601501059103000100405091800d0080d607000004001035400212000d15502003c0030b192140300c6243e250110302e41040000034030f0503400d2820203060200040d070119815038000d40c0341c149100d0703c000b003c01c0d07860009a4416229203070441c0c01c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 97828120 1250 97826870 97826879
    0xc05010c031a03060f07051b060103050f0706110d030504060f0e07030201120605150a020c09090601030507050a081e03160503180604151407120309020f01020d0207140409020307 78
    0x160066070a04841d86000c42d035200d0b860091690301e400403200000d0702c41e02c81c8080b60242c1d02c43c500034140900c1c109291011028104249418064203900c1241c2d01d13405803a4403035210106120940003814142800000c240103440d025403118011034414082558410004003009810380c010a100d0001c00780c00c03c60048100d43ca1542c030090750200b0380c0840c3c101c0414207144465800f90405940001c1d100d00360030301c002c111170f4407181c00400304081580103040f1400665240c0c1c5c0383c1c262151409074014400d0354514200503080ca038542d0402e134003400700c088045c0100d41c0009050300783c00d00660f42003011208014403540c10b60241c03c512207052003011142d0003d11070300001401c00590041c030001e8007000d00c1402c00689110328411080c040d00d8200300198a1800b07418600490164421031920304500b982d070340c0c03440025481200021980e1000d9540c1982026072041e8a00310003800204181240c40c500030b9596501886481000180b420100447d03484942102070055805030840f21502e466 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 97829370 1250 97828120 97828127
    0x801030f08120115080f09030d1104030812010905010b040b03070f02070308030a021810020d050c070e0103060e01140c0301050f0109050d0503190e01050306060304060e060a020c0d08040b0112030c05010c 89
    0x241c0b1030a00000b1004c0e030100b101c64103001b001a00400c0420015460985643c40b00b0000c0c01000301c8520b481e00c001d0000201160580000340508107584088410560424075010704440041c0c015441d005024071003030200c0c89001c1e0440350070002d01c0c140341d003030444c0c498012440c110650700000c01446005c01031000c600025000382001015a080c04040e441d01e040034450015040d021120040e40903c800300202c500450003001515040424ac0d2045070b203400004ca54514213030b104907805540da40c44551030002c20720492000f1821200403000781e045c00c081c80382260106000302d502c240c414a4100c1c925038040d201c0c0000401014105100e5641e082c14010784a80040040c000a035802c520300615080c801c0f0300c20302c034461050b1660750554032510240031035074000500488826558161080c003034801003080c188540500c0c44056aa9a02c204a09060955054080c400d02561505000c000360030080c1a605503400740c0c603005c1624089080486080000002c083c1055180c074000c041e10036030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 97830620 1250 97829370 97829399
    0xc0203030910020d020709052214030c0a1203020a090e070207240806030303040f06020d0e0318041a09040209070309020901090903080105220c02030408030c030904060906060801030f081201 83
    0x71035025a06c0e0f00d40e0314842e290a59000705c0391103c00c0701c004005030301d243c20b024480542c0d0300c0c005d81d1010108004c0403546850340c2d000e149807110036445440c40008012a0000f182d840500c18a01503041c201e0b140300190801009004160104001c0c1d8002119240f0070010b00000740a6030668181d2102d001d05212008044d011074000000c503c10700041c224100042141d00480c1c1c00f554100400051340ca880000f50017101c0c0f01e400140d2030301c010141c42c90b001c00c0034040405810042c03c002c0c0d00c9100c00c0200321404120320a0007900d6244141d0180c1d5202c01105500c03d80664201d80305586140c400c17001081c2d0b0380f00007948000c201d000410411138a81c0700c403000324466110b4100c5a6290030400c0100c52a51100e10386004a101c1200e007a5210f6421410300010300d801203034142034648040038255001b0b4514104076500220741d500580c501401010020301160904001d0076082000c014030040050201500f90f10041d4140010011240704862000c0000043c14582e941c54044d140708451 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 97831870 1250 97830620 97830643
    0x902030c0103060e040f030c0b0106050a0e030609030a031e0e0304140d1110020f06090c04051b09010f0c020405070801090f0501081b0102010204170d09080610060c020303091002 78
    0x4501503003040e45500034401c0c0c2d0190f0746222079907110340d42c480d5201140c04801d900103d0800c8030014948000584014201d4040c003003036210346440b00c4010bc0010481c51030800841d100b50300c29014440c901300d0110450308403040e6840d01060401d1007a8071959003d0503284202c0e41325190003100300d4400b40120107070080e03582900c4111140b40c000010001c64960210b00980781c0300002d92164107502e4400c03a2403082c0c4da13150050b030754803900c4c4400d110704049040b511a1150781080c8134420003071070315100c0c280e408130841d0380345807808011080d220900e0242c444010f048c000d00e4400569250301072808100d10650082007032107285007010005090513400e20904c0c80042c10018501204400390040c1e42c161400d1000030300d511484041640544910325111606556080001103007500c00c900c42a540110720300c0007024844401c402c005c00c100d8065104079182c1e0045000d000911841c2c50300c0208566481c5000804d1561a000090442c416065400e91080710841d521507900e4000c5001e06805 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 97833120 1250 97831870 97831873
    0x7060e030a05130803030403170712090b15180c03060a090e03121e04080a1407060903090e010f050103090809040c020138040c030b030609060f0106050c0a121e03090203 74
    0x2190b440d844142e45e0b001c10360380140070401c100722020740107a507070341c2003940b1000c10314042d82d0500d00200410221440c00c441920722507460f5082003a10780c0b04c1d040c5902d801805491001e05c6203c0c1c140c072801140303406000200e04103000000318000f541c401d00040090154040100302143c421148aa62644400a002d600c10074450005507421041c0180b9440c80c9a00b0700c2c100e50603591503a070174107181c5c001c44080c0d0a2044030720000c0c1c0000b40e04130140008501c0b95200203108a03041c140075007200705a40c000300c92124881c0044c8150040c1c060000c0481d64282004600122540741c0301c4d1183c0138491544d038010b0b01d030805400078164150410b400861981d070a510a01840c0e4000c6540101849062000e10f0026400c2034900e0500c1da102c011002c5003840c0001e190b80042000908001050781e261050b03030712103001d011200c0c5c200b43d09980101101d003400c074a042401c0c8581a2280c00300c5001506800a103041584524001d0304501129556004010040390038107001174001d002c0c14400780d019 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 97834370 1250 97833120 97833157
    0xa150614040605030c0d0201230702040f020901050d0e0a021e0405010920070f17030702010b0405010f030f03090b040801090507080705010c080d0b27090d1407060e030a05 75
    0x609162240c2d00a441d03003d005010351410300804c4c082c501144010881c1001800e1000320000f6166801c0708a9004513a0380301c40c0c1e90b001e180108000d4680c05a0110308861040010b0802a1703004000c89166042502010a08000c403215031814040f0854020390010f20010300c4107480e40040007000450f6008a0782002240d0301c070314030001102d000c00802000d80074008607000d0403182c1700001d843e180f8881c620034540300b6015078406080d214030316000c1c201d800c40402030107206a020301569207444026142009158504000c08101660901c4047e00e595610004441414850072044001e0b02000391460b40e00c07a5642079040c02000c1c10041501d40c0d000d0804040307080c41003c51114110381c1c05039240e01d00b03940303e52100c0d50598000c40704079110965881d105145034a0b1000d0100404804140d4940300d1144030440c1000170070001d1040c44107030460608068095000441980c0b20781003140020348030350441c94100c000302000e1714100030703600c40468060401d40c0c2c080000e00385d20643c590b00004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 97835620 1250 97834370 97834409
    0xd05030f13020928020714120309030f0702010302070501050906010f060201020c0705010503070c050604030e130912030c02010914030a180b0a03020928141509040506030a1506 77
    0x141920910710080d441524203000c1503070700c4621040344028504491031100c0030f2410080b641e040381d000c0d000850f240340e11480c1c0102440014040711000c1e0102003003403861803816464594a911900329041500740000c1707a0390056920907816510180d5000300200035505084164642d51703a0240320f00b8602d52100000407a6491040c0240c03005802404c000f0030704d55003800010369031078200074503080c100302041b0704800216504000260182c2e01079120050a07401c00e10900500301498114880c9060520110340001008446034881d20003031840e0001e203050380e205c000ca000d0483c402028001c5e481c440062074000002000030115070841c0e032a1241c11000900300c0b040412503034400c0b0f030303d0740b5000d02803c14000d000e03800500c0107540041c42c1c500c0c02c10380040030f010110500c81106500d5800101c09000d104080490981c03e244100c4980350300c045a500d4551291207015031180c0240d0702c0b40082000d5440070015204040d034010070780c40c850380812203448014612881400282c00486504070b1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 97836870 1250 97835620 97835641
    0xf2304090b1504020906120c0c0a06020901020709060b0712120f05241005070c0312020109030e010504300f08030708070e0607021905091503160509010e09010b030d05030f 75
    0x989560020f00f04a087c02e00005038110300244c01020009507500030440442131820500003410b078288030702c40050315a0481000240740c01500c0d001860030728a410010301c09c82d8035002c25104850350215900f000e104080c0012615004400c9400a03658106803050000300b44640040d0710500421124184898002c038000c0c03e16003614041e20342007042641c2c03800501c0c0c03040005041071030007000140319179941c1c3c1e0b46104e03020075a4030b00480141d648002c074a04059000b10175034942042440c03c0c40c00c085c00d06000d0340b0000007000c50000360384d102190701401800071001d8055a141c1042d45075030a030100b81403502c52603204485a00000340c1a000141d286400f41186170030740c1c10042d120b41c0c1004030b0b507800d01441c1504d2004861140d108250b0025442d40c81120541c80b411840f10171103030703982d0400181031800303c0c002c0c030002803007803d180b003481a41c45500940b0304540e410041308040780c8488440a0042401010907038160040041d0140b203507401900035801104008184e2589690305c65103003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 97838120 1250 97836870 97836877
    0x11503110d03031803030506030c030a050d05160204020d06030b0f0c041403031b160902031323060403090f0501021902100e0603090a0515010f2304090b150402 70
    0x200600030056162420341011815014600d1007070500040140c1203040418207030f14a0b080c02c03800292134604208080c10240244001000140c00816420789580d642d13a03251000e0600000030410301007440b0030f03915801d030f45003241a900500304540d00d00c401c040d00c070040c05e102c5c0020780700c0d41c1d030000115643c4942c40211303600c038a00030025241890308154002505c0c18803500415410720040c0040e88050281c9902c0c2d0031094803800c005c140f030418040b01c01202c07080580c40f84003120b10600070420301c11000c6110400780380d8401a801141e0010b41005202103000016089040c42001d041008054000c80804191407045091982a075616401241c1c1c440082c0b004501d1100442071000c01030400814001130664282890300c00c0e0fa1940c808500541c01c226a002c455602122541c0107011041c020305020700492a030341095981080103c07242c240d0244501208804501c80242911202041d2420340b0500188103004144180c2132501c403a507416250401002e01448107071520303140034402c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 97839370 1250 97838120 97838123
    0xe0c0a020a0b0a0906020c0709110a0c020f2e170103020f0405060604053c01140309010f0903020d030b0405130f0510020f04090612020a03110d05071205011503 70
    0x2042808110341e0b40740000b020250111554a0300d13200508000f84460018007030404146000b0240d052608011106030707200c0c00c4080f000c03004100f1100500940c0840c41e283c10382d070150303482400350440030302242410202801c01e21a61aa00b0b40c02451441c41801400090b110390740c036101000c1011400f0303118407034280320003540203000104000a50410b0b42000c0e0b80322000070b0003c0d050a40d0741e03000c91150440d03803210140c0e9284501210340c4041d0404250310300718001e1100712681a0300c90002906c0e41c440f83e903540e6080341011000030703120300c02500303c900d000c84001018011058949000b030350f2105002c0c8003c1c042420a120001d840c00c041c42514490119508140d680b1401ea0702c40f240c00c1001d001d000c0e80d0a0003452021003000c4e120340010854207481d10900c965440c41d01e80041c00712c13041ca400c410941c460812000001da501d020200f0180d030741000701c100300040b0400005015081c0d045004103580a50540020000c40d8403d000c28880e000303038000d1148071640c2c10401d104540310f000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 97840620 1250 97839370 97839373
    0x70303021608061608041109010b0403031101020306100c060b0a060f02100e0325021801030215040e04060228020601060f0e0303040b090a030b09061006030504120f050909040803010e0c0a02 83
    0x42c241941417150b4070385130300f143c01307609802c1818030030a003c1004010b09802c41b94103403500080c10410140d10401004039240594000c600710300700070000949002154204204000c1e401c2440ca0910806610100d415039004002a814031366601c0080d1400001c1c0341d64401500941c564018111040d00840401900f06006545031009100035006804014001840300200a210020068841c40f00d280000c400691083c1240d615600c1001801140c8038400510380c00b082c84104018040c200081744c20681c030034009030b141c44132040a054000942000d0251102109540b001c12035004038010781a07505683d0b80354090a40444241d070901c10400d107154155100300802c00082402c9005403e84a03802030009068039a43d0321000600c403000d41d00c80400790001c00a20048000d410000c03801001c290906002502d0241c59180e101d800d481036010030320000408613890140b00301c00b265141c10000b4210308090505090164440d00b09000303500303180403250085034031050760b502580d9a0503207650 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 97841726 1106 97840620 97840651
    0xa06030c05010c03051617190305010f0308030a020a05040f0b0a030501051008130606170a0b09030702280302060706050a0c030e0c15090307030302160806 68
    0xe112606210a90f0b40034000a0341020644c1c145503140340d12802c503000c00b03040010040004800f001d00009000070105042241c0e82840b188000c416941048940c0e240ca0b240c02e01c00703042e800040c021620510004001010540017800401c8003468010308140d5a141255802d603e40e40007030f10300f4103000c40c41c01c0015516201e400d00400007116441900d10f09164003404540c00500044c02880301600c82c1c0090100c0790704501c00420751120f0418a000f8001b503540d4891801c943d084031480c0c0c8031808a9541030780001035844043d0010700c1c510b00320035498404400c0c01e007800140124070410880001c00369039458060100c2c140240c00104041c1350201c1c04508646104852000389440c100304010118000a80c00da00342f8802c0e1042d03280030445418035071042c06102c02d0580d00d445440c9001c03040560200707441c502c6984c50703e0410034198030707038803001c1d203400007260203851078040311 = true := by decide +kernel

theorem cover : BRFrame.Cov 97661870 97841726 := by
  have h0 := BRFrame.cov_init 97661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 97661870 ≤ n) (h2 : n < 97841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
