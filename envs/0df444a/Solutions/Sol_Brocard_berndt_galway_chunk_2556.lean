-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2556
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:03:42.73116+00:00
-- url     : https://prove2.me/submissions/13a171e0-b60a-4809-9cc5-8927a1c61452

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 459532374 ≤ n < 459712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 459533624 1250 459532374 459532379
    0x300714010f0608210f0d0c0c05030d0906060e0603061602010207170c10060503060c0d0b060301030b0403080709210201020c10091d010b04150203210403080702010e0c19 74
    0x303108403151504080a250080d8214910a110382400c10382c10b0441310518520300581d10081c8800d91081c4502c1d02c003810b0300c2d090b940e45000c1c00340034103500554201086d40da80d411110b5036a0300402c60700070b0441d0340900d803001c046401c01c0c076007244a20960300640100869282ca0702e00640340c04441342c0880441d90204010000120070b89071050b000d1ba81d00c0300c11500d80e20304112150910400c201e081481078544401040280d4000440350b4009088201c4590741e0301a00c0304a1000d8504410700c6a000900000000100b042008849100c0ea02982c0c581e02c1648a5040846030391a0384d100d08000000303280c090200320100e0f401d462441d82d1050044502c83c45090000c180001c80000242000c2891054200302c15014017550103107003aa0041001450342c10000300b0205c0d40958090011070b041908600b124203802003049410605c2500201c1511aa02c50152511242d080313038218006038140c0f010030001c60050258240401c0d600001c1c02c8540b040905101d0030390404002105c071010710b807500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 459534874 1250 459533624 459533651
    0x91515080f030304124a0d05151009060803040302010215091506180a06060206060d08040905130c140f09070c0308060a0b1321020105040608040c0b0c30071401 70
    0x1d4100840c0c00044551b1880314400c1210491002400c0c0030702882416050b08005400231a0361003000550b07900030809a202d01c9030400b171a0746a41c000d807802c0c0c0c1c41d110000c00c04a8000018004480c403d03401c41d9042c80c040003e000d03542d6001d40d541c09061b80054100d07607064401e821516031080000e0000c454088150041000101041d20400e40590f59140c050081980c14410140d00200550784540071014980d6200e00e00d20461188981c000d40d1113002c2074030171040c405c44d8050950400b82c00c80a981e100d0003208104001c64020b10f104103030068414000b414404c0c941c07403003440c2c903480d00450405c1a032002e4038039400c020704181d8070203c210408582c146040019080703040c001c41550100900704010206d080460359450080031400413100d800503a404000c481c151902c901e070140040c0c40d40d140184d82c40030746400c141032003900820644103001c40040d040c40c3c100c03c3c1308400c958903610011b406490700c8a180f0f089c210000304124940114402c0c17010341103d21031050002819138031a140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 459536124 1250 459534874 459534947
    0x6093c0c0302070f06050a1a0a091e330f060807140406020a0507050d050705120115090c170114060f04080d08010305120301060f03091515080f03030412 67
    0x4c00c4604580d20b1043c0242c00d141c5104070843c407015007010700d903240b00040c00503502a41c18400c8048480d101e0b91940040c00065600070082c5208410038400d18041c002170140002240c1c40e42310700084401d22441208900020403000c41d580300155203c510f003000c40071203401000034414402d05c4058145141c2d8040c03828000c0c0f00500681d0f0103004075042918110b8106159a8000f5108020300261900842d00205480046810440b41031039075088059006001d008a1200035010a05000000400010940048070010380340e81d82d10450a174086445030541e0710078004d4886401210308401210b042c850020408041410b50381820142d032064aa49009406981c260001d00c0300001001001002c2000b000f6940c01042114150740c10842d00421800102100030b0030507403115442810f10a181c0d4130045020030302c400a1100c1004800700305004041e620410040c0d22501211110405c0c020065a0007030740d004100307607402c81110b0001c8603d031099644407840d1054400c0b4540702c5001070300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 459537374 1250 459536124 459536153
    0x4020114070330060e040c140d0501060b0d0f1a0f0a0512010204080f060702120d022512140f0f040b03040b0604050a05040f0312020d06093c0c030207 66
    0x428030541030401c12507507041e207105034801c1164128a401b4007000451072042881039402d6070142c682002003601c0011228600b5400c040e10551900202184041d40d0b400244400c6005003418054240b1100440301118003c902c0a12030045045e6003102074503001480b01071380000100f02803291504c138400501032900040d050985694006000c0101d11004c0c0300e04c0013101c8040016009130714096070301a40340c122089040c0c1c1b02020014a14035000c00030b606503015018010740c400380d441d40c8c80c00084138628860300150303548440e107880d40e0a203600ca0b9055101c00c154580b036144c02c0c20703a01e02080309140c00c0001c0100d581901030001150340d10f4550095440dc81c020003825103139042c000140030407200040c01c0c0d203403400c1c107050401012541124502056952515002410301e0f040700c4010020702604900c2841141003050000c0e440d901608150640b48400d5400400c0d194030034224808481d800041004014611064484000b03455102e44901d681c2801c0c094544070ba41c0d07860091800452 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 459538624 1250 459537374 459537437
    0xc0d06080c042d02030a021312050c0301150605070c03060c02031206030a0f0803090a14070f150f1107090c2109020306220c120b0f040201140703 64
    0x140105035480c606030090029219140c008160503003403078000f03003880340038404030110025000000300302801401d904403501503880c0d0484200140c0c80780d440540004008000ba6802c3c441c0040003406860180300d1a450340c52500946801246481003d039000c1e0000d14094070b200030391100002c08074005009403192911390354061680c8001c04011310140c044082d248501030740c4031181c0b11002a500c003100e0042c1a4000104507220f0780e03008101441c242d500301c8010b00100880d81200c40b40384000444109603012442035081c01511840d61010f40201840c541e000a0948080101c003a03000e403a4440c06801c4070b9041d184841d890340e81d80d509407800d4103410780006142e80b4001e0311070540d00c0380c11199070060301c8040c072520340300d070300069a1080f0241c218000488090107200c0c48000b10500714500b81c0d407100070555115900d030090303900349006000c00d83d00e4a01c110000340780800f928080d18442c0d5416111055440008140c1c4003042c0c00500c0c080f01402041180c200300c4034503400d1010f01c000003c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 459539874 1250 459538624 459538633
    0x50105070807081005030604032109030809011413020913081c06052d04020c060103060e010605010f02030a0c0305090409230a02010e040903050415030203011d0402180c0d0608 77
    0x200c540245101c4008291018004c8600301c144150754001c505e00d600a905490610741201d94503d000020700ca10a82c81c0c0303582450031486200300354005c07801610030031a4800030005450120b8040c1c40c1584200c400300c040c640c442c0c143c0d0b80140f401ca00c40c150010f0303103070602c1c0d4142c109540d181c02a0f41d101e424000c51401400301c5c0504040c1d040d004002c0074041c20b50341c000c480009419812648001754185a4110403688400011b03912164180e40c40507004004031b035070700e5959003001d000812400c3c503250b0f217650030030b000404da950081c04400400203450303004500d000e43c20401240c1900502d03000301c0c100a0104100003007950341e4000c400d00e481c061551480b10400c800c0390520910a188041c82c4140c0203030081d007000d40e801c2014100200c9094801091a044134a4201c40318030175170704043c00d010a58070440d459141d140d805507040c0c0e80b000442c81103105a482010304460310407500254481183c104e0311000c81c0500000d180c01650028200b420b01d4001d01c440d030706a0742260000080d9611 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 459541124 1250 459539874 459539881
    0x209070c0c0501170f04050118032d0212090a0302270901050105010203070219030816050c0603040b0a09140d052101060512100509040f12020610090c0c0501050708 72
    0x5114040700c000d14003402c05030900d00d100050481c07481c00081c6141c00c24489800080c060090a410403400384443c008081641c452610b00907102c421480e50039828907906216501d0340b5400c15482084044941d001003e81001070030342d651050381b10070043d80c7c011003031480001c0181c9415150081c03a848c104051341f80c0742030482c81d40c00300d40001490107040d42c0c1441e0040055903004001c8070700c40c81d010b0701c0000c0c3c04805901002e031a00010b6000806084c030002d00c0003d000d05614502ca4450f00c64015510144001010098079010990703002d084a081c04000c108080749a90101d0501441410a50300b01e0005203e6207003448031840814001c90000240442d0285640c10b6400b40108c0000244407103505115006005010300b001d941d041d00300030341c04640c900165130300a10060000070301d03500c082d140c1440c00c03008811414100301d88000070107118006090002c42c82921a4000054403a4141c1c40c140340800034200c0958210140415500c8400103c0e00c00e01031755114181c2d6403580710050a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 459542374 1250 459541124 459541133
    0x40e0105011d15070f1a06011409010e130e07090c020d030501030f020114041707050f03030a080a052706040309051c08030a02160c050306071106010b0d090209070c 72
    0x404000d41c940d01c0c1d001c0302044196a503100d01880384074260451026454640f14500f2650045d00301c5806440c1c01c8804051406500055030498400d80007a0307100c14031912880d6104645018885c02140030401030b450140d41c3d41000e80030307220030b50200c04003c1104085010940d0610b1515001040c4003521005540d1070f0640400240719081c0c41c928007041198034544902c10700461501c0c000f410006043c0b1519002c500b19820b840c0548400011020803030318070820161784025500c10103000ea100140c41030b03c580340100c00e0f41c40190342c503200c0283c19698440b801000b070a0040c0300007c0121805240403078501c100340d01d03202c40000d81d00282480c0c242030078003400c01c0b04a0362045200303088a4485101554004444d03c0d0040d40c41004152a0345941c02050b01a015524038104480342d030307104c807000b40034444400c1400c44205909403201034440150032616003641009000d0035900900041100381085802018403012504000481c0301c030a0b0300281c5080c80c00e41e1803100041c444d000750401e00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 459543624 1250 459542374 459542387
    0xb120a060324050105030f0c12071707060f050a020a240903050d06050a15030216080c03120114061803031b0601180219030c0c061d060a0b031911030102040e010501 72
    0x6081c100c008064102000503030540d11400e002c0d4940c0240d03141804272a80702801c000c4e081c080d210036030352540d001075140c1c400b50343c4004500c500000200324580b6040e0070384c040c0086451003211a409800b4222003500e548240050081000c42c201103e004443e903030071003038450340080318800c0d41e42941d41d03040701c0114401d0b25295040329100e144807120401502c2400c58240101000c9070401685503005201003940c000701c01c01c07000d018010b000440b1400b0581c0840148140503038801e80c030215980b1285c010103480c808101141d0010020084072044c0107108040e51100100101201c0c41c0001c03045c446000c00c8000c1c8a400400d40c0072800520010400020528028004450450802c40c0800c180002104581148070506584254206210348114562414250080d0040c40105007007400843c02c6204100ba64503540120408250010200d02502920640040003031000a820552640c030014036100f003103500d44601001010252404c3c00900014141c5681c9940150314010001d440b4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 459544874 1250 459543624 459543629
    0x1060e0117010f03240207140105070f050a03020f04080f0c1224060418081317120a1110092003060a1802030a21090b120a0603240501 59
    0x44501490040c00a41c203800c1d1100c0490343c00452011483c40d170484403030100c40e402058207500341d00015400c014400100805000010143e000300001c0c2da400504032040341c5403138409800030b2000c11001d40d4032842500a04580d0458420f0b41d0700c0e142d6560403180c98580d00c1e0b941d400407038020b0001c48001c1e20f803622540b001919220003502c0e038240540c2d41150360f0000c40380c04016182c000c0010030345944607a40131141a090100e00d407030b0343c240641040303a40350b0017100211840822441d0049800c072200d90550803021300d80d10040c441c1900f0315000907882c2e00600c40402c204034441000044160b0b04000360300c2e1003103400c40002040011410241040c01440000c04084440c104c203e011a460010b1151707800f00225800207213180e1111590b15a005500303102035450b10401d00c00809215082e10503142902c0300900d42c0b40030040d6200300756030310b450030f20651149640c280480b05070704280c420826030022500d0400198030341c41c1e540d08042c1224a22140d1642c40c210f0244074950364052181902 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 459546124 1250 459544874 459544907
    0x30b1c2d020607060b0301020706050103020f0a05010c0f0515070906030f11090919060f090f0507020312090307170d111905070c0308120702010c030b010e1002120301060e01 76
    0xd11a21010200d0411500000900034440042e21000b8400340f070703000c1079030501c1c003c00035581c4401505000380589000c0c00140e00c0b60b8100d40807030341d107450020240d004494068441000d8039101e5220614041c0c0ba51001ba43c5500640c196035200c00000c030501c601c942d0700c0e030701c8803415641003040040841e4501505404218070388040084a0301c4d8403001c1d202d10320011540c415407a42c442c01140a0001e100f03500ea458181041000300f03d103159014560700384d40740c2810070440c00c07058009203001d48800361100e0300940c1003004005004a0140e000c00c1d0b10600341070841c1e00d000740729940c1402e081070200c1c4032000c040c4003040c10303a900b110a0041ea031a100c501007540307007071511461150800043c1d00c0300c20410720400092440400c0300c20800c200007580c0100001307441d41080050090bd007141250100015440e2652841150b40284225841d00d041a901c5c0908000300d0030501156110b00d40d405019417080c3c082004441c42490025030103412280c0d1102d60120400c0000340600100c48480c40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 459547374 1250 459546124 459546173
    0x80d0c080f0c0a030f0219030b0d020d1e0803100e060f060d0b01030e010c02070e0a05040b06040f0905010626061608040212060405060709120c09020a030b1c 69
    0x181d903440c404101508a003880036116076860720f80009400825100d40101d58090010452009071540c0060b1140c2010003620b050244100c032804100d0020340b241c900035031240300c001801d408520101c40060405007415200e80c154440d90300e0320042c0390012039525003404250700050149140f4030814980001050b62000300b01003400b00050f07494000c4110712510359607600c40c50380b2207038030039004214240241c4001304500d0025000094030b070f800d280500fa803003901a03804200b075410320748200c0d803040e0381044a9561586590003044040d02056900030070290301c030340458022802c00c0c401e130702c0100032981c4105c10a050100e17036035079040034922042c1c10b9600300e83c0c100310750b50300000701c0340362000c26a20b03020046981d5840001c0150407403480c4182c180c46030200308001c1040008080b0b001d68281d032100306200e507680b400c0d52100d4146050003020b0603940c000c10016131804d90081d0840b2401c40c04c010408140f0341000c280029500f491010343d048600402805100c5e03100c0030150003209850640 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 459548624 1250 459547374 459547381
    0x914030a0f030c090308040807060f02121c02041815210204111e0405130216020d0611070305220e01030b1f06050c0f071404090507090603080d0c08 65
    0xa07000303078900814007080c552516010310b10b81d80b0415004004d0340d8803154107500c960b02c0e001c80c0e13a6500090700075a80031614a6410481150001500e10192095541402e2408181c01c8415050501803040106019024030002c04c800700c004100c50032401000400007a4003403a1742c0c0344d508050203907102294559400b0004022018040760407002c0e00e40603200818410100d500f01e4025104a20b07100e8911062000c801ca02caa0910740240200c80c000c50380c0b0000070051985000482c030400e400081c030ba20069240c0801400c03c4811410498040c83c40065400f811401d82c0b2025440b06c1022000100009400e136928983c0299041c042d005404401003224249003800c10303007940c180006403585801000048081c040503805510341803203103521138030a0340d58035809050398001c6a520740c0c4034040c5408d5080d441a001030188116912580c0040c2012002d00c180b0000f007015010030f5403123010b40c074404101e400003070044d040214030441c1c000355503070b440302001c0080760810700c0042d0802c0100000d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 459549874 1250 459548624 459548627
    0xa0209061e0903031306080619141311070204140103050607050304060207120e1309170903121204151e020a05070b0f06031002030f180703080301090914030a 69
    0x140e66080800205510107141040038184540c011603280652502c00012810743c2c118450b80f851007140d4017500c1b807030104e0f12142e0410154070300010040c10180320000701000340d00081c0d40030b460121400340004070b902e80d4107912101513860390140044d04445c00543d900442c2017a1040c5901da03141210301040550541e540c0d581c50b40c0700540000704000000c40800c0074451680d04880032140d021703001c0403004280200203007811000c811641c2c8a24451601ca400c000214000c44421aa00c5540b0b17107000f9400621642040e00011035440c0c251090501281585a40d20018104040c85020030541c42c6014030700688690031000424510a040c411034007424441b08100b081d00089000d000742e00c501504008a990b4050004041d1404180b40b0500c00ca20206070522401040c09405940d1b19000e00b8007848143d20090700c600c10f65848031000154000480f043c0d949140c5000c4054400381507036a01c4005058200ba00405080c2c0c0d5240040c8040020710740c841010a1101006141000801c000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 459551124 1250 459549874 459549877
    0x919020a060f090b040e01170303040201121d0f030d23240907030903030e07031e1410050702010b01090302060306011103090a08100e070b0d2301090c080a020906 71
    0x1407402440015011280d40394081c00100300640710081c01c458036151344041c00f0307482100c28483c000c9035407240044125004004801c0341c2c40b80da01a140c00117a80011600032001342416071451025540c40c91141c5050b10041c4504080700900c0d00085844228044074a403c8800d0080a091055290644105c2c240800c26060798440803540d400c42442d10302d4155600b08881e8800056405070040c010803100c1c1d5011303030100001c240030381d804010903205076000603601e40c41800f0107041000910724408100340c0311000c0a12036449040c5000c88107030700408161510300d0b1340d500002d00a40328000c21801507424070031030034001824a00740c104289143c001c03072034510014104a0400011460034070003d441002120340c2411302030568520641d0711214141c0310b1005180d0461058140190345480840c000348001c240c0d0003d05605141c01d81280c0010003c02180002c040d42140901e8118902a11034480da0300070710084101144c19050041c00509140d4001c0602c0d401d02c0c414890002e244e1030307840 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 459552374 1250 459551124 459551129
    0x303040303140310170609011a0a0504020d021620011404050f0f060a090f090504021513030b0c0405010f14160203010b03030d0b090703020c1005060d02090403080919020a 75
    0x60340c1c0b070302c070703c0954081c1c0308854002c074171008164403004280a10000b50103100d108990001c005000707440c40f0b01d10b0400a05044035902400c000020f00491a290703000703240580248200520b400d4004881c46100468102d007034603003030b000c2100700320300320150b110022150400346442d110f0301000b207480340207038083ea01a072400f070080c640140304180c030365851003201060004d00a9488201e200320080280c0d99500564415041c200000194220140540e03070040e80e0061000c1508005c052282055402c900c0e200160b074a515000080030590319400180254601c40c4000d80d0b0703609000001d4402c2c00449402010000074540f1201e058030712005940b01d958050f40f501800142d039000003409020203a0f00b4036070501000038080781001d0f880c5d1150100c400280c80b002c18680e1200000d404030300030311160000c44d42000c07840404d076520715030110364440703c01402c0c034641054580104a11070720849046002c6820901031000c241401c1141580c110107405104800d4181a404101400d0091 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 459553624 1250 459552374 459552407
    0x13150b0c1b0a061407050a0c09060504090503070206031e0c0912061302010e01030e01180201110715031e0c080406061517070504080f010605090f251b031205060303040303 75
    0xc924400c01d501c019000c4417001130b001402c41d0030310410b40c10041d142c0c10311481505036903880c0c0311001034a418140545c2d52800c2d00800510f061032050303000d000386a80018964400c440c0450000e20303070b8003652507401c1d004441038905d0940340d042c00ca051002c41c00300c0c0c1c0c011203440c0c0d00c40030800201010107021020301e95828a81510700020600c010780142014030207020882d403d241c0040221080f003044e10030a00d000340e8a407494005c0821030b640d155290307405100c140300c2c2207800c4001d010303003c2d4001d80c00c841000d1034400420f5140e0403485046901c3c5104c62000262000140018001c0300c0c021b9078040c240d500649a0140542100079101070591526804406e0101001a03400c1d8010300640f0300414028040e2034101040103a403a009100c02d000e2184250401004504c044035400c0200d841034110030b48032199540102202c42c0c0400242d007150303040010b80d41c080c140010002d084003041e903111303446850525500c0c10218040e40d8008119502a501c10701007080441c2c0d104003800341c0354120 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 459554874 1250 459553624 459553637
    0x140105040507051e0d021518180921040e0903090111010c050a0e1306080304090501061805010e24070b01050904020607031209050307081c1a13150b0c1b0a06 69
    0x1600c01f00300b00c6111803100d034070309800100e14403131001160001c84000180884030003460308203030703141645140816034084886902008402c40070000410000005a03840c124460500383c2d1480c0070010002c0c22115031040350070105000fa030f1940c0201c014600a451040240040c203403030000144070340908801402040340341140081d05450340c00428815201510301441000d807035a05413666588980315001d080ca180000014827188900d12f05a0103440114410034007526000045400281c5041d103607602c0071000420202c8108170025034000020352080340c90f203c000e40d04244641c41c0050f40150b00402d2001c04000c0169074640031070711441e900d4200800150090031010000b00602c040091030742c840041c180007030000a8028111404103403001c04020a288604a02560303590169250018151004014076182c41003028140315000b00c400030b00c0902c0c0800c5030482003c140d1040c1c21811001071224a42101404425075000200b10145910000f00020403180c001510440c0e0070040c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 459556124 1250 459554874 459554899
    0x1806010509061306030501062015091c0206070912050607051b01020a05090a0519030210050c011104090501051c060b010905091e01061418030a140105040507051e 71
    0x8445080c1c2d502e81114150f00003c994452501500030b01003800780d0404912240c41010080308d10070030b4401410400c0010f00603030780350303010121813461000d0084600c0f4020210b0114088803c03040b000c580840360ba009201e9403c2c6540b0240ca1070b032681c2c100060301248142c1c0b98000c1030300014810b42010092810507598130301e400c505581d004039140e6000c025400003d0f0100d080358408007600d90450101c030015002075507441000322101644203003610401c0d02031420805880e182c1201c29582d2030781d00380540341c038dd00240744030b007160100d114014064401040c14081013030103202d10340c050801620588504074100400014018420794024545500e813000d1000c141d100d502400010940981561600d08041e400c2c182d410244000480700c40380084000108603224403240c409074000700c41000e2a280d03402d605550004a032608481e00f61241c0703941d0f00d00090f054054228880c0c03030300000249a0800d40742003400c1803405d038401849520310903213001208808035000c28400d04200c0c0d2901900e034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 459557374 1250 459556124 459556129
    0x20d140f091003090c080a0b10150c0503090a120501142703040e01030609020906010f0c020d17030103031e050406210b0405090a112b08070c060f0e1806010509 70
    0x11102c4c001444086540c5c400206420300058580710f0910600c900d800c0c0f0390354000352021383c117050311075a00620201907505960502600010100500030320503070f4038120700340f0301181540400ba44080303100c031b00da40c0c07100042c020280b040100c0d142c901c01c0e5a4a035400c040d2401c101052903494171001d1402c081d4950152401c04000b190f0082020f51410222513a4a0508800824030904207a006007110701c00207081d0340c819480c1302c540c603206803200c608103000d980071b100f61800c10203001c60f8100c03402c0340390040b550202409075000314400d6aa034044c0b07032008800720103906601140c580038480244400d1007110b0304401030740d041d403905907411042100e40209140203460b642038000d81082c581402c0c42280c020100e5202c80326030064201e2400e043c0340c1420700c12100c15003274000c0e090500f501800c0703800808039501d0308141e90050022908112150321043c00d40e000d15486007011030541c0c40c040400d60780064030b84100c1c0b03c080fa03056006c0c421110200440c1500140000c0c10010000b9101680c0c3d03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 459558624 1250 459557374 459557381
    0x90f0d120608100c02010e0601030b0114120609010507110c090115020c0a03050d0906020303150d03020703150b010801080a0b28060801020409050c0712030902010e0907020d140f091003 81
    0x1d0060b541200c0c0d01c0c049442004000740b110700281d6005500700342410381918400540d19040381d5001c0300d000220380c41d0001000808145018075a4000c018120b4a01e103a00100b25290158124200004050403d04c601914030204c04403c102c0341e03004554110141d9481070103481c1141d005240110316081410403c80c1481e010b540c5550b4050001c0201200388200088c0041c402441e940356484240d454020a036980e01040b00d9980d09000d501c034a50320700741001c900d48911144240101c8034613503100d03900e01894a01c400d400c2407500d83d448950401a60f03000803000d00400c5160701801c490f0005440e10715401e640101a52120704000501c2001140c4c81c49100c60340c0b64026804004454407114600e01039402481840001410f1401007283c070005c400c2207802803035210f8962106aa5050320640c0a040f404400741c0c1480180d21801c03041d4cc545400e4540714068541c0a03040940040101038034a4440007261001c10304241300300c048450308881100e1004a0494620140404858044010b03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 459559874 1250 459558624 459558629
    0x1f050d021602040c0f090f0e01050f18010b0306030c0a0b27150d0606020c01020a0303050a021606020a0801060f1718010924181b090213060305090f0d1206 68
    0xe2404001c02140d40e4082e01d442c00b0950140c0d186e2203030556840000c80e00301380d81e00644501c0340230200100198501080a4289a440034049400c0c0040c00c55060301008000d0340300b0100c20000004022003032800380040070b0120f40c120303000c1c80041d042010300241400380c68929514820810459021203c0d0800c6880c011100100a84402e00840034189803980100b41000c0295041c00000302d15540049104064a00d041c0c2c0241901941070b201103000e00009001d101307034035508210941c00e205100b002502c03054026000542e0310400e108004000e001e05038440380c100900310840380d21240c1c0c4070459080b800e085402d80d141d00c0e110b0031a2100d1202203c1c1030a0b007190f103403010802c04c220a10707a1281c4410170380d41040380020700c2c1886107000d540d03c500403034101500d40008540010418108281c00324000c42c501e1000740e03100d1003c001280e0000720170302010420391108100301d5032b042c010964003905540c00307807861004182c2116588e004501c01d000501403a04c401c28003410f0396901c07a000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 459561124 1250 459559874 459559879
    0x20c0109030c06080901271109010806040807061107030309020102060f0c16030306050904031806082701020c100e1b030304050919050109093503070c080f091f050d021602 75
    0x1421284070351304001d07009101c00102e42c045c1c4491840c8c0070b03500c0c140664604a503110000340c80161344139075481c10568800e070011540e483e80e84485045100d85040503016a6102e9200054080340900029203090b100501400c81d4078042c40c10040100308040a85069403c0d228151b10400b81507e415006000c154100a800ca401801008141940300d0304441100240b841d440c104251503078001c5401c040102c840440344981c0c1c12140c1b00c1101031403010008a0600d00005081003400390359a802d014400325075003005a2282c11500451409001303141807600021441c4d0074110485d004640ca0b4051031141300d01c209000d00000f90803480a00b00070302800700c02c9100304070940e1035101641c010131101c041500c4150b140c40ccc3d055901040804180303e50442000d0360301d1102015540c141095200410440802910301d00c5000040c3c0c20310090f1442903001c82400f03807543c1e208401c6c0042c907880c03282001c99054000d024600c04039003260841c0d00e0340c440741201503a1103819640000040b080540020b4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 459562374 1250 459561124 459561161
    0xf10211505250503060d02120d200d1b230601060e0d0201080a24080c0310060509130f080705030d0f020c1213080f030703020c0109030c06080901 64
    0x80e10062650080b48030700201002416a0b103903100c00d6203460915481c45501280040001c2841454000c01c4c507021a0310080404480102160850381411009800030300850305051a81c010308514100998001b684c4000502c401d9281c441d000b04410003240b514450240210480c00a00c8440d03512101002a814400510b1441200d50700740d503040248645000290180c2510700d00b860031034400e0b114030350160341f004143d81380c1842a01c005e02652150303048030007a0042c5146d1762041d0070b000c3c00043c000080640902d00301c407004c2c1400d1006080000e00a01d20b411810f00144c0d41c0d17811465000b10786410740d29406102481c010207840d84601025001c4540810300c1805c101c0004010101c215520505002c100700055044050340103000c6401815004201100c0c01810124050040f00d20101c2d40c119100c0d036078140140c2420055504c0c0c002c640c00014545080c5a01003180d44c065050030b1900c09015491622400e05502c0240152410000844049212018250080e00700c0403103005126 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 459563624 1250 459562374 459562403
    0x1b0304150e03090105070b0603101109010908070f170309130c020d080103020303030c0f070c090e0609120406050a021006060503013b0408160305030402090f1021 71
    0xa0a45501480e0000000381060301440300c000011090b0352600906031075540c200043e40c3c0d10003400d404010041d5406200380d2507585002c41450150f207103005285140582c4d50b215510004208114540001249512064041083c4208403a0705c0040320360714190050101d0002510f04d085100301d19405e5400640c030072007201100c125038000c440a440c1d640840310307821130803102900e6080302444082d503d500306100140c40c2000c08002044a0108225a40e203060304950300e01c0c00e104c64641040d448150f45480204000e2405c2044c5904550020010525110180a040c59500c901e01400e420044003003050b00c40301e030082149201d07240010200380a00350312031074003c02d45d810910680d01d0107801406d0103034641d4900f0901705c0d0802c10407881406500240816105d4550010700b00311500c4608118080b2034201e00944108054480d640c3e05546e0309190040103a000360142172250410201801e02882e80000841042101c0a816040701e0003c50000e109029901580c0043c12500c9801040f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 459564874 1250 459563624 459563633
    0x90312030501090e0105040317190203090c0405070c1203110403050607020c01020d0e09040803150909211204150f0212010515041d0a18082a0c091b0304 67
    0x1c00d0503102943d8007001820301e04c10810b0300ba200c003568080c2c049001ca2008400d5055030155a560118040801604512030101140102d034001c60b400d88598003c5c5101054519190040a070030945914018102c2000c0342ca80300c424010045042c420b00d590307480e40220240d10303078096078010b5410005035005841c00b82000380d02c3c0c1c126481c1c1c0341d00500846489084450080c0150b019060000c3d2500050750380e65952003085505c050400d10403110800341c1e000795035860441c944d1140078108064881400c3c0c0d480c0b807c0700381c41c51a414410802d010b00000c100c0604441c0119031107034001c940f4441080d00d0018480081020340c5074080100d000146000c0c4a2402e850702c41c0c12034000b600d082c8a8880070070503030f40ca00e0095000e0144000e9500003110062034841e00c9483e0014462000040c510b4440400c1c850014103140046510b4400400c1045141c4007496154980d00019400400040c080700841503c61159214161042d901070000c25422000f41c034840100740c5090565650700e0505042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 459566124 1250 459564874 459564881
    0xf070e1e0306010b130b09030a02041b020607050313021309060501080c150a080105130e060709050f040c050406030c020f0d0207031209120602090301091a19060e060105070309031203 80
    0x35018028400c41000151100300807040b500c0401045080e41101410130305039441c00d034004203003580d00d0b22607043c0400150340c89104900003030145614015250f451114003a080901c001c02c0a070a0010510800091080211341004d000360704441c4081d402511090120041074509009004203103010700200c0c0035800082c1c81ca2503031004813802c80d29003c14011a60940c414002d001000444400c010005401e1014001280c42080c0c100032030381050118525151640844041000a0b4030200c10045420080540c0040315001c0e2001c1c049176410150207882d5100b40c1c03052604051303458003a10342881c0700340440341009255100350765420700b1140009540720700600054403031710000c1c842c92004c60b0044403210200c3d241000003101e40051a12250025044020381c00c1c2c0554035200c08800049203040120027000721001d0202d490f01740002c181c410210708085003200145020014004e86e1103074081640c0c003a400f440c002e40c1d2940280380c1107036040c0603a072008103080c40301a15107020980540 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 459567374 1250 459566124 459566179
    0xf0306031e060714180f1206040b100b070b0403050912030706020a020111070b28050a0606021213050904170d1e0603020907081812190201140f070e 65
    0x1a500c0740d40b205680e820313040324410200c1c009501003c4140b001c4580c1405803000d880c05000401451004090413403160410404503001c0303504840140400080b0240a00b181d07000d40440141d846c240a815500c28145601c0a40040c0a0100124429074140d5403680c20301101c100c10b00540c0d480e02610303e00309000c2c2d041004540c0140d401c00000c062602c402c0c40036a02c1054120540d05015292070400480d008607091074030302c410101c240c00c032402d44494000c0c0c0f802020702010000d036107480c100009003407124464036080b0403c000c028101c000f041c42c803070a4042c1c0341d0417a45400c064a80f40340c81d0301c0c103000104c4120f00904000c0f031076245001003948650203094602d0090720750002000c10400840300c0302d00000b9801301800300801c0c1414814041d069001d10015480468035200c13411603171030f04010000490005000148034004a20300c0341034590000c0c20350009001e08401141e05440544000b040103014016070f80c0001ca0031031042c0d9104851078000303442c0c102018141c83c0d1010a4000d03d2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 459568624 1250 459567374 459567377
    0x14070c15060b0f090f0108060d030e030c18180609030a030b060403140d0e0619080a09062d0c080c0d111303050d0815040b04061d0115080c0f0306031e0607 68
    0x2945c81032035402140c105214140040c080408101140c0c1c058131149001040301c0d4042c03041c1080500360b520b440d000c0100903007899240104070324110181d50b1405000040d19003490b0001c8061154512001081d60a60034003810045404007007040401c5c00381c09254406418090402c9241e81d05082c0414084030001895407088500003101050008620840221092020640601030708441c85840b440d60001d01580c00030509249544422050780d6030101120810004926141000b802000714820105406802808034072481c000152007900014410102d040c400901c40c841035509034041041c54100e840811348079580403034640e18400f40340c0006c030f4040c42080a58074182d4016502c1502c540c1c400000d00c100c1c14100300c1401b0103026403007412600152a9880072170401062001c44000d001c80c101c0002482d850f04102d840440319014420090110b041e0500142c400c600d4101d4080d20065159543d0740d40320600420b00c2c1102009006140d4880d181202d01125070100d421801003006 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 459569874 1250 459568624 459568639
    0x1707140c0d08090d0c020607021e0a060522050a141f021606020c0a031e050712020301061d0a090c0e09010603030201060501030605010e120304030b0906060414070c15060b0f09 77
    0x91001c1e0b1700d541080d540a584900f080c403a400c01417500d45180300f890409045000c018030036400c045000d410103a04040c0c0801e5012995400c0b107140f1b0304e0b1801031010302d07501421030a858807020450403c0c941c0a2548007000b6540354000c0c603150304802240e1080c60b4042040340900c400b0f4000c2d15890060700d5060300d020303101c0002540c0b5100180044c1d0154000704a0b21140d450356803070300040e0b4161601c40103a4010440c500d80812001c2c0000c01c02050200c0e0b451a0358030403481010300f103030f0b215000701541c024000c5424030020a0303210116802001c13a40001001009402e000403e0722a0780c3c410000070024000300030240806400540890703202e40c0082c8030894030b89005609940c03184c007409000540d401c0e007171903003881c2035070140362020180b4090b03034941607d0b07031104004500d00b1a1000307031550142040c0a210700307007072140014401c8600c041100c2070402d038100401d11a280d510203480056400c5480131414881d5000c80700820340b04060540e240c10036034075140d0a42295051912a001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 459571124 1250 459569874 459569893
    0x30b0a090509190302250b07080304060501051c03030209061314041a0f040207060b04090807140105011a03060a0e01080706020c040908160501140406020c0c011707140c0d0809 77
    0x24400f64800140394150003030100181c000c150302d40c604101080501d422560450000760011249008014241c01510032650340d251600b4074605903070741a801280208407008901007110018003c092480707601d4a005a50703032a110000600d90300030101c08551150801c2c00000d8088001c4000d2180b406e001e030360501a046920030300342c0d05004141c00c665008800d1144040f00c0b4909640100b8009118103000200d100d01c200200d0100c82c1d52003002c40319030f4000188130040c000304085103600c03c0c480400030303c07440d0f0400c000504070f030120071402c40300ea00c408808502e450b99032003858005084900c3c0c94509641c0d40d5035109959064030320528016014081c3c1c018843e091901552000d141c07c407003454640b1684403040c0c1c054405494044d20f05541c0c03100c506200780790460240c1d004900911001d80c03180b182142c1d0714100300740d540d40d40d1305226010740b10354030300316540c03130595441a09420b108090f402c07440d0104e052840340c00d0840800d80100311454001d5500308084c9030092040d58200c0340e1082 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 459572374 1250 459571124 459571153
    0x11409060f091801020c390112020c1c02010c0f0206010b03010512100213050907031a04050703020408010e030417120d0b060903030a020f1b0d12030b0a090509 70
    0x110005500c50300151020001207002040c42d40d0048041d1603007000505e05a1108205402e284040c2480e01c140141a1032130340943e0b01e101d20080c000102054411f034000141d034006030102a03c02c04810b84c1e65000300d400c45030480180304000070200040c02d10708469810302c04c0280203080640f0b0074400b01e8a5a45000003107880042c5a505942038200c00a28607404c0000700011100103101c80f86080c41001c400c59074641c3c0301d002a000054082c0704c80000300381803c04112161200500000c1014941407024600c1c03280b00b0140030225405480c00506601c802070f04401038410368020b042150f084c409000f06142c0004001c2c801c5640c1d00901910031a0020500c0c2d0301c40d594640b840f00000c0d418041142d4244160340281e00880004020074a08181400403030f046402c030100c0f103405a08410041100d4520134440b82090f42803038030068074101fa852000071080440010b01604402e0340081041485000c0d5001d4841040c004040744144da580b00d10b050003034101210b810b03c080c014000d0560300c3d00f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 459573624 1250 459572374 459572389
    0xc05130902030303040209270d09060806060307230a09091a0d14070f1d01150f211407111207020d0f020a090f060b07020609091e01140906 61
    0x3658000c01031450361715140c081000034a000b90008485100f4200c13400340090120200302d074180440c0380a03040140142c44080c001c802c6540c004402e2091000821035140c0e030340422603512003520304081e036800c1083c5075241d80c019902820110031071000207a5520301c40e0000d0000c805c407240070200384400300c03090f84200651a207900407650003210940500000a680d90f054a000b00c00a000320b800e8696503503400c030031000310790340300d007011051041c8a82c55031400110602d0161008485250050403102c4000700026587c2040350b0421024003000380c840c0b8031400030341070700384802a000d1081c0441c02d5100a0740030340540b603820108038003044034500d222000c0340d00740601e00300c503114900702010341d028044100a4540d040b200340981d8042030005a6600100c82c1c003414054400040204081400e1412180141c11030003006c0421b01c81400103076200070440d40c1c440d0307064030400425103c1c401e686400812070080340c102c3c41e1143d400480c45400c180340d11b81701e4000448075400f2030b481e41b44c18403412 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 459574874 1250 459573624 459573641
    0x1003170c0c0d050312010303080906070f020d2607090609120b061302160b070e030c130b060412050a0303230a020f07060f050714180f0a0b070c0513 65
    0x9810070390310310359103240003200c20b01094000c40070782e032814581a0100050b640260422800710320b001c018880200002c2004907402031080c18041c0c0701c8080384002a540c1e4019150342410000c103821030520740190f03000241e450070045410b8441a013442c40e4081c00c00c618601036000080e03105800001c01060a001003810240c1011346521ba40d1203201c00e008411014481c02d01d1426020440ca20720710703d03560001e5410078011950180307541004070f0003c00d04020441414880d0380301040102c480c0d0ba5404416403041010000003c8640108012a400340103503400541c42169490640301400404a00c010a01c1e10035641084241a41c8201e00c45208400c50f200300b2081d40800090461401903006000c40d14001040d141002c04555482c402d8545075102ea00c80c050b00e0f0710034441e516401403022903045a040040508181860040c0c1e91603900c40401d561103403d2a00d2800c07034507150165207002a1060f003d071540d03141e0950030b1109262180344140c0e40079a1481221780003049007031041420 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 459576124 1250 459574874 459574897
    0x30606030b0a2a0f17150a09061a0a09030803040b040605070309080712090b1605060105030f03120624180402041a1b031902010f0216030c051203100317 67
    0x900140d021080f01c44001c2100b01c8018005d034414080807060081d07120700d10942c0c90000410b0f41003000c0b42408140e0f40c0d10f034000b10b44076080000a021144000e4900d4102c00c2c0e00320050303901c1d44980401220b4141050b4000b81c01420004140028042c4800c0943d104034000c1c04248a01d44038480304600325003040402505400060042d0300c0010402c00c41450b062480b031611156181e00c5255891580d8031404103c40c40c900b194078500100101400b1040c011300040b4040c044840ca01d0440c075843e4840c40790360400300140c580c0050040d40d00c0c44c5148006522124031350a40d0074a1503007503e050707400000d41103108502201a0551850a4001c40b010740b003100c411007070101c00b1014400c0c1340e6048046c0c500781040c102c800300c2c09521401c00103400040e050711103e207903400c000407005c0e00311204030b201038a40c24010488a050000c4940c150000d2980c1450500005051824000d0514055600c0036000400c0041400a40070b82c0c0e110a8050300c1c06444404003400c0101f0003080f280c400d00a0150 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 459577374 1250 459576124 459576191
    0x708060402030406060f0603090506060d02090c1303080a1706030f0d140409110319110702010804080d0f05010f06020601080c0909070e0403032007030903020609010306030606030b0a 80
    0x18280e040a401035604a8072619011807100d8481000350b440381201c2d0040400039940d440010f05002040200a4210406941e10103e00031a46c0200d80c202c10001c098a5a45100290904142e10365504c2080111307004001140c40e000e072500010003c5030807420100c110a0700c0001714401c3d150119941d07440303070f20100081c540070044510642d41c040c42c0740ca00c2e03004624240b1000440c805c0d640102c6060110b4044503565a20709902d0860348a00f4030f8003018055131621010518041050040315022502402c080d015650b41d031800014600c15039070719210701070810214a14511454022a06076041410200c186540301d66041380d5515003485810202d500c08010b9180a041094001d60010a1181078401c8140c83d09070f2204001400c4d20b040700042e43d110042004082d4441c00303498800e07044507505103403680d01c2d200144501c0d62400007a104440006d1071040b641c0c003c1d4049002160b01c6034080c40180e541e41080d60001004031032b15050141400c04130456144006001b07040d1a20059000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 459578624 1250 459577374 459577381
    0x901110316140c03060a0b0a05091003030f020607090e0c070204020d0603030e1002030d0903180b18010f170c0d0c020c030c06041d040606180902030c0301060602100e15012301080708 80
    0x14001f82100040460b000800034402080340e0f15000c601034070402d400c030000d015880c607519004103000c00c0f05d0205801c540005042c04401d9a00c0000d460407075030703100c225040c1030b26407010002681c4160f600c001d5000d48005403502070701c1d460f6002401100d0007919040300440d00102401301442400280500581041141d80081440b46c1d010b0010940a45012505420402c0c3c2c01101011540c011900715440411045664034081040c00074001082c031b008803d0201c50003018164201051032415010f40090004254040d080d00350f809090340391030240540c0102c1c11000c0d4503401c01c0743d0064083c0c010a920203240d400c00ca004c48080301c4c00da402403002c0d62005e4900d824500710140c000c4a045450755000036802224200d505150800c1c0364000501da80c242c170400d1b18100048110b45c4c0242d0405e602000819004151802540c014050202d8401d4542004e81d080c5201c080c0c40030745501613200003142408998403110503181a9144042c0101242e10054865507802c80b85d9100081090300003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 459579874 1250 459578624 459578641
    0x70c050c04330e09060405010c0e06120712020a180f080a200402042d0311040b0d0203030307030c080a0e1e0f060c0c07090b0d080901110316140c0306 66
    0x2c49a1844894400c500042e12005800340002d002d030780e010102d90260040c88240042841030f0303488403140741400300e072900501010800d103015408600601038001c00c0044e19140c0158030b800c01441041da021980c400642401400100c121550498204060074002c2043c0419015807002e0340d06045c0107040000030390b40c2d1010070b000700c1c20300039070403030910f401070340c3d131a160340c0040d001418509071340c1c16140600a4418a402c814a55030451003401c21000b00701081d41442500100c18050305d0200708414202d02180c884089420002c0d0184000010082156810340c400007540a0741c0c0d544098030740f00c154190702515103031550a446034000c00e640341508990220030201002a40b02562a565180034003141000021100c125506400160100426006000080150401d04d504000c0c80c0a8607011450b9500c1810ac001c3c00000b00180e84092680203401540f4402c0000c1c00303c950300c0b000c0003941c0f50030200e6510b007100c0c08404440004100840441c0521070340802078001c10095582108 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 459581124 1250 459579874 459579941
    0x1f1d03040b22030605010f0e07030b1e1507120806030706020718140405010911031b1306030516051c1212020903030d0e15040c1206060b03070c050c04 66
    0x280c03a0303240790b00c03500000061950300a1074001c1c00c000141c05012403901d03804c0c0e603505c10003c0032601054a0300b50088100e9450003421481e0000c0200c52846015860703020851341000181c0d000e10710b450200f00300c0d08003e410180e40301401c400c1d0340c94410540b5010141983c6442501400d030160b088100240030021403807899800380b0080c407001207500000c050348174080b84811707601510584d440360740c84014480801084c94805d0400e0b002001c2040d1700e6013050300340401e00718245125085c5400e000c2c03c148080d4000d08041c2d82c100d001d403540500903101e5051041064460f950207501e001040c1030014100c48050300e1034135003114903e6203948691404940ca040030700420032680c0d909106459840e14100058070f54000e041e400001d4001540d1455444d240e10001c3e081e011403004010440005c9180e4045000c841d52039030011001c299900c6e10030040e00c080e0700481e24a038000300c20048000e600c684540441c502500648400d41c08100910095400f00d40070400e922000109194401c0d44904 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 459582374 1250 459581124 459581167
    0x150207030c0b031b0c030c0105011e0e04230604050d02150f0703110a0f14090303070206030a02090306130201080906160e0105120103080306090112110d051f1d03040b 73
    0x2800441e075a01132110800d02600003c21520310383c1e0010800303c441120910800380074154044c03200100c0b00c44a0100b0111200d98010701d000043e080e0040b60401180161400256441d981465111580a0001585ca9804840c1a05c1c0352003040b0030349480c64004220100c1d0a07031000300409056031907065804032540b0103401401095034910f031041201c600180540704162642d594106580c0340000c00902c000300c0c0b078600d01551802040514007a543c0001102c1505030f040e503e2030349035a01c40c01110003d001d01c52000390180038002c01c1040d994030408040002c83c1c0300340c850340c10741e4803410101607942004454152010341e04413000c58070301303014820a92102105140051030240000081480f42d14280c2c0111400c41010041c401185800300d4240d0141c1805002440c0514454a80c410148910015940500040074084050080c01c0c449a10120108641d294240d0705a480790802414010300c10302c807a401c04151561404008002c40d411120b8a210381e0703040ca650101c0c0d4040d03080c15503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 459583624 1250 459582374 459582391
    0x8070507051915091b06020f0615010c14030a030c0201050402090f0c0d1503020301140c03150a0306090506150f01050304060c020f1207060606030b06161103010f06150207030c0b03 79
    0x10080404188014000c03101309901c200c400ea00241031011181410031900e81000041d5000054103400114002800caa88922890000800b2007800d00c01654804c9243d1006000100364460318001c0810000c018640803050795420490300040c07410032130032141c0903200290b100700700742d0210310340c00e261540c1141c00881e82c42606141420b409910302c2120201806810140c1c0500010015403500703200300c2d0f001c1c008445101e202c52402007418815441700910181c02c3c0d401c6102807030b2480d113802c400c4070701841c1d001000304001c0465040a9aa0703040c01c0301c03480035000c1d54102c00c00544c101503240001c02041070711031504507201c541d40caa0107040c4c460b01c1c4108620810b5080c61100300101700e150500c04150b00b60036a0b562032810107009590982c0c005405140c10140300c107049898000480d50443c1d088040c4000840080ca40044840c0c5055040c580c551f0030601c500340740540d664092011515406408504002c0341d41c4240e031249030310b110181041d00c0750241080b00001c0c400c000c42d4821040b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 459584874 1250 459583624 459583643
    0x20a121101080a0b0a030f020a06030c02032b06062d050711190e01080d0207060c06180501020d1409060603030f0310050907031b030e19020d0204110a080705070519 72
    0x140c1003c241030903c207a1040d21f00f8943e0030f00000c21f5083c0b80d00d0b8800640f030545001d11468502c00c44c0699a0701c5868805d114281314030040d5103001e00d9140003100100c006007014032820780d0b01c042c0180350300d14003280300101403610707c0c0c540001220341304040d0384c111903501e409040400548035140da5400e000e20107030304000845000d03003d13200c665a001002e0700108040d420355505000013103140c604106481400e65101c0d4106114a540190a440c0400e9201c0c102048594881425902c108802d00000b41039600108640f50705201c00d4104044c501002035100b00140d6401c4142d40c1d81c0c1d0070503220f89800d40c0081140c0170b900c0035014025648607007654200d100160790713034001c05e034040011980c81e00065627a0221014a1000c500200b1341a02c0e1440c0c280301c40421b084c2841c0d00c0d030080300342c9203844101c0c0300007240454840204942400390000c004110003606034140004950100c1010800908050b0010358040e00a0b000c0d07404081e0000000c200c06140014030324401c07c5c2080065401aa4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 459586124 1250 459584874 459584891
    0xb01210207051212071b02060a051e190905090a15080a05011b02060411010305180601090f29060f1603020705090709120b06060f16020a121101080a 65
    0x203081290840900600903a95034461305500050b042c402d0161130041000210104680401404c640d540000364040760307020ba51b101042d40543e11882900e42c200c4031010343d00b401006450100010340480d0380c84280e00703074000000d07404c100c03001d03034085c05100d9000e030f861008164110400c0d84400071004504da122142c81d52209c100c07503c0c0448488003100c2d10b070b465085034042c0a5920041d000b5035511b50000b8603e904150ba242250404101d580b5410955148002812a01e689640c881c840c3d104005640255031901c1c04600a004050740d4860214204002c00320050b16100d81001e400103224295119003560f04d00304013050744051031350900f034042440b06c011485000b6894000c5240700760010002c25152905000d13a07450010640303801e004100f04100402c0290b01c1111948943c0300311200300e640d941c1000900305015a51442240c3c5030042043e9507051005045030b500d460085490246080e03540c03903442000401184000d107030744000302c400861540100e80b0305400201c10b10000c140740c103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 459587374 1250 459586124 459586133
    0x70203010603080c101b020a020d0302100c0503040203010c0206010f031b030c0e06041a030d0507170f071505070c03030203100e0901061703030601050301050114040b13080c01030b01210207 83
    0xc0013000164143c1c2c200040c84c2c079507810640314014020b042d250440e80744c8140488069100c407440000079002c0e10301c6c824404101482800030182c5090b5000381000b2184071104010415002114201e0003503180c0710140302c040e030001402504940c0c0c400440301c589429903646801d49010004001000c0301a07440201c0011510160a009001e609220345294600907003004151888003151940e40a540b8141e01559100440c1e140200411400d2030303a600c10103881c00480b103101c6a030000f1110310740030844910b40e004184c01450701d54042d0080f44000258155008100c070001d49540740031968540c0c1c540c000a000340c0266610540e4041040345e82517843c011f00740924422181e0b075032039940d24030040c08030b041180035907150302202304015030951a2081c000303426444103000b4141840701c410b003405982140a8101e0700582052482e4a4441c00d0500d020000c2a00f039004041190017507001e000c1a55101e84500902c0000503550b01c1e0409004011595554407085615042c05800b00004c1d000718 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 459588624 1250 459587374 459587377
    0x304350105240405070f050c1207290903030403080405030c0106030821010b04030807150c0503060a1706010611011118010206010501080f0a020913150812040f090207020301060308 79
    0x8044003180b110324125400100011a00d001c08801d2107a850102800201c41c0d02044102207650715043c01d60b901c1d5450b011851801d0f00144002c459610000340300400c000101004c000152560b541c0090220641842a103010318110b5494ac8594020310014010034424200d8903041400340080c8c03440c08015151310380c2900e02c583c0003074031014000141c540b000130000d03290300340850065443d400b055040600783c0c84248900d102c080c14540001c40c04c1c0c0705000d0300c40c818205002c1e11450401c2420680240545070b070300704480007803003250030100004440e40d10303a8450140c03074400c4000d0a0160300300304055441078955000c2010702d40d03841d4454516240c10724020100310505500b0004503180210009140600580041d41046003d4052003181c0b10040c42407a04105112000b68480340d411021441e5200c005072984030311b03810800c071294160f013100e601c4415a2022400c2d25041c054007604e5015503c29442281050506010700708400310f0141d0203003030603d00c01070002c1030032582c0c0d45511426 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 459589874 1250 459588624 459588631
    0x312030b0a170a12050f1605010b0d030c0b1302030303181923010b010207090207030302091309032007060818010c0504090c020a0f06050a060e07030606020f0304350105 74
    0x2c550206a41c0b005003c000c1d0310160034a1602d1514600e01150729008401d075000d4450124410301c0362551903030400c0001c1d0050030000c2009090212606e8260074000c2170303800051010f507954248040450301c200040c026410b030705600600258590349400c1c2c2e21010440b504842210341c0c2c0510006c0b1180341103111000c4c48030b580180045070b1072941d11039a1592100654440b00d850780e14040002d14a40d0300841c554040310440c4000503102d69403800d05401038030400d0300c007661000784030f00c01c0c040d110001d60050740b00c0c40c020b9890b0141c00919182c01f0001c8040c204101d0f145500000c000c02109102d800140c4d0301c020f8416045510243c00c0400703601390382d000c10f0048081000410240808007181c0b060a540e05070303501c01001e40340341c95200c04104e0348841d900601499160400039034205007941201c4000c00074018503105503c0c020700000c3c010816402914010b025680e00e200444500000303440c2a504085444043c408001c07603a04100d400300b04283c203031540340c1309282c0a800c00030300c2501d20 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 459591124 1250 459589874 459589919
    0xf0602040914060d02091305030909040c080115053102121b0304020603010315020903070b040f062303040f08030f1006050703020d050c03040503070b09090108070312030b0a 76
    0x91145450b40403284156000348100e0143e20709001c00d002580c0c600352400c0c3c2001c0d40b41b140c0202d038409810000e0031889081038141d084210032003480100725000d0050000c44541400800924203030000e1401d01000a200300340e4813281021500200306030b40b0704840003804140c04406094580da0805006a070000700000208402e0b40c2c01b044540103d5501c102883c42d004c0c94036624514199000540900041c00060620081d5440414482c1d000758111241c0e00c50040c200c40c0d80980c4c600b01c03500c00f607016004001e44866507460001d000c50007500c400c0280300d01400c246509c07030889262804541c2005005071061000c43e0f1000303010a01c1c0302d00450148501c1c0140084526165054036102c0407941d01c08001c2007410041c060220782c1c0440c5012079131090b8035040756030b40c6503514824554042c40e0401989070089000c00544000d91600801c11200c09072000d151984c4e0310754207983c0701c0300d0610014110403541309000030300510941c13104030354080c010b051403d40368640c40e2010700b4044c050244c29 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 459592374 1250 459591124 459591131
    0x50406061e0311042310020307050d0309021c0605010303020c0d17030403020c0d0b010501200c10091509090c0f140f0403060603032003160b0a02040801022205010e09060d0f06020409 80
    0x1728138107080c0140745260301c0d80d0004514000352076031440d0391502c544503000e0402d40d0300c0746c151045558011000001c188504c4821100c401c050400c031000303000078401200944121103c0c99800d0403c0a001e50301160801c00448007440388041403e040c5c2c3c8010400c030118054440007106a6480456019541d402000400c0b01503041c900007520341201d02c0c030704041000000c400c24441d0380000480e1040b00205440e811801200c0f0f040c10384184015400505100800701381c04120650b1100790b100072240c1c083c4c41840107072103c0724141c0700000091600c20000350400780da2014004254002c000143d0303d0600140382c650380c1e80380c12040781d845810403000504030450040043c07203094006019448004051850f00c2503207403000d0102000220001c00b00e03164480003540842599050300c000340b00000082d50380c0c903810802a54550003101d40010849017048003c1403552103120300700c00100019001e10381640b21581000941441101c1c2251300300c000098000010302c1c140040c1000b09041da1011 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 459593624 1250 459592374 459592439
    0x60315040203280908070f02150a020123060a0e0705071a0a0f1506030b1807090e010815070c06230a060503060c03070c1406040b01050406061e031104 66
    0x2c1000540d18443d05038a420800039401003801d02045580b2984c0c015402840d4181c98808910100112603040c2200c0c02c0114a81c940580c06421050f908103a450b101c104c034000c0000c00700c1150609031080c1c1d40000d01401d0500249902e8042d00740c110002c1e0408178203003030243da510f03031901462844130320503580c502c0c05220091000380103450444403045020f205a0034001d030748075800980c0b8882e180415442e03860700c1c8455125025a01c5002051107401c0d645468450009060741917240b180d40307842c0343d000000007009080820070165074500014500d8090311044d200b11000b4168800a0340d266546060702c0720400607000344e06407504200100c0c100945085041d95003141e00c15403255000b03422503030400c608441010122603014100c0d0600c0501c188103400d05240044114402ca085482440c0602c41413146844c429030407108126401e001f945e441d081e044440355404071152444a5400c00114103c1d402608009106510810b0032800d0582d81c40b0b64203407414682c40103294125014009 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 459594874 1250 459593624 459593671
    0x10504270303051b03090d170402030a150b0904050106030b0f10050904170a030e0f0c06071b12050a02030607030e0c090612070b0d06080706201903080601080105090603030702060315040203 83
    0x1d2418807170010b04988d03035514280d00401e4a650585200400e2480c107818940c0401c1000c0d0f0000700a0500a00720444501c3c0614210b4000c5c0a680015241158000c002580300f8080c0c4920303500c1003031400120381180b80f40400b0300110710700140c012a00d0b0100e0688040b990100b00f0042c000c046000c0c4d4002c92a40010703c1c00a00b002c1c101001c0c070160340c10000c101001754440e88121581e2681c8070540c110600756003084d488a05080307410031000c04000341900070603c0000126880d505001f1003d591154031a002c0550854030440728109031a0484030f0b40c40103900d001d00300c065000502500300040c4400070000141400c9140e00190140c00300411208508103003840341b85c01400d0b84a0040191354148607000e0001c141c0518000249500122002c11243c401e000805002283c0c00055249001d980ba0203000600c0480c0c01c00c0c0051044c200004051401140c400c0c000c40b07018029502c0c0c00034503005d00c101c0307600081c19000712205441651800b600c0d1031004604c1800103c800418440002c001c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 459596124 1250 459594874 459594887
    0x3070c02040f050a0c0203040f0b03150a06050711090f01050d060b09070f14070c0e0408070c0e0a1407050301150e100818060105010909020c1c08010504270303051b03090d 75
    0x40c000c1c1107510522090041061540b805016a152b40340c4c2c05840340d40301c01490310002901022650810800c40001514a810501409a46100340540756200007010103114038464110ba416805203109001004542080e01c031414441d40164800300301001d5240c08103141100980b84100003480c0000307002e00143d8000c4504140c200c400c0704c590310300f4030161035020b22000380b80a014242034180012804010041e01221503480d4007900a080701030307a5640d0703e081d0034004c903107401449052000004400355240c0e80144252100d46580341582d00b00541003140d10318841031402400448031010b00965240e100c5800310a41c10f41d41d20a007807503e007221414070100881d51562a40c07210005205da60703005075114081e40d551020060b1144c5004428900e0b1034480035040034410880b00d01070303810310341c800c00d002c1c142d0703400340e03414000d0460024058001c001d0070404a82c031500c2003049500028402d4101c0c0c0d800850480d141c1c145041c4010911046501c2900c01c3d804a44c03041c4804a075581d0071a4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 459597374 1250 459596124 459596141
    0x100b010512131b06090b0c030a1b1502030f060d2103060506030c03180f06040213110c0601150908060c03060f270a0c0f0f140c0127080d0203070c02040f050a 69
    0x51b0a141049055071680d560780c085c01c0d090005002c01c01c03081901010440b5070700300e58540c102d03030450781650f02141108001d610a070f84101c1e400c8003410004400d400c0100321999455803042000080780c0d0582c190425059042295204054807200001580d40e03500e4042c600411a040c2403660324180001c45c01a03450601e12a4030540d0030107914081c8180307001c11007903445501503404c09010156541c1a400410000402c0203d6140104081c1ca66050021303800c2e0603181c40c03c484052400083e00c0a644034031052080c2601584181c2c00038810050a5010315002a000b50180900040c0f030000504d4195400030800030540c20f40c265481c9040fa9583d1490b08070b410411700300201d950645000b404101281c0641041c031a00d441050445441070b0f0b072010074952448006a182c9101d000d03018041c2035180f1107045c24201c2410605c142c0d01a00510788056640080041e251125a81c0711801a4000820315070078040c0c0c40c0000d4003d0386442c000c15000d06084400002e8a19100b9405001c480c03420 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 459598624 1250 459597374 459597389
    0x2040806010e0a0e032b0606030e06180d12090203030705160906140f0a082509020313030c03090815040b0a0c1d0f030a0305040305100b010512131b0609 67
    0x510b081d1880e44001c0100d45820756204d81b0740c0041ea10601600c0307081e540d8401500001c17482c0100c0091680e038990300c415201020141036450503100d815003409404043c0c0c0704509650040c54440d07803840c1c043c1c9102a0713141012880480c0d0b40c000e07600080d09603001140c042e6800d030040b03200c3c2c480c00000381d40800083c04d40d80700208141401c00b112400701000710340c4490701800c1c8680682c1d500f59120084d00006080390381c1203d1000b41d112100103d407400e0040c200005d07815014000c1003550713940c020fa900c02c1d001440400320a410700e4408486070034680c03600ba4240010b2560118000105004545074061034000880150816103010440d18100600d03c1c1001850142002c69160f48606807882d84003010340013914440d803032400a507440c00d03441c0d0f0590b4544242081c0c3d0f42011703041406882101d018a05807040c2d54491a0300f601966004003c8900243c0100102078803060341d0000c00740c012031000c0c1c40d540c090440e5500c03d0032054158244040d5266480d00800c0405d501c050400060b240c070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 459599874 1250 459598624 459598631
    0x6050102101103010e0402010e09041103010b0a0518061206100302120c01020703145212062c070510050412080717071719030e0102040902040806010e0a 67
    0x2582c02420a404107000301104600c4003030106055a101d00c41c03c00109074018101d01103404d09282501903c084101507a0280d401c1840300c407240d14040030710004581000c0d2071004d20a5014403642d002c404001d000a0303220a1070a440300142c1c00402100c0d00c61b06080742c0ba49201c038214010020f03c2d06c00e51100341c4039030b03000d03080b0300d1a240d0b408a0700f842140c1c0d1051401c50b6450321040c00350700740200a6605107008014645100c0c2840046401020440b0751340d03060035224145100401c0d01100007062980000504030b000c003e1070305180d6058580031f000c1d110002da828101071840ca9415668602a9078100c5c2c40c2e03031003c00d113a80074860080100800c651080e082185050701901d81d018034071a144002c424981c441c1c00340101441100c2d60b0076440101c8019003148270700d400130160032840056804403011055080901c0c048822501007a11103244d529007521540700c11400742c88000d0401d6039a54090200141c0c08005001410181c80c00b00007800c030941c1407850200440600500542c0080c0c10b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 459601124 1250 459599874 459599891
    0x360703090803160210020c0c090c0c01020c0303041104060812030405161401080a1506180b1c050f0c0d0f14071706030102070210081b0d0c032018031903030605010210 73
    0x20002123a0140d035006072081e2040340c1e2800e130382c91401d001d141c40c510f805500000385d09440f0708010004500c12441400c0c41c1c603001c45504203110840d901805240c2d00f5900503c6100e406500110246500521400840e07001030086040c19040c510395034411680001502c100650365a04044100e03880607008000700001c460203a00d602c0c0d01c07a1035104901c1030100318144048540c400b280300e03c010f0000715900507a0f135084102655420020703042403201b5503240401244144090440c0640502d0854004a0500c0c91111000b0f009100c501400c0175080c1ea550a42c91000c501c6000e114864041c0741c603444990070340e0004192480342c004008510a9204001940040c1d41d03d603c4204c80c40c0c80342ca4040b01954485410071580100c4031700d965141a404a0507a0854105070001c040249055600f808201d840d50080788512142c4041800c42204c00d11502c284031400500c1501248001000c035465603141d81c41c0c06501c800b03141d40a600090721200c06000070358041040122919100301c08108042 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 459602374 1250 459601124 459601147
    0x110105090607140c0114150a06031a0105030603030705060114100306050a03080703020f07030c031109040b04060b06120a0b040e0601080703111f030b36070309080316021002 76
    0x11000c1070340480d043c004150800d5059095010703100841006a0040d460b0500041d240741078250145014400d0002c5980414018440d002e81d980c1c200344181000b000604c00c00040d503664000411a940511042c021080030071010855035009082e80780c0e1041d039404561050291110301108000b0500d17042c4a010007a41d2207441c000000c0b25000315680d901d41203e49012410b0414100e10458140314041d00070092040c18103007001101e1245045c404101013000901c16001022100a050941440c0005000c80c100307030490b81e50820001c0040c0d02c1d214000100166061060f5801020b699031412251041d04081c412101c0404003140204080d40c0740045540d034ac1c4505010007845803011015200094441811081d40c51481d960344102030440b00000500600d041c02c0e159100704000e40012102050700300c00019000410300c60010703070450b09025a400c4100103051312082643c0c403a15003000c9170801015500500c00e00310f200c84400c3e08510001d15040c102074031460074500c10444001c420 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 459603624 1250 459602374 459602387
    0x1050a081b030102120906160f0206150a050a030605010f06051c0e01060b12090d09050102070902030c0f0705070f0b03150f01092315162003010c110105090607 70
    0x6616404480c5140029100403d0182c0103e182d81d0003165a184140510048080380051142510302c803404018083d682003201c03000050820740015070403660101d0740007aa2a41613820100740038042c91421940d5401041005119610950302a943e910043c401d80940e00c40c0c031320040066103042070501d40d4100c3d1040c801034221030108030032681c6001490030340340290001b400500070712542d65224504542d4040f450b04040369045894000c1e4002c0c3c000c2d650007201080291003069000745480c0c3d0410450340000c0d0f101815000085400740646035a441024000b0311910344980041c0583e1443c162180d402c282c2036422141410105204000310144c074501070003104201100c0d0760b00180d0001005840d08003154108000494810103000c10b0f400c000c1e14459450b1105540b100854144000542904e0040303111440800741e100401c01c0100740c1c40415406400d4130480c1ca68014501c160021342114031250a205c049018041400581c403c00c0c410950f01040e07450203440e44bc83c1000009080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 459604874 1250 459603624 459603643
    0xe06010501020309130603170702010f0903080423090907050a0e060f27090105070e060301050907032c0d20100e030d0509010e0d091503020313021e0901050a08 70
    0x1004591704080100c211a009040216041505902981e40c45040c005c0075070311406069011400b64400c5040d403a212750000c00469420103d240c1c01c0505000d51002084014500c0400c1103614802c02d036480e60b100091940101ca00303030b0040140510380010711900d60056408103c01058110810a540d12241201403407034078210707039620741d0b043c0c3c2e03040e00032640541c400040026200c0c5000c00c0b5610b0815031009003d6007a584642c10013000040030810031b4070090054a8201181d100490300e41030094222545480d503c50100190b07a040d500001e45480384440301c81c6940e44007020720440190809140200300009070302c240c102881108405584074115081c90b0071030380c1c0d5403c007060b00780700034010340d071107141c80c0c080c20b214500b01800214040e203800108291207018000200143c0382c02140b660302113502480300e0701c00060710104180d000b500020010754240629280c0a00141d84441c0c003000c16000303c90110751480c002500740450a10141c100600641c4400d905100031040003801428 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 459606124 1250 459604874 459604879
    0xf060509100c050105042f0117090a0206030a02030709050d0f171b07030b150d062a02100f0b0a090908040b0f1b01061202010c0f050f030a030e06010501020309 70
    0x1c8204201800722207046141501904551070201070004200310700c81c0380568404841d005400103c3c044003a00448003421b1610781c003241ca03d850200c0c1f000300c000c211650046101c41611003407a61900829015401220070303c42c0e445c1d000040080891304058510042c0005459501c40b81c190382e81d9000070b00c0b001c500003a1006d0303081080310ba9584864000c44800c80700d40003240b10031521001c40c031a0744100d540001c0b1044403c0800040c00707012440070100c5903500c028000041c0181c01d40310301c0300810310010040c00c00c511940307840b10583c052080901450f1800d42c000c0250b86111502007040300c0c5103886008c40f1074103011841c102965124101e80941c0e801c0e610000c1c1c0c11019141c0015184107503840089500004969284924401d001904d81036424041841c3e01c644400c4406089824038010740c4030100300710b0b0b403000249d445503d8403451b80d8400c1c248920328140e00d0b25201d146c202101d0803c0015400000c0016425516000c0c84d131b10084040010201c81d414100081d48901404a1150 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 459607374 1250 459606124 459606139
    0x1030b040f050c040f0b0906180414070b0a0c1a041709031c08100b04080706120b0406030c05210c090c0d02030108010524090f0a060302120a020a0f060509 68
    0xc007482410703c50301c6400c1400810800002c084100842d001d0212070080c688a50052400160503085c41648095603030301031161440d07a0b84d03440d81c40c00303412182151000090302c00c002020403184103070f01c0200b03103691440c0c0301d458105074039103440b02000340d420311411010345078403040c4800203000d664038890b204100302d000c5484505000200b858a55084044075070008600c1581400c103811288181c0191205450840b80d103807940a00c4589109a01c103103640ca0748042070810030701d8440c0c00e1984105c00d0764000404d014906000250964829030019180704003080c1040100380b80c0100e100e49803090310f2075150641c0200041a6445801880205004091150009003010308140c1220004201003004540742d5840e45500c90082c01c007101c1d401c401040c4041c00a0110005202c0c12a03800402000c1c80b8a03a40c0ba02d00b40581c6150240c01b2000051301c0e00d00c04001641c0706119a228550504000e1608000c0c1e4010406540c036954031101d4007103114034081c030440f42d01074211044080240c500e01c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 459608624 1250 459607374 459607403
    0x3080f07020f071706010510170709050d0b09012306100207051011161202220603060920010206160c0b07030207030e01050301081005040602040b0a0c051501030b04 72
    0x5030300b030201d58040030380356010700000802e1001079400e02c129002404811106030f6a250014041403011004076200851548a2540140948904e01341d500c030038145024210301d42c0d136101184107410100000c03680c01307480c0c00401801150900c02c0d0302c145405505190326003200d10144a16120300a09420301480c0d2401404d00c8040c0200400c200400b0007515000081c902e00301c005000102041c800029801010401980c8506074542e0744140e1305004580d00b5000c44070303405c004508500b410100c4d121190920b14a00c4803c051060ba80110b01900300443c8071002c920700780c40d407540300300040b00c0000c070031141c070079401d903400540268800c0040c0f03280d0f8070703005100000b07803180e8a14010040442e0082d9042011584d8150040e041c0f0502c02d441d000000441b500065516000c01d001e0300d40580e12003140b054035455103410081c0c10034008c10740146056140c1d08078000c43e50041c520700c00410400b0a802c02080300c03c00a81c010150301920300403455045543e212071020001e4406041e0900074800c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 459609874 1250 459608624 459608627
    0x6100c0206031302190e06030a032a0507090207050c060f031801020d06090603140a1110050c06010b0901080f040506011202040b041406190509042a0b1207050703080f07 74
    0x584403541e001040841e0303400b041d520b880c5480c5c803240200051100e04102241060400148003205070740e040d200e8030108514035211000070f40b226600d54542c259480440300c045a030038030178107024145c802400360742d80c1c00301c0c01d10394904686c1b9580ca5004e5001004400c000003d10029642c101c041c0305101b0591500424005029004004040a0007031400c2000600110b4a40c0f01400704c0344540207500491940300080c503210b60104c1c0c0d0240030000c00b6a40807800f0724182c044010bd005040c14075506012100300461301d8508247c00881c00b41500003841d110b5913030410302c8682d000e00c1e041039805180c03800c2d54031561580010b201e001843c0203400081002c560f62900720150302c44000d413080140007000e04000001c4081920340d640101c10252001c411f41c448043d0040595001805841040c0ca9596449085851810104840301400d40314541140800105803004103107050741c403519411312081c04201c000000e450b0030b0900c001040507800080d04050700e198000d61b1101015030ba651011070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 459611124 1250 459609874 459609901
    0x2c0c0d0503041e0501030e0309100e0303040b1b070506040605041806150807031b020c0d0204090512040503010c09081e0106090905060916051c03031806020c0606100c020603 76
    0xd8003840b46501007102204001221013110790076601400501140c0e200386840e031040074644c036008810408003004050140c10200c07001e01015003200e1609503904103000c42608000940b80d172030500440c0c2205000000c02004010b42000c032400d6140a181c4000030707200744100e204105c075181d09001d15490300c0d98a944040011300b110340d441e244128130382c100240281011194000030901d0490700d4005c0706007805501402c000290001e041600c41041004a103ca04070022a40651100421000543e003482038842220360030314502d45582c05e0130105425101c0d0158080c0401213106003c200740100002d1131000300301d0454407410b16080402c003040c003511081c1c2000128500b0328517408100540001c05602c1b0b0b4180c1400c0c0c8180382c14401c01c00d01d80c04180d208865101c10702c98240c80d044203c407140c0d410310a01c01e0900044004400100108504200c401030f03404540c080b60b1486039031014000c1c2540103204032000c03144903100e0013001d0110300701180040d005102c0400001c07640380c03c490 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 459612374 1250 459611124 459611129
    0xf08070507060c08091006050d080705120406110706050a050301140a030204051017061015031b0f021605030d12020d1109150408100b1f02012c0c0d050304 68
    0x102c1404803102d91a0081c1c021001910000858402c450618007064541d105800654200401c1062160300ca5100c000d95034111400a903010702a1480200814441d4802080240415101c010000c0c0c803040035541071103c96032050040c40300800c0200e010719070001c100c80c103484038480e1080f80c044580011410207201508002e4106140000f40420329040c905000125a00441080501c01198298a8407820251a0050264100e00003801041c175210245030302c104140c5000076401210f1005400c0340f510351241100440e044480e5214541d41c184000445170804101c0310403030742c0c03030480465610740100051904100071600c1c41054864030b5012070340b8401030654240503151807265034504991002180c0c45c440c0b6600300e41040c90164010590302240c03403003400b03021100b802140c40710181c28a100b502d0b0380006d0354646045c0b42c1a102034403140c100110f90001409100b0b03030101149194100350407143d148940f900300010100e000030441e8101d201560f00003410007244c80d10030314500503078 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 459613624 1250 459612374 459612383
    0x1090e040f02030d110c0303070c060f210f0c11060c130e0a050105041d030a030203060612070201050a0501211b0e090d090e0c39070905070f0f08070507 67
    0x600c0742680a980c00410b00f15003582178003d03100f164801604155903032060250041800007240300410285024070b88a5040707000a003880440c0b05030000645d000744452400d40c100081c2c1e65a61044580e000e485120000d0707540e4104480b0441a103c1541d40c1c98600400518100d080000d10420300000303034002c98010a1140000b5119081c240c0880c000f0b050240141d6010b2840c14940c800b622180246c1000d010300c94402031480c0000300300c8100d019500041850390801d00c00c10600c1040500040124415a070703039400000c65040c9015800300f07958040c0d01802c55000c0e000a00d81c100ba43c1a5541c2d50299800380c0f06000301150780b419814001c1d141c3c1d00004012110800300100507501080c40ca440000310b81d81c1403821030f00c4d1041c00b101064141c0d01c9130b598620a00001c607029031001005c2092105510710400381038020511001d0229040e080c0c00c1c0180c00c0000200721140c09030040c950082c0e21070804080d115000c50703004041d0768200a90b80c00300031010b0007003641d01e07005004a0b600c280d00b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 459614874 1250 459613624 459613633
    0x9050106030e0604240c0c15050c0a0f170408030f010e0c04060c0204090b191104300804180e030a080f130b0c120a060312030902030c040504120f020c01090e040f0203 73
    0x106d1003d0701140c5045d0003070b2000c0d12810040c440c020040d00c9414810f91000c0002401d08111040480d07515069803404414429001040c01b8424070b59502903104511510540d40c1d24503200010403260399040c0d004030141c103d0075092000e9000103101395801c2d0b403024603100e00b0380c1c4440c1c00002d0203460300e000080c241d5200401440380c26060240c0c0103000045a940c01c4c401510f01e0380002d00244110300c0380d05a2400b0582c0444040303030552035404406203426042d440c4002e60394680802c944d001d40d011508080714030443d032801120a00511030140343c80f402841c01c10840713000c054400070006111012940000002552040b02c3e02080081030350000500011440c0c00000c05016a00080c071007007003013403190700040c0c0c0d50b0400e000c0d400071383e0340c01030090014041c2c0400a80180071805000c0381d00d0301a00e440c01001380c986110781f61103540500c4030b1225005c01c0980240c00a10020001c0046421408190449907040200705c030880d50351a03a01103a90f6a40d042000c0c08007001d1100030f515015 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 459616124 1250 459614874 459614891
    0x170405030c1507080c030c0d06090e1b03030f090a030b0a0f0b0d020a090f06090e0a022d091302180906090309030a15110d02030109050106030e060424 66
    0x200040900440080081252108481d4402c8040021812207502000816a80008400003019406103030052050740c0d106041c0a484001031301543c0c8030b50041342000e40c0c2e0701c403a2604424108000820844250f1000a005243c7c0c40883d40301c1c0304224007030401c105c0000c0c0303d8560b034a9003500341c8015508030003510094240103025001411035641d00009060820718a01c4503860712041020001c2d074000d10851015140c2a4810301511058140c0d1000c20ba80c1c9600040001ca03034010140c000802c400540903036080b91040040c092090000d034090004403000e05240c0600c1544c0f101c10001d02295000f1051759102d8065201c0f02a81da0002c2d0040310201c185003c2c0c58401e10024012202c03141a6000e41e955141e2a9603607000c3d5031006549680511380d8600402e44a50301c100c1001700000c0080344504080d4240b200d80da100f03070800000309600000400440035148103142c00741c05d0354581400151020600f941c0d8644019001401005460047c0300b201d140c1a11f0007950049210710501c07940d00c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 459617374 1250 459616124 459616133
    0x303030405010902180f06010807050c0f03030105190b04030303090809060d0b030c010f17040c030c0b0a0f020a0c140a05091003111002150916032a0f050f011704 71
    0x401d8507812805203664091707181640c800003240c6403003140c41c0003140d0400e81e03505004646018000d043c84081c03020401ca00c1440ba00280b10341d194480c004002190342c0d524100c10301681e21103281a00d80d0340340340b803241440100b0b0f9900460382141d401d4580450440c9040c00d003102e991068040072684410700003000c405140702c0ba0447d1113444011030035543c00d45040001034401d8000d4400c1000001c8160041d1004040103103d225081802500c0950000d0340f250303a0701007000341c0e0b5080045910340c0031501144190740040d2680c10030b491817000e041103c0c515540c13007880702c03000c0c0100e040c050b281c02806aa04e03101e07a00740c00e00408000307000401e6410f0000440c401800d80340400e0303440d010101084859400c001ea101c11403807003140c0c01071607814072540000c555031002600340c054900901801402e072482140315400030b103004040d04040341c14807071220b200c04140c07071485002c03040080d1410850005102c500104580e01079230403060404e100c0700100c171003410146d101130048480000b80010300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 459618624 1250 459617374 459617381
    0x8090712030f18090603020f030a05030301210803010b1c060323100f06050f0102030f04090209030f06160f0e0d0602090303070c0806072307020f0d0203030d140a02040609050409030509030303040501 87
    0xb40c1c0248c4044041c11490410f050300c543e0002c00180481c1e00c20401003000903013071044040840b0f080c0303000003c4603a0696844035150700a9000f50300304100401c0082549610031480303072140c610032204108191942c0d5420b601c078000c44100410344810800c02107650042800b0b916200030a42d8010003150101c101c461008101c4ca00030180280000c8000307280a500010813110914100f007905810300d41703010a1800690720408116800d030207440345034540f0800410070540500d4072070390b84c3d1101d42001c540c02440702c118426924100800805101c00d07507110030702e0301650103401c084090b9984c00010013091541c81000d40040201c0c1014400003624500450401d002e05e601e07a4481c80c8045141c081103c0c003020f0300c0c0d901d403206901000940c0042c90038541109402401418501988406800007801e503048001910004c81e01e070684143c806e646010b02c2d41d44010188030840c00c0c14108034004041d11241d0241900695030345a500d024107001f1825504030100081c1141d40e07070b14107443d1182c043e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 459619874 1250 459618624 459618629
    0x1b03020d020f0706020606060d0e06070504030203060609040b040311121308060a02040f0b030405011107080a020f0f0a060510050904140706030c050a0507110a1508090712030f180906 80
    0x1402110000ca800c000040f5500d42240c06a5004024940340e1008012255015488440e0203d940d0205021808011b1114500c07a07400d54940e0340d255031440c010f0500786200100301c2071164040c1001c110018003e44081600984c061914042c50070300416003910f00000c02c1d03140c0030202d0303000c6a582c41c2c0e40580070340c2000b525800d10a94105403244105601a40145c1c01001807584094405100003044000910346c028082c034004940d031101c5184801d841c1c0d110940a03150742900040b00711415404105114080e0000341c0201560150680200d80741c0b1319160004000c2c40e01c4802107035801c4203217140e0402800000301940e02d903051078030705101d130307442084607000040c050300200203040c0b4028804d48d5040590b503104c031464602d050100720341591100f403040710a445e03600c19041c002e460f507940060280a01d070b44103ca0703103091075000de401c50000505003031480d0300031a000d000c18505840e038079540c1e50b85400c101d1150503c3e5041034580440c00b441c400021070b5810000034004401d9003180d401c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 459621124 1250 459619874 459619877
    0x30f0433090c1422060b0d06080c030604020f060702030c12070f0f0b1c1e05060f0405010b09040c0507060e07030b0702030a0206180c060309280507151b03020d 70
    0x6032659440d25032606102a03c2200d602c50140c001604c0c80d14140407072007003224090180020003948408205110350005400740c05243e40d80d003070900991404000300080044110028030140c6001d60005101c10080b1308c2450181c4004200d65045481c1005415051307a40202649104141e10010507529801481103020303000c003074900010b01900070002241a1861090300e240307050702c1914101040c000014000392803d0391980b0011001001141882c40324400d0717580400c0d41d003030010400502000000300c1070300c15803502004011071000101210a0328409a0300403503000030901d4207481d1400f5240001e801681010385248190720007080c1c41d0262442070300e01040356165050100ea9900507179040e10056803003400418601e1800500000110240b1022640700400020101d03c050f003054480501381c4d84481c09880012811110203c1d052000700218080d0f820240c071499922a001e01c59800c00c2c07500c82003c2d0888907c1a40004000043c8403100b080c031030441c1c0fa0095440300700e40c000c00c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 459622374 1250 459621124 459621143
    0xe0405070b0301030510051e040c0311062703010204050a0801050a050a020901080402010c0c050310140109020c070e040206040504180201140a0c0b0c0c1f0c05030f043309 75
    0xc100e503607401901e058039081001003a00c0203580302c03035000a0102800140c0400c0402884485c80c03403642807140c1c8a144070704026801c1ca451b40c0b03010051014200c060724803038042031040d40f10700451480b1001c0249070300c4140d00101f03107242001c41e00a03c10364101c150405116000868500c80540295006880b11181040140d0721041400102e00820704c10340d000844900110b1b0141d07203d05070710510640100c07542c14003140d4402c0003926005140c0c4112802e00c1d1912210036820b284c54002500600882c4400e40ca0159200700b01340d142c0509000714011440d601001c038056454503801e0310060b10018104104000c5241e41380d404c0302c00c8803042240081c081042c00108000604141c0300310b103202e62210580702c42e06075290b0724084070013032407805240c070180003001c0380744c10821400e07000c09a18a1f010350f446946080e090161103001e8062410300508000f80000300d07032f500d942e031580103400098103100400008a045a003034046010340c007180d040e02640a4403c16181d200d5960703030b4400ca1244 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 459623624 1250 459622374 459622379
    0x90908070b160e04020a09080d0e01022401150c1a0604050604060f0b0708090303030114270c07150912091706040809060408010903020d2706050d02070c0e040507 71
    0x28542c00201c00206400a810700d040000c0d5400c4c1a0060040c1852504000300c02c40d4075408130701e10303110310380b502d41c0000741c0b207141090400d503010301001030301c1c1d84980070300c108401400b1150500c0b42018400e43d140303c12214040780185114010860449a0081e81822020388002d000c411290081d6241442580303014082440d0340790912403d030844619031112108a45001820845504030001c196014034081105000e40d03642400103502038889a100d02d0704c0440c811052107110480141d1503c000d822051181082005400d4060780c800d9107000c455643d032115140030040074001c1130030f101601d414601507004100401c5240340c2d010300305a95004070680d50714415071940c0700c10f8203184d242d60009030200300450f51a0000f043c03108009841285425920300c1c441d07003103404910301a8010381210950800d80703640a070f501d0100344448001f014a60804a511070446441c5104000a100000030042049100d0f901920300c0183c000402c900d480f80d07a445030001e03001003190221024051820701 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 459624874 1250 459623624 459623641
    0x120f0506030c011202040e13110d051506010509090f0a0c05162003060703050a1a0f0d020a0b12010306060e0103030207031b0f080f0f0c0d020603040c090908070b 71
    0x5503441a000100140082c042602c01982d0b1081c0c8071003000d03105602000b010640381c50050056005943e03000701c0525094240c1800ea1141d0031070200079106010813140d02c400b00e103001884c00c114403006d1502d0100b507180c040040c0d890780f04185d2090b400400e90010032007000c3d20402071510800c0c90000c14804040b01c04821035a6200b030035001c0e030441c100c004a040110780f0381800c40103440040a00340060040308400a0b18000b003c41d07070040041c0c2c8803020402c0980b464002d1690700c0030042d494207000c140c1b607800103c004903105110b90045c101c0661b00000e555800c0e604000802c690005a9075440c0340001101144409000550350581400c000041d50b1100c0d04a044c100da0b099409403143c541150385039008001960343e00428100c00c0b032b1011501540c290070301d200078111309000b89146080408034a013080f880a03020031086e080014004c201c1d403a01903080c11416411a82d00c1e64aa650349880c064655040e0030100c0818036001d554000c01c1940c000038081c1ca80540da0030744195a44400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 459626124 1250 459624874 459624881
    0x30501182304060218010f170c0d140a0c050322440f0f0d02040302060a03020d0b0904020603011a0c010c0206010302011116060c140610090b0105120f041b06120f 71
    0x10890001544980031076209180425001d030003c0d00944c0252411745c182070034005403005461034100c030600b2f502c180102c0c002c1d6482040d8240c0c0840c01d00e64154900400500c4450604a00f0341c00400e080c0d00442080141c090f036101d00341502e071904102e00100c0c8101d554117000050103004030141079440303010350303500010050711107601180e00140c1c40c03d01200d81c685040e800c81600765400d6502400080016a00c56001d07000245050758016122240c2d00e40c084261111203c0c054003d41514007031201680318081101e042d64403001c41e403140c1e90302040c25070750144030340c0111a17419482e160b0740c00102540422218100c034001d0703881e45075a23045104540d446143c1c0308204c00780c402d050308080180714051150324550f14011010800c03941603800c411400c149084842d40c43d2801c904106001c4100d80740704072682c2803c2071034864105509544450040c000140c818195001407070005003c000048410740070150602c0305200d4802d640d42c1014010b4a400c85e0b06009032400c0051243c0658810710 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 459627374 1250 459626124 459626147
    0x200c100c0206090f0319030f0f0513050120070f03050c031501060f0c1a09071505040314072313051501120e0d0c0203060703050118230406021801 64
    0x6018514056100301003165802c0e1813210f4940601801501c1c5081064042c0ba8111070b80c06a02c076100da0b510304c0d200c01484280706c84820400d1190a210017441c95010341e903d40252402802d1400035402c1c400765000e00d050044603900341502c600c56011030801140700142d82100c1c8034108075000320078030400701a1642941002c14990004600040056078801c010002c40ca590f41e003400020f9203c15241d1042102d4035001031078982c0300f603000f40120101e003004000000c249017100ca4003410a07c4a00500c1c1d4072952201820106403058140841481488400018040040e13006c0f1900042d40004c9600c0c510f003d45103105d2885954032081a100a02070030b0b00c200c1418440480f03800318440195030f007002e41709811311043ea9808441581c00810000c071030b490303502070700c9600010341c5610405180ca00000c001400b09420700004100d40e00c0102d07050b60784021300100c040360581e07440e0200d103080c1240391041c10800b0481e00501040c0709056000b460008c0401340c001c808a2520b0740199070315482c40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 459628624 1250 459627374 459627379
    0xd0e040f0c030b210d0f05070c1202030d08091e0102091c030305061c02060d06080106080f011a0913030c05030307030e010b03060f06040c09050303120702071e090b01200c100c02 78
    0x41c520444170b8800d0344100300204c0541003a5050542541714010501455004558502500003214080d86802c00c12104054114502003071180b500112264482c0707403040366245031149a5070842c0b0126029010380d0780e204d4010f40480310302c0c110f6600402c003805100e074041c0d012030318081c080f034031501b8110302018160302c004580c0c2c100003400c0d5007448410743c420b0511481265031000c0100d80c0d42004c5c0034403001410b055005004445086040d542150000400a002c141d0407200768012911140f03c3c0035031001c028910820a05070358202550003c01a410003071403404004100030216825600404d00b10035204020042e0750f03148000d05544207001e4460728030005880001418920703043d08551140d210610380300400c3c030340d20b802191540e08000900d01001005c1000c0110302e5604102210040038041c103020313030f4010413111400b0784140e24050003001a0326002c50317111a90050000c1d90b942c00012044002e43d0300a02e40300c1d926044980c842d10300c40c6040316840c42c03c80d8490f410582032144c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 459629874 1250 459628624 459628633
    0x1b0309010504050d15050903030105100201020c0712080403050316150b010210050603120301180c0f1209061d010903020105011e0e04020409171312050d0e040f0c030b21 74
    0xf00800c20990034900041141e111044541c1c4466822290060f0782c012600d10000390b1700d0f0350610302008841d08050102000f1603205000603181e8a90001c2c42008452082541c2000c40d0000e0620071040e115a400140c5248400030350410050202c0b1209441d440c0240b200003e00040c000000e02134401402c8642e0041e48110090b00941e9034640c80b17650840c82c018100c82e42901030701c017204c0c800e4109a010071480011002540e00340c05c444d018007102845c4910740481e071915180c10103000310320000b00c0540d00c83d1350344207030800300441580110094010800300c1008000d0384002103000e4403030302804500650825000203482c4082c500d1001068500300c43d48003e039424a82803030b611810050090b40c0c0b007511002620045520345003020801c00014078080d64400304111100f040d00b5290380100c00303052071189030101207803001c02d0842e41c2642c00d1514044180b80d000028001d4080449800032852511b1036040c138590701607210420b00f85042e100342d580c00741e050501c1010009105980603443c1c20 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 459631124 1250 459629874 459629879
    0x907060903051b030c04090b04150603080423090103080c0f030a0c060b0402040b030705030f090a030c06020307030b06030a060905010b0903070501050304080403150c031b1e02211b0309010504 84
    0x103000c800310040f0100902101d002d0480c1c02c001400b80e48500c2c03420744d60441e40c1da01340400d110060003401124100d1715020300069195989107006842588600f400240c0700795180644a1820070700d490039900c0c0148010070380c0d41c580c14411603941c0a074198034200d00c166216110303c43c20200c01d079074040206403205002d840c1d050315044041d0441c803c0d15503209608001c0410803162110145000d01c900759280c0e0317200d1501107070b4031010000c058400301e4039a05c8000d0410010f030307001d49070b49200d9034032007400760b240d846e00369065000e4184030415903031215020041203001c1d2341d039a00090444152040a00039666036402d42600d0384101c960325074040e00981d10502c40c2c2d500682c000c5401511a6080502c2c1c04d5076034960281440c1d001b4824500c5907241c0c181c0c0b480e00da5150107428840440d840d583c0c1142d103446940a8160707040240741041b2005100d06042009009000312401501011518032a01c202c06255001c540e12580c0c40074280d002035413581d408000c000050340c8054a06850340b0346082d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 459632374 1250 459631124 459631153
    0x3090c011e0f02010207060c0918060b1b0309100f09050d0206040302060f12041506080327010323100b0703020a081c0e101a0604050409031107030308090706090305 72
    0x1140240c2d218207564081021000240441c401d11380c400705580c0d03071079480b94104229510300790611042c5217902030401d601440075102c1c010480300b0a0300c0762020050070200350304c856411405040304c9a40e02c002d0031001c500c40c480d005114403801d24a0790751085080c9403240100041100e00b00380280d00410b09210600044c20b040c0000c0004840c40b00400c0c0c2840f0740d65510170991042243d049514107000103da088241490003018080c2c03541001640c100340e5945000e0701d2a09200030744141028003883d00180503400f035442076801001410403110b180d03459956400601c042902c40d9181c1441c0e107a0300096031186034064560140d80356029002410f81500c42c90180e0300562424545142810300341c4500341d40501c100190381d0482d1001c1c182401c80d0542010840c4c900c002d40155a020303001440043d030740c0b041c0448084e01c40c1150300051021030f60508541100d1b81e05003c1138648248403020040c190044240340c42403a2a80444075640c1d103031101128480c2c2203200040503644054000801e56 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 459633624 1250 459632374 459632387
    0xa080c03060d050601140301051806040f02040f020a0315080f060705031012050609011a130905120325020a0b07110c04110409150f1211060f03090c011e 67
    0x188001c1990400c40b40300d40314281481001e81c4039540e41c20350000c0280307240c1000e014007079106030600d0590408090350792541d0f40b82c2ea0020301c010103181c00c005620086541b540e01c11a443d29861400310348614201101600800c039200340e44196034031047c0c00040c40f40d000030302d14a5075a4601e000d00080c1d21008001e07101a00054000084031004c1240030400700c98108204551a0084004080905282d0401c82c21611000141d06092031071602400940d2140004800e00c071000b10800601102035040490910268000c079449419000082c0220b8a05900400005121022031107144e0313032660b10282c6e40d44c0c48111004000340304000c0040c844a009001543c40c01c0382003170990f40328420b5200020200c03010b60350070b42e0100b0f40115041c40105042d224480c2140c0541514102076030600060312824140c0f481060040700c41140c3c41c4003080300c080e413044403840000e49444d80740c0310301c1c83e480140364008580020b0f25214600801d0030540c07081d5a100d0045000a00f10b101f410300c03405044604 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 459634874 1250 459633624 459633631
    0x5101205030405041803030516270503011b1d010c0605061f08010f0b04050604030b0903070606080304152c0301021201300803070f0905060304260a080c03 68
    0x40c0814000000c02d034403180185e400404007441110801002c6240207011a44050400044e00203204900f011190f0005e100e020014041300300545840c41c1c8010f405610f9000d43c000b0341c0c240d424603146075491b0b100c0641c21303a4400c000e40c482440300a09024940c0c1e07483c854a4a03a80090180302c1c0e2140442c0c1141e11240e0008070280840c8075885462104a241900501d0304100241d101c01c0104001c05102e180341000d0034101507000d10300ba1402001500310700450001400588036440411118070307003001240c0e1b80a0f4071402c14070041d59283c1ea019240e03080752050304a0462454080a03040388030b000d42e00da60b800341d032000d45d0f401c1d44040c80d03859658108498068156608010454a960300c003c0c2c510700030600e0640900400c0c0454000c02b0780300541c0d001555028290000301c40020b81c04000742c0f80d04c4001854040c40d020010002190f2010840d40b140303801410000601040c003083e144052186908024102c442050a8514035058810400e4890010388a03201040300c0c4540c00008541 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 459636124 1250 459634874 459634883
    0xd060204030b040f17120c0a030603020d0501020a140c15040303110d09060c0c0b0a0c02070f030b150f06090d06020409020a0504060f020303060f010e2407020112051012 74
    0x1065125070b80c41e00c46000a8a0550380098007050800404c0340c01c2c2c0c2091510349000ba1168104482c1000c0c0725445040502412521180880c02c0c50043c2d02c6540f21074001e43e0010481d020a01a90030018000e502041c101000904000031012900c0440c0040750001d0108100403c0001c0d030811608207002c8000d4021002c040d2201c1111803415014005088400c00c944400181c0c414030340307802c0c0d0441e01d000c40f0345414804403d083d0b5000c200700b10702c020fa220060b10b80106055601705012030500740340e50009840c0041159000c4140070701120203a2149800101a080544880003041050061201042d9218a04110041a0b81008240c0d50080c2d8424100513007099101c6002e0404d07600b0071044400003c1c0003003801c2000603400f48100c040c032150703400a03600d5400d0203000f080b07008600003411070500c2101ea0107020240ca8017071024510b1040540407003803568204950480301d0303102c1c1c00306038001400c03020082c91480f00d80c41028000c0104018248103030b07242c201c0081311580d000d4002e66 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 459637374 1250 459636124 459636127
    0x1e0709050609040b1f0f0e0109050c041503061211010f09082104080709090507060815060c0c0a15110f1b03160e010e130327081606020f1504020d0602 66
    0x201102c608291070300c003a00083c034880300101c1c105087d400d48048141d02c0a11050300740700c00d0041150038541142c1c10b0b15181180c3c5059515151025005030006500085080b00300110050074008914640d450a1800340d85850803030003000822a0140c06070f018042c170340d800004040d40804541064002c542010303043d001d0070030365207698440c1460b60703542c408143c0700c0e00c40d9905003c025051004102400b0942000003041c2400031415041c0f0403680e4005002d400c00040c01d0140d0001088164280e090061043c6109a2160300c00e8141d90b6848031040c000c03610701509800a110003190302d0001400d0040200203005c04c940165140c42c1e41002141c1d0540074914814290b940980d450302c02030800078040b203165514040c0351103182c240c01030000900f03031104201351002a500c0100c503645140f00e0340320101c400b007180410709120075a50b0f10034a494401c03a682c0343c1c555110b00c0f1840301150004e400755003c3c524449461615003034000b20b03055000c14407500150051508501201e9850301400e40103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 459638624 1250 459637374 459637411
    0x605091b1e030a09060501050d0f060c0522030c0602030708160305070b100e061509010c02061303030c060b0301021612051e090f0103060b0906090d051e0709050609040b 74
    0x30020740d841034580302181ca4440c42501c003402074501810f801408147d908845074407158844102d40c03d125000100322075219240c11200b03a200d0301c00c0d48c0b0042900c0650943d0200e04280c03180c80d8032400d120031140d01c0c003040b0000590310f0021007524484d64020f400e4500e40700418074150290303800c4034022000e11506000450107d00c41503031503441060f0740061102c0841c241080040c107000001c140a00c1400c12103040f010305c01c10503060791072007038081c2407004080d24030b840010503601608000010035440ea030b0001050550054a00d052180280b038200310b1030b00103c080c03609034801da001c00c07000e0702003003e0448001110440c040b0a0280d80e13143c045d040c200809500020780f02c0c4102124103428020480e4001440c105506136602c0900342803c105aa1405c80c0104040c0208021035200c0d46010400603c16100c1c4040b04020384d44c810150303490754081d080030b20120041c5422a4807144142900031800c0c140c240308142c007941c0001e080111aa80b943c0d90128110300c000c101101d8600c5075200c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 459639874 1250 459638624 459638677
    0x150f06210f110403200619030902040213030218041101120216030e01020d030c0912050c0a0617090f0a020f0d0609111509060f090307080706120605091b 67
    0x81003000480ba5005595892660400306010650709000c10000000394140d2040750b941c41c001ca41c1400d907038400c2d40c0d003c0d61250405500510b070040d0041d402c58000240100000f101c3c0e000807041d644221030002c44000784616107525554226001010701400101c0404190f01400c0785114410325030402618001f10446085168032441008802181d0501010440c42d0b80520810440b50b007223240400031300e007115000600b0311455200c1c40304150116540320081c03000500c0ba04810b000094101d110f4140e4542004041e030742e090541003c030010903004101400c0b03003c1881d00d4562076402c020b00c44203040c0d808102f031641014010990103124000441d00146041c01280d00081c0a1603400140004510500a40324103061541aa4850400c013402103075866209480d03848026504194030b4043d440c2c040303440c0a125030485c483d01d1003141d100142c06a800f401d0720700c5d520540c03401880055035807c1440103400f802d4038207051801c50301c0d00f0a42000c0040c8040d002c003821029210170740c0c2105503038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 459641124 1250 459639874 459639881
    0x1050c1608130905011d090723030f1501080d08060108070c0210080603060618130204020705030408010608010c0309020609010305090106050a12110a08100507020c06030a150f06210f 80
    0x203e181d80751130040012118452141103148902809428180703045140d860700c6001134000e1545044203d80318500075690081080c04035280a03040f41c006400c1c80c001c050356203070154205032035403002d00c1c00402c06540100b482000c0c1c109a07181c4686580311a0015501901e00900607070030402d6207407140e005a40d81c00300b51025460551503c03c403a003400000e250501134020034040c0034403207400001e1425101c034050140e000d01580c201401002881c40002c001e0310034a403015103144004100030400036410b41c002000c1b1608203008001c802c0301036a068060300c00c00d400c0a0750001080c03040f0310455000b50051a8415500d01c00000c000345c440000614082c402c1c2c10217800c02c020ba100c038008008131000c01a91401c011104210518905000c0603642d1107155138403141035072036002180da818003c006840041d8401451035031070380b03406124440248401024000c004084440c0090042c448440311429107105596502c1c5500360707000304200b080d601001088a141d6a5a242d00b1445003511 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 459642374 1250 459641124 459641129
    0x27030706053405070f0f09050901020c150906011d0105010806120d03140a020301030c030305070516030819090b0a0507080909040606050a080c06030604050604090c030302160801050c160813 83
    0x84684820301d80d400c0c40f500d094800e0304550007007101140d00703200c541701c100340380000c5402240020505075550066140a80031709000400c05d0b108140c01d90a0301c1444100c0180318404680442d09603a0380c0380001d50301700007040354013491640d800e00141701952040e440300740e100070041c00304280d04a14802c110f2500608500716400030780d403210300300342c1402c001d920715401554402c825401c6506503141c95011150b0b0380710044c18050b0019014007084003c0c0022a80007554a40c040c0c07116075603003420f141a42c401425903000070940d00c16036015600604c440c03000d41f44a00b0070076003009003842e810381c0c1c1640000c8055500c9501409500724543e2080c001521903442008040780c598500f009102c0c0e0040a90000040c0c1e0b044140c40c0038042d00e9410980703601032011900401c41d5115400460014003c1800103440302d10210008004d05130005001d0103041410030100081550301c0518608070b075420354101c0300c021010003685105036800810786100d075004480c0940381807440541c02c11021150f6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 459643624 1250 459642374 459642457
    0x71e080a09110d2a080601050d1506080a0308060108070903140a1407060e0108220c150e030c0103060506030109020a1713020123070212030f07082703070605 69
    0x40c0c00c541130220891807100000d1600d1a00544061300304203200d40c580105015040c01000500c03810750038001d090090302c43c0e48490b28000c000ca07544030a0401c0d01d802c40030105a0110700002c1c041050b65108140d0a441104c40341c0e1180c400d0350455480205441002023001018810036055001041320880031020503032004004000c201e00d000703005800c10071428910740c14003c15008000b250a4a04000c2c0303031000c071840c1e900300007548616140c03035624283d8200400e002640b40301803040d00d400074500c1643d100124100c03080d10710060011400d8800754081c00b07400c4441480104400b500700d0b000740c13000c00400e0a0000b40031000400317641c202182100c4064400c0c80404e103810955810011a0588401340c0e030303000301c440b84900c40c0d200462041315002809000650b580f460020004d00c2038030034800d40318039200d944400c0d13420402d080f81c01040a060428954411189800c03038019102c02e40c2c91406400342c148585814820743c0d154005c0b00043d6040746107013078200050074030038660031280800d9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 459644874 1250 459643624 459643643
    0xa0206090601150206130804090c0305040611040602070e130f05030d0c0f0c240f1406030109030228080409020a1701050312250803071e080a09110d 65
    0x2440300c98900901030f4811424401e4050000c04100d83c003190156104200505c04000c00d00c507858602210720403a03110069191805041140155160700000c2c06103000d903400340644e5180c900306451034401c3d84140c00250340109410070440c0b040b411035550081c6090500000d146150f04c52045001e4411000ca40310f030030008281038404624414441c20255616004e001003100f4280a050880c0741600540f2a011005610500e6a4102d42c00b668400380068140f00100d0002212400780601e01600341c150041d101c0001d00750f09051141e0402c0b50780560042801550561960140128510681c3d079905e0360344004402140610005100a0031b450364016656514000c0013008050501100480b03640d18a00410150741c0c0002c80c0e040e10810f0729007036a03603283e42000d0242c0f12980c0380c00c890140103400310b074a0248014200917511811142e110030b482d00842000310206114000310a001190341c2c580840c1950036183c1c041383c011031241c1c509107003001c609800508030a0800750308a0717981c0e00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 459646124 1250 459644874 459644881
    0x11070f0611010207031b080c0f011d0a020f010804080c03070b070809150a020c012a03110f0414010c052d0304030308180106052805120a060b060c030a0206 68
    0xe02040110070041644001c60408225650040039040d80c0503449003001e07000348404050106040c1241c0d40a2440c0c4103c44591084030380040c082e11020064041c0c0d180d6152103140b00500100700303012000ea00030310030700c03441c000c1d68010740c1c885601900949061100303011040e4025010402055800c0c080d03c950001c40c50715420081444d00020312a1003141c106503191a03220000f00c0c2982c1d00412070307482c056284e040f4400d00b20300400621160340101040c00b020b0b41c1241203254071810009800ea80d0901400b05009200b551728404c0b940b10000030442004208503108080321034a1180c44145080010064140c035858544030a5407110075256684016046030304030011155124840c9181c099800c1601e0368402902d01c44c001003100106803600700e00d000700303640d0030340c0a00c000d450700400c50400344c8030b100d004506480c04103071030211030310340f0340400700d81ea24114607100300c501900c40051a00c8402da40d03034103003c0d105801d42c91b80c000c0c2c030501510303440c0e80b41030002d48200000341d40200001d14 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 459647374 1250 459646124 459646127
    0xf030b190612050709053103110114060901080607090308090607060f0f0b010807020d230319050c0414130f060909061a0307060815210f0c010f0c020111070f06 70
    0xb040900042442400d02c40114144860161406000703810911047d0000040c0d043c2580d150301c80c4c6802c4049540307480ea50405403501420300b5405580141e0700244240c1e02c0709002030342c841c030075607850021882c8840100000380c80c1030001c150003500640540c2c203040705a07591000b41c51155050030b0f0510b8595907482c0400031180705013008414246811085400c000c9030281d12405100c604004015a480c2a819001c2c1e010302d8142201410102455885c640040c910041804d500c0e4402011070400012801c000441800d13207040d60380070f08010303030386002c0e8508104440301d411810201150710342107050001748491103144010082e02e6001318159020349484400c8036850804885004040308909002d81c8000603a5420307617901c0e060450303090710340d118010001e4030940c042a60250040c4014041102e1a0003401401100c58048400d0f490305a1a06034803440b014441600094441c4500500c03a48a507000700005030041c10203901400d11202014100745194003d820b03914201d040400071907 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 459648624 1250 459647374 459647381
    0x1501020d0201110405010e03030415080414071406030a0e010903030b101407080c1905150c0304030c03050d060906090504110a080601050d031115060a0f030b190612050709 75
    0xc0c0e501c0200700c400700711030701111580614000c01d410440f8090314215251402c10441d8080d008a00d0809900c0d5082c0c0ea0041405008071411214000c0300c90300c1c100c8250313002450b9015541078100106954070800c0c14822544c20003048070061030b40352442400050420700c03414400034084d0f500071a10194000a004201c1703900d1605d10200130b4184e01248190318108140d400c4107600102c8a9034941d039a0855030316142196003e03100301550459800d08002c0001148006011464028581c603981c07409448904e0008881c040d01007046407080030002031042006109000224000180c4662190000f0044403c1c6401c0b000b1040c1c0c1d40d200740310a00c07041d0180e0307403400304085514082042c1000c050b152582410b10600d030060044211010416025500f500d0103624204121171480305081c0c2d5150003050180d402601039035201201003460a5041c0385031003070303035006021580151a05080c24414a082155040500d95100800300d101441112000020350141c8001c200d035a003405a404101e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 459649874 1250 459648624 459648643
    0x60907020c1509031c050c1209061204051e070906080606011704030507020904060c03061406121503070b1207020102190f0c230f0a030c020603091203150102 69
    0x65601101c1c210000d90368190600c0c80d002c00040000307440300c03032030000b1030b10f0720703449016081c00a0080e046140085a1080150041c0e4100324112040c40108025844091040003804d42d0400030030444d5220046103d50709580151084084070b012605140400e00c480c410981a47c4a40e00640000c000390141c0340102d070f0203441150060a91801c0c00c000182014220b40c20a40c10322490500140c10b150294054a501d03d4018008040618051030001c1c01000503411440c0428600180412160301078407006008a00141186143c058480441c0752401401030826210a400709581d40c1e4546051080c44000c03c00c240c1d142f0307160714a062296811140081003001107a106101032005c1d02c048100b1501a515076040000c1d003030384010b0046400c08511740000e013440714084050b0900e08564086003030815120001e441c01423200100c0c0d20340340d01c1d031824081d00003140b1400603005071500900445d08800120704954150400d07401d1103066800417900514144254960f1455651301401710180 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 459651124 1250 459649874 459649877
    0x20d020d0e07080c010c030e03030307111603030818030408010f051e06030706141b1b010503090604020f0d06180201140319180605040c090b0a0b04060302030703061508060907 77
    0x1664140480982d130340c410807050904211482d410034007814000c0300d010110a00140c2030b00d917a031810039009401c41c00f81444c440407510850300d03410034104201e012502074030360643d100d00d5103403034654000048809001c880c85060004000c001020705091040c08c1101081042c00729052070050f0150f41c460184101c2c9800c040c2c4001c08208040d03402298070802e45605040103200382c0d806510401890203610304064500c10400c00e22600344000103584a0040305c110700201070150300d40d004440c140420381e5551a154089004a001490030395207010200d84094100c5203400042d0319094240c45140d03c6104180d03120020141c15560701c1034003031a5861820760010300e035040c0042414408412102c01c103401c1584c0300b841604a5414110f8030002c00d82164040c03206082c5420400d40402d51407055100c00d9250884007003044c10003c041c00101c81d400341085080901d0000c007940030354002040002056600d8070049402d42035512002c05640d09a41c03a14024a40342060015400c00907003c1030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 459652374 1250 459651124 459651133
    0x9031906061719062003040b04060c090f36022805030f0402010e0607050f010c2d03060905070203120c09030c13090501110a03110304030c08070c0801020d020d0e 71
    0x680e40d5581c50304010049031302c200d0005443c5a2001400070045074a0071a0020420020a00050014590110340560700501c000c1141b403030514030a507202241441a134200c035180c1d182c200103480b400343e0f14254840340211005c00c03e0312803d140e908600400c20200701080c1c0d0210b41000e0b0341d00c016940e030071802d140c07810440200c40040809801400001c0c400100c15500d1030025045900c204401c5040c20000b41619071510f15924106403503840d291a400a150b18181208030441e11410032000481c500307400681d02030306950f9140c3d00c646041440e05060544030303d8005000040d034403d0743d11443c0168003a584508054444d100d0019011344050f0a50300b060014409039540070901710f0015804552440240c02d0f10070340000a00541000501654a880c3d070100c2c540e1042401402c810510380c0c0d0802c0302d01c401e00f54244150006650150014525620707850000c0c480c0c0e0300a1290501800d034200c0819503410031035007603034891900041c1464020031002d115609034010300c0c040c8500301c000742 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 459653624 1250 459652374 459652393
    0x807030e040506090f1015200319080705090d0308060103050a0b060a050a1107090501060908030c0d0f0c060c0e0a0e010506090603040c0306060807032a0506090319060617 75
    0x5079000c0c00a003141108406220209020143d004901401031030030000010590b6200d040103000039254034050352480d4050280c0b042508c0011003100e07814440444402441580d40d00200c40d051801071520040c00010070500e10507680e041c14040801d0310079503c10a292829000040c01d44d40c003c2d0140d042e803801c00b00003000e40c0c0e1fa050241c1d0402c50303a924183d9144d181c0c0b00c0702140c4940140241d41c00760700605401203405101500100d050300c1a5481e0040032950f2000c000350740e48112021039150350800400b41303131164440e10001e1005081403a103c546945552912000c80e003010900101090204110392800d040042c070080003450f0000320241c030b0358034010115440c1e1040e4000180304250010004041122215108000e1f40d0411b80400050742c490071515658051804281d0f04000011224030b1900d010f02c2c0000703014982c181d030302142a0f01d801c1c14442183c00540106516001c1c0b00c101880c0341c841c20280495440c025a40403c000303151076007290780c28042e41101d0b2456000f09040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 459654874 1250 459653624 459653629
    0x5040e100203070e06040e1e0c03161115190c05071e0c0e040b1005010c0201110304080115090b0a0320030a0b1e01081c0503090f0304030807030e040506 67
    0x203200d0240600c0c48090303600d580c0c10b84111200304140307910b01c2d401200031401040692401402c14410b50420120240608200e010030b42402d000303c5890401080810015145007101c1c0304059040070503007000c5900d41d40c4841d00e01d0604d62310f05034210580c020f4008011440071000c440c245405a0118108900400410000e00301c0c428684050071003851001191a8086015100040740e50001c80381c2c100280c450744d210341e00540546043d0783e00500c1c1c00206207140480385000c011210141c4403080141020741c01950201d0303815002c0c5d0102d001c1844000707211842030044002c0c0b01580e28010510a08201100e4201e134444039080d070203036144c440e0500c00900c8060700c002078100303d421b89156090032440000d1400c0390802c8000c000c6c1c20004107100c91030018481c40c881100c0c8100070341102c0da17207a1440f00c1c0d590000384051914109500d14452043d0f006d00010b540182c0300c070007610040441c8140480ca160f22561049030b2000000582d0070905600003181c1604007001c4030240401e0400800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 459656124 1250 459654874 459654883
    0x1302070b09250e0c07060606050406020d050f3a0c090812041707231e01020601060c03050d0e0604260702060d23090f0a0512090d050712060605040e 65
    0x154903c518500404690194003100c1510801980a8000e0191503110302004100740c009200e071402510844030324002844c0140c080d0344840e130740c80d000b15003004240e240c8255002054000d07050b02c02001c0221080328485031590084030841940d02080c10512640000d2599040b644a40703915004160050f02c0201d880f0121000c5a205540700030012a100b03404d0350900c44a54009078000290301c440700300107808019604004002103e8192102c1046c4071001c80c50410440c8160040c0c21140c014402c290185803000c500a000340341282c180000b02091608840203207000140a03845881000100078080a60300c20307044946104503004006241c45401c2030060300741c020f00c540d070045411602403c2c1076028004140c3c00c1071000608403800025074420f00c1065941e1580e50091541001e01c0d01c1d4005164040c080d403081c000c0c50300e50028501c1140036004014000c1d40419086182d10126000b00540300141880404803040c103542807500c3d070212046503010350b024074149618407504200106 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 459657374 1250 459656124 459656129
    0x230109080415120204090c09080c010f051e031833061302030711010608010e150a021e12160e130e010e010911060702060d02091302070b0925 62
    0x5041190310103200300142c54002e1070a003c82880d83c0302003070000e400000c0da0485403245402d40c644003640b40e00d0740d080603116035104101e18049142e00c118107584900c1600200000d44a4034261003200101071071041c007907030054989469404410b45100c40b902004c0c41000e01c1240164000c8480300043d20308103071900034520f61801145903940010b0115228405e882d190911081021541c2e0320b401000542034140301e05289a044d803038070ba400710f0076110520459640c1c0040d00014400350340c00180103a1138030340040140d50103a40a11207000194000300702c10807a003204141043c1c5603e4405000654000e0040130b074414154803600030381e203286d08565035083e030010544070a01c800d43c0faa070744070700030b4800301001810030b628003403110700d400e4019400021002e108011080c0703045171180400806025940000c0c0d8000c0d410801ca6202413820390082400ea50083d09015681d200510007504a0304030240c191011800300041160108083c07041e4480340c0284c0c0ca1007140d00c0d100140c00900c02060b030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 459658624 1250 459657374 459657389
    0x30309160e240d0f0b070f050f0f0f0307090314010603020105030619050a141e060910090e0c07140601060e010c14030406170a0b0f15162301090804 65
    0x2100c02034882011030b078441100c464040c084074a501200d24101c0002c004d0404141c072065401c40120700c0542c41588688050b9070380356643c1c0c2c1807500c20550240076900411008030b400300c00300f142464810b00c6101070f40c8601c82c3c1d52612800549181040d2a005100c00d41c0d60410b1307454240d0030700040c1c3c1c000b801d503034008009880b000f0468814002d00410b241481c1c11841c1c1c00812007a000480c50b42d0140441c1f20b060060340c050000d80c803c8809813800c1211940300030350114040c00441d9040c1131100a061440060780340000400d5a194283c0d4250f04c0140c0302c0c0040c52500207008020f201c0116031104821420000400c1198074100340204001c4202031440c0c10002104078a105021a0110710b02080c3c0310701c0142d903500c0360b1318000035007900305440d9940400d079810700020700d18400503c030b4445460001741100c0c14030b0140e102006101c604a013201008110180708042d03a525589a058040714480c000c01928030190040d58495218803086507005070f0b04000050b0006103d04007a282100c208 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 459659874 1250 459658624 459658651
    0xf030201120203060f0307080d030c1107030201050c0a1502031e07020706030f0f0515012303040204020d0e030d14060a061b060605031902040b0a05030307110102070503010905030309160e 82
    0x1044d001590341c608010609506100300880415030b00c00100c3c0c00750100c607803034170708000c495814074042c0c1365405d0710b9901c0062074014134020809540900002c0c81900c24030000d80d40015101da076000c04030100c50310503a400d503902004101c02c001f100c00f220081c2000246800c90300785818607000b941e8035640c0c02400201601c0e00d000300700e200400d8000c100d0400011200380058074050841a0800310321006060000b88840c2039542e401303000b1900d52028000b2010142d18642c3c43d0740178840650f000103020040c2c255200c0305001c800c6800d00183c00140b14034400458044012121b1950614014040038441c1c10404810021765400000a1844013204807031a40b6980c50f038288500200b07030550019815000d1500310170106040c82c0d0300e001030325100319420010b900c90314083c03151607111400b800c5d416600810032980841e80c2c140d030fa02180001441101c0744680c80d000460309546640038201c0e41e5074404400e0014200b010720071881259048071031202e01364030b0031210b4801304030302510441c00c2642 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 459661124 1250 459659874 459659881
    0xb0f090111190b151203030a0506031e0307020901080613030c080f160c0614070b090f0304090204170321090705042a210c0c06060806100f030201120203 67
    0xa090201c0c14840102d1142d8881c412003038104802060001c8a0f07000b00714940042580c1c1920700301c00503410502c0c00700700860660381e030500500700901d00030380b07540c1c1d051007100002b48c5000c41031992a800072107000c014544590441c41805404241a040f031040c9400100405c0701240c5003440c0c1030102605458001c00e023203100d08180c40d95101c0c1c001400c4a40c00b0002d42039800c1c0c4019000800814400d40c10329024036540c020031105103852170880a0010003c202202c0465040715402d5000200710099410401d52182c25900d0366002e540081d54071078000c1001c00100100581d050600901c020285260541c2c40c01100b00d00b140d82e401c2a91408421400302e903003803c08000369806000003a000b0040300001c480c155104030281344039160144ad20510300101c442c800c5000d00c410441d00440d05243d0f290b000c0041025000c00074024080103c0003510402140b054041c0300300501c0d03003d0113040a401c1824901c80c2c1c40c0066004285070740d0840c002000183d9204d810068034036580b2030300503140c0d103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 459662374 1250 459661124 459661157
    0x10110a0c0918050613080c031305031203070503181603050d09050a0e06040207080c0d020c100518040e01020c0105040b010e0601170c0306040f0e100b010905090a0908090613030308010b0f0901 84
    0x14145a50080d8030002c1101700000c01e00c427001c102940d40c02c070111050340b03a41c1d02805031070740b1003110f030000010010b0012410031041006e40100084001055640c440a01849100414010703402641c2c1603101c2c20440580c90b400c41070400c042e10042d220389603550305140c4942841d00c00035007064040c580c00112b800501002d402900d0300f2000040c00d892036075504190083d61404940b19032803103510120f240d030cc2018016802c0302c800170110a8041040360303071101048024100c00360035850f2550204401360035a802841107070310507841440840d596506140c100780300003800403c0c06e414419180005030a25a092485503400260390841c00c1c0d8956070071002c0b070060100d90102c070040c0b605103520602c0c0d240c0c0106850004440d101c100300601c40e0144011640307480d6034410b00742c101690001141e05245540c0006000c3c5000b41c071410300d08029040841c1641c0d00101c4130f18240000f4450600416600440040c01020b4a92040d8200074658a00c1002482070180481c1441003481c801071307200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 459663624 1250 459662374 459662377
    0x31103011d0303010303140405090403201e0f07030b041b050a06031a03071a030c07020603131101021f0b220c0e0301061410110a0c091805061308 64
    0x1502802504011034505540141d0b03a80007800100c2c04036240801e04d2004038962070aa8046400051800c01c00b91a961010364614600c4002903000182d5250702c40d03030030756041210366020f00e42500c031b9016800448001500306007040c9840c03903071900314002c1000410103030720050380c00a400040200c0040c0751640c0b0741e5562600da81c0000d80007000c0d90000102290180d0042c441d140442890100000c2c074041019184c030b00b14042c0346c0d41c101003075034440350b41c032044030107141d106d192000ba091a0107030a400007040741e0000c0f68002c412a851590311000c0002c40c1071070310103400081c0002c00c02d1011012951a64801d50f5082740c14030b598680b10300c10b2660700c0000c59882d082606030701d110343c0110b411200700640110030b01400460300c25141080300e810144104800c540103410041441001d81042085a40c3e8056004040041a041854818006205d00410750f07116405002001e03140c19205400d0780c0d2138100354406024040395820100744003050b019071200000003503c50010b214503020525 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 459664874 1250 459663624 459663641
    0x2a060711010513151d0103090506160306050d0f0314030c0f0703030219120608060108070306050c0714011e020315040b0117182b200105040507170c0a03110301 70
    0x80c498880ca0a0361078940107171000440c07080c08805405130081410064007615540300c4010890703400003000940c091101c01803540c2c425418035001c03030620741d11000654200a03121050f1228120007001c4400c054010740304803000310882c10482e0031440c01041180300ca0207400c5244810100c00030b0344c0c9041510a5040b03c81401007203055008584013880300804510514001d1564540b4040c80400c48040001e00103040300c0c0d007400100300550a56607090058200600100c00314041032041c0c00000344081e84040ba610304900c00018140314034003031650751904000586107142e10410a000b40c199001e030b103245450700240c8000c5400303c2c2c14001280d641d89510703c2c07191982d180c5c109008140039035000040c0306207070801c01c4812040c003aa00046c1c10b031981c1045540203882c081d0209902c0341c000e65801c607041d0002a5040034150030252003a0a58004032000c03240c0f82c000101c03d01c98241c805c00354000251000004043c40c02c0c40c08003040031200140400707407100b030314030114410341d58094000307000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 459666124 1250 459664874 459664889
    0x101a090d06050a0506091308160501060312020102120c040506070201230f0c07050306061e06070b04240c091214030c0303040605060306040b180109052a060711010513 73
    0x102d10341a418030f0018241542c40707620030010390001c80c24101080038205046500242d00e036203015500c0740341816581c44414100c8665481d160004041802805000c0e0259501d400140e500c403540b40d0106072402e001801c2d808807960620050105440c0d030020340e0142942828403080d182d0305150040d2520240c8030413140d06100000d00b02c0000b003814070103071030315000000840700c0d11604c0307004064540104451082c0c104406230500f102c1c45180b100030350701072400900702ea4034081442e1110254080c0c111001c0e948045000321180e15800e020003000386080940908008884800d00c000348681918802c1c40400180c1617000c8041c004400d4000841c1040c80085076560200403030402e480343c00448066a10a14001c0001c113141808120544613941c0940307003081a6072591250a541e12a04210b03001541d40c1d92641d400081c0100404610100c0315016668441c041c0410240040c9041c1c2640f4000c03a0240701100000300241d1404103950000d00b401621110030101508525549610100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 459667374 1250 459666124 459666131
    0x1e05060109031104090c0806070c03080108210a05071a07020c0d031e0e0a090c09060302030f0109050711010903031d150112051516030f140609060d0f0506010608101a090d06 76
    0x2500030303005094091010f00c2f9468841c460baaa40d01c01c6900c50340200b41d900000c0d19452480840403210400510481d11341e030800f079082c00c00b9600c070703083c900310510009020440044248114250100282c5010400c122001c0491034110b40d03004001601d00b0304068607106030202079180290113102c00c7d841c01c01c8040d100c080c0455036007980c200075000c414100750105215940201e07090b846802228400d0220b070354a0001d5900c0e0000090040400412100c10001c1c0c40c0600b80c0c40000a00031260610f000c4d560124164100c0707105640d00180c851142c0d048d0313900c0104d20344000b005090b80075044a144800800c00b00e6081d040142c2000b400c149481c11414200d000c001d8401601100110740540ba079800b0000c1520203103c040c01c880584241005402c0d480780056030500d82009500e51000000e042c03002e4410595903015040241c46008803070a4200c0390050040ca50f02c140a5580035046142002815140400e50441c04010b000401130300000003a28003100d032600b045500c002d9904c0356080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 459668624 1250 459667374 459667381
    0x904050106060e030a111005040302130621021e0d080a03290303091509030a0f11181b040e011806060509010215191e05060109031104090c0806 63
    0x550007022030b80900008a120300400102c1c5040004408a041c4c0d4031010703d20480000e4420400380c807004403000800c00404100c0840140c6466054604015100030049455400c0101824100f0b0a00d192400c0300c00072007801e00c2c007603503811425020315080840045100a891008660700c2120551702134070300e10000034160074465159010388100702d0060b17003030303c4000c100d180b40f00001c04482c0c400c2d0b681075106102d00001454041d80495a00f41c0168004c0e2501c80c03c803010034108040c0680564650940880d080c0500400c24002207080d00212582c8000441c3c0e079000443c8003230040c00310a01030740602d540b010940d0b505070803038028000e03260400c1c14941e591050000070030300b030a995142c2c850a240d00068002d002d9401d481003001c058020300401c851841c1c02a1111000804051035411480c0f1195a00d081c50312841990407640e101501c40c0410201814043e42c0c00603150714100410300004001040300d40c0c0d50ba0101450459020400085c0d90501c903a07800076582242c03050b40140c5050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 459669874 1250 459668624 459668633
    0x12010e0a03090e070c06020c01061e0f0e040c0303110c03060a06052706010f0e120124030c03082a030a41070c1d0603010c020c10030b0904 61
    0x9020481e10a0b075400308015103400c0303c000079841c1a1240404107580382e0841001130490380140c1014610080005003151b56440941140d0215036002c090195202805101c0d41a0410108000d0003c460b080406803d280ea0707030704030075001484043d040240e02040b100074a43c0078403649403803034002012a516810b14021140081901d4441d151181d82c40043c40c0c207424018180700c0b40070608100f24415999164001514588112003c281c03c100618101c0d1199955046018000c045800000900ca2290034907115540700740001c0c0d10384d0094a0703041000012001c1744403405980d4001503054862550031079140142c1850709003000380100c454560124110004060328418030160f64010f03408082c0442640110700c24410b4110711040d07d4511680c1c155031240300001a00f846018914002d11901c1d580415912a0011a40ca80c852111810900c110400054010320114000c014202039070001030346d00e010002c021402501008003c1c04118002c1c0d00607004804c000d015401d113894145030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 459671124 1250 459669874 459669883
    0x4030c050117070215090f070b04060e0109240512040f02031018080a23090a0518062b030507050d03050705070305070516090207030305070212090f12010e 68
    0x14007400220180ca020007070441c4000c0590141000c1d40160001d0f4070100c041000241008262880351b114404003078514070010000e500052400d840241c0d262810100000d06103d20441c401d0304105274032a080c05050901a41d040c61981ca04000319518076040600351000e0042d03648420f900b40040b0100000c0c00703110f00380c58903502d108809032054039040d904501301302c1d0289a200104007900904c22030004200744000c00d030505180c1000c14100c480d11a00035054003090b652022803400200b00c0c1c2c50306007400300c258000b0780801c0b112000e40c101c02614403c03022800420745407103208c9032500354a800c00920404400d00c00560035181030180c1600380234090354400d101c103c8191090f2441002c10500c81d00c2528094403556544610b0b11009031400c4407560000c6000390b039030b805000c0360382071000c1040410b08010000315001603111071080c107014084410090200c0103640048a000c01c11070308410843e94207171021a61085081280c41c0130403501d070304180360036056601c2c1c00c0b06a640e42d0720001d03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 459672374 1250 459671124 459671129
    0x40c02030304170f0a0e030c03072402150718030213060f080a032304080d08090d020106320603100f060e061606090f0c080d08060a03080f04090204030c 67
    0xc184005400104860f00f140340724100840345080380034081c441c1c00d00e1180d40000041c400040c111030804000c10002030400140b9070190342080e5541040c1480c1d01c0c0c09444d0882e0100150010304000201c000d01c5902810005000c3d00401c89001b820880c40a40d00f10407101443c0c0292611243d640a05480c800a02560003404003c80e144040010b240c040082c01c4c0341250b515549450382d03624a41a0813500075800c8200403041c02051002094001d010441c0d1011007102d5518039899040c42004107040a903001040011641007980600c40700120140900c1c05140600341c0c7c175501d950311451990012201d40100c3c0d40700c5400814485488449400130b000d46440742e403000aa2a90b0743d5043d903009071142c81d000d81208090210f140107005001c80c200f11680551704c041540320b5213666610707070004551021a00c2908845060004240c204410030140d11181006911402c000c0005a987c0d00c1d2440300500324080080c85040d0390108800351801055100802d54650b0b0716864803580711200c60 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 459673624 1250 459672374 459672383
    0x2f06011406040b04030305030c040b0a09171c0e060c0303010e062d0103090809030328020714060a1e030f0b04180b04081b0109020f060307051b0705040c02030304 71
    0x3600500440c903065040b24201c076101406545014696641580c1540004112403e00c0300184400030707801d84904c00400e010000d0f40ea480c038840e030504841c20a40713100018012903550203d41c60702c2c40c2c0e4038040c0111052102c9801c01a44a62113100069494810700742c01110300d0001100015150011020281c090710045459014601000152091911088540344c0c81c150f10190800265400380d0702464410340a040540c1c60045c000006c2461507100d103200c80c0d0510324816112500b0001a10b490508091602c0a040158034120000124844004111f0301c1a6400916502110b009405100d201c1d8003500d103000740030100742806801040324030250b4280394200010702e0b0081c038092155520a660079580003103601e10944400c40f0401000780200c5a11001304018048078424006c41d408400d07000002041e1020244140042e986c12500704a024100904c2401041034100c0c0c00d80c0c40c15208040031a6144400540480c03518040740e10450300240340c06c000c683c080340d0120040d4410b6009 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 459674874 1250 459673624 459673649
    0xe0a0614090a03051e0706140613020301051311090d081e1204330b030f0309010e120a0218070e10050d0b13180308090102090609012f0601 61
    0x807484102e0b220380c404200103000880401032203144804010020107050b900c07a07116410070302c1c242e403000100c6510b51030800c04001c06c3d6081114601d0702007101084108156170540c05c5525100c00710b49401c183c413010b2480d644d203603590b42d200c901c0c00d030b41a42c14032800101490031019650504800c19404050b0783d4948240c0c0300c5203d03100d208000100c801d0744010f1501d6890603038440d00c802c10340008407165158094524218a00c0800e11036071034106150880400241204100080600d0400800d1a442e1980c00034020020710380e800090010542d40180c0e0b400d600c0c1003252140354203103007070b08000a5008204100f284601c80600d50341c54465186500e0345000c001c00802000104148141c408002503c00c00c0b00741045c450541000a0040b005000300c003d400d94403180c0400e03502c2c0c0c080e45a00c90b02076001c615003032551020001c0c4d041000c05008601d021840804140c0c507109519104e414012080c2800e06190b41a00000000102c99400e80001061420030b854403020207220303002076200d0703 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 459676124 1250 459674874 459674881
    0x3040606061b0201020d111005010e180a02030c040513080403060b180f04030f02121c0506060a091a040b0304050c041d0709050907030203100b1305011203030f0e0a0614 74
    0x4802c1c04292440d90140c0040c581c0700658030341151a01803c2c420080540500c0c10360800d000024014503001c0c01d2010710307002403454920007142e20400500307070140312984105042030150301c000c070302450441c0007600d001c02c007a6903507600c103007035055509070040840d2400200041404440d611103450301004030340d100349120342c1c6202703001c00c01820360740e00c1505440c00c030104000070f011f0250020011090300566503d869503180e00c80c940e401400d030040c0c00b22021202d108000d5118400c0c16800784044072441d003030407449100105a0b00c90360041411b54544202084203128158054400420503001a9541ca01e07040c5040c1e510303010078041090103681405401e462480c00d40050007000c590a01c02041858903001500c4e000e41006404000103004414004c005600c040c85000c85598502c5404641d90205109200003000304448030380c80e60b8130748801400003145981040c0c145541500d0702040c3c1d40210040700f40101000110700406103d4001410104032454029010000d040d144200e2140c0c1d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 459677374 1250 459676124 459676157
    0x307031203050c04060e0906041b0519050c031c0219110606030105150906120706050c07050109030f08181f02060f04050d0807090801021206030d02210d110304060606 73
    0x183d1700030b0901040a0070741078041410094682d5030321800061011440321a110740481d65444030400041c001503000440700304000c205070560324585d041e40381c0640f4012207000032503164000c03880201070f4201541c003204a0074405405807100c0910344041c40160240318800503061038050350040c2c150740030b6000068002c2c035061040e17600c50840f0700800418991103404004809400401c1154804440078101c8121740080000302c014003010b80781e07580d0320b512a065552820109502031410800ba515003171000460414289540d690310121464031072500c4040018003500700d0584d1500109580111030701c482c40e840340c1c110784500e280c00f0365003107894a00c83d80c007c0c2070003210003805907808a0401c12540b0b1250340f0ba25071098291a062240e5902c60404c1ca0a9912030550500003420100a000e003e00e8203100034002511103000900420003800682403600d0004090034980355400b06040c5d140c060103811050180780004200755880c074092422900800a5014140001d141c1080d602c2221 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 459678624 1250 459677374 459677377
    0xa03090303140115030905012a08090109050c0603250f12090f140f0609010209101112030901090606080a03020106050a1802030c07060f0c0219110f0f0307031203050c 73
    0x3c0340c1c8448001c0138035000c0752055000c4c1c500000c04035101d650702c3e000d800054441340c0003541590300035510f90080b40b154510040407000c000d00800c40c0387c3d140c40b203000e001610008050490715403d40d51240c0300d40e900c0105400e000040810307000110030300d416821005a001915031072045650b04d85400d0848813004a608865405000500c41030602401c01c0108402014000000ba443da040707840e40114400c0e841d041403410f440c034002d00da401041c0481c036031500910401d500d07541458030074199041c008481d07035030341179400049400200000124140c0802904644040d50f0007034014410140da401205907944d01c48041a0010b500c1c000300403540e440c00156010884807981c014001000024820600950018000201e0603d0421004001821038041c03030503040c403403001c00110340d40c0b40e01010f418290070701c0e01084c5c082c00c04080306001510419902c40078200640c1c80c2d12501001402083d900011a0340069141c0325402d0000100b10810344420070b03180d12990284150384941d0f500d1401d6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 459679874 1250 459678624 459678629
    0x8090c010801030215070c03030903020f0f030309100e03030f03010f151d180103050309040c050f250501060f0602010b041e2003070905210601120c0305030a030903031401 75
    0x3481d250040015280140101d030f200100c0d0b4060a02c0c02d0240d40c1e034003901003090361048010680307950b42001940f5020016003a50300c002d40c0c80f04442c080302c0000a489100348220248140c070400d40780f034070b15880b170540310344e9490b0003408996543c0300704a40e50495800900c9800000e491103400450b41042400e1001903404850311900710401d00103030005110324a00024541000c1c0000107c10240c04450010b0b00a40c00380700556950002541484141e58540303001e941401010010301c0c000ca1070040031111003072880c008401e02072810007000325024071103010141c000e40c200840410300440d0380250301c0860f00c15800070070000704003d06102c1694110070386954905918640354035002d100750807041d203c84900001c4101d282d400342312000306401c15070b255000510048024481800c20742c1681c04c008058010240c8034610503200c855451505006a20b000d014500c10841041a021040c1000d140d01c2010b90707850300282c0300001d0013020091419400a41060300451070102c0d0444031905 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 459681124 1250 459679874 459679877
    0x1e030304092c03030105010c030516060e0d030b060d02070602070213020301050102160501142508211b0a0c08030123060705100c0903150606110327040b040507020d08090c01 76
    0x313607840e18005488a000001068060040400c11404039140c1c100300304148a201c0c0c14005803003901810080d240030f90034a4a1000d152500c041800c90f691280b041e1901c200c2030450150b44c900d414030b8100080e024a10303000f0340104a51144000104103a0040c42c1651000e83c00c42e103131503070310701845804c1d29450711405000c10068000804001151001010f101c8a000407082c14520160745c40650910f9641098843c03280118802d6401c0c0c01020104200f00707080c81c05900303182044088041d02c2070072004c41101c2000300213204040701d405141c100344041e0300030641a0322036954290000b13110306d00420a22180320210b40034203040c030f0010180c59400750084001c100740c501400e0a00000c0424400840c14003046010001c00a40c160b401c1c443c24444644003c6101490034001401c0c018005050300040e400602490759142c007100d210401040c4d1684c00034602c43c1c952408503008048088006810900f080c0410101503000102205000c0c016952494596202c494068070361070785c82580c50 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 459682374 1250 459681124 459681127
    0x1a0606070b060607230d1103041d0a11070627030210090809030a0602090a050a051302030a20070302060c04060c03122c10060b091e030304092c03 64
    0x204a0306200f00540005442205000086060202110751520142036080c01e00d0344407861480304c1b03075407140503a02d20400000007103040500b000c8455403103030181c1519401d520407210009480e4003040d0800315000c4110052580d54200350b0804001500081602c200c0b40c1c40043c900380348103000c0c0001c00b20160b4140e4090514412000b00c0c0300b001e001e440380281c1c2c007000d041c07004892960382445804401482a140180d86084000601010344c80660119109400c0030404008030380710b50010034a050f030310110059a95403a2510003000342a1000e444800109500e0b0000408401500410b9180c0c025000c03a2000d9650003801d401c80e201e40c1c01080c0004600d094072a001078001c58201400441c0c80c030001c83c05003a0301400e510342c020001261500300c0c400820f101c154040c00d02c0281402c0c0710055080c00f100c0c0c01e1282003001403080e0005035000d58040c2c804015402150303824540060402020f8907502c660b22198080940b80030100c0b81c0700c1c41000b019158013064278030441081000c0d90070183d0b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 459683624 1250 459682374 459682381
    0x1390503042d1e050306070203120c0a0903120504120b07020c040608120a020f2d0604050c0909030c150601090902041815031a040309080c030a02040e0111071a0606070b 74
    0x90f442c102d1000c0850b646601d00340c00840e0a513024824284140003640c0150340780d41c5850084808508080d0808014903010004907000d10740c0309000d1410fa0b90030a600380c5408803845000c0740c152065030300409552820340034800c00c0040d15407101e4010f40782e550854100d424400f0401c001c0324682d106510703490b07201c034100d01c000c2a0b0310005003400c014140103a402c0703100f18200d2681040c8034144007048041c202114600492001030b00c414190100c20014a000d00d0f0540d60b007651500f15101d0f880c802d501480c0007459001003003044484000307058095600742528501c2480300da51007a031725580410307110000441c003451648282c408079460b40b6284138414000c4c00f9100010400a40c0720b80c500101d00c8004000300301c02c01e602804c084040410b5481524007400c1c020f02409440c1c21000550b00126015445642d0005400810a404a90002d030724643d254800380140043c050900300900d000c64500144443d0001c400043e00004040d482150340c4c641c00c001091191090007060381d000394010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 459684874 1250 459683624 459683639
    0x70806040b0a3c0305060708090c010c080403060e07060f0c0507030b041e0c090f091a100f061e0c0201020a2009010b03041a010501390503042d 63
    0x803949000324071201a02000201d00b440780b900b00c141c503880f03400c01ca41c600c41042006030801035035900000f5403074410542d0030602105038a6000c0f0441e0107041000740c105e07a200740850903080f64011980004104000d10b02e02d00c0d2552a044248034010205940c12206c8c868140202d0301014410b921a01601c0700d241190707254a280c0d031015100342c92203507240010210f050300410741310303900c140543c01704e4500d98507000340e0030140c9000038129030145003004030810003c0c0301e04000e510040034241da69466541c07030403281c401e00380c129480050989039501d80054221f8100840d10038080120501020500c48484203460711030303c4500003030040e8070500345e4001081040c0508a001104000e811852140c0c81c80090000f0100303800c240c2d0081800000c0c0801c0005015606e1025a05c881c0601c06a600d054000380a208048100c004860710580b40300c00524a0482480303440a455004241c500c4468106165241c005005003010b1000e00325441007103040c201c3c0300e0744106540400442d00f446c1090340 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 459686124 1250 459684874 459684899
    0x25110703170903010e1b0105090603060f13060603090c0b0f0318031216120507080a020f160807032307140c2d0a0302030a02041805060c03070806040b0a 67
    0x518800c4160706010b003403a01d5030217004811100c04003e000f8405050b2881281541c8030840b011181031003000c00a40d5040c1e120781055030b40c0202d0482c6c100d03468000e09404189030f9040c084550244900c2c010000c038100340c05034000100c890150034150145038484042c81d0700741c1f0031900442c000074402d00024000340603405031208a0341c1d125096a0906110021842c0a05801d4840ca170060300b8440d01d02001c2e90f417101d6000c000d03144604050103682081c40740030b4103182d0043d2403c0030b145e0f00000c42c00405141e250490391103e480e9501007110b911a424039210700c0e0001401140091144044c0d0800342c4607000c445809c0e10555a102454282c03240c0d0742c50580c91144e519440a40034140103e5425500c18901ca00350302201c0e1040c5040403554203204040000380410f8a1050305840390600c0561000548400e841c3da048e034000a002c41c10002c1000460901c500050151203450b041001c4003040002841c0201120344480c42039032240000c2000b5568900340e0507400c91842d54082201c00d040c4034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 459687374 1250 459686124 459686153
    0x13060509160e0f1f230103051303080c0306010309170909060a0f140a181505060a0203030a090f05031606060f0308030703110408101a010201020304020a090207081225110703 76
    0x100184c9035076803060b0b041001c80000b02c1ca0454428214035a40c0c0a58140c020180d01603009040e400c05440c2603540500008400350046251346401f00c00a0501d034001e600c00e441054203c0c40c01038940a40e00f0401241e50301c4007001c18000d52141d004039410341821030207002501c80141d2890511030510059802c1003000e92107403079020749021800a20403c0681401420b400c22a00100e4403040f40250f04070f20b008258007881c06540c08124100708a9070110540740c20111003000810540414207006040e01140c040103080c902000405005514140c82c01c83c04d984d1182a080c003a40c1c1d40d807100c280e039290b07151001030840501000000c681c24403d030300c425200c04800c40903d080c0703034648040038a807907001d07107a1903501d0ba5a070102d44480c00002c000255801401d1009514510341503011400d844424414161055000b180c20070411a4180903549400319403030000599107011215800004802c82c00404140e04005100341410322030003500600c10175400090091902d5569103403044d29250 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 459688624 1250 459687374 459687421
    0x305060402120a050612070609180f0204080a06111e09011715120106050a1205030706021303061503050d051e03010306020301030c15090e13060509160e0f 68
    0xb002071501d01a00c440b41c490150310301c80800540e40c80e282003405000003c0c5082e8212640c01b1b171504000702c0d544500108162070b500118009c95000746d2056101402c0740c0c3d11400806800810080388007000094030401460150801f0300c0942481da928482901c0796600e02c0f8041450782c1903240b07000d20a10010404928189054078000c0701140304c451074140103882c0900f819045411113078107031500552411900c1c00b0f02c1d0081140360725002c00559420082d2188151402c45448000306104c4180180c0e406541c1200c4103560b541101b00801b151550140401c4400500c1c1007205843c900320100107409a075400401010504214030041e40c1d10303000001c2080307031103a0788c00a40380c0709080b00b4043c600842c40f034030740507072254103618050b82076602e0354101d89500c56850010050b12503201051204660b01c00a940c05642c4452210050025050001400c00c50800c010702c40b40f2003001400d04070030100740c140c041400d601c034011135842ca10282e030b0700189441031102082d00c280d181142c50010040c031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 459689874 1250 459688624 459688627
    0x50313031707111002090a1a0c030c010603020a0902070b010b0f040b0705030c010507141c0e0d021e0a0b011505070b070f090b030105031b0604080f0105061806100305060402 76
    0x1441d5168040724115032000c0000d1125541901c1c2c82d008100d120003620300c001c0d0660070260000c0209150480501c1100411411052041000040101102c014490117010340c0e0b95000820748990103848203200c220301400c0314100015101c8114408c5c2d409403503121015161503440c19030312072000e400c102c2c445e0551010801c0005598a849002009418800c002940d225841d0100160071554010712110500550306070341344d580040a03003250754811051005404981c10b0769045001400d501d40e2440507071240b815449180c03178001801e03040d24034410a1110720301c04080d1110352186c5030000020001c83e15140144180c0e17951002c05c4e05855202c0c90241c0c10030743c40c3d0311040300c140340c00d44071000883c8480c0848840c16501c607480d8400b504000c01040d145501d0500883d9a83c80d11112501c1c40741901640a01c9590f1094211402020075804030780d0030503800c04141707008103c2a1a818450603440c000d00074840c10500e5920720580000b0000f1960300d42550b021303400b618004084a0f44640d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 459691124 1250 459689874 459689897
    0x303171503010f0510050a030203071517010b09090a02090105040308071704170c0301050606090607030e061b150919030513030c150c0503030703200403080a0f05070305031303 77
    0x40901c143d00c84070701c01500210f054107000701131205126a0742c00650003452040018005610001007800490f207042d5516481e11680e080210340340c100030009110f01c400c44400004400702c130030010b0240184111181261501e80500c44000c0f48110625180840c601344020408240c01e0030203071640f98062030b204001058540200d16443d40b054200d103064111000e00c16126010030420310303a4501054000300414103220002541d2402080e45075407284200255075000c06100300c41e801000d07440501942c0c1c0320341e9003209007949181d031015842805c1c0310310001c88420081c80768501d1300031102c51000d0700c00301205070703840841110195000c0e8140003040020054001140340c8035030086010f600f54202a40c104000501d60f580d50203189000c201482c0c0d045004500d0203c12aa0001c4882c00c001510100202c029144048500f6404140e050040f40000c180a0742d04010005140e96903105e03d0107401800083d00c5d640100c0c0710150005004ec0009495402401040801c09009081c5601c0e44070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 459692374 1250 459691124 459691129
    0x51e12031003050d08130b0a090203010903030c1b1106030403140a020714032b0909050901060501020d050406050d0b1c050f1018063215010903031715 66
    0x5105a0341c0040c5803148020800c1488414451640405101e01d008901c0e4140681e003103021510100000e0b07c000079080115103a200b4640c405603400743e014000b40840e01c85406c029009003000c68140c80410002ca10310100f0110445a440d4584e50000c030300b04e0514032042c00e01c461a00300402c00c81c24030206ca900c5400007980440500419045540100209030034442c100d0103034581c2c4152030707010364805031840080c048145429003405940b0fa06090300016462402c4440310116400355007894030340018448642d0046d004041918000c0c0c0803180340b000340c2c5002300c0c0d503440b8034440d074400a01e00340b24044407062160441120303180000c0102000710042c10703140b00d1000303088104a5aa600c40c08807083c0e540130600044420350070303031103041000c441c401605c08031030100701000030320442e0340c0c4103104000c02030720104208070704000e409661140012007003215024400d41d0501600405502e0f1040350750702c65890b103400d40781c1c140e807102c00e688400a04071150b01805041007881c4400700b0f540003001d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 459693624 1250 459692374 459692377
    0x4030302210421020d030906020d0c11010509070b1b0a0b091b0609030a030c08070f0503040608063a20040506040b0d080a03060f15031404051e12 64
    0x61150700a116041ca45083c0480600003030390050710400e644a1803000a8020071400003040803410042182c5007145007641c000d224000055986600d041424040181d02402500e0b0106080d4003c0220f5122011015500c00f00c610407950600c0c000c01108008003810040160304c540381c41c0c226203690b61903540f01100c0e1001110807000d158040804041345441203c40c680b01c0310070980300e90780b030074543c580403e0b01e070007581001906009104802c41c08020150045600b0313190440000c1103200000c0c038200707071658880d1085200156078080410014603140314507a03000c409071520140204c0300d240b0360507105540c03144401d221051035403900c00807d4146030f0009201c40400800300325868510200802c54002400c0c041c0610328101c14507045d9140c0c4411080d07903e8120541ea1740b1900381c1d1604a010f040d80340c100541d00d0041d4080025581c0d20818698080302081e18107010170425114202c012810444007e0015488401d0758241c8241011040d4080d000c2c10f015118029034584956216 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 459694874 1250 459693624 459693667
    0x2150c0a0b011401080f01030c06110309030703031106150924030105040503030702073213060602010207020a0b030609010509071206080a030e0d0804090f09120e01180b0d0504030302 80
    0x12460f03180c10b000819a03104000350740c00f000c91030901300c2c15410b5403a0a9540100d030f018000601c2005078150840c10410000c0c2d0b00010350003401c445440c4d40380d24000704040c81001c0080003500c6050041040b1102ca6103036129460006090f46031541e5403c00303141e6010035502c24244d14079028001481241e1070a009862285001c0e60080d130340c90402c00c3c8020b03c4c0210755071092072041e8035805200000301e1080301741700007510b062481481c0e00f006800010000507000c1c030064600391801c5400035081d41c047d0003802456000700c0daa1444203544400c02d000d20b102c2110a190302c01d01007401480203142040c20a50070518038a092008a03090041402c22102035800940c030300e6000e8200642055400300c0341c0b02a500e01500c0e1959015504d81c0d641c2014051809488045600e541d240e032010412a48400c2200b600203508881c0c0c1c5003107a501030611101d421b4418002001001e040d440342c942c10070310707200301c884031132040e4600310410a0a10080c00094012000c254003041705194840d82c6da25600d05 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 459696124 1250 459694874 459694889
    0x8031606021b2a010c03020c060306010908060405010608070b0c2e060e0a27141c0f02061015142208010c1706061612020f100902150c0a0b01 62
    0x152005110460504050f08034201410441860065400070390b0100d0010b80005096030001e490782c4500005941c609030301e802c0703180c10b0310500d4208801d1060540109084400980940b8113a0b5182c8160711902e01c2420f00b843c0c0c00340d1001c0e0145079200000782d0303003001640c646090740300381141805210b001e480645c0d02c02122900484148500c2000622640f04001580b0802204d0010b2842c0a002e52150140c00900016280340004051607000c1c41f00300500480d0740710910707110b840c005002d42810182030250b0018070520000601c407030745100d000000e07613000c1e20301d01c1003441c500c01049440d6010b4000003184250280f00301c10150082404014142600340303000e0300d100c0d04048145007141c1078041807078104420107403900c4101d007802d60a1034020304151549a59100241201c00c0001d0b41005c004003008145043c1501643d4041003800c984081c84041c0c3d1440c20740e00042805a40c9a010701a5000c1e5503c01d030000c9902e6240010003c01041809403800100315403650341c000c4000764011403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 459697374 1250 459696124 459696163
    0x6120608030f1206040c08040f030c150914061017010207080c03040305210405040b010201090b0703061d010b09060304021903030c0b0618010e0601110f0a02040608031606021b 77
    0x303100603d54070640c4020306450400a25061000092562170b015201421109402c0541c4050501c80c00300860010b4100c2262039540c19400581e800501e401070054503600401d000b401e0883c0e60109005005800304441d4155550510440c10103969901040200540d820400700d4001040c002c050310f0750f48000406141c5803850350030428109000008030304484030f00c4065000b2020712103030699040d076600707503000030303030300c0d840000503401480d01030000f03809400d0810401a403683c0c541c0091007564203032042c5042c84240c6e840413204a2000307001c1d020714448140712202c898105040510340c42800104924003c0c104543c12500b401c4c1c0d9500b017a0001010b05202c40d083c0003503403043d07982000042c0d4152074511620742c143c0038090810300030040c013280e149000c2541603110320100c01c0f42082070001d4950b050b6110b03042d40d07640c250000c1c00320300440c14940002441c0c01e010090300d10001845500e580c84806983c0d903400254840a50701404103071849000d00080c030700f0850107540d45001407050303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 459698624 1250 459697374 459697387
    0xd08030126070303050f0f031501110f0a020409240f1a01081306060504140f1321090e0114030c0307120602030604090203060708190606080106120608030f 68
    0x140901e03011280305054600d540342400c80324a4000030302d401140c0c0c040c0740150701d4003000055a1224442c48000d8207501c080442803146913040c09020303640480c400d80301c8038544006810314035154004d0035502e08483c6c01c55610100541469000a40a0fa11900010070b0000e14800a641c03044000201080102c1e902c07507002c41440716922441c04103000350300b042280407200b500002c0c1f8000700102031040c4000031000c080c0412026802400281400a1052009541c00001d0f019940e50442d101e0000b0380401021414006108001c102840d42122160144d599400103501c0ea58204132000010443c80c0a0009144000f6410860180280e82c0004007e410498101031600b150101c50034441d0b00400400c000d01c0c22131904d00d08547d85d200c8009616552440001030042c241c000b0041d4041c0504400c0005090388050700030b208010442c04581c140c02d407000340303d0860f02c00c0d015680202d010b00b0014011140141c4114001046498012032040c0d103070309000b403c40d00001c2c031030b841c80c3d0030200303c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 459699874 1250 459698624 459698639
    0xa0b0703060e0c0d0e1216050114011a0307110102130303021c0f030e030d06060504170703150b03010b100f26060d080c0114010317031e090c0d080301 66
    0x185002070000c1e50b01c000c101c0c14180303001e050b10710640101c803241d80d036a0754910b41c2511041c4015503c1e07840740310001d91144440ea46609910000260440c0c441d40303440c100482000b181c40586041c0c58420300d24500d0380341c00e0040d00c44e050740f01070442c0051000350300101001d001c00b40014401c18070903e142c0d902940c590326000c2d00d004000560900c214200e00c0e0303041c0034268000c0280001c03040902d00070400004154019080d072007103610749502e040c1410400b00e007003a0801d000704100d98140209981e20200c0e0000140c4915240c00001c05841c0c420052012000e02e030b401c800403044c0010000102516150001000d4040145640c40400c0444d4015000507030085040c40c8064541e102408074003101024007160518000e2165100d400100b80d2041801140015180410280c00080040e64004400e020b1068400d2100320360074800d102840c0e00c1c0c103000e0000da90080c142d448880101c100c6801d80030444900082c80c6d92254402c440b00c042c8245d0311505041c0d03545001d071100e91f65950507d04e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 459701124 1250 459699874 459699881
    0x6090e37110a06030e0c010f0e090f01170703050619020f12150a05150c0307081b070923090102090d030e030105070908031c0f06091406030c0d0b100302030a0b0703 72
    0xc0f0080c145860246101c9440109120b64000000d10f0909406400d00106a5228510400e2150858282da0030401581020b49001e4141d070607881404008883c480081c940c1c90340d8900000344250460340200d5000810100d25603e03e43c014400075060076403140d80c1c400075400c039940c944071643e801740a02c402404c6205013144640d105451602c01c481c10140424042c100120014192a6000402d1000d1031004d00903a5881c991080000e50b40c0c6000780300032020900c003004441158015800d0000d0040039910031b1214100100d0f4400b0020b0a84a498034010300005110b841555001c200300f4400395649002042c03440d1003074079000d5800c140d1006050071901e004003840c042c00a05601480071800001c16140c001445208050b01e544c0c4100407000a019000107146619013003450220381c0c03565030303007040c1800001030548581c0b959982080650710f0384295019904580b0342d040400100e40c0d002c81003940100c002c0783c580340b01c9590350b020034503007860f4440c20740d8071415220610480742c0c0d0500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 459702374 1250 459701124 459701129
    0x406050a02090d0b060f0a0608040309080703031e0207030501050a0c09050d020a0506070303020405040603080909071e030c030207050601030813060f050306130e1e0106090e37110a 79
    0x38021400c2c4100720010809a0038808400360814198000042450380c884510110030038000d802001603a036110009040c000e03040e1130480c0818940720300402d010f07100142482c00c89405684462000c0102415452411440c015500850140140c0800030900074010140034241200380010100b290b0840100a1090382c0c002ca44102c135010300d0710001da07940521000070307039108507400750399215140390603002841f503640095005800d202000003030124510140c0300760310054400085558945000b00c0385500e8082c00003040c0f00211610346e03540b9100f60310214800030541001407400519031500c2c1e1815409900c1144c05440024581e2204040440c201004010a0400580c00c030113207980504035010061403a8094001e60701c03080205000e80e084024621011000e440c802c5d5000400c034500ca1641d90f82d8519958203003400001c440c8134901c03c902808880c0000f0b0426960380072916150400c1026003d030444c516541038041103070103000c2c0500d00030311031907004544000090070700c90304c0503003036 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 459703624 1250 459702374 459702391
    0x6060f0905060f0d15081006030201030f020c0d0e010c0501060e04140d050904050604020f120f0108070e040611192a020105071410020d090506060a0f1a091305040605 73
    0x7848015145603c1900b0740302d0001d03c030400840c0041070480b840c02d2800c0706a000d4505442401040d03220040c1c1c079401802601e000381d03828080b030701004000c13409034071441c900a06668400400c180c280c2d4032519494810fa90705240c400e40301c0200383c603401d00b0350b01103420075071407101181d09000800c031601d4000102c14000074043d00300c0c0c0703000e240050103500a01ca02c1500840e02c41e80012942e99882d41220300e00169006c0694845105464035a03140c1d40840d25440304542c404008a072140c000180b06045981c850360401503640d40396074010242c6085450410140b00030320020504d42620207810548401990744d4400c9020a180f0f1015484007503200c011520080381c1141000d85d90000c00c540005400c200042220b1300e09100103890024013141660900d880802d00c0d032103681c1d890700081502401602140c03002e0325074030204031181d19070788201160315540308820440b00b840500c1880404040e0550b080c241030300e0001140045040101034a019a0349071b0800080141e43d2040c1c5800c040030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 459704874 1250 459703624 459703627
    0xb060c1b03010e030f1804020a0e0a0504050603420403090605030f070e01020c1903060b03010c020a1b030b07080405100e07050d060b130507080c0c031b1006060f090506 74
    0x4043c0465124841c0701085003003c440043d0009003454074518000d460321000c1c1045640d04040380d4000c01250031091200c0c07051801c450006402e2030b181c01000d00800d0002d0103081019004414940e0742615409400d1302902d94000c480050050035201c40c50549807011507164515292038000c1000b0215000601401014000d0210140600c100540e00001508001d03402600340c000503440c04c03105d0080c0d50380c0b1101000c180c1002002030500c4c0d0080b43d00c9030303100b0f002000c0c841c0201401d0303030b404004040050b485104543d003c20703500403409a0f5022000821140300e9100d464204500381c0880781180890201402d1104101c41085400030300e4014030340c100f090301820008030740c41e040c651054500c520000c40c038074800d1018035844410103441c010040c01500e00100b45240c0a01800c541500c04076400a00080707044c03540c0e0089401d21071040e0043c501d40188004405244091480c1d801c2d00c0344075500c0680341c075441c1c902c1090064000d80e20381d081a161130507001406d02196400c41d40c05400c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 459706124 1250 459704874 459704891
    0x3090b070302042102120111090f060f0a03020906070b0c070b011e03140f010f09030906090b0909041e0c0812040501080f06010216030c05010801090212190b060c1b0301 74
    0x34401c20415005400443c3d1210356a45400006c0b4850000d41000c0155442e00c004c0d662403402000040510400640d850606440b80360704020483c00f40700b1400703c40040801ca0305104a110398000d001001006200034105585901c031030243c64000c0b903169902100001d0650180405c400c41c6500400c1070704844081e0b00640b00d000b00b0810501d10000b0b14442c0008070018607910140403488038100c45800070483c40045060348800741c01c0c4d070b000039000b14290a00c04110244240309850640381c0d0039154170300c1c1803060800d102c4100c400030026102c144e0744004a1020100c02070303031007454030b0095000107a0f50341007000d0706003001025072405008410411042100740d0700080016848561001050255600d650050381804041d80242070800302c004408801c0042e0040c800082d01c0081c0c0e80c0d108140e1701d403000d000491080e8202001503143c0b480008481919404026061b881c00c910b01140d10064940840e41940002050f01103036000070a5007d00b104420b1207420501908400900a114 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 459707374 1250 459706124 459706139
    0x1092307030f0b0d1112071203093f03030603020a06170105030102160605060f03030f040609060c03090306050601120615020609151314030403030e0108061f0c030c1203090b07030204 80
    0x100002d07903550191080340756018981ba401d100110040c400801035813078045480c0f8004010401d14019007450b0031028008250145190034407100340403d03000103903104048031501d4a0142d00c4070b50224101911071401100585401002d40c0052500e502c4480c2043d80031800014020416000240a680b041c030220341c0303168006407000c0c410b40d00100001125154078010403910044ca1007016094030000980e480450542c030300400481c1e680c1d0f5144ca9010f074880d0001c8640552040b0040d0024141d45028001705125a01040c1c000380c050600d86000b0400d08400ca003698900e9220200c000d0101204018298050050640c0054402c025007095034a1004c90100340c24050f025030501e035911503180e0100484000c02111418800c02240c1e00c83c0d580b450000d00070700c8d924130a10700294030040891201c1c181901c1c4040796850032400d8000e202d000103011210a0708444c0d054003001030100c452400324480440070002c2540756500440c003801c030340c02d1088034a4000340c032980c20144100700400021 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 459708624 1250 459707374 459707393
    0x1051011030a050d09020a2d080304180213090209040b04090c17030c0102032703070b0a020f0403060f06210f060207080f0a09030c06110601092307030f0b0d 69
    0x10030310704005440b00044c0320148001e02071050000d4000d00c8408022036690701411400d0005030300103000000721201850b0360b100d00d80d0284501c06080d4420b10080c4142401e045402c4a100c01104c401410301141521030029444a60302c4481d42a50010781110385083c18000c0c0e45164000341c3c0c0a200c110172940c2c641f41d180c2014400c840a0040c0700d040220262024021903910039080c4000355180e0600d045c1c00d80100c10001c10414606483c0c3c00794010340180403007034038003503504448104d41c00d543c2c03001080c02079031180d40000b07913901c0304000c00320010300f15100b611003507094050300261150818a080715080b080785001610003040d403c2000004030b1403441301d00240d900240c00342c2c0750491460001c05602945003001c41c8144042481c0404d95806200d480c2100d002d920fa4000c420350301c110513188651030b40c25022090b08100014010048a50800c45803064000c009000074002803141425002c000e03216100002e0712500c0581d60520b05018040780d00b04121000200500c0342d603207440c3c18 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 459709874 1250 459708624 459708637
    0x1e06011508010909050304030c0b090a05011e0e0a050d0503040e060a050a031b0b041401030606030e0c21010c080f011505032208030c0d050c0c1f09060f02030105101103 74
    0x1a2648604d03802c008040c01510015a801940c806d000381c4c5a1320542420780050551502503a002e0200184661241d1031100100c030381e021625000240d1400d049402c480c200340042e400440f011400101c50700d8400488006500030000342d5202c41c10140f034901120b501503c100d1055404038010f0000395512042c90040729804400884018401203e8140440c41c5910256080c0400301d00020b4042c00e4000c247e0800d54240e0b010000785464010680c1101c0045030096412b510180810308203050516560842084000c143c1e40010054003c842c01d440c40c000321040044c2c3c0c44018031120100d801042805003069401c1480000c5001c080108a40402021401901d084004505401001444954055410041e400da0b41c2c42c0030185041c0340d0b442020f171148213901d001c001070403803142c180903644501101d40292204058061110740c4845085401d00012651a03030100d000549a00c07840d07500926a010150720307580742c10108101401000c201000740030789402020309040000c800c8880 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 459711124 1250 459709874 459709889
    0x18080706021c030b03011b0e04050f1b090306070e03070602070e04171b01050105030c040212012702070309050a08010203251202040b040512031204030518031e0601150801 75
    0x1950002210440c050686520302c9501546850704003000710400184803d007c40d059202c0c86400306699082c84201c60040752104043c0e40142d000c2505140e070b003029184c11581c00000141012614800641080f405442a10125440c1140340105003010b01022004022a0014202c41c51030b00c8130108440000910090101413194510210020f81800b610700006100d10801020b20b85031002c0c500030103083c000c2512034131498072030540900d040d00840b803154007881c1014100344d1030a0000c0d034420001c10a0600000f11501ea1031059102610180042c2806a0740e0001007030700e03000501124010700d401011003030740104100310b034402460550079607074404008030600300754000070700300c0c0c002c0e403869040401d25000140c000f99404030301c0064020b6910440b81301644600c400c0c103580d524450001c0c5145078544a00019000c2070260002e03000c05c001c21600901d40300034040c0000e081c0b100720301d1100c0051620125083d03140b2400c010441c0500700b1f1407482c8854101041d005410705c0d60500c40c0c0b65 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 459712230 1106 459711124 459711163
    0x201140c151026010908070b040201030c08240613060801080c01050a09090c0306170607181d09010f020c0703030f0801030305030a0b18071808070602 66
    0x40850f15401c000103401c0080d40020022541d1032540302a82d5541d810316030713010541c840000c002003840744241040b04d1606100250403164900e04540420203448100041610341c3d00b00c2e103040080d0049107082a11a110010760305120310100c0c40c04102c2e180d400014a95080035280d030680c0d04032810b603000381c4110300044801c2d008450b000800207542c508100842900755012040540c0c8526002c92034948070101100c0350b00c00205080d104c0e51000c2c08201c00f07183c0c001c0b81140e1000c40001818105840c0c0304044a0034218410780e21031480508001c00e5018209510035001045016815511a1140b00030207807201d00134071068001c14a000c9080902c0b5101e02d2016040c0d0f6031585601d400c5484110400f0b004045807594039400c808803000c00e101c0c0203680e40e07031f25105074030315540c80000e5441706139103032071401e0f841d4003010282d0b2102009000241d004110290102003090081 = true := by decide +kernel

theorem cover : BRFrame.Cov 459532374 459712230 := by
  have h0 := BRFrame.cov_init 459532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 459532374 ≤ n) (h2 : n < 459712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
