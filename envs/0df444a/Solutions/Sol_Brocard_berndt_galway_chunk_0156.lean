-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0156
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:09:20.275508+00:00
-- url     : https://prove2.me/submissions/b4da013e-5c26-4ba7-9354-03ef05a4a443

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 27877703 ≤ n < 28057559 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 27878953 1250 27877703 27877709
    0x1906030504021807020606010e0d020a0801140f0c040303120b0909060405070602030913020a02030403200906040b01120b0a0503030a03050405010b0a05130902010203040509040b061e0604030f0c08010905060907 92
    0x1059244003441044c0c1d40004580764000024038111100c0c1282c1004520000401e810007500030400c84804942c1400641145210000c00c0768892060341e01d000980040d110151144034240708100000e1020a01c5600f0090710140d4040010070300103250b0b00800d0420b45c088484ca016900407109120400c403047c0115001008a0300c011414080e0250002e000c0b88102c0000231040d950004a0128584c001d0040d14000d40d005180001c0030f22000c280c8010400d003420085220301303c5040007030003e10b014418140814030695410700740d0b00b030303000b0810001c01d255802d40754013040c810300000f21964204000d0103802200e54003c2410b05280c80c00b41c0c00d5444002d1130300e1040d01d5022041c000780d1500c1d42c6494000f40d05420124410b545800186c2c1948640d0b0809504030328600100424010003040c0640a844103560001e51410b40c0c9850440c200503580c03605510046c00c200c10004625100e0081d070328036010321880c0346100d50311203559007100c5a02c102100c00d90094002c1200c60a0140040001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 27880203 1250 27878953 27878989
    0xd060203060102060c090a050105070606030501110c0f01021908040c0e0a0c0207140d0803100905181902010509100201180c05090c03010602060703020a020307050a031101200901050702190603050402 87
    0x910a501c1b0000e161a405400b070b142c100300000ca40d1500f80200d58100d00300440e0000001c00000041d50034540d8154002d5241207070a111707154501c051200140300700d500d4010400c040c0501e03801e10300001c0703030701d040050b03c2510f445512080102e8412601c0c4401030007582c2d407040010740601502006420645142d001039409480300d0400442070700c800c0d940d6002c250344680b07103c0d0b032965469821200c11140c1e812202100d40341c002005840420311244000c0340c2000805c40d282588000c11100d0005080c0000038002407081c0140003550824a002d04c0036001a800013240144036a210428280b145000c00e440340700200c4070030411030414043c1644c00a1a01900c17510319030600b00d01a40c0c2d04006030141042590004500401d03e1003841512030380c0391302905490320303401107003002440071960344014000b41d4a007101b40344e000d45404030502c22900d103203a001810201060015100741d041040281e0700202158450600c40d181c01690402800707081e00c0c0054541018014003004090070801004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 27881453 1250 27880203 27880207
    0x50d0203090a0915030816060e100608031c020f0909150a0602030403032c03030c100b0418022403010e070e09060904020f0a05040c1707020102090603190b0d060203060102060c 77
    0x700301e0444c080082902d4001900541d40c41c5e8004a40c15004507804019001030f00c0c4c04007199030901c000c100301c0d0810885420a10000d526544419140e04c51070904895080502d5290502481d45070041e1a0803040e810321036041c0140d960210305810b03412110b4030780c2c10380c11404800d50f510b014185d400191940c2e1000b10309090a43c1d4026040d620b400901d03034454802e100b00031a100d0088609403036a00d4004d81626110419100320f165a440c207031822905c91070814018400d1403c2c10720500d40318058090020240d400b01da0244101494a903580c6003c001c01d101259000d40006c000860003040b0001d01d5030042c2c0303403e4030700a00f001d01d110300144c032400214080c0185a520724588581168040fa0340c0440810b1000015411044aa10054102d402c10208094440d04000446060400c000c800461580c500504908034811403100325030006c802d101140783d00e00c0c203908085510f486804000b43c140414800220300400a000459101e6000400c00c03800b0b580c10b00605401c128001c82c854 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 27882703 1250 27881453 27881471
    0x5010609090c06110111070807020a080f07030320010501081506030d08010302120705040e03070506180303010e0c070c0b07021011060c07060b060304031106010b031603050a09050d0203090a09 84
    0x18a40b9002e4440c150800039112852620050300303511a031260110203900315036070300140c03a10720f00f036800c040e80c00d9200c1e040c0403800107000c031000310700401101c56000c0500030080c1195000d40c2c0007034045003e01240004c112100d5a030f04002d2154901030b010303450060421065800703600c1d0b6240c1000f894280a600f00c000c0c840c43d280e8220440e141940c0d4115000100100d04e07407003051505170b455201540c0281003400080314007002200070503c1501500503100a50b99400d44d54121403280c00b006412984104010403980c5401750314290440b001701c107810716015054668803074144280d04650f484140000e2090110320341910915640d10640c2012212403105015203500d44c08014103484102c0c1000490800b040802c1d400800e000000800c995100d0505080c010400e4003019412714140c4111000421520414001c0d28800c43d898040740000c0d294000d411409008041d20107044a900c071b181000006a040c4a05c4035448034076070086487e04041020040c590507158451030f107503494007042c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 27883953 1250 27882703 27882713
    0x906030402010f050c0109030513081f0b03120c010218032407140c0105070327060c0c051005070e040204031a07180f080607080f04020108092401030501060909 70
    0x92980180c09090900038070700712240544940c40b940864440c55440c000f040c41c1055000405082c1012030562401a00c41c3c441c0d8440d42e61301d20408510802c03079110001c903c0008084e802c00f861600313004e0250303440461140c0c8d42007100d030050000f881c056500400d1300e01c0e0104a0820903501d0807001c400500002070070140c0180c8038040c07207a100541100310000540131500501c07242d483e00f41c00d50095a641e0603070280640c0200300030ba419000086c144032a4070361442e03480000810f04039210300200034000b40c0307a56400007800b80c140404103000038043e003080820814048a1981c0f28001004111450042001804442e81d0048184282e106000c01d10115407600010700c070030400404030120649401e9019100c01d2034170300103010b00100c0c6002c0460380741c256684010031a1540000c41e592900c4000e0261105602111a420031844c003c0000c0c0240d0b100318400c1c3d8122903080c065403072013034003140c2c000c1c980704a50050f140c2d0342144000400400200340300704401402e044004001d100400d90795 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 27885203 1250 27883953 27883957
    0xc030c0b07090f0b0d050708070801120314030901020d14090703110604050406030c060e010c0209070309030c0206130513050c0306012102040f0501180501020c010c030512010e0405060703020906 85
    0x2a098500308800118040c1c02000840050003824601034616aa074007440040399000c001d1044c03031103043c403011404d0746003d020b000e8010001a102c00640b6030900005070a814404030040d01007210b81e0080b00040804200158001c060610000d40d4540c10395507030710300b920301d41c1c503642c82080d0002080115606000c1032000540e5440203040790b5050b613000016015015603002180d00510b0140300000b00820016060b00f20340240e241c61003038403014001505c6105003004041d403c450303040000b40141d84a81e0003a41d0b00e910a040280d6412a26004104a900701107607239101c500780b210042c41940760081d010200d402c01418107108500e081d0b00c81100740d0101030441410b2051920050008989034417070398550b22180c400c119150f5680b0f00c0820310803042841018040780c0310324200c20540703803080c400c6410b60740c0c103800030240c10b6030450044480081d800c01c2034080210502a080c040301074000103a0003001180f05402d62420a0300342a800e20502804440c145803041010042c41c0d216241 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 27886453 1250 27885203 27885227
    0x10c0206092a06040909140102070314070f0c03060515031b0906010504150801050111010b01080619030b040822140f0103090506070801141009030204020c0a0c0603020309010b010c03 80
    0x6030241030710074082104402d81d41e010100981c425030109022135007076030b180d01400c0c0280c02840001d01c0c24403503010740c500300e201c4c182001d0300040d50041d01e4034040380d044c00200340291086410500d00c070380710341780c11200c20441d4208441080d22101030003844480c1807205005d50ba0210042c0031203008003401f10070901c07412181c5074000c40c03d01c00042e542da07000e1070a96005103080450707025001050136004104d020f00b40125408940f4026014106100501c0b59007003800068552501c00c0d19400100008803500003241c003081e603488000400090700402503030340030341e2040c3c80c1c40c1d0319110714840c006010501a0384091421034040390800c2003443d0f40348520a003030019101c042100d002803004a010380a01c03440079155108980c1406917995002c04413038101c804070001c002c8428007d508000c074541007140d222001440402e0180302600e41640200700c2481000c086620140c500c1d907404841a1140c2e0280001c640d010041008500f001e0051500741c0c54240f07011140740d4400c0c1e80186c010004e080c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 27887703 1250 27886453 27886483
    0x140c06040f171314031c03140f130605180a030507020901050402030402060307081b0a0e030609010509030f0c0c0315070e0f060d020903011515090b030106020d0c050123010305010c020609 82
    0x4c026420f10f038074144219509020b50041320485d4000750071002d000341112a000815010380e800c00030361390581d105a0340740aa0341c2c00190858200715070b120580588009862001c3c0e500c81c114000341a00c10800c25090000c0c031988440e5191201c40c010040700443c141c0c05140240d004004020041c1d64040c04c807a40400507040400c070715150072113141604400160901d0340b200c00060305246464000d240c4c2000a402101100e8450703039103010301030030f07580160342c0b10302690320500584980b016103e01801e15805200d0480e48007003000d4000070b14145901100302250311952061040702c80d030001e40c0550000703081d47c80c40b902d82c114001040d0144161035000301d48580c00303d80003420740e6080d0080b2000300443e241c20106d554841024a103a0740141100c0400b14240070741c001411641801524120749103278002e4500d8000120041d41c0d4000c010a08071125503841484201520300300d0780c00600740800305407550b46981149450340c216860704003004250f5002074100084084001180e00801d0100c1c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 27888953 1250 27887703 27887729
    0x304150203040f0b0702040b0d0203071a0c0d05090109061b02010818060405010b04140f06090601140309030711041401061103040503011e05011a0703140c06040f1713 73
    0x440481c11070140341c001d01901c00c0704603000038080720310201804170075008a900b0051402044100303c0c100b05071101c02501504003460420611120364140445445e1090034140b5000803c1300c014100303440395038000c0c04204042411441c95074407000d04c1000e00f00d142004504240d61010310000114000c600904100c43c0400089642ca002d1038070035000c6003824200c8100b400c01d403400c107000c1c2628401e40c83c01546003500b0740c20311001d04000075000e01e102c1c40342081d05484420501c0032003400240201c1c10300a180785c5444540c4c09a000139031040104001031a124010f601e4612307503a820702411903116a01f02052001400d1060980b2811030703000d41840100300e04a01109402d50060340d10050b0b06502c1d00c0e0201c0c2e041411510071841e001a42c002c10429a0b8984003001c088401209018403180010b0020100085c052011180301a170f00c07032440740c02c058400b00c05529050089804407110380c4540c0110003081484c07206100e03118424062541880b89800c6070b800c15030020b1003100015002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 27890203 1250 27888953 27888989
    0xe0c0301080723060a020a03020d090302090c1608070308070e09280f09030c020a050a1208030c0d060303020c03010c08070e1302040f170c060a0c03050d141806090706020304 76
    0x180b0040718162901c003419881e1201c600402c040c7d201c3d6081c07041903003d401844c1c0c03100c47c00b520800c949015a40e0007020100c840d154484840740d160003032084514002e0030036007154049040300020f005804e201c3d031385424403468120740042000842c0d1900f10700400c042002d00098003601202c507566451075052201c00301c580e0302c9044000d40a2280c446040c039152020b044140f50b801460a09641d000f070340c0c1000780356540d00502c14484c0d014816008001c821800300000075010030029900141101841c604141d4020a5030049030090340c012800759004000356000c6080078012400d44a0540c100700300b5a00e850704014011400f40c41c02940304001500d0f40c50383e513500c960b0581e0060b1504401105010780c49030840010207104103980d1100388640c80040100d850240708030b41c445a00e507950542002c0590f0750980302500040c0c28280f040d80c5900c0c070700c19000584c511240c851061070a500f803180c2c042070002403e1080180c00720070344c0d40001c4003e015160b00001150111510031f00380d02d4132200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 27891453 1250 27890203 27890249
    0x601050306040c02150c090f030c010207030305131806030b0f0105101b05100b1201090f031b060c030b01031d0303130c0b0a09030b010b0a1e02070509040c0e0c03010807 74
    0x8000a004101710980000b404180503119014103036500044d1030201e022904003003090360301d000ba28541c4d0f005900c080c00a100180c0300d8009040500e1810007900d4403640c60b941403400000c0903d0100352080d9565104000340207800401c030760040d07428611a291541050301080100c88940c401c80306000108800980e84003040303990220703c40d080002d07554500100c04403140507081c0d95103114440c50a96217040c54450041c49600e6083d544945041d613111910342d01034494400e04841c21511001088207040410018040c079440480a541c0004203100c0c010009821900d9400c52107000080036180354000900002c01c40e5003000d007080d502c0c000c8141a03d8500510340c015008000c440383c1c0454020030080e00001ca04060324411100c5031600ea0700d441c400507c1d40540082c20001420100e40000d4182201000b012001c0311881900d40b29521180403984840003610202c03a80030010b42c0812031001d03a4a03186400c006c00c60390f06850342d450f040809668200d54014881640e000030200b41d4407203 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 27892703 1250 27891453 27891463
    0x60f011d150613150206011e050d030c06020c061902040f090203040c03050f060a05072d120c11010605030c010507060c090509180f010501050102120f130b0a030b0301050601050306040c02 82
    0x203810700d00750b00103140e1100d100081e00e400150410b009845040000309540032303590740c900001200d118119600c10324000030418401080701e401d40500a04001030008150640010142099000300034000e50a00026100c0220092008070f04282d105001c140302414405043d502242c0c81c1e01d001603240d840b141032040421040d50702c002d24034131407610110015400402c40e83e200342219001045070343e031070074400c0e03604481040040c0e45195002600316465407030214205e0030106180780c4104004902c4100c0d1013203031440850000403842003280202d01c54000d00078200584410340142511140080000e0300034001d004004040d2a140c1003203001c80b0f40f050204500800004103072881038104410120703242c043c1800e400e151800350100e1020300007014001c89048803030607802414888802c5021144a4000b00341c001c0e0449801c02404411959940c03850021740030b0403000d0380e51180001c40180888801e044070354001c5c4d0420041002d076a0300401507982c01007060340c000c030382809030502c106d080c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 27893953 1250 27892703 27892717
    0x207080d0207030c060b0103020306010c020105030405010e06070c050106050a050d0206070f08160b0a061a0d020c0a0302010c08070c030804140a021806030115030503041a0417060f011d1506 83
    0x265101003040b5051550021a20f58890f01507102084001003810044050380b008541c8540420540140d090055105100440d4024001c000004400713038a603110b00e017007040980703a0b24001550240200d0510101780b0030300f0010318044030100d00d00ea243ca00441d40c0c00c0c00410b00030f4072403a808100c003000c2c8206080c20494680c0c0c0000c0265849a100d0388000040115007810f0704c17a5817200b8001181414079114003000d0b542411004c10f42091214540d03502c030381c002000d81007115024410080103c4041045d070010030720940000c1903a03242062f004180c020014111000c00601613690f501281e00322181c540c002c0c0d00404c03040008461088840c0c0740c12a28440250800110481c21084101101066005810031802448118140d00b40c1c0a2000344500010340701f178000700410040d8000801c0d104d458140900c01a908165540080001120030714648072103942109040184000c00d6000c21405880030007004440a12a4150742e132000000418140512032071195004041d0380d600295002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 27895203 1250 27893953 27893977
    0x10c0503040b04031b1409040602031009050108030405090906010b0d110403120c05060603010204081902040905030c10061703070b1504020c010603021002030a02060f060a03020604060201051008030a050d020708 92
    0x10f00ca680b4a02048541c1d040035a203501080120008100d800f80340101c0c4182c2d9030010020f180c50380b05c5440f01c000070350014140c20400706460100281c10441801400d0081108038040d40d1680e10345810312000142c005e2446140790481d60040c070290074100240e80c50b4020b40300b00090103943d10200d03a0114403441c0c00107060124141c0700b01101c10361044190180c18814000d81d210358075040207050a0303000714002c0e5102604030400745002c0504411950b180c06000420102c4d5131002501d401d403d660028013001c0c85508160044100400640285001495051924803401d01e401c40490344a026404004007007079031140204003401400190302c421004000e004664403a44012200c0c001c140d548812405540c0b41420038820b5400441518070010954014002541d101c9a24019080c0018290760780304c0c14442011016071282e2015201424646c1c0000459041080c1580007030350321030f0b104504a1340200030035220b01e64082c06464409484040158031048185841600c40c0268085121 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 27896453 1250 27895203 27895207
    0x3050702040609020f090406060302180f0a030b091606140306120705090c070c05040504030e1201090b0c03091902030d12090203100c0f03140f04060b0405010906050f060315010c0503040b 82
    0x848507031003001001b11140499003048019a109010342c240d016100b100b000840c3e0046988080d0f007889039060a0b20700006140b040225102d0365188104141900e200712640d2141e050300341d640a4030444200a0300290810601c00c400103c0014620310009011901561036240c1143e60000301b00702000140000502c100040d2511210315840c03034100d1001603500080c0c900c1c00050504003803003620300444d0940e86403903403640c1d0181481540c1c40c4643d41440d00399603034007000740030070440d80119001c4c2c4c040c5c5c000642c1c0c2e400d005c500f407854581350402c1c06e005000c0f1000d80300300685c1e000403400c0c100d100714145000d40c0d8421501c04402440840c030040e405000b0101076213411007140d441810540c0c0107460b444e1200d030541c00c5c22811500448040202a100e41000c113035042014202c0a5010b840380402294444100002c1016a0420b03032000c0da405403218000c0c0414946441e00006083c01512442e04518107020300369a8144080c49003814090940001c9090000c2031089070301510020411319 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 27897703 1250 27896453 27896467
    0x3020f0a03080709060503100b070218010f030212010c022a0604030501020307031404050d080406180b0105040506190317070c06020c03100c020606041a0a060203030f070201090201020a0305070204060902 89
    0x10742000b00440b2040b00140700100c022132030701e029209803805005c0c0c1300001044107007401c680d04025400000c082c4c4e132200c441c60301090407aa1540e0100e010b816202d103125203462861050280e00d0484074590411a4180425140b40d658005441c2800203131000c098104e240c092600294800300d0080b110350481000a804400e001e01500158044e180b90740e82044503907200402d07240864000d40c0e00600319045250f01184040c0f04d07080841e0400d014480000b40030959003100484003071000c1040b100070603141c004000d03624080c8036580d48418283e55680030408803001c1e0328901d0102d0301005008031042d00700c10320542c2500303042c5c1d250345501c0b060200304151501070103580c0d03061000d080ca103e4461941d103000c2c0040c041c040d4400d200000c0d0003e1a0300e440d088200400b600040359918041070710131709480381507070b80e101e80c01c001010307250007565a90078a15114040c06000030040019603062020100060742d00090406003039030545002c035101c1c030142c40081d000d40540c0c0d101a00c911300206400c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 27898953 1250 27897703 27897707
    0x270f1b080f06090f06061005030405030d0c020d0e0102070b070b0c07060504080316090308040303030e010902041d0105060d0804150e04020304030f020c09010b03010603020702010507060f020a1812060903020f0a03 93
    0x40f4040e00c03086088640c4204043c403010358642084400c1500007214000d10400140503102540c1c10038842c405407030038081c6d941d5150707084039201305803d0010303440000304c50125a000200181050001c7c40a48205401c2c20481240c80c480c3c1c21005100c0d9402d540007071010401d907000e803820958410000d00060a00d0304152100340c0040e07070201032003151003840c1381c007203401980d81008895010007510700f02461920150020542c4906910495485001c2140140da403841054400707100031944000c580910035540303007180c000804a600540e014001007002c15079240640d01290a001050416803c1140c4100c0f0900c0032248080d800178000b009110405401c81409103203011a80d080b1051707107402c0410031414060038032034103008450400c01401600c0c400d800030070b403050041c10422b2a00c1540d586d44400c4401d80001000c031598041140c1c0d601030b90048085180c0401504030409032801e14800400c1080207140c000c1505507a03180c1101018000e00031411080d0700401503a2a68081c1c1c140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 27900203 1250 27898953 27898963
    0xb0a0c020303090a0e041203020a023703031a0103090c0302120304030b0f010509070c0b0105011b0206030405070e010b040803030a0b010309080309011d010c0212030a110a0201270f1b080f 82
    0x21240c02c8018981f0000180c8644261002001d0660080c00170701c510106115076541c5290b00c0d20100c0310100c83c5c0115910781c44058600161180c0d81c00030391624100100720302507041c900780320304050511507080d0208080000840640360101c1d1500c10300390040c180e052942c070503079000a200c80100300030032000c041e440008074101d41081d01c0010256032045e40c00c5414190785440149549a42d0b401440154802c0c4000c90381a03a40785c4400c8103500c200e4000803455001150101c03081d60040f4000d00a0880d8003800074018000c102c502400c160404102d1078890000914240c501903542060780d034562711075086849202d8000d01a10f40c1e0b4100501420302910940402c480300742c0b01c00807100004241481809804030b0590b000c2e00351600000c00464145c0e00c090a040f4185d9195110b6000c002c00860040c906a10315400014402042100c441d08010001c0383c03d80210424003260000704100011001d00b40d5030041d006425000c80d100b40840803c41034016103d18855503602c145c2c4000d0002d8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 27901453 1250 27900203 27900211
    0x90a1401080307020a05040c05031f080f06061509090a0b0316030303090201080f010506040320030f0d090806152e0201020405010305010b0a2307050a030509090a060b0a0c020303090a0e 81
    0x1805017030b598540d018403080e142262003a00c00500d01700b0000e140c101c4802054044c240755100c10380c0380b541d55240c6144c509100d59558228503080130050000354688026801e509480c84030105007412900c500040b03034180001e081400d81c54986000341c100342c2d03040c015952811600c400c107042040c0c580c00d004004200d161012030108100e100031070b1a900d04030840a0403104001d07da1031400c1d0540d0f0b0755950146000160319814034011490388502c1d078042c0180000401000300802c80d40318503503070007414142a90b21102c20741d041441400170084c07168145250025003580c40030004800d0000d002c3c0405029583c000b0344100d0036180003001c6a0640080040322002d13601030009076250409040c031842604001d03000304001186105171002e280c0c1c000680c0700307065a035284c00d000f0300f40c85160414200013412400101c0000c0e0b082802c0c07518185c1250041d121030010001d0904040e101d90051061044a1050180d1a002e00301159010011907810130b5014080c0c910b03c0781e4801d0b965540d410300361 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 27902703 1250 27901453 27901459
    0x30a0905060609220804050406030b041505040312110c1507020c010306050d0209041b0801092009040201110111040b0c0f0f030a0309060603020301090f030306050a080c090a140108030702 82
    0x5008699030f40380541e8400d028240074031025000040c044410051140464021a20038405100025541c3d50790300c180402140554902c0c140340c6032618107200201009221481d04500d840140408a64801d404905000c20100000365000010b41d401d4128020703001da012442c8102c3c2c0301e5060994103100418010481502110380d6480781e03d0064095500a001d000d4000c4a581030840140c50007100075a0030600412a4403130102c0c4030004d0041514454020f511aa0f441e0a003c0c01040182294440b24160181c00112004509030010750410005400a8108400c2d0359009018907000c0d4410700810402c20066990381e03035100c5041140da04000d02080c190302a09102c181c0c00d0740c000c1840344101c4100e9000e51b2a015580d0400e50003080c03801c00c250b901c01c2e07071307200040010f803000d05c00c00c04403502a600700e200c5605540ba000701a07803401c1d04001d00900b445a82000740100c001250f546517070781201d10483e00d5031150b6101005220708685610703014a0640009071705e41000c001031094600903 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 27903953 1250 27902703 27902713
    0x9050105060a0b0f030709080d030b1003050105060912010f0e0c030d1e030c02030f030108030909090715030905160608010e01060504050901031e020907170a0504030e060717030a0905 80
    0x2000460b0038280b05600020108100d0b0290711220b81000716401201410440c80e00c0381c4a4250b24034201200030001f000c01d03601c2c4c1100f07100c3e280c152200441305009282c10b020b65810180412950700810101500441101280c103201308801c0d00858001c00c8203480412500e41c0c107030041c03a503070021100d6440c06809030742c803660851403007500400410703194000800c0500760b0800081b40205088200c00e011170005012440c0e240e030480b8015402071000c2c00041d900d801e41d041c03c112440c039002d02403921960280404104135070012039000030213070050400180c0c1806130f04086007004031a8500700311280d02ca480c0801c015800608441c1a101c82038a404482d0703803202400d581c14170030740c09540d80c03110b2641c1c010000520084000d0110440d0f03001410045009a8040350b0404800d550310404200080c240c000718404040007260700500078482442142819200036090607525100705000d03603000200b64003030002d0307070a480948848004070a07a8030718003040c2c880001c10016100700e5140c020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 27905203 1250 27903953 27903961
    0xd0f060803090901060c030203070602070c091b020d05180a26010b090105060c01020c1002030601030e121204140d080402040606020a0b070f1101090609030206010506180409020d0f0609050105 84
    0x3000081d42c40825010b0242ca005901300350b0207854031390102400302c0c1144020006500065654000b40c01e00d0f40c46080200070303c0341490490010b58441460030074185003284606240c040d070010341c921007400a410856503e890b185100704610740038444140c0c0007048458000350504101d030708004c2c3c040c42086450038410300d14618500340c0e9400b074040b9510100000041c1700516081001380385e40e1480030300062070090650f40160512064500c60004154040100146035170540a03c800c1c0c0d50001028042d8210304508001090090b0b64518000e50401000a0b080000c0d440550084110010848822004100c00103160501c1110201c1c012800c104000135428000151510070356480b00d581c44407980d07114811102140700702061740402c64200e80c0e4280c0043c083c42032900a900510001c102c100045c00c01034075107071041c2d00c001c0c0101400c0002d840c80c030740c00f10076014120000b1103000c10141c400c0d000040b511106881c02900003501824400308128065001020144c0700d14001d01041d03503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 27906453 1250 27905203 27905219
    0x30c0607080903040308090d0b07030507021204080709020304030302090303300601080609041e030c02031506030d030b010306180515100c1b0b0a090602010509010c050409090f080d0f06 81
    0x905076610403143e40140404d10004080101a040301c40019001800306501511072030081901540c100d00400d07654402d01c05281d505100050403d90220000341c6010318085056584503030743c1c4100400c041c3d01001050070035119070101d0b080d054008040f00e488203003c1c02c800d8410209190700c1c4140c03011001c404a00c82403014466441043c058488440d5507862400340111008000e0045031030f43c1240d1840307400c00a03040640c000b0680a99550203600070903105061604e003944a4109030180807500f00225940e0000389503035010103500d00411003001074001a0040c001d075412401d008603400141d110341c0c102903801280300761207a603841e08040d07081005100c048001000000001141d44902c44041290104c12500f541701140311850041c0d40e44c8160300058200040440028407581d0040211030703424050550400712040080288072019100502584682d101c0c000800e80c844100500340200f00d80d005c0002e40d00a40d21540e107401c41c0c2c910100404091042c0040d41c1e1800e400491402c3d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 27907703 1250 27906453 27906467
    0x708100603020109060c02040b1c140303010f05010c03020a06050c030403180605040911190302030403080901060503030909180106061806030908070627060603020f010810030b0604020405030f030c0607 88
    0x103038044e1034801219003085130841d804019000146c0c0c0040c0c951501241c5516070b500d810a08081d50546074400390060729000c20082c000b00c0104260364424030051010b40041c2d040801250800d0070092001d4001d8501641040c64110b40945540e00d000200010400148001c61281d032096a415041c040348845040c0f450b100c60080768009070040c8418440345469501142c030003076032091030504044e04020301d41801804071411400094001c03042c041015085422650442811002480b2150506002ca50b0f00d01607162003902c560043c00105110060310350740040502d800d0750013880300c65103e9201610743c580c0c40c5c5a440c6201c1c80c0140002d6000d200b4882d00c1c0d0b40d00d6002052501d0320541d91554005402800c48209558020080f1003c01c4141449070041c02440f41a0210312207207580108012032455101c09810301040d50100a00c02d40d12072003101c05c2d00c1d400b80c1149426151600460000d00a82d008250103100b410310b40140a54000047d00e44101c10070115007007a0754110f4121004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 27908953 1250 27907703 27907709
    0xa080106140c10051506070606030201030605150304020105130e130311150103260301060e1305060904021021050108100c05040608060102030d05180606030d0f080414010c0207081006 80
    0x640100f240c1d00c20034183d5811040e0812070740c5800c41403c44402000482591006204488840d40d40300108210f5070035008501c0100703000c4031100001405003c4182c0e0320311004100904001001509140c044a2002201c01810b070b520200f0f1854601224441c401d072140303600030f0380450340541c0e0b00d040701280007600c40d02c070b80450f143c4d02e0010391a6541d4100b10072100d20035180384400c0c442150b10304e2492840510300900d466a2080c0c0d4030f803018400c0c0503e00402c060b0301d030491400c0008000094840c06407107900184e069070070310080050142c080f100013000795001c00003030300740c2c0944030300c5001c003034201701c0c142c500320029a84080ba009a001049402ca40c4440d00459018801007000500441c4140d5100314180150f9103825084058801143d03070444507800000b8003c890b045100404200c2250301480c2a0000d1810002c5000080c044020062441c8208411103000400300840408803c41071404c150003441604104d02c4083e450309071900035084c251148810010f80c2d0503c41c0500d00803 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 27910203 1250 27908953 27908977
    0x10b040203011203050903101103010906150e0d0c0906080a03030f05010602071e090207080403110103110f0a0306090c020d0f090501051b0109020d06020d0c0309020a0b090310020a08010614 83
    0x10110f00c1c0d0b038182d4091b004281c025038980684c011903007070420070f030051001500c4040c01d0607580e9814101c0c04401c4038401c0e000301c02c42580e141e40c600b0100c0d0b00084400c4a440713080790030403880c10403803a05441c0340010340c100c8140d184c1045030010b0000400160480c000d4402d2300c082c02421b258102d0201121024820300e801680100c4003081007270000c1e00007040b144a05a840e0503007d0b01c410422007030b40d02612045651200000d0100144400c2c0c80c205080840300346070500c00c0b03410003540b40009014000d44589641c1c4005401c818a5004e03600ca80c00800318100144103042480c0406519500f04034084000304242c45400001c035031083e0180015503205840703403401c014a03c40d403003c503a80806200b1540d503581d07034804000340c0ea44180d500125441103d0159a9071090f038858425616004078882c02e150500c1001401a45d46541711002e84850200d5151182441c8001914000488240008003480052094401e42d80b02e9020b506070313021525002c181940d04890382245100701128004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 27911453 1250 27910203 27910229
    0x40209040f0201020a050105040b041a06010804032709050f06010207150503040f0b0f070e040603020d0b0a0b1201090209160f0806190602031803070501051e072003010b04020301 78
    0x80c041990701012034010710440c0c0310040c442d42e41c01d085980584e0262143d074131a10401c170402010282600126141c0d20740c403501400c1c0140042e0102c032001d00002e040c861400203124120840102001c40c46092801c03d0248954030740912000f4034007030f00d40e00f0040c045800059559400041c7c1e0408546054114010842c480c01040b5141e40014004460340340d121988180170a0910300b20a0046d03041500c00760b420b00340380c03a024007611020811240101d0801c4410805a51045803907696641c121100d13126994074071701040010044019059404800851012202c440560000c1c03e150f1007907a083c802501c890610303e2107128007103040000a0415a12494440d101e005016080400a00550003021210184100020450700a10016440401d592030041d280c5690b250290700140c01400c4503905100c0000c10501ca00900544d08110707094140d614000320340d0403170b1074403a0014240300d203000e024500d154130154032400041c030a6090031007080181c42d10b803080b68121751821040072 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 27912703 1250 27911453 27911461
    0xa0f0e130213051c02100507110402030108031c0c090e0408040b0c0d0201050708011a0c0a020306150306060a0f0b130503100506040f0506060306040b011103040306060317031006030f0b030a030e040b09040209 91
    0x31910780c40640100d681200b0127058400c00d49460014501803c01e650242d0344641c000605d001d040440c00c9022a40a4100521154006d4003d856501030396480d0b050690182c0c1d8a0400380654407847e407000c9032807580040c003507a85503004a8103100d100703640e031b00900254a5850b81156901028098400c3c100b941b1041140420141c03001000104658400e072048803d803600000d06008044a2090740300c03e0b0004540d25070314080c46020382c0b01c0c40c100e8440680030f00b44034170039000480f24000c0c540c406a00003103500076150102e903900300400c002411100300581021b200d0307019202c103441c450b0042b0b0a0030003070701102d441c5006080c401c201c040d240d00e00b10343e202c4041001518034000c0782ca0500407409000303520001d0170f000800155003e00700104241d482d516144007500052903021804002c18010300c40d40202100c5108201c41c00d80c81d01183c030448110542e0010540801025403520501c0c1182d8105078002d80a01e1410100322410030000d0519401d1040c5414201c60081d800b40e0448005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 27913953 1250 27912703 27912707
    0x20a0b091c0f1701060908071a030402010f14030c040f0902031b090a0f03080a0908060702031e09060a030b0103060504020a0806060d0b0d03080a110a0f0e130213051c0210 75
    0x10102c8007a0740c500354090343c80b001c41407460540b080c2c020030001001240300707004005040000800411091203202c1e041035a8603001146030001610003810001e15800c4d00d8469442240b0b0368007025a04031a0031b07030720701f0007c0e019001d80c4e209114031000c0110015001840144601c00c4d1b81c8180c0d25983c1c4102d030080151081140b9038425503150768020344220020814500d8041418080d610805a041c1e4891945070041c01011103540700c040c0603801541041840ca9010064030340070000701c086000c01e0600781507a0051401401d80d40713a000080840e03c05a800e6054000c3c00009400380c0342007210648603c18042603124080b5842c02240e0720101003031a43c02d0100040c840503500d0140050200050000101c402c0c0700520305a0000d8501c4080c40240b984611400c103d009000c03401500d400c0e00800e000e4228081d10f541181804100d070b0103c022130300c0d28180031300c601100c1c07502196990b00b504099024101c0c1030042ca801000078031030000b00b0100511003d0707129500142075601c1d0844007841 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 27915203 1250 27913953 27913967
    0xf06030f0b0a02040f030c03050c031f09030c021c020a08120a1101020702060a050301090501060c0c030201050a1101060f0e0604020f0f030a0207060903080420010509010318050607020a0b091c 84
    0x55210710503401c01c400103021a411017004040c520406074014050f01d0349c248146008207030140c0511a4000c640704d40001c6c00800c0f43d18048018450001c2840525414190381c80c400401c4041c0d0800f00002800314440f4101c0c544003070301c0340300f212200d45860300e40320030a580300303d04c00c1441c0c0303400c804001c20b55209000e1044001c008403040005480d0524076030100d2140d4014100d4400030650100060018800c00e01500f0b024121a242c54014400e0300c0c0c071040c000c00366a10020307040c0300000504c00340c0e4038450141c545041038004002c2c080560b80308144045081244180c60341c0660b20004900c03585018000c031052018400c1c1800c0c10422141c003450890350001c3c20409110f03508200900005207039000348040c260203521135150702c1c501804c0c1003010265031a44101d00c00c014011140c1c540ea0044107981196800b8a8002055100d4400802d0f6200d10310002410b01d21420042100b0300f5800118191010b01c55030040d80c0b81c1d2240c0c2403280c0d1301d03400c1220a01c0c80f1103003030050102162042103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 27916453 1250 27915203 27915211
    0x40c1110020d09050f0106030b0108060705040b070203030904050c13050102030708030a05071704080a03050108010255020f06011203050708270f03280204020c0d030c030f06030f0b 79
    0x40e18050950303640d86448403840112170580d4690f80108248a44201298010f00400707000c2c0c2058540410020700d50304c185d0040081040e0046402019901c04000342c0b07000e9040508200001c0c2084102801c0f00d4018002c0c03094110030600000c2032551020090342c0c6010791001c5d400b030071615070040031009450014070340001c200381c1e1600700e0b80d1003510385283e50286006042c056502e5078000c80040980701c05130405001c682c010070840307041d840c07414502c040d9221607024000d0032960004040381d101900e20100400e6085121100b040407841c481e011115065070b030221203005041413903040d215502403107150100410604040d000c640510001c2c1100340c45404000d151800040c0c02c6401c5145144c10160392001d40030b4008080d0515540722010a1812001418a00c0d050400102e9104040701140d5140b4120380030001191a03540680b580c9200100c01c0c0e0f400341b03005480c001c0040c4602000c902c006400d1540d06810201070344280c0068039006010a05003a03455100d282d10410050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 27917703 1250 27916453 27916477
    0x501050d0209150a0806030610081b0301020409020a0e040c08010806010e040816050138010c050a020603041b09050103020603040f140601060203041d070e10020c04060605030402040c111002 83
    0x840d43c90b4162184400900c1440c91640302c1080d1418104141031424000400c6d0441c0d001e2060340911041800055160807201603104107150b0b40741107130120380617014507802500c07110f001150300980e0a8001e40c9901c010a0280c40401caa02c0301041c2c01c84100c102845140084e030010001130201d8003140308185c0d0b1081c0141089450107803510b01210b6900c2c4406010755080e5500c030304280d2031224200c1c013104960f4515032100498402e04c90005e8001540c0d00085050001c07400801c41001000c3c000a501c0e290018680d80d240e19140c10804240104142d119000300001e11020403900c1c9244503c03070507a41c000d0006400c69450380e440c60444015001c090303900080013010140c1100c0c0070000c60b8080d00d41a07018548507131800140d014038544051540c0410341203401048882a4020b8800091403002ca0703202d60740c072551a6050b0b0520052101541e0028205680402d142d43c0100084d030066200f03840030030402003901c000f01d0302d11603903800840664112070203c85a00d05c0580107009102c2010b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 27918953 1250 27917703 27917719
    0xc05010b06040f0503010e06061c0203100501090e07060f020601030f03110708010b03120304020f0108070507060c23070b0109020903030d0915050906040308010605030406020910020f01060f0501050d0209 89
    0x1000004045070000c1d80440304101003240c0130700ca1810203010321140c001e40b01c2c0040529042a00c000b44424000420f40c04820004403079040555030100022010b20411000c10070140d6120401480584001403602401e4400d000300081c1c41c074465084d8958a42465001e01a075900711b6a070003d0b0286c01600941c1006000707008000700380c1003403020100030079a2000002d155003414003454142201020030308000b80c3c0500410000d40c0301c0c007000f400042d10034030300f031041c0740e071351600c2540c080c00340c900050900c2d46018003118450f504544a4084115001141c209503401c0c04014415442400401041003070350306d0040108a000d50003600001d0001420340c1d0403d80010f00d00d20842d15104000c0d0b944020681241c105030681784107280d04507220801410a61405032400381481d003040c0310f2482002000000542480b20390350580750341d044010907521804064000003036541c0f180a030381c0380030ba5180010014025658104007021604103840c0c09d418a920b494582000b50041c1e441da903040040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 27920203 1250 27918953 27918971
    0x8060705030a0228020d0c0b0615070b04110a0b04060e01030e120a021b060304020604030f05010603021507060c0509030a0213110304080d06050103020307080c0c120d06061101020f0405010c0501 85
    0x102c01e01c10040525001302d070880710503071080024902615031614a061000340c1c00510b003c103959045d090b6100809641d4052103c0c40c1c06e040b03801511404c180644280d055030180010000b40d4424440c50090840708010160740341e0403074540c1445140b14542c040794140c0c0c2d100c03015500a8015882070400704041c0c47c0040c0c3d00c09039031241c1e980511a640010f800c10301000c0390550220681c013031801c0c4203440f682d04603d407550101d00307d88140d002c0a0900312141c40d024003000400d41004001c0d550207024000698240200150140c001907822140c4900744590125450320901c10303540302802c0240280300702111502801554a141e104211a064560380b4a1801d0105070300214001c61140028030f03512001c02000f10115025900a68101801002480003481d402816560000c040d0301556070f03500032801c030092500c228004000c0d8a10008035042040441039481a01169940d80303030f96004d01d05a000e2039080f407103544011910140c051005000c44d51041e04510240c0d40f080000141c5045 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 27921453 1250 27920203 27920227
    0x1030b030715020309090901022b020715020c06070804050606060c0102040e100f0e060a0b0f0c070605091e0a032a03080d0f02090a03060506010509060d022208060705030a02 76
    0x1030b2a540450142c0e0001482c9402e5060100f03090360700481b000000c508211342d040004042c041086545c801ca0340b5814000020f0f09042e5040301c51080c1c0c41b1005043c28051030640d003000e9000016050743d5070103982c00051009001c0c450b000d108a6129003d0082c0380c0d00c4400701f1040f5082515104091741d030038031011640115000381d03d8001c0302c02c000714081a0b884c0180d100040046030b0030010a100d044414403049480d49202007060310225405261141da0000c4159082e0188440c605124400d503040007515680000c01801c04250a076042406a0105c400112526004035100c41d00729844190400115860811401e5807008040240040304080c0101400c285c196410a031140c80001402d005041150701c10381c038681e540c00000b542050520400110b0b90031540c44050601912640081c02c0e91388100c0840c1d042e2030700109013a1701c0350f51202c2660001d4011701c0e07417805c5c800754428000c81e640141008070310403100c00304010b01042e5200300c2c0c1140d503500060b02030211aa000d0180b244158 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 27922703 1250 27921453 27921479
    0x30b0d050a02030607050c030a0c02040f02160b060307030503040b0912060411010807170a090501020d09060518060c160516060f020c120c0f0a050418030206060103050f010501030b0307 81
    0x1038080e8009168620071401018103118000d071040061140c100401ca0303074000c5c0402034441e141002e0a00c05c00e180890b0010801800e800740100382074030720004092504c0010388107041c423a0390148650341180d40e25001403550360141400041c02c1a40140000c000c0c50154000a2a000c0d0000e0b250980d4500c103040018500b80007650110f400c0600500c16542550340100d03c15405401c0c0e00c0d004060014481c02031aa225007e002c82c0d840c0c980350310120052040035012603105442e01d040070070200c00582021001404107491006d840c203854981212810030009a450144003d402c00506e803200200541e466280b403440220b55134054400d40d0010400c80701c4d04000109500d489025181d0107504c8020f041c4103000074868495944040b401c0310f001e8002490310201002030f10308085500c00700700040c170712010a80c01164440c0c10080c64040ca02000702c2510310780b611a40844031251121401901520b000300d035402c0342ca01a060041040b58403a8000c0c4056200150948a916403682d240300040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 27923953 1250 27922703 27922729
    0x904090804080105090d030f0507080c160803090c0a140f09041a0a0b010e040903080112031103030109060f080307020105070b0a0b090708100501021212090313060207030201090e06031c030b 83
    0x11b400040741c00100d182c26020b9502800400700c01003041b498840405841c840c00901034840314140450303080915004004244501030b00641010784030300e0070380032042d070320022022503901643c4c4003100043c001c49090704c41080131030f006080040c103103c640705010702201d0081c41504d076a901448034002c04901210103a000e1041000041503a525200c005044011039422481c0a48d281c00008008030fa407160010f810740301c09043e08034464010342012204180c9482242d02c2d580030000c00061410a142d0200d0b003207681c00b95001c51515a1280550348a024281010340441c13010000c01001038400c02c443c070ba0111030510300044100d00c41c0c0201d0450481140c40d880403400806c03d001405c501414039500800c0309200500e81404c1040c08031040780201c040d401c0000504001017100c1c0401801611152580d0405001086640f41c2c0002d40d01c940ca48010f0b80420707440d00c0040703200040000702a100e03070b802400030101c4e400d84051804100b0207013400e940405940d041b804a85aa5060844c008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 27925203 1250 27923953 27923971
    0x905060307181d030c0601091503060612020a080d08160c0501150f05030a11061b1204030b0c03070509010c060b04060f05030d020105061008090a0209040605090601090c02030904090804080105 84
    0xf010002c0f82c0c1000010760544050355042d4018030400703980c2c0400040391810340d4034903640880d00030310761130003c0b5a103100c80e000280503606100f0b0101d200c0c0001d07070030540698000c031110030205540702c0469888824071074460001640d4070002038850800f110900340002d203245428000d03007041d51182c1e0300b114048071951546815045007002420914003181c0007903c001c4020b0000ea022a41e02c0084e0128280a0703240074110100d05c84665045020808111024040988802c3c00006512074a55031050008840800d00c3d54041007280c1d80c10015a481055207894942c600340c011030065030f940c0d04103881183d096490320800402600c07140203400003405080004588107083c40d08250601410581c05011680362400300b117101d550380c00003407000309918100703251940c071055580d9081c61a5000041e402c540e415040c401000030f40d42c02907106035980420781c0e1182e41c9596085c1c0989c0c40484090f40140d0013030040910514040d070003045180c1c400d100f070380e14040e6101321341801e45500311990742c2c03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 27926453 1250 27925203 27925211
    0x1d09070b0a02210a020a0b0903090904120210050f0a0e0705190317030403050412060608030708030108150106080703020c0a0f0f0309090603020a090506030f0f071401050c07090506030718 82
    0x2c10410b2466400214801c3d01c0c2d040c3c280850554001c0d034600030700ca40944070007142000b084000c2803d10843d010300700c014019044900c1d2030305040c0c40398840c014032070b00148115030f03150030484814440d080c05403020b80341d000c240f40c444070103810140c0307214809141d42d40601c8400250301d9860205200f10103d440980c080114690700f4401c560302201080304205820402c1007000090b44070049509503811112001c40340342c0d15003002c9004210751381006000d8880000e1200900c41f45078007840c100d580140031903a0310300d5206414440d2280038070030328011419480c080346e10540030780c01901c00c40c880c64048031880d90381c03611114101d1510600603105072807845c14030f02c181a840402d00d400740c982c0c1c0409102e12440d42e408207040324030b030784038000c100c5940714040340d0607a5040c80300c0c0c0000e64055041350704c8070316540c8142d525007101d84a50b45170320240100c8000194040d1064480000388000545011407030021590044c2c41c000b0052980741c0106000410040c883c42403461902c092004009 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 27927703 1250 27926453 27926473
    0x16091401030e06040b090f010612022103040f03020a05010c020306071d0607080a090605030103030f1202040308030405010b010e0409020d2310020409230412030612080702031005011d09070b0a02 85
    0x2c7c00d19070000150040c90341020740a0142060141a0030b03441075040d0f803056120608400d0303280c4006442e00d031f5034489000010700040d03070042d5640704005903802154014021a0346400541b130080071804000e400d60041c00c0018036540c090a040c030042c40c408070070141c03c900b940c0c00044090380f0005007121a0040402c080401607400403511019000c3c6040051440d411030320094920788410340300030100894644010606c04194040e580116440041c1030386908082c0b41041c040d203a9004018001303071661242c0130307141c90b0070301589800b50f801030700d03072001116540c907985958202883d182000c000540d65031103032113808111205402c0313520480181c0751410a007504096030030141c11400002e400c404915554843c0000c51500580e100b04c904a04501c0c591050300540102d030b10001c1c143c000000c072001400004801407504502c218140d078078801c9444a503208443d020300a080200c003181a5001940b0ba104601c10381000710507044a03d80c9607038403040341356a44200350502c0141c00c190000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 27928953 1250 27927703 27927721
    0xb0a0306051611060c0a09120501020a030b060906040b07020a0b2206021203010e061207060302040f1706041713030606030203101a150705060103050c0916091401030e06040b 76
    0x10711100d40701c83c40e22404880c4002c1c84203941315000740c10354458007000981d401003280210b00c00b1000300508400a81c0310016410124000e4100d000014042820140c8031556440c184080314140c85006241d07900b010700700200080c04d81c0040c48101c5c0c011304400c0001c074580702030502070110400d08940d00011019078418014038070345258405003d5501c911050002e107413080058030305446941008088036540c8100117801714001001c4409103002d110004502181e00d90001c02c2135481c10040c1c0751700b26a6607102032010f4403294500109580003180441c001445140350000201020b90100381460380c040f401e008a070240b944121002540d9001c01c00c00c506044c400c00d10f105070702c0e013020800200c1c800140010300d10786900c500e1103202c560b00340c1342c042004c00c03085d50b040c1504003040341c11b69a121314050796200b0924000c0c510030030485000500044080711005819051542c0d5a0140303460203a440c42c1c402131820798181456103800700d902c84013404019440c03142e401610b0365001c6050103014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 27930203 1250 27928953 27928981
    0x1d100501030210030506060901050a180801020c0f060105060a0809150a0b010f110a030305060a0305060a02030a060b0c070303080c21060103051311060d150605180604120201120b0a030605 82
    0x1030f11041c1800e2a040003103658442040c0c0d4400e01003804e02a036209107019048030b5010a8801e02400b014070100041150302c1d05601030088029000100d81e14401003140c0c81c1d603aa0400d100b0310380d103d0030803c100ea010511498100307030400c94510448081c00400c40080e1041e60048070462903590b69070110710741c82c0da446142000040041e00700503025101c080c0c811521400c0b44034002d81415218408242e90381c171064404802103030854240c40407401c02a1002020358003d44441c142d060405501047c0c1c40345800032280505000d60007000403d141d03a5041d02c00301380050014200e10009c3c0701c0c1103085071811901140412040d80200074615205001404072071024066002d100b010720125000a13008000e050350058080b95200d0701e40c1005c20030f00c0c02400e10600c1ca1035812107070030400500307140c020024008000c9408450070303101d075040090100501a130b104d410312145035545800c01550050300c910305821800a0080340705c4681c0000b0403650310495000300e51550b45c542c01c21120580c8014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 27931453 1250 27930203 27930229
    0xa05030a03060609261207030c061a0901030b10030c03030309030201060e060609040504060209030d0815010f050f0309010609020408031c09030504031709030601061101050a050907091d1005010302 86
    0x30070240b0a8284072141007080c05017070203100144182d894014040703004200c0000180703103c01c807050382e50b1214a002000c3c8203030349504682c85800d03c8501092072095140341da01120000c0c00c280380c660300c1c40d00c5548003014007074012601020704079004404208502e400a0156009440204000d0700d6460020308407842c0d40e2062981017514000d1266660790f05044a0b005017003203501007a1501c031414000300911845401903450300c40d0b4010000c459412254407840f80b41e03d840010411a2036000640300c221500c1500300028900300611040403103480042d641002030907000080140d04c1c3e81da101c040380c0c4a6082000c0962000c1418100c40e01d840034200d102c816480414484820650760140030b174040e0307000c0140000b0031605c88480802c40d01c0300382c075000c2c80010200e9200313503591b00011701120041e0441b100300d035003404005169030105004903802011400014400145444036800041500814404038140300d24807100ea141e00811808010b100c074000300003115495441001000642d82ca = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 27932703 1250 27931453 27931457
    0xf110601061706090105010f0e01090504060e01080f0303040b160e0406080102040513060503060c0f0708030c04060e10080f0a06080708010b1207060e090606040302030a0b0910110306060f09030a05030a030606 91
    0x44c010b12403640d208030b81801050190070805003080890300141d8003055590050b039001482c0400004200c0209942141290000d0003540c25419018440e180c90740f00c211005884904600301164000312051410f41000380c146ca892803041c0200400201601d00c00d500103a840e030340109080c091307498003256a1104010102003003105038a081c0100703848140040c11a002528045040e61395074615034200d0710002d60120f0401e640e0324003190054000e8106005941c001405c0c400656a2400c0c43e11184204400f40d45403461142d4136030800d00081c00c0018900d48410391144000502e01d2030801000c0c1c00b4014000000c50254100c5013809916413050314201c010b54440d940c00c0100c1c64105106450300241511190401d0b510a07020503124400c42c0c0c0025058407078004044240150054950701884061064403085a07541420900380d40c28042045c2d500303034081000c00c00b1460450020103d903c1c0c0100c6070380c00c103120107000a007007480c81d040540b441e400014680c5212a4144036401c0505868 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 27933953 1250 27932703 27932719
    0xd020a050606010203040621020702120a0510060e0f040201020f162d1a0f0705060604050606030606040504020d0603050706110105090d0e040902030709020307050702040510150f110601061706 84
    0x42005240e4400d00c3c606101c81c2c0c81230309011160017903a4044614054025200000fa000041010381d66101c06c108103030784500079000c03800340c0007d0310b00902044580c070f43d90700d4403030f6101d01a0281032450b010f04124150b100e4440003008488090201d5441d100c00780c503042071401e02c2c0c00c0d4000308082c003141c0100e0003501c20300000600409404600c4060301c800c03010030074070032810406000d698403651030701100c40b55011511800b00180060200d200304019502031029865035424050f490001707031406075000005001c240a00e0405501501c0da000244d1004900a69a0b40702d02d42080c10a4209000203040701c4100c070003d000c240180360b000344a0380010a50042c600b80021b08007142548210b10450f2200c08401c255507080242d107005c0c20244804560742e040012014105a0000500704d020780e0400000805101407407048200302c076035484042c21070180c0b105080f1100c0e0700f452100420300581c255410070000042141d0760181416866002c2d005c040c40d00e01300e0a10310020401c1d8801d204c0707 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 27935203 1250 27933953 27933959
    0x1309200303040303080714040b09100903170d0f0507080f1006020616030207140609010c090305030906030903040e011206140601021c0207091b08060102060c0f0702120d020a05060601020304 83
    0x84500302c903018517140700e05482c0c40b401110030507100403609501c6003020a021540d801208002c00380031800b00c0d00041801c0c180c0400342c42d444d0161001501e08044c0c1d00c2c0011600b01e64000a150145d05007400048070802445403108803070003031307400d02c00050841e000c115030303113011011180d008030010700c191207103a10b0624000d65030040200205524069800c03600340b454000e4041da01c0c0c0d141e0000340001241001062950b82d1441101c1e804655030a1400342d0040ea4010701703e11080d41c1c0c0145c040d5241801e021300f404020f6002030044030003884100800140c030f82120700402c0c003904450415104800c1d040c2441010b07101c00e00c58890255040400303110381aa0001003140000ea0402c414100d000d202280503400d10006910030310703225041c460003001261150701c11213040c2c90035440380c002c9034a0b100c004994800040701d08900720803003004000c02455120b40034101081c401811349544d8401c25046a080800402442000d41d200302842e404004e024000664055070078030046040c203203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 27936453 1250 27935203 27935209
    0x120506070c02040f0507020c2d0d080405030708010906051810111b0606120c060313050a020402070b04020f0102010c020a02131803020a0b0108010c0e01110c130920 72
    0x151141050003504010301c41103440301d411624442080d80010440381c0340001c00a9107440307502105030b01c00c3d02c007030b0540c0c9007000c00d249403541801003030310b0494107600600c001d215024013000070035076200070300380000560fa82e000c21803000900810000400d50038031914010080c0e43e0080c0a1042d2103102c0701e000c070751a03140010800410f41e0300d5100881c50703103a41d4000d00c04611600b914224100401b07541e91188620000f0b82600540098071407158240480c2c03440c60301c80144c0c52609910040030030120314090381d1040d5040303515004000b0395040c4ea0b80741d0700060482e441060125500a840d10402066280c80b0011440070701003030000384038618242c50001e4440c180480000e101e0044070449050036001179004410b00045260b816400b1429420060350b0303895040c0040301e945403000004034001e131041c02101d100c0010364035284142c0900c000155080c510300e440e80c0c02c0c10311032210844030658444000240500c41c0784e40c00507d05c0da40d42058600c00c038180b8461040039811442c0141d09403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 27937703 1250 27936453 27936463
    0x403141e011803030b12010c0306140604060e10110d080402040b01080606030105040e0f010606030b030d0e0d0f031106071d060310090c050d02030c03220f030e03031303050c0108011205 81
    0x50350503e80000c00800860004000c01c00c01e030486c0e28a986004940300e10141c05034812000c0d9900300b05c540401d0000101006124490b901a000011f410700f0141c0c0e5043c04d150400b1060350340706052041141121402e802c0c5412090240400000d80c940140820343c1494402c0300301c200020302c4c020030180f5190000c100c00d0300c0b040c41210f0203a680c40f001c0c420411014884040c0c1d80c1d00c00402484815621000200501090700c2c509102c2e0240800500c1854043c01d281205518060221041d80805441e900f105403c010010b42c02d108041009648042090062912907010f41d1154400c240300c0c0350061020440c0604024000d240400c20300c651036480d0001c68003280d507403034000310316540c0300802200d280c0280241e0442e010b00210078070084440c030001844c0b083c840300400401110707108501c40d481004592000d00060040503036000402c0c41a11401d4414401604032881e10710904c901d8402c440507a44191500e4105800d0b6a00c00d6034070440b0f1500400c001114800ca40a9580303d0603269 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 27938953 1250 27937703 27937751
    0x1080601170f0604060b1c15030b07030f020417060106020607030c140c070b03040803040b0708060127050d0b1f0302131a0402030103051606020d050a080603030403141e01 75
    0x1c0b0aa03200042c4407980c3e5500803c000e404904045511020420290484030b81801d4100016900b04068482c071541c5da00f051000300c075040100c1d40e203030303440d0800140c005040b120307607140f40a41c01f0000880c8070300c41e240e0740203032038200c0030024a0b0039858084002c0c2042c20140100b0105401d0185800000b1785c401864642c02040c0c1c10060340d11103140700c407680750044641c094141a035010003004140092800954826800344034000d03140e0303032815030448904108540044c08100103403084e00f41c200a081d040780e04070f06003980d460101a2210001070002070f180e482180d043c0044002c00000700d0385407a00f5581424140d03501c1800780c0c1503a0020b06004980c10035007220560340d02611940700c074a00c0c10b0400500010b48115541d58590521b40d40300c0071503409803d040e2003003c03800104030344006144403a1209554440b4102164402c040342c00e0301003d01040c1d8103220500c13001c0302040350b500c900b20208414200034000d01c0d19000843c203200c0990a881c2c3d596916150482d40000551500b0a0403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 27940203 1250 27938953 27938971
    0x601170603010f1104030314091509040e0f030a0306240f14070602040302090f0106090b09060c060705071406040c0e060d0606080607030609110403020111031b0a020108060117 77
    0x666540300c001c280140200303103900e20500c1c1801e15041e004114040200300340d80c084c3e542c5410101c0c150b400c03900d4511800c650180c000304441c02004030301030958041d2168900040c000f00303600310b00c1440985011708504500c2c8103604001120010240c06100d500010304401001c80302c000b5a61080710b08025500080c1c400748540c41c0d2443c41c2044c4205440e014501d840100d140d215140e41c2441d10080d04140000c03802007440e0303008a004602c0c00d00e8007074103d540d0395a400d0710144c20040c0ca00e100341c00880d4a250032140500000d82d1001040c04030a200ba900e40c1d944545501550a001c03d00342d18040b414003568000f1001d000220b2420102101910241c0068440940701c100c0403984d89a11001d01408040c6030103400b0032600e0002c02d0460242440d030b17600344501c0c2c2d20340b81c104040700c110002180c6490001c000c200010b500824482c403078070b8031500641c0d0504500c165481131008042d080d118042c0c10080340d040456030820300182c6c1112007031900d40074540d1042d501c6c0f0041000079000c184 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 27941453 1250 27940203 27940247
    0x10803030408090a031a0f0a0e2509111306050a0206151c060f050106020102090d260d020a02100507020307030e120d18050f01050d0b04020d050c0306040c080601 71
    0x806864903c403030b400035030307111b01d41d1056a0500050020b40031410b40f003005807100f00d070002c140c03000b10320b0040310548801400034281001c01440c00148004c1071075980b0f920b8140780800000c80c1c441c20302c154500003005945656580f004003040481442181d00300c0c0c02030103018800c40d952194000361855000e0340500003044100303025000201c0f481c81c010384154100b8060070314501001150b800200c41499020400e1000340d0725038900381e00741c0c040c0c1012640c2000901d2408000b1801e21030384210503072a080a0038030441004403204400740d010080808000b40c0008140000c41d50401000d0317203003c00043c00b00900d0811204c000d40340e1042400c003400308207441c0c401044950701c501050b141116500120368500c4e10740d1102800704000a46031081d0180b84680010301803e1607800040c9010050f9241031610500313070300790303002400005580d40d0040e9003801a020300d80d00d940f19440c080e5483d42a001c0d228a4050308000a4504880d107803030410032a40c0070b105003a600044040850030200d030180b5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 27942703 1250 27941453 27941467
    0xc0309050307030318060906020702030c01020d02120d06080105090708100b06071b09020318060903030402030d080a090203070b0c011811060d0209030a03030504020111010507020c1e0904030e18010803030408 91
    0x45c0341c000d04020303028610700480281005003590042036014400d8080c2c42003d20740c038005a84803403520058001580000c1000d0000e050084010504080380030000070f4081c1d1139402090845000302c51141003a40707e44070a1085081c04c02c8030329403080d0f80d4070042c4807a161041c0402c00b03a0107241e00c010100d80150703140300240c0d04424140c2020b0b181e1108115121b1030101d80c6180c4070004520203400c28020800894241301003c01120302c199005002400f040c0c04209080700c0240d8018101d1020a41d00c4079004010b0703400303010040040035589400b9444a010980d66400c42d0310030042840d14030f103d0140700c000101002c070200d40144044451903100c0700a181c00300e010384990701440342d044c040c0e200290101600f40d130011b80214001e036941d031220a01d01c8101b80c01c84006880103005a0320a04076182107191449030311102403450205840d400c0704074008200321420503070701100403500700c2c0124045810000510314400c3d05080102e0711a5151003411a00d030300c40500301800c0350b00c00082d18 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 27943953 1250 27942703 27942731
    0x90f04020d09060f0f0504020d020613080303070302030f01060507050703060b030a020a0902070b0f070c0f0201110d080106080606040e0a021b070303050711010306380a080603010c03090503070303 86
    0xc0d03000754a24003010b00c040911460040001d1944140c0180c00701d282c901d04109102c583d201d12880380c1c1c0d002d40442c45400007502007104503004941c001c91041040d0f14049108a0b041c03001d14062b4085440140e06ca0a0040a10701003403170581240c810450140b040c80d010544c002404000c40e03410000001d440705103000403a00306145004081d41100c80d09a0008840510351f00425141c1d000308041a01600d40c8101d00310302c00d030203455110006107200705200100c2c204105020000c1c0c030504010041c2610401d030203090040c1c0119031004101650010032145800c120890b0f0701140440f001443c0504040b2a0701d032019006e40051041c2d41e0102c0c149100010620301d06100d22030f0741d0211145c01e41c2d0380c0b0300201950301407841240e058035020000d0b540c2e54000d01403041a104007100011000441c01507401d5205052801c900704544840305050f00961140001d14240d100740e5166100b500d082c406250a642206486404062400084001103003002c0252200d140c0e06280108034400c0081035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 27945203 1250 27943953 27943957
    0x11103030a0f020c071d0601090608040803070302070b0c09040605010503072a05070b0c1b0a140f090702070e0105060c060705030709030204050115030e010608071a2101030201081b090f0402 83
    0x460403e00c45d400700070585503044a000c03001440592102c41041d91540c0c011070380040c0724843e00c00440c2c080800305001801141c09940d0001c107910f0018101407140d03c076240b0010782074810043e9280300240e000e045080500074600902801e00300240b45080c065002040040c0f01450325030100c04221a906809007020005505903030003504a403906500c07540c00a1095000403541240b5106040b020001c90f1000b40c440f21100800411074140309240c0030307507a10b01500850a0301e6000780a404181d050b0355500c030003240582c01035030017405924107203000199131180c182c2206100d00300031b014005110704001030b040d902400f6484c0258583d00c0340311041d43c0281564100030342c4581008000f01e0502c6001c841b501103060641d400380b04240350300d00780324220740380ca0094408540000f4000e1113070400b040c0032501d20b0450380a800b4030b405412005403021054100c519507140400780010821740da40040600d81121219445001101d1004d40301c00c001e2140b2075809004841e0309001890319078403541 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 27946453 1250 27945203 27945217
    0x90b1804110406030203090f12040302130f15051e0307030f0c08030f120129090a030503070507090c090f0e060a09021606110c03030c03040204020c0703080307030605011103030a0f02 80
    0xa44544503074503440f014001e50000c0f80c80d20302074417803851400c000100000714481c03542c03030101b1520b14241c2141c0074414100280580300c030071141c5500301c0400c240340320f1240c98042182d4a1903540e034117003001c00300030701c0a00c51200300e181d84a010001c81e18176903000ca450012282d010324203031a0108a1b10301161204000d5220090790701010800040c5c11040c10003c09000c0351607440e44440e40c0c0c0320b0111106507500c3c0c0b069081c03050310300ea46000a00c50100e0080204000017001d00c0c048503682e690701465039002c544203c545400408040003a240c5a0003980010b0030181042a403060900e61608540395161041e009100c0303419000c03917030030f846580404001d031140c1d04066554035031400e0100100280364a048a9040c9455440c251080903182070f11040982c02001d1482c640741d0141c0f5011540000c5c2007aa40709900704440e80307004804100d048010752241f4201902c920305940701800321480d6030f10082c10300c21014510078143d800401140d41c02000c010001900c2070340607a49030300a0240790 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 27947703 1250 27946453 27946481
    0x3070803030709080601050d03052b0c03060305010b0916030507180801050f060109060905060c011103040302100e010b1c06060f0f030c0807080d0c030203090a090b0f01090b1804 78
    0x81800340581d8005040002d40340503101700d03195039070313620140000c1403208100a0000340040c0030011860301c400030000d1940300328101d5080c074800d0072501c1a044035a49400d41000c00da95442c03c0007006020b0241d41800034049400c200d16181c072a03802103540004400e02d1040540d107a0000300740d94000c1070140070030320100c00b600c05803944413149103000f44410359900d0040292400019000e610944228045d6082552001601481c00061024940004d03910b8520b5548400a82c80606510000b561003a0b000c0e90082400703200340394841089609482132a01c0d00c0c0d042410880180e00c41140300105e051951240c5001000716043c00c000078919a0400305445041d03c03400241c0001d0840d04c00e041da4060b2400c454080d035030f10340580d0741701c0c40c610488015810a05021600e0340c0100c4104035030030700030300659142201c15000591b40c5010740e0000c00d0103666401030303050281070407441310550720302c01c0c00c1c0385441a0070b007011640c042c00303010071a940320030160345c1c08800c6480d80d0704001e40040880d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 27948953 1250 27947703 27947707
    0x30406020418050103050c09041e05030d09243c0603060b12010e0726030d050106030e010902030a060509010b030105090f0c030a0804050405180a03030903030c05040506040e040203070803 82
    0x240c151140a04070070305c000d03161441000785948081c540b00c545507000f55402065641303903407101d1414800c96218030340c09a4181c0424010305c030107401940505400c42d80309020341c000c0300c0e09c1000e60740d10480405034046505813810011551031100c0c0c9040c01c1c0e000c2c084020109003c0c034518246802e010202e1041032029040007000010442a50007500c500141103d40e41c504501e80804d090803207850305c040c10030760b9106c48030410101b2400924419400740501c002c5000f107151003181032465201c00d0a50140725624030040020300d506114400c40003003090001d000c0003e01c0c5c0c00013640c4a00045000d80b445940c0c00100e0b80d100000d600c03135092040050000e2241d89060907d8541f41d0a80801512160007000012400c9103004200440010381c040300c00c50405017800d06000c01410300800491855070440c40c8030414a108014042140b0f1281d500802c1c2c0310183e10f0005c00b551440280d840921030140002d008540e910f60541d0306a503201903028240d80e80741c0c000203280281d103500030b200b98000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 27950203 1250 27948953 27948989
    0x1309050c0102190f020402030a02250b07050f0307080a18050313080105160f020c04140402030d080106090303030902030a0b0403050c1b01050f030403030b060406030e0606061e0304060204 82
    0x80400c0c40c11040200740c0a8030511801500054041c451410340200243c01c1110140014034040d0f000e190018201ca900506005138140071800324498100c81c1d5004c1a1001124802c200200e14000c0c0e10080c03601c0c115091128240c001e86403030001078000c13020310884400140300d0340c0165001e0941281c03d0b6102000604490074032945a07404209890601440e60300081000c14050088900900200e03052080124090000b11403080240d03820900310301807602e001d070703d41d51280600741c0c80d405001c0e000103d508081c41054900380f015020384040c0500c2d0001001a41e4000c4204411690181008515103a0620001e42441442c4000034280d440d6041480241036005014020201002d0201c3e0914080309001035090a01014418001a0100203400e0800c1340307800236540007031090401003280301c040f200041a0303801940240c0002030362043d00b0a031400042003e01d4220900380d600d14a00801900c000c0101d9103109090a82c082c80080810100000e076811100180300c02e481d10540208 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 27951453 1250 27950203 27950213
    0x90c130209030c04020c0a03200303010303080a0b0d031e020703170a02070b071203110c07080303090d26070203361804020915040f05040605010e010b0a0e1309 70
    0x6280e60700e0182c8a584590322690030944201e0703d403e00307090003c00c08240c2d07036581165000f80303c10b801c1032001c062542c00418200100087e40c0070354803c0d15454443d1500c1c00d41c0004507511b0b10003075032085403280c408001098100d5000500b80c410b8020180701d12100310816413a0810542c00200010b0004840c81070342800c05010300001c0070140c2c26604025941c0f1005081400741543c080c180903001200701c0c4c0528080e500c42200300c0b4543e111242483e503041c001c1c03410302485900c00070f4140c00000821284038420300c00c0c9207251905050640e00003111201d40191070001d80c000d1f150b03008a00e000b00d20303d00c0c0208265010080d40320ba0544d0151140c0c0310b88480b41e24500081c82c44424651020421858401030900480d10f0701307040c103001c980d101d80800c00080009800d0541d0307001641d80780304d401c1c1c40310701030070800090070307000030a05003014507106040f10303016070294000d01c411074014001d050110044400041040c40c14440018207807000686103000e90091032101803620700300c0b0342004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 27952703 1250 27951453 27951457
    0xf060d0b0f1012030e0d03090801050709090605150301090c09030b040302070801050c0306060d0c030f021303140d080c0904060e0901050708090c0604170102070803040804030b130209060405090c1302 87
    0x451192012252a40d118000560703d1400070b8002d0106040d0407040c5203d042440820b40c00b1400f91401441150380c0d1782c449800c6034821381c0e4410004a01c00014410b803083c1c1c0c0501c9005103000da600e0b040450541e40c2c5020b0ae0700040c0035001c190307501c861a85d100342e171049a224000d180c1040320130405003005d281c047d548030107a20807640c00307508000000320a02d0305002a42d00c900006090705150942c01d41850000301401d00c2c0b0303401496a40c4106554841041c80a01300623129680300c005070030306506081e014070340004490907041d808500c280800c0d0b13520440c2590040f40e2207102030b0708ca065040014014040b950040500204468100000a81c2c150803840c000c40564480c0c070310b5600c410076225200c8003149001500b0074030030030081060241068440544804480006040440507a20030040f0b81c07040d00c05a80c1c4450104091041c861040446500811070302c1105000c24042d90115500c2840280f4080c07050340d50b0750014484190600461074059001041d181d0304414030200340c0d0080d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 27953953 1250 27952703 27952711
    0x1080c041a04060201110307090e071701080a17030106020c090a0609020324010306080c1003020408010509030703020f010b090604051504240b092b0f030302040e15090f060d0b0f 78
    0x560034200d501c004000500301f1079026200c142d03904c2e1407c900b48501300000c00e10251000301001410190881d4500071520b00d50302900c0711801402d15440541803201e030518440071040d180b00c00400041100c1c030340020f039030380d10700a0548040303080d80e4030303c0d00c900000d204136400203c05500010801052203410702e0140140c90801000d43c00303540e21035004500302c4142c0e008240d07040d80507202c60342003454400d141ca020700b95286005032509031100250313800d450302070351849000c0d4030101d150020503030103005104031641110000c0103a1500d4000007440c03d100070b440d09000f95625800704048000345003150100001c0540b0902c400c0755458040c518010500384006556484108040740c0a01c0100c100c4405180c010a0a21081100c6031f0802e00c0d01c0c03850302c0c40c03400c0d4440c3c0045080050520301103024440c0c0243c400613103a038548030b00000792450060003d4032101008240c1d14990352100340315508040942d43d030001513034540002c5031911a15480141c882c40410040100e8040034028040c82 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 27955203 1250 27953953 27953957
    0x70e0121090b0a05040c0e10171507080c03070c020105070503130503010b0102010b01050f0d2c060601080903070b0604060902070503040306180f0b0c1b06090f0d09030201080c041a0406 81
    0x2940d50700314509003290425140148a5600c40c14204403010b68803811540101e0240d142070500c0340d5a2940c0212840d49d00c1001000b40c02c40d10001000d001b08451040c0d1103032150800146a190800b07000c2d03410b1000410a400744036120160a040d07921550a540c07030541d0000071a9910043d16203d080700e030000e48101c40c403943c28031840402c00d52041c0106403080c101a1038603404d0070494002101c00341c0005080740000360b503590074045915030042403038141c1c110150350b400b0702d42c0da0b4000701e41c10400018005814400c0b00c6080c13052041e00003007195022034010070300030a03c1d00e507600054041c19084c1d103c20394482c0041003000038014080018003c40348a100100100003909a0700701400c2209480a00602242c54000c00403074194044140c0c0000b00d07225040c42c2200185507071005885040c5800b1495010340e0400c00d07045010410703040942200401810066140e0400070503050071070000034104290301000c90444400d40f0281c40150a290007290910b00181c8124101900305e8820200 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 27956453 1250 27955203 27955223
    0x307080a0606020c0d110d02090403050a0801080a0201080103060515060d0227060f0d020c01110903010e060f15040204050319020109061403150f031c110601080303070e012109 77
    0xb44090000520300038800700034140208080d29520782c11070100c4041602c0b6080510100d0b140e0059032095a058403907440303038507010744a071110301d80104000030503007080d903955000c414108090303a080a426411a80d202101040750359402c404034001400440043d41c00c000040707596130b13030fa220503000350141d15280243c2101c4083c8441100c86010500740c071103500454200310015100b190500200009100b4440140c076142c886404142112032004000c007100d04086408125441c0a00030010700c607281c500204601d050400ea84d510115002d010f408407561102c00c04a004d4940750140e4005040080507035100c8002e5010b0322190181c905400c9001548814000c2070380360260305480e0402010030f607900d0942e176401b201c08400e40030311240c1c26400307025401c4c11103142e507040000c280014880d80e00a003181d000e4a402800c0301c0700c06500840b25400142c0144255000007080d25800b103550b24210840d084004016035000ca8000514001c854840440b024845001d42004003100d2060110704 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 27957703 1250 27956453 27956459
    0x105040f110a0c0f05030d0b041d060a0b01020a051504050f03070f0204050604180c060f0c0510050601050c07030308010602060112080304060c110f0606030c041404030c030201110307080a06 83
    0x80210307225203828121064040c05403040d4a4414035014100c28480d0040180c5008035494280c0703190010342e600000c050b10b81d003130b9659234142401054182c100c25565600c1000d107000ca541d4a800005008901243d03850394640c0060384204041510b20350840c00707072a8421132080c0394122128044900383c031648540c14007020360800010031251301c5600007040c070380110142c2d820007018000c05008154401c1d01c0e4034851103000b0b43d01c1c1c0024519803040e4140c000d11480c051000d0501c400d40b4015000740160341011502180f4080742403403d03c0303000e4070006603039640c40300103072194010390340c0c40d0495200e0741e003010040641140b0740f281039840c00d408403041681e0300e200ca00d40140201c0c0005100020a001040000d0115040302d4010304143c01c1c50140300e01c00c551072a2130300d00303106003030700542d07025405112090506210240c030f020020b440920084140070020000103134050002010450071104c9001414801c0d84051a40806544151f9032401d01d0350004081c0c183c152801107880d03285c200c0c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 27958953 1250 27957703 27957731
    0xa05070206040c0303080405030405041a03070501021b0603040501060b0a020a17130303050a02121c1119080702010209090a0902011106010612020f09090108070f121a0405010f0501030506010504 85
    0x707140329a500145083c040d42c11942d003182c0051020304212514030081c0000f14040d51203001d900245100840040058180030702010b240c000c00d5441030381507400c01c415111030b4a4200700d031110f900c5420344101e6680e460740e1501c030740100ac440c5c0c800003800c20f02103607049071345a000c904981014020340043c501c1d034070400d008800920071071401078140450070000b0030010f4002c0c400781451490a00599420300f00c0c02c1c107065140da1101036036a02c449840040400c0c10400c501c15904100d600400c0d80e42840f005102102440380003904080038004c5040006420b5403003501190b110100103402d001c001e061405d81c1001901040300203c0c08180302c0140d00048100c001002b40c1200e0b44d035900d012108030404400d070001c1d80a260260103000040158400d55150000103900800007500101401c40c40c01203103800d0030107a0707003143c0a0034882c1d03a079442c0850420b55298000016004e0312000c00d8680c1c2c37030b203907005124101102443c14208000002400b102142d4541203d1055905000c2c9a00032001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 27960203 1250 27958953 27958963
    0x10030605060307030b012718020705070e13060e060406060527061908030c07050a03050d080c0702030d110c010306051e030109080c0109061a010509040906060b0d02030a050702 77
    0x24250841070610001d20081d1082d004119a403c060404130070041c2e03004400c8249078904020b40740d02441203c1d081001d181451100b02c0c060312840401c40c01c20015640303064440310603101d440c101201d00004116603a41c024003410001d0f074400010442500d542c40303100e407140000c403070540d0322034600100003540382440311125500000518042081801f17510b0b4107a50818041c084980044d00b0114444a2048040c4c0000140944074000d40e2500e038072480c824500310050b00824001c280c2c44800304001303500061780c0400d150003400c1c83c0485a84007011b54203e80078800b0040d500d031151424040c0c3d85034100c0301e444000c1c060032040e140402c40c1d01c2d0054064801e20704c02c030354010b0f4180c203040198540903a480e60761910000c1c00401c070700a0070340b607078030003908000c10b905d41c5039645d9509402044140d2140e0140111050000d010003007034007001a005000364415180603a8584818404000c465804540039020083c20152550409500c250007500200c80007500c4a2820000c54141400055 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 27961453 1250 27960203 27960209
    0x201090605120612030d020c06041103070605030c0a21050708010501090f050904050a050a03090e060907090e04150615080105060702030703030f0302040e070c0203060a050903040621020315100306 86
    0x240e14040761552000e018010b4480200405280811b1201c0341d4004143d0008210040f000b40051129050904002040d004402c12032840b0341c3c8910801c02c40309411800740d13507020360700e049006e4640400050688041d9200b20a4803418449085108011850350340a07034080c02c019512400c103a070325040151580c1d07081e4007420400071a12031040021b8030304040e100d6481841903098a800d0050342d51031500e0018681c0d012804070344a91000c1c0058011611b5240d407080c0c1c1140ca0a00c9400c1040020701a101c503402070031880c000743d0002800f03100e603a58210b440d5400750070301000001d030360303807600080048110740d204000b956000c000221381c6800c0c01941c44444e001009860040e00d0350350280c4241003c0c03604482403503000e00c000541d000c80440c2c1c15108089580b103091050b1003a10405042080c01800702c02c0c4140b8040078401d00040010559064504a0400340c10042c10b082e2507045508d820000070518500000c1040f0901601c2440c0c265000002c3e100b20041c4a070b021410303000c0d561580 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 27962703 1250 27961453 27961477
    0x1b01050114060703021005010b0301031511041202031c0e0f0105091003021e0304051c05030f070f032a020c09040f021504050402070b091006060c080d0e0a06090201090605 75
    0x8001c429a0385490002011040e10a004848001c21080780314801e4400036802003803899004001013081c03040e651012201084140d900b0440740003044a01002d500a500580302116100303410321085440030055100750940300403e503607110505610081a003a926500e040c050300001c00b0076107455000340260383c81c031000200405450a0710f03081c120000e401c00c00d103102c036403050742281c0300d0000003200c01580258080d01c040c0001040102196060b007028441c1d101c1040303420000c2200e03081c001080079810680c030b440c0030310038200d02e0031b022030151542e190350079030030604100654074080030580c5040b442c29254080c2c2d00c00d0754038170003000510a4202ca01811002d54400003400514102551b0291450600e141d142055143c4000c1000c0383c00108048038228140c105002c40325400300807600c0003003020f03801400a2420510020404960400028030b00d500c04203068030240c0ca1500a5248484100103ca0000c1000d040074400f03400c84e2641603000c00e281e0400461070500c528201d5030b0390220380c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 27963953 1250 27962703 27962729
    0x2103040902030a02160501090c0605120f0910151d070219020a030f050109020a09050105030a0605040f0203010e0a2603010b1803030a050714010605030a0b150310021b010501 76
    0x20a03001800707544000c02103a6116804c0001d0682580e506072401c0c8400d010340000070b44e1034040c3c64162010501030b08140d09200085c010791040540c01c4400d25406081039113101001c2e00c0c1e600842e4900f003c44100c044950381055540001142a03a61440403a150840c8200b0360940d08481414801001d43e401c40058200c441c0382c0c0c899541040303600d80358500c06000d034161299a512085460b1905203021211030351100d2541d002e501d42080550040c01e00310204100c15494800007940d100c4034400000c01075615400050280445485130650f4681c018000340400350815000d20b0711800c81d4402210180620000c41c42c84420404500d21480709100920b482d40c0d080485003105500004035a44070900100c0302c41c0e0040d1400c0c000b80c02e62600c7c41d240c0c0313a00e49a20303141021040503100e0520342c0c9a854203401300810f1b40c3c0061548102d54100d20398215949134081034145023078980303000913018880c18161000c0113013942d001b0200d85c602c900c105030065111000c180d099401c20302c9852000004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 27965203 1250 27963953 27963959
    0x305040302090903040b040603050108160609051e180106080903070201200a050f010204050f04140105040207140a03050a0305060d020a03060f020d0f090302011518050a06030f0b0105210304 83
    0x41d10503260000b4503881140d0410f646c9002d074002c00d9015411510000b0b448400400c0500410046810101200703211441c016040440c010700b140550300c1050321a049080315034180081d95a520305141201a10400d181115011074a42c000000e11504000074000c1c00040c200660100940c3e54443d816900c01c2c900c404a0103c0e20000c079445000074805000304008180002e104000801c02d0315019000940c80d50b141c142000030224002c034100e0701941c103001d2040380b014941106c45042d583c0444005850302094101281c3e080c0c540c80440d41c45229403500301081c0f542140c007521002c403650b40c00f030001e65075150610041d0942c241000703402070900350b81400054016044a1402c00e4071400040c00d00c001c0d00741240035034046e003044106d896035404880c4141642170141c80e443c46000c943c5118010b02d0318100020042c1c04603488885117a40340045011180700d038214500030b40e080080c0380142182401c005074000d200317208443c450400700c24010155600300030b8110f500020640510304140c5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 27966453 1250 27965203 27965209
    0x1050603010815060103020f180909030403050c1504050603090109060f0207030e150d0c17070e030703110105070c03150614130e01090203030a0206010f060302090a0501050a090b0316020c06070305040302 89
    0x2101030001c0b818541c00748080483c1e09a23103000f5203040d18000104002c0c00e510003044c40800d60300a0072910791390f0810403060001c80c4001480d031031151330a440d03101c00e89003c2d001a00d140e024580010780d00c420000140701e01c1120540100c040c59005640811005000d10070010480c0b080c03103001404135074280480351940c905038010043c02c01568090914101b11032a41c40c00f111402248403010400000801d401080c0c030700c5040382e001107103003029280440c41c0340000e5914409440014180810240c0400135a446441654007150f80050300d510070070f03141d00d05040e00016405500d84898502038001a05a1100a01802100b00a0321000402e4001190302d0003601c48825803119a64a4001c00720068a041000301203200540d405002c20b541000e10b2008080310541c005010540140b20340c0342c90b60740301c121074800c907102420001e83c0c401c100314054450044513481070030b2000d804420401302051403280740780e04941940c03c2d2001e600030b040030000385018107800680010024481400141 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 27967703 1250 27966453 27966493
    0x605010215010b0a11060702010e0c030f0601050d050111030106030902040b0103051005010c020607080309060708010e060105042d0311030d030207110603060a08010f0207060e0604050d0f0c060603050303010e010506030108 97
    0x221003807805c1100e80d41e000000f07503e0321100741c4403003006070f643e004001c103583c00034000386640d03040850180104021440340c00c0c0d070354581800f1310762042d1070004403401084000d6000180000040c0c0001d510313582e4070503001c2c0c02007440c4032003a4061800c02c2448451076100348a240e03ca1144e80d8900004141424011603454110303d01c100d800404c1088803101044008003d1807007404100004c2201e8500898018284601a80320003080c1c0c480c03009011442ea002020344055600c84000d030703803814409807880e141100356481d01040e50307032034820044240100c0115658410740c06804464403015400c0b4214203d1160920203012004502c50103107140ca0401c004603080180140088003e949902c03000303084590b01036914000070b5000850400300802c40c002d00184d000780601521441c41c1584072aa12040005424020003181034020780019000f2040b019090360080340403c2260740701c2c80e201c1d1b900d038420b00401a08641641c00000c841c0350540c1203c0c10707220848068402c02c0c0c0300884000410f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 27968953 1250 27967703 27967717
    0x405070b0c01021201030b0601030605090405120307090509040b0916050904170909010b0301030c0e040201050702040903360b0c070608060307050405090a170c03043302100605010215010b 82
    0x255003c114040c0344501104d2218083c40c0a00003240140c18080e002608503000e591000d4040c011101c01c0101041d40407900c442c1c0c50742d82d600f46540c1c03551180400c640d0340f80d16800c141ea0100c03503001448140640c1c0110783e44240185803ca070314031070210b1003540082c4098405e180d480200a00080d0000700e03c025008001c2156180c4c10342001c1c11400090034401090b0455071906a0100040090045034515074000340316401c0c84500d503007070a0300000c3c0f19129080d03000e401203841e081080b007050320840081e100c000006c0da410f240ca1140006050380702c182c03900392011103c050b44000c40c29410719811124640e40b41c000900000d0319010054655110003809030b541801513038400256a1a14002d0718446c04180014110054207842c1c4110b1491070f08211080d41c0c030701484401c440c0d21000048400391003184041c1032010460070f020f40301030a920710801e03138201280740f85420482e03000030f612081c0340100b840501000741c880e4012039594011a81140d6a841c209004104070804c01c0d00030301007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 27970203 1250 27968953 27968977
    0x30105060f13091a04030f0905010804030c020f04180308060307150c0302010605041e0e0115090e01091406060114030405070e06010c0f1407051c060c050705070305150108060405070b 80
    0xc0c0031040e4460320303081e08080c542c224013142036a0401042680c042d003804404001402d041c00072a040a000a0403000020401403c2c4481449500190358070b51840040c4004020014420034845e07000c03680e00e0200103041280420040c5010480c0e40c03502280705416a4040000d81c0d0044061450803550300d881c8681c1034040d551707950000703e41030700c444c0182e00c03150302000310000c486c9159442100407101788000d84026645481d08040740f242010b4000350440e41c12080100d00982c40b0180c1900603e900132008000c06400302c2085602c8c3c00100301144201806d0300c40d80d090020040c02041c2512040b2001481e07600400e40500c20031074403010b020703046481850041c140d00000c1e03441c4440211031460584080d03a5403603040076070030410464000541410350304502840380004a070b000c1000d4078030000b03203040e132208000703d81c0303d20410030f031303100c40c2c0d00142162030003035070b030704049031070380c030942c0198135500010800400c82c95400541c4900495102c0c005102c440d1030105205410f0b0004102046 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 27971453 1250 27970203 27970211
    0x509060706090819030209090105040c0219060b1008070f030c170f0a0c030e0a080a031103011d01140904020d02030c0a03061b1404150302090d05030711030105060f13 73
    0x10070418030442c4005071107418101d59401c10401c2d8601001d204003024404c060041101c8609500d822102074116442a1004580030394140d905a0500360920500e1a4582d84154048140a40c6801540030864166403d1100001d0510704954042040742c4540220320710607a0310348118440ea110b01d9a05540c3d1034040603204032031401c10390488040d00e4154510400405201c040303d058416208a0702050034108255800a0180c50322402074000241038094013007041c0c00500d01a8000041c0c81c008008815903d60b100d5410903001481c00400002100d40300c80007286080322401f043c500c103031005051070581d0f0f440d0760070003a11000b1154102c1e050b01500c00b1408083d12080b10070340145101d220040351400b40d00303c1d5000781c40e2181c03800104110a04103030304000c00c120f8040381d099542d4070140d403541d036080b510160007900c9a047c5441e00250f694045805008000c00685003885c8111441c1e449540100c08260030399105445040d1b02c1403818003450402d203007809107006000d00c8810017003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 27972703 1250 27971453 27971467
    0x607080703030902031e0a150e0d05040e0a05073c0504051903021f1b06060311150901050c0a02040c080609010e040b010504020a110a2003010203010b030601050906 72
    0x148103801041044011a032900b0340d031821843e080c0981c040305010700c0014500310310412199075849070a64405070032402d1030381d0f503200d146005400002d002c107410412200300245010303000340964000d120b1303040e0840c03000d008282811003500030075000b40d9160362100600c24900c11200782c16a06d80340150700b00e640d68200081103446010075a84e030084507031142c5840303914000078804d0080440c0c900343c0300000c8007101800180d0710144000000c081308442e415000da10342d00d080d1a40f03520402c100380003880390304440041040175003110044c3c0780700fa02018082c04012062208016517120031404900e028010001594810000f032b00058110b0b0045030100802038002c207086425951011000030b1105080241c0c0b42001c030002d42c01050440508842e625064461035003044060241600c40c9070000340e00400f2603c01c0c0ca01005d810151015079680c5021468004110000305400740c0d86000c07000500140ca240c18403e40b4101c45440c484a840c2d641c512004540740e601480b507282c0c1c00031b0144641 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 27973953 1250 27972703 27972713
    0x2090307030b01090b150a08040f0b090303010306113402090901060e06060c030304260a02060108010606020d020601090902010c1407050306060607110108061201150315060e040308060607 82
    0x100015405000b020000d5414202d044013603d00c1c0e0f000880c01003ea81440d40240c5422034126052407200d407811004c40d444503d000840c80038658409090494144180108614048020b6040740e110b610200020148444a0b0045008201201310481003034851712100c401c0c1c084400c2c148812034400d500d0082c800d80d0010715070a80a4035194940d81d983d2000344200740110342d507160030070000c0704c2081c100112110000c0d07591000038002808031010603e56080621444100e5216a0548140c00d07220400a100256185801d10900045c1d40c2020f00c005205400841d9561284c0c1c42680504546da081a000001a2000e84400c030b04201d07401d58044007140152201580d0303868018003900c2d200d031810081500d0250043e01c40d5206e20403c00c80389002600581d0707452141e0500b0b0911000941d00c6070f000480c50181c40c0e000c1c24465003000398100310710700b044082e6000d0741c0c403a00102601c0d404404000c030481c0d1060040c10900d0404602040109020700c0c1b160b43c2c080740040c0300d43d06d03103000b5070b4503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 27975203 1250 27973953 27973963
    0x60305030306011d0d08120601090f03150902130c0201051b070303110403060608030403050c0109050d060504020d0b01060201090c0f0303080619050607060f0e010506030705060a020c040e0c030610060909020d020903 94
    0x7546c0b010004190360454032442d201c4d00b500300714240307406d490040c1802600b01c640c0d0403134800205680035841000301c40c80c4454101c3c1344600d030000c050b18103060089011720003421003c0b02c100c005520b4040001e0341300450394072049a112040010900341031441c3d8081c3d005050040100303080e610709000000020380c5902442001d001100d0246460300d00e5440c0107031903c481c66105c42d051041d608030a014648841e500b011036180c000c10081815201d600120f06141c40d42c980103066040304200218010f03805410038425a4415500041d54695490060380801d0440c00000d00140c041c1c40424003614081d22600070743d0710b03070084a26240e035079500040c2c219030000310b04440144d10750303490b041d10708024801c00001e070100c00003d100501d46a00002d450725500c0c040c0601c0340d5408202c00056a1007041004080c400c0903200700f010807a645006641d038110203a0b140c0c8070303201d9035000482c044461420041221103c0d1227401483e41065000c3c4065040612441c8445900f4030649500750750400c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 27976453 1250 27975203 27975229
    0x70c08060103030c05070602060712090f0b0a0b0109080a0206030a0509121c0506010c030210020a090f08010b0f0d0b0105101713030210060509011205010204051f030f060305030306011d 81
    0x3c4180b0503040500c0c5c440c2c20070005a01003410f540000703042003042d41d00188136840c2004400b02c00601d82c2540d160212076588210030141134003000c4010014a02807a03408030540a009813228982d40750341e60030b844d68038a002c4500030b40002d400e101040101203e50001900003042800392030242e001091034000e150042c1503c00540c1a00c407400741a00d924a106540c5c00240a01e040070802c0d1041e10082d42c4ea292000550482d1139002801280e07042c401c101c200081d0410030140000a030f980e00358180070748200303801c45114004a08100c001450100001d1412941c000c0301e800150780f07003c040103915011103e6903001e00c424145580141d0201c0102e041c800d0701ca01c8410210380c251400c0c000e180c8800743c1c200420482c036041051040381c1d01d4000b00760445001c01c080e442c7c6522a407031320302e01a004a80c000742e0003804606c180f109500950719200550181d035602003000c40c654500010a90b030f03080c400606980c00800c0414415407155113000e0046400001c81091492280e0120f107858041d40c07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 27977703 1250 27976453 27976457
    0x3090a03080a09030b15010306060807210e030a05030a1d0709020c03070602030f04050f010c050d0209190308030a0b030105072106030507060903050106090e2d06040303020306090f150105070c0806010303 89
    0xc4206e25640c0c140c841c0001400d11440c00000c1d928000d00080d11a44404075040e651040d484942d2034030b0801900180c17110070b41401540d8a801403082d000c1e0581c2c006403800f102582c2400c0c44800392402c0c0009605180c44020014503035540340046d801c7c001e52010031081c2d202d010411840c000700703056000540c0210f0b80050a640c0300d103018207005040a0140034a19221b03410101d80ea0762099001c01035820440a2410050b62020128000394000e0541840200810000c62000080c0450f041c00740d4418010307484180800c551010416003250b0084800b0349c04903518510303003038000c9214085080d170100803100000e80d0b580c503601e8070f910f810302c9680100001013003164280b003040028012400201b490080034000c401e1504c1c200c0d40c407450500717014201604200008444402c4102d20744030408003d034240c403441e00707241c01e0080c040d50003111141c4c0a07800310b001240702101000401031248940032000c4400605000c011074685c1c0c071030701081d03c3d48040300d032010070019820300219000314426 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 27978953 1250 27977703 27977731
    0x2060a030216080c24070e0111010501080708060a141506070606030c05040c053406020309010b0f0108070917010207020303040e060918070303121d0d020f03090a03080a09030b 77
    0x4070484c615104814080240903a10800240c0409203500c00141c2c1211b4242031241070a242d51004842003c4285d6140c24a50300782400000da403800801d00c6425603808005032b079143d941e903c0081c416244603080c904000007450002460301c00d00148000280e150090140d483c1c070100d40c56050231303164150410741d140c00709003004104030310f0a440351102015003820201d090110700940030034011020118000c6e54040c0015901010300182181684690f00810454403130500ea1661b500034201c20240c203000c2c1c103140c48030815560040d141540f0603e065900d0519a03800c0c80951269600c8102483d82550b4003800001c0060b5402e1002c1d00107008520352400300c41ca00702c0304000411001810300c0c083c2001c40d00c0c04001c0100049460b9090300d415080100040700d401014100601200c007030a1284900d49090855500d40442c1d5084059615030840ea46803580c50b181e5900c1c1e2140800441e0b000c50540300400018100d280a070001000504000c05505da807034446000c079070800c40346003810841c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 27980203 1250 27978953 27978967
    0x80403021c120e060a1808040302040e0a020a0801140a020c10090201020115031a01050f061e04030c03030c0506010609060e01030b060c010204060504150507021e120304091d160302060a03021608 85
    0x40c0c42043d50352a00704126a1b06821241c5950150348114007010f40150703221407080304941e00400405002541c0500b04024060344d0300000c038005c1105410310070820380f9074004951900020300030b403840ca09015000d000141c520b01405030052106090407410b654a03410344183c24202000303000d008500980983c2d101720007840500b0b820101c140c00240c890302c1204a003c1e0aa212042541c44104101004101d4140c4098012132280125800100825002100401010b41c445074102c2428070580440d03a007a42c075400706032040400ca020f003d00041e403d501030419503210390420f078400c80c1c010300740c140381c001e940c01344a007039034400d411110100d84002410400c100c03001c0300c000c500901500d401800c05010b0341c00201c0440059030404145180800704c0c0e9000d5070b9020b00e041c5481038100440c0d5407203a55403003541c080e00040c490146179801000402840c2000868101115240c401d800040241583d081180f15000301c02c0181c2015401e220181c4417101580700e041c5918002d001d0306454890b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 27981453 1250 27980203 27980221
    0x1110a03060b040303050304030c1a040f1505060f130905030a02010c11070302014b0f02010605180408040f0803070b060301020a120e030d140a0c080403021c120e06 72
    0x42640b002074101c0341003004002095100d0240ca8126915141800351100c1a0800030404000f14124041d0856182c0a102c2049900110700303290502c00d04a0003076413100c0b1400c1d8012601e085404030b400c240358207002031007840e0103044017120880005001512030f0403610744c01d1654218094580250b99030745802045540c00c210030102242070140249800fa0950740000c0628606550480000c4240c80031003002517120720219011200601c103003420b0200e182c405a00008040012401281090b1102c0901b5071041c005c0d502540c2014103180c8119000c3c070000395080c04002d005031284c1c0410f00c0701240402030090035100a00300780000315120b00c0f460400c0d00c5440c40c05000507110360b1041012040c4075070040740d24001d114003940001584d012408030f250a40c459211031088107850a01140d01c4440020002401054041420010322030006400d884074035007038070081c015a0104140032565800c0510041010066141600181c491301240c0002d407505c5ca00c05010b281c02103810032803030319 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 27982703 1250 27981453 27981461
    0x9140c0910031703040f060e0a020a15020316020f09070203030402040c030c0f11070506070b0115170a020306010314010303020105180c1011120f19030b01080708090a0501110a03 78
    0x1198801c1910441c5159180310006220b400071499058001c400201031014100040c0c50f80d94100109000654000c00200e4941c0e500c1d610880c03180603120703030204401c404452500700d0801d598000b149031601740c5c425280384400d0f5031001c0b81e11421000b0a80344540320090558000c04a0703800039a00c03420309204000990740c8500030941054070303014542e11500d42c04402460442402c0c01c040c0c10054004414904010171070b00015001305d0f001401d8000c00108004141c12100918641c10141400b10005c40d902d21181d0f600c5401403012101040c100100c9078000d540140301418001000880005c1652082000340e0003070340580d544500b04212040c0c0780c0c408c000c15100c400094001001c00500107000e804070743c00300303d0401c040440d58220110040102003240080306281e01d03100c0271084a00c040d40c0c0e024190200c119031007151a00c1c0f080d07020340100880d80c81c0c140c4032200295241681203e01c80001011003040c0d12442d945440410028800c2c5248440103441c000d80c0c800c0c0c4030802a05403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 27983953 1250 27982703 27982711
    0xf130515070303240e09010e010c0507030e03030702060304031206030b0a0911040605030706180503030304060e1002162904060b010e0f03070b0c160609140613030209060409140c09 79
    0x4038010040c4d03003502001c01900002d03110481429000d6031a41c002c518010046402844041c1d80f0301a0080c1c041b6400502403d0020710a568500300381c41c03904103064a034003c460307000303421010a201003000070380200920304481d01c0940e400078109590341c0343c070001240c09036480c2079015601c01c1058280600c0058a9240c030206032024070503507141802203a500c4809202d84006c100540c0000c06201042d00c941c000103183c0281102d0300c1e400e040c10f10b41c00a000c0340c20040060b10039100142001e801c2c9000703076148010750074405d910340300c0d154071003821140356032100c1d6030104d1491159140096044000c24007407409010b001070129a540005010440f1044100713220f5440d900c2d02c03030940d035000114042034440300500c15444203109403507180303084070103180e160b41c9405c683c80c0442c05607849074801e400c4427070a00b4084804111502440080e01c540104602d00021110050002d030401215298025102070000110720290f80c031494004038000c00b0840d9650490101040c561410300c1d503482e08 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 27985203 1250 27983953 27983981
    0x6051003150506030705040f020d0e0607090e010e06010507030905030607080402090612060c0a14040602010203190501150f12021c060b0307021504030905040f150602030f0f130515070303 82
    0x500c0c14443c0000b5620b031070901c100c901c15a160003007400524a2901a0b40c0540500c00c0144050f070711034040a9264401203603900c0028100810015002030710b820114100c4030810b07000181c60b21804011541503100c1003080c0d0500c400080001411b4808000b268418903541c4e90308005403d1510410a482c038001d4404ca00c02c0e203610301e80b010485004140180c104004040c01c1c0ea442d02204d0081d240366130080c840e1144840040340002d030b01c54064005500c2003c418020806c1c8464801c0b5003412600280582c084450109820034149401668405203170505410140003c2d02c0103000316060764841d400c480d034448071a070380300760004200307000b40b03009040e007140c1040c15884d1551000b965012914682c0a519118001080926000b85002006444d020b081404518203080201000d06540056540968240c0c0400502c851001c02646c00020410701181d14043c042c3d50300382c0e4150010031208a140960320800a0180d03206070503400200035400e201c50301c592541c01c1c0903049802d00c05503100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 27986453 1250 27985203 27985211
    0xe0d031e053c010b0d06321206180f011503060c0908030a030609050603010203040b040b1503060403110c0d08180411040303080103020307090608030a030c02010914070503100e0303071b0605100315 86
    0x1000d40c0c007e0001410b0904400580c04c040522000001c0010242c10340c0c03103069020b11428012030051020443d9205031114080390042d0924a0400d0701302d50040c0440110440b00c484180700041c2079070041c3e11940c0151400700c034929202c5a82c2425035010071040d501096644004101c0b0220501500b68010b0088000710b0031407801c1d450b07402064900400081c9403107030a0000800204031208808e5005e1409005c07103200c0c2c80c183c64054080348001c0c8082c207151050802c0d410340e5240803851601d103503504c11111400c11800d00c0040713130031030400030380c1d00e602a031030710301c3c61f220128400301800007036000b0354951425514500525046c142d07280c106201050034903600748081c11001040340c0d240301d96403500044a40680100300d00411101200502e14103084000c440701020001c0c52a050700c4003102a150010071000c0000211905610482c2c000d4100780001400f041c02140221004502c17107a0103080e1400c15a9841c00f1110102c80304407480300020b0042c0b00b0300c54202d181d11152003150100300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 27987703 1250 27986453 27986489
    0x801050115050901020709050717060f01020d0e0301140907030605010608090c010e04020d150306050901020c060f090316030201060801060909020619030e0d031e053c010b0d06 77
    0x45544407403200c5240c2882000901141540d1080080c1070081c00c11040c1048181456103006009440b0460054604210080420100d01e85040840e00040e4140c008284078203202c50241d40c10129006d005905540e034000b494205004240300e0f0707100e21455006000d00d10305501e0700600711034041e00048100034000c810840503800c0059a0b034101c4c00300f4200409035161150004001c2d21455607000d4001e41044071800c4010581c03900003056038416002401582d4407101d40908030b010703101c00107002c1e80c805070204080100b50b180c1035400028480540c0d00c0c2c001c0e4a0080c0c81003c035040700c2200180e640e8101004011030030702c42e41d00a0070350810140220710454000502600848120300c1c00d00103101c0b1816002806680001c0c0b1000d000c20039944010b201003009070040040d0800b10303018500b031a031a200d2641030380c4900c903c182c240092161030b001da030000040c8030550708071034540d03620400305500b0010b071120290203000b0004021825602d5200248800c1950110b0b0700028101c02c1c202409 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 27988953 1250 27987703 27987719
    0x100906050d06020304050705040606050d0b01052514010c02030c0105010f03080304120201060f060c031b0503030f1b03041110020f07050415031a010e0c0c060c220806060a08010501 79
    0x800c2980010b000350701c030b44603410900d0a02d0500d0780500d501038984000041c0098100028020024640301d04003c8620608015900381c480c0314400070005d003d0500701003000340303110780c002d9000d0b005803401a8217940c09c60302582161510101c940c0942d00109070740360380c0e80c0c090040b54050a003c165040b180c0340f079540c0308210740c0000340005082040c03034001c0e41541c92003540074000900f0b4130000303c0302c810f5550760003038105100300d44280d0020b41034680e101010315503015003011603a44440103601e180d40302480c011850002618401c02d42000e01f64030003502c0d4100000c1c5004900601d401c00996413030104000d40358505220b00801c5d5040400b51000c034071408110181203940c2510049000240071111080d0001d1540009011903051081c1d070362050340480810741a0b82d60251965102d071981e07091452a8041c40300d28400580c401400036040c0d9455030040c00c690030643e450207040180500074000c1c2e0004682203c07074598481c104000c1e20f8034165860381c2c01042c440c002040294144004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 27990203 1250 27988953 27988969
    0xc0509010b18060903010b0d03030501090b010503100b031308070501051e190c0504090f020c010e0304120204090309030506040303050402100e090103020d0f08120603010c0302040e04260f0310090605 87
    0x5214410500884c042a13940c40a400c5125090f03c001e000c094080401c4c0780150081c2002c0c005c2144e16450814150969409842140d00441c20152001041481c01040c002c1d258001050070b10071070034505103800064070100107048042e101b00008907071480c1000750000728401890029852180b0304050103910201d11107807440d41c01d5104804901451180c2040d03602d44600c0d400f04c0402464403c4001143c00198050b02c40e101c0040004c1c03110110644e078050385d034050b601402e070300142c1d250340300e43c018905540400b01051107820405100355990300c40d0303420101c088805401080d165002c0108601d803520300e454412440f410916408a00c0a010420b0140140402405420101c040b80c091041581356400d1490380240d80581d100c0c070a032104d4034800400e9030158002c0d805c3c424030707107043c0e4028020f55080d5003600c480e00c8420b83c0c1d140c480c00c8641215104680034911741c503155410300f0503644006c0c405403000364444d545c2c03030030484046005d55a01d5840251403910b072400034861035448401d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 27991453 1250 27990203 27990247
    0xf04020708270316090e060c0414031c050d0b01050f0d09140a0c060212070b0a051003020301020301150e090f070807031404030c051014190605030a0c0509010b 70
    0xc100c000c150210260007a0560007a0b0343d41441100038001c1103118400c18842a04c00c8007030284012510b0f480200c1d40e84000b40da03440740c0001c1c04d00062080100280c41d9400b184402012240100305104166226124034401040094400140c0d4590b0151502039500b80030420b2800501e004540350701e2151a000d4a0340a4104a480341521801d01040006c000e104020702030a03503008030407a142114010506115020140c014080e142c08443d00c0403082c0d0b034010750002c0103100c01c0e0f51491039560060200070300c1003628050120011015031002d00c091406080420210909004a2040548000009504544200020004c0000104448403c1c81e088a02402c103444a61a00e031025000740c522030200e0a2a42c80802c104400e1651018441c0e045d00e00800669080701c190402140544031062001d003030764140c80700030400e9098100300da42200b080b21000010f4003910790b800241402c90610b400c1c3d13005410240d06005c0d03454440000d81c01040b95412207407034445811044603400c80104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 27992703 1250 27991453 27991477
    0x314070501092c15030712020a03060c050c060106050c0c060903030403060c140c1005070f0207030305160c08030304030e10080c18040504060912020d120507020309030d050403020f04020708 83
    0x94505100b03c1041140303050003041c1401040107880c00e40310603107211080c103003414801d1103241000521450884e44003003515802500d9115001e04540f105009003505036190010400c0400401d601420180606070103402710355102a40c030a000d4102d00d24000004080038031a800c01c0002d072003540c1e0000111001c403507101d0300c0401c8079402c01405441c1810b12080c5112595800242050141d00108a1200010043d1030400250b121480e0072504030030b61032042c2c005640008030a2022a004401500000c215112540445000741d6540d0605500300e43c0321201c20380c00802488105a00b00784c03807404030203055845c050f46021171240185000b001509164400100081480d03400c41d0400c801071902501034011302850904d8030340040240901d003001c0d56503d4000c14000d60300c0b0f2011540c12000e0f11590755080083c2d10500c0805c00804010303028800b035100400000c103944e00c041c44011511801c545070781340c4031403950042c803108400e41c0340d00502c228410491540016404010360301000940 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 27993953 1250 27992703 27992729
    0x2030f18010c051204030b012114030c01020406110c090702100203090c04050f100b030606040e090a06060314070603111909051908010b03010e1509070f0e01031407050109 75
    0xe00180c0c1c0710030400303901078642d00498960740f1440b20702d400100200c1c1e100d480500c005a81c3c941c06440780001d1040890002c170606210a00030070a01500c0c000c10200407001e880c540790003050200e003280c0c00355010710085405020b039070110410900180d003800c43c050b50402c44c61710308800004d45412203000c80745005a130220100780b038210100702c2441e1540014000b0045400c1441018445100c0bc840c81c43c158030000c1004200f010f011816070f030141034003500081c14582445100b04408200401e142d0188c4202e42c01500803802502a45000b18001d410b0341d02c0c280d44440002d41000c0180e00701c2c0301810700b021100002c08448500b00e41c0d0742e0401d43e903180002d01c04400c0c210303003124030744d40030b140e001d44810100c511182c081c0851104403201c5100811070410482d0601d82a1200c44510380c04940240302da09540004621140341d02900e060155401c80e5115008820b8141880c0c001460038110400140b042005c0b086608582010311802400031a1400d00002c014000794001e44040c40c280b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 27995203 1250 27993953 27993997
    0xb03012a02101e050901060501020303060d0f080403061d0102040311010509180a0608010c0e0d020d0c030b0406090605090a0b0408180409060902030c152508030f01030308060102030f 80
    0x109008101101007042403d00801d440c60b114000851002005032a81d54582404a030406134144180c20031208103801030340c02d541d2074404100505a072020182c801070039007580000010048030060010310321036071000a000300c1170b03980300c11071002c0300800008581c030401062010402040100412501c2443d00641d03c1e50018082100480e0000f034240784451610103002c81c00c002c3e50003901c1036682c0c071f9000304500b8404201c11140740e20312080c100d4002020a4032400941015103091006c14000c4240054580d49c0b035441c1000440103d0302901c885581d24004070810155010f0b5035004440307000248110703222912124024100030340020411500044c20344002680c030b151410406030010420805500c40782001e1025101c850310480c803e00948520400ca45017101c0c54803645c1014100f100c0c00c084001e0304c42d15024103181c2a80c80c4014061244100041180700258400e024003041c07400554994076016200003c05400d040c10354102b446190710351041802620141e1090751826800854 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 27996453 1250 27995203 27995207
    0x3040b07020f06030406060825140d0803040602030103031d0303032e0b0301030210030e190203010209100315090b0d030507020406030b07020a0b160c080304020a090f060501030b03012a 81
    0x820721810300e4214101208000906c140c41e8000d5085482c43c07001d0781da4000340300d074800030f43e820401c5242d001c141c00101d0a00914810b13410110180304003038190005800207891380791160f0021074080340c1c820780000c014030400d0752045680d68110782148560007880404000603499010051401502c480ca4916040c400d01d00c402041d403013100b0151800039841d03102d1020404590007400168020310700144d620400609c41e01c10b1910070181034000e07040c021048000603040111501d8140c1c0d15640038800d50203150344080d84059540596100003400c3c481d00c2d0005103044601c0c1d07200e5800c20f8900000b007449034443ca607005640c0ca83c1850120b9407801180b000400500103908081c0040d5001801c020b949500010b0001d00a40140c08506081d034030190f082401006010712800003440366070325400090440005142c004d0300c010008543c803034031144890115500f0320740303220003203849140411075940c240c420f03140c40e544160001d03c0780112001c0a0202404060203540d841040c81c0d1364a5800d41c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 27997703 1250 27996453 27996469
    0xd020304020409021201060503150601091203030f1e0f090c06030207081308030c06010f120609030509100306050a0b03040b040f05030d020f0901080115020607050a0207081501060e06040803040b0702 87
    0x294020841d030784051171103031032a000381040c0c024540248a0003104040c0715000049151088030160341d1300651307504110710b840011080c09000c030f040c940c031140c410039030015500a00e08500240d00450500320f6001e071016066541d1030709107601c0c441ca01443c90b40400ca00780c2c80d0300243c1c0c5c1c50381009a6504050315207a40c961013110000d005c94000b002c8003041c2c241d0080002c000441b503a1044800f166200c45299105140511840071220060800d00001400d0350f005007014a0283c10068200868400410300b003c515520190000c0d03528802407080c0c4ca44448100040d102d011000c500f1480c0954808185140c081c1c8007a03c2c20042088040401c5405c02c200c5003140c1c103944003903484800301501017009400c6030045074042122100046402c281082c50801c00103900d0f40104055100e44d0010f4030300350b110982480841c040d81002280692080062040d1042d00c172030717403201661400000814031418400030318410307003081104001400f000010fa5055400d80070358aa9a00b51a00c0002c0e100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 27998953 1250 27997703 27997721
    0x1302281e030816030905091501140714150109110d0209060f041206060605070f11240c0105011a041e05040e0d11030c03070609140105041b05060406050d0203040204 72
    0x940800101d2081820380d0f0b00c0c05000300b40c840d4541c101c0050f2190f04110211008503940c9111010070464001158400e40440f0100440e00b00364624204450300c401124042210a0300c0c1c0542c40300340d6041800001c07905071b600500c980d500070000142260b02400342c521544240350346203a000f1136000c50680c4c0300000c48081e15180c0e00944c0c0d031aa41d41082e20528050494203403017480c41d00000140700c5010b001216001c95005225140128048e583d040000400c103182e00e4005940d245940b800440c54101e140510065800158030342400c5000b69081d0344050704880381400344102402c001c455260195400e407003900c18050f000d044194402044030b0300581c0419409814021400c450038004103c00032158445c0d0f5485455600100703c00750382c0d1245402c030260643c420000000800c4d029401035000d20b100c7c1c400450f0341c030060404642510803c0d10243c801941c110001c100c4080d11200d007900070401174130254107007850300401034614090b40040440003900000043c045680d00d601c00099 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 28000203 1250 27998953 27998963
    0x607020c01082a19020a060e010c050702040f0626160602070608190c1d01030c14090102010608030c01060e01060807020a06050604020d09080405100302030c090d020310051302281e03 80
    0x130403240100175540c990210054030203d213421a800e41d00801030160343e9031054079448140c503001c08cc1d0b09200007001074680f09184e082d901c6c180411000f0700500201c04102101c501c181ca00d034584d90000c2d04001c10305280104250301c20300204a445c1d00403580004803507040c01c2c40806039680069041e01e403618240481c010070f1a009080b0f081540180354000440c0410108002050403a03006404079850303181800d001c1642d0102100700c244a0200804020206100126009a0f510925440c58000e43c00e9114140d448060600103501141c600078018400792500400c1400d00d6400a91100d180f028090311490f2541c00041c0b003503d40f1340450b00a062040400c10500710f650a00c840207400034040e03680304030495a4801000d51103402541c3c0910700907120185800071442c1042080043c0790422038060103000310b03500d10b07034480c2c0c03050500c0b505046102001c00c1d486481004501420f00f4540c0b0500910185400340b42c203044048241665a824924550000e0498412502d40001c2c3e1002748 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 28001453 1250 28000203 28000237
    0x615010509121c09140102100c0314011403010b06030c160606030503130e0a06050a14010e0603100501080708040f062705030d05010801110f07060f0e0607020c01082a 73
    0x20040c3e86403c1000b5002c1c0c0660340b203108407602c0e880c00080d04c02d4450100c50042c0d0040c000c01040c08080e0788050800310190400041c1d91108c10a915a1400241d00150342c2c05280160300446007401c0c06103004028040301c9561842c030b020f920500083c01990307891030300256655001000c04c002680580095a000412241c0707400007072000d40c00d10381150180510001219000c601044828080d40007610001048025158101603d051a03032642080c03050400c070b0001c45007045616608019405921600c20505856017044005050154041c10030400c0000c031608105c0841c04021941c03c8007544140c2c08682c00c01050808681c85580888801440b2020740c129410094004004c00c4042d00c6500305000682c0d03074119103400c13140d0a03c03140825500820102c204040c28100a2510900c18080021000000c0095070102c070100ca030800d8207030b80710400703201015030100140d4000b035800f403803c8030141c601a040c044c100b91203803030110b80e20380411501c01c8410b201c50069601075003810107505 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 28002703 1250 28001453 28001473
    0x3030503060a0324060f0501050715060509010f090c020604030e0904030c06020a0203070b0c030402031203070302040306020d0f0b0d080d0c02010b091608010f0b04050108090a0b0a0f0608061501050912 88
    0x844138400d40c0112110f09854000d0000d500b0307031030b40b0081085442c140c441c5420300941c0d0300e0342c4210060b0007160318404c030794844000c91180d442c003020f01d002e085941708402e0501d003080c060204407090842c104080d5400a0301300400a81d010f034000c0070200c004d40c0e1041042c0c54910381924500085400146a640041286000365900002410405000700c01c1d407101502c41c160a64024031058402030340642003942d25140d00ca555400850300402585401407502d1390b203890380c101300c0c5c00580d64094159160b9201280f501e0341400303208111002103541e5071864007686d0781d1648a00c182401ca5031030b184c841d550418858004c1d070000c400014050003034910b030b18000d200007401540c4040f4120208082c01c002084135050840c00030140e4101c21960340c54581800010740740302100a228121a1103501d038001c00107481c8620780380c02044d890401041e100c03440300481040d550980c01900e042d0344800300b00f02c14280511240514840c003070a00590351b08480e00442d1a011030541290741c2441000303405 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 28003953 1250 28002703 28002743
    0x9050703081806070515040302070e1303080901020a090501120b0a080703050601081501030204270c050f03010b09130305070503030709050f100807122003010815010803030103030503060a03 83
    0xd18801c1c690141080700810050b04002090242d01c002800940c091b0540c9400a03000540b603e4115000e40101d1751440d58502c0e10010380380741107905290302c491440600f0201900000125080452000250705006a02100400418151150038100840480c08480300c03505581300390501540030704052980fa8407a41c20913030f650b880303100803a4a803088000000c1c4a01e004600c0784030000407070031408400c0c0d203190200401f4002c2c0394084084170005a1414111004000703400c1c05d1680303e1400e00040a1605081000c1102070b08e582a0290b410100584999501c0c5846d2030340c00000d16004104030101030404550034060020000c0c20b07440000288090990400c0000b0110342040300c0005448115906001800700d071040d403a4013051001c00440d0b200d60040703000d00f81808201c4000118842750043c120b030011000514052980b0700080103000001007805016580c81c03034020040d0542d454444121398920051001404124008c804103880d55101d0703c0c4280215004401684181608111 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 28005203 1250 28003953 28003957
    0x180b0a0c021207051e0319060c0206060306010f0b0f0405030a1a0c0906070f02010e0a091a03060c04060f05090d0c0501030506030d020601050105090103090218060316050a05060c010905070308 84
    0x4103900c206078240040c020361400140780c2007600c8026081c40f00c0d6005c1001d81d0400e981410f18415414040c3c0f05040c52606a505008200c4900407900480d0100c039140300a400d065000e0a0240a80c004200610550b0101040340303007281c00b4038074050341d1034040804c2c0c5013140c000c0d41c1120750f02d8064403100006016800c00403101404051103140700503201c1d000c0f400114400c02e640c00e40c03c00c00600045010420014510100354018100f41c840494241c001030b92064039038001590030fa0f621414401c0100150b448501403400a40040c40c003420a007847c110240118800da008220321031108241041c45403080d41c01001d40548544026001da28140007034203100c0c020140020324010018413146000110301811540303a4003d04030030303400d02004440e0f552020368024141601c0e41032001c010b844500304d44010000c0c1002d181183d0500030201400d0080030140240c071a030700001e040c40a42d440402c92011907200312812956104404030301400340100c51005803481c040c0382400001d001d10080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 28006453 1250 28005203 28005227
    0x181207080c070b04210201020c09010306050907080a08090f12030414130902130c050f040b030108010c050703020c060304060908030a06031b06020a02040f09050607020d0306090b010807180b0a 84
    0x5503005140c43c0d00114101d4001da11800390000c40c10313441d0510711410260803603a118010b2056400c40f8034800301188101d00300307910407561aa580c408000001106010070009083c04401401c221041e0382c40e004060302030110b44a02c181c12506016156079a055402211112003000352611940e440045808002c400c02c4440c1c011999191420126400b512410000340d034000c042d90840c9000e44054001040c113444890103001c010080010803000c00006000180b00149900d6965810000340c04d082d61000014103060090500c03031364000a0300804e05040e41c8a05503407558032580c440c04d02a0160440400243c41003230004240800c6141940103c02a24041c3c4078170307c41c004681420b0003c1c4a0940f0031500140c20141c0218018a0543c015440343c1c542610302007054030040d00d8031803d0440648a040269214440011559030140a100018108644200407180440d00040c240a000404030030801c620071076482054003240c0310800103005168280d54480b030300090060712510072a1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 28007703 1250 28006453 28006477
    0xa05010b040605090c0d0c0e03070e0105031005040b040f050a0c060215061504050f0d080a0906081b0f0a23090a0f050a05060703021c030501091503080318120708 71
    0xb440481d40c2c3c02d25000d0a401004c1040119141007a0000c0400003051240012401c000e45692201c00c00da5003005108040c184c0b000e0450348551400742003500d4050111242c0c180607003440100008500070103180c1c0d40c015040100c640c40400c461400e0f40c1000d120001c000d2561046010201d50198000342d041d044982004814441d44c03604010032402c2610886c1000b0050740400c410f01060902040e02000e200300035003c9200c8401035035840486030440d507070301d40020f40001c908201241c0c1c000305103a0080c0625440141c0001d80307041c9050644242c80c0010008a40040c42010072442103650700c101c10318104401010000348495028290f01c0100c0c07030351080304000004035807001c000c3c482a084a10080281c20342e20f10701018041d0366000080244c080d0302489e11a209010307064809901030541550b000150703036040440603404c80f1484021011006990788051000401c810220380d0040030360304240c402c8680801030f5928003848064003580048000c01c0507000c005015000d0080d089902c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 28008953 1250 28007703 28007711
    0x218040b090106110a020303030403030b010210020c070303080c12150411030105030a0f17030907060f0513030303020f0f07060b0102070e0907060503040312051f05010c1109090a050a05010b04 84
    0x100415508426045907000031004010400d8074007520494090605000075100c140e02c441c1c000a00b1a041101e0580110b0b8030742540038655a811702c40c02e2101c40404e001181040020031205542d80790900004007400710210124141d4004102642c1c1040b1912880414615010b448030001807000e804090007982010720b60030154680340282d81c169600500101104020354440d0380700300d90103d400399150b8442c1c0138808140052800290700c246a840b0081542c185040002002070362020325030800c000042c00440030b20f11044454000b160740514015882d040702500e880c000344070706038004180500018035201041195006003072994826020303a0600c0c0d540d812511040001151401c0040e000350405200c41800b800246801900900d002d60403014810302e410100c80c81a1034101c5034422401082407281099840a0080c0c034007883d21384d001c028940d4441720701c010396003401c9115005040000704442001c02c018408a40c22004480d641c0c0c0e1581000c1e4004c100f42e803480c3d030080d410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 28010203 1250 28008953 28008997
    0x705030705010c110402030606090a0824040b070c030201061d040b060a080703061a040c0e190503032505060403110607050708070303051e100905090708030714010204030c0902 77
    0x20750703640340d03401c2c0d0070101d55000d140c26013080100030360000700010780c0002c0610903044181c50b20800340002d05400d1000f070075200c400c07102d00c4030200c0ca039400c0c040e20540e07104c2c03c2000003480741c800c0b95001041410160401d40191806038050a45508072600c0504c02262201c9d1090074516403078003840c010303968440340340c6500003404869221409809410390011200f00005686d542c0015201c0c620b0340252085031403401d0019080c0c50b0010f54100004440440c48102887c3c603400401c014401006003891803481c14022a40328041c403480c07080440070040e041c031409580c1c0840540c0d00790b40042030340d450b0f20705440d015194628203818055103106080000301840d01a408645c0240c2e00440404c2c200069560100c0c09010000c01c0c1500c4885c280381c01072003040005034014000c451400c110044c0b01e080810700b0003110030003003000c84035034403031034082101d008080107c4203c640c0000318050160b1503503445502a204a0380002c001009021000039509015406403010000700d024032450a80 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 28011453 1250 28010203 28010207
    0xc01080907060212030c0705070906050102010f0c0e0f0103091502031e01031a040813080c0111070b04030602130f0b0a0e040b01080c09010201110c0715020d02060415090204020c070503070501 84
    0x71a41c000c0b82c0140e8008154100c0005a50000d5640301c0e0400040c13526000e06583d40070b080c880c075079000d000d103942c0b590401c0c80315603021b000381d4207920385000c03041166480c8000700802905409080c03500034090101c012070305920235004000c0c020340203092401560100200e5200941c005c032905c190502c903031170b050410b1022019240381265004503150400c101c40030610411484c003e041110703544810881c903825100388002e1380300140b4044c0e0180000c6614034001501c0541028840344d02ca4002910500c6070418140c01d44c0e091301d4103c200180c0700d4258032382d81c4c0041c500d9074101c4000800c44100028110b03c20310001c0c00e92001d039130750350380d43d124041c4144030070386408030105800b04100b88009107903241140e0150208000500c00410b00d047d20020b0041d00da07108010740c018035001482c0034402c20074002c0020812030b0261005080c0c031382d030401c4003d440e140040c00c020310402c0d0314081511b003039110340c0109026640041085540703e6415048550382c5c0014460075009008070000080c1541c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 28012703 1250 28011453 28011463
    0xc060809060906070e06040312090603060801020f1903060e0c030103030909020309030d09060f09030507060501080d020a0615170d0201051602030409050402030a061407020f0d09091e0c020c010809 86
    0x14a14801000c41c0d40740c080090313954050105c2c0d0260415801e000000100b148121410000441625030300710007802e02800806465581d00301020707076030040210880041c0c0c40002c030380680b5500c2501100320542148104d0251504d9440116030022800c1400140448440118100c911a454000f9515952061041603010442d0103200d542c00c10704c00d07258501300c2a0485d81c4400e21900002402d00e00d0380e11803c040704c5603401d0503400641e02080c41d10800c809445014050303c803100040c042540341c00c030029501c085550f00240712170f4503042c48406c007004079601d0348058586034100d04c0d6001c8089001d2a66820000d0b400700040d82020301085089001203001044400349501462600382420b42c3c507000351a01800491b0075200d802e000c500414400d1290301981555101d0704488c500303007004000c0c030303004c05d001000c1d440350880c106080d03101703401c80300c60003c50700e11200109400c0c0304941d041e07000400304d205551b900350403c4002842560b001ca0348030200507007600d5419040e04c4004246030b8076 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 28013953 1250 28012703 28012711
    0x20606030a020a0b09030703060510081204080307020d1403030a02030a0c030b060405061c0903030207030210020f03190e0105151002030309070e091606080709050d050c011101180c06080906 83
    0x704100400340441c00d000e41c003e0032244170240c00c0340c1a190780c3e6501d14040750000c681400c00541703108010b21142c0d0091111700b03400809814001e040a041481d4141c0b0381c41401070080c0b242240910ba01c0030003003607091020500b800340c000d03a0b0b12450900048400b0f94421244208402d2504014003001402442544003406010700361500b01401c2006010007503201040c0c00d4440210141c00b415800820301403074011521a03035000d6150703003540c50003a10306000310300e074800c4290060080c0700031104480140c1e5441940c03464846158619400082c0007800010103ca44a500380002c004400c2804100c1048101d815a0103940080101d94126100d01003560000039641144030b003004400d90105400d9004030008043c1d807074100f43c003160302c060201c1c0e581c810000318199000700915650032800c00001000c042d030f0030500c20249130b610a43c48907000f0024074180009101c079005060809d501035842d0303211030442032580e445542409401c3d50410321841e000217003d0300c00500c1c0303110081062800303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 28015203 1250 28013953 28013959
    0x20a08070b0d180f03080601030e0f0309090c0a021903110a0606050f060f030604020901020c06040f03060c0903050c120c0a0806041509120804051002030c0903010c03020406090501030f0e060103030f020606030a02 93
    0x109030103035170341210700403000f0740b40a0415480341040d0006074418480d2101e0741364414011139452010106100804500504603441030a00f0302c182c0c007000da004202c03e6411105c00c1c204850f90327031151a05885105810044404622440190784100202c40c0d01c07800c01e6820841d4040340b544440c0b4108400d602c1046400c0710503160920216846041c90380140800641c1401501c101e10b2400c0c0200d0700a8000e0741c003103104c0f120520020818008203215032103260001e4945084070a0a41c1c441c90b03541c0c0720f00e4506030700481884082140d040e1062001840c0c5100040c440d40d507042e554004140e44050035101503c40b510405003454280c00c0c02e218202405900484100c00700ca1080c5041c0c40c0040002c10a031664041c1e440301d1201d4818510055100d0420130450a444004003000c2c1400c5809244184c0d0925204001c2800010341000c001002c45409180c04112000508114000307019080c07a011814803641d0700101c101034019011a290070416030031a9840d5560208140d41d0348028840650 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 28016453 1250 28015203 28015223
    0x309230102011b120b0411160b060d020a0510030608030a050403060501080a0b01050904080408030d020307200319051e0c060f0c0304030c03020a0f030207060e0102060408090904020a08070b0d18 85
    0x4c6100015000300c8185a001400001c0b50303000c400e015002a48515031880e03c20014500d00000c000c2c08131541a0072500a440540120f48181c0c0440c100c0308180c003c91b80b02c2d500d413540420040b0b11030342105000c1c0c8034800030740707450f29492200903000da00503001c1250001d083c0b80011446d1032002a61100c8190002c04511040e4a8402400300001019005070f50300f00342000042914101007004050b403041080005a40345050b0350300900c0100c40764050310070016480007002035000004203440705490314040d038602c1420212000d0320a803107080c0d07a48142076100111420606070850150500c1e0808005849903560740032166004000d003100c00c140009401e00200780071902c075008080d4024401e0040301d04c00c101a4842d140c500c04003201c1200160702a500a100b8aa400790142114032000e000604207030529540b09170712400742c0860b050041100e200001d040d5503030300302454002c002c3c13141904c0401c0d485000f210b0083d8007a8a45168a0b82040b00810008865110044603583c00c20300c002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 28017703 1250 28016453 28016477
    0xc17010c020c090c0a1101050f061807081906080a0501230c07030c0f0609050706020d030b090402090403020a0804080606011e021504030908100603060f06050307060c0309230102011b 80
    0x190385d41000c840001040031041018508a00034816107015008100f500d40307092400000300000740710300088210b1468036540501000f2600005015003110040c0300c000381e0b0078029601c0728001c0203181d00401441c41000a51002c1c00070644c400080660300a100102c2d00e0561040300a619a003031310001c05011080141c03201083c45841204040e501c1248455541042c2d41ca9903001d4946189058545400c03485080040c04d40410030501d0689260400f0f02500c0034074400940fa1100060003e030094001070005410144284034051000d9030003501580c555850303c00403552101c085408078042409000080c5060000100e4108440e100d607000300b545000d42c100b1400442800360085090003000200031624040074030650080403003074400020701a1940c2407070300580e0000c1f14184e030407070b2524000780a40d1311701007800750540342e0300d0801003503c2c1c9161504840d124019402038551203a410132074485d00403000c0400074600d900f40e00a0200545010111124040c0c4d00030310000b00341c8055400c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 28018953 1250 28017703 28017721
    0x6100303050a090b07030324050d0807020303120709080d0801051302090d06060b090102121612020a020a03031e0201050108100b06070f0b0402150304030c020f0d0c17010c020c09 78
    0x90061240c0c5241441403161344400c908403580080340708402080d2190000200701d0106266141d400401808034403445284c140071982401c06040080e0100e0b01c00503901741591410401c0320002a02204440f071347e03141071040182a54024001c2c0304190245800c04100c00707100780030741410707104020500c010301c0c401d0f020a9402940304860761030b00318450f21071501c0420920702c0741400429481c0065039551064000081c01c04c1403030406100800d030107002c259101c0e17441490b4a540642d10070310b81115260f402170103a00d8001036410007544001045000310405900600055600507030022402402c20548010fa080c0e890901401c1020780c031003c540c0c09410465000302d804910050502880c044a9884101b000d00e0110400d40703c0080780710500c030450030004028240207110010b440d00314101907500802420242902078030070441280105002da03140b503211000c2a5200c001d2100040c0e03100f0202014410031103801d40d5030b518003050800c81900101c3c24410281000f07090f003030a03a82d56204 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 28020203 1250 28018953 28018957
    0x6060105071109160906030e0a0f08041802090a0b0a0f0e0111070b03090c06040e010e040c1d0106081503061b0f03090705040c09060f030b0303130909060b030610030305 74
    0x2070350540502c4000407410b40341c18900d0390050349900007181e0000990f660240000c1401d0b80401c0c00c02d803070b1420030310001001240084141e82d0001410400c1d50450500220b64012500201c411100d919100034941005038020b1040c1c4000fa609405101c3d50381d0303000c04c0d044c02510840c101240810344007201c0c4c80c3c46242143c13800001414801042017100c001d4510b06046a0044071680400206000e4506e900704400c881048040742c00919042c100894482514410b1040c03007141c41c0002c0100c0c0802c404245100050a18009001c102140f009401c00d2450000e110b00030103d2030b000b000c59200c0e54000300d034949611024000300301c951211810350607080740c0c00007510030540c03050054501000c070480007580102c803810010304085081c00c0c00c1000301c0301d080c01d151042c041e844504200054100300d42c2c84010070300e070600182424501e4042815071194401062500c1c1c03002c1004030b40c9000c164842c0c851107004000c02c00c6144001d8080c1965140700392030380810800d0710a41080040d1142d00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 28021453 1250 28020203 28020217
    0x218010b0328090f020306010f03020a06030b060f07030203030f01090608030f03090a020301020c0619050412050a020c03160905010803030c040e09160e0702060a060f1503020906030a050405070b0702010206060105 93
    0x62040d00000b07400044401c03181400422a49502d00001e030500750f00c1c6c100000d90240c02c261311803180c058074503070014002c809603200745410f140e01c88512426954500055824114070f8000c0b0a42d5103042c0e240094907a40201e800380c281c603a10000200c0c1400380d511810301a80c07510b000031850910b02c40002c06060300000c00780006d87c851104d0680050700c0a0020b8540440008020606410304181e19041000e1000c20401c0d00c6150ad4200000306034150680b2a101c0b4a43c00c0040c1d882e015003c0480c1008444c12100e0f4040c843d00c0ba40c3c80f444015070130320300d04035400035400b080f8036600d4000c900e450348015514640c038008107100c00d11100e00012a003a400410307942c2101c0f510350301402510000417a0368031007044103031f104c1c00700b0043d55014414a0345c042c0d2100300422441b42400c0c402e400c2603446010f00c0301140601640e401006000ba4122109080018419600c0346043e0302c0d40c1019000480301161341c5c4c0900c1000090142c55013041c0c41720198141c0140900f42e450000454040c1c02c044 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 28022703 1250 28021453 28021501
    0xc0201150f0603020d0b130e0708010902010215091c11010b030f030403020f0105120403030518030304051507020f010510080c0307030c06050715020c100501060f050301030f030509030610030218010b03 88
    0x520b02c0e0035540d0307d645000b41042c802c1d00001c0340310701104003124280101d0794000225030f4144141100180c0e0b0104d0b8501c400544094142d0442e02c072098203a18002852500d004080d20048128404540002802405800900090200103014024561110310645400485500c140401c0c401450540700101440704180b40c102d080c444281820341da910402d480a401080d5a0001c0c480480710350300006401011040045182d410580d403456620081c2c081c20f04102c0c04040c0125076003034400c0c401d0f507000507100e000130700860504100642d419603103803244000324400d13002c01400505010983c0c0c0c085a4008031902a071030b14044042e96280d0000c40107c2d412001c484070a0750300000b070b201130207214144c0e030300810080030520007003c1104c0c0c0682002041c80201d145030700340d06520104072415039602c08920030200c9040c1ca810f81e4980110b10f01303a6410301032141000103094590b854113045a0086407070108000c007000c44105904800e00a14000020800002d00d141c81c0c50b03100d040140c5404 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 28023953 1250 28022703 28022711
    0x1011090a0e0a0e0a2103020c0606090705090307030308090c010f0f030203040302010207020402070b0613060503100e030d0501080a0302060a0b010c02120a0203060a1401090203011d07030e030406030c0201150f0603020d 95
    0x4044054200001302d18111003424901080324205940d0702080c0412210301c0c101146420020003015030740f41c40c001d1959101c1d111020010f1551481541501c0c01e40c00701a088442482e1640b5000c3c0000302d04071002451031007842000c1c0155885000d442f008000e0507118815000e44c2e00700214040d62008100740c0941d07400b04070600042e141c610090091030b0052a01d84883e04011003040ba0080050058280a60428800b8440d5a601181c851560f4082e01c000140292420078510304500840500c00d203407a26000000030005404150008070320b20a0742030703482959a045058040780c40c000742c4070b0700169000e0040001410300c0302e4410900800e03041100c1c1c29045540c0041c4c681001141c807000360a8a5480c0c400190403500070050160a0480f404d60456051041c01c16402001241507001c620f2117501050340a4004c2e4089145480218140c030307503076078031000050701910b80b03c00160700562800a52401d085155803010301030704d00e804814004185090800c5020b074100600007103020740c3d1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 28025203 1250 28023953 28023971
    0x2010f09030507030c051f0203030a0b0a05060a0e0118030b01050f031f0209190510080417070305070b010e060102060a150b040906090606020a030e13090203030a021011090a0e0a 78
    0x400c0044000e502c629140c00c05e080c03c0109114004c0c08400081d00c0c0c165403480c4d06600d4503004400c0c3c0e64460b0040700c1c00180d6804075000501c51003210380c45950804000128411802d070701c0005200c41035001c1e00d500000680300101e1107446040c03440003604080130310005100500d081021201c207000000c4c1110465214030040c503d80311001180003007100c0c1d000500c1a482c6c00c00741f1043c0c0b2020010082c42241c189050086104038024108201c10085054001000c000003000109031589100703c3c0287c17070307001c41d24000e42203030301000e01684c50744001c5000003612581007580c0d42c030486042e0302a200f1a00d808601078044c15040752212134114920b034000c500308a40c0000b4200a00b000780010800703c0c5454214006c803156900102e0441d00451441e5001c0780e000410400920002e41d4000344044086440000a01c1064802541404000f400c0100340342d0001e45203200030703140082045012162403500440344645210030750051120141049076a13501403000fa44040c4244001c1800b400d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 28026453 1250 28025203 28025213
    0xc090402070f0605071e03060806190e0f1005010504020a1d031c09051302090105070305090109050405010303030515060901020a020409020d0506010b0a030e0d0c020907030b04020c010e011404030c02010f0903 91
    0x4210741d4200041c51b101c840d41780c442030b084c5a840415982d41401c01c050303401e0500701c58880300b0090050002200c01e002404400440d0703800881d4044144040c1d44416040c1e840103607c441241600078030741e0741004000701e818a068802c07252541c506031180140c1e680c0074041c51000c84102003c20340d240c0a06065680d64800e010003481070429580e03101c103050740c1000c080004100d41312800c1d044191050001400c0f40e60480c0440b030607282c26080c81900c90311008012a0100c6040c0c00443c2c201d03007441d00000805801da00040d0048600c0800360401c503072254148502802600d01003401640544c0f0024050300340f9902c00b00c185070020740144c00040c696100e161526800b80c0c441b41d10035200207403042e101603043c454a010300c4411406002c09100d2410018040d4041d070a010b449440c4d02004920402d00a6200c0381903044003078010b40d1507050380b400c441c0c020034806009004550030514840d084107050f00500344a2985a2030300c1b40c1c000c08a030011150782c01180c0500d018030840d1075003c00412 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 28027703 1250 28026453 28026461
    0x100e0106260709030209190f060501021507080712020f0c0d09080c01050702012f0c040e030405060706020c03071407061403040c0608070309021201050105090601080c090402070f06 79
    0x4051901d84a240c1c0c104500304850301c0400803851012440000d05008003240c0c004407540850790121040e8005458101800403880d040e86000c0b41035a1520109580840711038005004070342098080d03840707010005180000260003216040c1c0002c10b01ca00140c1c6c958042c44810558142d288030040c10003810400900440c0e05c40081403145600074000040b003154441221009420204003078011709541c08006852800b07002030080c184450781103000c00c0c2904485081407464821501c141001881814150301c0d400c030340034002c0c055070030200c0c8213003202d1000048408882c4040e0a05142451319116000290040300d80041c07540020020f401c0400c10b4143c007045010213017800f51030541e01d484809006280018030200c0688024810040440c49255810040715002e041540407035841c140103c0c0149513001c0000c3d400482c1c0e45240000e6501540319506a4401b96050143c5443c0c480055840c0501150083c04e80c010812030b0a281d41016006411264403d020319a034515682d580c00301a6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 28028953 1250 28027703 28027709
    0x80304180605030304080c101b030801030b150102061816060302090405150102100c03110a0302120f0405030708070606030611030a06060e130905030d05010b0a08150105030609100e01 80
    0x1030004100001011032981c4038003001010704400440c5024a0308031120388644006101900c120104c0e86141d0b5458050381045080c1c1440000b4020300c903c0529010b0030f0390f1020700054920300394110001d042c902d080380415104c640c05800a11507540c1e031800a408100d1081150885402a000820321070304807034060001a0240e034601503200c1259405100c11a031004180b208909403040003504141d801044410750030042460101e501c55982d24140c010303018001c20440485400544030b14055815409002c0c24020300d4116031050f00c03220800c000041d400d581c09403480d0000c110720000200904028504113114070300101f030050356501d50004503076448001c0741924400100b0011090b0281c03041401811150600c000f920405001040340e50304144110482d25540b41505070600101f0801d40300d24103224142800b0035a101ea03d60380c1a500007100040124805401203410301201604c00d440030b48069540a066640b10000c12150800140208100c114642800700314488c110703807000d010b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 28030203 1250 28028953 28028969
    0x1020d020a020304032f130e0d0f020105090105010608070809070b033103050d09020103090b07030603050f1920040e0601061d0a030303090201110a0b010317180415080304 75
    0x700c41c40c2d8102450388118007002c11030300c0c45010460349800400154103006d034a0701554502c1211036400205d0009186000858000e07114020000b03201c950300183c18880095a0344c028401034949c10002401e0702c800303019100114807610005070103544a6181258088040012504001c0e9142a05d085a1b030007030310300b000310180101c41101c0c0da80c00c3d500c666110a1104c50030100410b07241e01c00074020702925040300c810603111103180080d03a110790032800406400205032900c80c02c1c15140540100220310040703c96000d0401d25000c400801303d00c0007000b56201c4d4401000030b200340c0e02d0320103c0101005c81c810f810004050002c2544462140000407640c48004140329410300e50040c0550401650135402c12548480c40c1382c50391980841401100d900d4200450441510b1006948403521162020b00b07601c10a00003405112007609640e04030f1303001c1c28040c2c08040c1119101592481102030703440b0b0034102007898903140d0401e94040480707120250002842c40d5202c4602c117003594000d80c80185 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 28031453 1250 28030203 28030207
    0x80703120c0206070f0503060a180603060501090207021804030c0209180607020703061b05220e0408030103060513081909050301020f040e1303080c070809060406030903020f030c07140301020d020a0203 88
    0xd050713001440841c003410316081c01ba09510b003d9001a492010f1406205440400480d07141c0b200c100b80d13001240a50b80c0003000b4440741d80c69541c0710000350003084042e0f10881c0c50010a03050802102c0d0064021505903440c450001c2d002c0d0240154842c01510300300c40d011804405002d605030038070030540160440c1e8054100c007031841c1401030660f19514a8100c9400841c148582d20365002800ca07108130950b026041c100d01c41005024203039410310b03802164010301e07050800c001c11100c8001141a244100000c00141d10343c59030760101c1c01c0c8a140d0050451030b00700080300c4c0e10101d07405000003240851400480d0207440b00c0100c2c7c01c0e6040340805500106021a040c400c91002d003c0080d072100c0d0100e1100d02c0c801017a1001809144003074941c003179941000480c01c0501c2a003508540d09010090409550399a8490000f002800d00500030340050160709110b4840400120485c2c0ca05950760004200302c5040050310014407080c038503004d90641d400c02c5841301c1042980040c4c500b5682a0b00555 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 28032703 1250 28031453 28031461
    0x203130506060316030320010c0210050a0c0e19080d0201020a1e050f16060c050405010f030b0f0f180a090b01060201060305100b1923040203010b07080703120c0206 72
    0x40e1500707101505051107600b2505100403a040480c030180103d940600d0200171500005000c0180b89a40d171000e40484e500384030003c10b41390780001e4081042c96601b0020800c9684003607051003102c40512074503000070b07803c91250100c0d01c0e2210b00f44155810600031200010341ea403840d103240280202000300540d401003542520740b40c201c020200c290007500c1501802980b0700a0042040c8603100900030500c0010404a00ba0b42d030722085000742c1d0b40c0c4404200304421030100042d00540052041c580040d62244805069910a00514201010142114912460020400c000211040641600302015100e641c40c00107010040790301441d00d42c480082c00c60f1143c01d03da000d044c4160801d2040d0380c1490002c0000480000d80815081c05044000503480300c1d200001d9241d400e410800100407044540120711422542814000684032217106840c810a00301400203901003480f5078122031100784425004030b40d02800904080f0b00c640742c1a984110b20f001d41204a600206541d00141e115000b00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 28033953 1250 28032703 28032713
    0x601090e010e010908090120060403030203010f0503030c12030601030b090109020a030605031609051005100e011b020121060b0a0503010302031603050a1211032206050403030903080c0c04020313 85
    0x85180081d90b000207020421240e2200200c0744102120241040065035640221003019021609483d1400003510003904042c10014040d400a001c3c01ea6012036001000501d031800004a0b1402c0840e103002e031507581d6081100e58902d400082540e0b0505844056411084e90b4143c0403c1c040d04594800580320216120001c049031040e030001c500a500084800030142e805562a80880d8500f480100b22556000110300d00030500e6400590829441000040b0003a001a1400041d070b03800c0c0da030411401031070b01460701c102e1000721010b0f0200f4214006051a1483c2a02144604ca8000c201003249942c9014200d081e44c410498000080e0002c401802141740a100c401e1307403030000300303004145d00d0305680799107849a1480070010228080300701e483d94024001c00349610304e101a03d0035641c440b0b010302500d981d80d00340c0340d07410403240d9032400c030100e800e602410030751b800d4941503940c00c10300a09598a040d0305a104240b0303003906114080c1103000e695507a0000b54400c040c4601d40c00344006007440c1c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 28035203 1250 28033953 28033961
    0x30509010f09141c08010311010e04050702060f0c040501050a1821110108010b0301140409020604080109020102150103030807050304080702090103030e0906030a080f130806010f03020901060207080705040e010e0601090e01 97
    0x281340e071620180340a410308280e0103600541542e4001041d07010100b002401a60118000b9012a0b08070f8180800c00180c65004940d082c842d43c16241412240e6a6051403444288141d0088038003003001880030200780f520952203d62610b0050076a050030030b0301c032800e9854082c0050b90312181c02103c114040c0422101c000c02484140e0207013013680c1e195041c034050f845240014041c855a03800c4040c04400c0640c1e50381c010f0180d160f0050011076a881d16403110f42d018142d502d105a0141c0300b6504000d500c014954140743c100ea415a03100384103034491074000c560380d5101400942d81c0250501a284c0545d0300c0b80c032901c2c004c41c8680c1760b40c07071441001070500a2544000701818402c0c0c0012021001242e108400c4506404802c10481d03500d81020040340801a2950021a00c40c440e9a0021680100f03200958069900071034540c10660780e9403100300d0341c0d44200c0c01032081e140c11040c030070041130034160004d5448807a81000410784010402030540b8141c0240c3c0903c048588a07034070030f4004002845 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 28036453 1250 28035203 28035223
    0xa0e0108190201020a060e011808040503070506090a0303030506060f0406020601060305130510150801050406020d15140f04020403060f1506030b010806120a050a06021903060302090403030509010f0914 88
    0x1c00e503a42818940010352112070301c3d00043c21560701d600322072028a03029400401a0340160403485007070203141c10b00960721342150050034000e01c98000c0110b010700d000030544a424100400c035464060450b0b0b0120007a0502500080e002a4203120525441010b80301800c003800181d401061158500f5000030706440f000341039100d43c1840c200c40c5a021400218504c1d60314801c035000800e0221101700c1514103040540d100d0101c0e940381c0000d00c0304100b00d41d0014020754400c444c06200490340108550000a00391141d00708007454100c10f0103890a00011414500c207000b040107003000d0383e0751140000c1c1d80c0d54915640e05c2c10340c0d80c0410030380607446501101c090411481d0400020744903000180c20300c42e014040c02c5c070549015030500f9041e030007000541d510560101c15210102c1c0c051401c01d029402100c1d65078030403031400720644030842c428411101200d4000f803110038152aa0f440980041c500900f041005548400c0320f40303520110781c001c440e191840b8040040070000d00500b590f0818185035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 28037703 1250 28036453 28036483
    0x512040b07090501110d0f020c061303050c060418050702010f0207030201050915091f0608030a02030a0305011401080c0306030a050f071a1e0f16030305010e06010c05030f07030e0a0e0108 82
    0x300d41c3c6000e8000085190b031b51012030822040184525005a14201c1c2201e2160780c0301400140d4800102c0c06050030001f264804d40844800d985900100b101601960241030106c07650100740e940e0003802074200940003006030000040031000022080140d074130682c030940140c1c0d103520a00241c464100702503e900c00c00c10600c0d8080d03040040034503855420825625038000320100e80b40c0400303030340c0e41c1c0300030000c169010880e541d411f0881c4010391039402048524011a00d45000000e100400052083c0309920595881c919513843d440d03007001c56000602030301e42511450b03144a00144082000040c2d00003d00c005108803031a0641000c840321070484080c9105d1014801c24102e010080300b00080c03040f002d0410341d20f0b803026500201c8103005403820031980030061045081032540692085058540301e9440707034030301d60320000190381c07882031188028559070040240449007044000901500e03442490503840404c0702000081c1e4a20043d04204c0301501441d0041111040401024844101d50 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 28038953 1250 28037703 28037717
    0x1104090201020304120302031309061a0c0a06020304080715020408100911270a0507030b0105130b030a02040e0a0b03250506130e04030f030e070b03060f010512040b07090501 76
    0x540c0000e45038080c500c10100707058a0100c02d001014024801d80d85c28042d0304e440d024219660340310110180c21288900e2a500110041d1075072880300075002c032080c0010b00401005c1c1c0f110281e0383c1400130b600080040c0c4846000b40f00c1a070004181c1441c2081001e2210700c003603100c03400e06c1c8800b800c100342c100640d204c0c1441c02944c40c0010301c007100841c0840c6400c44200c4450b1101c980049200c2d65072990f5400401881020010000e90541c400c6010744110750b0208800c2805000640310b911802c81518480445500c0400080d041103000b940d00a4107040090308255560303100402c9400162140342d038090301d41040721040d0a042105101c42041c031995002880786030048807440714500c0c020b031800303400d00141c0f00c83c010034451071503401895840c021000310702d81420010001d00103a45102d0003e0b042106074043c0080002c0e10400303541c4a002c280e8a546c856900b0810764110002126050042c113114076011000e851100038071031400f419060010b0320b0400c00003000426030750407030b40c180028 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 28040203 1250 28038953 28038971
    0x3030b0402090a260a050706080c030108060a0504110a03080304110a06081f1a03060103050906100603091e0c14030316020402070c0e07050a030f0603050c011202070804030c031104 79
    0x3400e2100e012566601403c040040e03003031a03952490544d5a82d0f40c4c21500c50742c02c4000c20007070700141d00300480d000d65940015940b1003403411440c500c000e220f030514541c0300c2c202060f03811200e58040c580040c82001c24881c42c4910701e02048552506500a940c1800044200018440021600609400100c0780c1d40c501509100004c0d21000001e012881d020019214a0548001000d00c0304007500300f41d1090f1110f208415100103195204a8070540004d051402203034a203480021a24000c425522502c01d0032424800708400400307403070300240c50490a80e1103c218030b250710b510030242c442c06141480310705820960300702514006050120302a510400142c0b907030f41c124400f00fa072120360448025030740e5101424691031b40a22a0000c50010150b04148810560084018500070810303403000d104490313180c000300c0c045a18921001e41107402889510078030303610075812003409400e01e900050a00d001e41d10b90115540041e0130454200f1040101482840010840d00300100c0e011607050040c226 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 28041453 1250 28040203 28040209
    0x2003040e07050a03060801140a15030314090102100608030712050c100905010209040c050306030f07050f010818070f14030d0c0b06120a0b060f0303030c0a140903160303030b040209 79
    0x2100030200c01c100070001c40c4140c0d841e4403d41080006000c0f0800134455612020711004d0403030030945000001d0380c40c01801103915409008a4070840b42c241e22114181c09610034031300c51607404001c0060441c080d00f0141c10b90401c003441200c0152000d807005580311101440c00b010021500f8a003581841010b004004480c040020280e2104100007000324030101c5519085001e8001c80200d00d60141c2070401180d541c0703620401551040c0c60440495460800e0440d0480d200c00303e500809400548420816103d940a406400e07081701c0042809103080100c0d414040c20540c0710381001040c0310b40c08008021200c03c5e01c641d00905102100a001811010040034040700c45031074004140050100c00585a0340d070f16041003020311403510548042041a05d0401c04606c01110031a2150700a6503402c110b81c240007003a00c3c804c05540f000030386401000034083c1c07841c20210a041e02c0d0740030200500c070025107043c48040c0308070540060300321050b070945c580070f010f07100380414403405140705001300b500d213903 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 28042703 1250 28041453 28041479
    0x1b08030705090409080a0807080a0606081605190e0307150806120705040204090203180c060a051303020616060c020309060904020310090504230a032a050d200304 71
    0x242440c00c00503582c912440209024000d001c41c043c002110110b14003207100c2e007016a0034440c03002542d820b00150f0b20903c80b00b040794a280580c00000d001007002642c64554200b4806000d20030b420b0180c2401f2400f08e082941301c05402400000400351000b12100e4203080201002600c1015480310a41055400051411034002d040034410310083c8040580f481d0140a0749001c1c141c042c03c107666075511804032402940c0f064550050314040c0c40e54034002d400c00402c60b107100c040020308451402e907110000310380d9600403024511a0344400c00d00000160f0f03a81005080e5212090340c181c2a4600a0401d0740442d811035081c001590810040d811056031400c0c00c80d115058100c50041c1c0303a803a1542041c42010300d0760881c041241c41c02080c807040c00300c02e040340302290800e080c43c0d41009801c0200300d030700ca000c0c006004011a00305480e1039482552004942190821303402d0f010500035481c0c50301d80c5482541c0380c0200c003150350025440915001c03203012104841c803c2005501c0c2a00c0d08181c00e08903 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 28043953 1250 28042703 28042711
    0x160602060703091709011403010b040513060501210f05040b07030b1e04020a120f090b0a0603020a0504020313050a080a0e0303070b0106200a0303051501080402030c011d0d050606011b0803 82
    0x5440002201366151f0b00070300b00c1d10b404901c0d040490341c880d80c4640881007190702030b0040c248514070781d080810300c42e4950b00414040d164107948001074134030480704805440c0024000780450381c1e101c500e04400b4010901c10f003441140611041d28090510309409021504849446406100101c0f680038401d9004540b0605511041d140141d603a01a84001c543c0301601c001091030311400d044484081d4001354010400c000d000b600c40c2410f6482e0f02042030b0854100d440020b41000b6a0001000b803460142d011315481420300c03100300e041250303598500303080240c03080302103d0405011400c9802158860011078040801750b00841c0f03880d2054580d2609803074140701360030820070914020355442c2a82e0711300b401802c4c0c4840450b40c080403146800340181c8412200300d0078042c9041304c0405950b2184841501030341d000340103410308160160044840c0392414200c4041911485c200c511241c07525540c1d50185801000500014180040010000040540303c4542c110080b01d0340004204030304112500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 28045203 1250 28043953 28043993
    0x6031501080703090605180114070e060f09041e110403051c030905030a0825050a0e060f0c10060801090507060f020c090c0903070b130b03061216060206070309 70
    0x3030755440b100c0c1140540102140100080d0500e418030446449268600300d041c05001c0c024000c0d5000e04081290005007160700c90005000060f2090f00c3e810088003c2c407007040d0508000d80b41c08210000301e010f4428a80d4a00890109444c0000c1c20708882d01c00c0e11310344003500b0240d41c542851510b4907551902c1103041c200c1d224045448008009000354030200031194801c081d680c440701c062034042d090030011210500259800c1000c2c0001c1c0c0c500d41c600700da5824541c1c61f070a003480c0b04500d04807807013030202510603080141000544a03c192000261040c0a43c180081200f007640d50005010703514154814079281e810049200c0019102080643c2034030424070700038240071000743d4224500a9002089900800414180041010100020941c11400358200c0b907405944a540700e6161290003c2410f40d0b100603a4144001b1030603800450f040b103001050781441d0041c3c0f803180341c01e18400b018221041101c0007004c00280d9018482e03164007040d1070904021100c40d40e12060000540e10741707a090 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 28046453 1250 28045203 28045217
    0x10b03060c0a0302030a0204031a090706180e09100204090204080c030601060905060c030d0c0e041a090a0b0103200c162312010606180e010b160c09090302030d060506031501 76
    0x1408a6261f050f0340003160807032400a408070041090002850341a00d802040303004800001c618240541c915000150132038500382001c0f0b04d801d00d009076810026290012500680e03c3c4a0f894544e203001a0001d03102c03041d00180d0f180c1c60150814500034148800501a8000100402c00c40360804403042c08c80d241501ca80c4c0d50742040403206030843c4540b400000019140c00815864107070300c10072415200500f03803401c0011510443c0b80380307515403550100c140c0c00034a01001445107242c3e0380118684a1041c1800b1507105082c03081011107205404d072940c00b00c080464104111070080240c4800402c0c00025500024149820041c00d02d01c80400700c0300200a001c00b4000348c2c0c42e00c9442d00e1460130050000c0200a84541004044100540c00442000050140828200600144281240c00c24061240f4100010b86801c40803582140d003074500810000000402490600504100034881d41c0956a6000210b66000444055030003460294130b0074801c00c840680380305114078400c0d00902304a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 28047703 1250 28046453 28046461
    0x1202010203120a050f0702010203040b04030f030b03060a05040309060906090603020310230109060e0a090504020105070203030403060c031b0c0308040c1806030b0606031e0403180608040203010b03060c0a030203 92
    0x41e1541c03041c4084101c0c0c020088080010280c280d9000c18015801d11080c40c2d89a15030460403805c0c1d01050318060550845000868002805410400d40300c00c5d02d0304010401043c0c07031000a080840896810350060b442d03a04010400d540685204080e040504001031114217010004110000301d025660a056001001c0f850b0102c008000cbc00081c070020800c0c00d003660003080c5243c0b89806001003240460640c05002c22018090800741d400700b40d0190055000d01c3c90203000c08040c081c06041a0706000041200c940985c400740001d10165000b418003040e10020b494004084032801800c0c000100c12010030340074034a502c807007502e01d1180c142c5002c541079102c50401c51340c00d5805a02166104950b180715a84c54426908004101e90264100341e819079031b51002e011b6188800c6a03014050b0800c46c50b00c1c19542807400c0c003650400d0182c5000d03c54003806501d120208240d075080b4002140c003950803c0214902401040440082038028108500f0314001001c1e413030042c0c0308603505040c0c001c4006 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 28048953 1250 28047703 28047707
    0x30b0f070e040603030201021308010c21060504050708041101090e0c0306030709020408100b060403020a050d080d1811012c01030207050a060203040b0a05090c060c03090301050103110a080f0304120201 88
    0x865003030300001c02c03c01c0320030b54914002c1d0003544194180c4404e030141490001d0805010302c902d241e00400c5807229841e0208100d14034004181c0c50b03013544805542c8004c041503544882c4603291060405031240e44082c10305040c48049152380d041c890741000300300c10061140c1e0485130301054019100c41e441c00d40b42d848583c002410507031706410901c89148080740000300c001c07001900c1d203070a45868108001ca031000304180400c510480c00003940120f4812010000d50400c0140002180d0007441440d090100901c1408156000241c0c0b003105142c26000c12014000414020445000c0c00d00b00811054075184040c04132903074001c0b80205010b09850058000d034000e404446d04203500030306445000b0200d1a282d0020340041e00c00380c40811841d8002681c080b010300c1018020b200c0e94000303140d1200204100a9186d00c4490060001d001c03c4c010182c043d01c0c24010035010314403540c01c02c0c0300c1006050900100d1021988030407140d0340f1801c8040701c0f103c00401185c00382c5204c1c141440c1c43c0702e424001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 28050203 1250 28048953 28048967
    0x609030f0f03070e130501210203030702060f040e0108060106030e010c09140105040f23030f07030b070903050604030e100e0a03080a0207030b090102030105041112060f0a0807030813050307030b0f07 87
    0x1683d4200c10f0401d01c5e113450031160390289069800301c8110b20405003182001c141a0080b80600070340643c03040200350058505040641210341c00c00d07060b44d203410303150070190f000700000303901140b90760380100c005028aa4042c040c81214000c2c19000300040700e0403000041000d0060f204254182001c4c0e90341d88080d9200790122000f415035504420181030b030358028115498800c2010703006080111031040054680800c190100d40c8015004100280c02d42c0c8803810000c0c0701070521303006d1050704800040020402d0002c0c501c02c5019465043e000c03007008040c0b04900320481ca1050400c440244030161b03903a43c0c5a0401e065942000c12551540e480e4081a4070f080d00d5900054010141c0d1403c110030440150015811303a40151410f02951040404032034160007a1110800b1040c403179030001e0f8060500d512a42030780d86000304441403240e030b185c08650a154094000b95076078040010f500400001924a2400600382900100113071803171900c4004041e000a80001710807034501002c5804603210f004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 28051453 1250 28050203 28050227
    0x20603060906280311150f09030a0c0801090204060b030610080a0f1415030307150906060e15120c0315040501090c1202090a0606050d0e0a0f080301080609030f0f0307 73
    0x1c0d400082c40d120f804124802180c0310407222280300204130010b074204001d0303018081114207180c5080c09950002d41c0b280c0e0b080300381090342600c5094182e402042d001d01c828401800d042000080340e5506006000a40786580c00c501c08841041007445178581b07a00080c044441c010303103011101501c0c0c90b041600500300782019580600c2c103140309a40030481d281c4a05010315070103146010015550707001d0540b41c2c02030410140c010b0800322040e01501086400240700c1610074800001c941c1d0f240d94103154071200540311741c8403082d03052200039124140460031010380c01422005001d442d82510002c0d0340c84060280d1013000c3c21001020030204002504070900031580844031552454840f00348039403000340e0304401e0384600d12000c041100c424071480b421050366100d90f00e1500c0d000c06907410f0805000701e400f203905581b14071244100807a040301103001089104e030780b00c256a941740261aa2400c000940b84021030f800400020018542c50070407903204072096118280c49965212094071020f40d204 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 28052703 1250 28051453 28051489
    0x1050703210e070611030403120e030d0e04060504020702061615090312112706040314032113030e060909130c1703040e09012a030c0507020603060906 66
    0x5454401400080d4204500300720b008411215096502d1204890034580c1c85040e480d660410442030001c0381c3c0003c1d81c100a54068203000c402106a01c0110749004580000c9400240600302464030750315143c0202c2c00100b408032800d600381103c9400150040c4140704540f00300030b50800c4108100008816008640f011b0204100602c24060401070318207110401e516002078581081128060541402d840000c0d640201d007684054134902c0c400345040458a405074000c50601001002a0365052102c00d01030b90303100a9900c40c060300d06408035207203040f001c4c0c00740300081c0010032605101c0511420f0130903405261a070381c4604032030045540792040390010380c2c1018001080041d9a01120721f0402c1e454428001c070081a9505c22040700720740740d000c0701012650810403080008045581c201908541c8603c00006c440c810301e00aa4400a10b1202049c00300c1e60514480001c503800d80701d41e00e8031044900b400340c940f180942c001403142c88010007a600c10307d030403008034095803110724a80807040300c8a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 28053953 1250 28052703 28052747
    0x50603010516051b0a021306080d21110d060603091101170c0f040306020d151a0702041d061303230405040903120213140604050108130f020a150f090501020c01050703 73
    0x1059800007030142030054076111f201d452b40694485100e00800708070444000c00c2003c840b29007004c5038018000c0d8141e031b007041c01818054040480755501c2628001c1c40c050310000b55002d20780c90050721021070840064103004d1034000c50b141c101e54a0032004e5101300400383e45681d4420302180002240100d80000c3c010302d2011460510b580f00d036910031142c1d034400048035440c981d46c4014041138982030b18910003803d502070018500609241d0000c050f4480d12110091a6000c150034151500400f01c5084002c1c0d00c000a8132000c0c182c10085401c24000540d04582404001680d0050684078038811580920340d513111760300034548114185400d14101d02c0c030555444556903021481010340d4040c680000924402c000d0b41450280d00301e508594042e15030304100d42c0c0f00510a407115240c00000c4d1281c1c404203491030010b9440182500c09800303000311110b150b044a41000388050a0880c0c03034030034007240700000c1c0401e0382c000078140c07003d2100340b030003642d900680c0c40c003203272013107512024106c81441c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 28055203 1250 28053953 28053979
    0xd080c010f1d0a021f050d0207050304030b0a02030907180e100c020106050f0a170312011d060405040f0204150b030108030c0c030d0801180207120201050603010516051b0a02 76
    0x41c82d0482c00d200301a00c0441049181034a84003915021260002544600064544c40c030301402c80d030568400b0401c1d42407480c20003004403c02c201303a0f485201e0031100d035000041e00380300700801903240a030000007000c400c508602e03040c103040d0343e9100940185da0300b070222410301070b61108840e04000314501003441036070f600c502080c1d03501d00030303000313400241c401355007081008186801c01403a142c0c40003400621590700e951030640c01c8003108a01c2c4035002130502081020600b11403141041500030258400b003513081c0350005112100400016203a684100d060400340400714003010701240c10541c044500141510080a0540f16003010f80d004203000b45010000045416010018040c0c5030034410a0701d20040700c0c0010541c030360b80f40291200106d1b00c10001408503401d980e0243c01075080c0303400018a000e1651b180e880860004080d12130043c1e4480d801c01800741828014903400450815020320781c04e44010000d4290302503100e1146800c01c0700f141850349040c00f080300028841e005000c20640443c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 28056453 1250 28055203 28055231
    0x705100b010801080f061503120406120f0216170c010c09090c020706050412030507020d0807060b01020d0f0309060b0909150f01051c0507030b090d1b030504050d080c01 74
    0x1409180d25400708141c5400001c03120707404280140b050300c0b803502800459881e070201d6440d030050080e48641620481c0c005803454540c0130001d02c090080703500e42035603c00036000e0b44000d940703284000d005c0703481c0140400445400c0100262820907409104080d0713a580481c0000301a0155400004103982030103110039440e60051b28050580740c42c40824040b810030880166510b800c5442007000054042100708800030760044090a61882803400c945032503201d40000c0d039644002803003500e012000280c2c0c0820050a2300c02d280a51000f070003d46013030706140901500d0b80d007081c2050b009158861150b81e00300b01c0d241d4008104000c000f01203a1260074110046650f546144440e0000c14081c940412a5909000300c241d0403540300070300d00180381e01d41c05912481001c00c0807049a251003503410210015114504441c46803040c20014550010750441c028100d0b030603030740380d40310b01c0f01d050120f1000f0036440004c6a00750703001507540c2da84d511044c3c9031440c802d01c00c90013610742552a048841044103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 28057559 1106 28056453 28056461
    0xb07030c1a09010b09010e0105010c0c03120e130501031707062a090f051809121315020c010c171c0203060907090305070b030c070510 59
    0x3a82036524561101464040841860294010010212800d10400109042c200c3c1c1614242d45072050740c25403504103000b81030401c9540481c0750107001c120b829500080d42d1010110703951128008005010701402900f0f40e20805180c111000000d042d402080d050f640c20581107042071010640100550344100703811100c29440b01019080f8071a00700340442601281280c0030070710f00000da0000d001c101260000d045a04807002d003440301d03440d10f83c411542400380101007806a210148510310307051005030001110080001d1408038038580b00c00f250103c40000d515128010741444040e81c40d0b0102c030040d02c0c005406180418003181440740d14484038543e0000300c42c5080c90400071303988040d0755487c000080e15000000d21a050400da01c2840e44090a8034001120a0844e80d66545660f218801c81f41550008070104241425140c00c803821554054125041c800c03c2c1d5002d9400342c = true := by decide +kernel

theorem cover : BRFrame.Cov 27877703 28057559 := by
  have h0 := BRFrame.cov_init 27877703
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27877703 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 27877703 ≤ n) (h2 : n < 28057559) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
