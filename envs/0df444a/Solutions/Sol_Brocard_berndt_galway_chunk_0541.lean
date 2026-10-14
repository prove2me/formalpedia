-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0541
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:20:42.467378+00:00
-- url     : https://prove2.me/submissions/8b9866df-94d3-4fdc-931c-d3bdf7040108

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 97122302 ≤ n < 97302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 97123552 1250 97122302 97122323
    0x30307031d0a15020a050903070b09011107060c020d06110307090f0518220210080109050a09080313170417100c02030a05090604090e03071506050d061512 68
    0x70380e046200d04580d402509202d802181514000c94804600d00001c02d039010300043e5035041d001c0041e141c5100e240446901405410000240d412152018206181007a2101401c452030404a00d8581c0d02c075003d04d0021411052800c405424002c1a02106030302c203090000e2501e0084d980308040d40c201300c5111000410042091011031010000a001001c00ba5400c14040e034050107101d412201c010005400d103500c1442c0000201d09280481c454550040d00540007009040c40090103403900b40101020300381007802040030b41015102d230200c01c6820084260440d01d500f40404104440102c0075078081e14611208042c2020300e50040c001000501d2240c9a20040d21503114289001081441c0d1142d1800301410800d68000c01102c0e0f8401891910701d95941460000828070301442d04107202c1d040c6014005500c0f140008014640d45014826400525811040c0501501d4a601071540c01c03140c2400380e500003a26035040f02c402c010300d48619502c025203c2801400743c410001c829544103858 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 97124802 1250 97123552 97123571
    0xe01120203010f06060e0126010308030403030e0606060d02030604060b040803040515090306041e150203092e11071b0608100305060105060a02010917040503010c050909040f050f03030703 82
    0x248510880200f152100384601c510340000035000b081c184c2c03006414000c00c16620380c0010002c9040025010b102c010038151941c403800c0615880d08101c0b0210003107850240d800024600001c4c03450321945000300480c0c80c1445000701d1002a41000e4211500141c075880c0100302c5044d840c0150001c3c051080045407102e20700710030080b43c0c0308400640514014200308038043c1e0f44020882d80d621a4000003100e800146a862600400c0d1303074100080c000c1c5596050264014045070010341c007030102081250100380350070028850016030310158800503181d2211404d107100083e0003003288000003a481504081060700c402c02d81d03407000400c0b900e407104c0039181801801c1d0881541c5401c0100140301b03046031410b5030f035442c0d6662018007406100b07039030200b040d15009100750048500c155002c504031808000948051409400c5802824420b5003061040018030384a24155007040c0d100030f011050a4840b42c4621038070064803102500d0b00e019085290714420700c03c100a43c041c00096800040700c070070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 97126052 1250 97124802 97124809
    0x30a030b010512060904150c03020307081e040b070c17040e13050307030c080702030d0804021309110f04020405100206010509100321030b04090311010c03020319150e011202 76
    0x1103403060905108052020210360714021148071303444032081c1c81002e05a161403c1c0300314000b2034591658212030808144c9101306600d41c020314007841c5503440b003090710b031203c4100f010315900f11a00c00880601ca5070004010400119441e03800c480c0b5414100d11844107505c50984090b010480140b2803440003c04004401c48111209e601c0404c055000d0030306811541d5079501d0784150b05000e1704100d5a188100c09003c1c1000440b078480d5401001c942401c444400702030984c100c2154203900c94043c0c5101c07140400400d02980036425801041c1e5000c1008076010440c05403400c550143e0055428840402c10323032100d030140041c00707503190001c104941c502020081e011701c0050440c0b00040ca441404c00c001040040110800c440c07401040c8244521314104800404080e00c2c0142d1203801d10034501c0134990848644001c03000258000d01490105080541c16440191040030380d480c2c0c0108441c00d017007403940c40300e08802c0480104501e500c4da40c81700e203115010203070000c1c000c111003c01c01004618 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 97127302 1250 97126052 97126061
    0xc0c0b070c1e06020a080901030b130c02070602010b030c041505031e16060e09280c03110403120c03030e01050c090f03010605090105060c0a0213050906010608040c050103022505030a03 81
    0x445410100c0302c49070038800002e44869485200070003e5002080c44500e682c0030313030410040c0d0100a80310741a11702c85101c081c0c000e04541515400035008040021801c0361045c01801c10a92024005141d500402002c0c0b00c02400070301e00031140c0700240d07000411ba640c0e0900100c490510b642ca4150921140306400c2ca04003809054440d0704480413050801520350800944003545408584e000600da580d5083c1005180d14040c0c000d08217400740d051004028150f6000e0040d546250fa4200584c9206403414003903480b5278000034040340b42182d142140c00e4400ca24440c03029110349070110750301c20740114507820b480c02a00c076400307038000101d00ca030114142100500e04110045000340030007460075000c01e44203a01070180d1030254a00040860012030108610035010741d02401880d00a44440100310003071000780c0e0700121902401c000011210f10401c0001c2c000c0d40c00c0030707030303c0c1c0514501001076000354004580d50100e040003400c2810f120148005000400d4020b40103140d0310588890010101c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 97128552 1250 97127302 97127339
    0x120a020607020303090a060b120d02030307030b0103060b16050a08120403081632071a010b0315040207030903060e1c030c020c0d050106080a0c030203010c0801150c0c0b070c 76
    0x643c01030003004030f20701000851144003600070b80b0015042c92a800400c0c41d1914021401178640710380c130040c84c9050350000045101c0d90b01940c0402c40e011103600110b083c3c81041c401c1000c5400c0522401d1141184c14085c1041903104404071012001103641c3e0004a40041031080d8030036912000300028103401004042c1c0c421001840d941404601c08006030404c48422541015100c41d41c0652a00d006d45001d0030203010006401543c5900c05894071803e1544c150032034140c00131500c0b00010f841c400301c04c162030140c05d00c100010308090703948041c0002504000e4040d4104180d1020020100f50342d8442c015280300c00c41c2c003603c1c996900e80c08020b4050005040f02003050f1512007000c0c1007a60102c0c7d003c2c0c00384011a000103004000f8100785001d007545030801c04490080040c10b204001c11b110100b4200c80c400c1c2c4c02030110b0385903a0030664084200340300306c10034810b5280c00d00c8030052282c050001d03021710803261801110344a040c00f4082c0d070000d2004a4800241c0e400030721640d1080e0000c01001c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 97129802 1250 97128552 97128557
    0x2161e06050309060714040f0906140402070804030807060f061203020d2303130606083703110a0501061205011404020303191407060f0c14090f040e120a020607 70
    0x114145000f0303071a80c4400082100041000034030789040003181c6d01c42204c004201160002041640740d1102000800b07442c81845102c00b010700e0011554103003802aa805180c10218850900749943c0700c1c1049907000d208222903075a070303d00c05c4a412000d1440341e50007420f02034045092401d05454007915002c103d80c2803000b4041180728451056145c0c2c1000114030809110003900e130f0721284482c500b4080c1c0e01d072000302141d081100106e160307007001038002084181d410348480000b40400803822075424881c80450302c80c180c0364202d000301e8003c80305c03001c600d01d942e4100d9a1510440d01d900f800c40c0d000c1c0d00306494032864540c500040c400240074000d40c02c0c500703170b60b45840c904066000941d20711840c1e1215441c0c1a0101440d0882402840b103102c60341c98110046548450500c0c0800061040f81000c404241c641780210b000c0c00e104000141c1d0315080007218500c0d1140c0c8404108001181c2410b4503441a280c951400d0614014010324901405a148607034481d180c010b0003a052036002401c8404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 97131052 1250 97129802 97129807
    0x180c08010c111c03090b0108011e02130b090105090a0306050106120b06120606070c0b090a060203090a05130b0415150f02100b040b100c0605090d090509060102161e0605 74
    0x1030b000003048483c1e403030140600410403840d0010341980900780a86000c0c000e0002c2900001d0541e8041d0004480e4480307260318900848848190a0100e0088842d010110302c0c44110500030030000c5002442e91a80504006041ca188600080d40040c07540d04202c0d00240c40c2c800401040f5004910b421340c40b01c20100174003108083c031011072000c0c0030741c0300780b141610b0b24800410200c0e1908011103102c16008045c01c206140c80b000c03820180d80c8101501401040040d200082d000d1012080e103084020040c00180841c1c5850200219580803400d01c244403540d8150080f1140d840e0301c00d2072070419000045000403441c0c0f81c0480040c00b001d800340c0041c808000101e10f12070303601061803044c01c5405800011130b18010f0000c04d004002c0d90400c1a04092005240302e0b00356040750000c4030300d5100754000d100903650b01907010384400c0341506020120385003000511052603c060040d0340640180304940d43e407a610b88510340c0651095000e03840d0240c181283c84045085611090041c10144c20503e1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 97132302 1250 97131052 97131077
    0xc030c0e0303090904110310090519030c170f0c16080705090a0f090c1e060e240906030118050604020703080109090302070302030f010f0506090105061b01180c08010c 73
    0x30340b24807460b01030f00d10501c1204001020458640340e803d40802c00503045545000906d03007400020041840c00b50303003e11a0302c0e4807561100d0902c41e4103245a03072680d07501c08641b5140d510905004640c03003544031800301c1403200382c403502c54500242820164080c004e111086209004140d0b01a0b60341084100790480364080c04551120940701d5001185a0400070341000404680300041c41b08030b2004210300b80b815000114542d8003900c100c8044c0012000106069507142c0644003181841d20098000060203c0b650b0704a283c0303a15000c0600098030000d00d003283c50400548250b200360020580300c8803280610300d260825114441e4008026202140350050130b880103041c0500c14801c001a0326201c42d20117041510900000300103560190445240c40d201d942c800d070203080c031000000c80180c030304400101d071850071040650494202810b01443c00b814125510240310306520b0344907181d0b4a0f50403000c0314145400010144c28019a4030f0b0011030700340420b2500350740551a48404001310f001c0e008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 97133552 1250 97132302 97132309
    0x61b021b06071a0703090c0b090f0a06020c041a0d3804020f03010207060f050114011407031b08030412080a050717070309020402030f040506060603040b07030504080702060d0c030c0e 80
    0x401e91001c80420f0f85965641c250110094004150020284036090300c0010b40c03194031002510103607108a0700000c4c0e2170740c02000d115412045201d1500140c1c003200800b00d10342490362000d500368040180000c500005980800d4824001e1103044401c013401420a0040003020115207070034642004100e000c007060035140100700320010748003911604c008a00005c0f01d5400754111000941d0100e02400903a48250030407000f400248141103032289400d00f074100540c400c1102c07034120740110340c04600b01841e41c1c03801c54040024003443c1c6422000f4000d070303001140007032000d03510662082c0b40f5080d00300e0131003800030000c8034044c01f070400907420f003070910082d66000142c00302203004900400d061070351400e50450180c807001402075049880002407040021075034071000d106a00170400ca4907940c80310028054544400c40303000d001c0c11071607004600594442d8005c030760054051481541480110340025245500c070047e49688640e68450b0300301c6480d0580240c0c0d03502d03a0a400d115251480b1035020 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 97134802 1250 97133552 97133573
    0x60c0d0c09120210031d0604030e0301110f0d09150b0a09050c1c020f2107050a0801090e0c060307031d0c180910020a0203181903030309061b021b0607 66
    0x30b10131050044140d018511030707807241c2c4116800f981702440b00c1c0740300e4060a445000030768050300020f0100441400700e00381400b4883d81d4001d61200149817403071040d04160780b5040921000501074030341c50840080784a070300b00e46030110490603001692191810070041442402d501420b8210b007804108010403404809032100009101504800e2640310340c0c2e04c000a203d0301d4100f02e414000403030080400c8120a1003c01342d4900d4183c030621903103aa04d0181e429024000400f000a070700b0f94014045084035030419001c00f500c5004a030584046800000d801d81c20031039011002955030803000883c43da400d40c07154240c00081d000341801d003260001054401071043d54003404d030800d12010604001c0100700b000f00d00362513100115112a505900203469600c0f000190707020079044070000b0b00c01c2c5440c041514600b5029982980494a140d4064018104d841800d54000c0c2d6241000710651408101a41d00101142c2c06080454a500f51445111900c82c0000e80202ca06000540014055020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 97136052 1250 97134802 97134839
    0x709090609061d071e02030901090e0f010302060d0e120c060a090209150a080303070503070f1107060809030706051810050f061504080307110901051915050408060c0d0c09 75
    0x200c9500d9544100342654510703617011054084070350460000c800310b0341c044090310841800340e80c1d03410708580e00d03801d02000e038a003036401710400d48128004000500d0060000c00440442800103d03855140c003e000c1c1c14004202007030f804135000002e001105010900c043d80c2d021083d11010404080150042160302c5401040b60700c80300349080c2455603680d60114084c0040240d442120f0b42d80c5041100104590001d0b40c01b40c3c0031880c0210a101c10f64003440b0000307402ca400038002d04a01389010403c851554001e050520756000800281010500c6406800c1c031440c0c54807061a0088050308825207030010041b0341401d02d41c035000511480c1d4580082090b004030049903007501c480402d6010707140718415903000592038440010910f0401040d130300e017034811240803546800755a80c0c5506110b070540784003051903445042074400f1301c0003800d003854031104466140b0302141442d8440c04024030380617040e5070380c004c40c4c07001003000d04444105005035101c518891038000b80d41440c080c22603240350000e40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 97137302 1250 97136052 97136099
    0xc05090f06040f021605011508060f040f080d09060902030613173403080f070804032102070812130804090e030f0a0c050c01090807171203070909060906 67
    0x2c800300709040484d01070710304d20241104003040030092841c1040c028420f5000003100d8014205000032140c10102d280c80c481c0c0f03c0f01c030a02e242d640d26555101c4124401078012a0003480a21003940070400034811100054030a550008000040f401014507012000344196070506a140c42c0340000395822411000c19100c0c0b84813180c88055140840b0248081c510094071600c015441070a1031990558440c40c07114001c2d02c560589854032a030b08807030150b003160100702140312100031070002403140d486035140c0b084510440e134044500c1c601e400203903803103041e095514100210740508048007003030400c0d4021540c070043d85489090740d914050355000d14030030004070710307071311090705580950078011200c4082c1002c00c01c81e0740d8040180d015201880803402036072684030b0021010519401040e6003000e40d10502c0007000094500600040e1515442907200307414000c4c903100000380f41d2040041c41c02002e0517150a0781c0c00381040c10400407201146d0200d081142800c808004418041c00050030210019 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 97138552 1250 97137302 97137311
    0x9090618020d0905250801050705090910150203040e0a050103120c050102070206070f0308060415140f031b09070216030f0305120705030a0b01110d050a11010e010204030c05090f0604 80
    0x4002d42c034014550050054500d00520070507040713017078400c1100d00000c0c0c1c03420107000406464145031403c82d502140c7c070101081c02042407180a02e030000c1d40700e60101d00c3c4e111701d03d10b054071106580c02000b040202d000c0581c3c408a024081d110305444002c0d031000030b0705801c000700c0d03145880d0715269200f00c81d40c20042c410300c00401818040203404803260980c000d00717010b954148924014000700170114040d00000c051501052580c030f403501410800c40a400d10301e050302ca046c1082e420060324110880b03680082245580e04143d20b0602411080c400c0728000981c620050005210301c1d00402003800003190007500b600711922a104500b0390550350032240440c4004041c0c60305071050f100341c5000c1210040503104101ca150741c0300000f18030420345070f6800e1102e081d4400c0152041c3e1582001c201543d0041c010060a10344034034007401c0968280c1ca4a8030310282000381c2d150841d079004000c0051a500000d083c810700c09480340c120020309095546515516102810514452001d820f980c0301d103444 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 97139802 1250 97138552 97138567
    0x10b1507031103040303051e03040b18010204050405040b06030106120305070308070c1e05120403051b06090904030206010f0b070b1314070b1b0708100b0402041d070909061802 77
    0x24010250710014068120f964070381e05c900b00500346402c1351004824445d201103942c06441c1d040d82c162400389074040c9191986445603644000c80466030480341c04c4566080c080011143e50f10301406014501814a00c1100e041c140d052500b5500f41e504035071054030030401ca46c400a980300c0c0440d41180c0c1c141c604000d46840b0103008844805440700080c0400d0701e004e2901d50006a41d00b40c00c2d151178412401c844052050000a610305e00980c0b1016100d42c04c801c000c40400440c0d5034250045070001041e49240028850006888503c00d8800381c00581c081d90050100c010351000b440058000c6607400c0e4100140350b55000401c2c07000401506a440c103400104041020540c0d40c211040ca080d019038800c80d48808107914189c20182504080064044010040c40310104020041e036549401034089140400c0740c1002038003505105603013040e420000001d210121010440b507540d5030302e00001260074103050081204159400c824010f82c9004000c020800316140c02d8080300302d6060b8050784560b41e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 97141052 1250 97139802 97139807
    0x30103170a0216091410060903080f0f120406180807030309030207090f0f1b09051c0203070b090f010206070917070b0a0216090b0108060418210908010b150703 70
    0x200004001e440b043e03105000c0b82c0454181c00c00c00320030f0425400341c0c80603501d1000c9490f0f204002c1c8903c0c8081481001d084c400704d0307800300080241c402016400c1c0d282000c041c1c440541c561080042060500c1d8100034081048800c0c0240552840a0080002c100c1c8150325990a10311409900809042d55070381102e082600a11045004118000301001880c3c0e00f004843d000d081110200c003242c0746003c0940001510b401040980d1640603503e003000c4509090500080b06000c1e01c0043c00c0707026211082005940c20071107100036001c007071040b80d00c0302c40220612020741442c400141c15504100304100c0300a0740400b0460484840001400444a25010084c240032080d0898860401d0016400e48495000103007103001c50007074203044174582e07134600446e0201d031006940580043d10b0f90010070002d20b85500a40154010501c0911000c09140c1d141103002c00c5c00311107015443e400703126200c0d0894106d000200100001030092020880d01c000103541741c103040c00315042018000c18100141807 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 97142302 1250 97141052 97141063
    0x118020705011805070f060c080a0e150409090606120510050c0708070605040c0b0f0a030507033201081203010905070512070e03060a0c0203070201030b03160909021203030103170a02 80
    0x3041e5544100f03241d0700b81c1403030380d11074406005070005600070940000e6054499051030260b01d4100041c1030905840030702c21038a0140740d2510355400f413000c0201c40303c0c41e24a54010402000c81a500098440c128078056054900c2503001d5000c070b103060340c41c0401003080858110081d680b54100091150340b0840c0d01042d501890801401840000c6681801c01c11294880c0e801540680300011507143e8600407141d440c8648090a100c022090205501060003504501e41000b646d003804910400008002192005510200b003040029014803481c03846280c1d96060140c00d44102030b003900040305030302c01542e20061142600b0035aa41d000182414442c00030b488071214032420076181c5080c02c00004045922601c00076109018100110b403018215100e4000c11aa50fa0003542c2400e00d250015401824070f405482d40500962001510420b038034514040584201c0f9000528180380c1d0050054903041001a43e07055803041006201280c20304280e040000c00c9884a569608454030040f400c02 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 97143552 1250 97142302 97142321
    0xf030609021204110f010507060b030c040f0f11090a0302010509061e0307020d020109030e190b0a200303010303090e04060608060c03150d0209010501050a05090904111008011802070501 81
    0x4070710105540d14003008031980766004500a070f046003009460b40c02003190100c21401c0c9140071030b008110990009506421198245c40300405850107030b60584046004c3d01c20003c0607000c170b543e43d030610500c1d200c03851056941c503042800c00c8508081d03038800850280340c0b8070b0002905100340450007001e1990303080c08541c0b0780040c0003000d0061a0460f203088041d80c01c180d401030090f02803001c1d0f11060a01c140305d2607041d1070701a503404e444401d0400902054912280500240001136078022811011040c01031a018101c5c1d42c038000180003c0070102035840303807600c4000f007d8004100400100c0d0348900c5440980d120f5034020b0f0190344503071500000804043e4001c1c02e80d80101001c2242900201003c1c5214403407503481e02400380c084e0001c2001040407001c1c0251300200c0400107011a51150020301751601d00e03030424900ccc2a01d44c42c0040d20ba070074100ca00312143c80d0010404031860030021000703070044129081400361541840315002140c0c000e4850003c805034081030f250103000c025000248403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 97144802 1250 97143552 97143569
    0x4170709020a09030b0708130605040201020c030a121412010b09061306030204090b03060f070305070903050a0f0303140108060408131d0f061806060c071d1909050d0f0306 75
    0x2c41a01100c0580030b12014070013682c41e0311403a00084c200c10b029621140c441c550544009800302215030710503000b0103028200703904500c01d004038048c2d141c17010007051040600442c80c0348183e00e0380844c02031001e41c030300c80e003240c0c074440502070150905004a407071419a40d4900300303a502c941c5202c012070028003408001131911143c0040005820b509503000b84140d845441e0180041100c5a050503604d103410356985001705000000180d125100394400c5400c14020716005070343c142c1ea03844203071601c404113070140c490f44c540d0050442056058883d489420140c0701805078158500040c0644958000b403000d4823134180003c001484c11031000c01000a44107110540912214080342d004c1021401c865078401005c0b030501041a5207402e0388030400000d1500200d8000360344070404d0224503040710700b911a503807007041001f03d6868090f41d0182e03503450101407801035510f4034003000500c00468140c01640d4034a004156004078002050303401c2440400c0c2400051802c003114114000e14481c1e011070388 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 97146052 1250 97144802 97144807
    0x12050c061b0106090b010509040f02090303070503091309020907050f1b0f0106091b0c02120d08090d0c080a030e1c030605010207050625080c0a031707080403050417070902 75
    0x80010780800640d000a20304001c10440c0d4603001e204049841040895001c51000d0107241214503064025075041030014401504000d4180701081c916040308008554070f800204640506043c6400695642507030b201c1e090090003195004103c0c081c1f4003070102010024001645070030541c0307181c106c80381d0002c1035042102c0029808542c64880344d20721218200765080907000900e02c66140100d9207034241400320308410f250859030644902c0030108040740c101020b4840d40340180340502c0404500c1d81c00f0f465002c4145801d06005080000b001c0305030040c0401001204045940801607a18100d80390400041c20a000010949445074440d451001180340303c800100c0075a040d0400c01c100c070020b80846801d26119810040c1d140074100303040325403400c015000030482904110642c4403c1c0100d50291802d500d07007150505203160114107801150b0a080904450480c42d83c009a00c140c140ca02882076050a54000f030017885107101d614104400c49918a5000300c0c01d014a90041c03203800011513 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 97147302 1250 97146052 97146067
    0x5092d040303061403070803040510090f03050c0a080f120f09030703240516050a0c17090907260702010b0d0501050f06060708071e1e0c08030702030712050c06 70
    0x2c000e000e80e4041c2c00305814401140001c2414006100001d56014201550a160502c001d0010fa000e0141120040090340c11001a806c1d220211080186001d1000f50000740b40382e801344801a02e19074811201e580c03100d5010803100070007140c0c048040011100c00c1e07650714204a06c195180c05070101066041c02011070000401012140d00081c07c254205581d0580c1d05480c003c0c400c485085450300b03020130036101100b440d1032140005000e502c44038100b00890095a40791032641c0c05000006074400302001418000518014207442e50181032840c0141c3d0205090f070400060120240b01088100840804500028001c1d0811043d98401421076005480b0500304540a0700c41135851122034084038002c50350a0070320302c017201c0516401901c594a4a610784e551408140480c0c20134200c030000c0703c0d1040d030003d610982c14600001002101c0c6802e494582408281240b45510505a80d40708000c01030040c0c8001c11004111005d410100c0400c0481d03041003810204c01c540c1c5607610500c0001c0c0d00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 97148552 1250 97147302 97147307
    0x31908151201050702010e03090108060603040204021201060801141c030c020f04020c06151c0308073e0726030c0a0302060a060503070f031b09150501031505092d0403 73
    0x45101300d1040d070003031005c1c110100c070642d02c0344201e0b008540062140b000050541c2451030007035030007034405040145807040c03010010f22020420b80200000031621801044889031b003070440001000c0c103d03000000000082e0518402e1844100d0041c240300c9082505415076031005c0c9070480d07035600644155aa140604c942c80c0d200c00e4210784410521401c95840c0001d42090382c10718441a8400c044011f0264443d00c0a4075400b900030150402c004071214000318540b1000280e6841c0b5581003181001416074030081c519a5030b03130111111469122400c20081076204192440b00c8213140380c80b414150500d210319030306500c07400302407405c140310782c0259600301a40011100d1054405541c2002400d03290410143c5074200b07481180741c000d80c3e04600340049000c4050010307041c81c01640c074051807aa990382c0310702a02c0f41840d10140c010f0042600f080a560540035401d2407044003181452628205800160400c5d0084d0542000c200c245107581031004004140300c548080100744e01c5c1e0a8600382c03600 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 97149802 1250 97148552 97148561
    0x30f0703060f060e01050d0c051804020103050a0b030606040f0b03010515180f04080d090b01060503070e01050705151902030910270b06010216180e031908151201 71
    0x22182a031404001c1d101a8440f4801d001c00d4440b103500d840302691800b020840110417282d010380d0303980700900d00040c00c1e941e42d1070341c090b02583e0381007207815a1405000141c00c4490040140e8810740c10940c07071612995011071581c0e489a4100c2e0b0010b0041800c4102000501e6031410701c0d81c15610741001e216210070311100d41e9503101411151180002035100641c0c000a10a446164851a045010034000b07568100035040100c2c2c02000012411219240c0c902103800aa02040c00b00324008103110b00300d903000d040c114050600382002894011245d41c2d541c1e8071a4041901c00658460300042046108001d44000d4110f191120964490400f11583c1e81c40b01640004a6482440c00c00607001d0100000c602c881c4180900c07214664840030760310340c40002e00c802019141140695401c00055104111205014110b440a440300e401044400c8008480107107132070101503801070100348403100040b040c2e450b8882240c60032040701d032181d0066001e038580781207006a0042c9540c0e031107210325005500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 97151052 1250 97149802 97149809
    0x1603052d04090c021212041502120601020712080d0c020111030a022203031b11040905010b03070605040b03070f090f0803030907091109010507050c091e01080303070905040c0e030f07 80
    0x202008407003d002c0050366160300e00815840e45160502039400301c2e40d00c10703800b168040c0c0904010ba0807400c811541800303d030f00240b00007004d06080c1091201e1543c0c100071241c044c20301c900120310b42c40c0994450f00540d00480b00d008130350a841d607091520343d43c803e400c1810303c100e107840d915440c1e0610700c0120b0040e40000b01078103000f40710300d00c801c01e60745064404041240c0d014bc41b094440703102481000850400d03004180d4900c2201c20011141d503c442c400c881d181c034001c030000103131011070408141c1844416031150080080a00051000c400c4210889802c1480d81c14903882070b80c0702c07907019541c00350594030650070302041c11070010b066200032005503c103005007030603a06255240c50800d0100e8400783c00300d5589580a00c0110b9071540108024001280508125640340307a23141c001035405078048502e00b040c43e2104484100d00c0705904101405400180060b40c15440c1883c0000d04900b2280301c0c407403146458401c1d12124a01902c5007100014020f4260703561840199025503a40c4410711 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 97152302 1250 97151052 97151069
    0x190606110d0305070807120b090a0e0120031303020a080f0d05060901180b060409060b04080601060804031718060106051305040b090c0a120606020105060112021603052d04 75
    0x507090107540707120b0310405219085589490b00345854219048511103e0713200070440d4186e0701d0900300c0096483c1441d45202d0000d40402142c90513502051a007910030817010b00c02149265401b000b29042980182d03a03020003103500c24a40c8401301e09049140444040011304950300c0020a180b0283c4140010401d0400508051081d612403a05000e1580300c2407007600b00009401c4c80b410702882c0641c204006826004000b41d080907160403c2c14125549540a41120342e40064200b14041092100500612550801d54071910b8961405041c190208403d502c9180304000000c4140e03044140300d481c81c0c0c984204446180d80c5400d000380c50360340410101c001e0281004030028072882d00c5d0080b840250005480a01940c94181c0000c186420100c034443c14402c0382011201008454030820005000c82c3c0c1c004a02424200009041c0b240f004056000d0180104144800c200400d0101c0380c4075540340c48c4c540ea403071048203110082a0703030004090940b02c0c9410900d030b07596194640075005841494 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 97153552 1250 97152302 97152313
    0xc0e0411010e01020c0a03060c0504051302070302010c02070612020f070813140a0602030f0c07170303061c020d1101021f06080606030105010602060a0f0603080307170105240319060611 81
    0x2d0010b998030329170300041d543e20105007102400000c1007500440340610b010308210b41415101c000042e008902d00300304911081d80400c100040c9582409540b2075207403940043d140701c17400d200300109500080341180031402c0d000500c2c080c0180000c0e04070382c0b40075004040742d520380b04c040d41c4403150a9154407640201d00d00e034070300700b2a080c5403c12408045603010b4008502c0c05104c07125012031900075080c980d0701801803002c0003072407042d07100d00c0301c000c0f00241000c1c0d0340d13a00e0b21004010159040b4012400c1c26816000c418005031203049001c0c0d25590850f1100c1d07c09600440100d2901300c5180c08441040c0304040d12510308100f6401000568010074143c518642d59072050501300d8800340304000c0140d200c3c1d0089071034082d03150f2042c92084140350021440503200c0e2a442000e45c010761350600010f8448602081d221030b117008050140004450341098240d601008903a1980c0d80385010013002800800300d002909140d00d882c0e80c0c1d6842e110700380041c0b95240405803640d0450304044035035010381c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 97154802 1250 97153552 97153577
    0x30901060e220c03020d05100c0c020f012118020306060402090a03170f0f09030d020a0507061206030c060207030221071203020102121501030609090b010302010c0c0e041101 76
    0x801c80306031188030088004000c1203215400140700c0c6506030741c01d40c0c031401003540200140e02c50a0942c1d149034041c4000340104403031003581c0c1045880c0b014813002002003841600ac01a030390690f03202c50380102403034040d5403418003004101c5800100e001080401e86004041e400e1150402c024001807030003201600c102ea65240c050205a11442e07920341ea00900c509024000100d0307001814510030594400745042a10210008059034440d81840e0204040400c02280d0741ca0100010303004413a1910151070004100e80e541551000c05000700420f2001413802542041c84550008004540000d42e0020701542e41d900a07403508402e000a038001d5024403860041102685403050003503010400410140b1320b0695249441c00f4650000c80440d5001c01400d0300d202540520365000d08000340e81c4a825440320703000541114001e41c810b80040d410320807204041507501240038112074080c01c007040c040c0c080b440c0002c0030300305075002603d5240d10034040c0001d03c03040030898060880e0a0300c9006d0303011074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 97156052 1250 97154802 97154819
    0x10c110d03030b0a050609090a020307120903051b0f07030816020613090b09041e03050c060403180906060207140307080d09051c1e020f0d031206150507110118060503090106 76
    0x7d02c02100e9044000040807034160380c0c00b42c0c01103074040e1040c0380c02c8413002c002518401c15101e080400f50001070020420800340780c981d0103546144010352004003968049000300580b00d4a042c40058212007003c1000e082c00c071b44891145101e0f0354001c002e0755803203a8440448920300b00034010000e94510b0b000b00002c190400b02c0c0e215004581003440941460b151450b2140700c0171000f803040f01042000d21841d007820303904202150286200741c4404c1e42240031500e03607160600103503001038001414894100f00d0103130041400d000303688103844203a40300c20001000c00c2c40e02c0026840303071409118141101503880d500c45c041c6070584100701ca1505100288200314048000940400341010391380b0300e04a0005004030303c0307141c0840d10141c601d0a00040d0800042c2c403940d00c0c00d8065000c40d10685103603409011a11480014082e900e030b80c43c18a881080000781280914080200851540c0032003120707a0307010b00b11b8824140c108000700c0a4464480d40f0003085034100b03640d00c400660810902103407508 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 97157302 1250 97156052 97156057
    0xc030c060f060d08070606030c0905180102250804080d091502070b0409020d0902060408100e0304080a1b0f0909030e030c01081306090507060315080c0d02010c110d03030b0a0506 78
    0x9004000f007519548030003401c0d6000300b40456105568034000000200c21a0001008003580c020000d551f10b0180103900308e5084c4030442c0d4100e82d1041041c400048101445501c10307207a02000d4005800e01c5141400e064072a5400c842a944030f18403528801c2507022a0007030a1302c0040307101c1c64801500c40010b9036a1a06400740e084503520911050120b40365941c0a03061030640030001003071030485a000f0031101c0c0d02a0300500607035040070003443c0003405180103445c140c0060303100a40c507003881c1154840c2c0303504000100801030400741e0810f104d8403050802a001818404446100007581c0c0c80c4a4002000410703021400710b00d150310b60511507d00030400080784041a1100d10240d540c02110b0340144c0c41c8080304a45250f81c40c940000800c00421090000d401c0544000481c10301d0014180301390001640030302003551088600585580314584c00c07000e2181e085c00d00d040c0b0454246030205207848003590603900030001074046014580c1c1600103e9804100b0380d00005519254024003c403071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 97158552 1250 97157302 97157311
    0x60914070f06030b03010b0a031103150f06060c030c0106090c080a0c0206010902160b011202040e030c07031101170f040c06180b0c0c0306040b0411010503010e06040507090b0c030c060f 81
    0x18085800b081114000c1d00140d050b103100400004604200d5000281001420f8000384c6035a181c2961080302c6040811100800300b181e09c088088138075181400e0090b2600081034a40035020104015a02800030001c0e00c6441a041d40207011031900c0300c003d58003c011030202d040000da10100400e4001d80d852013031603a0b045456024203041d070f091902c00c02c00307036110340c1c0c8401b40c8032800190741002c100803500c4c01d8040c00d030700030084492186034010001605d910340c0c1c460a04ae00308120340305051800045420413280c1c00201b68062030541070060752500c805020a403100c1040e00108030f100f41140b5009403003103201c0c014141015440326401c45040d640c28800c91036a546124003032006405110107401289295001c91380f020b065000420f041440503501128903901c804203200c00c02107881043c1b00d140c4801e182c090304640c036240340c104925001621a5004595030004114800d12030780d0706030080c0c00039410b52070759a01ea26007895a45d900c0341500c00410300980c004941904001c0240300d006 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 97159802 1250 97158552 97158569
    0xf19050f030402100207080a03020105090705030106120f080708030c0a0f030203010503071a0f120910021e0d060504020301060e030c1509090c0d050406020a030c090509010b07081606091407 83
    0x10750b6202d074244625080e80244a40070361207840070016030800200410403215110f070b4004602ca08001038294034021b19071300001c1c4264103024080c4811135075005245403541d0010350019aa4006082000c00ca02c168107000d490b01c00000102300700c035a0604003c20340008240c0d80c0000603403d40350700700c08070701080c001c56034143c1000345c0c20884018041802a940c00960001c50714041c040040b1005580c00800202c1d02e9408040030441d004000b84041d000d03070340b6151001d41c80c0c02910044400303010590300140c10032040104421200b6000c5a03c00b0000e0103010b07108660342d5071103030009040c4d1010350551b14440d2144803440d248508041d40602c0d03905859000c00da0400f05402d08001421400419504560328203100d0203240341041e000c0c40b03002340c2c0140001a5603044002c402010354007418514428800400c40030045500ca46404504541c0b105c0f80d0300307407904074502d05001c062061b5004861300b481158007038001d0003a240d01194006104402e2000181d1b4a001529162915481000c99 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 97161052 1250 97159802 97159807
    0x14040b06150301180212070e1002030a2a05010f0f27021c050a0f0c0b18060c070519090b01090e04151103040614070302070203030d09050307080f19050f 67
    0x6004603204007a000c00302145809401c00155122024500000300c0c5c05c800050180c03141d08c2100d0900301140e01c00c1043da0304c007a51500d0800b4102501d800b4005040c40e40080d0324804a0548900401c0d4a1321410351142c02801114011510343c030241a1419003000564605001d00d031080000300c0e54004042d00e09140d151101c2c0d140c0d02080681c6400c548084504940815a40b0003e4803e000141480d441030030000758002c2141006141800550401d40c8180e008001d220480329044102841c0503404980703003540d41140a02c5da504082040d07100a4014402500c2100d5040074210b01c442642c1000c81e0400c01e0302121801120040601e105064816442e0004103010031480300c90500094030440d4042032042c100301061015602c103d0b03080c2c9002d07984401414010004200540e004811442c040d81020b40170b80002e40c4a1141d00a81e0140c0303580c80c1c10340b03000c000c403c0c000e4980c1c46801c0f038502a101c3c110060361b0061076008564400c600c13107003a6034504280303006a00740c542d00d0b44e000c4038090 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 97162302 1250 97161052 97161059
    0x90c0105130b030a0b060703030603030806060304260409020c0705040c02010c0f0324090c030e0f07050d06140709030c0b0f0d0b0a2d080f03070305030c0d14040b06150301 75
    0xb84943d0004e0807a0321040c2d110916452643c450b02e00038464280300b036500181c0a403660400900008019010b28456101001800046454041c420041c150109092850651045001d030050b1140fa0300100801d80046001300c0100c030041241d00c11540c080e107003400401d5800302e04074204c4194a00160104d03064212035081c01d8481c1c1d12214251541003442500d52610a4100401c000759600880e2003035103a02c50502032513814003a030001022220018005845694851911500a4050039000341c072002da0314014030610760810161103690030788130501402c003402c00900c0d054440c0000d0758030011074580042c160022200b281c108504401c041410450213940c00c101421621825070303400420100f000c6401c0076079030510030360a00c10900b1488402d01c034204d074100c0c060b02075100f81540c0e00a0140d80410710390100440380300e03590602d000d0b0303540c1c1c1c1c82d100031440a0040000a48410345415a0b040006da105c00c0396602941c02100001d00980d103007402c10889003a400d2003084403070010700040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 97163552 1250 97162302 97162319
    0x10501081c02160e07030e011b0e030a0605100303021608060a0b011211041a12040b100f0914090f07090b0303040b03040807030305011703190504150206090c010513 72
    0x500200092041d00d88031043c00071103040c0ca180c5a0003144403021901c050000300c540501c2076401d00341c2c034840203003d204010018a00b140801c40c81020501800e00c01a61295409000304500c241d4012010006410191284010101c4a02044000d445490b0340c0030304240780111320f003049681608c010a00b55569601040241256403030f0141070020321000010640380900136110301098040b42e140d1940d00d4185c9806e181c100118481510000410080d600e500c01492159402a008036800b49243ca51101900700b00c81e503907101c1c1c0301c0b9804444010441c500c144d000208804140c4c0342d41c002c1c80d00c85d0455039440341c5000c1030701640b65203c07110401c91039245070043c82e1841001020b0b030f41429550b0400002c07a600444003254442130014104c0300301601442080d0140800130040580240c80c8188075680388201c1c51a015807039642c11200b000700d446a0704882c09000e01014200d0007040c00c680c0030399100b00c1560611000d019282c608a4079511030816a6800a09000c6105181e0b282c10b03c1d2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 97164802 1250 97163552 97163593
    0xf061303050f07050d0305041b030807020f0a0e090d03140105030d20010e0c0307090c050d0209040609020c03070501110913020c03070c030f06140c0d050901090c081e01050108 77
    0xb40a4052041c402c043c0840d50520204150346403d84000c039541c6418034006084541040d600313410300013090030600218000741c090b03d408550544002048144540024010264640c088070300400c0b007000b00060300b58017042c3c9100005907500c2c1889007040000a20002c00e000f400381ea40c0650001c1250b04041d44544030511001441406008401d03100f8090507003074030f030540001c0c42c0c194041d07035441d1164202040804c00400300007404000043c040440148144034001140b025a600802c420304542c1e55980500d00905070307404210f41e501a020150760320b9401c10302c4169165407030b10301801c0e106c280711011a40002e0300141000d41c13030003c440c4048001d410401044260f0310040c0701841c00501e0720070000015502035076001c081c1d12601d1400d402624800403030700c40406c3c107040601840585c9401511030fa4070b01d0001c08500c680d01d040c04540100103245018045a05001e00001d04a0012400019014600c02003824a0381c0605184e4280c0d5001c0c41528049c0e400f800326103030342d022010302 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 97166052 1250 97164802 97164817
    0xe0603040615120c0b040e340306140f010e010f1112031602013c060e01170609030306090903040b0304030302030f090a050d120e0318030f06130305 65
    0x80008140c102000c81c0380b00e03030545800072200c0e03110b410308250030320200000140050100a585900e040d0030850030165186010780300d0407211400d155400c1d440840c80004042c00d11500200048007914a580100070b4001441100c00e140700c800600740032030800c002540744184040e11440315280040700116490741a4210034000c0241e80c02503001210070900c801903889864001e141d849040c130748d11039068840c40c03204250035680362a0b80140c00348100000c903000c180c503d00d0350862610342c9a40b0103036407420b80c2c21000c424500c0c04101180200840e00441d060710445001491460320b01c1c1c0000760364907401e0300d611129034010704c0068401c0c0740400031954040030481c2668100342e96142110320940042e682140800c0e008801c10000966082d49070340d124050000500e810071650b194240c40e00c40ca490b03400200030b1070340071403201c18000303812403c44c01c40d0700003c481d5a045640c5000601c4403014502900c03c1c0603a1000c9419903000046ca5030103030000145c07084c520304c2c0f03580d4141d40c03940c4101e030b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 97167302 1250 97166052 97166063
    0x110a02151606060902030403080105030604030207061202190906020f01090201050711060c0f010203010515040308030f0a020c03040f05040c030e03030f04020d0210080702150c04050d050a0501020301030c06090509070e060304 98
    0x204079800240300d800380c4401000e00700300140c4c6a0800c0d20f005040c007c0141c1201c0d002e903125204120209a001404108849280c102040e402c0a1807807040c000c1e00c50040101441c84082e003c9055080d884900c078002c55060b03500b91486a620380c0d20352402e840c508440a40011424028200030510b00c90490300413000042046203059040060542030602c801e03900038069502100402c940e0414102c0981183e1040e80c50500d024107540d01c5814901001d0700c0301020703c2c5410001500c108540d03044503202e08101e0101c0352155a00c0c00c0040b1820003070b0017030038042e505040207101028000e01802500742883d1000e5820365440b2001c0c3c18402000400503070380101340381150f82c0540c540104a8918036041e0355000d20038501540080c0c0b1b031150100c10303110059400300030072003140b454506030340944804075441014442ea508003d03180400641001d441944000f000104200b4601094400c956458440d91040c9039146e081000e030b640202e0300310010400c40155452070386044001558042c3c40358 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 97168552 1250 97167302 97167337
    0xa0806040b0405250306061d121203040b150d030806240c071401090308070c09020f091f05041401020f06180613020d06090201030e121b010e0c0907120c0807110a0215 73
    0x1907504e07441cac11101e0380c3d40e290b0a0000024002030100419429a1140440300d41204403a00b0070041411042180c201034100075094000c20819a200c0f6011081e166180268480e4500e0700b403103c0700a98001034150b6014494400005800039116070b00225610050311690021032442e15560455404040304880301000d43d0f0700858004041d2000e0036402910b501e585031030f240a441440704c01000317520400d01c40d211007032112440950005c02c8a042c1c903100d2401c00344248601005030b143c010400011356032401041d003007103101e0022607030a503e4140300d030702100c003d601da515401c69111484907020750460501c1c1d01d020003054440c5c000d00152031062500051003a58080640d0a1000b007040c41802610002038600c0104081d00c1d43c810503910802c000c1080e04648108150303200060010f04e070060589200180da840d009040e0300200c0c1ea0a60f106200d00d04004600401d000800c603295008129800200c582c640c40015030042c0742035014207240c0502008038041c01a40d040b06c441d8080800a1307 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 97169802 1250 97168552 97168579
    0x1809110d180605060913060e0c0616050d111005060f060a0e0901091a0f030a141501120b0609060a1703090418080a0806040b0405250306061d 62
    0x8078071561418a1210a03804010300c010b2801e40290f40000d0b00a40c81011600240800340148032180401076070302400029030008404c00c0c080c20252180d041300d03803001c80480c042010000800400000c24403401c00c1ea20011721148040c2d0b0782e15070840300509280c2c0300e000032440300d1070b19511642d08030b00c00601c1407014031880d200080f21680010300e0000052886403041e140c6003480c83c3d200d030140c8940b401c1404000031142090842551001181c1c0c441c0d41030381a0301c80d890b00d003030204242c46500101004154990b11504580c1c40c480910b4110040c0300c00000003407620098008038823045d9004920720f901d03840f51070402140990241c0460781c0b00e019000d00052144d00b2094000ca88142500910703107640a540400c0200c402e00210a000c0e1102c280380103000441b0201280c01c003946030f0070200e18a072104000702c3e0082c024200e000d0703007261a1805004401d00d0038046581c0d9409034080041c2d4103d203018084099074040e01c6280c002c903c1c1305014000701d800c1c41c0064117200c407001d0b00c2c10b440d0194 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 97171052 1250 97169802 97169827
    0xa021f0605060316020d021207020d0602071b0e07020d0f030b0f040203160e040c081b0702101d190b070201050d021303050706030c0c031407050d02160501180911 71
    0x1e513900807252009141204a075601031103a01c0c220f451500180288800324142000184201036009100305880c2203070904010059040c5c4d004940c00008104a12240842e81701a4801c18042c0b442c0c0c5004520000340018800510000c0c0d51041c1d40e1361140c0f409003114264003030b0251403c80742d84880d0401800c003407501d0320710195100d00c549a40480c01c0c40390000e03002d405584079000080c020f0b801c2810302a4581d03008030381b040d0810072154122505c0c0c910030014948501908100960095540e00c940003441d82c0b000c0403580410030b00900c0c50414500070104118050300c64412503200760402c000b0080004030f84054403505006041662500411000303c004036806001e2030318100c0300d400e2061080c40700800c451400340c2400c3c00c00304805812810b0140018030142c00007010040d40c6222040d14451507020380328500d03032082c103c5200d40c11400f0003030340703982d011100d203010f41d001c00c040042c0c1e82d03128110320100c2c8604542080d84584c2003240f2140034004211b04a07002d00030400030300380d5030103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 97172302 1250 97171052 97171057
    0x504051509121e270f0105120411030715031a2e02011112010f050904080906030403110d0305010e091501030b130b04030c03020105010f08060a1a0307030303060512030a021f060506 79
    0x15074130720307006065001d0801299000100f04141080f20910000e0100b0b10080c41c0c1c10b80050308107042000011000e00080d151200300c0d0041c1c0520403001440c81c04054164000003040190000d030725003c00004410b200c060b581110016010711000782d030082e202c0d450103403c000c0a20726880040380700d0525914010382588030103444040d01c01c0001c010000221802c0d409000742a0482e0b040109040c1500d40c280e6a01408108500c90900000410f00701400341c03a4031010380030307030506071004962540d10180007403c0c01d01c100d03121a5409000a081e204022580d00026104100201c07280d0f400c5482d00106d00c03034001d1070f09404405140003240422030803603500f48200d100303948490301c0700c50a10300282580c0042e8006643d00b24080c3c800d000000d0003042d0030b548841d0480c40060702c09400c4d05003980d120407002210f40c0600500c0000f001b816455049503081d113009031011518a400901865580c0c4140c1900900581059010f16003a44403510315545622030b1035004643c45855400083c1c00340e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 97173552 1250 97172302 97172347
    0x90d0506060a14030a060b011716081803070f02041401030c08010b030307030806060a020a171e0403032705030706030b010810030308010501210504051509121e 70
    0x36485081000024a0201d90b150003400030024048030f041c0c85072001c00d50b0b40d518000e000304860b4840890700c1250744181240c0104885140400040f8200500c401602c6540c114035440054a40c10002c3c5501200a01c40d03c0e45000342d0380118980340858560650300c010140040340d11541b40c2c000c80c164041c50107441d5000e18042c0c0007224549150041850844034a407451502079003080c07107050042500180c83d1940105c05072400c56032580d00c500220700b08080d2600080c040e0b000340910740443d001c102e015142607240e1880b03170a191280c2e9207141c141d5000704c1c400100090300500304101513070541d5070817a101c440388a24044c40a900c2d00300103030800001e031b0040707000240c0c0c41306550b10541c3c1c08005290040111030700300340c00606507280141100ca05000b041d05200c0b610f001085065100c949203c0c000c9400c8400300100d0600d46040c81e00c2c2c056040000d0b250282080c0801c082c0d201c0450400680792400e100c1c0c0b03207021190b80c00c40c84501d070f0841d44029001418446a04038840403544515603 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 97174802 1250 97173552 97173563
    0x50417030c1b18072c150403080315010903060e010b040b06120103030e0a0503010501080f0f0325060b04020d060302040e011a0904050111041d010501030e0d0311090d 73
    0x407100c0d165140362030000c1c1016004844052403403551200d0701c2d5488440020080c140a14a0076a1044c000350f038000030007991000c101002c43c01c0300096180010300b46520707840c00c0307841440f00441040c405034680124080904a29410001301311121140c40d00f0f0302c558401130405034815507480c0c8912003101c1080c1505051651112100d60307403460303e842800c0b1b51200898169040c0300001511440001050100400f4048a0a14002c05036240c2203000b0041100800078001503231102d4181d42c0300c04141070303044900d1140001c03402c40c286001c81900e44c500e490810b00001c920b00d8110413000446148003e1320350325030383e89510300142c40b540010040803c00050114100d482c45c8180002c0742d013907a2a020403649852607080c40c10103c6604a207248004031200300c00b50700c540c140a40107014448500010220004000a40c009175004200c0080600c10100703807940e988030019015211099845c001c690003407550360b601c6a000c0c1d0700c8040e12405004c0902c0c00c1029880202d5120105800c06403071 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 97176052 1250 97174802 97174807
    0x906010509060406060e04050426040305010506030d21020f0d020a0e040c0c0204050402130216060b0109030c060c1109090708071a09060a11010f05180a03051905041703 74
    0x4605010700125009441a10100302c0d45103003400052900720305114451242d9112000304062003984180702d030071840c091034410780201d821140c000c51b5600c50b1000319000c0d400c2400003103142c94003007000f1500305225191709903007034007213200d410705400e42101c0d0000140d0f0070710011160600c01c00141c030180641c4e180040e070f5024100405899a92188052032045d030502c0001328046138459288610607605076808901615a48001841d151200752110755480c80811156001c10900f045100d240c0e001c0d40c020405141420011107142180e07010240100c1801d40f41008014490f031301000c40c003801341200b04e6000300800c0c0019042c1e60240c46001260b4003040b014030405c40c06101d00300007854020420041c03c0c400c0101c0e204580100d0070344501c00da00200d14560645e014012040c44104140c008100044140d60707124001d0030f050b200e0940310707014611300e1a942039001a8014a0a806803134042c2000304120f008144100182c100300e04119082c000094032400307103040c54080380c5040000c3c58 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 97177302 1250 97176052 97176059
    0x602040f050f09090d0c03020106170a0b091203010302010809031e0405040c08100b090a33020a0213020d1509091403190507030504031506080705061215010c0b090601 73
    0x30ba40c5004045480c8070340103400500014910000305510411098140000900041c0c101a4010009540700ea92048480510b4a0780c1400201d00101498411580600f040c1c4560003502d07a40c501c440e000c240403150400041c4059030140308426400700160b0304513841c1c5100c0c100c01c0d060001000030228169003000c1014000303480c0c0f0740103d0840d04200c2c82c001c1d581c0d103003210310104c040340c00384a1154026000103030500d40380c5510444030f0103003803101034101d5000d8a0034030340002c1040400d01440411048403a088082d4804102202e1558008200101c6048106410402548402c010f4400341d0780d5000801150b040c00c5e0300020061a009030009500e40103410048000340c5a140c5901541d0401c00204030311340c01c800d0450211034460720b005600c514052405072250300c43c0360009040d1402400c4500728420703030b07504464107030b4802c24140e9071030940c0d031028083c4500030b43c64109081448100041c0c0c110440d44d808442c0b9840514180c624000103840e101400702085d40c00142a410070740050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 97178552 1250 97177302 97177309
    0x90d1e03030c0203070b010506030a0e060106050903010b0409081b01061203020a0c08070e0f040503120a020a0e030c130e0a02041118030304050a0306050a09052509060b04030312090602040f05 84
    0x2105100b6003400510300c1c242c000e585040da002d00500585d482401c02001140041c1d440354840c040d9010700c001107a00550319001e01911396045880c003244030313608129500340d013400c0a000b0403c0003039200036402d00b000c00d950206200440207111454041d9604e0800044a01507180392400c41c41c00380d0050007a440050805440f80c01542c0c011030794039032141c801000340701e9459500d9036100803a0b4088249544131890030500b0f61145009203c502c111010610003114466402004900b00340c0d100d80a1607141c8605241e2595100708800ba4480c40d401c10b4088040c4603500500400c150090035a0aa40039a41c00541203844180800082030000314035030070303051004c5400c21714405084008504080c60500020025040740c0001081244c0313800201e03030410700641101c051554084256032403500d03100303403040c2002c1e80160003411202c40300342c001910360010f210380c50503640a00d540f02c0c686429918140e503225403002180d203e003603840e0102d02c0421101e2020780040d149482500b40c41d20300d00f0041 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 97179802 1250 97178552 97178561
    0x70b04030303050a050403020304030b100801060e0105091006140904060b0406080906090705031c110d0f02250303032007050c040606030212040b061801090b1009080a0206090d1e0303 80
    0x100328205d01c0d0006000c0406d40000690302140e0f4403034054501944e40c4000f11301c001005900014280d0308105002c00c060800034502416104103032800c21107581e89103c00607000569114113004104004000201d0710040700003013154400180c80458000c0d0b640c4051000e80c1d00c203612810004031084244404608140000c1790004d15860003081c0c210b0600c40003903210b01141194400070808444600c0295002c5e441e171606100e9030700182c40140050b104050b0442140400190060148011180b0380c140f0250351146020307103074040c041020b41159030680003440940c1008c40d6210040c016804034041d4400202070185c403c0303018000e04440201400145d4200c0c0d040720042c035005026540c0241c0c8015107070755005400200c01c201c3c03600d980010608140c5030928011204034004c00108480301a5000150940c0040e10000d002210b9004200d41003d60f500aa455a0b0080340310b1001500d40b040c0078045920b402407100302001d03c11f07a120710801990000e1a1070009a199041c014550144038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 97181052 1250 97179802 97179811
    0x308161208010f0605070611030a09050606030106120b0a15030309050103050f0c03060f040b03010c051e03040c09020a0e0d0b04051219051c0e061b070305040902070201020f070b0403030305 83
    0x10101c24950400d16001009030281c0910800c1041c042402d00170f001c0709400003503204c403040c0821607603030602c81c4c107001c040c08007103034140c1c5c1900c5a940400c0c1e15060500c18201103500701c07000c2c240404c58560f17035a4008007000c4c00401240792610250103054040ca90104021403080d03ea007040b0301e1034240054143c400c01071000009004910401c0141c1c8081e60869601c04000c68071a514510b040d1300080083c203245100300d400d0743c680101c0000c0b1503003003c02060620700c0b07a840006000207103440e42c2c200744002c81e0000c0c100d00c03811404000101c03254024041d08130160910982c03a070014000700389104a1800255054601501030005121003441829000000c4d40e804070301d40030356510b07115200c440000e0040100500090390112850321100e44614500c0c051105100341c250282c0720564030402079070b045080441580c0c1c0424115562400c49001d198542c503143d040c9032034248200001e400c101010303410350040c2d0303459016180083c41428054803040130b85c0b58542c1d045040060856030b0040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 97182302 1250 97181052 97181057
    0xa020d090501082a0307180504090201020c0d0c0e04060c17010602030a110109020d0506010501090e040308180c090a0204090e01060e01090c0c08040609030b070816110703081612 78
    0x1182807200da40d221108680c0002001c10080b200780c54144204002c041641d40301032010004000e00201e20380c005c0c0141c3d140d49600c64010341e4a6103410401c001c8610744040203000da885804410b00d20708090714400c9040c0c7c022054507840310381e2030035001c050358012501200c40355038035a020200960010008001004001e4102c90a903040280180d624802d0f010f0440500c0070f00e000640020100f5080084995805880c4043c400c02c1c501c4d1140e6280c03828000c040c04070312001004540002c100180912580d0503030754650180d1690319140200c2404e0940c41e039440e000d911b00d0b00b9259141c0c3d901c014080c00c010300006030f5503440e1500c10303801c80320021100a640d03410304104020403100d800500f415107074039603800281610b00c4201503c284a003400e0084c02c4103070202d030000741d481e0001c0041c0112401140c170b51003240d07034244007112020411500300b40c2c1d03104004a118080b83c440d00c102d04101803910300710350f041500c07500c1e000303d150054440350605404001c039407410006840c03021000c003a03a50 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 97183552 1250 97182302 97182317
    0xd0e0303090709050402060d06031b080d0c021e03100603060506030a080409180b040c05030c030c0d0809041508070608010b09180a02210414060705030a09150e01140c0c0c010e030a0209010b0a020d 86
    0x3c00203011015010b406449810d604003210381c8007086502c00071489030b004080b5215082c40200b0f000c0508140e100648031949400300260889c240442c010001e103a00c000d442c0d00d8035040040c100020000c10400c4131100480041440c0064200c0d403045008900600244203e1450001007510708040c510300d1034001c0d04041c080207002c0e22192420320704240d00c124a00e03120b031004004100280f40e42c800e1000482d49106000a01880202e918001e441c4150345144103030707880c2c0c0c207850224420b0205460700001c01c0b04192082908559070190401e4041d1400740c507181c0300d441c80e003594100400601d034041038a44c09000800040b603e080074181d0424000e409140341154011b02280002801d00d000191550701c200c0401c244242c4000c0398003100c52041011101c1c0d1141d0030300a150807006c80c003140005002041c840b840043c240c0703200840d483e00401d408031740d22004580d00d03424000032030f8044c420515900c005030b442110083c01303441801c6c5482c0d21500c01c690000e240900002d150802c0c00040f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 97184802 1250 97183552 97183573
    0xf05070308030a1407031a0f0324040b0a050112060510030606090c020606090c040303081e150f0f06041809300f02070512030c060c0d0e0303090709050402060d06031b08 74
    0x80401e0310015086520340b108508d824082820300b9022007890f003203e0b80d481101e6500c81c0040205078002c502420390701c030042c0d440800c000101c5000303004486042000900400c00542d268000f2075225144040008101d945c0c1e43c3d880c002e0b602c40e5048045500c1d01c850600c2030a0b90304000c040d9110b0700c100c8404580d400c1048004203a84601d02025080001800006044050070410030310000307849000b003684c925203c02452500504140954802c50b4010b070205400e140808502c540035030003d20302480c151a0920606440044081d4107280740d0f1901c400c03c000c5500c038041004d10000c41c80c44804400600070303660603248030801400d001d0040c8807801c09000d507800105142610030035941e02400940c040070980c5103001d0900c1925443c07241100b040221400000030f462525841241807160548a442198980c0821541012598041c00d410005550643c0046410a00103003069190020960304541980c0c1281c10903901d87c0d0050040c0e107042e4070241c0d140c0d402403080e00064500d4501 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 97186052 1250 97184802 97184831
    0xc010306030803040803270c1203070309060807120e010b10080f060d03270f0512030d0507030b1005030f06040b130c0323041407120f05070308030a140703 68
    0x1004c0c0000c0c020701d03004000204007804400c072024211070074024008502001d500314036690b0f0003501c6440e01602141c0c89079028000c00105950750940d0503100c0c101c1e0340d07052050840e201500103221004001e0402e42000c0d50340c1c55403003181d040d55030f82000850200c03c4c0f00d0a0240c0d22000c0b1080504005004041006001442400c581c02040c100c032500d000407580e0800715408002c00c1f141b80c4111075031294218601014420f901c041311802002c4115103540c5004000c030000300c1c03000051094004200342003400c48194000750f40b1500609000541c0c1010fa00400c0799240d02c6800c1c60003040e400828044070100386502690300c03280407113041c03006c0c0b2181c801140305001e440001481c103d8490709035001441c0240c0000c00e4076400ca112440444550300f041016000041d00c4c150b4615814011138950304102091150030307945030075004c82c0805129680c15042c800c001c1d406941d00e002d02040400081e2006001f9406203248107404a50b51158104080089001903c11402c4c5403604495001001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 97187302 1250 97186052 97186057
    0x6090c150c0809130e0d020106091a010c020604150908010b041116020d1e02011e02060c0313080409050a0e0c03100b0a150201090c060201060308120403030b210c0103060308 76
    0x542c005502c07902c4000580102d102d40c0d4421a04540e03103810111060070750000010040303e034511550007441051358a050480864061040b00d501030000000751348900e5000d01814410b042c8050540d5107090396618080715400c54400c0900001000314504008180d02405002d401403021202000401c281c012242c105116110030200c5821031607401c2d10a655940318200112608990180e148070745511040420f03a540d000102c0c046030a0100a402c2420b10301f440480441b007540041191780c440701c644403083e03080204038208840c0360080040000e02e0107006400146500b0501042500741140c0d580103640c508035500360103a0048000c20a036550000f00514070300e203c0b00c8000791815144001ca03420405035007192041c1d110640340d88403507aa0550198608a005002d510701198a819040703090700c03120700c005440c58900b4091400410081146e0300c0e0403a00c2400c0c00901ca842600214180b42c0c1c00b444a51090303101080f0501078010184089000c444092804100180c255a140ca00301d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 97188552 1250 97187302 97187327
    0x10f020309061c1508250f060c022106010f091a0f1c0503040614030c0301090b060403230105070e0904110307080307060b150a1d0103110706090c15 65
    0x44040c5061441043c800d5030002c21105131154859080c1d0b178650b088559910b9280303400f1641100c1d030000603035054410440c21416217440e044d07140d0682d807518008885001000c030080c6c1c0d02820b051020306141900900c1601003103d030703402030b101a41c50001e81d41000b10f0703da40300c0d032410340c00c0406584111200c0c40b00e01040400c21944100d00244020200d0b5100d2485d0129080401c40700600d1010700800001030300443e4607655078500800010707506000705000581d141e112611040c001489030600b0740d00207821803480503150904140d5a40c803034100c19103540fc403e4026100b04c284502030f2210038000d1503401744480c00c01d41c840d5220300d4041454404010005042100030160a182c1660203100c080000c0502a0403651185018100b0318010b10303200700d65074450300c3c1d0020310103001c4400c4000d54810121b152074448686031107500003002d100c5200809030425540359400c882010f40036000d800380c540140c8c1c000900f2000c500d00800c059046070020719141c06107244464005500140340c1010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 97189802 1250 97188552 97188577
    0xb0f0d051204060206010f050a080d08040305090a090e060702031813140f0a0b0906090a02160818011716180911070506060103050727080a050a02010f02030906 70
    0x40608080d810691070903200c550719100003030000307001903002505505031072a1201030400507a55004000940c040d43c070568056811250041c0200c074001c449031507209019040c100e151013541400500040304075001110025920b001c142603018041141c01e42c0080c003400150301d8000f480001d41e643c100c0502c0400e2090908040c2d18222003159000000000030695003000d00d420300003842085030f0b000301e0320725511078681400040d480c0ba01a01d21409a90041e2060700581c40b0441320101941c80301c000b4140401c042090318000130902001440303c0c20014000c01080014a800102000707500c4070301040c460080b505029448a1100b0088003c20f2241081c07240c400154101101310f9003542d11000c90b491802d0003421280c0b01c802d00400b006440713602600c1c615501c2e0001501205d2080da00000051001c129444059500340030550f0820000b45142c01200d0350f90456515152100340f0441d0740350040c110000c11960002179980e11170007640040c600304000e00000c41c080b400340c611001e00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 97191052 1250 97189802 97189819
    0x40b0705010e011503030215160507020f0901081014010e070c1b0305030d0608030a1e0e0307091409070b0304030503060d0b04050a03020601050402090f042003130203070501030b0f 79
    0xc11009500c14018020389000a000109072000328800e0b01d046448190050700612a8903046c2080b9420650f1161301c160301003030303005410f10404075800e80160380100c0c3c000b24050030315035180e51501001ca0080000e0001840510522078000d020b46051000703c0024410860051281c00b00b03000360254000701601d03114080e0003803400e144412081d542180400b000c507108020007480b04c088010001034030862014450240c1c2c4171840c646d6841a220040c00142e1060b9840089154401d410034030310710340340380000302a07403c0c0700080d0074200ca0f544181d1207141d03102a07103004150501081c55200c0600c2010300000c0340b40c89170703030340039480020001030030410008002046682d80980146070141c00684101a83c5010320b0310030307603482c00100300340c0243c07040304000511464a03000b20750080e030700900080c101e04d054106210140ca0100851580700c03800a4444842058a1300550311503281b00c0c2e403442c204080f900500d4100b0380700f80c000c54101401c05195012544642404158450b0291900203 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 97192302 1250 97191052 97191067
    0xa020409030e06040905060114030906040f2301060317040b12040c0e040f06060906080a02040207080d1b030e0c0d1103010b09070f14030603070b03130602121e0903040b 74
    0x80b01807542c07111240d40000040b80c00b01d017840080d88114403035082a00c0b407005000400d10346206c45c2c00103c4241403180d000d10300050021741030200180c110742c41192310108000c01041140d81d40e00e510002c900725695030300703000c100340300c80c0c120013403581d0842c200789074030b01410007900c0f500500c0394a09900402007400b001c10f08111030070080b40020b1030504031102032410107240100302d071009000b040e50100d080c8500407501e11600d22401c000c884a890040141c622142c0c28000650800e01c1d007030702c05480501080310041060b00800d00a151004d80e03c04404400c01b0b8041c0807990420100c50865020100c10011622284404041150481040300c00049030100080c05000441e01064100583ca428440d8980d00051041c15082c503613203a03180c20840c0700d40403920500044030900d41c0b41d8003803079007040f030701d036251004581111100034501070049890300e80c3d20999021825081140d03115800700800c41c0b20700e421070101502242d4180c26182801000541d40b80540e0007042542030001a811 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 97193552 1250 97192302 97192307
    0x4060207151b030504051212160602070b011403100606020a1713060e030d170f060d05070602060a0b1e090604061d0402030d140421050307151107050a02040903 70
    0x1c0c0b00c0b84042076881404a903103860000c0c00b42c0c0040c4545809400741c0442c58469601c080b50346d0615a05c50041d541c101140007080590300d8070088400d885640c5e003000b4134008200d8074812070340070f00038000031724800d1030502084c180b030b080c1d201007202116071130100240301c0c49902040c0c0c15051a006032a46005080b044140141e43c414140420200262100700060080e0803d0340c41900c007030308905a4075100080703007060352680c001c0c0340e07600c1020030780300b000900d84800350144030381116000e000c1e0100702500d2350b1800c0c03600385a5000203001d80e001104001501d1014042e110041406075110300c034038680c04070344400768007141c07104a10405105c1c00050a644540d800000200013001c7c805950000310400ca02000d142641d043e40139000b071203480302c1c0c498020580840308240c002035045ca003d103040344654602001c00d110005072130307040107404085041000030b003100601030740035803109286500031803007102c42c00000301c000041e06100c2000858800318020300e01a03010b942c0455034004501d001c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 97194802 1250 97193552 97193567
    0x313060c151b020d181e0509091515090a2a0c17070201140a020106050d05010c09060f02070308030907082b080130020402031612020406020715 63
    0x260381d50389107402c41c000e52400c00216000b0034042c058080c0d60485110b04401c0700e03105000050032250707000e403440412101d0304049805506402d405113450103280c54500144c642a015220441ca56200c15080b1140a840080603038020041c0b0303980507220210b81e00807840621000b0024000c2d155a82d8142680200031424004040d200107240c0c0f0080c1003000d030190280402c0003096800b50f4000020101d408030710021110301540585804950220b28580048664402e017005000c55403114000a03541d01d980d40f550200302d00c00c40012914412030756000707090000c20b80c080400c11400040e42d001d0181c020546800340c90f001003500350303250b6404411a2818109130b0040c09240300b0071a0351b0031451218528001c1805804106c0d50301c40f8482c0000320761000082c05920010342d044941415110b000382d80d00e40c62015022044940100141c0000e400c84c1c004031054400b40c0c3d04181c6000401e0341c0a50546040380754500c0846c101418010700035138030301c01c0e4054030a846002c8007151401d01d0242d4803 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 97196052 1250 97194802 97194833
    0x80d140c100c05040806160509100c0609081c2a030b0a0602060f07180510031e0c021005040506040f030c080c031209030901082a04090501080607020313060c 69
    0x405100b000e602003401401607225110b819007600903130b404128203aa0305501c0c20b140c90204c1d66001c1c10620b501c000c001c0381c20344480e14a000c0c407281c80d0090001a045010300301140b03004010141c3c5624050700c0b0034485640c80c00c61100501e00c0d2844014411203025007114220b48840c803807120600364442c081e0002e082c60180f156000ca481c120000f4503580c005130583c410b101381e42044100e500d948400b6101e1041104000d40d01c00c003d86070038091420702c14003641c1a401c0381c0c54041910b128001c1e04454040d100c5c1c2018008640f10074031032102030b404128222a014540d44100410315140c1c451070380715000588024030035520b900c80f6900b8548940b10b9007145035040100c036662000320301d400c00d41d01d03071220080306031160340c9000143c0500e8020054542280c01030316074083c542c4c0c6a0000721440c04240241080221180258905420300c500107000a050241030010706541400c51803441c118000b0f01c0340c0c04640c420040840c00c1c8180301a88000c407581410103011200d103914062500c0e000404c2d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 97197302 1250 97196052 97196083
    0x30309061503031c020702010f0f1205071e0e0a06090e0105060702010c0b09031e0418050a0e010906060927140c0603041a060a06050f07060207060203010e010609080d140c 75
    0x1414040200130b58000c00d000e5100742c9410304442035402e404d030703110581c10351240042010609030440c01c1e01c85800207a440001072410900c8500c600c0e030348050072940055140b00055900d400c10015051000106019160390305014440310301c0c0400d4075040c070805000d10b600a14001c03803401c0c11a40540300d01258643d10120010003481c110303000030741c2c98010765441c114010006055020004d00c03441290191080e4418205841141c0a2010301404000c3d12050303030140d41d00422951054203100d42641c01d403040401040c2d2924041101c01034801c005040f07030f500b80300078110600e0500050b10003c5890303803000c0080e0030b0301c1c01900100d040000d5000320381e030405000401c00003042144865841c240d001d68281541e203482d4201440304400050042c200411010070840340403c00040c06807800074801c02c405460511a40d44000a80c0c10aa1008011905943c018003800740c000d5800409400010000c14100907a840b00500954690701060f5132030383c0001d0256401c40b01480b010180a1852 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 97198552 1250 97197302 97197337
    0xe0a050a0b040b01052704020a030b07050706050603061611030d050a06081e0712050a05010606020705090c0f0307030504060e0a050303150a08073309060e010203030906150303 77
    0x1401d000086010894044480020480001c116850042c5403020480f0120318015044540300b4030849403144040c0c0241d81c00f41e8034610000001c0e007070b141c59a109030140da540c2a281c3d0128900442500d00103450b1074842e412030820000c401e03000d88004000d0240e145860300b00c003140341010700d00394401c00781004190350a0100f0440e8030076598001c0300c00c0300c80100448031040001c0c54441c0740d5070503120001c42d19800940003000480004420b91102c1402141070f40d07000070b50fa951711400c44015610140260b00121800c01c524030f04465416032003002148198500038869039014001d10008041400f8140c0e94030100302032007482d030310120300d00031070030111410100581070081e5290022550003400e0800c0d00499a5a0f0800650000c00c0703071700c0c003801010084d05020403906a5248500e0504501d14000c95008414541041c160203008880e140c9940c07107420140c0007000064a83d64490641d030040051014100e000030f8103940c486040f0000d100c0840044000a00310321a282021041d0500e8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 97199802 1250 97198552 97198573
    0x241204080415020d080a1e15060f020601061e030902040f0605042d020a050c030415170103080a0309081909051e090106030203060112110903061b040303030e0a05 71
    0x352001801a9000d062090b4032110700544200c0c1d541000003a04030010341c00301c0c046580c40c000da8010303046042e20551005003e20242070703c2011500d444c81c001411640340d04040040d59005541211031a0031071014144541c14a1000b41c5841c003050b180c41d12041c69050340d40c071010310a07400305d070700e00b64000c00c10f04c50300a0b0491500041c142c940103c41c421886c05c42c00501d40c0d140c0c00c071640c581c40548154825803005800414000750410b424100611000300044c480c01281400188080e1014111101002019200040c00b80020480c0c1e211100140001880455140c405803880900a403801060250181c81e0049150080004001c0c40c400481c1c61090030640149160094840540e210703e012341c0107081c0d800c07522010b4906107800103110070050110501c41c1d00110703031080c0f06041900301c8240151480c0c088441c5000140315614001c03516101a1809210f4117070040c2e801e04581040564403a40001e05109521004042c15503070030507403213000000d04c60620301640105c251601c6004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 97201052 1250 97199802 97199813
    0xf03270307120201060602070605070204060906030c08060702030703050415020f07060207060206160e10090b0a0908190302190303090b010e071205070504050f130c050c100b241204 79
    0x1442048903034540038408040c02c1441481007031708569169000b07058003441d25005503004c0e4880c000982e009034450320041070041840c000c0c00d00545c07007030b85507140241c540700340b04d414841c0c0640780400b1508100288800300e0b40c0101602d040d0340c0f0b02d000c26201100201800e80c940301000440b40ea031401a840700140a603000304600e41241c9454081d11920740c0c500814101e48150840c5072408a00404074a042a081880d000400c0c140c13203080505c3c00603294007400440c7e42002c03002d0800602d52203010b03c00c0e50b505000001c440c2204000c074a0310200c00e990040c5d101d80c040a02201103d08007a01d00301418421b801407000140c00c84811049075840e0184180e03030b500101c404c04042118048030000c081d245200e080e21442c6d55aa0f03140c00c060802c000c00401c42c2c4150001ca030301c1925850b0010149000740300c0c40e01e241400c0d07141c0c1d65681e060032614604001c907444000740703070074900b00152242e5200c0e4a02d000c2d01c40c118501c21b00482d1a030140f070019034081c0880da00060401d09040008016 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 97202302 1250 97201052 97201057
    0x601030902040f0f0b0609091501180306050103120806031509010f0204030c030c080601150e060c010212040209090f0705090c120c0903010f0513030e06040b0d090b1b0f032703 77
    0x2690134024007443c0100300a01081d44514207070203420042100000740f0030b61003014034003c4014140740481c19076800d1500405142c101d50000e0f11800da40302c004000304100400781030b2610406081202d124908200003d071510021b072409258aa402d40c00200101002e5100c9400546600e0085454588a0034801c0110015020882c0c002a0034680030412090000300207041301c034900b07403420185007900011030b0031a02c0c2d105a02e400040500c04940616000c0c00900f0440c0741d0100311554501e05401003100c44240941038180c1504070344080f410b5620003040d80c80a49001344e0301e0141c5a101d100303da2500d41f040c56078440071915601c044c4041c4481601c001c2a0002c0218024009a088254500d00700ca4058610000611220003c600000d00500c0b4900820a00400c09400c060703840000000e140d000341840003801d0381e0b81c86038104008070781b05920341100910114500300e0398047e5203070700c9522a0060710741704c080b80440081c02c2c90085540c410142d11001070307411a8191000b1600da500d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 97203552 1250 97202302 97202321
    0xa062102010e0406030b061002030903100c0c1203020a0e0a082107051c08220f020114160201120b0604030320031204030f0e010206061905060f0c060a021c050601030902040f 76
    0x141e5504240c0100182700000382d4010010040183c410003000100c04001880007907422802d024800c41c40c0c20202d03180b00d044007142c0480392405640c0b000c842d00c0c0109019030640160b0700c0f6521039842032081c441c1c0000c90702d1441c1070701c1d800702c040880008485c0140380100c1c140188584140f00b41700703440c024800c1284031000c0c101e865a007400e44803a190101030482002e0203030305081343c404a0b000812a80d90b1107074a00750060600b00842040340c1c00c9000c1c039501802542d01b40d100452068401c5584c081c4420300c41c0980c80a00300180d05403070300048c285100d140b202504200100ea100781504141c8000c5401c46081c24040701d58495501141480e6864102d5058011800b178842c02000c0c0c0b4012810720300d5040c4140e01030801640d501042001a590a00d1892900c0304520800b00b101d4640c00000e100100c0e03003c010703580301c4c4003804002e454120010915050340e401809100085040702e00c0950090321518008a02c55555600482c01810035500196006050042d82801c1103450350041d181c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 97204802 1250 97203552 97203559
    0x602011506051602060f0c0d030515010908070e040c090c021b120c04020c0f0109050a0c1d0a0f1407030b040606110a0213060f03080309060a062102010e0406030b06 72
    0x2a03070765400d4140c81c1c50141800005842200e04803080040c5032600c02482003140e5868624105030305144003602e81203080385100c0100f540c9009102070002c01d02c6001c00e8114003460814030590520010399110052481090000002c08005c83d04000202e0040c0003d414001410440c440281000943e02c0051108443e140c0c4441a401c4a450400c143d079424203014444c01041d003040c1020600000354401061595540100c3c0100c0c00500003c1c002c03014068011402407a1908190500c0b200507505035000c07043c6114000d8106414001200c002584520300e4040000d200a81d207007900302500c80f2103204c012010a038020040d07450b4150344100343c600b90596003080380366202c040c25a00c00c0c84101042c40913a1100482c4001440e01d01d0700640c80704801d05c00810388a6464071418450a00d0b504100c1e04010b0100c01c10602c182c1c10003c01d80d110054001c00d118040c9803181c08012400540341c4941d0300f8505110810959005140c10506000007134001c102c01e43d60307424107e803030150036542c8611 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 97206052 1250 97204802 97204841
    0x50406090603020702030309131508100c05090108010e0402031f1509020306010c0206130f030f1b0308040504021308031c0e06040b0f1315060e0906010e01061215060201 74
    0x581e10302c02d1090316202e5901600552034071601d40104907681d6200d542803058070380c880f58078640c070115040c50300c00101080c1000f802104844140034094a0b84000380e803082110030700c19104183e0303000794801c0c11201881240701c0d41c0d445500100b0b08002c00d00354110a44c0c80340031120318401c600c9500005425000c40c100c0d109858440440708241c1c40141c80a40c002450040e42c4000b40ca4124000c1c04201c0300400d000c05c0850380d800340301c90503180310b030300540701500c0d0b49120000b4048407850445c089482c4200340421b07107003581c8c0e4200442c040d50003101e01540c2d010450580c18401822840041c0c51000202d944810801000c44915181c0d5941c0144481c00c003c030320401c0760340c0004c0d024040d50b032001440300c440e550406598142d29000345901d0032581d80d5518280886c0c100030103860000011080812041c1c00c0c5240d004d2141005010311000e54068001040810410103032079054820602c0c05400000964040324058121400800302d18114041b000a8042e0154029000d50f0104c101c01c04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 97207302 1250 97206052 97206059
    0x5060423010504030203040b1305031b130504051f200c011103090601050d0807060203070801030b0903070b04020f030a0c08070f0b0f090d03031e0e060c0a09170309030d05040609 78
    0x1d0985900352002409607000303100600c45069140d0161805d10b00c1c0c00050065251754100103031034440c0c802070790040250045500c441d9800d002e8103203001100b5205c8140405e081560b40d50f542c1c3d1607019402840e890741100c40c2d0010441940101d0000118900d410098030020f020100061f80a100240b45a42c40c2c010130341080d90111040e24851920040a000c40740c4c40c0009116010211410842c2c15241c02c11445000602501c06540100c542da696a0403540c15450a81ca0811014240392020780c010b1002c07400041600c241558481d90603507040a0110048002c20b14003032805400405070601103001144084000942c41d0840c0c000c1c1212a244554500f41c00180e849101c0d504030000404000205081c101b0114140c1c3d44c5100b0314000400c440103e18680c0c00c960002c400c3c00c0642e440d43d08060782c030320080100e1604800070364107052505c01e0038031700a00b05031428411141d1a0303105104462251005005544c201d070700150507129040c584c0d47c001400c546c4580140808a80c0c1d40f43e010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 97208552 1250 97207302 97207373
    0x30c030d020c2b030305244203040302120421020a1d041b0509010b03040c150c03090b13141201391706040617010b040f090c030b070c050604 62
    0x380030f8030301d001d400c4181c811078512181d07a003004d000e9107600080c84620740d07094001d03c4e030341440805400c8d2140003940340d05040c80c0003400e09901d170200d465050014001441032104100849a034122285410402190144007041e801009540320a85008400c00d180070500180102c891180f4814030030051080d000648000030801c15020f15504802010018003110070040b0055400c18002d40c6030040e0113540d08210103580340080003070310001d01c180d004031041503007010061025040a0a201d401c1c0306860442d543d45112920540140d0480c04000c1041511181c2036118542c0002000f4032800030000c0c04e1200b8a064003641520340b0320050800203e50555031801c0b8500807040e9070b5002c4050a03c084807590800241501c1e500070b6561800050030f8002d00c1666510792090320010602012000402c81100d480007c120b01503402c1041c250300142c60707800410203682c2d00942c50307001c540f155041140c5005110304000c10610403181400188600d0030310b44c0008036241c5000007220306401451 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 97209802 1250 97208552 97208611
    0x406051b0a0c17010e0115180b06090103021305090a0e0d09080a030f022407020c120c01080c0708070c140102240c0d0203040b06030c030d020c2b030305 67
    0x741085010001c2800810003002c2c1c80290400309200100e10f05c602800150708540601000b110107240c4048100640a0344820300c0340c10340c0300c44030108140c0003200046022481012403d07810581d002544001e041c550040309805044094800501450701d108e0800c006c0580104440e100d200b82c01051699034411b10640f001c1d00c041101800786000c90741e90540e241c8110a4442e03045d40500712064211210040e840d07550103211010281031400d103080003030300300a9540442c5018803d0512001d10103800040d101c983d1450178613000d000396070368400b0302c8414003030100014140940000c00e1400e0004030003000e004d4504c10000d404080b410600103a1713035031100c518018552240c14050458000c070340d40c840f030390200c003280c501c03481d04620b000e030141203910444d011207022085609102943c03e0130400307610381c80d5043d401801c40d80340410300a9a42c0200d0001140714040881e00c3c402d209840070304103101e2400ca00c00260070311050f0b00c0d0103805071000b03c0e860500300d291203543c4450244400e25 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 97211052 1250 97209802 97209823
    0x20304170601081c051c0605032512080f031b0304030c061401030f1101092106060611030301090e010f060605091e060702010e120f060f010603110a0c0204060302060406051b 76
    0x2103407441e1244810f07900b091134040c02403000500355038203000903080d1810311403028005580301c20040d00c2c0d88110020302040b0342c1508000c140880300541e010000d334a800032038019481250402e0344035602e10700190b4804021010803449001d0200a000800d0b070400f41c41c41213107100c0d034028010200e1000000784410002d103c05404244c010305001d0104803415101c0c668020180740444100d52108001080b050740e0031264018401900c0150b000e11503140310b6100502240e1500340e042985400c0d94550342d010600494002c1c0d0355490903805075010941c01510304040c841d9060260660b00c20001d000c68010004a5004d40e100c007130351080030361440b9110801402d008001c1d6040042c45e400443e00c034201c8861301a00482115404107040808101840d46103050303800600e070501c0d003486540d0100380107030b00150074182003440c080482e0500c4016620022140d1500d03040031045800002c02508441d80080d4001c04001004644180e02070024500c027011403590720107603071800f241030360303240320b80c0c0c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 97212302 1250 97211052 97211057
    0x31f050c030f0105120a061d01060b120402010f0201060513050a0c0c0302190f0c0305030c0d02060f0439230306010302091803030a060509090c03070e07020304170601081c 75
    0x180188810719254104003c22000300d0f00300ca840d1003480d950a070403100341c0c0c0110803002340d091300c0a0b45198400d00818000d0300b41c00c240107050100840f08a454004040c00090500000340c039a103040d18400d60006004101c020207540c000c00ea43d0134400700038101a21203214240c10b1464003007010f40181c0c00c404e00c46516900420a465403c40d000303040e0b02807540200e4481080c1c040d40c60104942c645620041c5d07015001640c1c0d43c01498000500d00f500a18000042d90042c0d401c100c0080d640d4000140c1c030640003000860b00c100c5000780140700a002c800610002a0721001503510b00008240100582e03003000d1300c10034020405500000c0980100f455194194440700040c401400c15a00701900325002c3d417010201c445008400c0345c210380046400e00c406556800f42004103141c166404c50b006404038000d010000c0c3c5190100c1d4803496107008070083c100340c41010600c001d1080044070000d02842c200d4001040c60071003440e80f628800e10a5004c00c0c42080040210614a0b070301600c5513202c242c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 97213552 1250 97212302 97212331
    0xc01020705120f0f010f140f061e09070206010302010305060d02210307020a03050307030905090c0703140c0d030506090601050307090911090409030c031d0a05060903030405031f050c03 81
    0x1108101c03841c20104902da456000d030f948083d42c00c8000b00015042d420401e00049030b10046201a4001c450000b00140c0c80a0860020f02811100c11100160458001e482d608402d401d81c40181c43c40610344101da0390405240010442460f9000c1503450580307200341d80501c0030391586410420351220030310000c0e5010003148600361055241c650b507503413002c00400039603003042080e40005841d416990300079603840d080024203030101640000035101401c0d04a0307102c01141441c500d1190f150181083c02028001030b0100030f144856400c082d20101c4403110121344c102d802c60070005000e080140c0301d5502441400010901b51340c09001502e1203003126664203031019207040058400340603003144001c44500100442c01c1130707444500403400924001d480340c0c00400481c1c60300601080c0c00e401c0c030094078081034038003500a0751000300050445204461603a2103400b01c2c4c0019085108980c0303c1035240c465008800184504100c44088210038444108a40d594105c007410700f6110482e0f5004c40510729 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 97214802 1250 97213552 97213559
    0xc05090d0204060b07140601060903030905280f0806010902070506060913020306040809090a1416030f020705010518060106140715110421050d0c05161202010305090c010207 76
    0x5140031111941c0000c001152040e50b4800f520301c16130001109071001c0012809004200e082000201e00504944c5058940b851442e20014509840c0c4d00401703121b03030000c8003c1c0c115800c041da80d100c192258016581070f038954400790b40751840b2440c4104150740c0100b01c00092500194402d440505410001800c0603607103074402c0000720b40c0d0042c194513200008405090150303c0c10842c50384610320a0680e25542c0000008004c00414000c00d821405410b200c80c408840d09004051504410031080100742c507002040140c020f00588100c0011035440462036805025054120754094103202c000c80029040b4090141d81b181024000d81022035415500d002d03d440c3c00c8001040f201d40107c15458606040881560030348041c0b0f44003003046c40c0c01040c01d0240f600018110070f50282e45c6035200340c0c1329086541c0e10ba2140c981140308000c1c012902802c00c10b218092102143c3d4050300342c108a8159115001e15501340d0b80c4400c1a800030f450a0700141340100000b80f80b82e030390a4141c005000161a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 97216052 1250 97214802 97214809
    0x151e16060507140a020d031a0109090e030706091b0b03010b030402060a0e041a211e03070506010303080f0c04030b1308130b0417120d0222030605190c0509 68
    0x4014116904110300035801c00071414004024180b1311609901420044401140090640303002c4012400030340d902480c1d41c07005070380002c861405c44518101c04211012444c5a040c1140200c00c4080c0480c0d040100d036204109600f441c200c0c268081c40c40920a00b511480c800c81d082c04240a841288442000858054984140902036942c450b15080600440e200041010355601200d01c81d4201196642c06a1518244035000404428015902a002060f0041c0ca6030703402da540007a1660845d603500041072041c1030040f240c05581181c12078006580d41d181c01000381e401102d6403804000640080789080b0320410848048a130000030000303858450f841d00c1401120144401c07170b180d80040022000e403503103c3e44c03920003c043c440d100a48480c504450800500300c0e4a010059540066010f10b1f03208003580e051b03440f0440d0f0180b0068903034421802030b405000925141805919080d50008104040c940010f4032642028905840c0d50381d00000c1c8000f5a0410852480890401d0140b0042c601303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 97217302 1250 97216052 97216061
    0x2031902030304050402120711010b03030901030b030c040203010e070207060c08030f1312020312090613030f030f061203030b030718020702040b0603013201021005090c151e1606 78
    0x20300040690b4580755640c00043d0490740181d401d000b800c03841000f08850035810506a16884a0f400d009210380e49170100026240d01c10440b805043c580e41d0102c04810f91010070407050040c002410466503540c46e00c9010340e035418100c0751000140700c2e0071008209140f05240c010311495201180314216200c17001d8236801e042000701544103961150003d18007003040801e218003000300da80c0245507540c203e4a0803440c01000100700100680c8550288211402c8010070f45900680501d480043d04441c1481200034004c1e21201c10300460908002254001080d1110042d40d07100341c0f010003103001400141600c0f400b251007041440401e82c44922001030003500180a824030060000540d03012260005445e07070004e07000080802c00040c8ca0b4001e0000100c0141031090428054003c2c0000c441c000139500c401082c0d614440315201c001081c903180081059007118100241010081c18455070180030580050f205509086800500d200c21800480200c0c0c075041602228011020039580300d8074082c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 97218552 1250 97217302 97217353
    0x21041b0501020604030e1917100b0303030c0c03160303150509070806060f0903010f050601080c03010b0715091e03080106030c0c20090c030a0c09060203030f040302120c0601090c09030203 82
    0x4150410301c51f0307116240900802c00340c8002d01d5410b0000c03032403c1e543c601d0004000d0103000041d00d410a003040c41d90f00041030300d0b40070345003400369a038421008491500317501070282101c0008242d5141d010400d9059000758240068201500c01d109590301d04005141c2403d03160701001c00c0300710380402c1241c01c00c040100420402e5071080c61401220602107401c58212030b605007103141e621000d10429603401014a600b1940c80e4104604650501248040a20981d0001805170003140d4021164540640004402c19000782c401a4a045111824810064100340440c0040c000c0d00c0041080ca02a114801000b10380703035903003004a096641c820b02d030454903a05107818907450407045840c3c0d503544d505062003a00b8001c0800d03100d0800721b2001068a180c9202c1380c050107102402400029070002c241da521160743c4044130140d4955050607400d290040b440b120840c0d0002880740340003030740065082e04a502103101000b104003c00801c940310722113400000d505810002031542e604011001e0020070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 97219802 1250 97218552 97218559
    0x150c030c0f0309020a08150f06030d050d050a230f061009060806030a051f0f0b01140310030602040b070201110607020c100e0d0f15091106070821041b0501020604030e 73
    0x14162244146c6140000e072004041035108210208501050030b030403990780106080e401041c0210550102410a000303031650700094503960300c0050459001504614130008141d81440401c0326100c2d486154428100c0e4400180c0f00030802080781da00b0242080792920a42e03690754080e01c1d082036811901034401524669146c8074007910703440030a07000e000d03a2080c0e115140d822140c41c01013290f5902a550000c104055552800c1070800701130760000198580700e03180400c1c203aa259142c191081018500f0740014012034400700e808107055000c0002401164000d803a0500320003480e11a095032000112a000010780103c050030407281048581c85040d0003240c106503928240e80380100e18006410f8400703403456642e51181000b401030301408444440d46e80c0f0018444c012960b03c80007140240c89000b00e004000010b9250140308404054031444800100084500e2402e00303442e00d045042550b061b100f03042004400803c0705410481d410031a03034113801a0202d580e0307a4070b081d10303060f0081652a80 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 97221052 1250 97219802 97219819
    0x91303030f020c0706090b180d15050406050a0b0d050705060a0c060510090c030b01020703030f090506030a060306060e04170a0309050a060c110309060409050703090b04150c030c0f030902 82
    0x41c2240030703001821501d00f4000007404e1061a110004000800c80ea02402483c0b404200c8a40b450745406e289100d085401d64104d01800814585042074010b00d0030740030328240c0345c1018801080700e03d4001178050001c02806106c030031058420045003c2c41c0640c010480c0d40b01d0702081000342000c002401c40301846084c801e41884954964600f42e503000c95000301c00307000c100400d11005440b03111710f00740807526250800060700ca24001070345d00c4040c5d002c09004d03c070794405e00c400460720420044c4098540988075a444e82028040c40028084070b0104030341c81824081e02080341e1514901a45c0f08540240b8030046ca8002034042c042c0c0ca40c016221842010344030300c031100c04907100708245884244120700000700c012401170f000388914404500c2180d150400c1280400580e13480302075606550780c82c0381c0051070341c46491044d00204000303240144042d002504000900c0f054050010501500c0c900603c2142c0485000b2000c0314608400d1a0102e80c62115422505209078460740d40c0c148090504070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 97222302 1250 97221052 97221071
    0xe0d0504090f02090a06080a1a1012020d06270e10020906120702030d06051207170c04090c0f08060f130302010e100c0201060b030127060510050d180209130303 70
    0x40d4000f0994101b02d010806050038000041482e2161450300742c03189450250064881c00040d0707026144400b400100210401c0b40178502c00305904880e0451010802013007660b6a07043d090b40c00843c0b9403d1441d04c50f082c10906500c40040340034814241e51325901500d4240703a8000404002d4020413826900101d0600500b418182d0f0358450a019050f650001c50b180d21441112406403001900075902440707002089034030072140080c103d010764800c02180044184040001c0d4900b05122000c44d6201e400c0009034424048881098002e440011000001494441b4031490795990203803014030541039500000b8039151500c888881e000751280c800821481c80c0319500da032030a42c8074444c420b6070907940d891054915409102c1c1c0c60050906542060840d0300d00340f00e03150000700c40d1354554840020340244409007101036021a02401000b006582400b421000c01041508001c000842503450a02d980d0f02a074401c42c9606641035000b0170307610f0290ba07842c241c40016840260b003141810b03101c81104 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 97223552 1250 97222302 97222309
    0x12c0403031b09140f0a060509060d1b08090102030105060d0e10050403050c1e0c012709020418200901050403021512160e0d0201050702031608010e0d0504090f0209 72
    0x2840800c1540c0c0d040001d1303042415a2011007881c0701c246100c0c1585034030340c0c0019100c2c2d00f000e4040341c0791418120f40b90b0380400040350051280c0c40f4910000f92600410850344035038100342e280c0380722603139848114664854044508038071080c001d90340d0100050149074907140030364100500440500043c2d4004150030305100c8251042680c045003c83ca0200d034050380c2e140300708100c00d02901d034105010300000f203200b20152500811411181041025500302019029141d46020900320f8003c01518890799429540c00941040c042c0c881940c60000c3e48250b4400f032402a800c0c204c1e4074500c101d0760301c2003035400f141d40344c0e2204546505001d020b02002003d1f0362441c02c035801c00c0c0c4814200d40c0d075030781040729514842c443c0280b0090b10003c055013030180740c0e680520080c0720f1030026214861000c070607000588443c0a20030000394140305076441449861940300c0d040c0210764003480203202c1e5050a20499803610307920b0310003c0003d04140401c0000080503001105d14200200c401850310f1801c0d80072 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 97224802 1250 97223552 97223591
    0x106080c0306130e0718060302060405040e0304050303160317040206120912131a07150b040902041d07080706020a030e0d0515010f0f0e0f07021005130506012c040303 73
    0x24040c0503002117008100e14022103840802c0211003000c1004824203590004da01c5015a00801e0700803540d610510200c4d407010411900034140040403641c03a25080c0c2250062032100c10811070010320505000c0030040c0844506a000c2c5038000c00c21400e01c14243c0c020a00b0720300091071203a140c8600c4a4a164841010004011403881c10380340800c1281130044c0c4281d003a40000041c0c83c12201000501d0110348241e02d101c695204880001c6034564020000401410708001d001c3d600619002c036100c500034100182810a0300a5010b07100440c1da030f442001d41314400c9108100140e00201c2050340040e210b480c50b031120100c001c0601c4043c00180d1035003494401001c00307031181e00f0010f00040c019940d001c06010000e2070350252982d2503d0030300c071601c5011140589000d542000e804c005c20542c600038040148601d0030020104400c1c9444000500002000c51043d5a40e001c0e100c000b04e01011034203408003c003440e0030701d101c2100c84906240b240c082d00090040e02003540c0c803080c011304455449003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 97226052 1250 97224802 97224821
    0xd0c0509010f0515030c07151104090e0c01020a0209220b090102070b0a0902030a02060313020d0c140f0922051f0509010b1e0a05060403050303041a0106080c030613 72
    0x5401405a003080b0a000c814861304010ba180e803101807017001403c0040304111510b45600024221209520100c1040501310902442c10703401c0020801081c0101907610200c030075410002103462611640340107a0300c0f9010810040d4010300c414000030704040e03c240552104502c14070300782450070610380314101e9822081d40e5034916030750000381200912078400d00741c9803c034030902d400700222051540020782c2e0300c81491000303005100100000b138503051500c200e981655009042542805030a140403408244c16004e0aa0700310034001a030180c50030314100080441c24090125002c0da101c3c0203010721400c5150b607030f00d40003070905131074280060400c1c41821a59030001c1f17950b04141c8469080d503415214010b1031206603a141c41e00c41482503403501005844d078100400000101350b5803201260b0348405503000b2503003055000600000700310340000114421401440e201011400100300041c111000788036110014881c8400310301b401e40024003c40e005a4000c041c1a4003444110540703050313070140c28 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 97227302 1250 97226052 97226069
    0x30f0d02090f0909070e040c08100b03060109020a050306040f0b03030d02090f10121e02070302030304020306070504050d0b092404110301020a0504090b0402041a0a090504060b07020d0c050901 84
    0xa07420700509041c4401409030204443c80901441c000768025a80c180f248668000a2a608040380510442c001c010003d0f020200954548448007520080a414800001c0f07010b403064500018511300c540c829556107038543e5455034a035031540f070304200151001e0592584116a0340b032501100d55010802400351004140d009603e0b000c4c003504010605602d001114000d030540351458900540c484580000c000d42e520300060024441011110190246100402d2843c4001352540c2419000405940f01d18400c500300d903200d9941c90004c40f151b0046104bd190050004100c0000092907231003610303440b6900c40100d070050b5446590850503013142c520741c2c5e0211501d00c1d051106000b00c0890015159405030001c2d85481d405000050140c030491050361151542c82e800710540d0341d95034040310014414102001c3e01542d03c2e544901e43c592000081e034000c2600114002080d00b0680131344400c07107010b8404281031034000d400b0701c600c10b00350010403140c20001503000700d169601d09215078040e01080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 97228552 1250 97227302 97227307
    0x9041113060e10050d0e0a240c080402040c090503070801060807080d02151b030c03090f01050702030a18081219090303141c0c020304080d0327030908011407030f050f06060c030f0d02 80
    0x31151514101e08c2c41c4e400c1440780d0400810708800750b04042c4068103d40c0c140d900246c1c19814180843d0070034800e401c0240d050081890000b81110150031100985101d10700b42c41380196540d050aa90f9440d544090015800560202c0a081c00243c1030319808006000c5900403450030301c03001c4145910480d059242240f0200c10302034100420042ea045407240c0c44000c05c07080c00d064401a41e00e002c1c54540404011202040c0d88140341c00e035805200805008003141e066030221040e058154009144402d035002d149910034004602c200307100380071a40c06448904000f181455081c210340c0c04450f0702d1440441214804440c8079091040081c050000e501a42e2164200047c80b070138844060000c07000c0504041d00c603500c2d803010340c4501e80d05020f1903500c100440b00900d415038140c103035070384921103075440d08007201c90725450020303c00d100c4c00050f9010407408407054244e60447d0390a0f14090740050000002a2075801d22034000c0420140c440200c1e81400c82c100310001c400e030b010048188203950003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 97229802 1250 97228552 97228583
    0x1060b070309060215010905151201020307031103040b0a0f0225020108060d152c0604030206070914010f12060303050702090a1b08060609041113060e10050d0e0a 71
    0xb042d546005020b0500c05041381e08085601c8461000c0706010300301100d542c501c04519030100f040702c0c0e4104c00c800500300a03056010240703960300075001144c585c00441d080c43c0c8080c070513010500c07c40348a141d000030a415141c4505203404000c050080b5085441c80e403c201d0707407040340c03000e420b902d1031404101c0c85850740541d507200044c01e8a001601090081291400390000100c0c02c40a01880c507074629000076003038015200d800c84011107103203c5e151080b080e82841c0407411010505610890090b003c4440640b10000704031140b225600c2417030f540e4101e0310707540c015035071191481012001c2c551400c034000c1c0780e071f40b0402c8084445503401100805c1c8001034501c1181440a2215031100060300c2c10840569a5010003078444450940302d000c004105001401590300d6500791811002c01500803c00e1483c4031610340203a40c800034000d001c80b14608130009545129840700480700c00090248203001d2400c041c103503826000448841003031901c40109854520f42041900e400078043c502003040440d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 97231052 1250 97229802 97229807
    0x30c20011a0a050a05040b0a0e0c0c06010e061c020a030b070f091a0f03070306030506010f030b060d120507030909050906070f0513050f12060a0c022503030302130801060b0703 77
    0x6001d40302078040d0000010410881d620390a080c01224025140450368840c0107000944241580e00285071400c58481031202111044001d00241e200c02000c551117a601d0398403c0000d16070484100342d2250b504002c03071940d40d610319142001c00e403001c0d24403a5880d4a0303584503500d540d0121034810007c3c50140300d6400b0075a22261110041c10f00f034105030145281c80e8000c2e811485550004078002c4000400709032510320a5210350001c5401400341d50391561607000882c40074200d03100036240d1000302c6d80810041e10317001c1540f20010ba407101020b100d01040d03200a650a401a10b8180d085c020070b4007000900c1d0b612405428030a02d030400260815290a52025080c1000d480c13144040200c140088028a003070711301030342d0030790b00c00b114442240c055480000320030074518003a00c1c41394001c0a0074080d00480d41e4101e40d4090740715400380ca80c51912a800c4240a0002c001401c803284801007040011134000d070300900c0c0d030781042030981c8016500e23030300f550b401d681059000482124000034003c06040c5d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 97232302 1250 97231052 97231091
    0x30901110f040b0a0210090f030f0315090f0b030a060504031803050303070318080a0c030801050402090d170405150307030c03050108060712020408240601080412030c2001 75
    0x2020004030381040d9100903540918041c07400f4940c42d0f03100c0000c04c1079101c1d000300480c252005403203500b400200c030340f8940000e440038280d4003140401c1600f2146600e081c0680540c683e41440f005091040602d40242c02d406043c03241e00b140e0599548255841603030b2002e00c40741c002c10307019000200d541e06041c60010441000c034200e26621f981c101e4000d1000030400f200701c03500301c1140d280109114211040c0b04054032000d0000400328000001c82005050300801c404480e42c1c000d480e00c00c03081ea0389600348416485010840d03644642e14020b480000342440841c0851820b071070943c2404c04d51680f01041201042e4081e0304900c1001104100700d2550501403040200710501d4240010b514014a41e60350b100050301e03c8042c804240062141c11300c85a040c1c0d8018007152044403a80c20020784102d2000030380a100740000c4503040002426540105a10bd01456009102000217400940220300800b55588404d00704605c10744170078100b480ca802c59541d41281c81000003891000310042c40f0462 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 97233552 1250 97232302 97232321
    0x90d060510090506011722050c210c01140702090106050403061803140309010906050a0f060b040b03061504030f03170708040819021207141b15090607050105040602030901 75
    0x2c2c0c20402003099030f0341e11405484401051244282054854840000030805c601da0241640c51a41e000d0006000000408281040d410b41e110a460301c5c03241051050040f4070320740031009170710200700d16015510540000030490f80c00a41242424519030000c0ca12503800c1c1e0060f8006000420203009000d00761141c05222010b845074004002c54598016003100030881000b04484c2000c4001024450290881c161165100c0406c0002d0f01d041001c00000740490518010010703e0b10001040380f105040440707080d9420101b900d41541d80d55010018003c11170110301014507014480040041c0700410206074803407103070301c40050540150101e90f03100c4000a0000707042040b07841c10710010030725040403104041d40406440070040508074060b17280c80391103802c401180000140b1a42131186030034410940d0b0561006460000c0e007240106141800100b8609620854407014240048403c0e0010f145804006d80080e041940c0d5480706801c5540842c0c040d40c0c041d03000010080131280038810600305 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 97234802 1250 97233552 97233569
    0xf0e010e1005130308070509040e010e0d0302040e01121e05010204170114010603020f04030227010b0a0504120201030e0d09050907050705030f07020f0603090703030f0504120b060105090d060510 85
    0x15241c83d0194500442d1550400340038442070001041a035841102258940751010300180083c0e04418000d40c028441c4076400d0580d070080703496130107003103220b03000b15812070340d55060040d0a64282602c080b00c00e10718040c100c1c0c41134003160102000c9508400c5800101d07011350001616a8545400226000a190b94900035a454042c2114581c482c0055050665485180058aa805400c1340c048107100365040650310404210701c2201c0c441624620580c0340c180414800d4481e40e840d042c1f080e02c2c1c09a204908041507082c4014005113042103018480980140340c02f081011580a246003410f600d083c0810000b40340d10006c1c081400c10000c05600400b0034074010b4a404c0c0c0507182c030b6807070f030284c804102c500400000b031100a41d95110094101220001c242554034201960072580c2d500f400e100480102d010141e68001c2a8060400d960889914440d41501048203560b800707421540144954144217090100c001c6e03d0300d400d90040c1015128050001d0b0340e0418811080c41c500c1542c0c4414031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 97236052 1250 97234802 97234811
    0xc02150309070b091f030f0236010206010e040302070b03010e0a06080d09030b06120d050c0c040501150f02010f051503010e0c0d0f0c0305010203100509060909071401030f0e010e10 79
    0x5136454050f44409030140240185682c21440d1504401900c402a525026940041a0078000c02c0484000400d070261642c440484d00c031211112011200070001034a001d44c1042004006041c00d801070607600c01d2013441a09d00050710b0381085500c1c0d400a070440f00708405000304114248810b0701c206c1c000703001c0a100030441d101c1040c0000b800c9580754040145904038440c00700300e003a01d40d540f001122510400688003010158040146941c100342107012441c821004000075904041c41880e050381c80302500e0401014410000345c90140d200a5650215907030b0f800c0d2141100100c4c403400b402051040c4460103402100420542580d450070026003154001c13403c2c61590356aa16180c0c1903032079106c000001c882c01301d810b00d00c004109a90004d08154000001c004e5544e100c1022038003500c0044540303500320f071100da06000e880c181c03c0f906541a9800500140000401610601c644c80014134011402c0307038084400209949444907400c5a5a44070300c04c9030400203090202108281c880c000c200f0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 97237302 1250 97236052 97236067
    0x110604030606060f1806030c02030d0c0302120a0603031418150a02011409071502030d0507080a1a030a0204150f09050403140705030f0327060103030206061c060c0c02150309070b 78
    0x1620070b51280300d06c10915641d580c0300d1020358020300554014100c1d0003c200072801074000d01401941c06060311165090894001464801e40d40c8a14803d490301903032601c100030441403000c9072070780c005903038841e04072503a01d034103440303581d40144c09902d80310111050707519051054000790941c0c0780b401d000c01401600c50f04121401100281c45803c0350b95000045071404a1300703800364110311802c50102c1c0c0d11130031b00c41000b42ca140c020050364040c1038810410040850161000c0304000505120560326070840000d4001500d0980c01403081040300311000c4107003541c0e4100c2206140c0c11688884c1d40030751034104000a054112402c00b04020904000b58a007080399500c00f0b0300c900c9146040f0f0f540d00e1011001c100c0c0c16511044900b00c4020055140100d90000c0c56580e0352070300244011001403081c0c1c0c000807158240f141001400310b80c4c0c49491000400c141c0e0300e410140140540110802012104d0300b000340c1d48680f0411400c1030a203286584d60708100f100075052810542215140050821088 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 97238552 1250 97237302 97237337
    0x4150f0b09040807020409050303160906210902130903020114150a180b06040306090b15060d02180d0c060e0102150f0a110414090a06030c0e04110604030606060f 71
    0x154032a0340030f40415564812880020014400c1d044043c245110100030404007041d441d007508642e42290329503030003403540c44008640c8059040700c000842c0d01801010110004245c1180c0ea6580c40208040c02204042c2d0300d0700101c0b0440035041c1c006039103800d040111314400410582d001031904404a210704407210204264050ba4402c5140c051285447c030408a0301c030707074400c026146004041964880e961308021004c0e01c84d07420107583d41140384000c00d4120f03c0074000755941d0310340902580c1c01d010500600c0c1009421880c602c20a4200241c1c2c8480300d50356541d04c0d1f40100d4452800f004405041c074074014440005601c203507041d0343c82100300b241c1840c450201545d0250f40800c08034842d99411002d01c02400a0b0b40c61203202a00109000c1004071800300d0380810703c08280c8d003407a00d60761b58518201c10f036201480050102042c801d400d101500c880c500450707006002d080c0d0500621480c40100d4110750041d40240d501d503507910418440d090388249013010b5844146014104050040c410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 97239802 1250 97238552 97238569
    0x18070905060d06030b0709051009050102061816030c0e0f0105180723031807050a0e07050f030c030a060801020a0207060323010b0c0d110303040201180801020304150f0b 74
    0x3040d00c901070114041c0080320007a00200060340d8404841e034854140000040c0000015000f558401c042200440007190703c11224007040341e405a0090444d6214810030385800c42080003009030b14000c282c000d51035100c40c410214021442040381c0080c40d8a04110348201a10281100f848402203200400c140e59a21150380b11a2061a000e041a83c503022001d841500402150200c4104403520912802c11075902844c030403030031041c20320001c51361410610f440d00a64003a460784410120004c1c040d114419a02541c4041d060070f02c10b02d04482e46410000700c0d003080302c990000d0300c030000805c140011180102c80081c46500001d5040c9040828007a44a4485c1c1c01182c2c00c056840c500f6082e011000e1103051000030701511040303260750312616500302035401000e81c0c4d401d500c204031100c0c1d10203100350001030040741080080c2d415900e8542c011940d00482c0b04101c0a55075540ca00814014800e1005500680c8030320b21b262611303160040100d081c2c0f180da0b0500f0a80914003101c166058994140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 97241052 1250 97239802 97239809
    0xa0609060e0603100509070c031e020a080a02010b0d0c08010f0b0f040b040204090e0a020f0102070e010605030c0d0606020307060506060313080c0307080a02061b040b090111010e010e0309180709 85
    0x42c403039100c2d80d4000c40411000410b81c4032903031000081d024001040e800c8514413080902954400d404200071400402d002070004400c0e00050380028030000101d890080601000d070914800400c180b00c11100080d030b40700e002c460076207000b00d004800b017100d01d10034401c5544030780b0104420300c038440071180003c564200301c440e5a402030382c48400a86c00e66031641e0444c2c0203024541410000308a10090440e541d0411010481c001e41da65003507200c50b0f60000403110300700c0b0000440d4100360b81c01c0110440303040d0000350010705503080a0040340d0207161940114809014135900a545411070750400d54281c550140c0003d0050074200140079401070603810b400c0c04a604000350f0350755004240e640b9403852258020242000002080c07004105602194050140061140b1003502850740d00c01050284607500c99181e440000301700001c2d565009e06008054190810000901d08480340701480c00c0d0f3310300f03007181d5007640c0000494900034900342d03110402c40300714002540e101d0b140c20080900070200070300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 97242302 1250 97241052 97241059
    0x80d0816050d09060f05130213020403020f0d051f05070215070f110705060f07022106150105070c06020d14040506030a0203040c081603061d0606010f050d0513020a0609060e 76
    0x50401840711039004171040b210083c0c0100214540300c419901d20400081d403c03441003080d08280c20901e0228000d85068a0f0000d0008203204078200400030240340e4014116a9409074900d044803072019034155143e51407411030081160710700741100a04105001400500014581c400c0c010415070103807805c00104824281840301d007114080c1c0501d460a1940010351100c800602210401001c1020b04182803007901c3e50320341c08003521040700022003860142e2803142e015500180600720003003050a08020706062040c5041002c0d2560380300420b02d03401c03101c00f60740700a510040e582d51207803445850040b4010040d05083c1040c00144561101401150352030b600440402c0502000b0f82400780146817000485c5c1c1120b66100b01000312b02600c0c84256001c51812001d001142209a907954900c50340602500480d83d50800564280000c01c0c180003c11505201c07000c3d80c0269441960300a2100e50100c204202591040108861858014004014029600304801a0441c490590440f400c0713 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 97243552 1250 97242302 97242311
    0x801050411160507050a05091b0f0702040203042001050702030a080903070503070e0604060b04050907210609050f010b0c060c030615070b0612010605031002030a090606080d0816050d 80
    0x140ca030040c0e0090b00e00101903090402c1c400b008000300000c0328003c403081928600500f40c0d6400400c032150781d04a80420710b88c07074503011280f6456080e10040803c010482502404d1440680209040703070030423641100c0302c09850402800d28505441080b80b80002407800700d242610b6a804661554100000104840300100c0d800c0c0d6682e40078000c0201400000e0100c0703540320b584a0a1940309641581c8450240c0d1502c0340102e0182011400c81e41500c46c064507540d140e0f11a41c1f001c59022041d0b00e008c6255513070022070f8494541d2540a50310042404510100e21801c1c99080d6104c1c0a80c10f0380700314042a0f040110030100340004c20b070329902c43c0e82d1100301c0d6100d6940001144644013203080e1000c1c610070000d054800c0103201c012a0b0301640042d140d5410b20a01c000c0624201c0318140182a8150f1000c021001404145d03001190300441d800300109410190b5035400080d5802c540010545800c403001002600e68000e146650180c0003407c00c0c29000c0c00314101a109218040c800701c0703a1500c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 97244802 1250 97243552 97243571
    0xb1504050702280203030310090605030a0309030803060102010f0204090b01080c03070207030201211103091902011407060905010207060501031b12030f021509060121120507051c050901030c0c0308010504 89
    0x121640d001400f0340180603031f552490405040029017000d401549551407074410041040d00300041d030210f00c1607040e1598200705040d616070816980004141c0f1781159200c080e20345002c2c4850028200524240001041114038a0005004020000c0c000310f00014103004010742d040d40064048201ca80a0a140c0e0b80352a1103000050b141c024a0388014415081060001403100000019481105c0103419038185160005400030341d0014480040d000a4880840d0300c540e459480040100d2482008001041e41c516601c02d400e90f00f181c8bd0a80b00300307686500404c107010041024225000e80503418141c6030b400c120410320342d03202c00d400140130040840c2001c0000342c0204010710800c413208004002030301c0d1a1300b50350b0781c501c804d01545030118048031182d0039050102c000756980300d030b00002c05101400500407c88550b00518010760705413080460805003601e5181c03103400c0303250041e540d0585d5420381030005002e0f10301943c00c0004001c0c19804c248046a42710309010b055560071035010504092 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 97246052 1250 97244802 97244863
    0x61b0a050408060405030301050a06020a03080a0f0b0d210c0803190f0f050106110102070c090903030b100509010e0a030203030d0b030f0106170d0f0c0f02010c0f0b1504050702 77
    0x242d8200d5119403145500780020b1210000180d4100e802c21942c42c1d00c45030311400100d0b1100c0c21100d005000c00e84400205d140c0040c43e42004c48441c5600170001020207540d0300107584800c0205042d5055162802c030300b030a001c40c00c40d0b1900c11601509000007c600715940310005444001c148040241c001e030f40d0600001c44640110844100070321051102030804000d800080c8000c0c032500b404680700b21151181e603001802a102003640003415803280034034040508000d04a542e400300c08150352038851007500d5031803039995105054555159030b1943c10b000005066602c02c2074400340300e8a0502020001660000101c2d00070071804007000c24501840c001091501109900d0f120440d400c042d000320700060000c10381140c11030303003001300d590355022840c0035181c0c0230001c1d16030000504600c1400300403603420405000103500c180340c03590b0580056110380322801d280440c22240310500d5401d1000f4004848110341c00329004407001c215504007460b005c0c0d0342d41224000c0b0120a1420051040d02c0726 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 97247302 1250 97246052 97246057
    0x11b0602040306020d020c07090c050403170d0e031c090f06091103060c07060506040b0d12120606030f0c0806030c190306020705031b0a08040b031f090b0102070503061b0a05 76
    0x550108040d5105c0001d6004003010b9009400700708400d200f1102e0004610704180503c1c1c481c20340d50788034103260a0450316807200c0314440114140486400304240c00034148507100e01c240065007100999240c055103840e0240030820741e5036910829041000c12004952200981c04c5010342c41240016044854030701020300707048462456526004203810400178011540c000d000c520f1082c0010451a80c1c1c001c00c0104440c250909039070444818017060b070010300481c4d8080d1150906080c8030b810880e1800c00c904c00d42e00035410807000a9100c41c0c0540008002c1d01a910a00f4058202244a483c0c0040840e5890302c420440520400410010380106290f181808019580244c010355a41c140c80c1059607880c0d1140c25110441940207804203120305c8040389a00700180c1c403a041030b1809141c4200705d805908040c03c0340c4000c9800f1183d05507040b0440100000400d2941b80100d4400880000a410146290b00c01c6000c0d4101404200c0d507184038210280c00e502c0704554407520740701044401c45150 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 97248552 1250 97247302 97247309
    0xf0912070305010c17040b06010311070b160e010f0f0e011709031b061303050901110105090604030810050105040b160f0f020f04110d09110d1a09030702011b060204 72
    0x900800c1000300c2440011340025800c0c10740c5403955001403108011003804018115000f13825110708002041e50345d0b09ca034102a080e40d50340040b0504011180d2100d05902d00140c0d0150142c83c1c0c9501001042600607000c640402d00c24209100d000d0311805000d04080c090160036005c10120300303500c1d2610703030140b50f44000d4031440001d25011480c1001150717070380b507200181241541000b0301480600749c0307000407124420320412245e09960400c0b50780694480d0000951203050140302440d0454541c42449042c1c441d1984100034403403403c1905002d414943d01411506400981150038800c0b642c04c8000c0742c040358042c604880d500d41e01e802150740300401480004100324900f004200078460045050b25070f80f4001c80d95220000f2100d400c02c0111a455034814070100401d010516441c0c1e4254040c025203030049a040745994030760b00000704503814800c0116200100ca4032015011000078082551107103c00008500c2c0c000c4940000c0e011140c600b503001d100399000050301c4208191038040e0340c000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 97249802 1250 97248552 97248589
    0x302120a091401020a1d0604080d030c0e04020304230303090c1306030b090703150b090a0b040e01020c0307050705042c01020405040f09030305070801240306031407080d05040b0f09 79
    0x107405e05504014402c801d0490040700d520406050003803540b404100311001c40704040e00038011010030340d8080e00900001200702040c080a1382c4981500c1c1c4683c00150722036403040c800400035080c0c00b0b101300d2140d1902c2a0420544d4030510800ca0f4a400008203c03840036403c540100581015007003e102804040c0c000500d007407410024400700307000005859041d01c2c40340140c0c2c0701007443c01c9410004c84403086013040e80301d000807000c00c100b0390b1b50742c0c481a0200e0018201041c2415500800ca09a80c00703155908115440042c822080c49800e00c03e803006440c044806024004e1030311021446e015440e103403001e00c4040250381d2460700340254104c40080001030010b10020104860090007404080015404a0304203000240d84900c103040d0a4141c459803480c2c0ea852048220540b5640103540c0c2c500018103654040c04000304683e00e1b00320b228144e00c0301c01850b460741080010343c1000e5490b84801c090000c18001032009203907201c1903552019802810644804e8400f0024072200d04d0652a150f0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 97251052 1250 97249802 97249807
    0x3090b0c090d05010f060305060915060607020f040908090112020702090402040c09030b130b0a0c0c110a03050a060e0c120d0309020d0f03021608070b07110f0a0803030f070302120a09140102 83
    0x417015042e0000e000b128064400d0342c080ea60348819841e141d40400c2036203d81c5402020005400d0f02e40f120103014a2800904202c1c182140c3d03c0118013100c021175825240308002150b400e52941e48200401d210b11140a029800c1521a030301050380480054030003442507485155500d94184038460b213200a58000c1517203002400c0109408101010007039080e1404855000020880d401c0c07130194040e4403065a8400702454235070303160007152046000f540307030307008014200c00000303d0010000306800c2c82c0944400520071070200e0143e072504200800d03881c0180107550240b50019000b203400c0305002000e0030040780c102c541d8800078610110741c02c001091041d004010302c0c107260f400030700b003100c00010b800e24902c203940303582c01c0d581e54440741c0c03080d644503180c10400680000d42070201c2e0b03980d850f000341c40840403800c0c420004404924507080310545a00100030041c6c0060720500b010b8001c0c03240e06045252490300c488400300d034540100241d60301900e88007000f0800002890300c0d40d0b4850680004c54 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 97252302 1250 97251052 97251071
    0xa0c020a0312020606090105010206150303041e050307050f01140d0b0d0f0201030c0801080309060c150103080d0c0903020a0302090403020f0f0d090b03010509041401060803040e0402010f03090b0c090d0501 90
    0xb402d201c0001c400c81c010700c10b040000d82142820078002c0d040c0d074016002000c10342d98010505440d0080c01080b550580428040050b8038540c050030b8046070700054034100019810700007410314100c0c03182d01540c0b00e40b1100744402c2c00c0d66006000c3c0300078010340000d0b550b5070b07004142d2100c1c050306030718030b5a503003020703090b2002010b0007035803004620201d200741c0c1d043c000f02035800710884543c0001e01804206810402c111101894110014610034843c0740584001c545448502300d10040268410b842000000038240031007900c5202d03d01d5405582e041c1007245034119008145282130601000b40108485408601410300804c00d01c01081d0480c411984186004e00d100da4998000003080c1d00400c0189001140a038030300c00036a8181d41d00a8a140480e541e140c07504459461490400d075091b543e04c1c0c00104149000388000c00c0030340340502c8040038505041c40014001d80c0c1d000801802c2516102d82d40001643d10102c550704607400f4040f140d19036200380d0004808290541b0000c0c0345d51b03e80f45012 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 97253552 1250 97252302 97252313
    0x603020703030b0909030f1602090408070c33031506050417070b0708070201180b07030f02030a0e0f0301020405041e060b030702280f0506180f060c0a0c020a03 70
    0x5100c0035100740e600b4070408100200340501c080e0152002605a08140007000d000c401d0340f409000d140036a0b417030184062080b5008120300e0740081d981070b1101c1400080c1d601c00d10a044080708000d11816a01c1b41c1007075605600001001c51958002c1e07090031042d0843c0222511a401541c100031070002115802540c41e58054041e03803141c4204803511046460103080004041000402c0300c0001210314a000f00c4c1d540c4148a96200348822410f00600c036685c054664000c1c03080f00068100344158079a181c3c001d090141c080c03801400301500310350041140c801c1143e802041020800019101d2443d001319140010703000e030050b5000f503138010340b0303005014044070348034014107107180704490b41004060340305c1c010f00c01c00e0700c070494881c00540d1000201d8008545282c10345105d220310451024202040c0350b4502d844403c003e0001c4e50f5a502203c2845100e000c45141400558101d400034840d401c8030ad2007242d2110301c01480084816000700c1d858070014081e00c40110039981c02400750005a0722031401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 97254802 1250 97253552 97253557
    0x15030608030d0603020a051005071704080604050309040f0507050901080406110c0109110301060b120702031b061014010f030213080d02070e06041503062a090e0a0504031b031404060302 81
    0x140d201b440d11070000949406e100b140380d00715814035521207140c0015a181c859505c03610305815415039404020000b8506018860980a244039001030740e9164a1a01004241d4005582c1c1011f2b0318070b02400d20004540040880741c0c408001e0070910065655414110014454051510186440010b100440c3c0c0e0f4194010500944158191040010b070b102c189403c079a024058010180c10030891111a2a40ca400030340d40201248112442d000940d00b4400f1030352500e0708030115030b81c044400e101e134160602c0013500180c082042d0030038808044000090403a1411200380303092550000351058032400c85680000940070f40c500b10f5010040b061002950740700c803403040b054440300c854081902031400e8080c000b01221845410800682103440d040b00401102040c8140c04c000352807083c0704100311024054514103d502d440c01d00070b1a0108070620603070024102008030386014208030000341c10803100720b0310700d0103e25028000c0040380381c04d0f070300d0001c0c8003500030300680080303000500650700d41c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 97256052 1250 97254802 97254809
    0x5100312120e06090304050111071a071101031b03021e0c160602210f07020a0e010f0602030c07060309080c01091203270305030c07060609020c06060306040c15030608030d06 76
    0x40c104050301030803102c1500d4600c25903031590a90800c100c200440d40c03203040d21200d00c1e2084426030380040d41d100e214118a01c462900003920b1500440c0420a200e08005040c00201d02820309110360720715401400307109072200e60b001080c15404107810350f5248400e0b0780c103900070007440d203165900c0c1450144240e54212a9076900c151080c24500070443c644003040c510510b00c9289400700d6002440d0002c00000e40101075070940109080c0101c02c00340c0d550054000040c0741101243c08035505103898030400e02c005400100c25540100821041c07040c001540100311201d6140000308030f100c0d403070f00384010b02c02c43c10f91030015070800e455042800010354901090700c805440810802c2e6030050a044a001481002078003440780b00d690001003030240c401998083c40101060b8038100792551141d040b941103401250309140d0102d07065915043c00c00c41150004070880080c1490f1030b085c0d0b2945c2c0302001501a11031429102040d9042c40c1e4000d07044240a062a001600e80703031191232500100a00c481d10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 97257302 1250 97256052 97256087
    0xa0b0108160f03050a0f1103010f0b010305060102150a05060604030b0408040501020d09031a07020f0f06010302151c02180603090a02010f1107050402090d0804080601060305220605100312 82
    0x20740001c08540c0c05509208a07544040a0600203c668484000c00107900f0070584440ca503884001d00b80c0d80d03086c410710018180136400081c0c001c003807000040807036000805507410755000031012800440c0241c511640144611400f1030966962300101d801c1740101c0e4002000038039003800740130820000c14003038015100700380e08075600103040000c202c0d5180340714400500186440c1443d0f80e0103800c0e40003099031000c52401240e8514821194992514000000c81903140d0072000043c4110300c1c4c0203074200d0030840d415070344504140f083c03800e040c203006141e80c920131420360000d032480810440c44401c03040541c0013400c0c44e460b032401200582e00e07011184c0b0224000717180310310340c0c000d0ba500500400445035031100c01440c040f81041c0c10b00c0002d601c840300556011480c4024000090714110041018000d4100034004035407400002500344d403400340c0a178007819119000c480300e41c160700e81e4a01c40c0c5034200c2404030b101c0c1c49004640c1d8a0341120f03000903015402c0c0780d480100303040d001494092207000d41c9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 97258552 1250 97257302 97257343
    0xc0301081005010b0d020d09021201020c0f011a010516021e03010f090c21021f08070212120604021308071d040b04020d050f0102270d120305090a0b0108 67
    0x121050202d80c02409007605080c401d1001c514200fa10350702500f124006140d0006494610f900041d000c0c407489561122280c0d00005c4088d003084003402a28180c03403005c0000e00c9080003841050002d18028160541001300c04180c100d03e0056a002c009c03241c640180c2042d1150081c119001e00707000025003021302a41c01d020121180d450b5501c104070800d1b420904034450241480d1510071101c002130300450030044003c80840c056030b504904a03d1043d44030311249151614a0b0340274000380c100511150654220111604004002c04111074144582c0094190540e694400140090040611100d90403801c4403002c10002c0000a260003602d4040c15540080039042226144a000490300101900404d401040040c10320140740214188a00140c0702d801000e80300317142c22600041c080700c50840c0629104144405401d9840301203007804d46040541207619100c1030714980c1301e0307d9003804060f5500c0018100718801e0101d518040c1d03012034003071580e50b542c407500307035a814032b48441181a1444 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 97259802 1250 97258552 97258573
    0x905120a03090c050d0b190603080c060106020106050603040804090213080a030e130e0a0b15280504090308070818030d0218040519110d11070501050106051309090204090203060c030108 81
    0x117403614002c2070ba2102110750a81e9035000c54400c0c0c02e900946000d40c0c940c45030000710000d14403e01800e030b42142c4600078000c56143c800c0c024250340c04e5034001c81c061002041884003003002c1c1d004480c140c500c588009645d588400050010080c82603000e2580c60050008027010154070140300150203404840f1713440380c055100c20110446802c100141c15070352182c5c41c08000109518034903940898031200034150070f212180801c10078143d401c01418400d000500c090942182c01c00d40380c0c054074003500c00304055031580d68090180040608210240704440000566203810b000d17410f0b4240c070b9580252a1101045820400a90803038008041c000d2140c00c1140c03900e050a2048034818582d244000400a81e030381c001c48000d00d41804240c8128100700540038035a5103500690340c0c000030880e0842d50300d242904025003140c2d0180c00010800c00704208041000303900e00c81ea082607650f0f40100041b81603091000078014410001d0003034141c01614208608003c80c2c8003d14101ca94010613100940764 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 97261052 1250 97259802 97259809
    0x804090510210308090a020603040510110f090f03120c0102130503010207020d1509050105150102150f0115090911030103030215040209280504150b150405040905120a03090c05 77
    0xd1005104a04007002660744003c0380c4181803484c0c12482c0d01040d28002c0c100754000c2007250b1700c11203098409512141d00c014518540e8030a5030030044160b042d00d4203007460802d800200e031094841c290300ca00c2c0e403880c0c1000159014400004801c9107103003002e81e104c0d1074481c024082d400c0900690000300414400080b141410300859205690061510b10911847d07610016a81d02021059030680d90312800c00c0300144d802d116182c01541000700102e94035180f031000a10709100d407148440a03070000f00c00d008503444030010940c10f542038503030041980f002e8480d007103446021030f03440015981d06058010b0241c0800c0001141647d000b40c1c01e580b103c25582c00c3c0000348410640703000703402424001c0040e8442c8400300080c426154040c06080c000c0c0621810401039841c10703241542e80803810f0020860100305032143c03007504001a511540d40c0c0104105048440c02544a0b150180307499002c09801c0180a10071710080002c42440c064885854060040c0246001003044428800c0c0c010049260318 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 97262302 1250 97261052 97261079
    0x604051b01090e01150c05070308030406050a090b04080c0109060f05010e01050603040c090b0d05161815051509100207060807111c030221090d0c080304030c03020a0804090510 77
    0x344242c9104160783d1810410402c1e442005c17820000b0454400e00c10b9002680c04e000683c010f42c00b802e900b44c0c80b4181410030208a4a024104050161402103030030300040081e02100c0d80107801010042e1141c40c03010ba00750151004610042641d071a002d0200c520001a500550595120f02e000c101d65a070ad50040c422280b0050310094410701802c40b0801c19846030342c01c0a0198007010b8040c1490082c1c81d900c081c42d01100d2004404584035422003404480560f92900c0303554500c600c0140304041c0685910060311143d80981030140011f0142190314110820480710b102c00e01038080a900c80b1f40120003900e0b005030f405208000b40c540d0f0003181ca058840d864000d01038403040060045c0c05000711644c80248a24000902403540a00c100d9582e2600881c880e46800541c0c2002a024604504d9050900709142400700078440c110010790301003420002580d61040d41030030300c0003a44165040592070000041c40c0100400d50004000c942c0c451b030b54004500030f0303100c000c0420b841030f107840440c00c100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 97263552 1250 97262302 97262309
    0x5010302030702031801020328020606060a0e0d081e0a030b0105070218060d050613030e100801290703030c0e0f1c0c050306070f080903030709050d03110604051b0109 73
    0x140c1c818170040302c2111502210003468001401124500301c4820f4140b50444212884000c0b1420518604012660144841940810200c3e0310350301d0701519000141c040c2c0c904680ca54080c40414a900081040060490b03140c052080003540300c42948012040345a4071100207040001d0510f07078510900d50095042c5c0740520340c000e144102c01a4111b00400c43e91400401a55020750000100c0c0d003c9030b402d00030305000c2c1550744956401d500381c500707024040a540d003a002d0b0041c0314600840500c3c5602045e414152840e11240030741419813901e0032071b010404001c94200c00b846c001480360425070180d014152120b01604c40c2c228280310407041001c42040e140b9125044045114070081c00d8048a00b2000200d208401c4a180c0d262160042031034000c040b25410085800080180040717a0881811984401040000d505e5454181d01c014441c0100e4400c00b0300039102000710804040c0621074800301c0c1c0000c1030855910740b800c0e007480795a4801444840031105c0421041c004507500c03450984098 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 97264802 1250 97263552 97263557
    0xd080108060601050a0e0a0329010b04090209010c06020409140a0912080703061215110406021209060d0c0903060e010204060e0d17030c27101107090603080301030c050103020307 78
    0x142e880d07800541d9240e100700818000c2180c0a010308a0702d568281d50f42c0042c1d40503614084500071880100c090002000040d1000343d5000401080a20b21060803102501c1c0000409a00c514141005a805141c40d4800908181c00410702080a42081c1d00050280003032000900d41350b00c4002c3c071076088510400c400350001081c0003008800c18002d06030315421413542d01d0002038071507032411a5025412450400c54109420003d01c003400400c0e4083c030001d030450404403510f0640340a034060b603a07001c00b21300c40300c041c400400c0304440c1396520000d403400c15065030814030000350940001000710009010445000345008403880511505100359010744241d600e8816484a9400c02c001045400c00000c803402c03000242408545e03060710700614010000b42e5400354a54071901c0203200025402c0060400c200031407128440140c0e80c0c5105034034400020300f0902d952040801e85c050070312840789c00c0b6121107810517400208004d600001907049900030841c444c500c42d1214011010b07803200b507503640300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 97266052 1250 97264802 97264813
    0xe0108070302180108150a0f0e0f0601020d0804020414090309010212030c120408131d070201270c0f0b09180c040302090c0909070507030305070e150a05070f050601080d080108 77
    0x480d5001350406030301701404841da101d801601d00300041f800f100a4005412601d02c003101002039840c2d00303e0098012404145032102c900d82400000d5442d03c803204241c00b00900440401c05640b5503a01c90b501c01942100302c45414a441c0210940e29448200a9401481101c2801284c5000c00d8207076401000c485010528008451400c0300c90400040c000340d0307001c40b04008185840fa41d414001c401043c15019130b069011200e00660080311008100f881907905004401402000004810005404955080899410b1741c01c1c203015860240d00040459152a0300204900c0c00c10b602410000b4403c503030080301c104540390705660880007541d035030049040038007061005203026030849030300607100700d80700e41004542000181c1005081d103000300442c41c000740d10014164103008490340241d040c10580100802c04011641c2c10b2080000c881a5040100e001d4207a1841001101c0c501904220340300c03198482401c000b62030f01820b1241c84414840d0300310070000c0350700498020341240c2da00c901404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 97267302 1250 97266052 97266097
    0x7080a0207020301060b19090f030309062706121a0d0609031b03030b0406051206040b100e0a0c0206010e07090603020d06170105040302070b0c06130809100e0108070302 74
    0x40d4100030030482c2c2c19502c40c0c1d0003140c400000e50203403034508941d640c100c041100488000d4508c828542000c928407801c0c41040c0040784c0c01025a00480e02540707002d00007010310078002502e0081c040e8180c240f0000c0d07018005052680044c110b080c0480010003000281300051b40a01046c0c50140001d8228003d4a40301d0f001c2105544090101800707811b0080c041c0740000048280110705c0b0000f01c0229aa45040c1d0b90345040922036000905070960f003900d600038134480129604e40d030042c03005101c81c2d100d000044015180c098110010300d00b0080d095014240446880058000c02d41900d0041c881c5100000e800403e007400319006a015841b550881801e00700128040d5001e8448481d0054032400c002416002644880c0f83c1490307042c00014050425140c003c1c108200ca034410360b00c5c04024040940c007448041025074106d0020382d040d5010740494a4914006e02500082c07551001d10000f1a111594100c20900b03c6070000b60380e4805c0e5070395200020f90880c0140e03000e00740090304521420 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 97268552 1250 97267302 97267321
    0x60607020f06030915090105041a04050303190605060a021b0108070f03091b06021e0d0e0603060a0806070203030406110a1202160512040f05040b030606061b03070b0f0a050708 77
    0x85801040c844161040170b960040e80880550042d14000042d80d0760720100024800e9065401d642d514015480c0c1c41242480d4507819540d01014081660004250203d401640e034954040001040c010300312945034600102d005e500c801015480e400d101124a469070342562081a0607407007110703ea00d8100c015154901c2c21070003049410811100700301c015060808201010f55000d0050045a00400301c1880c10b4070641d0500000400c204041d5208180402c086600705182d042c820205440007034580c0da82c6000030b0909201a0701405450144d01c0501c01c5136907010000354465400396400740300044c4140056400c901ca401289000550034549620b040c0d200c940080071001000f13034400c1c480d1801c0ba1299070070326074079481440642200180802450006400440080008031010401d9508101c01b090710340e03400500b464810080055501d41ca8401100b40c035080b80401d40c01c513034031201d82d0300e4603d6026400351a00340780c1443e0400002c034402c01074010f551050800359140380d4a0b4803084000e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 97269802 1250 97268552 97268557
    0xf0c07050a0b011202030d090f15050d0501030b060a0803090108070f03230907080303010f0b0903070f0e01090e0607020c091e0a1b0f1b0204061206090b060607020f06 73
    0x40321680074a0007101c01003034900c1c803428060980e501d00c42281c0314440c41018942038541d100c0005011209004106604521755010115415940d40343e80790030124000b01e40034803809a007107010a26040010003849113600c2905d03c220410f66240a8075504c40f085640c0e240100200b15000580300d00019141d07521603030321484032101314100800c00c00c40c1c003e0725000d151a01d40c00404188108000c00c844040d04103c031030b004181c0040030358915414071102c1c1c00c020b402030181c4984200300003015151510100301e0070000f03020300c03000100702c40c0d21010548404a42807081c00b14282c1400501c544032070300842c403075004000d43d0b0001e0200123143c0c820b22a143c0300050005c8244c842d0503802e80001e0b030050320400d2042454100003d07101c01740005000c0c082410070516420080641e06c150740e11a00a405031071407101d0200c3c0d0b00c482c220316200040207000550804103524120030581c07020004944c01048100703100e8803c05074903589240600429008500b0080e50003c2d03e0304220581c2d0422000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 97271052 1250 97269802 97269817
    0x21501031e080c01090b0a1a03030906070c120c06030f0203060d120e1003050109050f09030703030513060f050702010b06180103111b0a0c060f050406080a1401060c02090108060f0c 79
    0x2c0b828141040511443e00311850f030781081d14040040070401810380d01d948291140445000c5402415030421000b0a5403401502e401070b0040780001a00c0040c4004144844000c1c8100341c100e0b0980c40080c0303402602d80b0000d1282c2d1003ca8200105044201040d000381c07485580c000d010406611229103c0d114107180e0081d9440601034113020040e007039114610029941040742e20049495494940b01ca406c8407001480c3d000114100c0e0b05110010b00c01004844e0003542602c1d011031942c59510240701100b029140080c4050310b8041d2030011783c126600003512036640c40d00200001e41d555014011207208051812011900d08010420700c1d601135480008441c044040c0142004001419003e02022240716540c0e6588a0009003003040b001c036204002404a41c5002101300e00c0c440c1c0b000d04980660300400041c01290030004030052501d0380405544d84003c80a0255541d680601034080003420700140e000719002000440e42c464001101801010b07401c000102e2a900d5401103480c40c0c200c000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 97272302 1250 97271052 97271063
    0x150603060f04060e0a06140f010e0108091c0309120206010b0405190e0c03040b01060f0c0b040311060705030901150b07020f0112060b09040513020d080f0d061401021501031e 76
    0x80001c04d510a0340d05000e4452298480005010390810b00c000300302c1d222122051748a11040012190240d9002900300c050ba5000e08141d03031142c41e101000d41c1410440c6101d22441c503100e4500d030403503540c184c00854601d40140c0c040441c107525070400301c0c0c54134024020403440c0c0d9002c000c02c001a05203158100900806d104141300003c1c0c445010f0884928152001c800d80c190200610045c0301d1600c1240b40100080c0c14a10810040c01d440a054408001c4001d8424000c880029051502680311f1154007056801910b4407071a098034050f02076007082e030310f204440d842d01e040110520300c01c84076481641c0c121202d003802d0040690810541a100f225414100003c184450319014003134000c05001d001c1a450540c0c40c3c07442c1206100c00ca41c0c00402080b040012a042e240c050380b24203d26034036081e00030107120b030354002402400c2060300c40c001000d21281e282c0a0b000840a000101c00700607050243c1c242da0b91580306140a101f038250a0001078400a2044420100c01642c0c080142d819441074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 97273552 1250 97272302 97272311
    0x30a0b07020c06070f0314031506070804031203050702010c020c060f090604050a0b0c0c0a210203010b130e0c1f0c05010b0604030f0b0105090106050a0e0d020910030506150603060f04 80
    0xc0001c0380f00c0c4d4000f01c500316054182c5c80850301c00c054118005d094070402090340c4c0c1e82185401c5032190250082e22040a010701c40000c0d0130000d00c078581d021140030b96006444c4500440d4400c0d4010001c03d41110348000551070031750100e00040c80491183d03003260004160a05128031050442d046901c135503403055105000b0000010151500000746004240c10203455440d080b03606007032401c06aa9841c0248202001c0c107051001180300f035100d40000a600c02003000e04030851010030b0061403065103050303000706010000520707500d06410108402281009451030a00c0e18400d001900e420102d40410300c233902840303d19054401d1040c9649140207500202e80c207080600403900e5a40a0742064440103603004c420b8041c05050191140100000d480c009060341c03501000500c0c0c0c0c06480301c03940400c0740c6400c100d40340e542e45402c12104150001c02404540c20400d52481c100d20643c44111500d008060008103e0303601741d00e9407061004064541c0c0e1543d6a858108555010043c00c071035403141c5e55 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 97274802 1250 97273552 97273573
    0xc1112060103081c11160309050a0f1d060907080c0403020d0b1807030b072007090e060708070e09040311010c030b01110c030712020a2c01060806030a0b0702 69
    0x40010600035400f90300300503520581d0300d00c0b44040d0340510790400309680c00c00210301040b11404044a00075101b281d81c180d80880e60f45411112100668081640001e024001003024035490303440000b04d60800104d4074040803140750940c50540201e4090b9070043c0908006000f4600458155622010100f2414034054036035001a0059100810580f2030344102002c200318460701202c0a072844820500408e4418a140d81d110801c05d40103100c5810040d010611680c0080c00340b41c6030141c14220825a00300c0c9481e544c004000341488600300c00c05101d16004111032a002d40400c030300075061aa105a40c581815050105003000a08120208001c1300e010380702440c828840c40d00807103600c1e50003140795802800010300030401003280901d10340000c1e83c0d0344c495990018405044138249140d0703d00d07840030b41c0000798100000754420b910282403160100c010003503c00c40b1240e44400310100c1c40c06642c071580121101035046510f540c2641c489480c103c042828041c00550000d080c0c0704032825901d2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 97276052 1250 97274802 97274839
    0x90408040e0403020c01030b01020303270a0f05060703060b0403110906130203131b0605180406080a0b0a050109020702010c2a0b03090d020d02120901091d0f010503030a0c11 76
    0x70445050700140c01898001700c40d07690501881c104060b091006509509050011010118850f540b040441c4260108564250750500c011440f55400c40b901070044812070400c6904e902e403c880c17a0b00024070300000421882850000d46050320740000214007102c040350305124801001811071640442e9503031aa0b940b01445000552140c04c1805070082481500c1ca440840000341242c050200068250284032050340001680d250040914800c0540313101030740850020400d5801c1110300307000d484080b109000d50070400500954058030104540d81e81c940f2028100d00070204020700280300941c2240210321480000c101000c21ba44890b1100380d95030b000c00b80144440d500c4021078801c0402000803103035042c00b803034003d910f0300c0c009002c01c2d030200e58009482c0e851810400742038501c081040d03400c46c3d10a140e10b101a0010a0400b03d800307a0000d03850100b440110382e00d44085110380d00102e5582400300650b810700b0016214014119501d5503007401800700c481810b44c0100300c00030075080020 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 97277302 1250 97276052 97276079
    0x1110304061406011e08060d050f1c0c15050a0605040c0306050102160f291201080129041a03060403032301030b0117100c020d020c031b09040804 64
    0xe1080d44001100905940c1c445901031000f410706041c0716072080c0400034480d11101000000305d1514165039941d5501c000102c14603c440030140c03880c815083d03140c080c503030000b898102c2c6000709640c00011042090041725140b001100003070042190003045216070340180c0100780c01113900e1001107015500c0e0008101184c407842c817018002901d5600401032540c0512483c6026410348200c1845242010740400c558003007407041c01810741c0125001c801400c0905419404c0d44048000c26a4a441020545155200038069000c1ca03520308561900b80c15100401071003007101c50004000c1d5a09034500708401032905108444c407034030b0301420500d4240c0d030900a15214610039140002c4000030441d14038159030f200e042036203014905e04014800b254814030b041c0e0444600d0400b411140c040f0440c03c81c00c1a1220036020007640c100710040e00c200350046084d0595008640c21141c10401c200100750340c852242d82c010780303907051480f0201c1d441d00f01010055801402803030410300d803a9884940c01c040b50f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 97278552 1250 97277302 97277311
    0x30f030f14060414040803041113060f03140a030905040f0608070821041802180405160f02030a08010b1305220606050a0e040f0b03030a021605010302041214011103 72
    0x4840340e5040084510b060f100c0e12418055001324074007a4501070380d64000e1480050005003a4486101c0c6d00d8100c1d9a82102011110400450501445a8801c40c45c084214a030008070f0345204200314841c078448000460f520190380640d105001c2c2ca00d04070509c0300030b100340200d088803642c8401001c601c82c20100320003001803000300000c01c401000007130150301180e0b0300d00700d201c4817050400c402c22070101c585449802c0500c0c41400143e0750701381c9039240d10b07d0f59030f0119450b0b001410307d81080314075107101650f400700400350f40782c00c03035461019401240c991103241d01103c007082940c80140300c10384c1154090b009a0414041440f070b183d40360350000700721409010491081280747e51521041c0340150180000400311810301c1c0341020080e400182c405179030b503411140070750381d20384901c1040a40c82d005009124409000e0300e0399110308110003511400804007241500c00c000e00c00080651080c0b00300c40c1154000d0303000d01680106951001642c03951100301420f25900c0d582114980542040298001c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 97279802 1250 97278552 97278581
    0x11090d02150a050d060b04030507030b060105120708040201080c030106090b0d02040b13060207141509130c03020711030a030507080715060605040302130504030503061201020d05091513030507030f030f 88
    0x4c81c8600900138060700e105070031002d850310341401304100140001800d0802d40e03a120041c00100d5807094012521406202c28042e25182a03101b030005868001304228062030007079840046544d1a2000305000b03100c00c0c1704150020742c03006000c1003802e1189001d80740348100c071940035141c9a80c0381c048101070303006600d010105060400c0c003000b038503404014400081c034040000054102040c40014118245c4049034480118000350480d195900c0030241045506051410007082011040040094009400481d021042540349044903d80081d80002c0aa07140d521a850030400d40d80c0c0c0041a00066821a03907048603031901c19110350302d4010f05000d0111075840c15101c80c9180108034680c1206880192901c3c507040a00001c20380c00ec007200d51201c003d540076194010140c0300345009100b41c4080002103443c00083c040020030105018601a4000022501984501c62071034000d03210710b000207022610412040340042c2c0542c54900800000e4100082c8040b80341783c1140c180c40019845020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 97281052 1250 97279802 97279807
    0xd050f06010f02060108030306060304050a020a0906050f040203090a03050f1201060c1505091b0324150303040b070201120b060304030c0b10080705131805010c030b0411090d02150a05 80
    0x45035900400c800c02e14002440280030a51600032100d4583c400940700900801000001409100c001c0201c1418254090301c2907158940c1d5080350401002640519440b50305050460705aa2806009a84c0195001c0c0d010f030078004116541030b07c0b42c1c0d01580201d042c01c901848807210020a2801c103900800d825101c074155080c1c645009038010402422001e034161801c428401c0c0031100003112005440c072070001c441030000c05000280750540100c1e441c15010480c0b14001c403140502e02401f8002c1d0344841780c52a000b00c600007015228007075401003070307150003080c80f1040140d072003450311041e52501002c00081e46020030380803a4071a4030448054001c140340003089410001406640e50313002d02c007100303003580c014180b618031526070a4500c91103100d0026405140100e890940c4454011046044104071508003460054080d103030008108010914209440a00b03082500a04102006d51540366203001a9207040003c00c07482c0d400181d80142c0000b81c01c0c0040d5960070b000744204402d42d12440e8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 97282302 1250 97281052 97281061
    0x60a0c110609011e02070b061003061a071b03080d02070c090509031c0b0604052b03110d05040e04020907030b1315080307050706050a020a020a0f030308070e1f050d050f 74
    0x9914460800301d50f1300d071501c1000b07650003261026880303603005001100c071030410050381c100031400341106400c4041d0881c2104009488191101c0040c030391248101c405075400200c0e403011450984c070a110103400f444040101120007a00c95004140790703482803081c201034a0b01c614112003140c0b0201c4644200b584005128407c030107809200600c1400c00d00d2041c04007400041c08208140501d2184502800d8140c046a207001088102c0c02d44604250400066001d81c40c100203200d0401400c02100a000d5041060141d0b4428001c50f0250785091802c00c08a855581c05c7c010b1141000b4078840801d03541c1c0344003000300d81c2c4500490348150109500801c001e2503640101c2162003880e4480700e2194000c200a90002da00810b810003110901e041c282c0d11600845000c0c0d0074003007000c100951000c001c0c900443c0e4468965001000d0b01e0007030f0341d201d84642d40d00c2010b8814843c8403407601d5000d03840340010035494209598104007811281341483c2480720041000d0156070050f20184207207080e01c800c10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 97283552 1250 97282302 97282331
    0x7080a0c11030c210a0f1101120c020604030f020f07091b0201020c1002090d08070b0f060409030c06020901170109021b0a03090501031109130506041d060a0c11060901 73
    0x103004107107003140030305803079115100040e01419220030b0314101807225641001901c1c20901c2541e05d2180c100408070410340d118640080720b400040505400f080e4a08500b030310b9a141407150b2007214600c2d40080c0200c0c3c07101e84081d00c1500ca480504000c40c881d040c04107000020500400300148600030021540448075444441480440d880c91001c5a1051000d0140706a001a6101065140840041c1e85981800205a0210304d40c0c8001e0031602c0b0000c0c4080401100b5031005106d206000d00380c9800391030b8001048161149200041e00040c0005050340200e81d2580c0148608201418021001c80341d100441c0f180407401d0340300e646950f0380803460f40800a0a400041410030303c044c042c00d00340c0d8066401501a00310313070089504055030b84403003000c0c1e000b0f00d00440e070317070000d0081405605181c24852103010380011070348103020307600b01501c0c0d0102e003c14003010034440090202401b220b80d290328461009144203510642002443c140354019480113200300c034042d81d06180040343c0540c0105a0b03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 97284802 1250 97283552 97283573
    0x712021b16080a0c050d050109020d0807050106060c02030309090a0f0c110c01031812020a081b010e0c031f0603020409080409060b13050402070312020a0c1a01030b0c07050307080a0c 80
    0x414980d40000d0445400501c13445500001d42d0411100c00c0e1042203507040060060107100002500010101880c0c0e05204000b0302602441d0300c200002e02c0015240d01c0100c85a1341803080003505507100384180300041c0380c140300c081d90010b40320000040303640e0580c0f461000e0751000d60300b690103d100f103014881c3c40201480403100e000c80a00742031120411101da120030944003541d010740740b041103007568000c491090000707420564014400684804040c0c01c0803260b04000f8103c80c0701344d0b1a0000705440f54034080703401100003000a016110b040f0a16840802010420300e031506c0407a95108044010b903941d100e0851101e000d062625100e600340055041250b00310f4000b001c0360101406854402150f545500b02990000e850150b15415985030a44900300e0144600e2415400800c0400e1400d901911100c07800d4000e110303941061003074400c1c80708405420b0002031301c500c0301c0d0000034002c004040e0040c0061440384c02181d142403071131b454401094101d00b1a0340c0000341f03034401160500c000da00c3c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 97286052 1250 97284802 97284809
    0x11805070b120103020118050301060b031608061509030705060a180b0301030203030412030e0919060608040b0703050705070f0c0e0601210f0e0106120204050906010e0712021b16 78
    0x2a82881c0000952000112100520000b0b041054001c100c800e80181f2010804c01030001400900c04d058807100950b480c1e8104544280f40c0e014658217400007070384208800360084602030b01c5000600c00003440901c0f5607201a52007074040c03007564000140703621010010300900d403c1b50794414100c1d45080d5220000b2403d5400800100303014401400580e8020084030101c44078000c0d445841590b6141c1901c8487e68500040c3c0d00c69a02820084c052400c14000081e040440b80308004c0796403074541c02c1d42c4134030084d14003a118040709000074418600071750040707410040c542003050400601d030780c0c1c10500441d20340c8c0c101ca0348802c00004002d032005515405030007080900f00108050000d90b0f00700c070300d1303401c0e04000100f5503101d07955030080701300d5a0300c69441c01c660f0400030712080d51107015803001c02551040481c000e508d40740c006500190007141c1507050719002084c00717019440d0f08900b26040c0c042100102005542005005e4a0401d65040078640701c11000242488000103e40a640300125a2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 97287302 1250 97286052 97286069
    0x100f0b031f060806090a14131b0605030a0e0a02130204240507061116081809060d060504061104120b0a02040b091207031b0f050d030f05071401180507 66
    0x4041c00240d410443d02c540c000802c0d60344151a40e509150000030380620008003981122005c188a520558100b40c18000c5000300b000000440703401031200c001d04018480c000000381f050001c510b280c011500050110780c00d03901110004100358000030642e08c0f0411034500600d600003010070032002d810318420800031255204581004481001521030710408900602c540e03919406021028144ca040c1d803240008112802080c0303456107407011245d0b100c500780c6600507030002944805880c2180000d40324090141c41d140d260300d1a0b548050180c00003601c11031340b81d9241e801c0760044a00e41d50141004200704152451814540e003000c02407024080c0109110500421060000200074400c42c3c4a94006403810090350120004003030078110f07280c000520641c100c4800d64140d6011080070000d80d00360503114040243e0b00d10800070208007070032004010800d002500400140104080c05041d8041c0403c0385c84210401883c2e0b00b1194150311010410a401c190b00041c00400c200c840043e05442c0d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 97288552 1250 97287302 97287361
    0x60b0f04092009271008010b0406050607020904050705220b010e031e100c02010204060914090c03070c050d0f1202091e01170c0304020f03010b18100f0b03 68
    0x40040d580148900f0b004240038241840c18600d0f2520645122070024035100d60282090422145c0b01a10200034401e460340c070b6080000d010f60a00c1c180c419a070031200c0c024003082c58000382e503003402484a0001c00940346800358410016a5403250079103e0300c1c002ea441014407103900600d910b001120381c0030003031604100e481e41c9009150784000400c072114089407e14284045044805c00d46015402050b40d440141070039030109040d0b8054003d00140c034602c4e1248440b43c4d0300d0300e01c150702c0c1842e501e124070b0780901001e000c204034940d6003009580000075842c1003900305a154445c0c51520b046c103810f80b00090076000e1041d1a180c0e21140e614449140700c80203524010b0742c100010343c601d40c11004007942e182545668a410b07030007900d110f8007840e0040785010300d0f49095060001160011141680500000701c400c0300c0c2072806129404035107800a203010003218000010703400341e00380200f04036150550080301007203c61890101c4001060000d184c00c0d940d01e014884840c0340744128034050600d0951 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 97289802 1250 97288552 97288601
    0x30201021c150b0d02040810020405040c0809030301060f0c211206031703091504060507020706090305060a090201030b0406090603020a050f01080c0a090e190e1c0c06060b0f0409 78
    0xca04a0710840d21020440c0b40c03104c1640d1050303002031207264440400741c868a101c0d0703400c0d89620340150044806c00c4500f0082e6441c0c0880c15122307820102c580329081e410410040c440301c0d00600c64221203034042d1400e594100701941e1a80704000d0011020702103803c0d80c642d4501a07035400480900c1c0c0a0304850140a002d11703503a20b054481480d20903040798000c01000251800d8410001d2202440d94140122a50b00341810400000d04040d1070510043c000c100740428400d00a4044808a136802401070099a4070002c2150003002d0f4400200e0415480c1c080720f6440c0c1c0c0c0d403405140c014066441c0000b4019180d0300c10440b014216511490054082d000b6582c0030b0307038024503141e0b80701e020346000d281d0701c0c200b00000b143c0000344c541240d505045654284090003c1c000c1070030b88030090114081054600808170703aa0795130390000720214211012203040c28268450000c40c90011b01c15000440d0703080e21403a4851190f0000c911281269201180030044e080203801071031615511249842e91903000c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 97291052 1250 97289802 97289831
    0x80711100c030309020f0409230312010302042d0e070801150509100f0303080a0f05041e022101050601020d050a0e0105070f0f030806030c1f0305070908010504030201021c 75
    0x10004006403d16980d0b04160082d0b403a1404084030145d8018401c02c5032004510702030203080e01030318041c0c2416441000c00e42512800104445008140c41c955000d2a807956003044050401103c441e546205410769010001d0005102d01942400c01e100c00325420714441156442c1208035407020201c0c0e0704003283d209200e44015140c10644000741c4d0a5084ea682c1c0050b41d100388110b561200c500d0200342d032000428164800d13900c5001380310049081c04600a07080c0d03140d0680340141d17005000380001c0003002d2451684611070b40c14a40c8003400f2041ea000310300c8a4941000c3c0d0041211030780343d450b082000f4040d81e06100300fa500c1c0d52141065410300d4018000140010b4403100e105041c01702c00074140381404240d40140d102542e00c1001b052600e502482e00a0030000c00b65405130080c42225440310311464524016194075820b5010b0184e86120a94100c01904001c1c00400c107110b90300070003207501c80c4203005051049000703800140c1e44200305400003440c0e002841901c0d1403545407174242000c504 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 97292302 1250 97291052 97291067
    0x10c020c190302100f0507080f03040b180c010e03010e030c07060207170607030b0103060803160b0c04030b060607020d0b33060d0b060408070608060f06070f0b04050a0b0408071110 79
    0x95185c42c103501c40306010300050b9840d101d44070000e49000d00c003089404086914000643c8a54070070465450a41ca810101c6042c18004619080e019003000ca07411a09500c1a03c41111007000280081940c242d030b64009400c42d4410480440c41e80c11110b401d110054040005600a10008482c0d4202c4001c1c900c1341904c0d0303213002d0189820103496198000041e886500034002401030001965034a83d5040449401011620002c403800d00c000000903001c42c407014144c07400c680d001100c0c09100d030b540b034080200a0f4884c40f000c9a10201d0107004901003400113403110306c520303070a401411f0100e0002c2000c2c09400404200d520090900e00030310441ca440d000299044c0f60250540810b16402d40000212140100e4105002603c01c4d03510004032107502049643c000c0c1000d0b208110f1503c548414411140301300d0790054185a1a290303032800288034071803c164000e0213001620007480c4640c0c1c94094a000035142070b506440042524001e0040200b04c00b4440b800846414100171003c80700a007400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 97293552 1250 97292302 97292329
    0x507020d080f0601140414010e0a0b09090a1103010303050c060a1a010503130605100504150335030c030601020c091506070c0510020a1502030403120e0a0203010c020c190302 76
    0xa0580210b80383c0e03400b402d03c1c0d0340e9441c001e46409403221745070303c030f843e0400d0b030520030045c00111300a909000909007000e07154152000c2e18021494031550341c007400403440010303006199241c0d0b580d00c0d1b00c00013000080a1406180300342e48450340d800165121600c2d0220180000c40c0181c58943c01c00c2d0710242600c0309580160082c2005c40d105d40c1c40c0203911824008600c0041e24550800e0100800140306144040a4500848041101c941070210280a000d014000107000050f558100810380c0f11300c18284408268244c174001a694142e01000740c2e40d00255070b9140c800e0400b0007032044560f01408074200c81c55003642c1d85003c924001c070790b213030116441c031720414010680015500180800d54544d40d0140c07001410402c810110034030000d50f10000302c0b0341611249503101c02e8468017021802182d018603003564407800080c40f60b605400080580140c0d0750f03910b200e858003c40050b1820b0080f00b01076007090700a001c14844010601c0014800a41355030103a03092400c09000603982c920403008036 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 97294802 1250 97293552 97293571
    0x6030402040b04020903010f0b03070909050c04020f0d0e060103020111030702010f0e0f180628060f0e040f051005010c08030a0504140708010207030e060901050a0809011d0703060507020d08 83
    0x41d48002d0115000f0f1081074640c903099400c0030b030024481400e03a04901000700c1d05030100c5103225544c0e00322008030b80c1c081c3d40c0100b42d5003100854103844e25241d00a0070509001400d803a180c6001b03421783d402154600c210486558101c6001042991b07040314001c0c0c0c041d200200954504003403980000c124034803c5404106004401144540545a11065400e080c42c0901006150000c0604440700000116405442180520742d40c4a0100c1c001c01c1c00c00072218072b210b95482442c00d082081d24001680207440c410003103401044034541d41c9600505d0540c0c0c04500e0f0001c2d80d403c0030b0f500c000051801303800190511107010072100c0090000007c681c1d100c4520b40c0000740513200d5240038070300700204403000300041c407802074082900e40040d030060599500c25180c41c3d1081a400c0c062091500898041d6408210144081d5000328090503e5961150390540006103c0c4454000f090f000e10f0001070200060780065418070802c201407050a03000b10050005011929020100500090008010801 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 97296052 1250 97294802 97294811
    0xf03030219060b120c040f180305090d06050a0506041113060c060207080408031206030c01080f2815050301090b010329041109100503030d0b0604050a03060c02060a0b0603040204 78
    0x5100b0035500c400c1c0c060700c00030b003020003100245151950f280c00341c14189200724a03080961160403440c0c898050465428080c00038010000c1e102501c850f0007054403240c008006820380000100340c0d21680d403140104d52000a45818518103000c11201c01303050200c0314010801c80ba8100d003000d141020112001450811401b01301d42c907184001c1c3c0655070000300f01d84808540424250710100250214540481402c2c4441d40e4040806940b4911020b055003c185800041100200d2072081e050380031031019858403048100f03505203040e4900b003800716010399a50f48a01c8002d2280701c0080002008120300a001c0100c0c151500044040c062100a010100c0180c80d04c1802a1005a01c0d040ca10106580c07450340c0741c00d0905602e5071030b603600c2045c420b004500010380d0316200e0381407140076550044e000303600342000d1100802c0109038051500381e2000d01404002096510130f407080015601c1000040341c0426418000382c5040c01c0a8400342c1c000341811040e16080d2691420350380d1050b0115804117 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 97297302 1250 97296052 97296103
    0x30e03091306120b010e130206091309140303071106061c0c03150533010806031908040e0c03090d0f090308070b06010e061201030209041a09010609060f030302 70
    0x300500d6107a00c10442c0420303c0c80a4800e00134080c003024121007200820b003001d0342e12035585000b6554003050096110005000409003070800c3d00032010745a4203c100010a00019100c415003c50034031340c240f4031030380000100101103034451034407003030a11503400070a442c1c18414001650413048001c4135445980e111214014000c000c21294002d6800007480d0301c42104422580010f00800c8402200d1509044034409036502c034040c50210b03503c2c0e2080c0180c1c0e00545400110390340000503140c103625208107220b2800708010910302a86c3c3d60300c681d625075034891070810206002c40cbd0007814400704481c10302c01c01141c1e50022a44003040d40161a0400c101c085800080d07940e80d41d030381c00c0500700003400304100701082807541040d80214402d0b200e030782c000c104100030001c940c403644100b1902103030b241c0c0040006007804800c1700c3d0010b110310f540100d504010301c0d1b0840f034442c0c203c601500ea6034440904201b0f14240748a102c000d4040d040e08068070504585029640301c3c151007044921960700e69102 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 97298552 1250 97297302 97297339
    0x40b0309010c0f1b0b10170109051207110103090602040b0d0203040501050a1b050c1e030c07050a05010903080d020918041e030914040b19090b0d0f030f0507060906060e0601030e0309 80
    0x44c00500148402e070384000303107c0c103401ca00800408104031001e00c1120319801c07040318070100391400d041c0c2c08669460044454001100901500c4c902211115000d10000c548442c1c0d074801307011504104440103807a172600c0e0400b41d0941e9030203090250384c145413503124168130029400c4400c90030704034103020760341e00415001ca51038440443da455011f440d400890b50760000c3d0100040012030039a0040703403a11602c0f8010041308401601c11030b408a410031a003040042c0d042d01c080c0011451030f410040c1011411804629422000c50502d401810000204400c100c00076007490100c140e80d06a140000c0456607000e0107541450040501002202d500d0141698a42e040907030100300c054158600d006200c0310050341500f007400758060207424a4900300300c0341882c1c01d68110036500480d183e4150300710754a0a944440c0e1020200080200802c000c00c0070034000e000d881180c0344580c100007002c500d840444070036070b00e018005c941014280002042e00381d00010603240040c1003240c45032800d60710706605 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 97299802 1250 97298552 97298581
    0xe0f030c0d0f020904080a18140409030c0b0403050c0709090203060a0b0433050102030315010309020102031e0703080702241305120903061e01150302040b0309010c0f1b0b 75
    0x354004a07160402040010b0800a0511f074000d03030f110f841101c280c181c80c110b005040da01940c2c807013014000ba40e80c01f0b4178103034012085042c02400d00311221001a1500707058200c0848060b8081070b000240c8003003000080227204020521102e00700b0801c1c5440e40040d44504015008070303080b54460184050560750340d4444a04030010041201030584042d0100390343c01c0010440641000c0350010004445d4008000c50f0f105205040407080c4182c80c01c00103400034000e021050741148024440c1d1042c100b910003031403003409131804040d515148640340c000e12003040101404210b41101e8900c5035a100d0380b12216440b80c4200c0d008602036690a45414a00c04104002500034840d08121283e80160340004003142c1c0e0080d015a1515950b14140d50b1034003004a6000c0d443c14130388401000400e03501e04000b0418591071a0252030150344140001c1c0d00c5d0015206540f25964074541d1400050b00702180c064106803d0502c7c41e41031181001c18070380740310050f5000c0c02220721900041e00f00c0140c0043c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 97301052 1250 97299802 97299833
    0xb03041113050f070c0302100f02041701020403060605060708030f09190b06030d0206040f031202041211040c030b180901020c03030403020d0f0203121f15030209010e0f030c0d 77
    0x401c0c510941e401d10080507000964502400c0355104022035212445113810700c8401d60540c00502040f800c100c0340d100100080c2c051182d64950a100c041802c2034503a100302803092400300050b0b00c403400c5040c00001c540719640110b1065800b04507900c00200c1c03040549610250301d03421b101c4165200010305040501c14171000c2e1112001d08400d00c2000145d00c103503400340400703500700c0d6454900000160ba8950042e203000c3c114240030761658002030708c905601030542503c1ca070f001d418107a40350b0307403001202825402154490002c0261300b90700c1c28140710f0a013135201546014403d82e0075201c0407509015200e909640f40b10841c900203245840b09404403920314810b002120b0340c0349000d00b0005e469050451203e0000f604d42142d46890301d1001094800c29203681d49015a9a110312515159007004040e114845e9950303d40002013413540326290258180c1c0c25200541c2d510703410701c00104a40c072000030042c4200c0118604e10075603100040e183c1c40440c0e09440d126a2602c0c903041c00910b000320b140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 97302158 1106 97301052 97301059
    0x703021b10090605010f270b090103060f0b030d050414180c0703080a05100603090203100501030309050f03191707060501140913020d0213020f0f0c0c190b030411 71
    0x26000c4500c009487c9000604e00704800101e0360aa030264025280309c1d5441e5240009400d1501421004480440162a011010100103003040c0134074069040c01e10103e0003005456140d21106c138580c007185d000d01c02d01034600031141d40d510750b1001c2c4081b0000380401e004514041c901e80541c0e40100520f0080c0d113411410405e0071401000030044c00d0740e042c420003c0e40d480e00562403242c2d50103540603603605102c03039081c041444243c4103810301c0180254000c034070120b22020003183c0308511590010b00184582c100001b0080d80c0c0c0035080015124529100000402404070085140309400a480044055440d2400103420766414000a074101d2402d07001203005103085854600d100d0064000182840002c08080b2210f0308044e0a80105600006070f224410500700002d040c060030880d0701034204229100f5054981800b80b040324800130010010604000c030520350b5100164014 = true := by decide +kernel

theorem cover : BRFrame.Cov 97122302 97302158 := by
  have h0 := BRFrame.cov_init 97122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 97122302 ≤ n) (h2 : n < 97302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
