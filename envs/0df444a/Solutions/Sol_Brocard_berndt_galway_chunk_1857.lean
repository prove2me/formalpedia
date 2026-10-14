-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1857
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:55:33.155887+00:00
-- url     : https://prove2.me/submissions/7ef467ab-7e69-4540-a10e-6f83f04e3c97

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 333812949 ≤ n < 333992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 333814199 1250 333812949 333812981
    0x120b01063b0303130305070e070801031202010b060f0d181a04060f060f0305061f0b0901020f010f021b07030201020309010311070f05030d06080102120402280b1306020105060f04 78
    0x81d0072030002034515000b0300e62034481e1600c81c800410411008004040091101c81241c2645207051a409080c5140511000e000050f42d0108420214400e5002c5031104000902c0b05881e0f400643c0100c0030380e007141100702003403442c002c5c80d1032001d84812200e40807940d014100701d840d440c00c1d806841d51510043c0c403c540c01e0b0f45402101840300c0f0103010b090050b04c1400d02d094000351039420b040b8588540070b0083c0440e260040342036444030102c02200410f45002103070085e9110301600040b0319003132401c425000c0701d5181c84114082200c2c0b0b500280980f00014600b486800111881146c55000c2c0303110007030160303004000b04001d550281d004a5803400c48080344030306224080c0c542d4021040c0c20340c41260150130006030340061058505c1120098580039008506002444d803207101940001340c1301900c901007404601000015014083c04408004180d01c1c100756500c0e45100019000061602402280480f0101d40688148659032060700700422421040801405200c001c194040c2000030b52 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 333815449 1250 333814199 333814307
    0x70f0f050a0b0103050109030f0807020c010e0102070b0415260601030f0e030309010c0206070306050d02060903011512060b060c2116030e090601020d0801062106120b0106 75
    0x42104000303014004c50242001051070345945c98003d0081c640c1c0040c1e0409c0c86549803d01013030399400603103182001000c1c2418507041d051000142e203030522030740c000740f644000013901003081c01065094000b410020340301e0024008a02c0c80301e0f04050040d110f0752855038200d4000404079846501310b8220a03c0355107001601546100b501821603004841410590791200441e001ca00c1d41000f140d54014011b04d4100b100b58203150020b0100404c0c198041d108001c0424884065a0700b94810302900c121042401541c40e1754a1800d04000c401040c192055468007160901604015044030b0782a0a5080a000c4080a003680910901d2a1134403268045000707110b601403049000c002425014003e49441850f00d68800c00c101017028002c15240c11904809002d0310484d4000890790305565440c200002020541c0c55410b892001d12a556444d8a041030800034100080c01c91402000c2d0242c0d142410982c1c80d0703003068500c0100c0c1c0b50003039903503014100881e000d61710701030b001c015804002d003540600e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 333816699 1250 333815449 333815453
    0x702040506030c130f0237090f29030f1b03010b0405010302070c030507081015300b130303140108072304110310080703080a080901090c0303020d14070f0f050a 70
    0x3000280a48224038100e0505c1303a2040306081040303404420140d141008c4418140380441d940d0b200e1510400c80394000c00415405100000b03901c40803100b4840d412943ca0f46004000300d5402482660040c4001542d00c41c0d0b01403101c1100d007120f060307a00000c0414505460b01c00118001d43c010b0006a0300c40345494404400140e05100f040010500f640090500240303583c83d050440d45010040c2900c10240380c030401c5051042c2e05141d5503114a00e600301c1a8940001c0c20241c074603040c5100420b600b50500802078100c40544003e0b500600903078041101c02504540309003148400c0c0900d18035548052820465003940d0348079001802020b40305407503a01140700205054844000340074a401001104010364401e941c1e4845004014030700c0200700c414610784640c1d01c035201e00c3c42024100081c5c000010030f8a07038250815100f440d440400034135019641d040c020344038422200c6000004a000295036490400c982c00e544281ea000b070a001c4040c100f991300c0707880c11158280300300da07907009691980300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 333817949 1250 333816699 333816727
    0x1902070b13030224061002031e130914070f050c0705090702030c1006050118060503060402090a080f0a050708010903080a0c02070e07020c0306070302070320120f0702040506030c130f02 81
    0x644c04908440300c00c89003006400c000000c0141c006500442d4800c0c40300210064001c0316038585040d000c0141540c030758992a2040d000d25140e00a0f000140c1450a88041c001040c0c005c03038425103442c1d0f16089000707522003048840f40b144140c01d001661100005201519040794015085a010f00480b0320301450b00035224109492046010001395803003808200030b5030403085140c00010803d48a0480c582444006860340c080034243c94051a80424040c1c5c042d00c2c0e03103c4000107804050704031150800000046560750800e44400c440c180180b07040060a1001401f81c2240726074035443e0b0044ca580d80c00c8421005041388800401103220301c038400610700c03049180c03580c05002d40c0c1e070190000050010500d85024030141007602054410001000801e5128045515a01ca210b640400740e0b074590844624000c20302020305a02c0c100010002e9200080c0c100601d4154400d9800780100d0b65141300701078039200d074180c1c500c2d044075424401480580443e44620034140140c50014180006d40c00556 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 333819199 1250 333817949 333817993
    0x70b070f0e040c021c030c020d0c02041808090406050603090705130212100303020105010608060906040c271a0408120d061a120912040b13030209040b1902070b130302 73
    0x401680000724068145c00702500010000c078040e08044c0000ca0403840000d60b10750903800c4500820181d403803040115610768200c1030000d11142101001d1175114107120400d54441d11039103110324039065000806042120540e07101d5045d401c00f070070383c00d0310300010310a0000003000c00312139081c3e0030083c2020f126402d15006010707814149214035180e04601d0b010303086a40603000201030020010030400141c0d9041020303944420f081d10080346803a400c2c0c4040da50307610454110300001b03829044070a0720080002004048554919510785800d001c00101a03180c484d80c041c401880c0c0101b032100130080144802071400f540100c1000a072596240100d1441c140135492505143c5c0000460301e400b00b1403d40c007182c11100b02405484540c86000c03807089140b141d4452a24205404101003941c202a010954025600a0401d14480c035081c54004500181255020010700e030342d0502c071102d54500d100b40c0d180707a54840242c08142c0c80d0b201c40301d45840d0040348101c007180708403d5118007240542e44d8003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 333820449 1250 333819199 333819221
    0xf0204050913050d05071112010f05010e0709060306030f081e180406051206040b100522060605070309140a030206070f11010c020607060b04020c070803030a060605070b070f0e04 78
    0x401000c0b91030316242d0b091406003e00d6104110040c40708401050040891200244086401980c6860141945800f501d10a02d6040400389080000101c3c0d41e07408028900c00c4005a0300c2c41c00658803482c0540407280103000160076000302919030302c0050a16401005000760030000d150310b514007103014000a0307010005070800f21030381040d0350810341094001c04c4060320049400004181000110540d144002080078085d0009503002c1110000321140c04405804042c20100d4204040400c2a4800503609a01312000c0d01d401ca000070b5280c46a0240c4400e66815518000c80c1c0340b03000460901002c103952030640c4101c00100000040c0e4038840206440e0b4414454040c10001d1750424650484044c41651306001c80c826000e00141d0750761302202c58090380b02600040c50600b101c00306000340600140300f0810310a003039000c0741090000020b984100c0d040d880078014940c40e0301c4222014050920000d1001c01c4400101d46424050301080d80500090301c0c14101c2012004001800e403000880a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 333821699 1250 333820449 333820471
    0x3070909031b020d030c0201050c1e0708010b0109090b0117070c05060c0910030203040f0b07090e0606090f010503192301050603040809010f0203090d03051902010b030601090f02040509 81
    0x148800c060b0028007035407039045503044516a01a0741c1e000f050140d15058001003c119a5011310011a8040e01c1601c42101144048030341a44040f455a40d100b02e10354140320717440c41803a0001030518414098814900810f961b080c140d54501501503000c0c21003d10031130b05108901100821031a5514000e41c80780749240c2d2100225152424003038244070014008032100c40c0108410385180d01d0f0700e841d6001aa00300d1500503030769520ba081c614560002c400c80140301242c15424031040b564003c828005445400901d020700d9290001001083d02c80c00041640051010220700785642c003950146a00a00d07019600c407000000340d4940080b1034804500300c800601d80a9101000100c1000242c0035000603640f00303145080c66290413440e030040500c02810081030012840030b0718428001c5c1c0b040c1c03010207030001c1010381e0a45405003040d005166201001c0310030300c1104043b03a205001c0e050f4120310103070140042c1e03402c100341e21001d0070154490401054007044006000c0d00e510800c0c1c0c3c07203000c0301c4803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 333822949 1250 333821699 333821711
    0x1003081201060e0a030302062d0c0306010906030c2c030109120e01030b0d110d06050f041e020904120c210e0603040b060d170c010b010e15030f1005030709 68
    0x26003d0807806440050034020320383c03c9000c0c00029000144190085002c07410450703c01420078602129551008003c0c40c4864240180300e6420b4520b40507601404003600c4507200c0c65110f04c2d0840c11079042c034164200041003520214811042c10051610152641e010b486040c040e82d0f0129094403c07289003142d004a0a0b90309500c10b541c03246141d0302960092030144400800c0000240b06254010809850400020400390302913076010107004100c0d5100109029a1600390b0510140c010101c0b07080d1110303a0103110103c0c200c5aa0880307080036503401040300306c007070300c03181c070394034096107071400c0403404e2054400040001c078103080c0c02e5088450069180d60110a481c410042c40b0b5034a0201040c00307003200b44288000030f42d0002c12554069400e6804101c5c0050300c0c18011440440c40750013109000340001c01001100d0190010300501c4000c0e00ca0042424100d0300307024031010092039100c082c007014008a80340751000841950070120355540a0b2015885500090800b01141d0007940d1a44d5030700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 333824199 1250 333822949 333822959
    0x41e020109151e03180611040e010e06041d0a0b090106170307050d09050a060f030b04050109050906150a030308090705030609030a021903090b0d110412050f031e031003081201 77
    0x141d0f02c403101c080398030b800c3c032013403101c1c2c0c446a0300034500a400a0903151221004960510000700f6900105490020030242d56915031800000c0700040d03030b10718020760070003030001c02d25480000fa1112040c000002402440c0080d00c0f8001010400b07050415203540310907001505020300241ca40c920340011019669800300d0b45003061402281c201c49805010b0306180401c59036407841c04c1c801c11a4514105105541d4008008070000c10ba203012440d4014542400802e9101c090303813003e13214100c80e03402c88009442d401e0a00b0b8102c075202200c00c0d4015005e18050001030321541c916504040810308130360310161140002420702d2402c4810203826800841c5082075140c0c100541c14003000b1100c3d03131303803107104c281d07200100307440c1080c00f490058500c00500183c2c1082d950f03100c5440348500d010001d842d90780780c0c10071602c02c6580140944d9627204020380d484084001004840c04041c03d108111400502e9440d03505131504002e015010b2801114000008500218014211042c0d1108141e1066040c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 333825449 1250 333824199 333824237
    0x70b04081609110406080903131409130c05121203070e0102071e03080f0c0f030a180e0a090311010204080105180d0824030f0106061106041e02010915 66
    0x82c0d40640c0b2181c0c280080701c0405140c1c0c00444042d40e030285081a00340c1e86201c0024a10b20500050721110489814002203a00041c004864505800c071440349507500e07030000340701a8903890074000d060808440b10402c03880c50000d0120089480703000694080419010b0081c0c07032a0000c0311032401043c11900901020360b4180010805041a011108002c001c0d1004141c0381c4941c900005004140020f541c4d584052070a040d078000000090480d0b407980070100007961260805603201002c03076048459500040c00207030044042d0350400e11300510300d648240d05c110203007085c82415010b00c41d81c054984100e85080c001000501035a07130005c03840f420070340350403030801b40207400d46030f0a9004180788442803a800032440703401c8910f9008015401c540740d408078060020503401340d0b03454451017a0304100900190400c000321405a00e80c0d800040b48a60404d840d01400c403002042035901e42d00b4050100d403104800003580e07006241060000341c4603651034141141148400001ca210417844036044694 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 333826699 1250 333825449 333825493
    0x41202040506090f0f04030309053a1b03030b091008060c0f0a0f0504050a1e08070501080406020d0f0f050a0f020a020c1c120f030c020a0b04020d0203070b0408 70
    0x10503124450a40743c4104c10341c00001d8080e1500d02260b040002190078940f00750801041d040d004010340304800c11010a0b2814907004800641d100030380c1c08101850444802441034201000e601d60300e000c080072448070800b00d2044001241455610702e4541c85540b10040c503944100c0501c080030010a00f0700080c81d14003100100913070318404003008200701a800c010251041003517203092000d11a004504241c9503400b454001d190044c203030f030600080494045c03d550881000c1d0782c03003c54196860b4802c0b80d0300c40e549030040a0120354000d010900007110b42d8001c041291000d05c2c00501a40b0300c1f0f02030340c140c414090b14000d0007034992041c40090103070740c8a00c4100090702202146881c2c0070b01e034041d40300d8480c200040e01c1340910411b204194580c202e5a4075065500c00400d1402e039446540140907806910020000240350002042e907540c00002d501c00d0f60354000740748005580d503584c00c01c240300c0f400604c00c81e003500941c50002105020b100c00b410280c42ca00016040001d01d0480003004048 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 333827949 1250 333826699 333826711
    0x609030317011409100305010e101b02032b0603030309110d0b06040b120303010303020a051608061308070506092113090221070503010e0f1501051605030412020405 72
    0x74562004101c150140040b00c40120b5050760b1008540c0d80303401300c1413002c9200d81e0001d0f1440d42412505030940320301040100800c040c0c26001c11191050f0030305070711203440040681015078410800da1600b40d40c02030199404403100406560041060045034050714140d40c000c0380401d80317489001d42000001400c0c20000481950440c0843e49251551142c100d00034240c5802540d685504106035151203110000c10122903088039075a503903c1c84c0003036413060111010707078082c000c49080303410f0540c84860f40380440c2c610100900d10394468100c0c0c401c104240703100071601c2103400c1140700c0000382c00f4004584620f0850014051840e215215081104500101142c3e0008100401c0d4208004100b00b030b400c1e1844003000580318240c0d0101d9682d00031400d1007250311005090100560a588400114107850047e007480a0340c0e1103031345445d580c00c030f01038981400000070b070062403445500c80c01c0a42000c4801003200c0d4142d45094031a907055030f1068010440015a0310289000d40c1401c2c046c05030400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 333829199 1250 333827949 333827987
    0x3091412030f0f10030b0601021006140f100503041b03050f0114010b0a0c0f020f1c061103061807050f040b07050c0901050d0b0c0f121806011511070f06090303 70
    0x2260139480001d0681903400004c5c480020b18000c40c4140e482002b05820034140301c14104020340c0c50740f25003410a51380d600034612030341500400c55a00d041c003900da80d100c466244c41e500c3c1141c03615079030890b0380c1c0c801d410361015042d8085000000b2036020810014408108070000440004a14481610b090142c01141142008011075000e05620011907111240c010b030340c0c0400b24202c1d10015034070054500c400e40e03120101d5149050850400800440480d04c640002c0241d100241285003a500080b603072283e00403510039070901e00c140b04086140e0b0003205460210300d4003402d04030150642d0825000481500d801007030807410406d0400c00b141c0600c2c01115030491540c0f40c00005a050800076000802c02803421000c65844400d00040d0703a004000560825120350820020042c2d07200c003150442a070340d501c0404a10602d0000c90402c3c181c4503804021200e551f010a0103a40040c4200c1d040c01c101e102d503c000013402e02c0c000307150320301074103403a03032030a0000d851800d0040021000105440842c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 333830449 1250 333829199 333829201
    0x507140301050d030e0f030a030807030b19030b04153303050705010c05011103070503040201030b0d17130305160f0906081b040212012603090603060103091412030f0f 73
    0x35607a0101103e60382941860907007a1241c000c0c01043c0e81d00e0344244816007501c06c80d4221005c00d40c21158040c400c000301c1d9000c005105040d4100b00110b100020503030071480b124801800858030305408258010701940c40300d00411041e81040044030300d18202d0b2030038100e0002d100c405440f50300007015000c80e05003900107084d40c11501c905072075210b148142c50600001c0f40b8010104074081d00300418001100804a0b20b0f86800311010307200b5402120101d0000b407901203007009034900804039a01c0203810002d1140100c240300901807140c1d000503a11079400c2d0041c0750000010348104848030302c1003140d984019155250800d200490203091700008002c50034140244504a00081c0c01454490552958131545a4000210f0000d100e0f901c0f03085d8985200400109030365090b8541e0804070342c111007492880364200c0003141d84038003608500c2ca030b05c1102000814503942c4a81c000d04030050042480100e01c484608540e4500100304900d443c05120200c204844416045100d03030344401045140042 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 333831699 1250 333830449 333830459
    0xb01170c0f0103270605011a070c03020405060a17030a030e0607140f0706020a09080d051602192c06040903021009031103040b0903060105040606050403080703030207080d0507140301 80
    0x11510300141401d0405a13a20540280300200380800f400074074103c0d0304140e801865060110140c402400782d220b0a1041452100050002e081160007141c0c00c10b034211110380c115400c10005e400040d0816a100100817004580c030008454286125080c80c80216500c805844015083e91078441c0b1f040f20607002182040f20381f0b0340106602d100561084e8105588141c1200100ea040c015000701a0082c1d10228034081016017005005003680c4c2c4940441e584000f410100300d5540c81a5008e02e0007501e03140408100508010502c02030b000c0009481009064441c00d81d911440340c80b40340b48000d001d40c41840111560410103842c0c1000058038148031108050300d020396208698020a140e02e542c3d8a40c003000c1c1740c810201c8241c1003001d0b0050b41e903200c0d581c82105080740c12030030515109009120000032a4603103403040500300c804585404d03080500e191603020751508510383c2601455000c01c002000101e20300010022528417000c0061356042c061030040c43d403801d5101000e10100304000501c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 333832949 1250 333831699 333831709
    0x60f06090b18031009050c010806090c04060c061103041b210b07031409160803031b18031f0c020105042001090b070302031908040c0b0d0b0901030b01170c 68
    0x81c4060301c2c042c0c0501c0786100704021901d89266180824000c1d8609500d1000700007010801d014900026603600b031260302e400017080002e0f14260f42400d01c40000700020022a401440343d130744e03400d0060000103119410402e45c1180f0740d208450442c0c00c1d03140ca003000008501410100c0000e054010084400c50121081c9403900e021a44000b504203000e410000300c1051080d049440a88000398068001e4100307507032555643c8800b0610041206101200450354103000000d680c410501031489902c070350100d08411900340c5c0314020300100045c06400020703203518104510071581019117149001421010010421580e62400c0740085904240900c80401c03104600301e114007400350760840c1c4182154005903511242503000380c001010200b089802e154000c00036105290b082c0c0e584119001104c5c0c070032100c0840458004060008052061001d2500d10024141200010314002000c00c4072000081040e0b00c241d00840e02d421540006102c072421000080c0c1440d40940020321402c084400050 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 333834199 1250 333832949 333832957
    0xa09020d0305030c070f030509030f0604020f1002100203091b0303070f0611040305060c0a0f1701060302070c080a140d03020f031306090213050a0c09061d0105040b0d060f06090b 78
    0x14041203004008604c074150843d040b185840d07800742200030041c1041c500a8a1500a0011640300b07000b945020b81e082c4070040b54841c07003150b00808640040c00e1200801800340035401504085200302c00700e240c00d00c4a184000c500801204004003000495071600c450f1402c20490564043c0d00306001c0040000c041000c0c20f080d0751750200000c2404106060039103064040da0740064090300c84c1e02c0900489080410080c8140c0301c951b944c002901403003c4056804034010140405581c10042c0100840351007540946001032242444140c02940e4003180d524094041c5d400351508610380c50032003d84032041140c0c041e40c040d541025420200c02c0100801d05000c0142114400c9201103401401c010a991000740c00643c014401d001c5840c89041325001094200c41c50228585014104035035203005481c1d0908071807869440c400c10300061011000d40d51400c0e024a41441010b000100d034011a00d0041e00190007041c000240d86403070000603000b200d116510000038021a60018014a0711490440d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 333835449 1250 333834199 333834203
    0x1240f0f0c0201140f0d0b031203010e070c02150306030d080c0f07140a0b0a14010509150a1a0d0b06070f020603100902040e0f061801060e0609030d030b090a09020d 72
    0x1103104075105000503184402489440704003207000049074040e004155014040e030554810080017054100c20525030b44d9080000c00140c1c464050004100c0c1c5042d00410aa10070f40d146032900c4411225030115144100340c217250040c0d0301002c0108500b6003001c04c000040c10085140140c02030800b141c0ea1680e034804c0340404c8900036000944070042c02011881030a4241c10304044403500301d12410100e000b443d00740d4100348014140450244440805182c4505039000201403203003c1c0c441d00c42042c105242c000c00260800d422840c00180c0d500c800b01d02c0c03064203207a4500c0c07a42ea480100701d0300003240c20040c0090320030b0030141302c20004509091102c07250507038150303901c43d40e9803948411040141c015a0102c99214000103001c41c000b00c403941d5803030141001403481620380d181ca500300400b5060b1076080b02d24101e5400e0040000c3c2c0d1054141c0240340e0780c00b401c020724041d000c01c0030070705041040e0f40ea4004039444106c5044241455914140d00c040d10510811008105500158981c19030480c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 333836699 1250 333835449 333835457
    0x41d0103031e0512010605040f0902040605090405041a0403120b030f0d0c2102010c030f180b060d080d0c080603060f01150509130506030d0e030703080a02120301240f0f 74
    0x80003540e103010f541241d003001d44004011059681d18000240650721500608040400890300001c95500e00e009032021f680240d00e1b26810414080140402040700500035184e4800030039901100708268040c0b140598020340d2581803400055451005031764042ea41e00b406070740000740c62103010502140c0020608828134054003038214a08000712200407140c20062400c3c8801070b240e080303580540c8640160401e948040c448040401078050444086c5840c00c6481031a1034828000035401d000802e520031070080040b21100038a450b003d0141c2c001c01400d510059881e400c00415070342154400342d2000d0110700a100300e1406101c01604071034184150f0007180188402d00b0801c50003103040e42c00b50b450291800041c120319500200140c030781640c1c10b40c02400ba40802c2466544904440561a54054010300b02645155103041050340108810411030007020501281035448070700840c024880e043c0a858042c3c00c1c001c5d8907196030110f000c80c2040c060103240c0c02c408160405801043c8452a0070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 333837949 1250 333836699 333836747
    0x180604060c0315120b0106050901051606020409090623010b070305070f0218040311010b01051e1e0a030c050909010608130605240d0f15140c041d010303 67
    0x800781c0140c14908030f074480303071071a00c580401c420801e0400041d030a03018292180c8540d0381d40c001541c00b4455014501d0003e4010000d0b0501e20740551541940c1e01e100f94001450a55030301030010480d0a4184111850b5890746c5d644440d0f01d6045808400300d201415001c0910752405440300050300c101e0200a00340440414500113000800b030404090a40181c551003c02440010341d03800103000f00c0c0d00300c0126618403800660080e05100e04102403906858003807914410301310b4508620568003d80e03061210400201e400e0103880c1d02002c9200154211580d103818840750007800744e42c000c001c9102000030a1142c400c43c0d40d00d08602d6030465000c0c5c11300d44075030344038441c1d071207001c904191001e440c00341000140654054482c1700355040d02412240d00e542002d0000821502d800d00c51000b40280c0e000c4a800d1020460380c1d0000c0c0003040c0c603001e001600441001c5826080741040b1030480c1b51280c041800c10080303d40854140407580e00a0605140398116600a40300384994410f1541b0040d00348 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 333839199 1250 333837949 333837971
    0x6090f2a11011e020309010c020c030c010309050f0111070c090902060d0504060f0c052101030f0b07051315030f0b3102040e010f080a03020d141603020106050918060406 74
    0x1d40b190103406403000c0e26107448840c00f9140c20296200381c8021110750300c3d0950b2000710600c041044c0b22040c0000300500404280c000c0114003416402c80190b6150094900c6404501024401c00c500d81c4046840503464410381e0900901d5800740c0d07030041c1d0300d203820071580c20011b0742e80ca001c0318480d0400d000001a507444d035007041c0000f0f25280680c0500c41c0e00c0c040c01d801c4015004800380540d00100c2c86a00418040e001901802c100d007840001c1c00b03d8000420080003a1503266081d070701003c40e10b011800c28050004002d1101d81c00e1713014400401c01c2c1d500307100c1e00a0b818080c080002c410107206001c6800c04102045400c4080d07a04240e08000d0f01c00b044014042d1803005160465440c00b055469544038020000b00c0700080c442c141c49040003000001e104000803a00320b00f0f03103030550003800c036010804c0005d03907030140b010312610040d01c000c0190445900c060f002117496540039030f00010b201e80c2000c080c03240d0725a002d421040c10140c004a0340c0c2807000700040440e84254405804901181c00b8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 333840449 1250 333839199 333839201
    0x3110f0d26010e010e0106080903090d110618040515090a0e1c0906030b27060303090d0506060a0e04080a1d06070501020c07060315030818060c060702010b18010b0c0a050106090f2a1101 81
    0x2c00c514de5408100020706030821004001043c1c1131481c11070f020401e548039000c0a0806e0708030555419003000390320000a048841c903600c143e4a0640c076005503000c820018052842c42d00c5c3c00340400d000b0400d065414401503501d481001000a02030b590f8071010000c001a50900d03042650718410607640c031000290041d10284180c854101d005810444084e0b60b03460880e4540a044588900604603403000103518041d10b42c030301c3d0003281c1050341e1500e0101040c2084412440b680383d002d01c18251945012443d4548000515449028100050712900510582030400115504c60020142460b041500003c0380c00340c11030803a82e200800b180e4030700440700b00c80c02190801c07000c01d52116003c90b02d120887d10100e2070078891103003980208030301c4001d00c08010f040781c011800c21400154190051000441c4800104520390b09601150380041c102c1c2d5415095070701940041201688882e01d040403040540140c418418800103a07081d0a62803c070001d0440041640d80000c1280c402c031210424442 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 333841699 1250 333840449 333840473
    0x1609090902062a100212130f021207031e060b010c0503030a0c09080109031107121a070201090501090311070e010e15120303070203040303110f0d26010e010e0106080903090d 76
    0x185810b484c02070a1940184009400502202041d0040203000444207001e44034000c41c0345a0120020044111035001d001e40b01545209104103840b640e5804000714400b0382d6a0b104201e0b801d182c80c02e41d03400520f402000d5460f00e0302c225041c0210100d026000600200589a01c00908140080c0f5610700d100b0890340170315280d00c15400b80d440c007413000c0c080c1507100014010049001c0d04484940f50707036001141c4015065407000e8410300f411182907000383d0b00e0080d29900014a44000300c2c042000307880702421603045043c100c0211b44541003080c140142488a8001044001301d80095580740040703005820800610700c62505650604503581e6070703a03001c243c400550001084988034030f0030960103035480d80203010540219130000360310f52407034100181d01c12141c00340c40d028000c2e80880e41c00980d1030081c5450354120200300c40e1403011071400d0004496008105103ca04601540340c929060103079503068100c0d00c00c1164640030041c01110000c22202005000d13a427224441107141003001036225 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 333842949 1250 333841699 333841777
    0xf030f110d090605250c02011403090709231b1903050615040612110d0f090b0c040608010e091005130203012d020c1005160909090206 59
    0x21000c2034600074084258080d06885203d00010089501c8071003001142c0e102c0410780c0828502420506130380c02e80308501040486206041c94100d04000301c810001d150000c40e40021141d100c2e40382009007c03100d0141e451084980c0b20054400c50030f81c00c0001c81103500414444802c020008088407044a000445458000465041400c13042d4030304010054081514840e100e0500900c1c231846240300c030801c079000c032500c503200d2031040b03102030902d900504200220071080010922245403d01041d02a01d000c500003030600092100452418100d43d101c0544200180c81007880b05004c815003020080703041d140c0c40d030640c50465031600004c910346400407050241c0f0f10b091400780240040c4142003200703028800c400a1141c4003c2c1c142400c1000300c0d4100c49440351009a286071031306207441d4002c0000c084420161040b821103205000c003a6442a00d410103200d05114690310b4a5612484000c042d0681c3c51060044500f540c0004070389018510461804003c4e07000c01d0050040f59424000c4042 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 333844199 1250 333842949 333842981
    0x20a050f0f060f0c16030501050907240e060d0903080f040807081c1d060601080709090e01060801142a03060f01031503140f0304050901060302090d0515041709010f030f 74
    0x107a0215040c0032170300051000b168550300748004100b82000200d0755600b950030140c074889046d04885031018030420119520000e2045054079005680c071460010002d01d030031241c0100f003122032450001d0900900400c40108440194140310024081c5401c403884650040c00140e181c100f44541c6c0000b240404613020515407401000c00d01b215a80107a40025911107825112550341e40001500c3c400c03021507403840011a0040d0501044005512440740407010100000e40d5585a285c1d171800c588421280c4424070703c0704000c004090301100b021075101d0030b04c1003219041d08096074052515000240c007480c0710318100c3d622040300d40d12950107020180240707843d140c1c0c4d49a0303d0405402000d8140440e000501980040d00b00000700001241c049510107803c2d9101c40c1e2030003100710001d40112407615440803680d0000000314104210f4101400c82500c100191401c2038541080341c0320f01d410310902e2050090201c602d1070380e0800d0346859410540d060200b02441c14025034002403100440d41d071265 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 333845449 1250 333844199 333844213
    0x40c1701050f0109090b16120e03130f030f0204050403030b0414040b0709121713090b03160501170a27060c0206101203200109020a050f0f060f0c 64
    0x800542180d80101000942070380580d803920108015a00e02403c054102801d0001003099440b0070303034034022a90ba03540390400011002c000c1c0f9509440d00a4820a5560701c04900c980954080b14808002811211290801c2c1c914640d5000090101110080c0c483d942c2d4000080605000750050500618000d00c10460707446030402c200000c2c8002c0d030f02551905041000a01050f010718881021344030303020303040500d101d019650411003c4c204440b4001c4604248038100303407103200e10485009444200300104075075818000340761801100314424101145c9a07001044666000342c1c031500b104d0800311a10341d80c2d079030708610030b00074025904181c1440c40903000c1821405042c49012804144150000d01000c07403420012a980d0342c05548514800c0b403080ea04016007401400740e10b0f24140700c3e06048507091014028040b40c1440d0242c00c81640c1d4452142d942149000c01080020305003c0b10300c403146020840c0410b94400d00c05069901403a00000c0e000c441c0c5004000f80e4001c207140071304403442 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 333846699 1250 333845449 333845489
    0x3060e011b020f060708060604170c06040e010608060105030114010e0a0f120209011202100c0302100504030c060f050c0d090206040807030c080d0302160807110a0e09100e07030605040c 81
    0xd140e030f001900006a01424000c503404e03a1164003101c0c06000000e00d03203410582801c1106001c04955600c182d11403007040468880e644891000e04000c080b44055410130303603d400009084040000d0403036041010030001401b540d210310880301d1041c0800c0c81d20f8072400ca51140424801c003003c2d00724228089040400140100d12044207801d2503200b540c0c070000d0380e666001c0f9450203c0c5449c0c002580706031414040d4040d603120b51101340c507160292045501c4481034041c00b408594095405a0001c0c001915500034400140104c0c0107143c1016010003a529085038028200d002c0c903801e10f035540d911a8840c1c0103640d1000c0035600a842d001f010f40c2c80f02907407403808400c0c3c058107229034110f500483c0302c518080b500034400c0e40c01c3e1a1000401a0440d0141e07602c10096a115620840e040814003415100c261210032840014026044120b000c9081c4a0031003850401c04201d26601181030445045841001050540807254414008500d540341c078503001000c00a250448644a5103817641c80803 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 333847949 1250 333846699 333846703
    0xf030513030503040f23010f05040b0a05251a070908100903030c020f03070320011d1902030307262704020f090909100c020309040b061303060e011b02 66
    0x440b00017041245040340d4540c13002603510401c5501031602030181140440740e500401035903110b0f903414903005250130307110390380080b640e0040031a4200103040820070b403c10706420444100080c6200d8003100014440307689882225807049150740c1c0b15a007040204c0c126a0003005211f0180103c5010741d054503400c0b0348800000c0642c50019030001e828202d01401090000c103810400d6180c54015600d84201600c080e00d161203192002c5070400d00e0040c1c0040899000e101d901a070b42003003c0c01c22802d1040c84540c40c9428581402801e8010900b8050b000507580042143c0c02594014620a001c41c03444c05880d0000d401b48236240e1003801d0000d40721041c42480c031180307510140861500c645994081c42444124050401060001c2108000c000352500c0d050001d20340c04214102201e590b41e00d5010342c1810780b03910402e0b01015910101e02c0810030f15050040000c074841c2034441e035051629250000814425030711016210325a03a41c060720b03486000390400103814041c1c0f205a41341c55000030b0029 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 333849199 1250 333847949 333847957
    0x50a1809020f1c050c01030504120c150c0e0f12071a07060c0f080f01050109030618060c0c061a030a0318050303040e0f0a0509070612090606120209150d0f030513030503 74
    0x12003a005e0b01d00f80950560203441401c0c0160b410011142c440b154800081e41c80d031282603070030388040143c41007004664405000799040b811465031582804146981030000c06144841411300c11003c1030004000d149002401c541150f01c850000012001d107442c24244d00d20406401800d442d0520640002c4542c018249061000441d40c410529039110041c04900d8042802180c2c0000d680301420400318009812030603071105034580e10000a074840d5070709011030f40011030840105a0520244060041d148641400f0702030140248180f0102580000e4894502e130400809000261100080911042110001604014040f65511902c41c0103140380950b0864254820110420001d050317500315015680c012a00800101040c90401c0c0f42950302c5030b01c407021290340b83e0750380d8008070100e40c1900461b8002c00c03150512400c540464014400014401080008500c1c4444040380c459110402401c60098002160f02000241407404803501c1c420b0310354010f04c00c502100080107020005c0024 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 333850449 1250 333849199 333849203
    0x7050c12010203070f0507050319031506030e060708090f06040f020418050705131404061b0503040c090209010e090a0b041a13020c0309060705010c09050a1809020f1c 73
    0x29906a454800301900b030388411500007000402100c01d0300c03c001e008030302906506214005527414144188a044090b45100342000000303900c60111320500320b81600310360003924143c6402d12040f0554400f007030b900c00e406001207080091a800007800a6014442d1450303c034043c10030f481d403078145401d0681da80c40350144242d10a40c540040300040c40001c00c944a01e05034000040c01c02c080ca031034204401071107580a54141c094440301d018004900c0642030f144100d104800001d07080148414240282030307500305007000d0120800c280004182d03881211f200300e40300c1d20f9015964044140040380c0d400c41c603001c090313004421001070002510041e00310f00c1d0f000c0800e580c03c1000e480016004c100408003144180c0d080710180d0004088039480f83c0007046100750b98011680741c90f0000300030270441d601007502916680d40d40d03080640565448801c5800070709049801c0c56410b402c00c0270310085a2005081352015641d90aa11411900d4501886d03068500080c109485003001da010340090500543d01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 333851699 1250 333850449 333850459
    0xe12090d0203060f0a050f06010225170a05010e0313510206011a03061203030f0103210905190b030a020a090518070f050c010518010c020111090d03050408010207050c 73
    0x1447c40340c040011148207010590081541101425245075114201c0844140340c460a2401203904002809282d80301483c00c0b008000c6280c1608106003100c10041c4a0000381d0010807010444034045c003501c800b5250b4074110380c41c1c0b100c0000e008401200b5100158000349076900070211544120b03900ca0866520300d40c031143c0d0007911119040b42c0b9200240101c0203019501207241d104425131401440c0c3c00309000e4021803c9a40d2400c1582c43e40e00111206020034602ea80144108642c13021107000002c5890301542c1e80d034034000005442c1e00720b24011140207582500400d010000d000d2000401400030218903070b502e0030505800001303036100c01542408138002d4800002c0d0360500c2c0458889051100441a5103034441880446600c00e00310054400c020041c00130b580184001c0c401ca60049550510b809004d895182d11182502c40161190040d649800c2116010900d4a400c07100c6038001111080580101480e017502c081c01b99412085003036201140000c2041030000fa0146100b1003115 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 333852949 1250 333851699 333851701
    0x30506010e03060c0409020906040302030604080c190c060804060b0a03060204061116091112070905120a0c060819020d15270b013501090e12090d0203060f0a05 70
    0x10b05541d110700b40c0e843c0c5035581d801c0008000c41c8525901810901c40b000740001d15065881e00005c0c506a01034030185d130000000614100c00030010059407000fa544258414818501038807508244101881000c0c14089844002001c1005952203080300100050403100020344a040000083d00580030700408102092141c40c4000300004a030000914a00f2803500e000c0d0900303040e040500714102184c01c6280701400840c20001e60085414840c003416039410704040c4c60310b001c10402c40d40003413000c2c9103034018466040c0824449081c0001780d4139142440d440c41c0d121800d04142d00003e0300740c10301c242c1e4800300b41320000c0c1c03407260000c8120b0440810300344a01519554030030644500c10501e07104641c000d0b41c0b0000b1040c0a904808410b0605040a0344104100c0a103596805d604c416180d0340030440600a40c1120303041035100703001d080454401c010403418401d05640e038208101500078030079804202c0b910199503280e4410703030455000d000d6600d542030080c5490002c800c03c4d20a0480365017400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 333854199 1250 333852949 333852977
    0x40519032a0215090927030f070b010e0106020d0f0e130e07050f011704020604030209131a091b030c0301110c010507020d08010b1b06160327030f021c03050601 70
    0xd0113451401da0028090215511414028200c1092054288114242c00e64461442d1320041c00a030404502e03084400340c3d41c240700e281c06d415491058100902d00c2c150361005107c4070303500080314405810f56081c0441680c00c03000e81580c441594102c0164007046d0001410303421030058007ca9103072070258044034402d0703445100300034413071003802030090020f514003566101998482c114640c0150001e0304c05403419850345c002c111032040440c1c10751403d030703002111203080040790f024542c525424a480b04039642004204252079600300c650440203c1080e05540805035018058104590002002004401034200101903107070040034015116502c1c040018009900200c0c08140300100c40d66940001d0b805c01c3c00e0300210360060144000d203040158039100f50198100007d0b806140d84007000f0f55518101c100c02002c0d9400d1050a8601510540c0c4030081c2d070503a16418201298141013a88042001d07400c100d291900384103050485c0c8140c83c5420444a406501c4240503000a90b6034110524007c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 333855449 1250 333854199 333854239
    0x20306013b0f0709091d0606030a020a090f020412062f03010b0c1015150306030f03050307360b03040b0606130b0d05011706040519032a02 61
    0x400d40000c20903048001400104040b805942c854054140420800c2e12840c00d0021030395000c3d40520000080d4120300126001000400d6100c90110300921003c1544da001ca540c0920600c681c03105142c545000c009481080d805581c050b24400c0708040c24010300d82050030203041c0046c0807404083d020008910701480501603041170754403030360000e85140d20780400b12025a110451103c000c0c015002145d8220a460080d00c5007000c8628814044e14144803061506012010203070041c50329011080000401c480540e00c5042c1e09820300e142c50b942c6509065a810700a0362104030550340b40c1d1108400c45c3e41c08800032651481d071000c00c02400d5110710341d03029103101c1501d014208011500010303a180ca4a4401803400303000014485c0d03007107966400650321036003010341e241761820744aa0041c4045110399690105260b400001031181c2d06080d20703940e4464038051042e059080d085401142854040d01c2c60a402c4400d162804040403110032100e2040c00d4a528100d00c10241c40d0b001078801100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 333856699 1250 333855449 333855539
    0x90215040519030f20030f01051b040305070b071b0b0a0e0121090227011e030803070e0d0f0b1501020105011409060a1508150409150b040902030601 65
    0x805801c1850204260302c4d4440d40f580a5008800c40c80c0d080c0c5c1c00d1481c50348062081c2c05200403000004501414004001103076403040240d10740d00d400e41448100301103031000031000204d071500041d5030b030345070980c1c1400000c0340c00041c1001c5003010341030310010310140c2d440d00800c1c6c1d000c215502e16040030a54801120034030441d46050108080341c50501c04191003d60260b01030300c0c4002d040407030140d03c601001e0b02c8090014a04220f030010080108000000388610086000c850710819140c42e0856403103400d0741c0005000b074402c0218203811160b031070712105040666540c003c0d5a60200008500d018510300c0d00449002a041c51001e81d280d9140d40140a034074140c500000440c070100c022001400184200101107035401100f1501c0050b4050761139074640741c1041c0f180d807500c2e06031520943c1c9455401e101704039280154074041c00070340800c881c10b5503821058910f40011843c05400700025004c4c0001c410065450b0040000008815040407003408103011514071090313250703604814034184203103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 333857949 1250 333856699 333856703
    0x20d0e0a121101110d0e0114030606040b0a0903020a0b04061706031020030a060e18030f090d050d030507030605040506211006030507061d101209021504051903 70
    0x400c55501c001035940d8600d54540300c01031610b60f0b10590b125518605d40929580601d0204482124050031940e021703000143c11400038081038a9070500e4001308010788034900c40c1c0320740f407000400c1c1d01c0521449400c0c500c00464000704428107841d15403c505001d648140310b00c1002c1604000c8400504e1780041c1200d100f40c00040c0900050707440b00703e2782d801401e00c0410b50310354005003529400203200d20b00702035801140e9410000995a0604000202051024101100c0c0c5420720030740604c04d5000004450b03000491454181d06e0b01800c00104000044056005200d800744480c4114451342c1944018170071405a601403110300d9844080c081220340554040e0f400c208070004140d035844505000382e80e9a6545130490311082d041940b00320460303030103800c00c8420341c0000c401040030540c004146490b1030049800b070f0000c4e00410340000c23540c0c1c070b00203e40014020341c103988a4084019501006645802800042c1110250001103510b0b83c05401554802c0603a10021030400706501240c07000d4039 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 333859199 1250 333857949 333857969
    0x1908070207031203020904060821182101050414100c1d060c0303040807030f0306050918160810110909151c08030412080c07140304050a06020d0e0a 65
    0x15045843d09199000380100c000c0605808100250507a107a501c195030040c210b55019007004140c0712155030840e86400792542c1c240005106403201100c3c694085000c8560403201020049805c0d427010500149005528483c5c0d440e0100b00814014404104582c10841720107a81d01c041e4610000d0040b0b507107000c4001c0c0040c3c2071600018214600030300c4440041c0006181e5400c00750180c00140ca503600c2160304481c0000d012444404043e00010245484d44c5a0301341440158102004144203410041c07000003400f494202240c9803000a010035240d0724110110f0f0325600e80c40e40d42e515035615400d44186005072400c2c10801814003100d0958100e014001c3c44020a5150306074148500c03445d1494040d40100c40305000010300c076075148a00c0d82c0130f10500c0010341700d00d0a4140082c0040c0390b100c101c07040c00302c0300d000c00207242c0a1004840e0420b0b40884174a0008500f904d1035840c40c007683d00840d400c04003075140460346540004000d20141c0860341c484400b4000381e824413080c0d114a00c100c0901c5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 333860449 1250 333859199 333859213
    0x109020114032a071e0605010e06090703020d0b0a060309020109090912050307021006090506121203010b070807140f0f0f030d0b03030d050f01051212030a1808040b19080702 76
    0x12110400452146406450150900145803180001d001a8138854581784220850800402059000d900e00401200c3e02d6a2220320341100410101d550050081c800c05500140c4c3d4100003520380d001840c07804016103403814185e204d45025006100c0b0300c000f0781c0442c0b14401c0c0068111034078020382004079405044c10001c0840314905031840d400c050100d01c1540240d4282ca40c00c43d85500c1104010b0074a100c021459060501c2440702c0014448881c0d299a042407442108080c000421207044802d42003400b96205c015042103005070003007140007040210000592550f4250008542441004600541d1a05d59007001c10700e44c0c40d030004502c11203582061210500b54813041e402042c41000c00f509991030611420f0814084440464094409003050303c0144924100794041200034480c3c10010b0001c05140e0496440a000c010000b1344100d4540140070201d0a002c0300403e402c50340b00000c5900e030b5860300e041540b00c0d003224040054a04c07110803d00c4030035202e0080b59001300c0c0160060040307 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 333861699 1250 333860449 333860491
    0xa09171921030c0305090f0706080703020403050f0d0305090304150507021305130c05030102040b03040b0402060705100b090601080601050d090c0503030f0405030c060301230312070302010902011403 87
    0x1000c1030341006a401021410301981c1007040c10020000450103680d00060741451400090112100504911070660002e040000c40c1400000c0c1c0c401901d15509040d4030a95a0600480c007911440e0070041081c09403940da003410341d10000d0b206032181d8040e1401d0000e0380e138801003580d40340640d2240500c000c2d10507850080c032a010b0401002d80c940003400e94100360210681c400c050307400c03d484009481003a41521820720038404d9042024200072030003507103018649403d0304400c0c00050400f821070942e5001040865403100221090316a008007076070040900380341c40400034544e1090341c1d0300814440c000510698425400640b05031030503101c0c0360170702a0010f034441c0184070344001111f0041c0ca42e880032955076001c102500c0341d080003403482a9114182824541415250507846005034800d00040c41241291003145055001459505516000c180700180c9404038107510060488000203000c2c0505a064014650f40d034001c0e02d59440341e025840c403c19107031004371250110f4140c0c00c1c0e100c540d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 333862949 1250 333861699 333861733
    0x1401080c18010201141f170c0111160b04060912080f0703030b031b010306080d0e060d060509010303030504050c030a02150a180e0f101802090102011d030a0917 70
    0x24020043c07000150a030320070303802e40320f5450b81610b032030103406940306400c51044150060000500900100418503000105c411503940c00a00219811f010204100e980c2107403003009110450001c507201420469510f241e0840c555009007e0100011008034005c200c80c44850245020568840d0f07c886ca0404130a5440c10603810a000450400d5103c04200b91300e0f940821400c4e18202080d4520711131800c203100098212580d0758040e00854102460540d500b0340c010800d00b06002d0b00340c4187d56100740071101d40e070091049801c5590310000010000c0185941644840c0c820b600c5102120740501c3c0d102c080598481d1b003072100942c000a41d8616540401c041c6007c1d04540c1d03641c1c142210300e0400d15a07903844440f1150881e08000380301004001c5000300d00c1c0c03045038018100c05568441d090800780b1400f4034190400c600402c4980000e09403210303910035480300b46048028107418032400700c1c202d05540c4035440a28030000052110902007031a00164480c01c000200d00d1004109104c40300f08100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 333864199 1250 333862949 333862987
    0x70918060b01120f02030a0e0a02030c1c080a05130b072301060803040306140112030f0305101509080115060e0d0f02060c0708060112020603190e0f0105011401080c 72
    0xa0401c0004516241d00f038040303008001c02c081c2010070241e240e04e000500c0d94100c0b98107007140b540d50b90060140c1809a02c000c105040d010038165410044d02100b242000b03500c070706110000349680b0340001c0d40d0341202da00102801490300f01030400750030142d89104103511070042c0c21000d48690284007072180035500c83c0d0400d03030322005561700100b40c850395151100e045030016030003510300a84403034010300524404817005000d03045400c1408000c07071140e00d00030020707940020143c05061399400071914221180d00e07400c0c01000380f840c16078203100d40200001c20442c0e0503c10007190303600304440703002120800b840d903c00340d50855840410f0001c1c180d007001060320200909980d0001820000000760322084010521840c660000308511841c120040e864441c0c141d002c1103011801810501c0140d40c2e480489810001c0d44005100c960705c1078180d02c1c000c012400e0f1b451030920910040c140480410341007030b03041354140c000000d02200307035030019207402c1e20440c0e007648890001c200700c50508941d01800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 333865449 1250 333864199 333864221
    0x8030d0c030608030403081e0a02060106030209040902040e03071403041503090f0803070819051902070c08030310060306080d090e040602070206030f16030b0616050c100e0307091806 80
    0x85a4a9540d00350703d401c503070080c0c00685014400150251140c09000741e50a410170444450610f00007144800945a04041c05404100354000500d4419640c880e00030081d1150018010080c800604201700d40d05d0340401022035040c400c080c0e40c449402401300030344003101c1402140b844640f42c1803408a0082280c9041101c203201c1b540300c0000071500d0440558810506070711541d4550520020101c4080b03030426068807080c0c1003104010341d408c01c032039030030501060300080581c0301d20030344c07804216000c095089a0b0031884044108007160800070005002c484103078500300041611030800640364030181c003054020802c01201000b00030000480c0b10380c068000c910041c1001d6044e0300040c2c26a005a6100c07000c241a0024401445120b100c06a0000c001c0d060412440c01180042103440c0034810344814103a030b88100b44401d11005100c59192648010422084d1600400000c0c101841d981c0c80c16010703102e51400421180f0b503030b11500c0405400c00507080c041e110203aa46c900680807a50391 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 333866699 1250 333865449 333865451
    0x12050a0212130512010501030c21061a13060f0501140f0304080405130209090f1803030c0703030b030a03091412010903021f090215070341030108030d0c03 68
    0x24404203a100d6000b80103540394003001c40e00d010f0320700820050403002c00c81820580da4074003070040000803540400c0368201c070a002d0038140101140d80c44c00c85030804446024141c80d0402495121044080410b240321400807030760b508500411340b0034031049039098020b4482d400c241940520456000700070140c1c00c803810340f404520349050031100e4085600103031411643c4c03900c045428041d500e0416150290310b0000c090850800d030443d0002031703008a0190521b4103910b1045c020600000140a407000c80380030110840360307a414030000c3e0340400d92003840d06030002407410440c0c00080c40c01041890f021034140d503c1401c920b09249001c00c14101c040007056201c040d010a070046543c2c280900c0d070040e8029005020100314100300d5a2103920300d211503440301407030f00c94240300590750031400380c0540d0003c0b00c100f03444068a02c0c017031b80e40c0b602c0c81018100e000b0740d60901002c44450400281000c07810224220106000e84100c500315010038003440d0190b40040c81128001ea840d07074000100340050303143c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 333867949 1250 333866699 333866713
    0x602030603012007150c0507110f030d120606020c10050307020a020d030c05100c0906080a0612080a0905060a0f0804020102100606020c030f071401082806061b12050a02 74
    0x44054080d0040c000f48410301c1c0d40481c80e0b405001081d404400090500003003440b41804404000b03100d4800d1201c003c00c910204905c52016480f80c1401d030340440009412281c4008038810301811082d03005070300c0724007a810150003080c86440800d00c0c0c100024040e18090803148416419105500020014011131082070708540169484056042d1154029101c1802c02040c2c1d0a04904045114041c08601420281c800703004035800310801c012101c06180c240c400c0c2d110303044c83d80c002d044241c0c0002d4003a01800004000d0110320401032010080035120b40c1c9070f06076541c00b441503134003440b04d0784404034080d0f0100704c1c01d244c054405c265120f407051042d5101041000341540489542e50040f20069101c0800c01055003400c00c491100e015007000240700b45843c0c6111036220b4640050712604024800e80840c0310002c0c080c4614200021290b00c008032a05c030091039100402d55032140d00d00048043e2083c5010310342000040f40f115400041d0b281d0701120444c1c060f9915400468100110302c2034079 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 333869199 1250 333867949 333867971
    0x1080a090f030e01080a1b050708120a060510030903080615120a021308120315030a080706020a1b0b0f130506040f02150310150c021206062407060203060301 69
    0x403100701c5920a0b19561031010342031000506204c401850b49250b50b183c0050014118900d29400b102d07031425142c1503564030b0a0b46040720880c0140400060b800c2103400901101e1012900301c1c0082ea441650b400c640b00351080412002c3c0c0304101405800302d054000422368605100100c10500883d03140700034508049180200311107203040f54086045030340131a8502c03440c0c1d0207548c02001040460010891054803045030f041500c0082d285020145201000c0402514188101c110040e0407010440d110030756802d00b20065030008014100090890104c04107926514405910454020b809034205580c0d00b0b04c0a0b04405014210404400840354680c000407030400a55110f54070501003000c01c415684140a0000b01c04521b401c01480b00340b0802880702c00703807003c41088402c00442082d072841102000e0311038030101200070750400c41c0a2519029214009100d03070040100f650159940c0054240f1444003c074448003602e0036280c00c01c0500003040032a005541c10807401400000c0c0e2008003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 333870449 1250 333869199 333869213
    0x20f0f0a090906060509090c0a021f0c02061003050a0b04020a050a1403060c0304051011090402040905090d1112030a0b0402040e071b0b0402060a091809021e01080601080a09 76
    0x2560100d0300040c095441071102242c5401203000030001410f1441c00e1a03803d90000301030070b01c001c0c201c1c0400e10b000b154040c8900d1080119061441e03140c1e41410550200e40c114a0142101c07200b0300c0054850b00011400780004e84070f40c1c0d4112a041405080410000e0f82e901c41d2602002d030099030720140a840101b01640d4180f80800103007c580b00030a1128042c500f8581041e10003480040315031803d01c00c02020840118449260075001840005c0ea010306030070340b0900d4001d40076042d8000d440441c000c00e100100c0e50049025840c3c0c0802c8920030f0040b2902210300c02030300c20081d52160052801c00d2218080d5401650300040c54942c00303c1c030300c0c054001160490300a84d2050148068032000d00041540109a240086442185c3c0c0c5a024902c0e45441c0750301c42020704001d004080000c0d0f4080c0301441203101c42d000c0c10401480200c120021100c600c0940820b038070a034450501c03400c9419500c1171303800140c00c000d80306031142015035860900645164500414140819850f007680340c0006440d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 333871699 1250 333870449 333870457
    0xf05030c070507082d03070c0312020102040902070605150306101404110c0a1205070c0303082203200105010f0504052a03102102060c1608030703030e120904020f0f 72
    0x1c000c17054001008907482c00355116245000c00b80c66a08200700d448085015098440141c0b80c100f00c1501045150750022130081c4a00e5011001c040d10108541c02000b0082d084940100c0d0000c0340a184080440101504c0b02406d803610307c3da41000900410400400d81c0000e42440780042c0009180031001c0c00800107179000703162982440d004410640d040049450311050402554a4490b003890040d56420b0135414003408007a05004c18407000a48243c0007414102c0c41c07040442a0b003091206a00d00a41480c2e41c1200980c0b080301400311707200000105105650407151700c00860540149000140801440c001e015041000344203d0303110b11088603209060328400d01030b145244da9240c008403110250503203030490082900740c805e441581c20402c1034880d1000d41c0450349180c0d140c051004088c649110305030215003980c5040c1c4005030829011024001c000d0007510180314010300001c841d03844200041c00c0c8441600c2c1403003007102c1400e096025141c0d51010482651411008105e00821600 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 333872949 1250 333871699 333871723
    0xa0834082b020304080c01120b061c0c050702030303061203120108060105040501050105121b2b11210402150d0209030c0a050d080306060d0e1c0f05030c07050708 71
    0x80501c11151608111030014965100301c0c4051402c190401319200d40364a603580c81d1504102d03983c4418411240a58440081120020542a5621008800420078016000174501d040d4078100e0302a0300c0c90b02444c21036030364540c02405507145584180c20010b02c8001c4440c3c0311002c0c44140000c4000000ea51880c034040c3c20044028103030356142504000076108141c200604218060085400030002d0161080d0410b0024000d03803414045540b00300914000c0c0041c001c0d540b41d4408140c00b01c00c211400e0006009040a000d10007450f51f08110b8000d4410300c82c02c9a0344818a06949a40f0790700018001d8000d0303c014142801629010403002c1c0d990405640040ba00d42d0000341c2901500d802c00821103161300c10782c3c60613040d41c6000005903c9250180c0c020707040640c0000002c04583d9941c0c00c5424080303203104100007444038409425610f55054982c180155010140403800d02d00400211140c001ca43da62280b81d50303200701803941242c102c820226024491000049544a030501401d00940 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 333874199 1250 333872949 333872983
    0x10031e230105090706050d020c0a08040f090f0e03040302060f0d06090c11010905030f0a03020c06010b040e0c030105031b0f031c021e071202030a0b01030308060a083408 74
    0x203500416164210381018100d6000360380403840801403d504101687c00d200500e1000603107401003c54014102a840c140c0104408800030b40030a00c0c80605a0348000c0d5100301c0c030208500d0040300186022200c00c00140314035948140010401450100b0003821600115680e447c20243c5802c3c50300151011a008100300c19121250121616400110600750403103002c002d02c841140340e11815104d00c10305a214031803c4c8001028190f043c00380c2c04960b11880d001e000c03211b083d0395134403107e416174009001e99040e944042c0c4c0030403002100c0740c1c01d03a03041e601c0c01405040e108400c00c548500b41c1a030381210301d40000803c000307500141c0e81032107552501051091503514032001044000c0c1020020844204401000610711440300700014607101540c41c0344c50522030ba6000c500005c2c0c41c1c10754140005005181100c000b00805a210072484d006080999544140a4a03441440d460700c044002140351040140034940c0c002c100d880700070703005000c0803d10000054962088500b4088002d004080790 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 333875449 1250 333874199 333874253
    0xa02040e030f07050a200a14030307081b120708090108060a0b0d0902030d11151015020109020109050a05010c0201123b0a081b0c1e0405060910031e 65
    0xc062080d541000c0304d40511ba0b411800c906040000c0d124495501842801101140c41c903542038504004940b04150081c1c445904d8000e4034000401515038403850761450301440146c1244c80e10024150303003055612081150815015000444100000032311107640440200c400051640428005118003500c00d400030a6404460040c076103403802062403c010410301c034402c20603096001c18100c0c909840689190a56161516248144002a04600c181d10034054620b044a50151f03c0b16065610030b0303c800d80042d036118100300c06006a4890140071842c981030030b900642c416400a4908641c200740040c9001d5559184c8244030340308074036295285940407503581158044100a000480740030b00810452116649203101c46c014003030903810100f01491596145001844071740ba2081c409011321110300e000c02c483c4840d485808c410680030340c1c074100125200341402404c0c01c0c441c2c1c19060203802102e1035a905d80c40122003034003090b040110b51b2a001e10000e502128004104011848030b4200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 333876699 1250 333875449 333875453
    0x303280207060e2112062818090b0c0d060b03010605040501030b0604030215030c040306142401020303150f06040603060305060709080607120912120b0102030c0a02040e030f07050a 79
    0x14100d10307404c2075040000303040b28003d114080c00086411100484400c402d05881e07620225000060811a484000141c0c04030003c5c40700003030f00c2c80412110348168051425268a4100045681910001c0c04c0d00d81004002220f8250620080c036000d80801070008106584141298a0b60000e80045000800020b0304001c59a4503000da0200680103c0f13029140504d95400148000c5481e03420304581840400051003408110043c1d030000c6d81c0005081c425a19203820148025030229030f940c06a9086440c2c6a281d08070074808041940b806030011460340e128a22903c2c40340b07108021296001060205a8005072900c502600044c44161004101c85045103446404c054000b0b0040042180b0714030200aa40b200194564001c403490500c000800d103014070150180c42509405016200808400c910540c0d2207940f4449011346a107081104c215603c00490f280c0c410200908001c3d841010390303002520b4a03621844808403450100e80c50841160000803294100004c20780c3e40f81c000c07004c00c0701 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 333877949 1250 333876699 333876703
    0x7090b03010e030301050d0309090624020a020108010e19150303030e030c0709180503121f0f0509090705030f0f06070c0f111c051c050a020303280207060e 68
    0x10101800c60007442907a000074a1141d41c1d00051085510500c000758070001410b00603100c2e2400751100b40400c2c40416215503580750300036144180100c1000020301c162100c188046030f2400c0c1036505944a9469034603120446c4d00c0490040d0208991b0610f8440d000ca007501c283c03280c08a5001000c0d00b01a905c0c0ca18140038044030044010b500080c2c20401140c3c0c0355050216094042d0b4016a0780001c0e0003250b03496601c41c410721500018000d02c400581c2c20364100c900003940d40305890503207104220818107034404021a200e8401c542c0700d02010f00c400d110501d403400d901c0d580490140304803124284ea5a0002c1e03d455043c0b0f0300901c0d10340001200851280040c400c4070b038401074508001200248595540d460042c0651000d040d15640070314000f403a5681042e400d0504814440040c1c4080d200d0800a071140d404214248003243c100790590355450140341135406076260368000e5800c554520b82d003043c04402418144281d540c9000e1070b071842c6009403003e450071a02490000590040300030ac894 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 333879199 1250 333877949 333877961
    0xe16080c03031309020f09040f0f0b241605160e0f0f011205101a0a0806040f020d0302010b210d1809020d090f060227130b011b050709 59
    0x1c0c025001005071954001034a00c10004444081500590303d940303d2503401c40300e0060300740d0340b6071044c14a000a0708004c500c0c0c002ca4103c20424404020202100c41048900011300f00d0b804080c1640c000d9460450280c400074000e20301c600d000302d50403523404d5540c0174185203002d0010180d400091805025940d2410581580b003684a4610885401c1c0042e01c14960350051148912100c0610b07080000c106003446505e02654450380e0a001a00c80a0440744c0c8a901c03250455001e002d8002c8001600680003900354000d941000b040c060072045a024070150402e220b50650956403200049010386c1c41e5281c400f49411040c40c0c1c0701c811226500115810441002450010841c00e140c1800c901022138403400d0880384205001a0b89804480007031014201012018280c1d095120100042c40110f4004116014401501c582c1c01201d4a80d0000c60b00340d02c0603110b4020513200034050460189900100560505040c084082040d25102c2d0318198048c850840709a000703100100061345c40c0380030300c4c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 333880449 1250 333879199 333879223
    0x30917070b161b08030720010506040c03141302060c070e040201091401020c060a18080a050c06040b030c0906040e04200105340c0e0906060a0b070311010e1608 70
    0x150314031000f101002d00381050002c060101c500000c04100c0c09801080c2400c2c0004560390820100200310120030300034407048070154012818940c150b02c41500c40e20562058002a8003044161740f114020303036000c081000012070300706000708100c5044960402c03103040240702d41080c220082c80d081c800101048550b40c0144c0b180b51a01482150503030b0081360030680382105a0340c00e40c407402e20100c103d071000c80461004002c0040d0540c08200c110340413400e045800e0041c422038454058490500c0403e00c40c501c141c10020000740f01103a006640d200047c28010360040140c1d0034192203408008e0b185400b90b400300da005503007146400004602c03021601c0c43c00800d0910300d051a8504811901f402140441e420309072001844160030084621f690141035500000d409084c161182d912021142d41030b41c1c073300303064800c407000110075140100c064015241a440701c582001e429030f605450061682003207400c0d41d5240d0400522098040288045406549400c406080d150090481c00c02c2c1200c000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 333881699 1250 333880449 333880457
    0x503072913083a03110d0606090806100e0703230a020702030c010e06090108060a121a0c0403080a050c010f0f020918160c0804030204060605090f010309020a0501030917070b16 77
    0x32804010380811980040f081500380495041400c0329a0f0b4010b1140c00c3d448945070389012400320b056603104040c6421b031450030703003220602e8a51001c6410000403e01c1142c85070348140002580c414070a4108010405007920404d00d0b059446c0b01c0400c58650441704e041a42c3d50201c0c00c941503260400c1b0031810758600b03081c052208452900416858450310f0241c03818030000e00042034840d1500040100100050001d070304a035425407426405400b541c80c14040040c21410104501c540e02800f2513040f25030081e903462030f0803040d00055500340c04c10140c1030750035540d948260004500e180125400c0315190640140e8504a0070108141e80101403003004601902e001001041036491103103811343c07050ba007019586000e1a19180c80b01c4c5c4180c0e080250054240800020261342100180901503411100716100021240045044411120300654802160801000994042e521007000c00b802201c1104200d80c0c0c90810540982c00120216070981c4400e080040c800c00c50011420b00c890640340c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 333882949 1250 333881699 333881773
    0x110a030c030c1d0d0c09050405060628090509030c0f100e151f081b010f0806150306030f01061401020717150c3001050307291308 57
    0xb4032040c011041c2c0d2483c0340038101c03444986080c0411000341800a1a051005104902e000c0c900706441e00e0060f2034242c000c911401d1038003080c01082c0000c40202e00b00903681c0030039a283c94600006000080e000c1c04150004204203c0e54890500c0141050030060004181c5d1a134445681400c032002c65141c03000c1350300303c081003010341c440e2240e840e9000242c4e130071005100305115540c624a030903180e0040e0300520403c03450310104100150f42400b11703042601e5201245041030026134140d00b040780d60590004c144881d00d02d90200000203541c002c00c010303046034128001d0442c903070b007103840a402414519050702101615581d0401040014000b0340300036130880d2a04420180e0b4450032100a20300b52004080060210601042610382041d500031031003a0b9889114a045401d00e42c0400e21901082500c002250791705000900d0300844664491121a8814905210075075040c580c0c1c00c0801c26408001700c094806056800380d003d0441c0c08046d209000d600c1800b59000b00d940c07488890515095a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 333884199 1250 333882949 333882977
    0x40b16030e0c130209130b0a0608090307120e06120a05010b04030c1503110d090203150702030417030702030d2a020f041d070f061704111003110a030c030c 68
    0x21681a40303804082e03461010000380f401e01d02001e0f010b64100c06030012144c0c0450442005d40b41c00c400761000b02a40d82a1855407909803c84081310111000941d0764000c000a50020714180b503075554060f0f6078903000d6548840c000018856921007000c0d03040b003001060074004004002d00c58540144400300345685400e20f107948041a641c84c510a146816401e80c08400d505406500304c1c40c114080a0709066440142ca1a0b0318000c12035000182c1c043d128620f0010f00000c00c40001501a0015400450800e882c2950401d10140001c15140003800103200c0040141c50820101c42c4003019512811010700b408010704039490318811a0194407000e46804001580b503882102c4090340041c0c0700465200320803100ca0180807080400105144601000081d80709018400001030398950358588081c2d10010422095020701902d0241201d50841000034462411701140009548141000311303007007006088619240c0c11034442030300400e840c2c103600e00c10a5414458800310706100d040c4082607034408 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 333885449 1250 333884199 333884203
    0xf1a01110604030903170d0603060c0e0f0603160e130221010b070809011b060605010e0607021806030a06061203090815070305070201020d02160c050d0308190b0306040b16030e 77
    0x4d03110240128600501001d0054583c42c1116025415400306000c0b0b80d0b52803404400a00f4507840c0c00b03000804c20700600580785000240c0c600c000e0401400c041c11522019440d414002003000d080041c030080c2c264088036501e401c600c2c50050300600800503200c2d24403811040180204899050841c081c580040c40742d8110304007503640c42600b107000c96840300e020340d00694500500d61004140c00c0030988180040000301c0d0803034010b90307800b0f1b0707681040c0e10303d40c1e0203000d41400b8422000354086011b42d2082001541c0452041e400000101200e8140109071180d804a9101da0050010b1131041200481416040038286c8000d00c07020000344031621041c03080481282c800b41c200000c254030303000429043c034400d40540b031109130f01c0d03c411942c403844440c44000740a0104011648281c00d104005803614050761100700b41509074079400e52650b5051200305810100001040740c907569201d00006644040002510552240100b4080d0f0304101070510340185030315104c0420107040c5030509200c1030b40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 333886699 1250 333885449 333885467
    0x150904060b0f07080a110609070303020d210e07121b2414040b1324021c1b030c0501110901020705061b16090605010201090c030b0a0f1a0111060403 65
    0x1c0205a03d1740c0c1c00d4031013255891003a03e20790b841c0c1d200f04024030242c5e54001c40c5110481c0c0c400e8003141d070024500e0a041e500302446c4140c0500d1010241c411138114400d641160a02c0184881a40d22280e103440e00201041c0d00d129065401c5400e0400c0c941e56010258201000761103c0004c03940c4284003a401401e4880010b040f09003005240001c522109900c0c20a82d409409050741954880030641d158408040141c81110030303844505410140c10055210b041c1121146a40905450086201c1034260861291351030000c01240c07510b003c0d103480c295540034281c24425941d54886000d40e090890944403c0c808908801d0020080c01405a8000540310b04542064506507180c081d05c1e80c0040e40001c04164904441c001c03101d41c6800e0681070311442c2d0a0781c1e8444c10803c01c0c079413984012422124a03010081c22044480801c4c80401d8014000c41c1c0c5c007152a007804a1642001c155038402d5403580c441079091101c900d03c0c9441c4a40c0c010400060050101c0c000b08005d01d05910014030b0220 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 333887949 1250 333886699 333886703
    0x2120c1902121801020c21060f070807050f09041e05070905060a0e19080f10021c0203151207060908120405120f010608060103020109060305060d0809010905150904060b0f07 76
    0x10b801074543c1a940d000b8003166444841c01000e08940e114032061204540e1550094000540503500003d4260000c2203900ca006555590b66101c2581e15200c050321143d01c2046414840c040500500e4010350703c1c3c3c0952070402e646404000810818910b0003401da80c005003580040c402412014031654540200fa500401c019181c03856603061002c010801c0c00c03441c18039404042d00140004a41041d000070480c2038050640111503d106105003058201d0182c0c0c80018034040403148403a02546c1d01c0d401079074005450304594013145041c9400540c842e0030118808015811030380c010003916800c030308507000a2200e500607000304103840b04120010310681c000c40e4404d0710302420280c2c2805041000e4290144014001c111280c1c42e105156a140d41c01d200890000b900c3c5440464520b1003406018007a54000e80300c0074a001c0c0c00c2d540d540107500711403c554104a8007041c002869501e40c011003601d18504e002d0a45d40b00701901c00e00059a600760040c20b80c070381082202c030010382c003c8011155426 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 333889199 1250 333887949 333887977
    0xa09030f030c03140f070e01020307120c02060c101d0a031205100305030d0603051903021b0102210912070302090f04080f3c0403060f02120c190212 65
    0x103280c0b5003d600801d11102a08019203090081090400c1c004036954010340b200e4881a038201200c100480c1c0d40d206d0410020a0b03070000221540c4428040c0c60740c0550380f4401801d0600309442e1950301450802c031b000b1110041ca441d2100c104181000d004594030060158000d811010042c2d100035085076241da0418801e641e85030006103134010140d29840c081e41e07100c0d003500e070303a1090008003c0281c40c2c140020341d981d0242000c0a07250001e4100b03c1514180e143c1c000d02912504060b0400c0b171820b110f020a815401141901111001405100144840c200e81802d403189441c00a0004006907401e201607107600205050001d40e5600c800c01c0e50103600d0000020041e41c452510384000d000340542820001d402242d490135411010310a04580300d6030007032000424141611800baa0f03070080f03c8111803900c0420090010840541140107040046103002d0700d0051800060642c0b503400300c5590501050100b1882418402c580ca0074003000810300c014400320745171421301e6015104180c4180014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 333890449 1250 333889199 333889211
    0x7120807082d13060e16060306050d030f0c0b0106031401080102040e0112050703060923010b06030c0a0912050c030d020c010807030c0e030a030801080f2404020a03290a09030f03 78
    0x824019000864150310181c00c5c0030181000c100996036619065061042c250041c0002c141c140c070921851040f078900405a10120101c0e84043d240d20000d48e41c8081009029100e500204650f500414000e001a42d800240300d001c92504e0b000400c0f0680000d15603900410080000310524202c0c3d5040d0b460b540036110341039003a880c2c10351034008140c0c4024569410684e1100500c452070100740f282d0310007000f2024a0345070f100e40c10340c03c9aa0032481c4903480131040c000f045032600044040c240300c449900307081182c40d842d41e01810014810031802c660301d602c04c031050720381410107004024240101f400100a4100380400107071081100a22050425544800c161a80ba01c20304030902c0000c005416649244a07504000700101300901600c0100e2094500c01c294691001072550408860f03000d001c101c4801003100360070110f1014000341e83c45200d450011012400003542d81212104090841d21480d202480607040204001d00c490340c10b40c40d0507113110119801c0b1640b001035200724940040c070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 333891699 1250 333890449 333890461
    0x90c0e06120f010212150a0608060f0a0f051c0302071a07060e010e071d010311031c02010e0114010509062407030504291e07120807082d 60
    0x20364018865200d103109500c2c44144000041d40108501142203600c4461070340d8500b82c03c940180311000481c0c00601030b440030081300d40b281e611140c2094004142c01040c0c03203a00001a04003505070485010044240f2080140b49070040300b0644440801c0307141e088004080c3c44c003035103800d60343c0b013880300050115008040b13012441049554040e4420010403c865a946816000709803103130b06640203100300c20000c210f90381c0400100000124580c103c074016800c6980701d440b2420106245a054421511002c8000e40d55841c1018140004d60001441480b042042030039900c1400752803080c0503485006010684075403400c41d0380650151403200e50f00c030002c0039503c40b07000d07644e0451050b643e0100d2803500b0107500c100107000f22907100300100e01021808440402120701c0f00682d40c0000e504204404002d100c406680004085001ca00d0742070004e43c0d25100c91286111001000141d04001003001700d540041030281c10402420040000c0c08540318641c210080d5150021882c452010024603 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 333892949 1250 333891699 333891709
    0x302070302030702180718080d0302220602150c0a0806040c120c260f0103021003020c12070605090111030c1b07060c120f020a0803060d020a030c060909090c0e06 71
    0x200694081c014624001745402c109207480310a546c0d0000081105607110003c100b0039100405660103c0003a085070036190500341c00a600120342d0510490720f0542c5a00018000400c2e031000f0300c1c0b40c2d0060321082800d525009103006d4000c00c21500c0b98804d01c002030340307587c0c003d004a41c44841a500080c1c048248a01a641e40c1d5001074105011030404010683c038642c440645a0074501d00c01d44007c3d4080c150313104e07008145084440282c1c5008400040015182c0403440011b00341c00f5080040c500044030014504049044001c0008000001101c1042011921a86034014082c000801c030009154002e602d6610020300441070b0500041480035400c1c90070300850201482003030854a41079a00c0300050840741030001c0a0f41e1150043c00c01c1d0700340501845940084030300a0340038191b10503040d82c031550140c0000e001c40d60450002000d00e401070f16070071011005180500b0070840703031500d401c000a01001e5990800030041d03091000303900019080d002030200380d80030554016002e0b81c600022031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 333894199 1250 333892949 333892957
    0xf0f0807120b03011d0d0c0b1b0403050609030405150c10020d0e010e0609010509060705030f0403110610051c0807020405060105120c0c0d0e1018050a080606030c1807030207030203 79
    0x50f899403078804066650411040f5900408880006540450440071000d903000280d0f941c010303080d840400c0000303680d034048041607503070743c0754603052542466102e8990900c1c10000b01c41d20640e607440080c00340090701d0080400d00d80100d44103006442c000c40c0b44680c0340c0f1840a5840f080c00582c0202d04502c030b01119400900b807400f0b860000f04210f6028400c0c9030340d40d40d01562071020070752800340031a0b52464045520b610407031541d142c652030754560908103400e00b0300040c000d400300030404030a94440031040c801700c0d0140c040d00c9041c220090502040200381084180c0c1003018800003960840003a20034020344586a070101c41c001010740d5140016100c0e41700f014940d0081d10407650401c1030a00b5140c015280c4241d40c401250516580c008099614458258090f070b40312543c100300c051024807820206d809810764001801d55241d41e0070220b01d41c140140c0091a06030080390800031f960030b040040b04482d50088a0488413940c5121407400f08580240014040540004210f01031600802c229 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 333895449 1250 333894199 333894221
    0x51b010612050105040204050a0b031b04061703131502070b07050c0a0618050105310510050406030f090f0f051501030b0405010e0c0a120f020a14010f0f080712 70
    0x5048024501d00302c0d00130042190224421450701000c152040040c0c89410350b803501c0900200040b42c10358171050104140419150b03440ba8a070080480d00341c803540740e5940c122171784900440e11403a0f190300c0201540740640211070b410340c80515a458140e07001403503c00325603012540c00d030b031080c041c10705900f402101180d094120940400020b04a64400c03100d80364207801c03d83d0101010b031034500440309889414400340380f02e108809241c4410700c2c26600060081c1600c4044201d1340d82d02d0700491403507030142108001240c8041001c00131249c150054034101c0407400c0b001c201404184e9030305401c116034001c0242458110440356001c0100c02c201c07600110402d843e140b00c0a41e9a4980200d9805003258215115400c081013420076050014110300c0c40b1900502d4520b55a04002482e040b00244d00020748041841c00d0101015864281d542c1000e01600e203031407600b1044010024103d41486605d0004001c080b01c0d0101001fa40845203507001891850043c0810f01d0780340c0c1c0c00024000020b20 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 333896699 1250 333895449 333895469
    0x90f07180312020a020321070b090a020301060303080a06091e0509120409090c0e060d02120c15070506100308031504021902060a0507030e0c060307051611031507051b0106 75
    0x1541100f40c0020b002d0101c0392088088640d06220350100c801e4442c08000d05c2d0301c24100c28412800010103441880f6442000e100841c0c1d40707840d0030740000f42907521301d03402500440e002105000c0355080b14060003014000100701400000703008032410a01201e03042510f100d1507a52000301d215071505000842030b01441a002c5519161150122402000c198104441c074000c6080009440702628100740d00c100c0c001050910420015001d000503a400c01000e4680c9004002d42e1003116138601d0702181100c2c192f40d9005072284150b26140d4640680904010b00104142904000190200c0116503001c02c1c12850880e003845100c0200b4040c0c0103481c008107250345294070100c04181d000803140c0c810345407070700207010548903a031003582240c0707001060f1601da8008034640c1941c0e0130074100460b0011000d1426618180c3d541e0b4540c1c11681e000c074822155428000c00828642c5401c00c85606003880c41842c1c9203890420403406004c610030800c50f00f06485000b44410746d4035100394088801003410b500c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 333897949 1250 333896699 333896723
    0x30709151724070813030302041203090e010b030c030a0209011b06050a06170a020f0f04050903030103050d141b0a0530040b040e0a02090a03080901020c090f071803 72
    0x20000703403100d00e80300c00b2000c00c0300302011540404801c0c42c480c50140080740c0b10b007000c94481116100030801005015003c2c15020040003c0526112005100c10f03070003566007401c0c890400d60035400e9150180d00c9040240c006000b400740e4500448120f80d0401d0255200503500c40a280c0140c078070305005064002c0d882d480640500c24400702e030708110720581004604000c0c654461801c608120580034100c1c3c0785901c102c0c8034100609081e20003025500c00208400440842480001e003521421074010f18150400300041081000c00c010307504072079042d4201030b81107840f50300b15040d0301e01841d2180c40b45840a000c920040c404240100d03152990440b0944455040d522a020b4614428100ca03103802d11021b8000e40c076410b5410180c0301910785440340c1c54030302480e110068400300400341003000255820015081c0c655280c071001001944242c41541d100d99044001a06040030340710f007180660b1201003007100704980b42d0200c1b40d11800c50b08000c1c41c070307080b0040b02d5003056011303400080a100f0091 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 333899199 1250 333897949 333897989
    0x711090c03041a0c090105180a0b040807090209010e06300702070f030209010303110f01020a0206060f010c1a1f0f05031e0607081503030a2001090203070915 69
    0x24004500c2280140c0c003c0100b0002c050544107100d404607590b030304084051046080a40c03240d001801c00030000e00c46201c00b001e81c140002c40c086080d50000c41007440000d13080004c0642409080d00a106000c0114140288800041c140d40c980740101c43c420307000084c03440c01407907030130510818182402e84040d5001003240300c205020307079041d40c120f8050310400600240b82c1c520070603900f0681340d02600cc400c0c035910310381c0d040d6080170620105a04030301910208601c1c0c844240b014100511555000305440c0c2060000e00505500200c030460411080710155804515503001020075000d2449d0003500d66500d00d6116410314420800e15070584500304000100040301c07071400800e40d581101170b503581d05801107800700300200100c404150b58102000142c0b0040c01105000e51240d030b502c40d8507656200321300001b070455110500044c003066181260a00034048081224008090b0000030003407400103400095880a440c030814421a4840c0441320003d10702940000003000b404000d0f0403100901 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 333900449 1250 333899199 333899221
    0x30309030f160f12231906050a0c120207030908060717060405060f1002070f0b09030601060309020d141c050d0623090c0d05070c140304060e060d0e10060501030e06100b071109 77
    0x106d10182c0b0843d0920012440c1d48201d88140c0b89003003002e0b21200302201010300c51001a40100b68150140280d84d1000120f02805006c0607100e004c05c0c1d81c45055000b80b00706550103004014050a000c8c903c0c200c100100e5031160b02c0c400e00d5414040740e8104052082c00812440c0c643d0582042072400040000002c038200042d000c0c0140c240d04400340c5405a0701d90070201c00300c460550000c0d6004e011a920b042c00b240700d01080301e040da200b003026500030300e0810100b05e000191070494040090400500140400d21922980c1e0182104000c0d000003020b084140707104403540018558810000c0c07002144218481c003003210711070320001500348030134070705008090400c84040c40c0659818000f40c81c82c100c224004812a8150780c02501c4e0024000c80c90020b018607030300850000d8103a1591026a404080d5040025150340f110420340420f06c40c2c2054001003d880155000c04950743c403103000e000c00500b0b028480d10544110420082e2034807080c1c14400b0005410500907a00000c04c2c2082c05502921 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 333901699 1250 333900449 333900493
    0x102070302060a111c060503060403050307030c020703150c020f2425030e01020c010f0b0f01051201050d03020a060f020304030e09040b060f030309030f160f1223 71
    0x194003502d110755100e1841d0310513119102400b803000402000f041400f490001c9503c21410081000001d40d66115000b080c44d0800955041e4003045000c030412200990500a1040c480914805042c0f000e184d40d940c1d02c0813103c54448200c42c140c0b40c480d1422003a1003000460010300c0352104032100342c01c1032140109501c040080307000000c0840d800090b08000b519080402120020240008640300c61030110010f041d018140400b0355001c000b012042c4000340a4200080d00713003800021010000001c001c5030400d09042541440310502200c19690035092101c0d04440381507400b40501c000d40d02e4102d042400c0e40d20020440c40c03404449031180081c80d80a90b10851098542c880044000d00030402041c90488008003041c5078400000c80f41e00784100c1c1584185000307000c132800e0010520000b4200480141012038590054024010900c00003805400510400c10461865802d280b030f0b0500707400c0409006030001c2551030420220480c80c0d00e071040c88080c903c0644030340c02e002c0c405191480075 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 333902949 1250 333901699 333901703
    0xa0e04030e031908070c0e09070e160806091b0703050d050a02040e0604110c430e0405150a0509070f0f1e17150a0b010801030f14030c010207 62
    0x8034440c00c50165080c0090003840040b010350002c0d10440f459560144140d01c01001194645800760001071828030080c1c07000d000d40c608034081c1c101c00b4241208000c894400130700d490619115403500c6000650841ca0032604004183e8403003800e641c500e904220540c13105407d81d10b4881000910409040d8070401500d0800905002031006845880f818130981c0943e00400700c50904400206900d480c00e688152104500380c801c46051013120b840a9040024011003940784c10103950a26400900302c04841125100a000012160340b02c8001d80e8000c103120301a02c4102e00a200104d002e10104000c990f203102c51500404040c0e280040031400a000305a4584610b44a00c0e1804681c0d00740d0132b0502415110300b2340d00581031610b02a1250b10700514403020020315580c11101142d4020301d24a100e0340c9484880040001202c1e100c414400d0b914000c01703a400e803038604507500149a07800700c030650440f0f8000d010310107400998100540d04941ca41501e100b0343c800000d0346000410103401401c0c03168 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 333904199 1250 333902949 333902957
    0x20d1a040317010803030c040e0a0e07090605030606090906040807111009030b061027030c0603240803040e0a140403020f01110c060403110f100f051e0c0c0c0a0e0403 73
    0x40d1340e0318541c1d40e50f0700040d80c01c00c00c240c1e0188018420844001c0110b98450060040070405100079a80c82e41040c4843d00032180c52a04d070361081c0303e2400c0420099401a0f0183c607101690319000e601e00d6140c0c640a00014000c074800102c2c94180001d01c1d070b40090000001300310442150417a6005400450240700c12900e4903500310002d1680d01d45a9a0003400c4030311900c86048c80000c514001d1084a81020100c10040020b100400031903074103200d1070054030058500240d107002c4002c0c004a600c89140605002132201d0743c0034400c504001c03065804445820034020b049071500001c40000c0e000450310360484007818001c01c41890b42c006404020508050000c01000007a4bd020900760722850080d0911a80100c012400081c03150840308810029082030328546100501c2c06400c007074904c400b0f07d501d00c0d2140404100c48510303110301900400403200c40e0341003444051101c4403240004254202601d0003240580305d085080c4005106000b00900c00c03041a5112903039901891010b46042e0002703 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 333905449 1250 333904199 333904201
    0x140a0f0f150e030a02010e1309060b0306060d201309030206060f01030903092105030307090302030c010801031109040203070504111206010c0b041202010b090903070605071b020d1a040317 82
    0xe5402802c2c0081061000b60140920109980040d1081004900710035000140b0703e42140480e03165101d0041103030701c00d010105401c040101010702d4440085c0ca0386203c0d0328001c1c0c480000a11900d4114603c90f1081c20099120b2920000a0b44000914202c1001a03050650003420568089001ca00c900d00c211400c840c0401c4c50f1004500f20740101d080200805d41302d0700240f00b030703104101e1041400c61841ca01d003a0510f00c140c0c1c4d01d6085030000d5480c0808280348010500443c5014010701011500c2071801403080e40c9103890f1942247e0420140c01d0144050b140403806640f000c1c0a071342e02030300b0094000d020501c221501442e607036001c1041d0f01e00d20300c3c400004c580c096201c1e11000c020b507500130384a5502e0351650307202c48140e01868201c001c1903641e103a1022250b80c031108030640c842d80d00040555250341e00c0d403d2000603107030000e001400b000b1080b0400041001a085103d654540580ba03024035035802e071601c0042c091201c41e0704c810342d44240c8100010180d010040000544000c0f03011605 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 333906699 1250 333905449 333905489
    0xa02031c051b0c120403030807020c1e040b01020a1202071d041a0a061e2402030f0f040801090606080f0a050c0103090203010b190f0509060604140a0f0f 67
    0x4554040e80d522201c14030500162844901410160035502902c905884d040d03500200d501916034030540c0700328082101c800401c044143c06010f0400781d4042a500003214805070034101c901c400003800b000c0d1195079610175800245c1d02c00c00c483d444ac1a40291021000707031450602a55446980c802e50312624a01d80c5d2110190442000642c002c40e072003010310307140503260320a500031900010511401a5030b1210001010100451007580700c400810075860710030300b0000d545008414600c0c0d808400c0c0103050070036030341d15400021200404201888281c60b6041550b00e8009445903a0220030503600385032740750040c40075641c0a241200d05a00c103d40144001e0441c664031070443c401c0240040d00301e845120340a5019801600c4010f01c003e000080c1c440904c40000c00b1262082c0c1c00d07e0f07045059640607c0700c041d0800031540030307101c1142d01c1010b030b14154000a900e4481d600400001000c03204802c4c0140e03d0b1801c1c0400600040c42c001c0701d5840e03c5804d0344800b4181845011100c01001c101006 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 333907949 1250 333906699 333906701
    0x507180b12030a0806060d0207060203041e050d1b0501020f0d0b0901120605060d140c0f180c07060b030304090e060c04050f150d0e01091101020d0801060f140a02031c 73
    0x2902007100700207941071034210b40041d159468001c20b1660450001c120440c00035840f0301c02000114420040180c807400c0505041c6601d00072000039512401208030054003151000514210780d91143c6030900312a8400740f40904140001d00e0020308a60000c40d1070300302420010b015160704407080070108030204103501044613401e000e115484078060f95803160404100c031500516417119002c0e10f21540761986aa980c510080000f078070a4031904507204d903501610381015030b20104202100e444040014900301c0180500303000d04040740354072001806030f0801810b50040d00c52a180101500d89a90341c8a1111001d000c5900f040f41090280750001a01c4130f1601046e0b4059820180c4000c1e041c0c00a41e05016440040705282030b01c0c0030382806641c840030780901418000003e22000071a200a0303500e440070408d400e046030981550080321071180e0295100c80168112101840d00d40b40079144441c081d03034188550035405e488500d0000e036603403050fa000001040c042e581407a80d5a03d030005944540 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 333909199 1250 333907949 333907969
    0x20c010e0c032506080601020a120201020d050c03011a0706090b04050d02150c070602073e040606050a0f03090206070305070b151c2409030f03020c0304030204180507180b 75
    0x10302961145403d000d082c0c0300388405c075402541801102c0f54001c540e02c0b2008840300701c0850100503900050700824144060082c03942000901150f0780c25035040061741d0f0f520007083c042d030300440480420100240101e54110700001074200da08903811f400d00c0e007041c07512075070505101d4001d8401c041c40ca81c09501c603190000c0c890740052011134101046640c07280c01a500080302a07070114100744001c030703101205440075a005106d03e031403030003070842080c0503900c3c3c04000480c5030310842c6420005c00c6441d401c42d04440180d1442d10f810501c405011005070018900400041d40200d07000c1880030425401200078a00540181d0b001d080c1941c504c15905404409002400d030410602c0c00c0000c030303da200414200c1d519210b076456264400100041c0181c400e01d13032a4800d241c81d1101181e9043c550442100340c0300d140d0f03d240a520f42a00f489607265244600c3c0300080c0a65560601c4a544620a011000a5640c49820b640800307035280c0701ea2000c0148071803030f81d40072031601004c44001d01c0c00352085 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 333910449 1250 333909199 333909253
    0x2901150810030f03111c12051509040203030c070603020d0509010e122d09010314010303050f0f0f030403030b0103050106051215010c0503070f0c0f03050303040b040303020c010e0c03 80
    0x5003201d02d082d82d032040344003504401c04a043c000c0c84010b070b600360315090290720035090000c0d02000422000390002803070602c506500c429014900010301640381150308980650ba101501c0c035804a484d2480481d29504c03801c284100940030340b4002180290307140e0014603200d04d840c00c042c000fa440d440c441a088603824424a41c0d03581c00442c0209800c1e9001010703001c050b58000079950b0000f034610320004100075041c052800550f0001d000a025a050312901c1d040d040355444003403156040d96005010342c415489425401c22000ca1002c0b4000300b00300440705040d069400c0706481c5d007013514001e005001000045408203080c60000701e181380c40b8034107641c5400d290170350801c0603031075002060100391051031b0701c86d04105901c0e0500010500400003402011b03c6211344480140d09404c05460141194002c0d000e060108002040400c40000540340c019811030144e070340c1515545019002071144460900b0154200302d501c612400300407410404140c01907050b103560440041076080312552080007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 333911699 1250 333910449 333910471
    0xb0c0f03060d0c080f03040f0618090b0a0510030f050601080606090d050a020303041503050105030303010f0e06030a200414090a0b070c02060d0506031903020706050729011508 77
    0x6000780ca8000c1e40101814000e5201482c080d40701c441490801496a14880c1a640005401c005640d000242c500042c00c80f80340444c2c0c00f000e991882e4010540f94412946415100d0168566968900b145030004040061004005081450018002d0003155140d80401480c100004000d9401401010f00c1a100203010070320704540082000701407185a076081c0d4061003000710000068408100520280a2a14240c46074036606c000080540d0030503048540aa0010303c01002180002070102c4250751350010041c0c0d0139912040420314010141001420780c0401d0301d1101c026086d80ca00e0818610019242072110030300131401021424401c1da014040350340032004103408200355122aa42203c3d0382c1c909054156610f80004500da08100a44422141d03600180030061404100560441d0038006059202c007120303440c0a0b483d41c6090cc514401e015000804000b0400e0300e098500d4225009142c108000c030040380f040c1740c0381100340110308004010280c0d403108030f4080c0a03079510403900008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 333912949 1250 333911699 333911701
    0x20a0b06040905010603060501060315170c0112200a02070e0630010507020d1e02060c0a030207200102071a0d02181c120c2102071806030b0c0f03 64
    0x284001042c110406031195541d0349004800564240915402000256400302c0d03003a030340700881c00100c4015071181c140e0003103450210740c00c1c000228131a1141c0c0002d00b400c00c80e070f2031001c0b0324030040e10408490180b9000e000340a42d041c0c02c2c0d490054502c24a455003103501950f160055101041000c0d00e0040d27001da051904112400c04c07a60100164080d030740304101d1408208a461800d4440035580c10025030404000d2000082d030102610000c082c0b4401806103141049001035210310000d09040380b112400281c0e0141c0b1406901100d5255510000b41581030400c00000c004244c1001c07245070040c095100b0018401082d0902c01d501010100b02c95440d0214100c9884020350007c03c0d044c1c41d98035581288882075036009100185102c4d08401c152951f41c061410020398885c411500060180c2c0804407404a2410340c207030242690180781c40a50300c030504006034545040b5034002803d075107800b000e4440c0c0010a40001040381d102e00c0301e005d00380e140c0300b110f02000e01804c8038000d4400c2c0180 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 333914199 1250 333912949 333912961
    0x80f09070f03060f020f04060305040605060a051e01110a0609061107080a0e041e0e0d030e0d0e0d020306010b0417010908030c0304020a0b03011203020c100e3a02030d020a0b 76
    0x182c824401c404e021900189489859207020149410550002d00030a5550381080103000e00350141030360107041103400890710ba0411001840700070070b4140e494811016010b02c1030007640140a241143d0310010120b4040845c81e10707000d400340a1303283c012914607007402030284041c6642400d59007a03039801000c07030741080285081180c1012248000303039070054907038550f5203480d00c1092886000100440020038842001c0d21301c985020700701400380b020589420720010402201003649001c003041071400c034000500a400080c5401d041c208060f61500518000281a01d10000144100e800200319080c0b01c042e8582210f088130360443c0302400794481000041c0040e00260010341d4030178402001400d02c9a22a040e010b9250000d070001c03c0419913040516040c0b5404100803403495208503014100600d81d4800144220841200107015030b440d007818082845002e071200e0b094680007035031000c04400c0c10081c1c03c10304000d410142c3c080d000c0e450400c00c030a4404643c0c121401c4d046410162551508 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 333915449 1250 333914199 333914201
    0xa05030708180a15031401050906060703021e0303010312050702030a120309050a05010b0316050a030206031b030a090309061806080601030e060f071e0806060901050c0d080f09070f0306 81
    0x10020184050225a810446981da41c05074980034101c50b801c0c611a21328800009400c441d0780145884074a10503400400540c2c2c0d4510035070354004030035103507107072244442e26041c0d10700f00701d04a507651180c021310b82041e0392180c004090350480e400b50707103006e40341c4440c08002c0d540e900c41c030075000c1d404d03410400d03140c00410903400c400314058641780350001d0440c0301a00d5990400c50001d03421034250351146140c3c0141c0c41c080107091295902607054840345031902c0000f903c8010b00340302c0240245404000240714181841403203030000141201c2070303940d20300031a035480109018042107010984410012429500c0b605c0d8000180840e98948084141401d8050f40d143c5002005541050744900e041c5090f81401d0000d1030094032540000350785401c1051003d0f040c4141d45607007034220000400b4154450740c3c81040660031502c242e690907a2000b140d40100e409100c1c50543c6c070032503c80c0070b10b10314407143d002c40c106101d1101c41d40c1d00101034071016441134448419110303d164450040304184041076031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 333916699 1250 333915449 333915457
    0xd1b050a0602061f1707240c1509083004080703111e01020c01201c0603020a120201031a01021213030b01080f070b03010b03011205010b150705010e0a05030708 70
    0x82061010313856580b002d1255101d992080b032002c06801034117041040000c004910741c0603107a036000c044c015000004000348404440003015050036040c030b06000040d54194003500b001508015000d56591002c85001800e4802d0f00281164610318062525003420100742580950f6101d00c109242c1419500c040b511801a0707044100309000310b10350400b88040b0100a200b01c030310320000168986c2c0700a4050380c03c4901007803160074200d40080308844024003071400c07143c110000180c4e12103900c0034900c9010040401d0382009402050307903980406c4400c00d1a0450410034800d903418000030295044521102e0369407082140581c0c04142031442440a1001070000010710105802c46180d4a8071009400c940a078041866508003001d503611a030014000c84010b040d0380c4201a01e1940752504001d400e1205106c1c0c01c007003240e001140300801400790008000c00c54000c201d03070b19049915916406036070050038112120b44c0b800c80144008000400c4007141590082c01031800c010003501d849415601c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 333917949 1250 333916699 333916741
    0x3071a04021201020a0c02011404050607030513081207120c0507060e150d060602240a0f0905010e061005041509020a0908071d0c121909020d1b050a060206 68
    0x345003855100c4824013403000c0d00c02010f40c0d90340c6901c0b9684a0001400103000c1c0b000c0200c1c403c4c02080240000e841d001c0403526203d9240c83c0c9156039200d40c02c0710121501d015044003541d4000c0f40000a511105030700a080302a009180c00c10f0a108603103001d5035810079401004020b034020355020070455004a07115a801e80d00544185003511505203102c400d903000e00e40d403500183c1e0302d40e428440e0300c0d4108800c0681d5205009864600896051600707818040140704101540d01c03828600038003c40ca0300315240660344a8000d001e58030840c0e0383d03551551030460f2100007c5d416410000342514203070049001d240c1808100110150810380414065480101ca00d4184690b1031400500f2140420a00004007420b502201f4064500340c800c2d564140701500050024070203000c0440d00241c1c10225681105100ca60036401c1d03001405c0c8100074140e4a10040d620203a440f60441c103000240c84803900800d901c00ba0a0151500c440800800007030a01a032001030303009000080c0080380349498070600d28 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 333919199 1250 333917949 333917959
    0x14030a1e020304030b01080312011d060409150504050c0f040c090b07030c02100816080103030806130615050409060801090f060e030412050102120711100207110d030f08060303071a0402 81
    0x603071245ca0303d50400b003003070b4080160741e0b00025561070360400b81e4841c140504000080c0d5414811203d031603240034000586228031441c0d840c01c0706820402a18101d45042210410600c00c600c1c142c00c0c031a4a54144c6041c0718083d6002404800ea0740c03400c1c1c481d05142c111541ca4516005040801ca88000c0d000058100d080c050b1111403100941d90340071000c02000801c0c0c0c1e0b0b280807440c2148554594014520042060200c03860061000036001b4031080d03030200c416542918569040903190001d0010340d402054030400b0441c9503180b9a510600901c20742e0a0b00c00c061103a00c1e51034040f02d01725420402c0180a103520140d070b030340004a50f07400a0800e01502c1045a0030952180f1001c14510b140035004c9034036030f500040948542100c0038509520421030304083c648440d03e078a0940c5c1b60a0820300f5405c0b25640011404200721108141400070180a400c85000c501c0034540501003007000c184c803e0201d9814030010381140380010495604550200b4481c0c0001131078600d5030a070860180c4100ea08ca = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 333920449 1250 333919199 333919207
    0xc0405030a0605064002040f09020c1c181a09100201020c010203010902070204150819030c0c030311151005060a0c0209071d0f0d0b1b070f14030a1e0203 67
    0x30180910714039148860b0400742d80100c0700c50b04111740c44602091310b80b003170040c0710070400d0352030205e018812101403400169035010114081d9080c140c0301480500c85d00410700142203071581c0f080325408803000d85440000915140d40344002c10100c0d450704035041d44000c00140c0568108054a05885030342800003500304100d4109060a98200341c004800c041d502044080c06c0d49081c0c00382d840e102070504e070380032400d03401c06000c540c07100c50f00719000c502d8241d4007a555040510034040100026041f10300b4218641e00da00d002080103e142d0105600e0348610320a0700b80c2e844045031b81c2c50041030100f8000418901d0403081c061250031031100d07a01845483c82c820000b50309d031280c00c1071242c21140d0b903101c08203032070951410101160030103e030b000c0c9061125441407500c407164074184603608004051615134039070190850084518003070903041c56001c240b0001304550002403c0078240305030b00c01c081c0004092a11681c0e40a40c42da0701c0c0005140c0404440a01118140044a0311442c0b05403450 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 333921699 1250 333920449 333920479
    0x9060a030f0c0e04050c130c0c030509010509180403140a0c030f1412240901091812020303190903170403050409020406020a0c05010203120a15030b041401050c0405030a060506 77
    0x15101c803c480a41d91500040508a01458087d002038485000c0c0c00c4d080007245590640140480a074a03002000e00c80f00080c0600780d60300401c2072340d0b00300400400600d030851580a28002020041e030302113000c260040c42c60711000b040c4034142c54010040d69143d2901c000507031421a0b5200c80b09980d001030080021080003420840130090944104c007003d00b02003401c101540207140d800c580b8018221104a001c40e213090307034420070703502d0464540100110788241002c00701c5c0882120050b00512003403050008121407030b0040301840c411200342010301c00d110000741070441603580c10400280054540108500445211200c007174210b8001c0c41d01d54240341e141e030003280880e0301030703000800942e0140d6800300030001821031807006440b003031015505203102c080304420a6503000c0d045000c40303078560040c0411a441d0035120b030f004542000e214a03450030300d03040840b1208002101c84016508110002e0014112102110202e80000e4001c0c4070307040d565261080288805002c1d241e100e001403118009c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 333922949 1250 333921699 333921719
    0xc0204020c010b120d050d050a0e03031306180b04021c05120405120c01210b03011d010b0a03050d032a030617061b0702011709010f0b09060a030f0c 65
    0x3032510360090000807074041d10401c019070081032581350441d82c0d1140b070f03407046100d034010162003501c14400000700f800e8590301400c0c0080c1468099428844c84003104211450b15150a0804820300901c010000200e51007120b05014074140c00c0500f500034030780041001801d100440c011440d0f00e90343e50940050b29645c4031400d00000803c0300d6490000404c0910440c07130301c6003500c2a40f194030401818656140c10001c0c0210510014924a4004181c03d207041d0103410f400000301214010003c0143c0b0002070040428009050390315200c0352300e0800400040c0c1001c285603401c1d00c3c0c01c08010b011020840c80202c020300603044911521610b4081910101800702c00319440a454948002c510300341060045a001e1005c52611240380d803020082c081d941101d0b4800640781c8081c41342580e6038407005d00060ba400001030f022036101064020421000712019401031401502d520424400e803c0c285c03080002c208019100035502280002003040050f100c0c044900c01684590789200340c580e91880c1081d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 333924199 1250 333922949 333922957
    0xb12040807241a010203070507060c23010218032a0406030f050a02120a0b060d06060b0c0a05060106090b22080d08010504110712080601090810140f060607120c020402 73
    0x484000d0310b40c0500d50f244902c207105030902010078802103042030060307260142d40b29207a205450a110414820300180403580c1000e20000c1e00c1c42903028680070000c1c0f400760003980a01a40f030003440700319001c2c013500e24000ca020f44144209484e8040920003891114a0b02e80081d220349901a940d04400000240440c9000c614a4010406840740030618010300608400240002d400c0d900500320140000d07081c0005503030488002c2d181100440200d24000c4020a125081280c4240340403c1c612a880e00004501100c540b00310140c800311307661480d0a0310b498003913000308002c6c09400e11100c035000c0082102410f4404458407543c00444d66240d5081c10304410000c0c104c0060444001400f1904150040c0f44aa19880d41010325110789902ca480841d811403242000b00802000440c10391b070300c1002d1103005042c81c3c400b900c01e0384034103250340c070020b07d01c0070044148103481c400000e2004062042e110310a03440540442c0c81c01c04d02c1c1c1e450403101c0000c0c0d84210700788004280d0072030168960744080c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 333925449 1250 333924199 333924263
    0x30201020d060806010602030f030a02120906060a08120f0702031603140d020c0d15140705040305060606040501020c06031e0a1a041a0114160308100b12040807 70
    0x1690380401c10010400d45100e50040c0809901c101c0c01002002c2c0d0000880f100320003072001d103580720740780c0c288080302911444e80c407220092210343c148072120001043c0c081c01140100c844098083e0f40329691610b440c0306401030030b800f040521404101c00300c0b84008040b1030f4030007001d0301c0032610224260801541d86400640c0c00c2c005c810341c0d980d00d8040400108140c43c00900003041140c0c05030340040e401c0c0c010810000c0c8184040c40d000c1a9412050b001030182030303907002e03181105250900740101260003901c000d894a11518010821b2420802c0032a810364406901528001490a00740140760b440602a11441c00c40c1c203021440c003009010805000350100407002c14aa0210007407921350902c02020707944110b2800000d02034681900c1c1d6110b591410a081c40c01c6030286006c44075903140120040d40908030101c00d211001c06601c01c4c10180b280c4200c02200080944400e05581c0314000c3d0513907010048088008140130541c100c01902d4814880c40d155214500541d0010402c07610800ca4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 333926699 1250 333925449 333925451
    0x9050f0109020310050f06220c050306030c0d08030a02130801020a050901080703180b0603030903060c07060c1803170c010c0809010b0d050a0f020102030903160e010504051608060a12030201 83
    0x1120441c94213100420701e5510a250030321460800c4a000c00503024040c02ca203120314041203c0c0c00214452411030300501481e80c5040003040314000003e442c82d8811590a8800d0281e50381c1284180b50401c01c20b20b20ba0b4001100b04d043d95070780c00d942c030003d5001036a004c3e81e415000304001051442400200391000455540395120b4800000142c0a08409060401030505110503e103000190307204261109070841e06a071640e4403100b0120f400c510410020542500540c0c2c2001848842c2c0002030250a00c5840c0801840e160b54808031003400b50044003001134000710b0000c0000c00d8607840041c001d105c4510b50145085c11200c000f9003107842840410380450110010020a80800c3c82418006d9000f540c2c084550b6449556817600d80c2d00d01d10b8010a034810100d80d401c203691080054801800e0b001c2c040360318402d4030202e01242421540300f143c00d9036031640000701d0f1900302401594080c10b80c40ca0200380e8a18004001d0717502200c0104540e03003191860900280b000603407c0001052406500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 333927949 1250 333926699 333926711
    0x9021e0102070f120609020112110403210206070e0a05101101050a0c0203040501050309070902030414060702010b0f010305130606171e06041514010311041a0a050d02030109050f01 79
    0xa81001c00a0380041003004030340300104201c0e0130030b195140d19168004000a101c82c3e6a200594506000c40900d0100910704007010501681e000300600582c0e0143c000c00d6240d4400e07040401a40d0031244c41200142c200e000440c8416000d108040b00100000340f0488203035454001007003034140580680c00024084a24030b0304200f40c01e00c10150400c124000910802d624008060742e01d208a220b110304111001000030801d40f0140021800381c2500001590307a41054100100c81e000b00c0d00d50441c40c4d01410380801c1480d401480b44041058000d0144a08400c098005400074007006081d19040c0d980c2c01da88034002404d51043c20054420510042d440a5405490303a00c0c200c41085050501002108680301c0041c0019196601c258440c01e04182006886e08882c0640aa0000800405103000002c000c000010402a150800a50302001000740c00701c1521200184210309541203036810105001904114203601e91044c00640003003003803591692003e1601b01c01c0200d40206075502c46c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 333929199 1250 333927949 333928009
    0x60203040209100302220b0306012702040e0a090812180d02030915030c0c01064a090c0a030501060f080313090c2c0406050a0e0c0705010902 62
    0x8420b103500700e811200c005810364155404070740100d820740007501e048090715805c00010035180d004101c5440000c0c090700d00950f501c00042c00101161200c9040200d607080200c140d01c416031094400b00c802c1c0c0320001c00030b40c94481007078008261030282943c3c41d10f41000182c07a102d4820b820300b0f002d010401d0a4040c18015101101e0078040b440704070008641003008003003a55030300c0f95110300f0240780c0b01d06802e54070303105c800d4010100e00c51040b600324154201034000a410301e0b21150703140e41310303c8150040c1d540046c4500102d146541c0c05440c81d42d105020301e43c91191801a45825440310034103045803442d9502c0400104501c01992013204c0c01c0c0e45031076041c00360010038140744008240d03490055090106200125003081b0b0180a1040030f60350b02c49154280c24810441d9025500440300400c0800d640c40507034450100003455034030b004500f08600001c42d414400724035412501c2c07036201c0101907140c00300c2d40c00b415032001606483c159280e0703040c2d001594603000798640c0c0304092400c6014a01c000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 333930449 1250 333929199 333929209
    0x13020315090108150606092e0f030c0c060510090609061d061c030504050411030708011a30010e04121d010509010c05010c0504090e12040618090203040602030402 71
    0x160001c00300c0307070401c084c0c01a250006100d0190400c10494040740c1705c060040206900f0445696014016101035251000841034a07003041c074801c15070745c1c0f03815601f040100c0613411740d41d070000100000b4520200c008046022640000c1d04490603444500d0410b0765000d0200c15076900b0f0708080c0055907100400c02c13020b01c540b800324040c140d180341c00c001541350010009550340d9003146890961550000903030304251283e07048401030040100204086016150000d100c4d400480385000460030140012410807412213280c04140d4191021602e0b01c032001034580141c01c80228903ca010454800c0e54400c40c43c25200345010b80038501c0c80e0b00140c5001c5c100b504000585800c2c0c1000d004c41c000780340f01011071303030b40c8001c002c48403e0a2841e910140100100c40b5801508800b4000b946440212030f0a83d41c000b000b04225881044c050080010254100b0303207500384591300d088141c0c0100401c02c4040d000c1d203e042e800101440c007074110565243c103050247e0b072080700c0441300150300004000031460300b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 333931699 1250 333930449 333930451
    0x10f0309114504150906020d0603020306130819090302040c0309020907080906040206221e050a0e071b0507030308040309090c080403080603010603020d08071a070503010308091302031509 82
    0xb061801d000403800c80115100c03504003420150a074044803c00ca0100200c0c0d80044a0003a070000046640700a9884100020a8903000403446405100041102800b008003004c180c80d0704802e584e49400c400c2e040300500c210a484503801880641a40000560303554030407041c401404ea2000f01c1d0031031061040000c0c0000003806407051140c05801c0c441c0c201c0f00040e49560050307040e54042d58403114174010500f5050142c50442c07082181800104002d85400c140c1c4c03007561880840b4166131502d607020441c0d54071071802090a16243c21300001c040300e2060700c1c0151221400c0080d1105a50070f40c483d43d082c07a00641003a0702194001c0240800c02d03500801000050115200030040b140440e44024100b43e03000c6d1029003003181c10f0022903107595080d8440c200541d8014100c82c420500392a06404642003400c007035451408a512103000e10036005003d510900313159030741034a180c0c01c1d40d882890035005401a40c0e0070110b43d44044801d400b403840250701a0483d14515643c103012350080003001d00d4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 333932949 1250 333931699 333931789
    0xa0b0303040f031707020613060906050f0d110702060a031e06180b150a091d090a0f03090e0f190b13020304021f0c050f0c010f030911 59
    0x3104100c2088500364a0541c2c4040d40e0303101d282c090305030840d14420041ca025008002c3d40c4841c0008024100e907034280030034000c032001d689500304107a55490060300c03540200070349818080d50130041008420f40a0303200444030072140202d1b9040041d95004144190003880b50030012996170b003041a41c400307148000340c40c0184e803800148039040c00d0030640410001281c0090801944564800100740d40b40d5602d07100e1040041d0310b058807062540c20003401c180b580c2c4501c4214207120303101c0414800c450f10117944603080c000010030f1060030320b0b6a401c02c103c1c01120f06404008040e40003050444a81040901806800c085440720741071006132104d500080d04131180c2d00a2074482e000b40241c56407900030b0210342c2c03030302e60042e180d80d91400410302801e27020f426410784062a002c040d4240c1e8100800150b040d01a0007203900842d503813000e240e42c4400009580d8081000110100c4005201c2d82004290390b2160181ca42003443d01400b1880b801e04000d401e080300612820f0700b00302c02c8016005c1d8241c500c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 333934199 1250 333932949 333932953
    0x48140111161101030f0c0e1504050603180a120c030e0405040519020f0a060f1103130509330117060d060e03040308030a020304170a020c130b13050a0b03 67
    0x90200001e0041c0580030190081a00b6210101d03a07580b607000341d11506031881d00990901003840906c40041603420b20070280352003410514024602240f0f114242d41c00e541c070113011076140d5250300c40030050301d22542402906612400c511680003031020003000711641045c0e1100301d55010103240140c440312600b00d500d0b0040d850b0100304004078400042070a18000c007800544039622290021544000c565010150024000d410000b5060350140110719102c10070740ea0000300041680030a03032a84100082c084a580b0891420710882ca450303c09190024402c2c43c626144074034035a01030010004140c070500000280d101c00c1055540c000c1c28100006800c00440c0860780f4084c000603400c000e42075400b03844542d40f0310303036128a484100102e0b4040c54001c00000d480e0306d07191454001951040b9000c5030036540d407500070f0f0303455a0104280c8159100c1074002d000c18248000a02c019446071200e4021015161100082c554481803050358030340d030310302801040b1483c01c0100042031326040e140c810301a0f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 333935449 1250 333934199 333934207
    0x6050916110f0313050f060a170709150c0b0601020f060f040302160e0106030c03020414010305040501201312031202030a0615051948140111 62
    0x115559454903008040d41001840510700c1d10509161608202030b20059100026808240100d000007090480300f044030a0002c005450b01800040d00441300c002020030342030b40c40118480801c0d0301140d44275040d80390078045030380d407903030140b00c060b50028509000c20b190b007801e11305020207449c09a13400503003030005118440f0405100ca65544000b464444901030403408941058420b00074021000c8009030f5108541d030701e03003800580421003840346c4804245000c12050381107000740203450450340d11548400c003800c00c500c0154041c00300148101c0392556285d03601650f0005c911801041c54034013109081c0c880304442c0800b40f01001726000482c00845021000c070000394881d2041e205481000c00150b1a03444110709880a41405c1d0402c1642c42541e040c0700d007900341c1c003801a2002003888800408040400c80013618021280b00100b04410500303502440e00301508860300c603a60b000300101516400080001e031a510103140003c84500c95440701e400042c4000340950301400e8514a0480c0ca0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 333936699 1250 333935449 333935461
    0xd05070f0905030309040b040f0c2a0317040201170c0d06120b060d0501090b0117060a060f1403030f0d1e0e0607030e0114010b1308030f160224030109060509 69
    0x290317018080c112171045450751039024003a21036821100f44901903200c02c0c442c503c4a100080c03d810200c15401d00054480185040804111030b5495001c0d03400d40c40d10880481c00d00608500385c80001c0042c0c4c1400001a120f04c50b8595024545210390a500d0a480c1c9030f030414001042900c0040d48041c40a4001e04810b00c042400e0101403034106204550554805566141c10b601402c4005805440c8220b004000181c0514000c0e2203e40c41d90b14005941042d540c4000c2941120070038028076540191802e0b00340514090300042c900360082c0101100e0038000c044c100d0452692203404400c0d221030b03e900304507501254100312101c04141041081c40810401c03940240e941c54014803e404240d01d654450142ca42d00390320a0249081417a041505136865228140e21a4040f48076139800340c0c541c0800113400d100200c10348a00a014114039450301c0000380b2400c001903007aa00c00da074002030744100c59050490311030081c41c4000740c401c01d60381c8961404100804803451640705c80e00a050060803c01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 333937949 1250 333936699 333936703
    0x92103010503161802160510050103060f0516110f06010f0f0806070e010e130e0c100c021f030b030327010905090a0c03020c011d0c0609060d0b0102120d05070f090503 73
    0x11080b14004010f07110700c1e031b40301d148803e03103070980000d07105005101460645510380d0b007001381a04d00880040c0002e030301e40080c1004489088030b031f0456103016170240c9014144035503c440249003d9108403880002180b00103414110f00781c0c800441005206c20030080d080440d22820008d00010000d0149441d000d4409000c038181d00c066117040002c0c8018982d441c2d81c2e0360704041001924075104010f11b452040643d55a4541c11448a01c1a142d101c0700007015481215180c111030b50161802901c1603162082002d40600e00f00c11005154507250b044000b51000c001078040607190340c402c22122010307481000c01495000c150241003080c1d141003800540c44c0c032904a9005500204009200301080740c044000b4041e207041d06840b9420b05c00028a0212009403c1d003c0c941c1c000c0642c0c410030341c9541000017610030180d0090b00050240181d100d4503903150f0040ca4400018016581c00200c171004926856109035490a440d598403014401c906034070140c10181d005240c101036228a0405001075 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 333939199 1250 333937949 333937979
    0x504060302030603070b04060f2d03020c01090203060705071406010e06010e0a0b0d02070c171203040302150c07200f04150f151b120809210301050316 66
    0x20141500000441c00d00c1c2c40c00c1162000401c02c134040300340c680d0744800000700084001402c0c01c0010780346200920580f0303090303094982c010808e82c44000301081c801d1016406034200151459141d544c54880c840581c07030902070280f08200d141d0b80e050356040c00d403400300c4070382d01f1780880961140d0018005102c2240768105007504110242803030a5a1440a00041c031654a00d4111030380d84030010403401c010cd4400c0c0c002c1c1800c2c03403040c200000120340358171440306000b250030b584000c180d0240e5040e01c2c2802c0d9603001990414000d10640c0c1080d16408007158030715070f05031900510050001940b00c1840303d118010940710340140ba0801085103c90300180754403900d030022900c581d95481c0d04104403444444001c3c02081c15942e501d407485e545071000401c0f185142c1d8004042070b80c0d6034800441401d00c080c6a501507a020780d125014980d8a40210b4055000070b0050665208903c102d0480031800b44040c0c800714010f901c155078079070410060509000404003154803500000c2d10500040310038032140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 333940449 1250 333939199 333939209
    0x50601020c151b0105181903110f3306030703140c1c02010207210602031902071223030c0903012322050307060507050903030a03090b060a060504 64
    0x1c890440940c80182c1c4900c15211a50000d1100c8507540f00c032240c0640165128500701d00031500124483e4401c40d845101000e035001102c00d0305580d250020b4065440d10380755400d90001c0350083c0081d0824245842c034605480d47c42c4038400040100c01c454006120b0724130030304400034800282400c001003552030249001c0100307080c07069918006803071401c01c4814950742c00180841d41c0412040300745c07075800c01070391826030050082040102e618541d00c0a014496031b2018503409416030640c45900007500301410003c6000c1110074503400014403070003d4410b06005000500121040c1c02c805000380700b100320103080c10301070035040c03544024106041d22750081c1d82555a0740e0314040400041d0040c50680006060704844008082078036074500e44441c4903046280140c0e440105070089140b001a188000401540c4104040c03400607038036400003500408641083c50030102204000781c290340080401d4000217a48004080511908901c1660400801d4651110807030515800412a100d24091 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 333941699 1250 333940449 333940459
    0x206030613020d18021002060c030103060b010e0607031710080c09090f07081501080a0804050f010c14030c070e040b040b070e0301050709081c02070501120e01050405030a0f03050601020c 82
    0x1c03000d0100036011510b960120a60401c0048007680c2900c14103203406000ba4042c2d000c6090303101416000080c0715010f541882e58060441e8619900c21000c0c12074803d0840c100410030320248600d0f10f5a44c094002c9a00c41c2c0c82d4541030240c0741c9800d0504c510018004016064158000c0100d29800f00b001025201c090302c900c0f41c550f60701c604280ca08018131000125074816158009045200801c440b4a81e580c0020319514070b99a64811a540d02200c0c0405403404070100404c002c6031400000c41d400318481818815641c6401c0e844982c000d149105001c8990340000482e12600b40c0240169000382a2070020350250f07060540340c1c2050142c1c010402080c81031800003184840f40682c41d2005100c1d03000380284028a054a002400300c107544c4903a66441c8245c500038050304888405035941c0c05034540c024070035a4075100044550b0a0b0714140c42c020780b543c4042c4000c070301e1828007071584940d0050740195035a040400c001000c2e0400342441c003040601d04418030201c0d80c0d02241c030f00c100b1541160 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 333942949 1250 333941699 333941719
    0x30080a031808040312090f05030c01030e0c0d0c0801060f0315090f050d0c0201033207030207060f0b0a0f030c03081c05040b040209100303020709050408040b03070801030b0604020702060306 83
    0x1c1a015003444441c000307000c444000c5000000c01c2403401062072000e00540d0b803012555901d48801013990078600500c1e034127400601d444c8102d540700b54004038644c1c0410046482c1e480c5924049155909614001e6030607580100007403014180c24000c806c02032803100714014106141d612560606041030001c0700e0901d07221400203050210b01c040141105401070b0a0b07800710603005102815040e02c4000c00c0740481d003090700310f480541141d120704030034028009148060351081c444000070179400400d00b0090540c248001000305086208131060003907042070010760390a03800100700240a807913010f51000d11401c4030500000e0101c14504007226400401c054551010003003000c03042514248807034038949003a0410051003010700c0719034000d500a07142c05006490740c10003d0650080c03400041d0259100c80c000300100e1441d6842a6031150168130b2103401e060b16280304540603030068952900090000c2c0050052008501c11550001e00403202146801007a80c0450460300004102a02c1080000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 333944199 1250 333942949 333942971
    0x27030201110c0a1a1312020a09180213110c03031e010302100c0f06050f0708060103230903390a020f0f150a020a2102190c030c30080a03 60
    0x940340d4081103511107002c04d58440f401103204010321442684a402340680024840116120b40d1414031400340e11a6046042502400200710081d12207490190369094070440d0004014050103040c00448040d40e660f00704071281d0156207441794400c02905a050004100580d102403041c00000c0440c10101000140341c2004d141e2001440809401035061030b0401c81c401010b030000600c110341070789440401e51203030350045080b100d0b640344170302160144000c1418010090500309601c40360700e10840345461084000014219a10450340002240101d880780c0e000400400400c8a81c0c03184006142c619042e0f000180d6040191080c1406200b0503038108200d91030307480f07540354445400b00109a03a441103100080d500c042205081d00d85180300d01c1070324040c0c0d00b030490a101e0218144e0041c8204501c1e40300849100d11070708070464550f15038110010000d19500704c00710080140c5480116000c0f6806c0200070728005010340060302211080d6620002a008001d0360f200301818a8005542104a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 333945449 1250 333944199 333944249
    0x601030f080d060906080d020106030201050f0912030c010b0108011e060302030702030702030a03081e0f0403050c030d0c090e0f0f010e06040e0f030d0b06032527030201110c0a 77
    0x255440c1c2c29a41480804102c00440750000000c9071340441c2258400843d00308201c0c220b0340307a404003e0008404100446400d1349542c06072080100003012050700c00748011803640b075603021810f00072443e515840e00100c00e68020342c40a0040c0b0806415903031581d10010b1184072259180a481c0c249603021010840b55031080003505c62880d400744c201c1c0c1c240c6c2103505003c1c02e440c80894420304407104030260078100850501a0f0b50254501100441e01ba071036a03038080d200c07030f000001000781a100520480c0b41e00c040714000d1070030018a60319040c3c504c43c144104003100500040100c1c41c00e6001000344901405030803c180d0444000c60440f2529858090005014090300021005188110410389000070008001030030101500d0170204841d20441c814089280004c0f03c1c0c0700c41c0072000521140946071900c12481141c445494000905040e0039089d01c500e182ca0348001c40409460342c014411135801541181085a03000d000f0300a010040001401c0c2240074002d00882c8014010002543c00d00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 333946699 1250 333945449 333945457
    0x2c100203220605010f0b0a0212030402240406080c030705070b06010203160809041d060a05060f130b0414060d0f1401020a083102010e0f0909030a0806030f0601030f08 73
    0x1609415a40750003603400c007000039140a000341c19603c206150000392202c0503508480c100100ca8010f4110030220001091132a0401071059030020500c0071051465114141030481542940c107031161180c0c100b01d8010305c4460010898480e50301d00b0400d01c03100ca038001040c0c800c0309134046140c500b84c0d036a0f080100d0841c00390480c04001c0c2c44022446804000c14100904010074080d60b0401c81c03841165007400e044442594956141c0d00f00b50f0200e84111016040780313074001c001400c030709444051a8003207410380740e07031b084040001581c0b035071400400d24043c02640e00d0a000240550024209040000c00d20347c1280e5008280301c010111260402c1600e082c0d060495080c50002c5440303004203078000d40300d00030842d00010090b601100300c3e000c024210150b0f50585081c68104005400681d00554200b14400d403a01d41c0042100080d51603941c9102e81c4074881d0128030051a01d61401da86c0180007d07001502c09031082e0031400103850a140d000070042d0440b60020f0388100304d018181802044e40c41 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 333947949 1250 333946699 333946741
    0x406050603091b03070302090c0a05041d0910110a1101090b041a0c0c1209040e16090f091101080402010921030f1e302c100203 56
    0xe0003100b0400854030110b503a20301a0050150003030440e180d44201078860140e404000c0d442a03101c001b160341400300d5409010600b8190030715a03d095211301030040c0c0d403001950b0201d4080c03038200410107050307001c0c4080c9105903204602802000c446541e80504c0b40a010000c000308090701c1c41e9a8202d074000d400500c030281d0400c2042d40f481c10f182c200049030561103981c201c0000c240e40c0c08a6074903100c0c8400c0321040420030000e0041221070081c0340a03158000d410280d880750700e440740c4808201e01445059480703081d0080216070035243c00b20b220203583c505101044845c0c5044c031400003044080341e070f41001001c01d01e0080c1c001d0b0b899100585156103280c1140c9030016583e11210b401d00a0503000407003080c0a5125541291080c141c11144825249101e0400f0030b00030000d24030840c01b48100d00d02c124078070441a400d002034100c00c14544141c40e08068910b9450740007104031100c1c00941d580b4a130012000702c680300140e0303c011590700d1010480740c042255001001500344040d8201c1810044 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 333949199 1250 333947949 333947959
    0x20f0a0509040507050312070c23090f0f010902070201120203060109030b0a0603051504020d0b0901020d15030c0b03090316060f020403062a0f200703141203040b040b06040605 77
    0x800c003400c140399101900d00800b8080d200b40c020a0039440103d40965100e10342c4080304c88027040c101740c042c54004503903840d002c042c0c41340d2800140c3c0681e0303140041480b4204214114901d0301d0300c400c1003005400c0c1030b84543c0000e4070410295003d030741d0010001d10356101c4030a000d40e40361102070048503081c03119407010b428a030112040c00000c8040d5003110040724064012181011b540341002e150b422001d98009601402000c2c4002c00a6000c11900d03600056010005042900b00d007031600594080c011040d0260340310035414010401140380000242c609030303c102d42580780400043d40d1302d1061007140c044441d0a0780680302080b00e1364001c002c4c40c454016080d0345a41c0d8038034250000e4030400c1803100090302c91141a0540043d460641860846641d94500036500700b106d043c0c0e080a81c2040300d40000d20200c0f01c00704840c01c100800303030046104101100d21044203414490805030044a07400c0005402c0007800045240581e4031a04540c025440d40c005840b0307c000100141010380c080c603000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 333950449 1250 333949199 333949201
    0x3090703081303050d1416050c1002010618140f0a0608070b1b0a03022112040b010e0f0907150216030303050105040b031c05070f0819030c020102031003020f0a0509 72
    0x580300b9a03940200c80c41001101e03000c84100c2c00036620600d20a050702038040303040c4005906500b03485138142400d4001c400f40d0b1100000c00003c42c6190b02121000f00160313441c2c440802c940c86600d140d80f0340540841c0e00800182d007070130103140603191000d0250f60104004c0780104044c24800d500c80c0e00240301c02d50031101280c0d40e903050b002c00b94010f445514101c0c190f010725401604da005c280141c1455060380030b00141070744074041281030b0001c80465034102c80140103508141c404810100d0140f8010102481c02c0d62400c040f130f00001c3e500030551080086000c0030300c032805000103008001c1ea01c0106071150700400030341040b4900070310f45007000408500284000180750301680264103844c010391f0b05121084002052560340c8040200041400300c65041c1840208d220b403004e00000b500c03805401420742034a46500c60150019081038403685005403203079602c0358040c850110040c201b8002075045282202241744005401e100c003900520510368510380a03038610802c000517140041c010352207 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 333951699 1250 333950449 333950467
    0xd23030a050604050105120c06030c04030605010902030103111906050d0f2a050403050c12010905030f0d050609010303080403030c050903011509060501020606090a0c031805030a02011119050309070308 88
    0x90034060700c60b1402103140a0010038103040412661044442c030b40000d12104924805103d481e62004080e50282c0300c083c08003200248441c000c00740244100100940c50394150306203000740d10002140d907445131b24001401414020306110000440341181020340e02c0341c591003000000b41032803040c021001d03840c1209441c0c0b8118040e02c42d4810b0321890780440310744180800705484510842c04045e03e03035480b6020781d10300303490100c180f051900d47d48000850140c00e559219032075070b04204801c1c1c0f018407012407036482c5803020340704581e4042802c60b51005103500d181c5000d0b0070146c0250000e010151504014030b8042d000c0d0040390384018019000700b1100a400c07045100b80c01c81030180400340c50400e10002507a40c4006941c0b8054007008141c02c24a0f02c481c8500c0000340342e0003514030309058580c4005902c010203602090602401000596036690ba40140242101c061402e0300440100038401d0034400c2d12800c2400c0c0e038006060520a0ba40e031a0300d9629803900303145a000074420a00010b0100c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 333952949 1250 333951699 333951701
    0x3050c07140a030e0a1406070807020405070f080c03010509010905150a080c0103060914160309050105010605091207140105070f0b0403020313060804110904111816030902030d23030a 80
    0x180c1c05000c0c4e0399070450040c0140800110070070700d1240700c0d80f00c10742d40c5095100d450444002d00c5140c0c4a100002e1074001030ba8042000d0707034404c84070000807405199000032026004104243c0c400904102d042c650360410001522151042c0140ea08007541d03503000843d05805040340b01d4003280010070340c0070a50b681d032680307654411120b513200c0c6c0024146100002c180480c1d02a020680d01040c0407696039641c2c41607a5845000100801750405403140f1000020036020f01c40c040c040d260555485540d01c000c1414012081056a204d0006a0010004008007280daa0481d0110a0309280030b9650785401c2c2002205040d03a240c0c094042c40100040c0010150008014502c03c40802010202d95031f076050700366041c24040f40c0c041e0107040b17052109500f501d0321108007030348507120b11003001c1d1b404216008200e43d04007000c1c0c1002658040810310007013a40c500c108440c0c5107581e00d01409116032a80c0071070746940f030111102040c045941070403c0c43c610821103d0b580c5100d01c41c81c00e5280e2408440c404 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 333954199 1250 333952949 333952963
    0x23070f0804180203010510050c070e070e0a05010f02120c0c06040e04061803080106030c0908030d090606050f0f0f010e03060901090b010609080a03080702031c090605010b130603050c0714 82
    0x10200b0300c6000c41010350005402520704840b0000c0000700c4020720f64405550b1580140409400360280803000321301c1514900045019044035901d049001c0b0881051062860107030304014140a0a041103821142d400295074040010180c090750f00c0c0c8950f0000d4a190034902d8203065031241010030003103294402c90401c1407040e0b00500007030011004140c20000c200b804120040d000420b42d80060044a00a400a01e4a5802c03490305450007a81c07100030f03500390b4003e070340f256200c0c6499012141c1400f006003d0b030b00140c081194007110341005c090018500341c400340b000e0b41c094000d0038000f80250780520380d1508404005000d669091401c92b40c4a13000305290b180440f1903003100000800d0051181c0444019655071500501c1d1000c8640c07002c1e601e1010003000c45045100c00c1213243c4000c4801c0d142403059624903140441c4074121858a0820340307505800c80d48280d00180220b0351911900c00a18080345d4045c1000a090b49680f0f20020301481206c0028144090408881c030081500003941 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 333955449 1250 333954199 333954209
    0x305100b0711100210091a01092a090f0303121103090304050f0609061c0e03040510052a0f1005060609100207030602070b0105010f1404090b030708060c0c0d09030323070f0804 77
    0x181f2180e8039012030408807044484650808883d03008504455001d092003c3c40c4035000e401d01035196566500c0c00411a4130329042280054142400c403c5c16030102d0240d850506115801c0900354600407400710354901880c03140300e11458080c07603649034a45810301114600480609010b42c0c40c0082070300d66929039082c02600344030714034100d404082014084251001c0e10b900618100740c2c1c03e4990380486c0c41d0740100c0204414650071001c007080300c050644040007602c2503040603003600e0314079401550501c0b6141c115443c0035800c5c001004070076960081104d000704003c84040c40c0048075034004030300c0d04140d9080200080d01c000380c4281405038011846048030f00036aa21301401a40d078500701c81d2070703581c41c440030407004007844180007601d50b40d00410714426002d400c5884941d902c1224070300d084c500361810f140b01500020030440030b0b0800d2100d00c05004090400c03120040c0796541c01080080490142c0c03505151803040c43c2e8002000104580c00ca5800c001c01d801c6020490038179a841ea0700c036102d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 333956699 1250 333955449 333955493
    0xf1d28050a08150411060c0d2f03070b0919030309021003140604180822060903050607080a0207050313060801060311090409031404060305100b071110021009 69
    0xa0400800903400340c0048101d0701a1411303803541c1d5100038505015081d06a0700070b01c14850900a000d040285061000c1623a0f00c8098000d01030040c504040680c04020702214085405100745400c00011282810f134400b400c1111070351032040050600a0700003403610114401d22203a818540c1c903810545d0a41d0003144d01d00c2080302e800c80280c2c119960800c0c1c41e050406003000040b481d02e8564000b00c4000c6000c0d02e01004180165581c184d40c2c1d00a10884c81040c11141300742e8803042d150843d030000340010b03090401f08681941c44e030503a00c3d4001001c49003080000c200140312858140c0542c0d01855010b011280c407041c181072100c65000c118081c080015000d0f100008400d4424044c1c03000d040325021044c0e00d01803e0f0070501000d07007003c0d0742c01d4050100790f000c0d004554808000a00081000d0382d4001180d04000d100103000c42001e80c032058522b01c040c800c80c4007003041c040e404281c015044880304449254103a003030742803980c012a002c00d40e0b45400c0f103503814041d02c0d0401c01d09848020075 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 333957949 1250 333956699 333956719
    0xe070819062d060b2505070b0f0301140a080316110a090c030b040506100c060212090f0d141206180c0d061208040605030408091509010f0f1d2805 64
    0x1001002402442c140126601c42017103915070095002c10904007040c0544180d6880340d482d8801740d1a6544006811030203c03000000410010032001020740030306c1002c480484101c0e181c585110342e28040c4003034003001c000c182da0000d030800543c08201c2a020a002d4034440b02c16903100000c00040c0503c08000002c2420090104d01910b8984201445001e0080c03c030340350044040000c450544034241d080781c030541d00700032101060751146003051041018400400391245010304542c206207007002c102091214101440c2c8001c15440265444440c0b007202e800721300d640c0c040c0001c0b804940090741c0d4030a44003031814440d05568000003002c607480031480602203c2d40d659810b15000800303c0026080389170921042c01554071079002590064003030b007205410083d1020014a481155801e2119106800182407016581124a00d9985007007402c01144515104201902da51009183e600014007402e0101202380e55150103c402c030340c00c0c1007054014060a0829a520000c00d02989101d061060 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 333959199 1250 333957949 333957959
    0xd0507080a0c08010e0a0207110301050907080f03040608010e041e050609010c02120301290d0b0423010b0c030f07050d11030f09040203070e060d0f0e070819062d06 72
    0x182421304aa5116006080f255103001550009401141d01180c0055001e182181950b42c00d000d841d009040e9880a001c1c142e07e460b401c1c1d0f107800c154840b90807458005202c02c001150704400c4c468112084400d509855a0719450f1030f0405800b074495440c950550380700c1600c14041c00003070092045d13290741e00070003e00381a84030982e9200030028603448903480030001417001c5a41e001402520140d5200b400100058140b403890540d0040e840100340d40d035a41c4182e07140743c0307010300881c01007110035415407020f144d003c15461001481401604c1c1c840000182c540042441001290444200c070790180b500c0d4401031070034507110f100c5403c15100164800c010444600707008000c4032f9450200b401600e01d8090042e0911029410040ca100148103070440b02c00a41c0d2a044002c0c01c1211090b0b0000455900881c1100c1c21140110b1012039a684003050a210708540015030701e004c495080340c7c07900c400025117004400303012080e02c04500754201c00d480001e010884400203440c250720720750520080c3d8440d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 333960449 1250 333959199 333959207
    0x141e060601022805010b06030f0703110906160809060d14090f03040905090c0a06172d10030c060c0308071b020f450705040b0f0d0507080a0c 62
    0x200c1c0300343c1142c02040040b07801200c01c01c500f1100b00f441039002160400c2600002801900308582c2002012054410001e83e554036200708411104d024641500781041c1310040f40c500d006000e0290070700d01c444100301050080650603500d08060080401390b4688940e03131b0780406081070303000d0b42e07200b002040080f55280401241144550303007850003c506042c40c00d9201c50207000e0141010209010784802c07880c1e035844032880c800180c0955181c0c0c900c0841079841208045c0c9004100e4602d00105101480801d5005e90001c036681c1c2420b110800b00e03031291003a01c1c55542031540001c0014100d0703c0000b41240d042502e8500d4140a03450b0300d421607a4141042d58003040b0489000c0006e0540a403400052810100c200e01d00c03080506501c10f40040d4024843d00c00700106000c0240c0b00210000d4030a804c007050b000c002c2c89204505043c654104a40c000d007581c0078a000c0c0c2c401c20400850045000e0300040261034140c0d800d800706102904050001030442c0005480d9902c0060900c0b401100321070207 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 333961699 1250 333960449 333960463
    0x2a010e1e0c010c170415030c080906090714150c0f070905010302060f0c010b030a0c170319081f0303081504020306010e10020a0c0b03070f020f0316141e06060102 71
    0x6840b01c4100e01c8081e130ba400009000000368801002091001041011600c001c1c041180c403a074400045e262401280030b44542070007003d00031030341c0c400030400414107c00703c0da0b5822241007014030b8003d01d40c8240003444a502c8405048264580420980580c0034005615080c0640400c25071308580e031503007024804e58500740806174109204111551842403904010a1100c650800006030804400002410326092070b0060300e1555007403a0503c405000c10120041803120000254945484a1401901b110b01c0702c1b41c0c0e8003131102c0b050002d40190b5071003160500d241102021101c50607200e143c081d01088003542e070300c102c900c20071102c81024103082c42145c0c05104143c580341c00340444d03901003016503040605000c046006001c43c01c0001131100e40b045001c1d01c41c00f10070a0310791034801c000420403c3c420204000b12751008100e50b14150011044601058090328035266441b400e041402e10314480794000640380c45414800c11320208070040012441045006581280e290303c0012660341003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 333962949 1250 333961699 333961723
    0x3040f1a04051b04020f0706050108120901020c040b0a0b03040b01090516020c240a020c0310050106270f06050307030e0303091002030910060b0703030c0c03052a010e1e 74
    0x4410f03007054460a05840d40681c0001d4000d10151030164112404411a0070115003100e540791100018080c070841482403102d812149000325040c40c000e0301c0000c3d40e5143c414100b0707003e1965411240e10940f02c08000320301034a10081c03466a00d061900d000340b4844001d00c01c80c0d0405252001003501080c00c00f139210f140c407121368004c0c031074240031900300403401e0408070f007076001c0d00d25140e45120700d1840c1c030002c1e110f03d50064002d8154201c000c01418102229007001107003007031800c0700501420760458a00c1d8014403880402c0c4181c40104d0543c4006190150044800d080440500281075a40000154466443d0744d4007030010804a13000d01c1c0e920b00059403882c1260300810301038a1009595400755501401103003c03242c92080b001201c0080f64016009041540800900c400c01d01d07400d80a2020094013a24000200100a4800410900034003a0b4031715031207820700814400003005513100d144008400000c20212a0f00d050300f6603203200041c10301004519080340c000b0000d10104400741015 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 333964199 1250 333962949 333962953
    0x4081b16090c0306051003060603051e13030c320109080a0c05030417240702060612210d0f020c0a030e0a2c0a0b0117060102070b03040f1a0405 63
    0x6400c114402000c0e04058411904141e9107410014046c1d03162080b50300740380c60f02e490024010341041c100030280d0b40010b1509400d403803400400100c69030040384084c1d03c00b0590036900c0201c0307e0751070203c45800d070641010381600c0d81079800d036681c001c00c10300b0000c4015180c00206d81240c100c01005081e2200420701510716a4140400203855000d418080328042c821810f580c1b600da00c0c0d0050032607801404481c01050b1707218000035000800c04080000104c00001003014517407a00c034100039910640100082d018101d03e5800315144003080080e000906607034501c0d21034071000c00403c2e640680140c0c03500c1d0b01e15414030341030200030a454402c03100000d4065014055004440d1804d640b000300e002c5a280d0050820036002a41e101b11006030003468802c6203e042580480c02110305141d00d0203054a030b561443c000b0104801d80c0c1100500750041e003880b0601d135442d501e4000503070800009074401402103000008020402c4200600101070a205d8019000c46e4084424003442085040301c006040c1c0e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 333965449 1250 333964199 333964243
    0x10e07031415010c0212030405190f0b0f0d0203090d030510030b0f0903070b0a0207030212190c060e030a0521070912110604090e01050916030215090904081b 69
    0x1c0d1182ca10000303075402c1810007041d26001e0b540410280c4200300c0c9801c1a6420100301800700c1d20700f11510f03000d598105084110224203040000003081a6841030480030b003800030b05041c030641064140c8200c03900c2400c0464991030440c50f0941c503101c00c01c10500019240c43c00090500c14108003100661ba040100e0001951b52490310040c4000702400c101003611050260701d001859051925109862071440541c45265615010b0b1808098035013402e07003000180045c000243c804101040f0340003203403030b11000030702c0c281c10a80001c241e40080140383e07000c0040d43c800d401d80c102c0d0040001842c000701c0c80d00b10940d038400d81d109046080d640310f40003a58031441042074011021704551214050001c2003c030386070100c002025940141d011040e100d48400c1d0000540e0b9081c401ca42d880314884003c0c010029052008466a0b40c10b80402403084403001e000c01002401e18068500e05000508205402e043c1070800c0b100c950400720b01e1036401c034510360031000519400b040801810b0032020380daaa00b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 333966699 1250 333965449 333965461
    0x10020a03090f0f140301090f120906080708150a09020f210408090910091a1801050a151107090212130314070f02030d080702010b030703050709090c09060b03010e070314 74
    0x480130704141c15503056403141400c2010641440d034903500d4900c1405943c0b008400a80090b00c0581d26920200030710a1603c2002038540d040107440e0b6202e105138014000f80407541e000140c3d04102ca0b044445224404501358500e425114010020404000071140042100c3c0c50f07008030200301103900400b510020f004051103401c0000c19640c00204a02c0c07907040c0390f91900c02c41d50071141e840c19071150340e4074881c608201c10b040c40198030005840340c0200c19407079030400f008510442c043d403044140011602c8016007038540700c0d440c0c10300c1d90b04900082c4c0c0d424681d148404d601030b40006003001070030721042001c50901048000c14100007070341034903513078580a2541001c4d1104e8101752403c0d21855200f041c031100599090001d1200d5600d243c4a025a80c106400c000f401c44413000c0210b40a94002542803010900011b40d403c00c46070307005404140c0b61540d02d880f06180b60f5031340c0302d401c0b8503092640109282003d50080e605890340c000d014030701075a40300030807019106c0841074004100b00039004684 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 333967949 1250 333966699 333966719
    0x30810120c0608040317070305060f01032a050f040f03110d030206010506030c07020325050d171803031c1104030308270d09030b0601020c130f0b10020a03090f0f 71
    0x503005001b810300080d408401c540107000010111100d00010b5918800c05c05d02e85084040740c0e410074402c4ca000c1286004039046c401c140d54000b6202d180c4900ca0aa48a20390391081e022250805072415009454a41c1d44884601060060200310303080540492036800c0c40c1894416251140c0d0191b0040c0026441d10040c0030b00b540c070144c281011960700300002005a241001540111303010a1190511841800c0324003131980856005240701d01c086100900105101180001c054100c0c4021640c0d60442c0e110301403100245051207030b41500000c15010410b40c0b1030708080c034107041c004178140400b040f0320540d0040da10981c00002c01140e013180c003080c600d030203001090210f0b00048107005803607040002114640028841440d001684021050041100c159121504601e00b800285000201000011420001070000d0041c0715138907030901500c4840c13600f01070014a000b6050000640f003040001351103180030b00c0c1c01d42c00324901840001d00100c036005600700310b609c2c1e1024100c0032030400704200 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 333969199 1250 333967949 333967951
    0x50f0f030702070e190506270c16120305090313060c0201090305071712030103030507032a060c1106060a05270c130902090102030d18050703030810120c0608 69
    0x404500c648100400c00140340220301e401000107040a0035420962a1782070140e85004007401d009140700c0d00294500c046880d44501d6540c0001c040c0c102d15500e214104100d13010b9100a91042e540310000c00040c400b40080080d100b01c081d640500195450120325552441819030720351304840041d40c2080590301c2041200201e40c4140f41c0f4200295694480510f0b14980e5000040c3c011000c4035100b5450343d0800c201400c4121418101d801c540c9581c401034a01c0c0036041003d0705115003441401d2a42c403000720900d1404541c0742c5401610700a0b410990010302c1c01c8008403010a1800311104180c15000618030301c00d1078020f10710500c1c6070a144c24005012110007514050342036245646900c0a9101c1c5803601c1138080107807550710303100049121204280b080d8007400e0b8461040214208a076804001c50701100c1007c000030608042c55001c2c01000d60070301c8400740035030003080008400c15510042d150b00440880031240c0d8a551200141d250141e20030f240146103240e00101040300300c0c001c00300f035 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 333970449 1250 333969199 333969211
    0x105010c080d0c081005031603020405271605190302060f040e040f0b0f010b12040c051f0815400f06090b03031614031810050f0f03 58
    0x40d08080200700c21406540d140001e841c00728100b036003080b81d4540211701400007040708600400d8a078008a201c4003080405020181c001c86c0c40d02e000405920703591104020300340111030a510040030550203161a6080004404040c0465020004070342c6000381401c44490400c0c489844803614540c03c116265005011211038403505210000d4140b00d4101c3c82e92081c0e0091000e0300b0910030301e252401c100c0c8001002002c0b80850301e80140918034021003613985051103522003020715140e505003400403542c19440380c1ea1002c000b03501980341901c0b0b0707015414000c1e001d840704032198803100da00800c0156841c0d00240c0007484900d00720000d9800b01c000003c000b001d11000300c035146160100c09464240c04a061019903102d80c03009000085c0303442103070018030601c0402c1142942c1c0d240000e4580c403c00800b040310440e8a903071041802142c001941e0031070309010490b943e6090050b14082c0c0c6903a080307030852040c1c400c181c241a0302070003041102c070418803e9010358500089000b80c8540b5801c09015 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 333971699 1250 333970449 333970463
    0xc141003090221060a0e1207030c0c0b030c090a0807061205271e070f0302061c0516020708060601080718030f032d050d0c0e0d060507080f010305060105010c 69
    0xc2e0509003194201034420458140e02138441440d0924083e0107a81810441140351761010003840c40ca002400d0030f81d207103650706180003a100d0a45051084c494019500010303001800007050103456a00d80c00140754042c4250f88d528212984d40044503102c40b4244500c0d0701184422140c0e01054900340e00c1a40d000118031180381c01620402003d41c41100c85071f14041c40c551000c10040755441d0040407424032030038900c00070b041d000d0508200e04600c1885100c001d004040103d0170109403400c220107482101200c40c8104410324041d0b621078103040c40075100d54090700071a0004101e0442c0031510520490042c0c680e41c0e569142c0300b508860280d507580c28459130203402100400080c20b025021032125000b60740701d500310440d021032041064000e100c16603800f10b0350340b070603440301e0f4226080d1210062104800245c41005403010780e21403000246131a80314500e090070a08102c10380e4003a0f070080c105581e40113529600e03440e1000b5481806c0c0030103030180d4401130040002e50f1190801d01c038954403d4403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 333972949 1250 333971699 333971719
    0x9040207060f020a09090b06040e04150c05220b0313082502120a030914040209060c100c080103050c090703090210030501031e080d0b030705031204030c1410030902 72
    0x503110215400c00c0000c0803090380002e01211341d150f22280600190407a40c5c030070004090b011000030910700c550300c580500d03415501e00060602000c10f040c600001c007a510140204c017182d41c0c00510940c404540507020204d503140090401200319102c0c806d90f0050f400c2c1c5840c1d9241e03200e0303610461205080c00c4806102c00c00c075065080c00804440100a060030344401d115003400c1c4100000c943c081443c01c1c0e8182e2100900a01190b80803001340115116941d1041d688041038011401910400b103001b0b0b08a0800107030f40b060072400183c0038400700c49030781c0100b00c0c0300c2c1121002c031002c00c001e01c000382c42940200511b038442c0ca040c000c51504242681000222914a80d002c1100d030850300b0009000300e56100c0041045c001154802c0b804a1118618000c0c28003240e50303002218000e01c407030302e11540e940c2e1010714010b885c1040a00d001d46030050403514000080e5980140380d51013400112820f40072000001002d0321701030000c260040d002032130741c1448603010b50118010b04c070b001c1060f41d101500c92 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 333974199 1250 333972949 333972953
    0x2090604050d110f0402070201270f0b040905060d020604030813030f05030a0905030c130e0708031b070501030b0916030609020301060f08130302070315060b04170d14030c09040207 79
    0x1030341c00e818144503d1264106005003020401c1900400303c03210f002d2401041030100503a88142e18001d0f0140000e03c910050b00c0d0804078512014030364100414007140c902c00840c211900c14040d10072103100c40401c0c0100c0c0e0740d020508c00200440a4000e41140c000e000501c0041d20000141c40001900c0c1001088150b070b03602c036440600d0030b8180585e0305820004011103025845101c080151205034003c0008540360707030201e010b44120a000394100c0e9918140c0c0440c0503005d00c6a030004105420807692655042c0e800725920b40c112015400f414441c3d450001040c0d4042d00440c1e0708210010148100c5039550b200c10034003161103603400c80c101540ca0402058440c81c62000d18064480303540e41ca900700d03203106000f80408501505504d841d00171059041c0000e503000882600340d9a004134a0b00e09400f814015001429a580090b4080000810081105800401ea100f08244440c04640f192000340c402594104a02c20041d2035000003040090b800650b032000402e111540540010f150101035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 333975449 1250 333974199 333974209
    0x51c0509061605060708061f050c030316020d020c01050f0901030e0106060909060b030c040501050a02191110050a170717040803060a0f0b0706090305071a0a0e070e06040209060405 79
    0x3a07002c0514502c0d48280300c4248081040340c198000858108051a8181980000d010a04101203041e84841d4000c941d010300380300d401a00e100f480341508803070712402c00b60900c0045d1048029000b0051081c0c0700b41c0000c0c40d1002448050441c41a141c084c0341030b0685000e29030315031091400f203050640318030a1400088003440380300000e06080d0b0b1151166814803041e1015a800e80c0e00041c3c518200380300f0f01c5400c001c00d40c11038046690074200306507141d0402d042a41000c5804512080300ca00e60181d50b030600581d0303159900000000c54050315000c5500000303941c540186009440060340d0424030704080040200701e20b8000042c0d080c0502c094104954011010f071044400302c1d61b110300481400220b0504a49900c090030405020002c01c1e8204464031015000304003014007141e882d6101c0030241402082124041ca400c1203040306d507501c07038441c0300b40000b005481e180f10451400d05410343c0c2c100301107003c0b81034400c01006441180c031800c1c10000a5000040c40c1035010b4010000090769030f44e1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 333976699 1250 333975449 333975457
    0x60b1c0f15060b03180d03020703020c0d021c05070303090626070e0307140a061b030f0309141b0316030f051c08040c050901061b05071701090203010513051c050906 72
    0x81240c0c4004400b11217035140d800d00d0071303c0300c40030141401400000000313500840c0d0341c10210020707150042d4034141400000e019a02c400e528400981e6403a8088040c08008101070080d607012740c58861706a560f8000c116494030515401c0304007003001223480300b102c40007920025041a00d514100180f00c20903800641810016885244100d07884d1340c040d0400d050000c0e14a0060030396003840303020f020f01c050b0450700015070154002c00708140070580f04005400790340120300d030b940c016010071207040c8000383d640d0b900d000964050701015007104012800d0328000508280700440d20100800003071955031140e4001035103000486183c01801d42040088028201240802e08590795010312030401c2d0401c948400d00641046021700386510060000c2d07500045440106207040705004080340e8a42401130a0401031742041c04c041d51040f40c49459903405401010003580218020040f40e00c03684129a601412103a000348260458a22034007010b51010344038012008030306185240401d010001417444e40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 333977949 1250 333976699 333976711
    0xb1b130303090503070e0f090a0f03050306031501081002090303121006080c28050d0603050d1701080a02041e060e0a0501140102120f04030f060b1c0f15060b03 70
    0x92480010800c1c580c1c480542c200511058001c0c0114504080d040074100308014400c003114a01940801c0306100200407046241e504048401c0c01d600d2280b130020301560040c1c4030f5610910803204d82d103401c503458690850403503259000500c0580d20f20000007020750800503642d545408240440003201809003240c910410140242c07001d200e040503800b030070070003000d88802c4025000f0b100d10406000c80c281d455079850302400309140d118401850407280f0380b01d0008010b11150405030700004100d8001018100d0603c1920b500d80841c00004518109882c00d03c07580000360701903070725800076040039072280740311400c5c41c010b01810341078814088050380c610b40d20141e120840c1c1010803807006180c0c4100c0380906a84220a885504080e0000b581c80003042800c2c1c60441d00052099800303116541260000c540c810610129070900703043c01d00040249040300c03409440d80c5882e490744e1014101c044503040e5440480700e80c4122841e2030742101d081300e14024039052503681c4404180415400c0c091840340c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 333979199 1250 333977949 333977977
    0x2091c020411120604051003140114070512130227070e0418020f0126090114010f0603091e0f0218011406030916080304170601030209040b1b 62
    0x846910500044440b8080c04549120051000469502025002e0341d001031040300c021607592100b04143c3c05000c1b01d544020610440d25100d2032013054190030880040010341141903c5565000d0151841e2007242c40e41940c105614001521801d051401080b4150000d40280d07201403400d5084d281006410050b02c05e0345100808101c00b2a034415900b03540e034507081e1814440414001c0840c0142001e030407000b440f4400264114003181d01c01c501000490020030504030034092041c0101c8004101038406c95190f50030041d50980c0203080003042c90488034148042e0045600c1c064007103000706242841118441da01602c1d098944c0031603408550748501600d038283c551900b42c0704010300c0302252800203050401c10401001030f200d11710954140c80005903503c0d9941d86d01d0725407043c1800e1102e0380da06420050001c0200b142000003002e00151840540313090722a200e051041a9121424440258065140c1c0c00003030002d482016403507000f0a14160a80604c43e80d0010703e01180c0000c1c409403403030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 333980449 1250 333979199 333979249
    0x31209050a210302070804030308130206210f090601230a090204060e120c0d1a160810050d020d0203030d09151103090d050c21071202030c0703150209 66
    0x220008a0b818a5881c115040c00c40c40c180c62035a81c1d07586070155110140c140076070b0701c000684031466403d110b0411580107000c1030fa13a0099404c1c403102c0000d030711181004408a440000d940000d184000d50050111600a10140e03190018140c2d61030502540c0c004034203003c80e80e220075502c4030841c04001d0050b0320809a201c40c108200100115480d44000d0f00c1004060b13024260210045583c080e0140140c480201c0001642401240b007a001c010030b041090f115420090740783c1c003100704050728400d0341c0e45119541d12240e0209a14290034010b05901040781008240107103440961944172a20140507030f800c1c4040e04100034100e40d03c03102c09951003000d1210210b04031005100d10b0200e0072200b1041d90540c108030311501d83d604118103081d0280100041d0401c90210100151161210821401e1006042145c500c0c8d810350807505048440002030b090041210f400030083d98984a035210050200ba8a1500c0e0985d00c20403207002c8000c11a420090051951140f088200d5440d0480c03030380c5540 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 333981699 1250 333980449 333980483
    0x405030c01020a02030d180f060f0e1005011505033630040f0b0304020316030807060f061d100807060201090219030f06050703021b010b091602030403031209050a 71
    0x130388190701c501241c01c041f0000713600001102c403000958a00d400600000d019078148400784000c01d020718100d0080e120300d00d000c025202c850b40205050f6049054a8001d403440c29200380c400b800300359241202c82d0000d4a4a007090700c0e20008604ca4030442c0c20741d80d0a05881001140d0074003040b5100c0092503800e02420009561950361000d075445c10a0501c43c0c40c09207400349180f040c441e1030146410078000000850155501046610b0100c240d9074001025185d480c600351145910641041f101c05042c01c10071039a07101c082c402c8100303e0700d06400781200e2011065031408540b400901e880780303504201c9000304540c90200310800c00b41404d0f07000068054258010401900e50041c1602e0001a07003d8041c400264180da01103d1198415400318203500c0309a8107502a0107080c0040c40c0c020b05090456940780c80c1500b01e2480900c00340c4259006496204000e800300e90b6010700e00025900401c0104002442000c0082c0664405030340040e462086a9503281000c00061098a000040c007441c008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 333982949 1250 333981699 333981701
    0xf16030e1207060c060902060309030301090b03010506090402040902012307020a0b0c03190c051b090f0601080c160c0303030617030408070306111e030702010c170109050405030c01020a02030d 84
    0x940c010003224850030040254103041c1c1d40346454010700f0f08000358041940c003000100c0e00b240c49030300e80c010300d00c075284d240c10a0280e50360703002441020700d5941026003000c03050a041c445d0a000b9034020300100065600c6409000107001903240881c1000400003504544540c0c04410402c401d5501d05d406654100d60f00411141c605650400100c02d02c0400032280c030104000304449250400c400c1441c1089105003041c0c134041500b001c09461401003120b9a1640282e030900c1444002080b41d01c41665159402c0e1440e07540c4044411a002c61982000320700801000c00281c40c1640e04a005c2d041c21000c41da8030902041300307d900841c042512400300380003944e40c601c543c0040d01c00e030720021402d00c1d00d01640603980301d100d03100c06401d90b6620120f91089200400445075510040025041c50020560380d481e2143c3c0200d411b40019481e10300303007400544c401d6481400c3c10561003030360609039080484480080401500031102c41c0b00070881e19280d44828005032008410a07005143c4440710081640 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 333984199 1250 333982949 333982967
    0xb220501020414010e09012c0c030601090b03060312030a06030206120f0106080f13151a100302040b0405120a050f07050312040302060a0807110a0f1101181a0f1603 72
    0x3818405d504012075056210440058115410b140c1250041d800c0d403d2205100100800c403000312035210070030440050396920055005000a9a840f2420f80c1e48001096143c041900e079035030b143d0400e030f49100d040300780c5501940e003000000400007001996503000604560001401c207003580e8050041049003a145003001d07004152509041c03207540742080d03503450030702c000034054005001003044550a02c200c140c1141882c400701d4404014980001c01842d605039141d0003903500c0303074205c01e03140c00c4140c0c401d000340c03030454200c048070a0a06041c4403c121001400810501c030750300c11111600d01144040050000380f508800140440c14240002d050400102d2150b0b01c5a09100300000c100580310401100c005480c540341c424901d48446108541c003c01e58000410b080c0304189018091240f00948031550313034070541c4841c4080042ca4015503101d040403505d20402d036016081044400d0040e05000040030001d1401450121001503194147d040040d02a90003001560710108041e0441000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 333985449 1250 333984199 333984239
    0x807030b100509040302070306020a0512070503040b240d1407121502250c150528050901050c0a0b0109060302030d1d040b03070803180324040b2205010204 68
    0x40e003d0780c030305901c01039580d60541c407004050a50020369400b074603221b9000d54068005c00c81031040306007000301d4000c001c4d03001034802f80c540454442c0428140f440700401512880800b85600910a2901003000f040c4440803105403001e141811031400d002c07501380994809004c042010b0260b03201b96041610ba189208114403030050301c100714000802c600d80d264240d4098025200c0c05000405150601c0340c090668040100c2c0011030701c510202d00d03040b00107080f00e40000c1c9070f110083c2502400402049006042110110f602000700001d554400d10091038960521030480303006c410305545008600409078400c0c01c410396152014011454140b1403d0b0f00303c240c901e00503201160004001d01500c2d8004015403203103940d000d0610700d946050049400801059050b81e0300c600d0080200282118a032400380e00c00d000b0400442024a0060002d4408211500b660ba400340c0c3c0703e540300c19080602400f8030200c0ca80760b840c1760350603c0401c0070f590f200500c540d00145e1290300e000414027485451003c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 333986699 1250 333985449 333985459
    0x60e060c0a08040b131a0306120c0907030218040605101107120f0201080601031a220905010e06010e19020d0902101812020d0f020105130609030b340302040807030b1005 74
    0x8007546d001c4c802c0180ca8114a04880900072542590b0400b444d04d107604988507003185042e0200b0003541e030160301610840310074034038a9a07450800420842241e201d030003020380c4107400b00952a85180314415095032641d2000481385a80d4644010007404102114115041e92aa010311011542d10080080d0044c1c002e01b0180000302208101301e50f940400080d50307000f0040030351440080c01400c0e0a54007002d0050384200444402030030a280a014084913021443c403c0100029003000364bd56040d01c40c441e001e92082030300d01940c01b200c02079401000110000c0785c9680d000c40c0982d030782c190780000102c0340d40c940c035021703038140d0030359902040c1c03151300c980c12050290a5400c050b0b240c210b08a420560310180300109600c10707100503115402a0080e60300c072120b895001180311390700070001700152409540000040d944030a81a9144c18003210301c4055540c00b618680792011141c102c0d50f024061606015003440d4580400c285031022640c01550b00405d070302d060141070703041c001c0c4c1d40700549000d0303075 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 333987949 1250 333986699 333986729
    0x7060305010e0610020c0a0b0903190302030d2a031e02130e1e04140105010503010b0d0210120e0717030f1e0d06061205060a060e060c0a08040b13 64
    0xd02070740160000304010b00514640b201341500503c248060302a0203070050403210000d489101d005090382115080c18083d205244081c1c0c60001011f00c01280b0942c5035000b10315003500040342c0806071421034000e020281c440291407440d5491481c881c03840d6003480d030700041c4881d02407100e0103000c00b07034881c0c1848207031041000c0034444850164800640300259800c0fa101d44519010312450fa4000400d804182c100c0703005c5c00104003034411010340d0012a14000e02680c1d80396800c05088660080900340e00804400c1d0480c0141010041c415541005003014081d940c0191410015a840c142001d1740c20780141005002c0c1134040b006800c201503e0000550812010100140641c4210384035101e181ca42152101101541ca00858401d1590148280191b070369491001d443c0c1c0c0d007005030340e14003641081c000404504000c0c28a9046031032079554011904a88001d00030650b1080b6041401402907081e110040340007a402007000344043c802240c1d9034051015245c24089654111080b0104161 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 333989199 1250 333987949 333987959
    0x210050601020309061b010f060611030901120b270603120f120907030602070305070c170c1c050601120b070c110f040209040507030902040e030c030708221203020706030501 76
    0xb00343c9148084c181c0b0030580e5103000004015440c3e51340d090021040d828928000ba070303809247c000c14200d44050b02d54040001100d610305490f8013800d0341a90005250f0b0822901584c8103070044541540050f001000101550320800300b0f0703200c0400c80300340c050070741ca05000003801c0411014841c11003406010781003010081b80020940310b0441e40c036640140c02004144600f02c14801400215440f480071560340002d40750103449600b000c201500c1c4104000c0300011a410585d914901c6101c800f0003038003e010941c401c108808241c1d601c04614640746c000d0070800a282005014045c1c998403a40a104880134507041c41c1c03d0000034121410072410074004000248840c001800299081313030421504509180840c0080c040c02c40349940c424105000c1c0440203030140c0c07001420030b0003038506000421079589856074138030605617122b0701a48100100030110326501301914034042c0941a0100340301e650600001c100d46c0c1500301c240d607080720102007010140c0401c4250000c003542e01b0300b802198505 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 333990449 1250 333989199 333989203
    0x4030302150a15030c0e0105010302030c07020d03030f15090b011106181c0302090a05151602130c0908010506030105070804030e1216030c05040218012703030c03021005060102 77
    0xc986040d9010421004a5580d40031508014907a940c446080c5002030303a03a0401c9110b6040c01d01c06c104c0c1e42d00d148000483c9951084c02103d1048000ba10440c1ca400760643c00e0000c061500c41081d82015610940380610050318045d40c51085410710710075111031f05200b01c01c8112203019103da418401d1004d2203242c5107001145060340070141c1d2002d00b00705101e33401600d007400c24010031a2480225006109982c58045c0c1c0900402c103402d070b4075440340c1d54564003407022006411603409205103041c461001056001110003454a1014100048403c060000c00e0181d4003500c1d000c40c00301d002c0000a205c044000d01c5042d0348403504070000e018505218201030444940600050104007243e80e0072070b005d4441c440741e4110fa86091040302c045501c120120300e01c40c400b03800112600505010001402d1509000350b0310040b0010710030304491803142d07005507a0a2113800d03c9130707118004022104211000312403001c000398001e840c0d01e0440d10251030000d0401ca8014042130440b45080b0521071641d0380 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 333991699 1250 333990449 333990463
    0x80405120415082a030705040b0a09140a08250504020706091a13141507020c011107080616110304080a03170f0a0b0109030f150e07140103020d14101a04030302 70
    0x2881d2040d945c030f031903461040f05c06100f1500f142c3c101010001c0d464246680c480d081508889402c1c829075038000d4020100440c4032460700c03030450154000c3d60040b20021141c008042110031042002e00c50542d20340128050fa04070710006e440c0195030310f11a07814403c00041c2c118051405d40c5e416051031904141a81c88405d115034041c14088451000040c5143c040040c294040161004112103180140c0f000f076483c0c40791650580020800c00214042c10800201401910810409400fa039561581c07075400c5583c10311030103403c1228801384182c1644c000e000500103880c0d800090020140355040152410882c00500d40701d401da0b02003084910b40108441507042281d49502080f0115000e00489100140c1d41014000b02c4070281c800c4100403550004040481141d9400e201c180c10b800c00b11070303d45100e07224400403400e00746007201c15503210790300600b040001e8250005081c041c0004008000e5022076425810751181c0600388080003902d40c0d5042c44c0055030b0a4503182506540d8000e440d240c0c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 333992805 1106 333991699 333991771
    0xc080d1b020d031e05061804080a090b04030b060409080904020c0109050c030106050a06080601050f0a0302030403110607020a1704210b06030106030209040308040512041508 76
    0x3009014004803241440c00720413000b13000c960054007406000b400140d02c0840c520405440e01c550300a654011801042d40b15140c40c1c1200004e0b0125682d60044000d1410500007080061620a0031590081040e0f4001c41c0b43d901e5803609039901d0164000c0b4680c403034004145d08254890541c003540a40e80208206d800c60b0304107101703040c201c03a000d0140903088804140103001540c042c1150940106042c03405c02e241c0304800e00221181e41201c40d071000006e400009000c145540410319840d245c0424001d441c540c00d260309c02940d02c100d840d2008003003c200c140d1100c061358508040c0c0307000303003454141003450b81444484118029070b1070b00216100c101220208507d81814481d810580c0c5d400b504980c00d80c1c0f103640b401d4581000080046880c0e10409428040d43c40145000e8030040070b400c25048048d0070b6420000c0c02d4020000c2000c6100541d98921000080300501c2c09000c01c2 = true := by decide +kernel

theorem cover : BRFrame.Cov 333812949 333992805 := by
  have h0 := BRFrame.cov_init 333812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 333812949 ≤ n) (h2 : n < 333992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
