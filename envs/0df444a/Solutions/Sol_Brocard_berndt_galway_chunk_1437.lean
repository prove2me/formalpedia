-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1437
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:59:00.506029+00:00
-- url     : https://prove2.me/submissions/814e335c-4eff-48ee-8067-a86aa16e12b9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 258273381 ≤ n < 258453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 258274631 1250 258273381 258273383
    0x14162d360f0c02160308030f0702190b0105010806120303070e030a0203010908070c090c02030904110d050a020316020c0d0b3106060603050603070902090f0a0b0a09061731 75
    0x7a115110b0703801c03481e41000107220858003907a8010b82e4a103103440703001c0c40380b0000c1c107204000702c03056001600203802048402c801c1c01c15000910300321103841c00d10500c1c3d81da080c0111400143c0c60804501145440c580d802c441d5907004000e1840d6480d1407000f580c40c07080c440c186075003600a84d03040f00301682d028816010440e0084e26515503a00c02da141c00054018a03402021a0710b1801162031030445c3e000003940c0440c641603600103034013035903410100194090000c040741d10758145403c000c00140a80c01550140408a505908800b503410013a601c0d0f1868001031038010421254803004100240c10440e00004000405040c1d0440030b03506032000c040725504040c07280c030021002800c00c012407103500e000345107914003042a414903100294803101640f1074141d84e00e0f00403c442e40150380344804043c0b034000040a030040c5543da100c8a42c400d4000410201c08038a618900050f0b0038001c2c0350714004018005003110256848e5600500080041958204508040c401a82c3d109040d107100301602c07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 258275881 1250 258274631 258274661
    0xe04061401031506020615150d1505041806110f04080303060102063601020f0a02010e01050c0a08040f030e1003020d0e0c0d14162d36 59
    0xd0844840050203483d030410321204850600311040000700d6010034407036004030b08002c8402e507219450000a40d0200307041102c9401000010300789880100b198400c60403a250380a0360702c0215514000c00046501d8003e0048042c081d5101030f50020f80554004e04060440c40e990f5820070703ca1240d10001ca4015400902095100000f4007059603010031205500012080e803203195200820071400c682d007044a00360190b00b990320143d0b240b02c42e007034041e10364001400410301e48402010350300030302811921404030825440d200c00704014000660031150710618030344a028254949a507184048455420140c0c200700c02c0403c125501d644074a80c4031140c02070340d600540c6074040b0b44103650880e5034902442e034055100002e94506074a54544e8040002d0f00106c0300c14148004105182c1883c0c94001803550004c41858040b4241010b031002a070070303522401420040300c0c20f08202207503405081c09000b00b40b0060659440d480904100444030103107401004076408014072a03490709030b4034504903450003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 258277131 1250 258275881 258275909
    0x40f050304081e01020901120b1f0215161b050c0d060501030b100528051003060f0605090a0b07030c06090b0a1a0907081305030a0e040f090c150e0406 66
    0x201d81c0954101e4000e84643c0700c000c41c686001800060120b140280f0020300042c0c0b105101452551514560003281c0760100c0051880c101c44d6000079101d280035140c210840340341e1008104c9405000c0340c0c4852032801070310340082c04511459289066041100700725014810003406031480d0715034122201d4118812070700401ca41d41180f600c0302c07061500a1078100a10f45183e0208003550700c4d040c0400c0340c1e03452484000101d10f0110185110720180390040c0707400c1444910700d48035090707050b40310b1000c840041e01c0004109440b400100e44038861101c43ea41c1c001c0800c1c10910404004800802c0d00600c241450321000f43d080e40c4440a6072000d038025103095200c0002c00140510070b010f05880e410819105100701149200000c0704004042e042d10200302c40e103c0040c4042c10380b04403600c881600324084984804849100038800111588164055820603200c0d034124403550007481c84080e40915440e1100e414030f0164611a6120b2740d81504003c17100751600125111849400090304500f048140c03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 258278381 1250 258277131 258277153
    0x60c1b06050a0f0f020c060313060915320c090d050d03050903210406020f03090a021008061311090402040e040c0f03050a260a0c05070b0c1203040f05030408 69
    0x1601003d41440301032180707038003c0400c02580480c2030f40c40d44d50304075802c0f92281c4070343e8601c0400c0707000030500920341c0e460000c44601b032010041481500b084001e44c207104c007145811440c040c01200c06080c103090719900954040f910829a0320702d9200100741007035801d00c00f013a070005611205240c0280d415402c050070501890f903150043c1980810400001c61602c01244072030307118600c03910780da940c9440366003002c1010045c0d40c1d0100e820448034910225141d0504000c07654884001c058128480c0c1090700519514500402e141c501c038500041410314883d80c40010000908403098001090142c100701c0301d08117079660b201038406070041843c01d0310b0b01e2030540342c050344840150300b0400396100240c00402c00a02c0006441d894964020202100d452681c2e01d40c582200500350310140c0700c400861090001070b804504440c1e024003030411210b40725034400c6015258070464080d8110b0b50003600f40d542e105204e40b402150018403440701801001990b40303495040da0455004119540c010742003c003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 258279631 1250 258278381 258278387
    0x30309041d1c0518060c0703140606090105060702010302070501060509100906080309030d05160606090902030d0c030509010e010c06050a02030f0c0a0518040f0507210b0a060c1b06050a 81
    0x200a400d241c00700c15408002c1da009042401044107109020080ca5520368403a114401943d00030007040080b5440103450f4030300080c00c000c41e041c0030400d03032040b800007441514007441500d0407910083d080c140380c01050f400440c00303540b0811041d100d85d92919000900303501c403d80c0700740c414010300e4450345101b400c00c0101000e4400607440700c0340980c024805010350f40e03808542148082c1441c1002c44d55265141000508a101c0e4030b40a44602e02d022000603403c002604440c40070340c400c409a4095070302d559070580e9029094500900010818860750102e0b5006440003401c41358141418002e49007290f17200000da403012107003608141d4011042c07100804001c0006500320040710380f003c0c10104a500b0082190150100c0b40c0c421003800700440c1c00d03e442700d03070250600348407119085c07080f4540050040d203035080d240300c0c410001c0529030705461440303410b02c50195000d5004010468080c90207204460203082c4410903140000c43e846140814100c1804500c000c010300c0d11503a4462002c2035000d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 258280881 1250 258279631 258279643
    0x2031c0f080c1207090905010603020403060606021f0c02121c060602060f070f1103270402070206070f02120a050705270f072001021b01060501081302030309041d 71
    0x540c0600240c0e80910800784098410754141c3d60009801c1032007550789120442c1c05006503480544801c0c684000402c0590b415001442030381c0c01107a017480702c5680c0360384c00c030703960802d0a4020010b5041c1003c88800c000d04d582100d08100541e1049400c6100c001c03402840c04d6100701c201034001041801006540300c032500411008050f14000f4000d070785088507140c0b145580c002c0502c1c0402000c1850052003a003e050010540070350740041329254641405a001350025221403072800303400c2001708031284c2c64580221840341d540504035038100102a62110340740c9000e60801c990003078000555504c2e50344100305400c1100c2c0144000d0241920b0017003400010a504808030000610b0002095003070042d2045517030300f021101d284260300d980d0340c02c021030700c402d030801c004800c40e4060080c46403e00415009013804038070040d8006905070600c1d5840d404c852007032003003d020480b0600020748404008500b1200240094241ea103401c00ea44d002408a445030520382d90031020034011800c068104003c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 258282131 1250 258280881 258280907
    0x1f05090c1012110c061510050f0d060e1f1e0611150705040501020115030210050a0c080706060608130b15010c0c0608090f0303040c030b06030a02031c 66
    0x94500481035001050440140d5414003082c0000103500740c624101581c04490621107012031903880b4840050003e450300010f48600d401c4003006290400c040ca8130380d0300c1401e5042540c423400c1c50001968484856178002c00180790310166942c000085414035110744901c10f03201006540b110040180108141300ba950b081421740e12214030b403046201c641000c01c241981c0c818105808042003912800c0c0c90003001048021602001d4010721150703e40040280c01500c0b4260000d201000715443c01841040c417501c006503100d035012414541083c0180000c210750352941c0f40201d0880d03041d44409031a94001201241c0076592041c0401207a54004001034209002c014000f038407003440d840c0e05400050180840c1017400c808510082c0716802005400581544201d030301d007030203a8509015120700c0c402c5504030301d140611502c4207600c100110403039100b1940456240070803820764450041c5400018440f58142c41400948409a81d08010807548006161a0381f82c0f5481c0d101c900500703500854074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 258283381 1250 258282131 258282133
    0x90409050102040602190c032d03020705030f060f01030605273306040e0a0c0807060806030a030816050403060f0c0e040c0801030b060301021e04030512030705030718081f0509 77
    0x40c8403400a8a552030803400c40750091a41070350f800c54151403c1045545038488278041031040507070400c258011a0303510071034100720180e60b80100c10704001034840320120b840000001a20006000144680d80180c1e0024101e0030910300e1001036010040710030700d544184586c0c0350700c01407442c40100c0100b00d01c0e80817144c000d0415040c140184210941000018105510850725482c0c00041e0ba0020822690900d40100c04428103035910300300d164139108a802100000f0f91940d0016141c3d080004a043c100ca60581d11070f0700c82c1d9100c0304001c02c0041c0410500041200801002011512a010700882c2d1032000c840010111541d000141c243c00300030a015001e203080c0320303c078544203800148540c116a0401b582d60300d41e80c1c07084006802032050410510300c030fa0811103c060280c840c000a030095038410801c4404180c191400030702e0600081b07401030001142000040c1c03110744200c038101c10824020011500080e00c4034202800d101c82d900c404043c80c0c250614040380700009016144d0420400c0d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 258284631 1250 258283381 258283423
    0x409060f050a030f17090d0c0302040b060c0706030c0909091101090512070909140f06150103020310031509200a0905060d020603190207030e041a101103090409050102040602 76
    0xe510031101c040e144c900039010500c0100c943c041791840e40e0440da6481e8008000c06100c2400385009140342d0454001680134a180c0032a41d000b03800d001084a100a043c1c800800803180b4000f0110b010340b41c000501e4007009500100010846418007070007854a100e03c003a22021601800014200d81a541c400d510031140102610800503020544038180c4080040100c1ea031620750038003c00c81c00706010003881c0d0784503480075034645c807402041e1180181d15488584244c0e40e000c40044059020645076900203054913a8100b00103940107451301c0e44540100d0b80822550f0907601d0700c80f59030020540542025418282c941100d00c1c0110700180506a001c0b800c000e141001c05c08591310549450000b40038003000404100102d000700c800d2500300c40c841c2001c0d0368804203031034000c02c1e10f07690111013030080b41001d09030f050142c01d15580c24a0080c0181c4101100045007004840918201c8402c1509010030441061a44c4840c001d080c0000d0040b80056503552401100030725180118642c1c41102d0592 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 258285881 1250 258284631 258284633
    0x100506040516120c021e01060e01090b0604060806010c1218120503030a150312030b01091d0c0d020d090b041208090309010e040b1306030212010204030b04060f110409060f050a03 78
    0x44107402d03c00a580050008181001030801e902e000000b540342181305000304e00405402c08150080d01c02d503401051014240e980c5e80300c1e000d0680d08188802940031000384828000e282c400c94402c1d912410500d000f00c69640c071610303000c06140003000081d000030228000c0d007103054200d907101070044c1003008200c9045070840c0c86090f160300016003603a4000e5100c0011200541c03d4020440203903400c800c000c040142200ca01900828400c2400360210b1100d040c001085081080c001e4402288a0401e0486030b5400030604860341c800148080701550071b0090708060341c2a442007030001845003071061100d0a150414142d9071100102038006c000d00390b070402480303c00c04802d40b944c0070001c1c02e11b030315012011000240581544003890b034016080044202c601c484541006c02140c1c0241c582444106802c0e455900b80c0c86180000b50046540601080000700103a200094580d0b1108000a020104a03aa1120381c2e00c658001103420340c80383e10900031800c00e42c27144401000208c6e482d03609a895 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 258287131 1250 258285881 258285887
    0xa020102070e070c1a0a050a020f090d020112061211060c12090d12050d0c0806061b160b07030905030c210f0d05040305100c05090d0302010e100506040516 68
    0x201d4055803007000310050100e960180259031042c02c0590103105220101c0700101102d41c4c0e040103e9100ba0b0b81402c1c88041000100c1c14800c4036259000480d106140841da242408080400307204200d040203040c0181d985120107520481010f09110320450034020020f085c030000e131100350480d56100b00010030103d2024400000d03600256000030340350a0b2500e540500041e20480e4566000d03120840c2d05000d800d0044e8014010841140220030400c00e1160a40c0304690807a400c640480e004181040111344c180e1000f101548085e00c91402c031680540701c0501e80340e206100d0345c4100c0c038008010465504058002d4a5100074140550050002400860000b0305074445401e80e0f00c50310202040340c05030700800748400b00d004c1000408031500c00c807400c03400402c2540036110558003030140304941c00364000c96008195100342540e0340c2d9410915a07200b046100c0c1001c103811070a41d0359542c4190310340c50090004c0400290407250000305841d2000034807007a0360f0010040e4000c0c040c00000e440d14550 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 258288381 1250 258287131 258287143
    0x306050901080a200303031e0f070e0118090213060801081b04020708070f080405100e03070b0919120b0702030702090705160804030605041a07020304090b1804050601080d020a020102 80
    0x9000310341c03140e4200d190540b040051146134209a0903000c0042002074800c031007000881d080889142030482c5903501040410818029140c2e10001a2022091000d641c0305904003d07a2f040080d080300500ca80c0c6105c544100e0740043e025880c40c00508404200458012080c0703401042c0050203440300c0003d105448024031400c0b00851b2041d68081040e4060211a00640d40029800302c0720840e83d100b035040070400364009109107072044440202a80409100f8903985005040280c014240b160518903024260340108d11201d40110341c0d80122626202031101d00f500078800b40d02601031900440c00d12803100d86c3c00070980415903004200c3d42c40140c6071a42140e030310108030710705103031207541480c070615076583c158002805440000c5004004e0000e01c2d40010301a911940050f03244403a003503090380c03008004503151000768106000c1006000d034a40c03c090080900205a030400140b00c82d1080141c4009440c207440710350040d001402084020000c900c035042d010300041a1600740e80d80003c1d5611 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 258289631 1250 258288381 258288383
    0x50105241210031b081605090c160804060302040501030f06060203072301020403032106120602180a09091502040f05150702090c0a0e010c1703090a05010204080c010306050901080a 79
    0x840ca00144414000301d400740b015680c08041040c0d0341540c04600300d004c080602440c0c02a0140300e80003103010701e24000740801c4035009400c01425a90700044901a504400391a074a0703030008080d4080081c0d011801003000e46015100180c9941c05d2000041c02c0f2520320300303881c64851800700280000c0313030000150352460342e20800d41500c140054600460187c4914501410340d80040340110416410107040c8030120003140541c05001c58180798442920084c0c45030300c0340400364144401c08140740750001d0005180c544002d001884e080c00120380b804000b9402080d4035030f40c82854000b00409811032608a400d503910950519041000c03414081d442442004c0c4503250790030959400960344010341d030001c0d4009044ca810380c504400f0400c4650b1046110400054050302402c03083d42c007a0500b22802d541180e000030448521801e05219540090f100f0300141c4200044000004c009000510207040020003030000601d00400140644d88240c000510500f1118010321a669000074070542c45 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 258290881 1250 258289631 258289657
    0x20a0c050409141b0108090c0f1e030a0b04031d01050a030b130c110f060f070804140f030c0d0804120e061c150801020a170702031204050105010524 65
    0x2d00258900a040c84010b91039011541c014110000311440301c2c40d24200f0440710130f07210200c1d039a848201c2c4a4960146590071381d07014622205109203800e05900c500d80350418100380389010307800740001914003440039404403aa081054200000c25900481d07080035004c0718020031484c1d070301040018000340500f0141d0f0003016600c416111699503014040f4090401400c010855040c801200038012110022035180e20300ca032883d00c6800b1000020924880c00c880b00e4a40507030b485105003140c20b20f03005842a10901c40701d001200d00007006002c041c10942e140d000450362252072082190824241c0c1c4c0380c81013131000e2001004042464064156042c0501d80741c0340380c00c0300414001a4690050f0700e10030f10101c00c154031000d4011003030390149450080402d500507010f40d481c20041c0c245d100700014500010146410480c0780b0303a5031401c160300040a07005032800e040c1618030230000b5007001c4034151b0301a910341c4010481800c02c20a10f51007044580244402070a120354408a580f084017126009 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 258292131 1250 258290881 258290891
    0x3150219080712050c03010302100207030308041b080319030b010306080712050736020301032a0510170f010e0c09061603030b090c0c070e060f0907080115020a0c0504 73
    0x64540f01d411610301003c00001c081180e401c0c440c4030340d000ca41007400b003203000d040701a4400d11040d000103003074004c0741d84c50741e076101d070306da69a030342c1c1c8880920349026094a080c103c00d8003003180002031000c1d1100307a000400090440b848400b00409130788c0c8a64006061515000d0184030100005c40e410080d1401c07608007042d06a02840c00301d00d0b10510303501501c8500d01441c00d0a01603c0410000c4d244000c1909089040f0b621600100040344001c0c48020720b070781c102040900d40c13107101c00002e01124840101c400c4d06165540301044607818141421000038907041202110906101a61604a02c039020040c400c0d44c100340d041100b0b60030241c00340d10480c1000c02c00c8802580c0e00c00031903032540110601006013101507e006400b802e078110041c0d00c03d20203200006c940341c007120140c500c0905034000511010b0b203050020700e48ce450181c519900309002c2c80100b2446d03100c0e038060394090200b03903440010562420700d68003402000301d904001150800d68244c0d020074030500105055580c200e6002036 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 258293381 1250 258292131 258292141
    0x60e0f07120b0f150706150e2212030f02041710020403022b0206040e01060f2c1503040503190806090f06060c0a03030203060a080c18070c08030f010315021908 70
    0x124041c0a41c02801c903802c2c047c21041281c107440c86407003140c10703040040e582a114909000c2c0c0c803415801070f40b01c0b11079041140d440810620224100c903852607007000507508011160b124145e07406a041103980d619070006c0c0301e41c2c4000412291103010541038045003801d0659000074a0042503c480c1c4001c00d000420003116030b00c5a4a881c484142d00812542d52140d40300304d541013813042441341c000410200c500801089024026860301c0001400010b2840c2c0040355600111003e0040400d40183e0707043d1040885c0d003503030401503000d82e014a00554030f5150080710000d4580e5218051010001500148001070b100c0d20348840d0840003040b41c103601540c40c0d00100d0620300512091640740c0c03040303403544024581c0560056000c0d400030b903860b032103090300c50b48001c1e901c04c0c094041a0b009008901d003001d040c400c403110940c2000d00b03442c2c03108000b0900c1e2142d2804d41c0045c0c8200c80842d00e440010010403081d60316200d40c200e0303088002d42c1001c03107410b0881ca01703100c090307400302c240824200015 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 258294631 1250 258293381 258293419
    0x51213021201050f2e030605072a020f010521060d050607030f05011409041502130f060e090f0414031c0b2806030f060e0f07120b0f 58
    0x8501000303040020007840c07400d4051040725403010358a000c010030300030381c5034003001e204440c4d20340000e07004085e91760305075145030342d014002e02d0000c3c60642040f81030a1049001d81c0d001220b0320b90005820fa19581d0205640100f16500d60b0b4180f005052000401c00d510314010076810801c0000e00fa2800816127070382d8400403c802d410003c500503d2401081c040201040d01640000d1500e00301da50b0411060380c0740c080c50002e25150340395040c0d201c4000f0340040c0024000f01c402c5038221404813005420b06104661002004d0900d4002d4024071078100802e020440d440103000342140002c440008413405e00082d01403a1001c037900141c032400e00004101d03660032081040366510841e190b81c04a0250820081400914912400b98895500c00784023410700400c8035010304100d138060882c80c000e00d1610400f80c0040c0150703400c0800c120f440f12030001d40519080c010074440c1821441204035490494401400c164852112019180c901140f200007512010780c5a00c400c00107480c42d50400356420340070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 258295881 1250 258294631 258294649
    0x19030201020f2a0c0120070302090f07080a051009090f021201020a030b030303040b06010f09091d0c0102011a040c090f09020406021501080a080306060c0709060503070605121302 78
    0x402e0300090b0010b41070241c1200c0c002165207602ea0716001d0040b043d0640c140307075228a10741d040c56000800b0602c10034a49503c1c010311140d41100c620072031703003459034070781c003060503104100c484217240c00c42c0d10b0402001c507400c20710259108203001010003041c03400c071400d07520032038240c040d400344035a40c2d01c0c1000401c004410b001200a8004140c480e44109160145010358807814055001900b0701200390300a040000540c1e0281e580500b88070b0b00c41d5540c0b001183c502d5031040480c001c01a820000080c4502144601c50718568107144103c04444100d114500d4501100741007811a03140c0403110401802c51910452219421a00810040038401c01100c0500c0365401801a804440c0c00c0000d07003402b954001c0c012180c058003943c80550071900c1c02e20501000744602c2c102e43d005190402c0c00a00b1203401940c0c080d100030082070405400d8628a841c2010980003034900b140d44400038000d5181c200312079401014507240c15440c1c441d100d1140c0c2c41031440501031000107941e0000b144115958959a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 258297131 1250 258295881 258295897
    0x150a050a3302070e3706050103061d060310090614090f0a031b0524010506070c03030c02120f06060a080f070b03071403040605060f1002031207091203050415020106081903020102 78
    0x54011948440745e4400710710002608665421894000c002074154000d004e240c084072140c00c05002c611740d05c0300a2491990008103d15490f000b0032424102c0c000440c400c40f580c8034010100011044c83c0b807090382e501f5030000780051105a0202240c440d40100c0090184d11941c0e0500d80904802c112200051181540b00001080c6008880f551480210380400388035031400040c550446c0303039036114140110742c0f00301500589405280c4106101081c016000001031910140003000d0302c00821064a0030041c0e03199400e440d64001000340b040c2c40c6404008100500309602c05080c4010001d1050355070b4000174450040c10f03000110010340001d02601c40c1c00c81c02031040c0c02280c8c6e00e00c0c29140c030700300070802140c040c0d01c1518284003040340f80c104485644001181034000754030340322180884400700340c00107010100b002071249020402c010b07403006c0584590b109442d83da13111800d0102d80140d495801500c84116803405000308016900000c0310545183e1516070202c4c00d4140303040403400392080b058 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 258298381 1250 258297131 258297181
    0x30201060b0a0201050412031b30090209090102030606040302090405120304080d0501120f020d110316031a040b16120c081806070503150a050a3302070e 67
    0x940b850003d8064000301c0c4540d02c02c03000c101c40b40100000c107a0440c0c40348138080c0b1701c1503411251880141d01810500341c40e2204034401524281c0d082e8001a025802900107011039511840c0c10011400c0004141d81c1000302407000b9402c524100c400b00d0024002c912000c1e210f5030004011038213200d014050f01c02c01031070b0303034003c40c0d603a2900342441ca8043d4054584664024500030000481e035013040e900e0410b15034850525800e000640c2c08000060910709020b68071103d0102c42c113201980c080000400d1087d1403400d82e03100380e2960821550f078809041c000107414503c503003040700040c8a0110640d108480070700002a05800381406c40d00d0701c24401805a0580c40d10100b408426044403810748501c10303442840c10584402d500454450800b82c0729200450018000701300320300c1080b0310b081c1c1400c0b4042c00c04060240c1c2c1d4000292501181e82c07102150274039203a03a20040c0c0d065440005581c1071000142044100da0b40310080d61110144603103140d002080d008038240e100e05510501c40030b08410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 258299631 1250 258298381 258298387
    0x209060c03030c0406170705041716150e09060906061c090507050a05041a011b081603080c0310030201030b210606010818030d0207060603150e120f03070c030201060b 73
    0x2a4054281d0301074002d650118000d8444140640706c00740741103102d00003d54440b82042c0c9809105101d0b01000000c4408a020712a40200699142001e02d4010f1140400c00071040c009000041e04000340c4808150140d840003041104a03112103a00341d030403810540c0c00c02e64411035080403100d00c00b01d102d4400242400d0240c0b250500500240c0c80099820803210f90410683e144200411a4284400f8a820b2115a03101014642c000c51014007075181003081d150300000340d03656081c9254030a00c4050000121040725400f8036510424095100ba03c18440d2031640c01c100034914290a81c52100038105900e0329007608a030749502031524140c40c5000d045100c105068008152110011550607001402070742c00a20004440110780340ea0b824070b04003071403409034000032080c065030000301d0982d9695241e650000001f02e240249400c03088401100040c006c200d40e202d141000b060342100884600148031951001d10b120046070b8200e10541040301410106146c164094000741d885120221804 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 258300881 1250 258299631 258299641
    0x30b0601090f0f06030b0105091c1b030b0f010f080303150a09020403030507030e190e0603071502060108010c0314010e090a20011e0207050904060f02180405090105010501120209060c0303 82
    0x552080c1c815290b040d101442000911b20044459002d540b01c0c0960008008503045c2282c25070f90046034450380200049180c440c0e00007400c0f40c480700d0641c0100d4800102c0010401c6c900d501310b200030301400351100a03c40c581e03e4214140d40e00d00001e0040010200b17442050003880d592404018000c1010751030541d100d03070707407030038080c055070461202580800c1204001504a01d400404130700112217010103104094203080308454580402002c082c0c05114108000c5004081c1c60701004c0f1012169004220740d40c1009034460039102c50003040001d05041803c180205210b03400341030b0540d1b10320400c000c62743c3e503100d000900e07020394017001500700c484000390000a41c1e846c85071141e910000b070700d42c9000c1c0c10040026080b41d40000c6041d5006820003082800203150034071003150801c3c001c21000c0307629400446008220f034071051003145000810100c1e42200e041a0148540c4004504000c205540c50800080d090003505150085c949500040352801503681d00d0513070307400d4994041181e40301d1400c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 258302131 1250 258300881 258300899
    0xa050c0a3018060f020a020303040f0501140f090d03020309190f0e100b072307030b07020f0c101701030b0f0112200103060312020109061d07030b0601090f 68
    0x501c41402120158002269001800381c1500c00c902e00100d000714000320725218003191072001c3c80c442c000842c05881404c02c00350b50f0070000b40000c2c0c500d4500300d41c1d034103240030005020603c030314013921a0540b05010130307000c4124900582d00800416141c1412140f4545000c900b14850089001e502a055012500c02040c01e00404401e94403980f070352590840d221120040c12000446009024040340d0406000e000000d00c080c014592050074185920341d02c141d030704240d150030700504010300d91009404009002240b40e0098020407280042e20f0140d00400c101c80e00c0d180e440207410302400300d0302d040485007489a0180038103015860340310116540c62749070401842e081074607800b40c100038040c0040354941c08212084201907202440300030300e070300c00b0b40518031a00c0c05440e40ca044c95500e90b0000081703419682d020340e440303041d5030001032114040e1401c0d5040b540320b00c0c2e41d401c20680a0340d50a401d5007001643e0303800d4a401062081c550340e0341d0300040b184002c03140c00106040c1e02000c0d00052842d5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 258303381 1250 258302131 258302183
    0x3031f09020703110f12030103020d020f03031611012a03050f040609030203070801020a1704050312250f09330f020f030708070b07090302041104050114040302060a050c0a 75
    0x81d504145d41e10030314102409a901c55143c107541042c600100f00400041c5801c081c0b490441e4805424540c100407050002402c5801030148402110044c0d2410700420840b81042c140281d03007400c0c9444c003881000440d000701c40d22a44001508010030929600740760242c804d48449a00010b40c6030f590315150103000303010380d2003032100700e0084c0714010000c02d0512041c000d440340745095650704441c0900395403414414250251098070180030030065160422445030301c40740305e0852a0410868141c5034000c0040c5c09140504047c00c000e507100824582561154401003242d80c801c2c44081200040010f040349480d0340146101a5902148d80c001d002e0307045804004600078603000c2d5a5840010030764180c1703a02c16070f00000c0c1500420032041c000900741202d800d0300103600d480d003d510a51240d01080c111080c0185e204080702020408006075079024150100f10202000b800b800c1502c0c540c00f260701805943d031014280032002c595030316001403c109802895400117003103c400c00d007001c00d00021607 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 258304631 1250 258303381 258303407
    0xf0c1b03030905090103080a14091509010e030601180b030c04050f090601061e2106030b10080106080307080903122107110a0605060a030602040902032703031f09020703 74
    0x1c0c00b040b81c00140b034070309032141d00d040340d1f005402280740c40480c4108444000c41c19940c1c4580318400d10007000710351038110300107060309080e0701c82a0f5205201c20000d0100d20b1811031451081d4050740c010320141200c24000320790300300010f201151188000d00000c1c10880441e591a401500d80300402444082450260780203948000684103070f0b03622800c0450719401c01c03a268010800d0640380056059116003804203c1c042004012508003940e40c500c4070941d4030f158001e0702e540b01d219042c0100c01c0c203110103250090030300000800c0301074034100c2c41a071030f801600400b030100705001c80c54007219142441240c00c40d00520050598600610346000f401003801c40d00b03108030762214000030303c2c003038002c007a213800016034803008001030040c940e140c4001d410000c040c3c5030805150a00080018a14000340c00680204c0c038001da16441c01d96095401a9014064103160f000e405110300b4041502004807900030f45440281c500040c07090845524134415540011841840090f40d40241648516200810 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 258305881 1250 258304631 258304637
    0x18060218041508060f070c051b10030209131503050f062d06040f02040521010b09010f15090e0c030906090627012309010b0418030f0c1b0303 62
    0x10b901c01d01c6030940c2602e640c012640540c1c040710104403a0b4491080b03059024400303190840c041d245a03075131a810001004080781d0b07454013200c50441c89140c07400c4500606103032440d04505001d8502d0026040401201d8140ea02d1542d49240309510100c40e0103410185400408588101c5030410384540d03202c0c0101c44416024080d00000220300b042503520b4001051840b1860096840325810480103020403900300302c1080e0708100001e03203500c8070079860703400351010403412038084c40349060346007518404c0c9070791031040d80c6500050202d000c8041005003039800b000d143c0041c82c4000c1c1000d41d410320a0f41c1028100211034001c100c41003a100004510500d603003001d80380d49442c0c28140c3c1e9980c0e04152180d000312180020703010b2040042d01c81c845140101071001041014290540340403180c01c2c1003140c0700300c00f042c2c0d04008068409024501140105650401c0750500c6180040c80502c1503540040c1004012058070101505c41c00f420001241c0124115880c1e8140fa800a101d9501510003107000c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 258307131 1250 258305881 258305891
    0xe1603050d030f020f0307050313020a0b090306090303060306041509200f031c0f02070e040f03020609060105060d020f0d0e0705011713030e18090d08090c10031806021804 75
    0x9001c540c4c001d548064550718555400c0d500c81c81c2040d580b0342c000400f00114030004852240143c2c1c1e4000684004256007441a507645202c41c040c075013480c1005110710402c0d40104140001a1000200340d94459040b65290903200e81d1a0440406090300c83d0f0041c280e0b0014040500740d01d08448596a031305c2c4021a40348840540c518103040d1250b680c108544200010000c050a649003e502d0038502100c1d51710580740d60607265070495007401c0003554140c1c0d01400c0c29071284101501048083d03000b42d00100181400c3d071402001880a21402e28554000ca8010584c03d45002d003e100b994441c1107818000d0040f0310044450b1641c2d812a40329050018207200c002c41650148131003c03d0080c8000c0c14400b0a040454809595038118441411b4000c804500c000205a40b03882581c0c0c040c3e181361018251429101500620070500584084029006603040c1002a500c126500064803128100468070300740403180203415001910000d8589800002c140d01700100e504c0203028105412142005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 258308381 1250 258307131 258307151
    0xd0e030a0c0f0617070f1805030f2d0703060c090905040f060b04060b120c040315020a020d05040e0a051b0a08040c1d011a090a0e191505040e1603050d03 67
    0x130009000d44e10b1002140340070382c19401c0b4a100b01400c01004900000c000c440c00c1e51000420325060391082d040405e0303002654080c0d007c10410810081a01c1c031500c2d0042601ca0301c0303008a807582141d2200a0007181e540070b944015602a84a171002040c62000400031441c01d410820755003e090101107844a20b030041c5031005103404d12a0400b903442882840d0f081854081c040003400002504a00e1001c00c00d10002001400b068100007502e9515400541c41e5615030401a00d454400320030b050a114042c4030038009100b02d250200e501900440300450a03845038cd0000c590340c80c01a0f9400c0d010f0b00000b4003200c0994001000030b0040d849103018103070171551290100120b004140310001c1c050034a100400c03542e14561201c101d030074805002c81e854085042c00103180f0301d03026400320300303042501070070450252455201c0011308280307c1802d00c00b50142d4001484031060701c2c020b4500c2243c0d150307103005d0f64400402801480d02450a02111401d4880c02c1c025555141144044001713410705d03c05c10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 258309631 1250 258308381 258308417
    0x180b030c07060b0607060203070c0b0912070b040f0b0702010221090d0f030b06070c080d0201111b0c0d03230c0d030b0402090301050106110c0d050d0e030a0c0f06 71
    0xa00c2030305250389680c102105599090003618124410560020303052000f8008141e039440158047d400035103810307192a58901e400d811410009060346d085411512a55110311800411034078817030f61082030706d1042d070f41d117207452040c4103903001010781200c21620420000070340540c02000d010b401c0400f82c900e40a80d024100c0b4030304108a5582029130407e40041d100c240c01103134418600544c9050104508850388045142e03508000010789100e410706408000300e10051041000390140ca20091240d281161002540d0f80f1407c42105d00300441030b010745054040c21f02085118805c0200301780981c1d0701508009045081443e80309250130814104000a421682c04039400e0300034880c080d003107021903858150000c200d103619441d00a5000c1092416940d82882003501a003640d440d4090300001e680a4649001c2c01000e10501400c400c0d032407500406c00006801000c00c20720315245140c03105d900042401c046140e02c005044001d12a00443d801203841401b03015502c0c40e55440d28031380c0b2140018 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 258310881 1250 258309631 258309637
    0x10e19060b07020d15020705010623010905100201180605071b0c031104020405030109390504110c031305150a0e13020c10060e091c1b0b07180b 63
    0x4030021900070000b00307005081007042d80381c5041c081c099004a01c0308091411099900c1a141150240d65441c01400002940c10b403200e101807415008090400d4120f0010b050590310780141c51285c5c1c2e241008071041d038402d400c120b0018101e0141d690383c544d1146414000341c6402d44103280814104800045042d50403d403150712181c21107a0440d0451954807004000880e681100741c00a8082001217165102402200c20f8240304240d50081100740c1121520501603280c0700380c2e80c140703020080140c1000c40304c1018040d00c80840b00003030300e400c01741c080c15000d01c10842c014441e4000481c11076840440309108504595058644c40880f00d20108091414031400c818031002c610406071442d054288030b040384040c504503100061405501c02501031502844001c002070042e1a00701c10b020458400c031050350440faa040c010319291403500e0419030140c403010582801c1022004541c94280503845e98010090f4016035813400368240398000070074560110114004980100c440011030703040c18021 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 258312131 1250 258310881 258310889
    0x6030215032202030109170d0b06180f04150e090c060a120b01021501090b01020c0406060206071809050f0604150509070e030304080d0203130e0402030304050103051905010e1906 78
    0x480700d0b000002810b482040a040b0181c4e0950b60b5256010001030052020403c1003602a030810303243e50030040c1010a464803100f4140c0621030521041103505007400803d40c2503102110080300c2081e21002203001070040506145447d482d141001410302524403842e801000180700703503411428a0307020710440717120325920403000540d0403040d582401c5880d40105288901441514416081c4806c04001c0050070b0304003520300d554948080c01c6030340e01080407041050040d2410302c80c040c035204000e512042e00804034420302c011540300d107c104099402500c0541980322081045080c4221040c040003000c490050085240204e052401161340718118201c410017481c84400e075684000841c1c081c2a4540010f030944424440401c8021090107208a045802d03030042d515035100c0403182e0701c003002c01c0d80000040708040d4240000358501000f22019920300b801c0100e01d98980c80f036036043c042209051906000e00d003400106801d5908000c581c01141d144101c0049040000c03035071022240366100b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 258313381 1250 258312131 258312151
    0xa02070b090c0f0f0d140105010906080f0615120d0e04060501030515150d0203150102061b0a0c02150c01050f150d0b0c070210090f090605030307060902031f0603021503 74
    0x1043c0c54902d0011049404010b001d0407204d03079900d0035951401041411a81e80c4040e0b5100c80062210032030501c250b000514038500205901c6424210b404d880e5000940300306c5100d154050a4101600d60813240031340340001c0c00031150a1224480b0003000400d508040b54403980c20401d00260a6200b405100c0c001d8030204408440308070700400b0003a5603190114160001c403c00c3c031003901603c42602c050b51050403502a03c000c5841c2801c0020704041c0014a01016400c0960300c040c02d20341e1003400e41d0120020342c142219000b0082c0000b0b244c448649081d800d060400143c40c045507003040d00928024881070210320709548548003200e080714401d0f0f41458010b41c800e42d04401040c410039403150045000080b2510b000b038690042903400146500800104246000c104206035a80e80c0c1d1200500b854402001441d04100009071203104500e00034140d03e8681e2041425540d00788188281c4c040100d50f9955003200341c1c24010082d040f45d100585c4103698540c210101d100e45482100d1269410319 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 258314631 1250 258313381 258313399
    0x71203050d0507030b040608011505040207030f0e01020c0d03020c1207050114090409051917070f0f061407021f0908040501050f19201507050a0203120a02070b090c 72
    0x2604040142070040620f020103484140040840e1200e2180402400d052030010a40d0316000c2c41c0c0500101c40c4c0d6121030301031441081844003080c0d210382a41100c000d945061014806040c004034900900005100c1e81302c04031050000c10903800107103194000c44107036110310054801c0310407240c480340b00c1d10403280480c05043d0f1205404030100024030311814000e00004d00d20035161102d515010801c1c01701921001d881c440441070010000d48144001c0805001d2881c100709075a42003580115450000d06082c0d01e400e9180c01c0148640003160801710894100341c851402400007543c0d142d0140b1800b00b5010000000d480302100c40c0a00310203150010412482c16140a00446041e8840000f0000701c41303082c003101da001c1c2c0c520002e50000340c00301d58410000407500400c502070401d1041c0d03002020b40c410309004040c080182c24444c0d00202a0410395100c00315200306904501c5004440100c60303210a04004596810307502400004d07001c1c1c02c0a030600c1c0d0390050f0f6180c1da00d81c0d143c06254828000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 258315881 1250 258314631 258314647
    0x703020a09021b030403060e060c09180a020705161a0f180d12080103020103060801020a080601030b030c03071205060702061009020d0b0409030801051003020906121b0c060907120305 80
    0x2c2c0c00805608601d0140c5003407180425802a0031504241c000300d54481c0c554140c0d01e0001c4007041a150803078250303075805103000000000159100d082081445100d004c000000c2c0d01024217030b041e114116006400d036081740b005210024408207580c003c8103800030500700b0960f0000b0700441030b91099082000b06070710b01180e1a02100b4003180f034281ba0344e40010024542e4000600040e000c0d505411039480c1d68084e541544005400c2e5142c64001301c0d02684144070f4105125030082c0c41c01c0d04407800b8240001c5603007070000420b0a0840040006400d0300c105139000545460840d208041c80e4051000e4500340d4842100c22a115081a5555552030002c10000d0040e104a9402400110741ca5840000c001121030b0200d0291018200c0a0300828610310041005050104e00c22804111900c2c00714500460440010100d0288400d10343c1501c0c08180014440c04c804480c0703041084408440c00d4842c0c080007440d0b5550740302100c01140a009078080001c00782c404961802d01039626481d07440c2460a5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 258317131 1250 258315881 258315899
    0x20d11150c090307030501140112021f050c01180b0619060e1f030c090605032a070501110c071e031506051009030b0c1810030e120405120703020a 64
    0x20241c03101003808820003842c401e566007049028015031050b40086501802450355030b07048941648405105110900c00784016951904198040210350000500301e0941003021a40c1e4003480c8042812586416580300200c0c1e680c44101003007e10501040045030740302418000b03071054007910000c402c01108024820140220900340009030094034003032007e0303411540c41c4a42141c0000f4080869600c002c00d2444c03a82c4040004090302c1c080c100680707142040d0764041c5040f0040104851030701c60b41003581e0940d900ba0000c036540c3d00e40100092065499020004072581d1051071613103d944680d81e400641001f07604100130031030b490310030900c84c0309156444112005e034150b800380c0300e069030f00e910210300c6581d0550039640e031581983c2d1b580c04030303421464050a45c03080070f41424800e110520501e100c0324000038842140e41419102e0f40344005030321300d068018000c082460311290151142050b1322044d0440074004548044070005284003c0d40f034000c0e105c0c903103804080e4000700880c0090041e621 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 258318381 1250 258317131 258317173
    0x1a091b03010b160b1617010311040209180a02130f0e0f04050c040e0606010f0203120106050c07030510020d0c0c1505150306010b0c010606081504050c0409090f03020d11 74
    0x10f0841403200441c0010759038482e031160300703c0340c0e1140215035840c1030a020703911000d100100407005400400650540d111030f10100304011090303220340c1c0c0000d02d80017203840d41c07400e0301c80440043c98080b80354100105810065004410701c0032000182c00800503103101020b4020088440a010a8501c0d0b2110405030707090140091050340c0520400075040e074642c9491281882040000025215604001c0001401c03060f280c402e01c000c40d80240b10b00c250314085449040d044540504080780d9984140840b141004005d90024000f40a4003002081245498000b0a10030801400c20001d04001541c1a14400038082000d088110000255810803881e9486290407031200c03102510034a00c4880041c9c60704000741c011802c26140482c058000340d0307013401518040c01d01820080f0b850320708140c00c896041c0e02510349030310981d1103101154400c0340901c02c4a01410300c0c5038003404030000a05164003500048101140184035181141881c20710036018943c1403038400b00a008469866400702034034103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 258319631 1250 258318381 258318397
    0x16080f07050d0e030607111e120307050d1506080a0b12100e01050a0504020105070f1704080c1201060b0403170c0109051b10050a0302030a0b041a091b03010b 69
    0x10804100c80e8020603401c0242d6050200c80703a0395100789103880720a1608044000d0492010310043d904001540c007000b140a1450442030090341d84070300e43d200c001a01d010010440300c0145c02c2c2c00800d022040e0b9115000340346006800c0360a1002e440c94201d11100d03560980b0407000091410008110508200e80120079401c0005020004907500840d5144c00c101a41c46010b00f81c03a681c0c840096110401c0c001c0341c2c1e00c66040c9000300818138040e00060100d00c1a03980081088224402d690704004440d4510f0703c8803a041c030911903c2d2500c072062151b880108120b5548500740d40134000d441070740140038000c159001d101e000c07400d041c550b9880701403007070458a050301a074105119598140409124414400303000d103001304040241c0940e000315907411201c3c80d500502040300000d80b515004811241814154070740160b4942e2400c0540b80200700c00424164402e00f42017001018907501000e41d858800110b0b96425952191640800000b28995081034541d50900040280a1108018104c68 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 258320881 1250 258319631 258319657
    0x14100e1309050f102f0307030204030b0c0307081501020c13110f0310090b03030315010c0210080a29010503070216030c031205090901030b0702031b0106090c02031608 73
    0x61500e556180e003407640000d24002160704ca0340c0003059450f550b00488503500790062580d03912244240030328a44104403070099080f19000000b0540e910b1007541218001e5030424078092441c00c021400044a50098420f000020002c8002c5003040c80c00c164040d80000c0141c00802c584001c0c8400d00551180b094000010303030740d5a0700321003450308000f802014882498811980d607032401c44140700650340ba6800c40140e0b42d141c01c9114540307480c00400c41c0c2e0025007820590010080740d0740100d0344103401520080d0800c0f5001c5182030b8403074008003032a0080c2175810060291420301d0f0503e8440c014124000c0003029014200c001c800d5011340021500041548140ca03034441481c008a40785200c69842110011040d44040040c00845148580080c0203858030518201c40000090046001800041c1100ba9240c002c00c040740d0080085a080404441aa058881540c80c0040c0200600c1c45810340040c20b11440400341c510201c211030314801e003a800306945003c1510394802c1d036080f205a0700b01e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 258322131 1250 258320881 258320891
    0xf0333090e0703140a0507031115070b060a050f060313030203040e090a1101030612121e080a0507020f150601020c0409060e01150803090915091014100e13 68
    0x10405001e440c1994080700c0050960b54554502114081c9801c0313001c0c40142c02000e641c0303000410105806003100c4d003084074103000c07500240019403406601d4080b020707400c000060346401c04c0101481070344121030468a4040c482e5903041809101c030405103116510103410400a00c5800c1c04400f0f054456000303204507130601c2d4440031428500c4505491700546980030f507001c0e200b00403040750000310407034081c41c00380121841d04600c0640c0346c1c01420010710b0054070401c020041c5100b41200800111a03000c0384056800d04040903154400070341e030fa1015a4100000140850b0001400d1000c0010724001000709200382480e500941c40e010b4040c4c2d0450207006c0d004003655841e8001c1c1c817003840c0262400036645088010240c2140d050000d1000c221808150801c82040c000c4240e460744403094549a540d591004145030313014491030b8a8580c45000b181c1405000a4405500000c0d80d00203203044c0e44803040a410415401282c91003035000aa03c01c05080403070820601c402c201144031a00824 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 258323381 1250 258322131 258322139
    0xb1e16050601080a0c0b090d0212010b060a0e040b060f0702010507060e030f190c0309060f05090612090f150601030c020a060f0209012a110111010903020303070f0333 73
    0x1c1008001e0b4003020042c2e124041210500400b203006600600d28991007910385200040030035442c00d070007040644110314010002c10ba240c2c0a421025090000030050340d5075010440010f403000c081c1120182c0118601001d101171802e0040440e03040005800c80c15003885010740c01121181e00502040b241280c40e50f90468510404101400428400441180d02c441a940514140040c42051031081007201c0511402182e00603008200303803810742c0f80c00f182e0b5941c6101d003038483d481420200c2d60409030002e140429001d003014441d000354000c00503109250b546c07074001c9550303c07040c3c2c2030703503c2d01c050101c081499980280c0c03000c1040c2c2c04a0040d1842110300352601c6003102c2c05410100005a00050041c00780c1da0321601d41009055144141d500c0e980480c40319030b508010751140144942c10f060f0391004c80c1d0b801444800c5111038502c0c001d02c41c455035441d000f5180d80080c1c0c0c2040100b5041006843c030b0394003a029044107040500c0000da07003c10b008084860518668146055004000c003000c9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 258324631 1250 258323381 258323383
    0x4020702150c010c1706010e090a110304050706091d0a0b181006030b0d03200102130b0c0601090509030711040b040c17060406030c15030b0402160605010b1e1605 71
    0x181c82075410000103031191000802030445048008003005c0000c4200c104001aa0801f0346d00b041c01c801655521050340d6902c00c40402003820030608030307c1c40400b008020801c0f01c0002c202040c2d07929039641300d0200b903541507580c03004e2302000440034452400c4c00015000c02141c0d030001c0a1150000c002a501d07800c00d8a00f00031144080d1504180000c03041c100780300980e014083d10700302440554440280104589008140c2c20107000701180e659501c0100c04050369094042c3c60b5181900040082226514819551a980f0000704003605005140000072002800d1141921030f8030031001442c904001740e9950210b0440c030040c0a60f000d0790394030045955444510480402ca940b0343c540b900b40118260710051140740080c0813512490030034405200140d51141d0313070021903071062032542f4120350150040c0d014205107446550050320124505c100d1940c2d18a00381829405039000f042140d0702c582015507684070b1604a4944204203210104540c1546401440c009000c22016960188070307035261 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 258325881 1250 258324631 258324637
    0x80a0f0510140417040819170412050c06040b091012050a020403031d010203070308090c10030209041808090609040207050708011b030b0a0e06031606030c02010e03070c050402070215 80
    0x4803035800c1c070344002c000c02c110408044c5803160000f41c802a007090303d03015215541d62040000b0981a85004880900308205005280201000b07848104d07265070300d502c0b86110b00c0c104158199920f20519004e0030250501000721010744001c04400c52800c0780d90024081c41d130906da40f40302d0802a125884001718041442080d000d0b02c2d50f0000980d0b29451424001c28030848102d001c15000400c100c089480d0380c0020071981850b902d414000526583c4200309401d14801c0c43ca500d80100c2550030700c184081e41035000f07060781c100071901000841c5145078451103080c3d02640007890303120100107010b064513001000d00140c5100400161070b1031150b90312942481402c3e4040d141d203a4448450410242004030080000202c510f006c100415603040080d036400e01038490400154483d03408100207132424400d240c81c00151905800c0d000b0380d141c400600821135150303003030700552a24010b000545000300885100c80e07001151103000030300700341c2007100039417044004a0b445030711843e01c199807071148006 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 258327131 1250 258325881 258325901
    0x181a030d0e03120f0301031704030812040b160819060b040f0f06110d030c030b0301090308060f032d010905101a040501050105070b190e0a061401080a0f0510 69
    0x1031903503a070a00e0010b0500c0c0001a190008620701c0c00d11401e50080d100b8070680341129007001c1070440361401580c60200342d03c00c940018026000c002031402c282074028286a00952040c401c100c004c1e91103040d880780b0403559103078a000041189000c660b481125103090441e100ca01600012030341da0b100303c0d80016600a40c0004c00500e00b40344c1c20010b8000b980d0b2680c00500650911224a0020045590716580c0d0100040140750761400003110a9110703600c102c000840c040c00811500070780d41400751500b601100d4640c443c009182c0d01019a04001c140c6000c038000f1404004102030051031146948901c1140707000e03240d036a07020b801001c11420040c0240400c2052400654003640c03048400c0d03025400f05019005038103101c01040340342d030f000c1d08a50b50a070300642000c96075100e009540c0100010b845480b1840760400305d5100d41a40c011502c1002248503100404c80c01c210345074000c82c118400d1003051826000034500d00013003800d80d01c1c01c982c2da6211704291001b0b001c40e50000d40403107100d580 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 258328381 1250 258327131 258327137
    0x5030910090807084603030f02070b09010605190e13061d0d05040303120216080d0b04051e06061b010203010e01030302010b09100909051515010810181a030d 69
    0x807116519503009290414084c41d082d0720411542a0f52000c2c035111440c00090a0748085c95080840506219071f100c0d10918030003d00542d581c007154104415050003e540c019020f51a103940052646000401c1400d41c01c004030740054a18a011203000b2052001071024000114182c45440040c18031321038280450441030718845400441c4a00c246401b8003556001c092100420007400425004114465918211040542e0318404152031080721100904014982000841d10158806264006402d032000507501000700c1d41e01d0100500c1c0590a505c8080c0c003800707201d001705110f400d280340144101c0307a0b000c0b0202a032400c00c40f0074a08980c002da05c03810390320074400014010198280644071080c2f02c12925240c1c54280f002e40c1100030300080c0320f034007220b030740e11241c00702005801e1142c030300c034105821648622494002019103c3c03e88136182540094400b00000b000152040009c0701510403400380c211007440d21415080080c0310303007c5981168401882e024542d95030030400d25400710000c0d6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 258329631 1250 258328381 258328393
    0x409050f0d020d02070e0405070e09030714060118090803060f0d08071109010501050c0c0906010c0f110a15090e0612060709051504140609010c080708130b070503091009080708 77
    0x150085c285911500000d81c07100c5000e05000c00304000041080c19601c4026440c55551180a0445d09e1071107000401000045a40012200140003191040c101c401c040800c50448051501100440c0d4403000020006070701400030a1041c100070040c01c42110000d1b022480310609a100c0000395080107400326a4040111011110b50034161080d40c0104000c0c03d10904003025010042c0d00c80e01140465400b6802000000d002a0b2203100c174880b5041c1c01086e80045580541044000780d0b084070f51160084030700c0100068001425030742030b90500c44680e030b141c401d641050709142038030001030041030b0300c5040202081362406041c07103054014115500c80c0410a45044180141d042d410217103541c04500034441080416190352610b42c103010f00711141d56803540b6080050f2804544804041c200c000040b800c0000c0289e170710010154100c140040200c10341c2e035001d580c103551059080041c080c0d0014171035000319040880035040c0f60300040c20b0880d281074440761068a070080c0b0381e00820282d8051 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 258330881 1250 258329631 258329653
    0x206030a0b041a03190c05060c01020c010e1c0305040c05090a0c030506270613050c0418050408090108060307080f0d0801151b03051603090501030b0409110409050f0d02 74
    0x24450665100240103d550b00000780703000190f00c58020143c01440c042550001c0c0c420401601c0201c0091300c0e0003030070140c40d1a104181c40e4001e40000b01886915864100b51802c01c84000500c01c0b04c6492290105165040b2980120003800d005842141c02c0d10241c82c0106450361303059a824850f10021030f00141d9031240e484010107980000d00200d004160004000c1620404410040c5400d0b10800744d103105512154045110b6a80b1041c0c95a4060316107420720240071500c070010812079060703d0414003900385042450301110800e9400810481003000396481c103500995a0a500c0a0000c0c2030744c404c0c65481d0725240c108180901d1711034054214038003115220741c001000e24050032004035090f94048004001401e0010004140360508061083c08410548240210340440c0c0d05c020402d8500d0606140103003810143e406554003113810894a101c1c581060b00c00c510485410254101c010b954100a00004124001003604d89000b90700c000c0c10070076400c001c03859001c00716034003d15182d240 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 258332131 1250 258330881 258330889
    0x702010f0615051c05010312021027060905010603030f091710020304150908031008010c0f14040e100905010f06080a020d1b0c050d18090510030206030a0b 68
    0x10a5000495841c004050001c10b041c2d1480c852440007a0805643c1c400000350901c82c0b075800e44500b0161030f0f0401c8004000c100302d0300c07241c101d08141c40e003c07500101c12176186002035031644151114080c1403500c1800c40d80f14085e01c00e0304514099000020952020740700c036401c0d02e03c80c2d00154007040712241000b06940d13100039003000038180905650500c40164a0071030b1204c03000341c00c40010325008000301d018840d00a160054104440b0070402c60240e49140043d46900b04849001980e200300000281041042c000d020505c0c006554000c203e490782c2200352100d118200c014101c292007800085000b10a0b0102503004495140080c1006880d03c1c1c0054103440b0141c01501a0007485c000400410790000d2125070018240300025803519040e8001000401d0301c050030f0041c001505d007000380c0c825008480c542000b40650203440015050f401c054413000f568000c0d00c031010043c000108031040c039540c0000e8208100c0001c52440c07940c0d030f8001034000d400545450bc01d0715030354003061900b8a0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 258333381 1250 258332131 258332141
    0xf060c100b0316060e040f021603091a0304052d010c030207050f030403020a030602030613141501090605040501080a060b03070519080609011205070503010c020a0c050a0b030117010b06070b070201 86
    0x14000f4400c18855003406402400f08800184807402240c1720a4030080008190301a640c3c0d20022804c08040c0302c17071a0400a0006986101c3c0d4010440d03184c00c0b5900664080048034440c9030004010040c520f43c3c6001244140615165140d981c019000004501d0a003030003400c030000116500943c8480c0305090a50808141d1001c081d5294020441040161030340701501701100d0300301100607141c0d500c8001080f95902c80041c40840f240c94590084400c0340e801382910f0040c011502d410900301410801076030340e10703140c3c00781340013050b0107101c1049250b104080b8545d1200b4142004903116940369015030040d0400c2e00e0580c00b0030400304511078004400070480f502c800781840c10b800103042c21404100c1520b01809462000d8902040c8181840801c0003048000c000c064001c010b00b10790b1030b200030340f00e00c0701c503030221780c1410b280c01e000400d480e1000601084e17480d0b84015a1559190008207461003c0c0c200f40824195203540314450035680312406400c060b4028000000c3d14034100c2c500030b003115 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 258334631 1250 258333381 258333403
    0x30102030a0617010614100302041208070312060e060d0c030501060303051909050904030c1113060f05010e09370204030605060409050705060315120c01020f030c06060f060c100b03 79
    0x617150010800c013101e12170b45500d00e004026100e0f130014885034070003180039124a030041e0460165000c013000030420268001c0191030f00a5071019500300102c5406003d44095101d0403100c8400007001c02c14a2400b41c0c901c8440c01d200307038a041b40c0700d6a0303940c813682511065841900030550201d8a590300c030090000002c2c00d410b0700d02d409007810f800c1400003107a811010b40042c1c03c0200290001c0d040090981c2d04810f18400245103a04400e41000f062021b0000e40c040c0710820407001030300086650242c48074110582c401094284a55a480260004001814410002221845214028400003e03008020305c28101030250340c9508608000301601d07401b60035280902e05d0090200c02084000c01c015064400485a0f95680c0e1100c20050740f5804945040340d03441441c4242c40c0300c901c0750008081da1004407e800340ea04510481c13404503101e0007410910b00340c03600214001500d0b8900684466214600280850705000c03280800b1442c0814108030aa5000e5440c030100c1071a01c3c00b0032050b9112 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 258335881 1250 258334631 258334633
    0x3050703050322081f061e0f0603020406170907030b19050f010501050d0507210b040e010c1e020304091a120303280914030712080103120c050c030102030a0617 70
    0x2030b4600030314542d85440343d0490705640590000d041c14174a55680058000300019000c0c204110040c854411348200d50b4415941046103100700014031500a0081d10112200c5442c1d540820215415035020b07500018050383c0c0304d00900760080001000b40c140706000b50031180e003c80c000d200c0b40340800212103000d40805681c4200c900100300c0c0d43ea20800300c50b080c10b010140811035440b0b66606542c011038494180d29054050034a5000c0e09141b81e00c86010000121002e0140c03011902c0c45508881565640e0340c000741c44c054140d1220f402e01540c4428519652040703d161999070310740c20f011143d8100c103032000d800ca101c01980c0c50b0719001514003c02d5140101039860340c14540f6000203450100100c0424006030303c144c5a0740d0207065841406001d410017216801100030f100205d0b02d99000007001c0303d0f201c0325866051302540c4224081816240c1c484881e051209141e0400d50340c800b90a181120103208800d00e5010380d45007070002e1402010041c030081216824450165202c464502c003101035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 258337131 1250 258335881 258335947
    0xa06143313050307120210030b1210110415051b011d010c0305010e060118030b0103051c050a170603100f150503010b03060a0e071203020304051e030a030e0406030507030503 76
    0x5c0c04503440e0f8101c240d58110b40421b60086042003e6016100c2c144007254005091154400151004142e180203130904c280101318800010030456210301172030050000094094110106950149004000910350800f591204c4800300d03240320f00f5030300c541c203400820b080202000741c007180b02401b50b20009021401c0a000175030500303c04185a001c0203090b181001400c44071101c0144d42400764401a54110b03040d03120035a12810b20658620300d580da00f1103104800340d0702c201e45a1142d8240e9106804540d40d81a61003e481084d0f10030342e101a01f02a451300a09441850000c1a446100c40c60182d1341030100701d46a031f41410b01603c688952180c7e00a90601060360125a0013203006540201e80b040c00040031200c03049400d20780400d540050984489040450050540010241c003c50b203040361b4258100501d18808198103800d0152140c05030312440b101400280200401c4c00d8164010740001601d070384c0c03a11050b161038080c0d4019151a040003494034449030042285031170300d1480858540b4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 258338381 1250 258337131 258337139
    0x50708100f0b0f011206090f05041103070806070c0c080303070207050901210b090f0a2a080a031103090604030c080c040504050303041214041502060a06143313050307 73
    0x500110310f1a00320704202c50745200c1d80d0484029440b0f00090001e00d0300030403101d01d088080e4802004152419942c440600f5441c108031704d00041e4107403d0302c489401400d10380d03c8040080d5044010769004482c03000800c41c02190a0304c08101942c0704001c50390003081c150f4034000034813521703001c113810129416036803507103c071003030001c20180103e10b56000c1050b010a940f801c0c034980c20301d4082c0c03045441d1402240c000350140032100bc1840c0001500404041264940030740d14070040c1e5840c451088160020604407001c070b0300482c0706100790850442507c0c600400440040c4640e442600102c1d045040312805010303070201000365020b004011f850406c01810261980f90703680c000200b0060010f24000d600609440c41a0340206510307800c1c122072900e0b10b4440010032042010842520700500c0f5078000607207990b4a40c01004100c840311455100601503140034418404a01c080c031640c2018280060828104001c40241c1c90040080e59030b81c80d15060107600c44000302aa0005100c0e6001150901c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 258339631 1250 258338381 258338389
    0x31b070807060c080d020310140603042a05270f01031707060605090a0504020f0d030813020d050f0304230109060305070e0d080405030d0302180607080403050708100f0b 74
    0x140075210507043c4404518201d01e84080030b8401e148035119003500100a001c030344a00c014684c0d0540e01502000b500c4c0c400504140012400101c0d4054400d006e480113240150450f0b10303680c8622404200415404c5072070b84041035604068920904c0320380320554600d42d2540140444030b8201c801410b043d84503524645800e95a102079814041c51000d00050100c2048a1940020010000030317048084a107003032010300c8001d00c0100c40c168022400c9c0b10080072180780c1420b004a5155158031201c4468550362200d010015031900f049030801400c400100201d801005031407a640e407400011076030783e401e000150003030f0305040c2c01018641c00b5415400d55180c0e0050003650076070360306150004a41e600c100342103803100700c05040c0d00e170000e458580c0f52090103040401030050b9801a01200c5003070b103499600314103d01c5001102048610410820001480c11400030302040703002c0e081c00c03400c4c1516074807454202542c0382e10801d0305c3c2e0311000954044040d2802071078584421701008018501c43d28000c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 258340881 1250 258339631 258339643
    0x31e0f0c0d082115041802130203070e040510031a0c03160507020d06150f080c040209010228020906010f1b29010317070510020d02041502031b0708 65
    0x10b00701140800d00000410666402c0d1035030f011842c810820702d040c00492269001510501940204c2c00d2102860301c15811038040701d0850703400b13849240361003480c4000c040290005801082041854034055020303036200c0c000c0900580301c028603803a480d840d42c640100c049040110f00300d140076202c003c22400c10941c0050f203a2001455a160308800c4000b502202d0318030451000070b5006400c64200380500146034022904900c4410807000c01030344801e90b00d09c91032018030031403580e980a01c5002d04503061076005400390740c2040c0100c500c5401d1100340d0040000c0004404c21100c4031140321501503140913850960041c1e02820007080d0407a41e550003d00d0390b0484030382805002c09010703201c0e0800501503911211842201352001141405040318040702001b0300c002e0b105460407024100c060300030b8504541d681980079000304624480c50070210081c0d0000150164810341c02d00c000210b51414218800032070440c7c1c0d000c0d5595900035116240300350021001072007103038440d110900103040300050b1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 258342131 1250 258340881 258340883
    0x80403120f150305011a2b0609020603010b0316080f0103060e071701060905150a0510050706060f030308310602271002030f0405090402040209031e0f0c0d 68
    0x216244800305100000b030441d4801268003400d400c40000180071042d8002c1c07080041010301c0500f00e048103c104005000355081c01034101001c4c445420b03210b40d04049141401d441000c000c43c0e07428850b000241590000d901c0750070099000000c00100c6029900300e07000d811500d091801c21424502004d642c0d01105000040140f40e482c9244081c109080100380c00402402c2c40c1d0701c689038125000c10340070b0010b0f4800c0200c40c0341048040340c0c0c00c2c80e42d13292202469102420640380ea84c507110030003203c41e098903102000c0c0b190421490011652031b000e100e0151910280d0009a01c2c95490024500c0c4030050410000101e04144080000942c101e412440403c60700410000103090405d031000b4414000240900c2c0142c26815042e0302c00320403100c2c80d1000440e11f960400e4030f403840598803440380300301c0c5a41c80d9404100500c090300e40071b4006908180060801420076980d41c1c00319250001c114011401c0c418000c0865103031010410508071044121006400c10254410208413900c14180d8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 258343381 1250 258342131 258342167
    0xd050403080417100905160e0c03072304120b0f040f02060306060d0203010311030d08070203120403030b2205090a0302100b19060c0203011a30030403080408070501080403 75
    0x21001c10f00c0010850074107141c1c2006010003001030075260071692100b00803580070310f101c5019000959100500405482000140d00d0309244d03982d0a60100c5d00302c03000d100442e03020114002c1d640c4104541070007a0024098903205e5802650076424400d083e00340080c0142c5054011100b00000181610605099194184e03101a01da48402000501e00d01801c0040080c6078808030000050090788056403030071070b8080d82501c26400d0410030407074050504a81500169108020701c03034001c0c042e000b0b81c0da44140241380c001214241361002a940d4802041440300304110012b404031102000d210f00c03904051070030000d01d004001541c3c0a0340b1144c0c50180d003150190799098800d84e5484004d0070914020b00c0440d22807002c0e07115180548030300c1102d43d00764065840d161480c80c94401c94102c1010702e40004125010580c080c040d102040450b40005600c0072a01c01500f0200e0f00b000c00190014520558031309840c4c908101c00d030391600d80240d0195040117262801d2101180c1c108040080c4200500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 258344631 1250 258343381 258343409
    0x906030318060f0d060e01050f06070321060605130b090d03030f0f020a02031c09020a1503061a0a1121070f0f0305030a0509070e011716030c080d0504030804 69
    0x400082d580d8002e512054038140c4001610424814a950005c425140f03549070501e41a6243e0003805401119956426041902046080003203801026402da00c40c00400d4080c4c000e401b610f505809584075640254003240f404070b103150349400450300003005050070401550501c1e0000b40051000440b51601405151766540403000b582400c1c0c1110210116260040d5940d9130300d981e00070b660341e10280ca103038290010f150381e100d80e2055038081c00b8401ca400815074407035242000711050200c0e818032174440c1410340d40d440000e01d02d82450100f42d10046a0351106440d103226a4024083d001c401c1c68203142c0760041c81419004c40030200e00359800c1007800c03107200c5d00c80002d45009800003503915400ba000a01d10030000040544c050300841c8110781e041c000b80526202c82c100075540746540d00460303048176991001030042d007000148860007078215030700300d40f0324810b140c545050ba4070007900141c40a08c02c2000501c8007d2003040b500d01c51306801d1a01924042c07954075941e429001d140114594142a9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 258345881 1250 258344631 258344677
    0x80c190521030121051516030203060d0303020c030702131506050f0a050708071a0a0b040b030a03030507091706070908070b0703260717010801200a1704061a09060303 73
    0x241d51190b016580320048802c0d20640403480180040100d441220f0b00145007c01c900041c400d00076a4043d0340040c0400418450540c0d042d8080e42000900000d2848144120b00159956211003408080d84000005502203180040048950f264100d1800c2c80000c001c1c2e151117001c40c00c1100c4103481103180141d120f6035a46011b14551266080241842c0c41c1071100c0c442003084140c0060090944050810009007454184400c0d039081048240c1d16420003144600464040d400c0030303030300120628000c0c90b542d44800d031503015074800c140c0c03c003440d078400d1080051803070304818010054840d5900601c02e81e4649a0104094400d060004040102c024151542c0c0491600101e41984028245201d03c0c940100c006044a0340c006000300003200c050000925003906119590200e0150300b100f804410a030f588415080e070005c01181c0810200d400250403022034807807505c1c000ca2141078081840114507090f8008441e1504619110320350032011701903d41d50001c2203400d00013070120703400507001036 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 258347131 1250 258345881 258345929
    0x409150e01140a050f01080a0f110403050f060906091b01021f0905010c0f23042705090d0e010f1103030115090b09150304080c1905210301 61
    0x4954450348090820344004142c1c00344240d02044560020746840600710350301ca0400c103e4203030016030301d03022070340c1d40010900b124696044048602c00006021030701d0060070360702024039481a40196480e8000841650034508103008442e001103101d801403044c0d082c500c0300c0c1c81c1c4643d107440d4200d01d80b92254150860a034024442e01c0d582d03024a4929031159118043e01601400490204564a51908140010440c06481d49401c3c20740c8503540c0c6400c0b000001c10821461580c0c1c5900380c0c0c914000d0200080380061041100c8085000c00708016001d41d8006440f03080d030f0750142a094284d0414071401009a502c030300407011031402480c00400031111180d084c1d07440c10300300074072620a0000000200c2ea4007201c901013429480656503070a90642c1d5850f44213283d00401004583c0641c24040390b10048900720051031700540900c041c3d5180c108410155032a128250300d4071400b40b00d001c1420300070b00405100b51f1452882d094614600c900351609240c41d544014000c0040c804000b071000080c040b2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 258348381 1250 258347131 258347171
    0x2703031c091b03050c03010e0706050c0a05030a0918051b1c0c020601060f09051507031b0309090b18040b090c03030706050f06150717070204090c0503210409 69
    0xd00a09004400000303290300818601443c041078400784a00d54a0f42142c1c1014401c840d0002c0e0900e02400600e420a04112516804042010703010f109000c00c1c0000304d00284000c1000c1d00322a1100480d076443c0000d00c1b07190b0a03401c0038400c0218074000410091203001c285d029552642006940d82e540c58140100c6411001000100341240c41d0542030500b0980008400b0f040e2400c80d11807055050003203800304d42c4215079018042c4c0100c181c02140e02c8241030368014064440c03190034100e60460f40b003180841c0001502006030001110300c07008010501d4203110b07005024005440300e41e0b07260b1755564248200748010300b0003481031071440009a8203820601c000c4040c02401015240e9845070345c10040068001901d030101507440f0340e00030602601d0050400d00c4412000101c0b01c0c101100c0e0740f1070300b001280101c0043c5204000f0400030700142d449201d801d134010701c10140d481689040c401414501840316445107484020500c10406800584055800301c42449102007541a030410801e001e4075 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 258349631 1250 258348381 258348383
    0x1a07030507080d0509010b0406030c0b0c070b0a0f0e01030c0509120705040f0f0c0207080703080708250b0105010f170a02070203150417070f0605150a06052703031c09 73
    0x80c0200380c00b65201c1c010341129000f172040d003009000030070101007008101c0c1d40350301c0010b00200244004004401011001e021090288000c1da541c59540e09445a000d5100c600300000140120202c21403460300304080700181102860b041102050b8034001501c14414440064032900f001c42c0c403c040b2030020802c8501800014100f40040075076001103d014258880240c505981414404601c06200103039080454072424002e1640d140b4544459459511046069030045010071021001c10144c00c1c170500e50158044100b0b2240c0c3c1d035401c01003642041078100b181040303641c1d00001d0041d9401840b12582854094500c0c4d69038598042c880000c0c030170410025054041c1001e4070514801214005108038000d41e0500c0510008100d254868031589074000c0401c1011611400450b4080e4401c0b0340c0450103c02166844154100040f000c0041c1c2d4003e0001500024030440381f18242500c8282c0394410310700000c1000300500000361a80211945110070420b0f00e900030b03002c0d000c1500514111 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 258350881 1250 258349631 258349643
    0x3060d021c02040e01021e030a091a190b15090103090f03050c0d0305010509041202011d030301150c080904050402060f030115080903070506151201020d050703151a07030507 76
    0x48810780d0040310300074081e08401e0b886070f880e184c200022400103000711740c003011900014170400d40201142d400a5007002d000c49200e90380c1c0f0703014100028001e101c02c4d00000d21000c1b4598041c41c0c040102040390b4014820f0380e107680d007441d02c1c040176a190920080c200640d9180e00310345407407850004800a0080c1d00000d480c0080542010b000d25030084000d1000d8100d100607101301004059041e4255502031161941140000000401103130b5440b00e0804018401c0c400440c04020203072220501c004d11081050b8503800c00401000700e44c000203060300388060607003010250b5500c0c41d00e56030f10501030005c2c1e5501a03501e40740001c045540d0403048885001c0301c141c1c0130f91030303584965201051b8142c0b00541e02c085030640000c5440f2000010070b0b1803806900100030b21565548441026070b66003035010061300302030f0b050381380301801c107081c005080d04900e1604c0004040c82c0140d4002d0a440c030003085181c0c0800840010302c50b207a00c000c44c0e00c0e8101490710782d0555441040c6000c80c0c403482099405406 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 258352131 1250 258350881 258350899
    0x2210a031e0b150c150a1112070f11060a0c020c0a030c050301050123040b120d030b0907090303020601090c050d0614030c04112a0109240507050405010503060d02 71
    0x32507469000058825050b1048a02c80c1c01c910040a49071142c01c085904030341c00905030a20700d0003803010350740d0300070b140310004034001500d089800742c26081825106203140714001000400340c2c0c01a0f41c0d50f80b144d17451400c844656401c00c0025103960700070704102c41c400d40794040800030500802204107101000f034400461155a0704101c070700c01c000360161078465402c0c6030001580400707504e409a040942503209400121041c42004018100301454541040e81d8010003940d00009210009000449403030200780d140011042104089009000c00c092001021050020030b600280d00740c155040c1000c0050b042500c01003e840600482c0302d2039100300e050102c04501c11445040c40e50698105604030380d0782d00304803010801510b40c821100512003c081c4000b18580d02c2504064400c420062000800146001c2d80a425038000280564000d452040e80302281c00d81c40d03114080458280c0000c00a90601030001040c03845140700b01e074100031021011032000c5e601c40d002e400c00b4039030040c12609 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 258353381 1250 258352131 258352181
    0x41103060106180e070e041802131a06040e0705031003050a2a05010f120b091312110309040c0e03010f0606090803090d020108041505070206041202210a03 68
    0xc203a1250901c0441440349683d0000b400c1c4044401c40c41c028039140d1104800c000145052100906104ca40c02c544400665540005a12214182c0340d05aa0300400414206904409a6000030100c0380c22400345104001c10000709031f880c80304075040649458a255a41c03180d000080e00b003480764201400f0744c040e03094080c0400100d403801c0051007008540440b403200c0100312200080c041441460701185500d03481101c810b200340481e10004209103000203c1108000204094580072103403041244d05501d03aa00500ca2881c51880d07c0800c1e919108141110110303105899029034144033b4000c540b16000e91180350700032105042c40800c0900204940b0f050072048101400711841010302203107100e540410310005c0401110030180010348007444c0e207140c0740d0044031610b20040c400d5900d00003100f1011280001c03070189502031030841d03000740851b082c1800c069200f0045141100b040d980b000112030700342041d0070024030222101111158071004203c03016005071103120061485a42d40f044079035 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 258354631 1250 258353381 258353387
    0x4080106090c1b0b01090e03160503070b130f022704050c09071b14070b0408030c0d030e0d0c080d0608280302030f031b030a0507080a021809041103060106 68
    0xc0b018148559030882c0d0400050181d400c040916a0050101c0d961400180084c2685804c880804481001240d2611045401000054001a1003110340d0382000484074280804121681d400003c4800740400103c400d80d2110300100e51180c0007801003803440c086040e2180800300700c041c900d0464145000f586000c0c604252101400215540304003411070128040398071480c1c1204191404800f0b030910032200d41ca4001882c0d0076130b20110168415500041034078003001020300010003040700207507124410f0030100e0f801d01d05004100c02c1014540140c0352000980007070b039407800340c03030728140b05000380001d06005220344100c4040c3c0740d2207030900100145030300700056a40c00611080d44020701514402d0421180708031600f05c00380c016807090100101900b002d90041d5006891010208a1040703400c5a00c03005420031200400125621020040c4090b00101d003180e100ea40103404521b4403045100240728982003045060080c1038000006c0c040121815a00b18400c10040465410350794441c002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 258355881 1250 258354631 258354641
    0x70807031106010e0c12040f020a150305150117041a13110f030a03080c0409110307020c030f07090b0a0b07060b1c03020a1106071a0109110301030b0109050c0408010609 74
    0x30782803511500000003454204807880e039004101090480b0b15115807200c036001c01140103081529050240d099400c0140e498000701802130284841c11078504058010183c201c0344000c080c1c0b00c2114509450340000c0e0707400386c1541a0f401081da00e100c6180c5840c1814403041648000c000d031268486424810707164594060310320140c0c818401944148024014840604c1c40050100e40540c425400300001034014074280d580070700da1540503428035503030b0768080007500c0d0b070070104000d0b116001083c80340071a414040c01c60f210303100f07500510610184c0d4000581c5c400d114030425040c16690042030701e0699400105800600c0e075081a5a2540b00d1800d00c44010503000d16294400c520030110000c0820072140c2c0c0905564042d0040c1120006a442c1c0c10640bc2400c40020783c0000c0400c484c80014200346580c1c1c038a401041004062503051201c0d020848500740700000b000b20341440100001100b1481290642d215a80081856100d200b8909814023803504841c060b9420311501280c0c1e08496449 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 258357131 1250 258355881 258355907
    0x703021e07080d0201060308040311030a060f09140c0d060209010504050d0b0114090405030406120b04020a08010e06030a05121305030316150e190c1517011401020604140307080703 79
    0x19074407141180300f016400c88003284402040c1400030b000c1000031404c00c00c0c554032804000b40940b010f00703289554610071580c003054248405980e8110484c248003880d403038218541a21070040810010080c0090b164441d0341e88010446074000402100703a900c108144e40052001416104c5170801c00d180070480b811090091600e03103418404014410319024006d81d00581e0068051450176080034004ca40707011381c80203141501e9884d00072140e4282c8580c0700428100074603a03645c4200703504010002e0605d200c00307012140b0035405409810085440400c03108664100300300880e55510603c81040381c2d2446075032240f907240c0004948100214a03c64208600620840319035041801400074a003c03074040708206c403407541c000c8440300740040580300b112404502404c003610030170b07030b81d9100f40078800e080400d035000003040f04c20305d041d0709078891b200719025007005546145080c1440740000c0d42c4210082001d48022030607651400034441c28000c40d0f40c00c94106820a503180d0700350602400301d4005500f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 258358381 1250 258357131 258357133
    0x5070501050c03011503020c010207080705030c060703050c1209100501080d02010506010306030803042405090a0311070501020a08030a0e0d2606090601030f0e030313020a091803050703021e0708 85
    0x1414005544040f00e0503101d8080c0404c034040c100c140202d0003074003c01540900c940d4200035a034042801300700501034007071140c401147c1d01e50700c00080d02d041081c0504148203250409040c0700848242c034094440c0c0c5a60300969140c40d94840519500d420900003450021928010010480c3d039804506039081c00d42d10b4000b4000c544a0700011012a01c46210107400031209001180000c4c401000c3c0412042c004101464ac0385c1c6855001c0085480075205e0500c41d5000040e414101600702d4803500e844000360780505075052070140041e4462040d03c1004007840d800100042d0700800340c1d4403e07002c0740442c10032103a89042100d4054003d81c000e100038091402c030648450b540360380c1c1d058094854140944595038a84903100103402230564100d110b0341040e1599603441c0305e200100082c500ca400380d00c1d03030421241414014070070001d266401045101741032144c07110380740140c1d800600d0032590500e4140d0795081f041c202241400624845034543c0b00421030036841c001d00c0081c41d070040c0d030070ba20 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 258359631 1250 258358381 258358391
    0x20a020706020a021809030702030d0f0201061a030f0405030d050a091515060e060903030d0504020126010303140405031608010f0204061b03051309050906060d02011205060f0a0605070501 82
    0x700140d940d40d0311440300035402980c2d90b490fa003040300300100c1c0039004510700d0b003240e0400200d03500103030900c0c030f200303003018002600d00040300180c9609015041c020400c0601d03012024485a120203124880100100014299800801c0811000b04215019054140010092410210b2405003d0281c0b4201034400850040c4a40c0341d11b655071080d00070854507a240e4041c618584030081c0c8082c84204c50055001009110401e40c9450500050180400311031000070303a440d180c4009062101c42c0300c10b000c800b01510381e06541c004d001000007815203401d818003200140c0c0101241c2c4032481503800564060140d24541d18064800c6045c801c00d13214220000d0080542e002c000c0c400b24000c0303100d0b810000c1c0c1201c1100c2d100d04491820701d80c840d07010780b418500c2c100607007150f1001d09407a6440390f181f0a54400c00c00c40d1000d4144040d54000d40111081c500415654000030f1441211010480c0c0260751a40419000d5465042c18100c03040c0c043c1001112594444018105400040040d10654200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 258360881 1250 258359631 258359639
    0x61e0203130e0f0a0e2104170f1006030b0705070c0f06030e0607020c030a080d02070b01080d030b060a09091d12070c0504090302030f030403090b030c1908061509030a0204020a03020a0207 82
    0x45c2c0514840f5140354401402c00c5010542c6c0301032042c00c481030281107500204000700d01149501104004105550000e01c51240700b00d050b1407801d2418401444024501441800000c0f01d0987c055085211f61074525181c103600d04009980031500c1d0300a1903116030030a800114283c254012800407000501507a0b503681c0d4048050781c42d88102d074225541500500310759000601400054102c03503802010060420f40140daa15000381c80a800281c44d42d805822440ca07601c0d4140601c07001c0890030f5680c0c0781040358030140a00b03244005d024402c030b100c2e00d0b903050310b0004031030740d24241d0075003c990126040031100c0203d2412a900031607040d40c0c40c114401010540d030415010310943e03141e159000710b1422280d03070070050051708040c2040701004034560001522011010185004451106949507194030004e2070704580c10a040c45079041c40192800c22810356100402d42010381d1142079029594000b07140006d0500302012002035120f031003c160191515810760150400a00c00d8080f28401511 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 258362131 1250 258360881 258360901
    0x1d090607091a0c03120702011d0703030503070c0f050106030c1802031504050403050c07060509130e1b22060920090f0406031e0c0906061e0203130e0f 66
    0x1450003100451421a200ca0706802c0365034006101c5442501e050340c2c207010600c20a0308402905550080040c0e4440790442103000d90b41c0500c030840d0703d4030b0006044491440c0d40243c080e0000070411070502059a81d120284510b60204400d141d034004000c104d60b64032482d1000003040790340181c2c000c243e91941054a0404244216030003210b20600e88420700120b003040002510000b8000c40401005221314400c440d401c10482025010503142e1607210120314051010300248000250710705804d00b00d45081001c008195107030309079a0110b000c800c041c120700226400c600c1b8004d401c40c500200030304a800b4007540d83d0103007007664150f0b2002d000c4000c01807461a05207400c4ca9040c080345200304440a80c501c0d140c0500000d00c480a48082031180e56a01d0b062605102c0d40c0d132280d03100701b8207200b030f0042054541880000d003021100401060742000d82c001c1c005148801c5ea0200411143c083c82101b80c002c20942c3c2403240400320f03802ea00c0e920b969003e00020300035242c11121040d0710010800b100e42e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 258363381 1250 258362131 258362147
    0x1c030c1b06050f0a0608030f091807020105010602062401110f10091124070204060b03040f0507060908030f13170a0c060302072406090f0e070b030601090b03101d090607 74
    0xf1900e00440c2802c45023101c01c1c1e100d62021210f240d001c03024030280102c040075a912248600c1d030700e800000d06517142c120080c0c00c00100418050341d0440caa04c2481001071005055400000c0a10f48400800000308069142540f14442e84407984201440c25448480c00d4100142c02841001c0303101c1800100000c0c41403a40c1c0282d0311020702110749410f40803284212000c0c02116000400c00b00e031860303031042c5008295000b07a50554070b10100300d0241042c410100102c03002000b42c0d1500702a0070f4505003200d5124003868940804129000452513004500f115018014004c040030b9007090f560b140c2c00f02c60f5580d4030304034121110344000c0c40c00690180a0b200340e80340d050b048151007040300e201d583c0014409070b001c1a84545142e41d0362012818070003e100d03455082e801c2c9140010840c07280c41e6014913200495100458020701003003008816603006844c1c90890301e1114000c0e03283d840d4030003084000d0031107400c02c0e82d07000007040000446084221405000309246425074816482d03001c0c0c03c40f0b000e8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 258364631 1250 258363381 258363389
    0x51e031e072108031810020a0512060a050102030a030b0a080106140a0b0c0c0d0201020114190b040e030904020304020111030c100b040e15100f0308030f0106021c030c1b06050f0a06 79
    0x94400c4c40012140600c80444482400030ba00903a01e10030303d51941402245c010054040014401040d6a410381c8a10038186400c02c5003220600e070410301e8600000e607a8071408204508040d20b03016045150340702c00b50700b00e01401100300240181d030303280d80401c80709900c0010b5151003801882c2c80003440704000c1e0708590900b4800d1024000400c43c582c01c1c07100e203109003841241150340c3c3d82d2040c0810301c2007030040d5015400b0584900307110541c000c0f210003551000c5902c0c0d40b25a1800781c1d0208400700010464040f00405c1e100541c0741c0e5150300060b100d040443c46602164000051100c0c0440300116007100700c40280e100c100408004202031000b16008601030480560084140d94649601e030b840440d409040401401c06070790300c0f410080000c550a50080710009404814004820000c0e04801e002d4102ca200814814480c00e481160746090514544113141c0d4a180362050b19120340780000b042c807901150070f0b5040415162480007043d00300c404009080d003c00124006040c9400b0309030880f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 258365881 1250 258364631 258364643
    0x2060c07051b0117090109060c020c0906040911100e0406122a05040608011b03090305070b060607020d080706051f03140102040f0602060103150204051e031e0721 71
    0x1d1890b0070008401e5004042a20b030501200c085401c0c40d924038210254412070202c0008100080c0c540b400c0410b94411461074800e54011200015498446850455000307104a50100300d403449404d00040c40e500940b0440d800c0904031100921050b044000c25407981000c0e90100314056803640c142583d520380403801080c1c020750749080c03d83c504100307400d900c80290712800080b416507501d00280c03c90b01030742d00005540c0d4440138440007146800f56a03004401c06414240311100555074001d1180c403604800400f0084a400071a00301e45802060b900a654040e00c0e0000b4190107040009141e044408100e079a0b908000019160210041c50706804844c00c4001c00c42090456580541c1d00940ca419442d4546d4203020002d100c40e900303a0210004c1c00740e0703000340000e075044d030520301308800804104128050041004004945490b00074683c081c5400c8104041d440c00d40001030305042c40c10302050310142101c0d110b440c1166000c2030100031190081007588a58000c0ca00024460b50800005001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 258367131 1250 258365881 258365893
    0xb090403030b01020c1f03050a0507050f160602040609090e010c083108030f0106030902060901110c0d081308010b1309020d0b150f040902101202090303070f0302060c0705 75
    0x3034001e80005040c91014015140b80b1003e140200300345000d503404c000c1c00e0180c07614200c41c1d980d406101d0290040e0440001303116519001d44058135030320485800d0402c002c2e0000e09100c90b032030320984488046038082c1c1c040d59556980d0341700034900b00150144a442c0c1d440d0001c071a481e40303c1441000905009a121028541e450110112101a01c1030304102c0740c0c100d001500340190701c01290100d40c91700c94000192a4140701d2110201024140c01c128203051030166100b015a6070101503d0700b84c2c43c05d10303000184200d030003103841c00c1451514800f6004040b40000c2d000b00880c14003e800e20744100040e00003041d9446108078241d48500301c9036134002c0801c800e800e6854500b60005030501d400500281c0080b0043d0b500c4810406007220340703441d80304081c10407854601c2c0100c3c0740c83d42d11f0001c540511030280250002011030314400c0c2d4540500000c180c0508880c440e940546441c504010f05a80e1560080c0c10b06003109442c841e4110010301132a000038100d56044410b0710318240e00b103401044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 258368381 1250 258367131 258367133
    0xd0206070503060d050303011211030d0503060d0611070302011a061602060c1212060a06260703060b070510060e0108060f040201030f06060c02191a03190501030b07080a0b0904 77
    0x1560b038800f800e10b40d0465441e02000300031400400045000b001d950806425112040c18131066003c0c000e0a090320a41046041c002d8159108007901c5d040360044400509504281c41c1c241c00401f00025450001c0c0b10101e8850103254065102c440c914060811030603903034031640308208652051804195005505410403405800c051000d0308500d000b4100316010619140709001b05500030801c001c0d0011700040800c151400d00ca4501c03c010000b40c02c0060403428407401c20082c460080c0a400b484010f050005104548240c103c01b00404a43d445039030b50300320504226407100700368940c41a0306410600e000641c40b0783c407182c1e18100c8028102403d115115121200704050020700281e0415840f10050075030000d091150388020400e076180c42d85a001548184030070080030300354203a000050890100001204103170318800d0400b04e25036265403a038032070021040c210b0501854020132840c00c40003008201c860000c850003225a0303107508825507142c021720015030b1a20f0050035001000302001c54 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 258369631 1250 258368381 258368387
    0xf0b0f0708131b1a0c0712151a130e060f01080a12020a170a170f07180807080c03060108010c0c0222090c060e0105030405070e0c07060c05030a0e0d020607 68
    0xf072041d000d500001c8040c0e0354a040e082000c90641e18600340100020b582c4184d100802c40b0400904020304c030003101030566100c08504051031910408802c0c0c95444081c140c1d94002c1061219100c0200485a640e440c004c01c0d0004000e14540240d82e849030502080610030642801812580c0c0c08000b03000080650b41c1d501119021101030509600ca403410030b00000300b900e02d01928175055801070903168210307084001c2c51700030f070104129889484041403100794120380e95907a501c10306038200741408031030040d40812112401d51040c900c0c0c0c01a45404900c004012412120b800003c508584081e40c898442071f00700e5003170b80e100c0004244194109001805c1c40440a800c4684620319008180035003104d0b101940c0000c103084a0462825005018042c1c1020b44107948080030318042e401d501d426581e941d52908140a40c10a920b040000503a81000c4c1c54110360741140e0040c02030245401e6494040c00c2508280c4601105604000c281c4485160000d03440b055a0000e81c014078454903890825 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 258370881 1250 258369631 258369653
    0x60b0f0d050c04090c091e110a1715040e03030a1104060f032c0a06050a09200f1201091109041505151509040509030a02060109180f0b0f070813 63
    0x1700c0c0c0e00c0365440d200041e40d0741544522210920441d06982c880e03071220024100700c1c1c8031000c81055292081c000d000f180c9030303c4114030f0f40940c29070740c100d1010344071510058040000c0121807513106003803c025041180d00800510700508c8071402c140500100007204030003038040c0703015680005031490700e10b0220300d100750040c124030307225540d0034404621360b002c02800024031080440201d52040440d60204040c1c1d128256000540020400c41c00c0d0700e90395140e11441c01d4010300d114040000300c03105065500c9170b110040e2410000d00340611651200a101d01030480602c056609241e07007011940d05041003001140f00d40da0000c8070400702e440d42c800882c000c28000e01540c0c11a0f00e5144100010380712a034042d02c8618501e05165200c4150034108001e03954002c0c00848990401d009010089030001100d82c1918001ca80101d0080c0c4805001e640e041d03200c090140c003003150344d00c000c0c0c1803081064001e4002c4007881035111144ea542c00301550800419903c60b64480032240c5658045040300000e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 258372131 1250 258370881 258370883
    0xb03040807021503040303020a02120a05040504020c01060905090a050d170f090708070623070b042901170609070e07110709020309061e06010c082104060b0f0d050c0409 74
    0x142c000078820000f0f540c40c0b02d40084a00b20040303640000d00348082ca404206c03240e101842c102e08540740040048000342304c1d0141d84151b074011030300403400d070480250a4000002904880400300700c103240000e2030669075414504240d55a0140c105110000340c4180c0318054816044003249099841c0c03000207100c0124014542d0105008a00022440384820b001d80c00c002d140540e50004403008174403102211980442c00b10941140c09c100700f03000101802c10441d0b0080c1c10982c0390344002045c000000300346200d120103440300c444da00000303c1c1c0c3d00b00040040f841d444000c07040307403000d40c0d440403282d03a01c1440e4002c88141a07418000194020701c01c000105445040500f81c80407141d40e0341c400c4043c4e8005032082c0383c250300041c08200e8507007115803c3c00882c588e101c1c040349160514500180841c403142c4070240c04010700043c0c50804034020007124000c00c5860300b4641c1d1515003400c02e040204102d10000d4419201086820700f5450102e00a80c08540c1060143c40703448100402c200003040d29800c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 258373381 1250 258372131 258372139
    0x80a0605061801050c060f061c020d0605100f030602120708090a2303070501050402180103120318050a06060302090a14011707030f080703020105010e0f06010f020c0a030326010b0304080702 83
    0x448400317041c4007801070314094441410595540d0801d00100034900601508805203840800c24040c0583e89241c0565003964115000041b180c0311219600b02202c060307000f40c6e110090b09140002003003020340c01441c1210700210382841a444901c021110703d4030549110440d0f51000070001d0200710200070302000f10035181030f0035131600200700d0181c0c01e681003408255810795494040109500301100b08032030079010360b201711495604542c0c44d0602d070245082c1000406564000840801035190310703402c16035412100322844a2600d03d0aa00a0902404202d004541443c0400d507404e40c1c40c012214440c1103240304040980c00c1030300c1e84900d82030040b1441428420300500201140405403071144160068102c1a9102c006050103425104103034402c85070000600108041c0c05400002940c202c142440d0048110501c490b08a00d400b20204883d5889188050000300b0190045503001c1040d582d59080b0741202c0d42810100901c1c0030910680004081c10400540020900700040003c284020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 258374631 1250 258373381 258373387
    0x9070504090e0c030c040209031911040e0303070e0301022d0706020f19020c0a29030703021b0105070203030f04060e030d09061406130e0708120a080a060506180105 72
    0x26244068810b402d84a0b4110f820040d00000030f801e007400320000c02202600c1c154070b001c0004010a966100391401c0701500c542c1c200c4c81408100290144a0903103500410034018842d41080302501d9500a40b150341c0850302006c60f0b8102030506001341c0c1c0102040c1034980091405444070620312224200300c0f450310a1040007482d0006003984050f25000c4401441c103502c500648140032b0301c058204a8943c155070040c02030f0343c2c003581e40390804802d80d00503a400340c9051024007103840180c428410a20384408001c800c00414580c180d000d01083c51080000e0418000710003081422184292000030043c0c00400c001400d9610b03490b13105410070312442d0300180301c5c9041c80f0308a0842c0c1120480d10a81c1c0d885007441e1041c04030740c0c0202c50840300b07135002001107402d20b540007449a96414030849541e54a074000c81c561070308184000001040d811050f5a900c3c0084001000785600400d280008100880d001c04d01143d10f5118a00550b8009002d032454001922007010400d00d01c24542410042d0030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 258375881 1250 258374631 258374639
    0x17070807270609032f28090c14130905060a0803130e01080f0a1103070305060f04051203010609030809130f0501230f060904062402012909070504 64
    0xe08860401800d040e9240e428803802d602e8131804010f0b164030713a586130000050311552107015904041003e00e40c21903418403e83c64404500341341c139011006c50002d03d001810b0004c1c01e1202900a080e810502d03030b8440f490068030400804850240f881c0401c10101d100006010083e503070303405182c2080000b032210f07088590b20144149142e0007481030fa4944d1042c2001040101403c2d0701441c00b41000f42c003c2c140010443e1902c50b5143c04415018086c030b030b404500c220644d02e042c01508051900081503581c1d9145c81802e0109046003641c0445040c4500f20307030f01c00640300c1c0741c050b00c2c1038950030b954640e103451441c2c982c0358a82d00042030451344140f0a1440c2ca0540505110303103010400071400118a661400d1038040f12002e0071244941d1a880b851001c0c1075507076610f580d42d825040300301c2e2a42d8581c0120008607000740182e403c003c00e03180e10907941000d40b0344c5405010b155000f6540c001d10034008521a0b140d240c0c14500c46221030020700b00300d06001450008400f43e13010a2a203802420561b81d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 258377131 1250 258375881 258375947
    0x40605040c0b1b1014070c0c0b04081b03010c0906050a12020409091b0501020a03031505090106050d180b06010f02011b0309031101060b04170f010c0f17070807 70
    0x21a0079200c1d020480806490440b00c1c0c180044e88031003200c00c0080000c1c44420f00d1041581900070b06280421117041d90320301c2000100134240f00a00101f45c5c41030f44803510382c1002d540c2c90300b92031002d240c035000c01d403241c54451505020b0791103440c20550f0ba0b0b0035500e180a50640350340d0401c403178810500103010001d40500b400740c40500018030f0044c1003c0740024032410031040e1882270a900b0031168100100c2800541d03000201642210b42c03614000034038904005880b4441446034001650141c4d00100024510b41d20402800030b24403c03640c10000c030010700d14296400b850315400101210103840c0014081e40c06801016103d0030240000b1030041103050a854402c0d6004000c034020903030f190f02110905620000c10946c900003c80200070081c100040102d41d80205c1c0315a00307442e01c3c0b60640c100500000e0102003491000c0600900680c0350910000d4a01c412161800c80090b06101807414049074014000d802507000340c03100c100d161503401c0308450b0343e0380d00034500c14025500c44c101c103002ca40e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 258378381 1250 258377131 258377137
    0x61f0b0d0b040c27031713090606020d110105010305060604050a021210081e0307060c0203070507090f0c05120703181a0907060c0c0510030b06120403020d0c050303040605040c0b 78
    0x45039955100c280c0c2aa889241d000900400e000c1684c83e0245080c40000c44205007200709072054528140c840c24140e580703800310303410381d081007038160305000d0001103041c0c00188210312011151100a00c255a0340f9500c0e0890f9024031001d403a582c016808aa02400c0c29800940c0101d2005000b61520485021303100c1c0900d400d840d84190182e50700020002e00f0002c1c4007444c0c41c3c0400048945014101105e9a0b6581c011030002900c001e85d10b82989074254000c10483d402d6a5200d03040c0c90b00d1a650300014402898010300c43e481c0c503030410f144058441d02c83c0041783c410890f41080c80001c0d40316020110010200460442c0b0300c5c40340183c0c00e2000c1035441803030b103041c0c400c0704000f9000ca00d004180c0c1c40c1062940e505c05030501c10150401400101050500002d50b1402c2d22401e003250031400382100a0040548081e8100d00c000806a404080c3c0100c1144664069021640a0445d84078211114400a071001c0d00c1504184045000103400da000710781c005009404c50340701542c4581410541e54 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 258379631 1250 258378381 258378401
    0x1005070204021803010c03021e0c0a0b0117010b04090302211606020306040f0c2102040905090c030c2704080904020c0601030c0e040b01090b0d06020d020408061f0b0d0b04 75
    0x25424440d1800314a424017648a000d05d2074581541080e40b40004a19010390444044400c0e82c9c01088980200b4030403c0301c81d2465400140d580800c2d40c1d81c4005065202400d42c0d407a00361f50801903800001d0503d070181c03214040e40742e40107213a50007040048031640b41c000b0f080500d2509040141c921421003032030310001035600a100059490603d1000c001c1182e244000c911581401c00405071901c5412070049020007400981c448180d40c1c16020700d0000b4403583e00480352940c41d2070140500920002235070f400c0c1034429000c60710005002c1d4100300000304041c00900100350010318840080d44414022508240320302043c2c0d0805141d040060241d800a070103110f0a580160010000c1c44403550301c0100400b40302018501504064440d450350fa601402030907106520b600b004226900c034400c1c070705020340d00030307808548a454001c07100019500500c03030f18a0500c00c5001042096655498008144000403084c0d2a5140707800081076140d0406494020402e90720086076a03546c81d58000e05101d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 258380881 1250 258379631 258379657
    0x3011d1911090f030a020d0210050c0a0f020405090c2202070b0718060c02030a0f02011806081503070803040e040c120c030204140405060f13050102040e01061e080105100507020402 79
    0x30042c070402c1c403180710000c4a0070303842a8040141e010142c4c903400804134210390165080c03402c40741c8000c42134403d80702e030040d0358215126403411b050501c944441c200f003840313108807018425038403482030950350351170040304840d4080110044c44c41c0d440c03410062500c0d17462401e0009800c0180d03a40300c0d010481411100680030416411541036182c2c0e00041007806003e05080210000c42250003180e542e02c405200105101011003140d801d41e1300414017468043c83e4800c18040042d180d0784020310028090f20030300250141200720750210303d004503c1ea01901c00c050000c41c105480d00800150040d4007900c169086403c24501040007154140f0141000b4010752181801c5032640c4144004c50310b0440386110801c2d02d11003400300280c40400c00a40040c50071040a890741c42d1a021101c085440c1c1400800941c030020300050440d6910464904940c082d0f2203c14032400902118441d184600d0708800010320003000602441c80c00710a80ca02d05100c51800e0b0b418200241c0c0481d0880e403000c0344410314 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 258382131 1250 258380881 258380887
    0x1231e091f090c0906020601060503040b1905070309050d0f020a021e0901060203040f0e0424240f08070528090e250b09010c02030a081908070503011d1911 68
    0x1041c4d42100c2c280c001445280300420466240c81c000501d00e000141004244e000100d0118202c00c014000c086c010055a41c402c1103c3c0c10040d8010b0010180ea4104841e14054001740b20782c4203016903505c082c410955006404102480e60030045660f010800ba80020120000c907031a07a0341b40c42501c01d0180010f6001107076140e0030005612081d800552008402c0e00c1c10000300000295966800015615245016046500b414182901030480e809403948203d1860b5150342101c581140e45400302ca0301c054a440000e5241e29503940c5a08182c003c242e00b010744d00c22900010940e40080b032134440d8540000c16200d5032200101e00c1a68224420079450313500a015444481006075010050360310f59803500303443d592600078200724602031140c20b00c0c144980a4506c00543d141031100b541c09a0b40020038558441d4503a02c1001c0e0909054021000210030307500081d0f206000e00304a9058841810050030014048001d103800c000c0e00401c00042d1992050058461040901030198200e0b100740000c2c1d2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 258383381 1250 258382131 258382151
    0x1a070206010e06010504090b010e061602130903020a080a0e1305010602010c0804020f0d060b040e0102041517040b09030d06081c0c0b0106050310080601231e091f09 72
    0x120300801a00b004034500120801e202090b82c0110840d811100b140d0000300c3d6966040c40140c82403034004903032541003100010599000711a0705d003502100751003142d00c80d8440035410706030000c4514030200100075034003c00c21103000c210407001400442d4214682215050703854030200b0206184000102030303680c1ca90005000260f0280600421100c0d903141c5110245010340005001380c200041d9140210700e40041401400540c1e080220030002c090018441446008544d50003035000e8416800d282c5071a01200180c0c600c10862030310901010034100300381e03449584402441ca5005440c152251100b08102035907900d560240078000c0c000c1c0d40103004e010486a1901d8031001540000074100250b0183d00000100d55407902d6066403a00c2c540142c59694917080010030b4115500b080426218843c000200c00c41b805074150310500c0c0a4520041000075102840100c403080b024034094000381301c04c1d40c10242400d203521035026000d05500001a18080e09106901c046600110811500e403002c2c01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 258384631 1250 258383381 258383383
    0x2040810050703151a040918030e060403080717070b0403020a060b031603060209121b010e09130209090124150504061710090e011d0c010c02040f02071a0702 69
    0x40e4482e065007400d008000720100034040260181c060541c0410070488a03e00e518030000503240074154080301085204914134102c3c503a50480d00c0100d0004282e400d00810b542040c0301a01d0417280d01940050410141c0e80c0c0d007039260600c0f01c0754040b4901007809424045414400003500540c0281c002e880e4010306414404151a1030080c514000c0d405011a40380590880301280d00300c0b40c10407801601c41e8400400181208140003255125101c2e0104500c1c01c0320b140b13201a215010300b41c0b83c4440001c00c08052000151003262071201d03401c0402d140e080541001d83c0c84c05d81c030005000001808029680104494500304003981c1c51a03119640c3c140000e4000007810740c01c405036824254141481c0100050200316843d468008608220002c00c400c8541407600c503029040c9110140024032881400500920700c00f9246440340c030004454160400011440f2070001e941079540640d524034507024032014202600505003185d9007007010001007001542e008503128540c0c040e46540341441c2c8402 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 258385881 1250 258384631 258384641
    0x160b0d0b0405130204050604140106080121030e06130e0916050330040b0a050a120b0306060d08070f11150a1b03030e0609060a0e010b0a0902090a03050102040810 71
    0x4280a01c0c500740c00c0c082c101c0100e11140740202c4d41200c1c08680c80d644c400106029040500000a858152000200f070243c1c104c0d0505042c4e80c407003200c8000c69405001d841903c14840d14010300070900000c01c85100d820101d000b000c120050442c80027580e507440407440c1046030215004100d5400124041040c00b150f030020b24024039044004041c0904c502c030b49a03402c1c809400181404c65101d212001c2150280c000b078600405400c8141900e880007038002606c2a4070507044003002070141c54440030b164519108850452a01500512041d600c041c14006440401d19055078100818440718000440202400907580d03c22507510014120540070f114040920000c00303000d02c402805510003440c0d02014560081c0c1855503080b0030101e11b030030158020a158214a0362a0040a0801c1070b540c10001e200b40c00307440c2505040040baa005103d141c00c0b2040340424640c0b00002080800080c0700540213400a00c00c003c29012449540399510350032070307005900c0b4400c00d030800c00c2108480440c0b0701c19 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 258387131 1250 258385881 258385901
    0x16090606090807050a0527091605180a0c0302070203160303090e040809010e060c1009020f0d030206150402091e0f060a05030a110d090f05060106020114010902070203160b0d 76
    0x10443c242c1800c000940c030703e55a014050040080b0884035618054021602810501d01c4070950030320b080001c1700e1a1509050742d100000300b0704c0d5000024450520410440e0041030040e400400354031500900b40140507200151340c101a0280481c1c13016035424000605203d1000424070101403031450b01411042c520303031120b502a812042003001040d452412103c0840091130300e81c142c0400c034000150b0074080c4540e04041d0b031203903001442031031403954815440c20780216102404034140e0810046020030442d40100140c0000d008a001d0030041c2220b104075100040025041c921030f000450071102440748008400b00403c03081469a0a149005d00d54000c0300741e48035843c140304810051303e90300c801740c80c0305451543d440c880b400201c070701c8007074030007140709110107105000e204d0802c5040d10a44080130313601d50080c0d100000b402401403180392540100c104210b00350741c0c41c02205a000b504246016a007600070f030908006403a02c41281100030f004824501ea486140703140e40312046031b82e101c40c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 258388381 1250 258387131 258387133
    0x402100507033f020d0e0a080f0d0207080309030a1101050702030406180e0405071a091804020a080106080a03200a1e0813060f020615151c02091c0f0b0702160906060908 74
    0x28540421420b204682c049c000661038644e0f0303075600d003004a00906c20008007400040b4044144540e03184003000400d200891a91120003050001800724200d5205850600160340304020801109000d0359804031000506100001c00e07990351410800800000c4904a45a400c03241040c00101443e00300014103c4880c034089003000101c1011404040084034040c0300610b1003000141150f944903100405888030000900c901652101a560b5822034000114041287c40714240444000003e03030310760305c81000d002480d13684580d49902d184140301d008d044d14280c10a9400d000496000002849441d0b50720403260003803441d02c14020403604448140f402103400c850140010648c03074040030b5490410131a14880503413503902c400600d600c10041d459801101d00540034180b01090b0780902801078041d522601510a2000848503a58103258000d101001d070b00e252001045405101c1940280c00e401240e02c10000b50854059005450f40005105d640b640018050070790b11912410081030080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 258389631 1250 258388381 258388393
    0xf05060708100b04032316150302091e0111010221090d0206150109050a0806150a06140d0b04090c090c05040b0405060d0204030b010e0402100507033f020d0e 69
    0x2c1240c500754440c5120250041030413171b40b40d8218034060600d0702d0b032400c000001c5803021602118140d15070806845400000d5403d8403e01e10300901070700849207a440020000030761007110312040441d034428001c0c40760411002c000340b10a81e41c801d1008201c1540d20400507100c0c10380c1010680c020940040894020ba0440c14071141c40c10b400280094011401035000d160700f80741e80b00100c40d20392940d400258059401030300014444404107116028103d101e503052400ca00c80c0041c400d04e41094480c0308002070a620b44024269603250103003804108540c400b10300e41403044000380950b0356200044ea002030240100300154107052203081c1c1d03e8003060900030300389441c0140c501094011031044501a900c0068401483c0074107a04441c06035600501800719543c460903010381003102201c080b805103100085081805004106076240310344e065075034918440081016442c401c40d036001c2940a80d000c03040c2001d4510751003500d991882c50900340140c4404010418000f0754001000d4400590444 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 258390881 1250 258389631 258389639
    0xe150405131116020f04090309090606090509150f121f0b0f010c050109050d050c07080105010b07030302090a03020307080c0108060907021207050309150912070b0301170a0f0506070810 81
    0x35406807581600f00c0401c0c0280c0f040700740042810407048a0400d5070251070aa951010103400a49040039540c6200c07042154540340c1a064075954094007070baa0707001c450707640090040a611880d007074190380c016001c0d009681c01400410f650500c00d2007110403503080340c0f1a01c0a15040051000b840d00160f01060002c190b840b0302050f02c007401020726a04025200c1f07418014003100350041d0404940c020202c0d80c0d1030160309002465900306403100282d8cc040c0d1072001130348542c14083c0d01d048e031369200003442c60800d090b0740c150b00a60021002c0d6802106886000016950500c1f50000034100440a080350b00f840e040010109072000709040d210303101030403c0c401d20a40c000f51041040e400301c45400d03500c0d501ca00700366146020380d281d080c0d031124440741c0d107a00401c90200a0f14066205a40813144601c01c1c0e0407458603601c690199042d6014244010804256554001e05102444209448500441ea211103540000101090300c56034040c0042c410026031200f14a503000b80d500603040c0e030003820 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 258392131 1250 258390881 258390911
    0x10905130f1d0a03080c0f09061b0f030d0e01090c030f03020307062301081b040b0a080a0609020f0a1508041707030c0507050609010509060a0e15040513 67
    0x200c0420044456910808860321101c1a4800000802c1109014950350301c1c1c0780c1c540f03070f80b8054408200c00041080011943c064800004d0300c2c2598011007070241404120400e110854100d950b600030150390300d0f05034030715080b4284124204500b01c07a01560b0b85490b8480d10601b50761031103003500c405070300d44540d0001003000c100e4001c042e00d501050034480b030300301400c0c01c03882c44c090700c3c101400355072900d4030040d00c0d41107141040d042103004120300140340eaa0740420075119807100349000b914035010741d41c900b01c1c3d01d0b250b07202c0d2540300c600030f207040d00d02a29500118034110048408a40301540d4101d101e003940b07800e80b600724494508a4241440906109590428280c146480d0090040a002003010401c020555a101d0101225119201c410505005142007040c43c2d00b601d06015071130000c14103060880440d02250010b0b11018a010703000c0e01440309a80c0501114406c00001d0800328459594a02140003c0200c41c00d280b900c1303608100400c102c500c445a6400b400707078940055400d107016 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 258393381 1250 258392131 258392149
    0x100501091205072606010801050603100b090f0403091a040302040b0d053304051005070914060c010f0207140c0a050112020723100b12070e0c0904110414010905 70
    0x2584140e9204078003001c02c00f89111441104000b1042c005d500c00420700c2401580301724800c0c407080b400c44c0d001c44c04c0c2120301d90886032042c00a50304942d440000408480503540d4094209210b4a45406da86903034a030002d800710780072820341e405004001800c00640c0b03042d020b40103070b00c4001c56058000ba289a074aa176900ca09070085c03094961216090504280102e40301c0654040780d502c40300340c0c64509032800320307107441140c880c241142d841c040c0807130a170070311030726001d4140c0c0c2d081001c06140360710010400c8015044042c00304500c0d074031840c2e10400c0001c6130001c1d002c2c2d5446401c404001000030b021f09810b01909a0481e805003c0c0b00c4030400c21603a00c4202032244d1001c9000c0160307502c415042101d0320904011940004010300c1111852031000000d035a810320a40013405c0265820324001c2052034a0040c81002056001100a100c06541c0c1c03440e041e000f5040b030f0b81d4180b40c0300c03c5401140070707101d40f100a420b044102040401005580044c9034003020001d1902161030b500300301c0000c544103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 258394631 1250 258393381 258393389
    0x803090a0507092c0703080f040512120a0c021201090f02010206011401201507050c2e24080706030b04020310060e0303160c2402060406200310050109120507 69
    0x103c521049641310071800c0c020100a1900300e10080c0c1d454401c24002001540140700d000d01440070103102d4806020080364916140189045181c5810131005e41101d405481410681c1c0c4014000038806420700244200307602948143c0e030041100c27102e40006814a0016800180c8082da004006005607a10044900000c21030759a12042420f103041d42c64905900c20380d50b0107811542e90188240c00c4c1d000350160640c2e6109408888803501004400c0c0c21460390b12000542040d84c3c1130101c00100c445400c020b031031042c050110044004000424242030003540e01c80001c81c2c001900070f01c08594140107500c0c0c06d010a5400354510b040203200c9001001c0c280c0300700c10070040d400f00c013007840c2d5406008440050302145550300780307000d040c00e103c00c00000b284214040c00c804001d041190310165014401100e103d90041c10241d90307640c503050068200c1c0d10101c2c3c0500610f850045022603110061401000300c1e0702c000d074540c1d080000150031021190042902040300d8428040000c81c00142c0000351 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 258395881 1250 258394631 258394691
    0x10317070b13060e0f0705030c06091503180709050a0c08091e030c0d031b030507051b030405130c032f090a09060308130605030c0f03130803090a050709 67
    0x4942e10b41858002070000d02c46100d481d00501d1405500008005250000d40b14100c00b0394040c2000c000c200f0405103d00c20149401941d0704c294500030b200d59002950b40850790000030740c1c9405810f0034031410101550080c0d240d0b66034680c144411441148540400704030141800d25450400c1d001c015500c0d40081421a6828044110032290450030710548100c86029012690b5040810a0140c0500001c174840040341c0000410b050300140300340a030600951403600c1c0c561a046c0721104042c100314407410a030800c5e1000300720004068999050043d44111030081c0010340d1451a5002400d4421039a8801d5820781d2104003640e00b0941c0c03090b44550381102104107aa070b442e214002c61a0b19059600c1f0380880b0f0710300440001407080d0b0314020008034251292000360f240d00d4440503181801b0a41e02942c07040c905000e201a03440c0c1c44001150401852641018061801c0e40c42001d903500c110f40500090f04130301400c1081007020001c0744040e08180c10f0501c10746031401c0049881c400308030507030b00704 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 258397131 1250 258395881 258395911
    0x120f01031e050a0c08030c0105091203160507080d0515040e1b01031103040506250c020f040b04060306150b030606070219090f20090d0206031b07050105010317070b 72
    0x1005020441d0440b00b680c40302d285a05180c0d112076007a01ea030808213407501c7d154240340000300500c0e00070418a1007180c42400e124156110050041c88401c01e10307030414203000080242c080840d034400090980712503064004a8180b60584280b0380d460090f69107540101d007810340f003884407100400c802440105031000028510300c0840120080d000b40115110110742c0082808281315020458a22902e00382c4900c0070340c040c0d101342840244142d0401c40c070000303a4113540e8400501d00100701c5000341000401c04581c82400a0000741260b1807584102c0342c50f0342d14240c0341120a0b040451100620a07440441d08514003c40800c0c454803520fa4001d2150840e813400b001d0628a0201400142000c2d0030300f0400521581e0f20b003002042511074400842c0b03103030100c03d041c148010040f01c41c0c1c07000c00307000e14111444e00d0b82031050382c4d040034210400484960f0f1640b020100356401400e061f90048002149039499030a145960300313451a00210b07100400c1202201190741d0001850b004500e440341c40d02 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 258398381 1250 258397131 258397133
    0xf0f0b091e0303070b19051e010509040606090513050705031209041d100608010b0a05030d0e0f04020d0f1505150304060213061d0306190209060408060c120f01031e 72
    0x4110701c2542d800900303003144242440848808030300d86c3e440c6d031401c0140070406900c8403840d032000c0740c0c4004500a0006d101a0041c0b1480c200034504542041c800c581c04034100740c6a2145200340c1d503046412400c426200c04901e41403207c100902001041e082d000f6081824800149642502c9122000d9000e04e4030f58a0210b200000b240301c111a10b514038042c0c4226001c01c00710b00002e0203892180922640c20480c40354000d1802100100890340001c00a00000c100701d0003c1c3c505681c1c0c0703024560f00c40b146000d00b121903250750000303003182c8248050001c0c84001c851403c1c1c085036081c122034804980000803c0c884c64803280e5270500d0703189100741c01e01d40720350760b51414401900c206200d071064228195400146185c1010f240c142d041d031034004101d10310440006240d42c40108071510710306411485140014065540d00030038050300013405151030692618219850040141c50300400301000027800d00c011a801c0c80c0c80340d00000504866412035245468480b403031001e50321422619404c20071000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 258399631 1250 258398381 258398383
    0x30301141305010e070315300203011508010b03070e160c120f0810050105121504140105120f0d030c0203040f060203040807060c020307030b0a090b0f0601030e0106030b041403070c0f0f0b091e03 85
    0x40230f00c5a0080007440745004101c0518034600380c502c28060030350308040b09801e00c2e1402151500c141d0304130005a2829948803a800900c02d420b40701c400b0306110701600c117440411f1100003204550200ca4481961032068660010009100208803641c91040350609104981e800011100e58030b244407034903046500c49a8a140050100c001d855034410f103807414070314410040c074400c10304842040300da01155030411905242c803401c0e0040508915041800c403000c403d8020ba11820207010f2900c103d9041c50780311174014161942941040c409a171012604000d071003800c10070000a4981c80c904003452001550200360307264804e0200501d1903140303200040c000c0103541c0c04890707220703040140d05520b030924032080c2090800c1036407283c0c00241000280c8500311414003420007207950004803070b0955940c0351a60b00e48c0c1c030040d4a0356400d90004000a0001c00c500020765405805200c0c620031034246440405403440b0742030f5009046580080c8084c43c081c4e5602d141140c130080d200c40785111404880c0d4002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 258400881 1250 258399631 258399719
    0x219020f12032220010305070c060e0304051206011401050c030d2a0c12090e0a021602030a050705031c020c040f1b0302030f0a050603030301141305010e070315 70
    0x800d8035103089030101420300400d000041002d00550035203101500020004505a0340f040f20083c02182c00314000703a00041c0ac0394403411205200d8020b0f2820652a4000641c0c905582c01d203205680c2d104600501c00301c102d0240c441045602400c14501c0c107256a2485a00c03802000c1c00040d0700c503650000c6401c10030460180c2d0841c520821000703c21660580c038040d152190316502502c034100780f44560041207000300050016a481202d03140c2e16540c501d0b100c40c02075808540081c2c600c0c00d045c0c10801c0161820000002810710881c05011018200810f26150031700035035014041000d21780c921401035030040340e40b110424095038085204840a42d1072805006498020b51901c0d00003418281910362642c0514040d580c004500c0e2000e881c0d030b600d01d50030780b0016208190b05410400040000e4001202c00c8149114040e160455810503a034801e030448000341d01215007000c1ea01c2c100248503031315104181401c2100c440a644036030900d28080c000084c40b900074100d5182e81c4803ca42620458044 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 258402131 1250 258400881 258400921
    0xd1202070e01031b0605040609090e01180c061b020105030601081b34030e010c0c0b040902070212061017011104060203041701050103080d091b090219020f1203 70
    0x101c5501d6596030b00d0305400c0503020200414400b050840c2c08900c09101e40d003214101c403034550740e00d40346909140700480201303020100360070720390f50b2542c031003840440d9100c403402803500407100e0030703240c616099001d400c0200289841404100c800300c0b010050703820030b05694100318280b17001c20b215941d08805207003040c84e0103000001c14001041d10181d404031300d02030f2800310300011448500015a00c0f600f103403d410380e04004010030740340700e15007116510130b00e00207041038022070fa0904070956030702e84c2200e940d004e03401548215400042400540c2484410711078403030039220040825240806400700740c030320540517001501e0003840c0c4001d50b110007504a04110300f8000542a0b5841d512580a9a02d50051280034400301d01240c0c0411080810f01c2503504030790b00405070614240b5112501c50041c04880700850b6a144140ba8103407002031450401d00103814100d9005030344481c0c0011215668094103030100865010081100e0340900c003049604e007600c071111920f81c07691111507400c00c080700c030941 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 258403381 1250 258402131 258402149
    0x801120f08070f1a0a0c11030d05100f030318050603060310020f091c0b0624090409060528021305040911150d050109020906090f0301020913020d060605090d120207 72
    0x140e1303c080210103002d5907004c1e2100501c00c2018514001c8140c4428a0154801c50550414040390207164142c0d0082c591200003507004040c25a21100030700b604401c641c02c140d00084d00140202c10002c02082c0e05005410200d40441c1146000c0000a0b522403421802003105600070401559204440d400d84034550700041c0048805900c0c0d00d030841085051100580d05424804082034032410550072640c000c1c00107002c0404404602c071003403129030f440601c2c202d0304169180d0742c3c0750115100d407003511b006a620310029902c203c44440c010302645000c00c40b0007103152040001c8100c3c2504017414004940040c0c0b00800c1d015904e08221410000c50700b0006d410030207046401d4000c000036802400d89003019041001140d81300c10f580c1c000c0f8003070017502c00e0300908100703c04101d07451300083c0d541070707000020005440c0041c0c8801082e04a080c9140b0444440e80200310030840780014001c49015042c586040b5003071642203400940d0301a48035001928101d244845507040d18401e02405000d424040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 258404631 1250 258403381 258403403
    0x28050405130b0306060105030c04030b072609010e030c03070f02130216050f011802060c07091a030c0f010903170d020307050d0b1504051002031b0106060801120f08070f 74
    0x480700700003400c026011035219000d01000aa002e601400c10399028002ca002c0c00740c00d103810b43e0345a410800000d800d0005002c10301c0ca2905036030019198280f001810310100e0304881c00c03c0562242500c0c01418038140b280c20520905100d420008261114550004004107410a03a0300100d40e0800b06801d05051003800024070a401000196042456134030174000c81d180031984010785800c840101034291512807030502140054075000000d45001c0500c2010385102ea6529040141194400600300010007071000f22051681b40600022420704021b0320780c04e0102c480f080c0020402000c9000003080201080542c05d06080918203407031480200403000c55a90500c0e86002e00281c0090211513059424208917101038140559400803810080307030003034107050411040145502c507041038807085210500c8100a150040d134050b0781c03c0442c10000045150501c0b4004044c000140c210a190106034400e000024940000e095100b98005601540300d000901c1c00c03001800441c1805803511600d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 258405881 1250 258404631 258404659
    0xa080d0b0a030524010e040812070e0915210709050903041503060302090a18030807020a0b0f0406060f080a030c110d0309090b010c17071106040b0309100228050405 72
    0x2513820550301010b00c120320506a82e56862030b580148112030040100c001440050101c0c0500c1c0d00d90360b0040a0703410040500f18409010804c000402c8800c801d4900e160351240540d030405048540000501214026101c4510030005580d82c01500c00c42221542d05c90005031451004c0c400c0c6c4000c4d1588001c0c040c09407980100003001380840303000c282d20840031500480d9a90f9080d10407000540034184001000c0340741e0f0340b02030b1076241c0020018000e5010f540c28000c0020300e0700700c56a214403001c00211845081c1760911400710f404507000440f6017440a0014041d8150005150741a03682c18607001d2584a1645060703203078201c1c0c1403100380e0001c2d00b0003604c108043d0864900815948410b0080010080a10044503c2100b103000034044c01400460040301c1900d02e07000701025406105640246020340c0c01142c0140e1040c1c1c000481d4041c048140301d5070342e00501c039240504c502c000040d81881d501920210114a242410090b1940000001d01c003032400346050714010040101040e40724505 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 258407131 1250 258405881 258405913
    0xb040203240108011109010e0f12150f0a14010b0904020403060f050403030c0201020a090902030a0b0306010803070309050d0b07081905130606091a13020405030d1106090a080d0b0a0305 81
    0xe0180d80f9955007014410b0600c0c20349002903e1074036205030b503141011900fa00c2813244514400c1c500c01e070480710406135909101c01c2040150286402c800d1480014a0042240b0145403030140648040504150188103109405800b00303041d195080a02596101e00d580010002c1c4142d40c801845241410030383ca401a1480c1e00107445180070303803400d00a5841c070705800c070300301d10404440001289107100c05101154003980655800a400038000035980104000203140c0310090780251307200da00000d0254201a1f010404030000d18042d18810720310702d0345560700e0102d404010f003a001000000e800083c1990100d401307284102c0c220200400c0301c9e0401a040d4440c05040d090203131181400c104000869001c240302d00c80b14540b001403540d003040d40b10310811036854400340640405075002d0002048655080c044018409829200c505400107031450f01400e000000f03042d100c50741c01171515600400c00c16011140c0c02002d06e0800036001d10440006200312800b900090102d10800040e003201c2d10b8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 258408381 1250 258407131 258407203
    0xf03050c010b0d0b011d042103060306020c01020403021f0f0c1e0302070501140f0403081303080f03010509011202011706031603061a030f0a02040203070c0618020a090c020303040b040203 82
    0x392044286d00318481c401c42c4680150035240104500014031000007280c0045069403821111458081a502d1344d94a40d4401d90f000407405180695000600b0000c40c582406407081825050710041e0b1290060300e00a0b0410010103046d00a002e159100b400c02c200075402205081c100c0481ca999580002e030030002d58400b194002d01e40498028410704040d400c00c00144c03146042440c00e800c1ca03041c00d40d55030600075042003042480e04c860050740440020fa200d000b80c50000d0552001c0d6413a90f15002c01c1202201040c0e01c007e0078002020f11032000350b6445124010780b140425036040040c1c865502007854140c00d051907514103111547c001c410000c00d5000329021500b1240744000400c0c92104050303c4203401c406500e01e59011041c51001810940c000d03607072100040c28010600f0300305450745415105010315480d6000041c038407540031840d08a5841026004802c0108012440d441c0c0281d07403844042d07c003600c8400e00000244c219501000710441003148100e0881c0d88044007000031072401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 258409631 1250 258408381 258408389
    0x41d0d021c0e0307050d050307080a05030415050f0615040b0412050c10020604030309061503060c03050a0c23090303071406010b030408040b0a09090213030506130f03050c010b0d0b01 80
    0x307114000c030340c0440c0344942a200c00d0800c004001e0720700e00c0d01e001d003001000c900c0c00c40101c640c0e01050007044041421800a840b141d0141d49600e9a17a00d41031520300c40c050041c1601d25850b42c50941803140d609547e401d06a0b00080a403401c0004134030b9507560030030340d0059601464840c1c0000501140020307198402c415049d01c250304803100d1481201c01c018601e400354450303e0040e88000005400319209422011150b401042c00041040305c00c3c00003034241840340c00503628a03856801500003558184030705a800f030801c81c002c10102054400042000d410003602c4008415148980800c40d0145412200c006000070122581c42e040392a01c03c0b040800c041e148070702e42c06004000074030210810100e901c141e60141c07245140509020b4042c64682050900000704a0580720104140031140b004014034040006510b0321203103036141c21846e00c1d200600962869440c544080002004c0d24419a242a45814141c0e112210000b2003401800b15a0b034050740007008400040034403038100109410b072 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 258410881 1250 258409631 258409663
    0x309020a0b070b06060706020c2b0305060603060607020109080123070c0b2e0305031801021209040e10020301030b061305070228050604050c0a060f0e041d0d02 70
    0x856072140c0624240c0150344000d080c1c042600300190340341c90700c1c000401013070348501401404c0c0114421351030301e00745400c600d001c07076081c0c4441010111410101008130001644c81e06010303c0c41c21101088140c080034280e5401107002243d41006c582c090700c0c5200281642c0402042030912040103c01d812540c1c0900b2005c0410030404200f909109030400c40c0c1c107039002558808141c03a14240d144504407490f2101050245221070082d08859a81e1721400850084000703607181d130710a0580001540003050501d042d0740c001c50024103070719009003c1d40d2117080100e0b0005000c511500c4034a0502990200038400c0ba40b0000001c001c1046002039030380500c5007034525082003815501540100c1d282540c0c5040542c0c0300d002c0c0f5036018012600b55114030480300520400300807a955410346064002e60302101c070f03500082d88901481c1001c21134640200000d1421000d080f001c2540035000e500003106c014055521036404244100407002111403452001c01101d205010990f00291200c16a4001d1440 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 258412131 1250 258410881 258410899
    0x307141821070b090d0b150108100f090203090102040b0708040f0f030b16021f050108060705070210050c0a0c0e07090504060f0905090a0516030c0806010311040b030705030d030902 79
    0x20180e8100004214016124002c00009080c45a9a12150010b00305103070700c05000c501d030000280b94443c0250040440c010340f12200c5074600c00240590703000800c008128100b2401c10405004429103100403150740140c01692600c0f1101c0c11406403140340c00c5a007c02c000065030000700f14443d00204120348002c28101146a1241040d500c00f02c2e262001030142c0c82c000002c40ca000da8081402d111400060044850800301e0010031743e140e8082911100b0100e80e1403004000800d0b0034000150f001209140151411b02551b000584090300b000c030100c02c210000c18201e9001d442045801e82d40e83d0042440014507039920351441d04000c08507512800240d00090001d42d604050040e001540c034a000003504c8141040e0050000785002000c42d812880388051900204900344014068500c6003664084041c0c1103050625a10207070703900c20510307030380701c100100041100c002c8034941e00e840880c1d0100d1803a100340006031901042d41c0015031315009141e001d4540035015801003003171520903038030116 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 258413381 1250 258412131 258412159
    0x70c0e0703200a0509030c0907090f08060105091603110d06090b030616180506031e0f070f0e010c0507080106080d020c0f0f0112111213020109050603071418 69
    0x542c070102d0480e0400450000c0c070107001000e000c1c0001d0082d00d4030150448030301c1004000000c9407120141d50100204a55110070300500c40724121030405040b040000b01482c2d450480814051132004000d040f110b9044240f07954007134401e8202080000c1082d26543e05c41580801c800028201d602c10f4500203858490b07494018200462101c1c81850003841c505000d002840e07041c1c840b804c01c0140c904002d2501c1c6d0380400c980c0e44000186010f1003000100d000c8443c0700c000070350907010014140801c215152400c10800c1c603400303e200c0306140e02c0c9180c402c40c12010b210059400102007030000380940680f004c08954000c05500c510100ca0400d403c440e11111420400e98549800b449a90740000032640c101c4100e040c0b4410680320070006240c400d1201c03100c41016021948181b402034424040080c08a0514151020315030300156644403448c1500030950010b40003c425108a9006400110005000c6c0e0302450b040c44585840ca99800d0399030034440300080c140708100c440c1522840d50198008 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 258414631 1250 258413381 258413411
    0x130509010510090b01020c0105030709090603060911150d0f021209010f110702010c2604030501090c0f2102121b030f0a080301062307030f03060801050903090114070c0e0703 76
    0x1410413042c1c01401840c9650001120f460b40001d0241c01446400540020122458803a103401107000d0100041c07108a24601008500c4000091070303c210b09100b5880311252602c811241d0056a4440018444c440300007503002a025001061003048541420400302c001c06421010b140624080100036203240e000c081e1110f40178900019001958141c4405d00003580f4100780920f100700d0710708040c166600c0509902042e0701a4004650603515000001c0402095508090140801d5042e907036041e82000a0008010743c00210038110340705020500082d520307030f84a0000b4484241c02500d1702d0107054401039001d203590801c010300034400c0c018614611200420703100003855100c5070307007440c50340b810804071500071210303040c00d00302180a4815445458900024a106d038443d031100c43c4008404070340902114065400b00a059050608014042c88080200c0f204e010003400c1c02d0030804e8207001c2e104628003c89000404002081d0070124054110b0a420307881100e80d0380c2d0511002c110031000c2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 258415881 1250 258414631 258414641
    0x8120a060b09010806150712081317090415080d020601050303030f070c03020309061803010c0c0804060507080c010606022508070302010e0315010f090b0609090105090613050901051009 81
    0x2042441401d000c03040c0c196204801003600f2100041102c201c080c83d44c1b41040d0300c0e603c50076080714208000e040904105801400c03c46d40400c046944009588940e00d50807a0030b10f0030b0003500c0000100081e030a1150b600d40d03001d9105054074100074252a0b40b1441c40580e50034014824501611031200001940c0c603001080300d01c1814121003111450303d54a0054500d078689803000c9055001c1030103030b20020b0701c0d840045e141e0742c89004d8680d182c11808005060848204814500030021800c00a02c0420446000c85044810f60f15102d0364401450402031020f01030403c03142001d5081010010321990300103090f040d1403192854032400c0103004c2915082e08840c44c440d268154024127010070266004940043c0080d0b005000e660320302c008031700c0000100c80241c21000310f03280203900c24080c42921b03201c3c005900350103031000c07031816150400080d0400c02c140301c4d0303900c107584440000744551145c0300c0754030b80800034501c00d0100b400c00340344280c00307040101c65500c16405a01c0380007a40424902035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 258417131 1250 258415881 258415889
    0x1113050a0b0724020309060601110d0903201503090c010801030f02010e06091807080703090503040b030406110c0327090417090316090c0509030d1809020708120a06 72
    0x700c5840d241c015902d0241c000c048440400040d0081c02003000400400e00066104031860b102801c4d01d460158009041c00b0749449440c08142c0c0206500d40b0701d103402c0307801c9070196034019004c0c4040d05a108400310120704100c0885402c40070401c02d060a040340e1501440c0a13145080542e14a0103201004452849003440040c2c04000d0303910210f4091350055115001105000c1c169900cbc0111140100d00403c034072030143c17550400d07408100715010354444880c5400259502c1c0610620706141c4031103540740580d00400084c60302c0000400c0400c0100e40c8940314156450f180c460300da000c000300451b22034009035601d07200079003244662040300c0d103450a000d040362401030840320395490300c0e00d949054185141c0c0a0481701c03020488032581c0d070780820141c1c0031000380701203100d201c0d070030f1098440950301f402c1051803c3c44420700c071010032950040340d0038a416415103400504168106405201404281c0c00403009610000b41142406281b10003083d400090290034a45500c503140540c08a0750740d07100b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 258418381 1250 258417131 258417149
    0x180204030c05010c1a10031e030e04110a030509031605030429120a0b0919140907031203090602190e091b13051203070311010603080306010c14011113050a 68
    0x4209050020500c13070317107400c05003808004050311344980d10010540c00481e0b19044180001c0400030030940d11034061140800c0943d03041c4240d0081c81e071070320074a0207009010400e040d1541c00041c070480b002c0043d40c801048070507e02c820a004e50070040e031680e20030300402c20660303070f412586500c0301500d4062508a001c0d81100038a88002c200c1110101403004c1d107001320040d180c0424818590700c1c1d880040c02020011112041c661240b84090221145121001c3c031449603c801c00000c101d0200c1c4040c21a034200c089071040d50070380f080c100c0051100080040c0501c1c404284034010280300140d00f142241180c440c1d0740750380c800104100140c43c003221501d040411381103131005a01c1c59140504050b1031180d060035030300b545510018072840c110308007500d52507101043c1d1100741940008520400d80855000304201401d42d11080c03001d21004100303d0500c07d00314403170f2040005040e8042c01c4800b003040204108001c41c500302d100c5134021030007607800c83c07140c1d030012130185081c2e0f42c0c220440d08006 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 258419631 1250 258418381 258418403
    0x20c03190207150215190c080114040504050d0507021203030a0b0a0602060f1803070501060b030a2f090609100906030507050a080402211207060c110a06090c180204030c05010c 77
    0x2c4180c8000305e001051111500312008072100303e49050700070400382072041c1d280c50800c0c0d030500c6170003d404441010010b11450919041c0008a0310102c2c2c3c80100c40d40c2c528105c2d90b12142c0d400072071701a99005815620a103c008204520b5017041d9000c0301c02200308840f510141c50b0b494400301d94441c1c007500d020904003c0c04011a510042d815070030f0745039540c00d03c1902d0038401651134490071140c6641c05003011120010400c4011041303840750604071006440c9640c80e402824615103004419a10701100c0c0d0840055550709036600c100035610030840017040c10444905540c0010701c90903261080d6400b090610000c40d901c83d0140080e0380d50030b00c2d103513101c001300e81c1d0750f80030060740c1100c28200c102840c4001400c01d9080344140441d400d000c201c01c0b00555600c2c3e040c5001421281c0c1d65a905041081100120743c03d0384010440c1088550040c7c00403d0052650074020524161680600c40c910744d800340d150204059038000e4022640100042c1c1427140d56000195500d400b07158000b007e1020003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 258420881 1250 258419631 258419653
    0x91003170a1b11060c0303090609010e030a120f09200a1203050706020c07060507031e0806010e040b030303071d0f18070e09100905070905010909020a03020c031902071502 75
    0x1c01201e000c840c090f40d940c07004151140c01184495100c0ca034603403501c0c0c00c00010010384240401207950420307030b4a0020007021a408000719100d015010507030040100c20b040c1a0181041500880c0c0c4900404108020480d9289081661110781c001c0300c01400c032012019101c9490070510b908220b41d0030300006030f010111a98116010b074810031046814a60a201c005905001000082c000d01b0060300c803a03540d4981401c000e0300108801108604c1458820807115106512800560b0080400e003400d8249908600028025144100d0019094440403080040c407036441901480c1f0455840c1506103140800001d1144044100742c103e90814400014040710040c0103c81c50307809029864082e202c0716009002410000c4280c070030b21403640c0300b200207000b401ca503441100c7c0c011185007062000d05160900203403010a40340302e450317009680426440744040c007940440301c0010482060703a82e40c00301d40c1299042d000d01510b5130001446040404a4280c091001c940c80403c11500240300d00da0704 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 258422131 1250 258420881 258420917
    0x130b22150507020409060603061e0c050906090d0b0a020a260112150c0504050a1d060103020f090a0e010e130b0402101e2109032c091003170a 62
    0x1c01c0b80101c1c2c001d0303591900c81e0b01103400d80c401e0001840c0b288102240d104c20481c00d511001010071103940e031540c9885908840c01d43c0102c2102c600c0301080d2905ca071100044400581070352012072014100d200d0312001c0100c400c0d030343c4c1d0003050219600d864003010340c2c0c09010190030060344452844001c925400c0148484800c0b680c0f0320507050320a03180c10880000309905641601c0d641c3c01d039440850004201403082c2d01d029400b1002402e52400c1c21581e0700264003509a0b00b1070090041c1c3e05141e40020100701560620040303644007400507001fa580940d5400c1b80e404920401d1283c0c8420b0b0341c01c633011590a010304409015901e030804407050947c0c07955020807007500c000900d10350074025100100012002403445030201d88009460b8100030704400d821120710403043c0c041030404a840d05030346000081d00109507107410496403200840003c241c204091780721504080b5142d01068030341c100100f1140002258060760300c9020803003007900c10b816914541d030207402c80110119000340003082c21140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 258423381 1250 258422131 258422137
    0x501090602070f1a0702100e090f040b150a150503060f0f03030418060f030302100e0619021806040b040812030f0117010603060e0c151306080705130b221505 69
    0x500240304d850004030760300080c07506010514540119a200e00d000046160508419038440000d0a1181040c9800c3c0d850035901c6900a2560041c560200014066a140c8503000d1029007000e91448002103242c42028003143c004440f201e120f2911031040350b00e035080040c100344031184041c00550900b0b051035010031005084070400603c050b80c0c2d1030001103540c10b5510590080d0b002e5005840140c2011a1b00c00580d2400c0f9103040e4030341e01c510117202c40803170792003030185e100c22021800603150082c0b06848106065820f80d056440310000c02d012442200720002041102c2032a42125001e603928181c4140a002c212264030a625500c00100320000304040300c550725050305c00000540540341d0781c44108a42445400202e543e110011807411410241d45050800108844d52030403c0300d9090311140349000c17070140340d04010001011801c0a4002d00a844220032000c2e00c082002c0d84a4100140682200b04440303a101c901d44c4060700004254054603003912002820350260b0322002e8010740e0305038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 258424631 1250 258423381 258423419
    0x1518152d062f1b010e0301060503120d02090d051e0c030a0609080c06150f1e120f100c0e0d0c0302040e1009050a020907050c0c100c0204020d060501090602070f 70
    0x8800403000785201c11003803004541100c241605811940c1403e00010014041540058042d0780740200c28060741e6000540448451100e0304115543c0e01d00303450200182c041c0c9031445030001141e60206081190101e23401080c5e110541c00764103071141600303da90b0ba48100807580d9406822404101c0c000c12841e07000240e81500444236240307000380203a540d85c40e0000844000088031660b0701041c20614110018510401003100d10710214184174800405440310240024868000d41001650000c0305000c0f10006066003010f454061021960300c10180c603401005500107007000030821458500f50680d56034054010081c2e40559085600f03100052480d03500c40003040c03140034502c81801d1400d01032602080d01c18800352512174281d106114149401030b02000a00001340480010f2090000b00c0d204107810854103440904114102601c0b00d0103107082c081e4100340009088001e540307041d00b2103401c50304c0aa03102c004683d61030304126203c4600e40112180403800340c0d0204609001120328101403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 258425881 1250 258424631 258424697
    0x4031107060e0d081209010b040c02070b0d200a020d030c0c08030f0a0617030c060601091a030a1e02131a0a121b081006031518152d06 59
    0x41a900080d02e05e0034a411500112181c0d107805490080d42070502a1240c0303644103000604006040034100502030080340007505010750f070790360202c00310b03544520104c2d00316203c11003685c1e88440300c1d0802901d5410b002040004603080030050b100e41d40c41144082c20b0790741c11040440c00d44e10b0b518983c240ca0703840906407010160304c13100045440304150802010a10455006666814500800d9801c200d0020025414880c1c03002d000c108508410f01c0692290091204d0682d036982d8000301c0a000380004000c060150600081340702c81c07041721b58000c11104d0400034010842c0d50b0b65030a004085034082120034051841400b2081c0968000c400b03c2c000c07803c4102010504120110030400b228204c840c0b281c0020b0003040c10702083c0500f000d4048041d017400d250031710a07a80d06514404c0e40c07441034411080129042d54290860a406500180c1d00c0c0c24041d03031900f4100d07030b5143c4000350b09018100d000d409454441c0c0103040d14000c01c03e000c0444410381c48654080201115510f6215010422241a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 258427131 1250 258425881 258425887
    0x610120201020f060709051302040b0f070813030b01080105090604030203090f12030a0309030809060108030f0903010b090109021305060910031d010e161e0b0306130207060504031107060e0d08 84
    0xf00f039414840d01d480740705299103180d141450901000700a07014603440c0001580304100c140070314440340d800c8a00c150503548015030390780d07040c0c074000f846881640300400503200203200c040104544004203d0490302080000e21060301c60201072611f44400342c9000700540d100700480c00c2c7c0c2d8204000341d68218032005250340c00c0d1300502c54200d41960300031400c000011b981c40368200c0c10142c2002c05507801401c4800144900c7d030403d08450b5682c410028400110000402c0701e03011907a094002004060024040340d00c103580d036000c29006900f1628603031440780329400c408645410a401918001c070340c0180141d4140c0d01e050000c1d4020907802801000308000b5120b45480034000f401000140c145070401040b48010300c440c070300804403140c1c0140004060101c4901007807814420ba8005584600815035034944550300003422605404034864000350001c52000203103c09030344004e00c242d02a441e2800303842a14000140c4419103400f07140c0101e10318956442d800c3c2084542c13405124800c3e8240c1d46 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 258428381 1250 258427131 258427153
    0x101a0a170703140a120807020a0f0c080109060b010306051e04180b070206060103050c070803070818070f0302090114240d0e1b1905010e06040302040207030c0c08061012020102 77
    0x2a40d103150204000f02a807168030400704002c40398048001c5040c680c50700d4902c50410400c001d445c1c2906460107016641749501c40c00034042070f0031b5904020000640204051034aa01c0c11074042d02c40c4020083c08207240110024542c2010000d041d0060041c1d40544c401a1104c402c03c40149a070300000030b4070100080c00c1000190100d00c2040c0034039043c0d0000c0c140c07031038110001402e452005080364403400c014880003001465000a4a4101c40f1505010100707981c3e43c0055080b254410303410f101c80d81720388000050300410540884c002d980c000d44022600d6a02d620024510403120b00358940c200c500c2c2e1071951428400d07000c000350643c00524440d0b00d8000403114030300640782060340100721500300804d1242c1c202e42903501803038400420760301c40c3c00821400200a00c8440e581c810241405041b03a80795209642c2e8000f00c0b03000e150b00420071512141241070040c480c3c42004e01c1107558001b03a910100d41c03c003001174018892944004032080d042c0c01c01c3c03500502c0b140d200104a066206865000c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 258429631 1250 258428381 258428393
    0x908060720250906060c170304050c0310020703020f060105030307031809140f092b02070f0f050306130803040807210503150d0c0e0621101a0a170703 66
    0x800e80070810004200504003480f5000319030080e407091041c0301c806100c000000e400c2c60451000018030030080e0b81c0381d55442c01c3c03ea0500041c030303510b40c0d450301070481c0781461081590301600445004e40d08558208800110840d514542801040c1e41a802030280b2400207104d4090f07241d950f46070100100c2c02a548511010503580c020003404440400441002482d81c443d552a40c0c0c8115080001c040c012080c04140d4402e240861507480400740c0e003505104200e0081250900400440180b06009075a8000103100f10705070340240b0740b00f405603a0102d5134400c0070f198030309451034001080e00d1a589850740d071609035070301161046540c0d58a94102032244070080c207040c21440a1a101c0542e40d00d032056102c5009816028014490504503d40101290b4555403800c20b491a10b10380d01560b07101e440004049081540d900c0803040907120b0b10031072002d4081211801c900c1c00c0b010601401562800c41c04214211940320351304421442000c00c801d41d0031041b017080344100101a00e2250303490707469803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 258430881 1250 258429631 258429673
    0x23060f040903050f030a0207030e09040b06060a050c1c02010510180209040605030f060702210f0a05070b04030f080703020a1b060b030d02012c0d050304050102120106020d0908060720 80
    0x52030050347d004c5066400c0c99000303600380e1030440041395000b40030b02d81566000000381015003101e01131200403448894a60051003122070b901206000c0741c03071002d0661036200c0b1a2010210141c019400c01012460035603800c0d44e1103060300e0080c83e88202d511a40300e4120001d4000401450b8801d031603103030000d1f40740c405000f40c068458856010300300324a04204c001c0c2c07600b150310101020003a040780d0049070b225104010384aa50801214080d80c030900410211703102e014190b00641205c0c0c1032800c0c4410150068900541c42e4030a844d40c2600d030b80e62000980490040c22000404a410070a02d2081c011045101042d128032854000420b40b814001181c600134682030300002507991040c40c07581076020804030105054030300710a855030042d86c0c981c1c20f40300d5030141928400d1041c080040b40812000790140c2d40000004a0395085c25030b903030f4400956918840000d5400b20f00d8880d404501d108012078034910450103a240c102218138804d08a2484003180b08029a950051182641d030b0b880b40c001c03d07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 258432131 1250 258430881 258430891
    0x2180a09020c0f0c030c120709240e0c0304020d0c17030901090f030305040b0714030a0906030e0a050c0d17031015050c0601170319020123060f040903050f03 69
    0x1a216515814120f02c0c0283d41c80d00712050b42c0c040c21105100ea54005100128800103440d403100081c500e1300324502d4203540e60416241c1d5070030a2032180c1e0b103800c84424032074130322180907200d16059541c960b40d4050140540b8414644102000014090b040182041002900c5001e4006080d66103c407202d9000421040a03050341e000011022840e40c0e018280401034800e84025100e0240346503005080ea01c1035216100551602090710410700c12140c400e80c0e40c40300c2c0390042da962131074a00310041c204080c602401002c2840d10340104400400003810980c0c40b0350060082c59840105810407070506032008044401503100e111003503101c0c140c00d018500440000c08241561410800100640a4203011034800c01600307201c08000c085000440504580e102c05002c01d4911000304804d00b10700c11080c03501c03502f01d540300c44e00c0c480c5a0305500c658042d075641542c0b18007007851150850704a901c1070b01d00707551048043d00f8001480c5842c1e44410a49446400c000b80b030403403c0700c6503104030b03001110 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 258433381 1250 258432131 258432149
    0xb070e01080a0c2609010608060123030304090e07180905120313021c03021905030f0d06090903093008090303120411010f030513060b0103020904090f050c010804030c0602180a 77
    0x418005801c809010b28005005010058071103981095007107010021030100001c000280c880480c3c95330b45040c01110043d003141c3e45c00f403040884d008852546d800851003881d40c1200c4850391404031b21000c9c881c900440390300001516250114035000d0000d50405015080d41c210960760000c01641c48001013855a155018038105a4400d0b0501a0800105030f40c4508103004204511000500100440d003109007480c01e140d850703a101030302402c000c15441d0446805149001051340500d40c00803244402c60b5082ca0200649402c99031602100e00c50103000c03070b0200c01d21404005c0004100101400c20480d0181c2107074103058803600c112401c82810b890076907020820240c203454659108081c480c011406040c10301c9142041c2c804030310806038049000e41403d13524404c0b840c00b07078441d03012100004d0001300240303e81080341c2000e4546000e0460222094461700142c2081ca500880f1454407503a0184c81e01e80b1946616200c0030080e40c00380b00c00540801e81c83c0d050403ca650b03006580e0b070141c8110b0b4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 258434631 1250 258433381 258433457
    0x4150e041403030c041e03020603090606040506120304050f0414040305120915041401060e070306140411040e090c030102030a091b08030415020f0a030c0b070e01080a0c 74
    0x20401111401e10204a040305420400c00c02020f130b010081154125890742d44205480400070340360407551545904000d61084001051222102d40060f0090007070004079810002c07a22030001f0030001e00d006845a290980041c0420419490001041c2c021400042e1010070b0039800403440c3d655000c0101c8044010481c041507500c0310001e0420181e91191605009100d0301414a000221710f400c010002041d40e9101542c004031090213400001c010541c0129040c114101100041c0160916000d016000e50300460b6452503845c05014000c503030103802060030b282c60306000404804842c01042c510b650b00c211004842240c500340b0085110703c500040014121100d80740040111180040f0540200c240c0b003414842d00d4004000c0b074007215400700c100d5034643d0000c0003d03402c3c034405503c3d034005401201d050078241504414080005031003110312030069580c008003982d905407901c41e45030002e904100040c02c0c000f03076980b01c4684910301742000c070f00b850384209a5a10035aa811000d81203c4001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 258435881 1250 258434631 258434633
    0x60127080d020a122d02031207020606011103040b04170a0c2309040b0105041503020405180d2307140d0c05190503070f021203031e0708060d0f0204150e04 68
    0x107011480b0301e292075260581d0403e0f6845e007203101c00440803481119800ca01d000c0c080c1c101e402082203e40c440080f4402203100d02c2d010b40069240e2030122026070224102c12003035500103e020007210709803140c92458508050529603244041241003016080342d00c100c409000c085102207c281c80208038900c03500003203200184550300407000446580f40200343c050709003c002684802c805042d03071006d0b42c000410090300a86020084c80962020b90054504030912504620342110301c00e180c9400003c4844203c640308040342d075819422078286502c2c07400c8a4803a020b40c0300380001c1071114000c445030003000d20985011030405415034480c84c08503141e820400d041003028040e011210714448d00240c0c10000540303401e9164803420070001c0001881c9940d100440d40c6003e404009015a04100d83c0c80c1d29111102400d0035030f400482e68030601c03a0b2800100c5031803244000c544601c1e40600305109a621656811140c850385c84002c076440f0380c8403a49140e40c5164485004000c1c500d9200d01310703150401d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 258437131 1250 258435881 258435893
    0x3071a040503160303080708070315080106140306040c0303110a0c0605030414060709030602090d0507060c0302010f05040206040308030405010b060c031b0c010917120f03060f0108060127080d020a 86
    0x1100310f20030031001c0c0b22041040030030340080700c0c50391040260404e548030b42c2d03446804800400184503480c18500f84040007054980c0b0552044003a103400c0c1710040225181c01040545d2140c1c2102c00900000d00c03d58188006480350240c11103a07000c407400c5500c0c20400e82d54100c1c2c2e00c01513821190000b80c010041105100f10550342000c0d000040d4043c141c1d41c11710781e0740284141500d0101030b025940000381d401040c2c449451064925800100343c952440d1146401840d101e5a0f0b0000d800640c02c1c5003012500700c01a00c1203078021503005003060300e40341c51a40d8074021a0401002641c1a5680c2d48a040554641c2c400400c800d8040101460b0b580c0111681c4800c0403000070f050840360741c041c0c510000c01d640c03c008450f042d100c040612180d03c030700d491811442d000d0740f48886107458801207001a10084c000b03010310f00405007110802070704001e100c0115480403080f50010b00180c408140011802580321514044a124518080c00d51361100c6000345403490319071110006030b11004d104002c0c0300d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 258438381 1250 258437131 258437143
    0xa141906050718030b010501030c1211070b09030901080708070203090d0c052107060516170414040e0d08060d020607120e03060903090411071b14010302160f0203071a040503 76
    0x2850f0315a24602821500c843d07041c948140651414980e446424203c0507000e6040340c107844250400c20b1180c5410b14004140503044003404941040c01e001c0411301619000c0300340c400340030040c2d4030400b00381d40d024000c40d40040c010302800c0030f6010400103441a030300c079002400749090065025800c50f916200a00103441408103142d5408881d03440d2806010310041404400c82d082440d0041e1140b0900c1410199100340d0329000308000c1201c80e198540462000c041c004840c03460b00c2021070200e4040c284000d4604544802e8940e4110890303000002d80201c00f003c0d00040c01a05010380c80c0c01d1035002c03d540b640045415034911035016140544e26078010b155212400003580644400d00b040b0140940d00d0041da400144520340301e0044905001c118015502050b41046400b40310014201500101c00d00b01d010308a500c80e90142c010705079501074000c8403000c13002c00341c030845942081c0d15243c507400c244800072607160050460004180c0c1d4200d46c28002038038030807003090b030f1366242500701440c00c9 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 258439631 1250 258438381 258438407
    0x60f0409052413020f06091207180b100c1b08030f0316030c05030103080c10240f06051c0b09040b010f140108070302030a060306060609091505030a1419060507 70
    0x2e02000f00890058484d03500400c030740342c803d40b091790b1503002c03141c0090010001c405144c4c000e403103030750b100148080030110303004d00c80404802c04001460a000501c00905041c014090116096034441400038043e03002c503080d0709595042c81d04849484a5900d4215804015000a000808001d01820081001c101d485203940f03414100148440ca0300082e12900051001410301c0d540400c032125450014484a00301d14443c010400003640509000c2805080943e11100320826020002c542070550400d10416551030382c55060034080c54050021591085040131801c40d40c84130b804964540b41c030016640610722802044003c0d40c14904041b0540a50b58065015601000240e0406136004011190008168680940e0381e9075246c06240c007074002d507131005144914000e800108298045c200005032011082c0c05c4c42924402c92400b2141c00203401b0346541a00b045440a00003030407000304a074040480015551840f1901007820124001550f0a43d0710903140ca0402880950288140c1210 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 258440881 1250 258439631 258439651
    0xb060607030c02090702010204090507080a05180c1203120109141b07020907020f0a030201060f05120c010302070302070e040b041203050702071e051f0206130b060f04090524 76
    0x48031203500c009004105032032020340580e0034040444e854034800c1d0100c030080c01413110140010305042900424403c2e0440c3c1c50105076290801154244051140508280304020700a1a129858504010515071030300c0b60380d41c2c0740c48204001e1030441e092681050003094503140000f51035080a8140c05c010000910841001c030035443c528007041518801e0740c0540307805072440180c650b2000c8040e0302d4500c411200304442d2051600010030540d05400034410f441c0c0131643d030382403e640d0384c060041900d56600443c1c0b068208080e00c100720b5100b940070b891341902030320490b02c1c06a61112900f107000d00554094401c072008404000030700404800c500222402440c042215113050100252643d00074010301185000d001c6040203904014810280648002000010010ba4498410aa40c0c03d12508031000d400f403140019800c80403007540009042e0040c5803488260340310010000106416200c042c3e02940e104000c8020801c00c01c106420030500c0c0314820617101c2800744403040900024030b20404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 258442131 1250 258440881 258440887
    0xf2307210807030504060b09040b061c05121e040602030c160b030f09010b04110d060e100312020102160302030a03050c1c020702060c1501030b0106020a0b150d020a120b0606 76
    0x496440711410768040d4651078000b5079602c8915054000c2c207041020540c0c071820041c18042800348240302140100000c0b21f070b00305030070b01c181040c101c200440d000250440c0c100740303091802c0300d0048000f0006c1580f003885e07201c002c1c1100a800d4a884d0820303044880180e00c0031819410f9440708000c0105541406a06a1501440c00c48000d00901c4010710a08005607171502013050320900350488a861007000700188004903a29000f012150001003004540b5420000c0010b13050603c044541d01804c030008001d50f126081d07840701a4038403d030340c0c441d00456608101c42d0710044004000e01c5007040c0300c0e078091070b50707000602c50003810b80700054466a40e480b02008812031243c050004134070030400d89440540c03102490700001e078050182d40310000070ba0103082d40c00e40d601a072010505050300e1040c00e00a00b00d03620ba000c200da42e800300e00f8009021070344800104044190103182c0c2a20110003c208a01c24900c43c0c3c08240781030810340c40f1059001500b2000401c001c0640ca61580c0070906648642c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 258443381 1250 258442131 258442193
    0x1905130617010603020c0a050607170f09030a0c170a03140a06050310091a0103050601050307080109030509091f0303110f0c130207030c0b09070501030c051206010f2307 74
    0x8000410f114610a050b4001409580102c00f807002c2541c241d0428191901458003510103800e90703d403812080086205600002d2810a0000d01c987c00703040d210008601300220320030290b46051052009440303524804148800c0958608024020100741d40d03004901d004508141e6610300f18042c000c0e960107401d000d01401181c40c0010201a00710340ea110102d504030700c50800c03113807440c0002a000b4124400500220501c000003880a0407104164100c6402e1961040740700c2c02c890303580500070300043c001c110b841c20300d01e4070324840c139048101c0c000350340e2030382ca6051600205181c2036441180410240c41c5a11a1150103100d080720003031025024050580c074050024044070241d4100008981d404181031007810320078a89815102d91107070341400c5038207100340100c0d03035030307144cc4607040c002404e103240c0e0003a041c419000d40d041c041030801c2c54855600c03104015074030000c05001000c10486001c10135120400761891451700c2c054135540403640c43c2020300b425036402590280c3c900c600000380e41410b0f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 258444631 1250 258443381 258443417
    0x3091e100b010318060f110301030c0e280207020a0810050405010c05041206110906040308031b091c03120c03063b1905010b2101080312060619051306 66
    0x24104903405000002c482d82c3d00541c40006000049007c0503110000c0004010024090241e03c155a00d001010f8071581ea402e4100c15052009610400341543c124000490314140d50090a07840c1d00c000c0190000c0c0381c5861226107417020340044845a141c852081c081482020b200d034030b07000e44c242d00c0e0140c40e050a01d4240a0b21030500900249180c2c0d49807880012091104103031035426000074045540d60b9501e0910480c142c200740c640c042d004c102e03d00c24569014042c0112500204040d200340410f00c071955070480c401840c03c1007501800342144d90507074104240d02c5a50340114090703e000034001c3c20100d1840750110045080a02ca5205a180010864044800c020300f83d0001030150a55512819000e0186ea400d5402c035118505010010410b403400341d018191400518140c039116600d8407054113210082171040c1419a002000440d1140794800e01c0c5070344c07108000c1c00302071030b00b0509100081800801c0e140123001402c042080003204400481d860001c0c10710b403408402420058540c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 258445881 1250 258444631 258444671
    0x6241e09100e0f12010603020307060c05060705090f0f190906090608010b010c02120a02100f0813150903051b0604050d0c021809010f060b0a0210021e03091e100b0103 73
    0x2a1084078110b00030060503600350040c0016548c0a8280e40000c0c4e0354910191112030701d85812119401020000340140e817080c0d00f40c50040c2c0006004050001c03c100501c0b0b005074903102560340140da910118822100d40300ca074a8000c3c00e0869000450074a0120060200c41050b08110030690400307595150b10307a40200d2808074070350110b441300c0780c3c00030042c05c561802e0400c1c030b4000d4000c0e5500800004907504130a04440d4842c85850700c03401940e490303e00c7c10b01c0c2111420008e18449885034501c182900300c0e80500207440c440d092452404200700c201001c2c0008201a6140640c404820002004070500c24420b81d03a11500f082a003a09151780000c0c014510039001505c90410341d400144042e81c2504202c070080c400b10000c101843c0c41d00403855150380b040c1040d401502c1402a02d80989820307108039042c05034402c2499803606150700440364a50300c007401003004c9205200412011340c4200360880210400c583c001c11907842c49210100c2a0741c42c54008a062502c4c1081202c010b401030031034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 258447131 1250 258445881 258445909
    0x4200d2f13050c04120f0308061206180f030d061d09070e04020105070807030305091204210c0b03010b0904050a0603031b0311070e0f010e06241e09100e 67
    0x40750315a20721010012038000c5034803000f0145205059017080c8060405000b414034001c2c1e49a203c15903480d800c0c0442c1100c11582202140d11480010f01415400344286d004e9100c10b03420f84441c0c99100279014030755000030304d408625503902d141c10004c07020060340d100d0506103280c0342c0d070146d0720741140040c0e1035070040e2003030000400000d0002811a8429022540125448a0000d4840303d290600400514080755020480e02c280303541c11381000142c2c01550100e40c000d90400408090085c911400c0300030444044900c2d1750f400740d02180f007100100141d406849002c1d0841e4441c10380b1000c10080e10000381c02c0840c0e2618008050011075407000c240050f0216111039005c49032607034641180e81a00031b00c49003a650088003000700e804005036451500900204e160030945036252103100d81c0f0760000380d8000303600c41c07404402e4003060207102c000c0b00341c0303400c1c0307582030f2403d10110700c01100d5000041d003009244d40100080700c09843c944600798a10000140c50481c00008900c4040f076000944440 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 258448381 1250 258447131 258447169
    0x6150207170d120209030304051804110105030c16302d0c2a05090c03010503150c21041a01321003020a120e0604200d2f 53
    0x1600c1c0c00b251b01d0400484e001020054000203c2c910702010900c4210f905540c1100c0c90301e00d01c110004550700c180142d0b40540195501145030038031090040310a481c1e200400c5940c850071310810a0115100c421884448000090300d0501d207404420040514010f1928080c1c0c2801007500640c9454000a20b0032080486041c0180c103401103080c0310004e030740d10080d0254050300e00000c05000c1040b5110500c02c81d103081c1c90103911501c1d0350314030a900b40000d0060300d4060740100248030401809480c4183c028072803526039403405007000c8440000c6400c0014840700301e891002400100125810b00701e90809030b402c2c02c07007a1941032644102290307031000d401440d00c4070303414141a500b11003038410b842c0c1d2107801400c044e140c8501d20f4001c0c000c0e401901560b400318103603c00c8406224038074001c059030710540b02e000d00300075611503445c400444003c0d0810300860f80b8500348d02c0043d4403126070000489000380e410b0403c10442d002e10f40003010500b010040d03c20405000300055403190681c9150078a0070003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 258449631 1250 258448381 258448387
    0xc140c07150c02030106080c040b0409120804080c0f0a0c061e030b2809181101030c050403060e0604140318130b030d0c061505061b0106150207170d1202 67
    0x254100c45031180b00c8800ba606510300b4100203506500010340c100d90f19030545080c40070041d414100011a5040c0c1c2020304982440c054a10004d0302c90700c006640944110926801d0131030410f181031400b6101000700300d01d50f004200184c01d114000001400401251422503001500d41d82c54001002080c01d241d001d0517218014085941e85041c0c00030060300401252001580391607a0b031040c1c0d90400c4c802c00112034a81201c070140c0300e52842d0480c2e8210f4012851b2604010564011802000710541c7d2500700b1500340008400900f560098401642c0d003c00280102c0c10982005944070034a0a59000f0070350042100c02c01038080c0c070010000010f400c58102841c95408103503940908402ca56041c1d140c040c2200340c1c0740c0103402000011038a13025100070040030f41d08102c4404054018003416a200b1014801d28403014510701c00070030209042d400100d03419aa448000306040348000300200940c111070014050a460703c070728050307900001001030403840800f03240a0602a03010082d90f9501d5000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 258450881 1250 258449631 258449669
    0x7050a0f030509031b121204140f150318010204060e0108060a0911030910150b09120106090e0105060d020f0d0501150303030c08070807092106020a030c140c07 70
    0x30b5001d5848085029090391000354100b0342080390030034400d04c003503ca03411600b00500105c40001d00401101c0842d10782503c1c060a100303070400f01d920107502090b8081703c00b10b45152651101601180c03204440300c01c0300d40341d08001c49841c010710311007d61190705030f2040c80f0410056504c00b10065000e5403e00b044440e68803200b0101d42c010a003504180550781c140f4880d08030312041500190721860380d03841a50310311414040303200103580f41d40341c0ca101125900d080911082e543cad08001d02e00240010002c40c2c030420954012429180164000c2d04e24030350341d4151804000c07080c00303003a80c0312034120b0701c513030300341000d0b41c00a4607207000718030b42c0c034010203541d5584000c20000b540420182522003100e807080e1a900c0c9030040141032b84d070050200007081d8a02040c0715500440b08107000d02c03043d841e400710f000e0030103020107442280c0c030b40401c0e0241ca034140f03000301142c0203100802003c65695800f140610207400c000d060325a400348031042000e0204003520440a011850340d044c6c0f03200d1a485480703402c00e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 258452131 1250 258450881 258450887
    0x913080c0607020d1205070909050a0b0d0308190b0a14012703120819110d1401050a06110c010807031e0501060206090102041206052707030b0c07050a0f03 68
    0x210840c10185104441c1880240b6030009044400d41c255581c0340130039010000f2200040d07401c240c0c0c010000c1010030724144485c004940000e503001d0145000024019105070028010b202d040806401084591b03082c89440350f401c0c0b9032500700003070002003840607a0403180460402d407801e100d0a024103075040070b04500d983c030039014500c80281c40803041200e01800813100303500030880e05c003c5408900b18204281998007440d0000c0c0701d050700310b0240c0860304d03020500300d025201d1000103410280303042081c0141d90031b0381e200305000800b901d061210f041d8104021700582c50071a4014801348020440c05596050000580100c44002882d01d180140c40d140c03002d4016051100c601c8500c2c2c07640746501060003c460380420304030750f0329900700c503000d45408101724203e1042c1e01039900006180803946001c15000d4100c03035000b803980c60000b02e0081d03910703118800145280c3c940c07181a80180004100b803042d41c07071840c2d4221208a0409281007420380e10701e035446404160040880c0d052910103030134980 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 258453237 1106 258452131 258452137
    0x61005031c0513060804020a05010e060f1c020708070201030b0406120f1109040c09140105060405040e0a050609010c02150610110a21030515091308 65
    0x4260714090020085042000c14440204030706103458281d401401d004103440e58410481d41454410411115800e80c42941000090f000c2c080070790f13035008200c030199074048140c140e50305401155410041c403944207401c170b914400b107041e0b024400e0300d5005180c2c1038802d0b0380c10060f0342610700c02c000844286024070703140405041951000204521030403440d480c0600c3c1041c1c1120b14030700010b0403208040341d080b290a4101c0c8020041c244090207104410a251240c42c0c00079070404020a20602462150901c12070316400d4190750342805100500115402c28140c824516004120034040e007a501c0b0070500500c24201c600301d01c608202c00542c09000024120122152540801c0300c100180c03840640b01d500410030000c0002c1c00708802da070711483c0300d507600c186140403816021702154401441e80c40350360102d0b4002e4409a0300c421070141c0c000c21645541f48103200f24100b62541340 = true := by decide +kernel

theorem cover : BRFrame.Cov 258273381 258453237 := by
  have h0 := BRFrame.cov_init 258273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 258273381 ≤ n) (h2 : n < 258453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
