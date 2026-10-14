-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1519
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:22:37.95899+00:00
-- url     : https://prove2.me/submissions/024d3748-97ba-4487-aed7-fbd534e5cf5e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 273021582 ≤ n < 273201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 273022832 1250 273021582 273021599
    0x706270b01030206030c09040f1514091302031507030f0b152208010c0e0f01260c190804020102151e041e0803010e010b04030b0a02090d21020115 64
    0x64190b9804540d1251259518102c0070410b05ca12015150068142050707000006500d0300043e202c0c4d80c0b4540440c480c903480e401c001c4180c1a01000c0d10764040550300c04200c105040060034240f0500107400e48503d040d000040210491003915848002551000a00c1d03815149218000310050105e8071a5180d00ca030720001186400745800820b00c4050403070410140030403d85108009251a000901034010108d902034110800c400f255801414210703003405845d0310580360840807421412842e1406a8440400c074600c3c80c005182c0840c0300010051951021040480441c8141135507403803c00c186804c0c07000900b4000d41e5410113a864072a80c003440102000d01002c2c42c00c0c0c410300017604074290b540d42000020341c048000e11134501c02d401400402442610802141601d04901c500c021b02d03640c4440359507180c42144805003480341d140021505102042d00285040680100355034400742841e26500c440600004e03030180e544442c400500a525028010700c030751002c0d4071120b003071094a4809103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 273024082 1250 273022832 273022853
    0xa0f0e07080106171503160e0906010b19020304051804061b05030a0e0c09070905010f050f0d0b130f02030a0f02070c031e05060106020c0f091b0f040b070627 69
    0x20b40b00c88132034100186004180c8020101400002400c8881a2082e80300d11410542c903400b5100d882c001c1e10313000428070000040d03884e04940344112001d15082c0314910351045002c007144040f0450008000000d40d59076104551003c0702101c8140c3c0d500d0b0300b0f040c900f0380110340700781940e58404420211301000c60703070300002030b40d6108035448404549021011580390800000e6907100740e00400000612480c1948400100c041e40d100ba2250300480c400600180c070350b8045e40740c2c041c41d021820414080d0250460704510320082c00a8081d14030b58800c1810003080d1020144426009036010080001c0c10016006481d13a0300801c4500b18035200868445201c10702e181d000251010950304403809441030061181100305402c44107944070741d61130340402500e42122801c92841603040d4200d04400d8900720610340d0140004485440010661408141c019082020b292034405002e010001d405111100141385e000e200d0100003800f00c0e0810391195041c030081c0c032500d51a070040100c10340002c0c00c0584 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 273025332 1250 273024082 273024107
    0x10c0809063306160c06080c070618020402070f03030b0f030a0602030408120106020d0f0809151b0c10060e07021e010b040c08040b09010c020d1d0a0f0e07080106 71
    0xb4120300c50181401c94031446080c60104940100001840010388940c40307242c42e000034442d80184540300c5e0344a0701242c0418007524000a5200d08004000010b03074140d0101030340d185410440140d40c0d04c940c0014080360022001a01caa00f28180030380708050303040c4180d400da1002120782c0b18104070403001103562505089001803403070381e000020400b402104016503103040003d820104056864540003500da00058050303a0101d003582039a1184070340113800c182d2246a030f04000b440e9034200082c0c0c07400f031355402811540b41100088c0450a0040f038500051450401e1740004101001c1b070b540303104c0b0458005a2003922401c4280050052044d404038404030400140300300e5030032603903e01000c180186405807019900502e44807504042c83d40080402c0e10807401100b154200355030b035001640c00e88209141d00740058000041020000307004055901c90a6081c00462900d0624080820080742450308019140401c00e07008205040c00b00500c5588002d00f403a04022f1945084000740005810342c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 273026582 1250 273025332 273025381
    0x2070b03060a0b04031a2404090201142a030c0d050a0e03030a030e0115050307180f05010f032a06050705010902180601170f0a020309030c0f010c080906 67
    0x401c20036a1014a000c014000b8120b10940c0c556503850003131700060741d02c14a401c0440c004400100320305582c100903c01d1a0544041d4a03007204401c3c100001026880c50890500c1a05400c041c07c007640b81c005019042c940141c01d0843c01d80300700d01d1a8000c45040880307400f50340100115850b0060100c0c0040c0302c400f0b50705190b911000d0348101a90100c1c0701c10400341c0c061001080b81401180c1c5074200c0048554600002c014800340744034944042060340c001c083e017640c4410000c2000088000810500e034140c154002401000ba220074420f6038820390000300e0b2200c06803414024010745415108465200f068400300305460900d4180b004201480388000b840b9011900c1300a2003029006110714942c0209030b4503041079000d50306d406910050f25050f00080c442244500803000b900c4869026032980c1450a4450361000e0f0480e010303520040c046919030006001258010004220401c0c1030b58ac9140041003541d01454020140440101044900e60000c4140142e03c0c001c28204081e508000303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 273027832 1250 273026582 273026587
    0xc030307060c11101b08060306010b0a050708070f02011e0e06090d021206070e0a03080f0703090f080307021302030112021302040b04090e0c010509031f1b080f1602070b 74
    0x100801c3c0c42451180c1c01003100e6000c1c01d5035140380c0e000560310903807401e03111211045000070101011250315104030350070754155100000500907844070002a00c40b03600c9920701249054071659403404d46400c0b040c02220101c140c09001d6085680003008202e801200c1110b44c010749824480c0200410362410a4a002d124001140c210071b844112002040e42c1d00545040e40c0141d42c01103107680e800c41252805c000132003030984071040b45071011076070088a0b002192941007542c41d000c3c0c116079902c001021001e01c0307401d000c002981200b4426907002412458040c2d41c4808060042c0703d280039164010700700c1a84100018400f85000401641d413464065500d1000d11020040c7c1200a01c9250015411f80c8004280000c000d080c9400c80300c042000d840a42c0c230001c0c41d4034010b4549015805805030f0680000007101c20102074443c40d8090101001c3e000700700035100001444d00c2100c02440c00d40003c404604119420700310000d1260403007040d48503550300705a143d1009403101028013807024a180d00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 273029082 1250 273027832 273027851
    0xf0a02060a0e1302031509070f02030d180b0106200102040509041101140309101401030816060f0603030c03020c03061b0a090b130503070b03060a030b06041404030905120c03030706 79
    0x4008035554800d1003c282156282440c00c415494141d2240b05d0030701c1582d84e8800103d0451007030800d880d00000d250000c50600500d0407090380a8007051625545034610000a031002c101440c98250092190f80c68610a18010301c1c1c460180e010a03006441080e801040700300300503250070780075a03441608022150748004020b80100e8281084409034100000048240900307100b011480003001803e940f0104002c0400f40c0b80e00c00c543c2c80910000c0d200010610804448003c020304801c40c40380304910002d80102000642804c0301d007a42c1040d00014500c050707160401d50100b01012011804400600040c07a0412109994204a44880c000600003282c0c007507206005813090405040c0ba000301c251076a0352021601c10800b51031060303503c40d1007000c1000071144091802c4070300640020b00b4008185086483d511240c91002e0840b907001365803601c0c452503401d02c01d090180640c2c0719641d4080894900010003529122921207481c5580080304c2004599074000220741c0c140f41c5c0701c4000b047e158603 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 273030332 1250 273029082 273029089
    0xb030c0d021209010605030d0212030718092d1503030e06160503030f010b04140d1104050703050f1e060d02040b120106150507050c091009021b0f0a02060a0e 69
    0x380302c0c07411054504210600c014000c0640244054441c160126100c0004407030f000c0343da0740d086422200c1c10200420200707034114452540c54070045060750b1100840c0d83c0d90301a850072201414441c607002215101e6050300604030304d10800f00145540414000300c00f00516110780510144802030a00c10003070040500c0352034807030544581c2c5600f900740498880d01c1d4280251241d00499065182a51000c00410218542c806071410744d5802c142c4040c510b400841030007523444858500352600766a9031082c904036980c0d4042c00748180d040c8d6801003400d01f003a51000140020242c144012650041e02120300300711800750301d03644503100702c514281800c803d0020070014100101115000702031f20000f00b0b04503c0540042c4101c42c00c11502007607070324040001700c070240101c0c0001407d40e0408402d02c000c61038070000d80b41e00000381012a40781d8541d5080020100c0c1d2002100f480d69000507000085243c4042c400300740006d030b03020090100002c03181e0018175a84100e4a0b00d90600c035580b050490a42c6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 273031582 1250 273030332 273030337
    0x6010f050a3905010f060602070b0a17070509040605010807020a03031d03030f092401050904051606020706090510080408030907030210050301080d020a0209010b0c0a0210030507180b030c0d02 84
    0x24003002c64100c60061104040488000c0a0700507510b075824540c0051901c259031144408598803540980182d80c10320740100030540c04103120328204196000790810440508010b907005038107a440b455620840030b410304c41910010b074082810300180404018030a5000b04010b01e00c41d0340b501c1e00188681d20380402282c0500e0760707280c0108910001c03040090700440100c45500a0440d00102c0e441c0044002413841072613400c032246036034039842c807004020740c0c101400d0043d0807d101c1e9064800380c1e0b040d50804407103286558070110050b4000349013080010b4004446001070300e000d07115070665008654000c1e0000201410080005100000003180c07141c00340442c3c0c1c00741d580200031604002c0d1550300104260030a00480106005075041060102d000003070542541e580074012240aa182122640700c0340c1100011028501489803442c0060f918402075504c03800203501d0010350742c10102c01c000d106190360051040c0d5101c00310024840d071860032041c2c2c3c0c1d1040341c110400d9036801d00c250030f040290 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 273032832 1250 273031582 273031637
    0x19080c0307050601060801080a050a0809060705121306090e180a1a0406060b0c060402101407051506120a15090b1302010e15040905060a1e06030506010f050a 69
    0x103010215188080050205005040b07a4981c0c3e0b41d64050390702c981c1660344900f184007000340540d0226040b10006034103040a0115050000c1c002d80c01c105445d2591420000c226400010807400011422080c44a81e2580406401d030303890489002e0b414040300312420200501000c00d070070301002c21030f04403038003c0201040d0243d002064100d5840d0801c405030f070791001a201204c480d0708291002c507013056000142e84542c15404014601d40d00c41d0740a016521810314109020480d8401c21140240c01c0d400003030a1140c4528018400c58050604e00d404160300a40030503c07901002d00c6041155000148035400c264100e0402c0ca0f80203000180359000701410f54004000d1204c41c004c000d02000742e40c07601c00740203000f030f224440b15483c400d0400110902d01001482e05140a101c107124032031959001c554080310150540c0780e40e50700c03410380d01070302c0721028440c1d07000c20700070482170150a92600525402c49000e00304602e14200b100740250031303801450640e03010003030800503a007000c8241c00d0000101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 273034082 1250 273032832 273032857
    0x30a02300a0e011407030507060b03030d11090f0415090c03150321091a030901111234050c0c0604150206060a1d130204060e22051908 59
    0x48500c441e402601c101c0d4040031090110700d10200b030b43c8035040d02d07204031341c0900d13815581e1034a008410b980309002403000c4e0030002d80600c03062106119020700e6104080560703030000000c07a06c4014880411100d42c2d186003086000300d04060143d000390b000c0703001444c02e40728901c0c0301156604a4441c01c80080541c0a010858400999400824801040c844014440c0322000e01e011940a014058450064603c14000041942c0e000340160b01d010340c004c2c58000d400b4600114403100780e20b00d141c80c290028005030b910701102105210070000c030034600011180412400904070000c40e0755400104520203a02c078107012000504808980c8280034410030a40024101c40e140e40d02e4a42d40324002c03112621007805489201e001c96660f00e0005490002c4a484a60031904070a603002e00200c52407001d004203404000c0c07403001c100183d6860203640050084008042c180346040442694419145014800b00d1014040c0c1a00411004160f000707a94480c403a00701c41c9084c01e490300160b94882c20380071510 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 273035332 1250 273034082 273034087
    0xa080a1803080906310f0c030b0f09012d0e120d06061b120212041503050a15171f050a060803040b0702210a030306080f030a0230 57
    0x101500505580c0c083c079003000c00c03074000740c1c0c0d07030090b000d01e620361701d440d0103a450604030b40d002056584400403020540b01d401240085012035540021000c69a00b0868140e02e13a0b00400141d029000441c41d030003040a4000d2101e05100104411111a00fa42c450f03013610384003042c00340c1e1542540042d8801d0100e441100c0030401d20041c0d6902c20782000e003000e0100750406500044040c4259170200e850307100003402201a1400f07548041c0b131030039090260000d5005e100881695001000f015000030b02182d09017200843e41200014100d0703000909001c4c0881c58842c038521040844203608003a50014151041c0d40300581c1101c0d86130029485c0c5088403001c1b00282444480226007046014081c00700e02808074549540300c094403400350b4043e5010085060040b10058540b2505e48900306001e803a584481a143c54621410900c40c606c040d400b094a4200400410300204901504a031150001d1414141e695500075124a208810380200d000c1c5044511400740d0807044420804180d402d0131355 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 273036582 1250 273035332 273035381
    0x60406180902030f0a2321040504050606040b0909040510020c011b0e0105190903151b11030403110609030d0206010f050910050d060608030a03021803010b0102030a080a 74
    0x102405010000320f019008444101c0044100054400340482d48002d0100c0080c2c2103000510294942040b420614031800724514990b000340c0c070301802c0c3d9140301c00c9015030301c906140520041c1cbd5030241c40c0c01d0264404001c10040e501d001c4055900c401d070100c91041880c2c56a0a0140c41c02c040301800301d01961000840e07202d1004158840940b125420072040343c050790001c4282c40d0005258015408039900300200c1da40a5030a022011145a46042042d0b0131a00ca0703da200c1100d004e0f043c0301e0051952004181c0200301c5d0340b0f044490b8031115103421240c41441c03450094070707401103100040150700a10b05950241c0d603420107880150002400700e0b040001031a4000b5942e0340c00b84540c1c08907142220000c1071505048180030b10074103032180c01503d118600018800da1440040044c2c6030702da0307100c0020440141c1800280304125031660050b80345c2d00300c60680300c00d009201014900c6a031510b036a0b145aa40c021040d40c2c01490603003001c02c5140c0c1c134100032030081c00310055503141680c00b00c402007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 273037832 1250 273036582 273036629
    0x90305060a0f0b060909060d06091502220b09130221060a08010902010c0311150702010e0d1106011401110601061e0c050a1506030b0a1b0212070b060406 67
    0x4090082c40d80b814010905208203104940c42031004040e0440b101000190980c1008020141528800c01c1d0008030082d56480c1c1071411501c7c4d40100d26019000502820403000c1e00c246001048111244111143d18020048090f0710440d44100d0003444528408403041c2d0702541038a4000040c4405804844c40f540000341c22000e0844409100354058100424401014811103120541c103868888080e0003585090b600405d034605000c01c41d04c00c0360782c0c850541072441c00c02070055215070004030701002c8510025042a801c900244104080481c980d010071900140d102d04648000c1c1c40d0184200303200380101d0703031215204100c031070900c00c01000044882c0d001d821010b80c0484081055040f0b02c0f188011204e1800740c07039010701039a00c81c41c0c0e00008030303040180c80308180c5880c00300000d88641c1d0359904a0b0000342103e20b040b0300b55540c070104641c1c680a49100e040c4e840a84013030084c1014401450500c4c0c01000c401610700ea03241000510b0603120ba81c0940042c040e0079414403c1d094162044 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 273039082 1250 273037832 273037841
    0x3021312030305010618090b0a05030d1211070209040809030307050a03050a0e01030207050307120225051816120213080604060b04020f040b1c0903082d04020d0201090305060a 77
    0x310000b902e040f00014055204890200000361354070b049000c414902005030003d40020300a40c0d81c0020071400014a40da410410b41440b881180c41e503808548903a045441103550541c50140d01007410842c0d000140e4a00201d10b0788141e000c510035448603c4d101c0804d1030360103468001030003441504415818160020064003400619680d0000f00c10240801101a4003171104001c189900130b02402c0e00003036540c40e503074000260510464a04150000c0c02170000101e201902400d074904940602240c1060034188021050080c3d00090b9820608841c814288541d05054104500c0410314025522941c044410110054040007450350300c40c00f21948400c0c05036002c036103161500041007070750700349402510b0900d003c0b0200c0c142400e10346103168186038483d400301d00c0c00780d082a45e40480900580f0413210024002e44e542d4410f49098a25001120071455003000b200694a00018001451548142d409941038071181480e84d5580300689080400fa0402004d5008240c20007a100410350300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 273040332 1250 273039082 273039119
    0x50310030212030c0c06040317070303140109020d0b040b1807050412030f030b010309030f0f0c020607050d1b050d0c03031d1b060f030604150b0304060c0909051003060c030213 77
    0x2601d6511842004110300c40c4658232004000180c80402c982005c03072840c1c054800b0500a003004a81217841c07a00310307440560301b6001a01555130104542e0300b0300100f48074424000310305580800044840030002141c0000c41d0f680311a1035040040050341451040e4142d400412056074000c000c03104914000e400440884808000a46442c00c0610198401d000e0250b086415407149200d0b0203010300100d4005000031100c10500c240324590000503211607008003002d038004d8001d4803407484a07060041041e01020603819003004100a00001f042e00441c150182c1900c2d41404c81d001041403405a011b0300070b0300c40150800c1c000d011030015454020981c05031512a040d0700d85032800050f400c0203090f000c0d0a0403121450b00c140005600c50410381e0102556030402d1040e940d0703659482c441400a64005c07070b82102c0640d1201c5543c4030554001c0070b240042e0010f994140326528040c11072040041e070300d1201620f09070312129243c502078000c0d41140c40f50703c0f01401080407682c9552091684d1041e986 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 273041582 1250 273040332 273040357
    0xd090c09360206040909050c1c120e2106150901140609041e0b03060a090b06090606190903110a030b070f05130303020a2010030c030b131b0f020a0305031003021203 72
    0x41e00c1024126102c03809c50761280d0040c1941502201070008817203e007028030129030032840ca16445100c5030a60b00500801e000d41703900400c89494082900c502800042c20481d00801134000180954210049903100c40e14081c0e4903640c40704050f400280207000e60415600ac3d00303503506803419911030306400c8504402019000c98400ba243c000342003088402c50000906171441c00c402090952a100d070090707800c00c600404660608022400000c0e605e00421180d1000c00c0b1910340c1001000320f603000851040b00110759002d2001c4ca5515810403415006002c032080100980003440b005000714142c40b0103040941e01540d0440d00c03860040d5841c00104002c0c2c800d41502c0c1c03041011095100d980442840c0c002c1d1101c0104041414250050704441200c48107160f16182a92080d0701c612051030034000d260a400706200380c882501c051562050a500c40801c121020784000d02a0002950004644d0516010b95250380e8089000710345181a00003d50040b41880c1d0f182c0d06803c0080030306040c1c8d0a00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 273042832 1250 273041582 273041599
    0x3050a11040b1809120c07030b10050a06051201090b09040b04020d0b01090606080603010c0905151207031e09020a06050904021c05061002071410050d090c09360206040909050c 77
    0x1800308901400f03801c01d110b1f41c81800240002490027001a4100e1502c4042030b084544a1001958501c5207030041d400080c1c012403010a0880740905141c01070511400812030055044040344c45540d0042c0054400e0841401050454998240a00441c3e07081050001a941c4a540181c050300b49485201c00003181c5001103401d03440e0610903186c2d02c10700d9854a074402490f00081c000f0f8001c09c007031034440036401402444c0f0240b141082007032041e802607600240401041950f00d10350328511669440ca60b1a00d0300d0070006866050541003550018107085407182e03290800100603116020990741001385220781041c20300804d4020500460701215082a03002c1c0460049968524911034003c0e038441d80328040c0c405d8103094654140100070b42c038047d4500410100e044007524003522086030300380d907821000c112050f128803540346024600c201628801200700b1380504049484452400840d190003003840031555801c040728010300b2552014030200040c2d082040e01ca025464000e030052064 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 273044082 1250 273042832 273042853
    0x803270322120201081b030103050604170703021b040605040908030114030a0b0c0307030b04050711010e010b0105030a0e0a1502070209070e010804030e03070803040e0108070b030103050a11040b1809 87
    0x415001000b540c80c4009621038918107500115443e600140144000c489101040d003d043d14203002180a0350144000b844542082d180c150340b8107408040d122100d640600041e40000d901050b6031031035035101c04100611110071400180106031382d41c07085900620b003030140b800704040000035504a60444104004003502003082c075171110050ba800502914010000800c41500007005d581c00072168600081c1d80c1c60800c000c182103480c191004000f041241c030060148160074000c0300c8005846600a00841070018006080c0d8007015100d881201d46a00c8400c50112040003091500364105e201c0300d105d540402030701002136200840590144401d240060940b90155a94204000069440700d055680da80c90898101300c00c641055494003c1c0a000100b00c0c1080001e0700161020880044295140050351032806100d9844a42d10300410310041011a030040f480b446e6481e0032203480f40f2015003900004004040005c0c0d0280d00144c019000f0000c1d40003002c1d59482121000201da0340c081a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 273045332 1250 273044082 273044137
    0x70801020703050a0513170102091201020406020a030c210503070e010302030705070f0f021e09011a04030206031803030c0406080906011412010f050a023408032703 72
    0x4000c000b0740850400c12056000c184514000d080704041c03040e00b140003544890400c00758071102806419070742e4001c180a07009142c000100412266020001c52405d841c0950107902c07961090130180a22042151100c240080d580c00002d40300c119450b01c1c1c03403018100601401c15001a54010300284006c1c0c54202154003034030843e0b01800c603076200e007828500550744603103060ba840c240444c0c030305007803100300300050329000c42503110021400e4102500044620a00c603c0c1241640040f40502e1403900b501104910742c0c0c02c0310241d80e010741c1c6155a0f0390700c1d03103400c000c0e426a00000b40d1591000008001b2201502c40150081c0c9503d03646e586201d481d14030a05540305400e00600d0b524043c1c41c510706540d4035041c41d02c2240c01d401103002044100301c600002c03007220300489823030074400e400050a204902c4006000d94017040c2da401d40c40b020045051043c41d0210007900300030030007840080419004460303a8203040d680210701c0c0c51280f044c5110080345480e038122a03a08181000d801218603a21070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 273046582 1250 273045332 273045337
    0x106120204033c0605011802090a1a040e0702070501120c0909020d180605061503040b1f121202010c090515070303022104021518011103090d03080907080102 69
    0x2508985540341042951031040c5000f80142e00580d8030551401200000c00c41220180d0180e074050f80c400030b030a41c5001003490035100626030b0881000d104006840721940e4031804403058410080b00491590145000700d0741a04c00d9402208100003418104011340398009507100c02da60003070b652102103101c1d0300c0c581415108030b031301024041184100c050007081c503240e026007a8691419808582c1c1078642008200e074000000c0300380c480c9a03c0340308000507810b0945031902c1100030705500d245146400d490b0300409610103042042000d6400c0ba5034000d0400242c01003001c0d150000408142840c80d25281da40340311950440c501550a10b00d00300411800341c10040c0844801500e440000f82e0a401c060741103611040c0c0c204e040c9a07003884410000021b00f0400b80542c417030308072100124201401000540d000840d002043ca210030040b42d902c1c4031601c560b48050580c00e00b0601c1d0321102c4044c403070b030950085006181d000214000c00ca414184d11440301401030407840151007000b903d40c90084c1c02e0380f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 273047832 1250 273046582 273046589
    0x40b060f01050406081603020418061a03070903201f17010f0e0a0e160801150303050421080f040311030d0c1509050313050f0901030203120a0c15050106120204 70
    0x1c50100001b106003584034a0362000d0001ca19005103082c0e02c0da08801c0a01103078220b142c1e02583d0750394043c00f80441c61003179040058107107845030b07046280901d0004e01113509408028501041d161628004405030706007800320100040c0109081c0e040d982c0d880d43c0107901d41c24448001041c2d200944049204450b210b03040e610748040000c08035003011f005609a80c8082c160740c403035541d01d50003030051400500840750b01e505908500c6601383d00c0c003103010b401d64a61803d2071011801c00f1004000298101d0125000c81c1d46000410507828207000e00c50320106446c87d4050400c1c0780c0002c0d2509400c40d944000c1c01564820314812030010f040b0030606641d001222141ca02103030700070100340082686200c0440d8841c1030380d8070104003002280d81352030560f00300314052889403207030b01001e01c5586030600700c04248080a0701c45104640c9140c000903596458001e0034100c4804c00a02604007505c40d40e0109403154010341c804180403030081c9804000c113024070802d000030340d4695955002c0c4603140200d5045 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 273049082 1250 273047832 273047837
    0x70507270b0d020901090b0d0507060c0c091505100315030326040b040201200f03030f06100e01031509050907050901060f0f140c1005100602010603050a0821040b060f01050406 77
    0x2240c6c01c0c001c10344000d00d8150f814030782c48003c1f0122a000100304200c0c001c0a480b6507942d0f400d8000542c60002480c003126005181200e00780f064585240810b00341d400100c61040f14101c28071000704500344d000340200c080500c1c2d02e9033305210100078503400040c5100d600d520311100c100701ca41d160302c440500c1402690020000132401020401640c0f16280d070805254000c0030303003204445007080913480c1003404a040e0500303401c00b004205e060408654107533032100c826545c888928014aa000702040100c0e0b8030300d41450b0341c1ea00c4840c00c500c0b00d210303071101070031a42004105030300f0042c0e60305544016910030240305074459800400c0782e9215040c003c042860700d0311100c0c0c6c941c01991003078a60450784080030404420612070b00810780410440325102d944075440c000b420382480c1e00f841c08a12656006441560304180041000800000b100c050302c9405c18001da443c0d0403410468070b015000b10b034200c1c810080d00d4007480244540c460b18103001d82805c58014a2801d050300c0150790a000e1131080e08007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 273050332 1250 273049082 273049099
    0x1b080f03150f060a0909020906040e07030e1e100504060b15040f0603092d0609060c020d09051e0301022809050108040b060f0d0203010c0e0306010f1a070507270b0d02 73
    0x2640d0342c6e5401404082c040100024101615041e80c12105401260a040020744440ba2403190f000180400031a12903142c3c8110307107030001c9803d0290380e190440c0c40030302090b0b138650025050014581c4058107041009003069806922a4800070b030f5500503002e130b50315112100c40e000074558080d2180214540d0b0107440a000e001c000b03500740d0720340e0b60811384c0012103403501002040005c5030f91140008840c4650b0000034074242005009160101c94003840090058984003031200d0740d144a59550040e0691758500c65120070035003c41c2c06802a040e5104528076264011a0200c18600310141d0580071a9a1402000c0e900c100444480358152000381100f00307481d000c1251802c140e00d421802c1e0a000e04001ca8900749507010130700b10340298422800152005112800d41e15050045500410102c4802c105080c1010f90341d40302800740d16058001c0c00000a0241c04014090140100038103507442c0f0300400750b4885482e007078115034039003c1c0110145080810315007440c0044000760156000381c5800c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 273051582 1250 273050332 273050339
    0xc070828030302040905010b0424080a020a0212030705120709030f02120a1406160212030a0c090b0a0915030911040f020f070f02040b101b080f03150f060a09 69
    0x54005150801502015000c00c1301044408030303406254000c14074101c80aa0343d42c6050f00c041010a4500e100c00b401441a09041400b80c0c0d218031821341100e4182e030016590b01c1100740c1030b072410160300c50580d0030a1020040000d181d8101000e0011440c405001c040555500c03101107440303019601000b0f002c070144052803005800c01009006181d10500121a22040143c4540800c00440c1160f50301c40e5200c0d070b0400c412501c4004050b510943c4a00080601c11200291100386000c01410500300955411900480a00c1171211000805421206a036100c00707460008101c0311007402000085590694000741c043e21910075010540d40161040c00405815001c10000d02007655122515a03000d200b8040c1d041c018200400e0201d20039465016a03500340e1041c0401c2e40d00e04100544118540002c1c85030075600640d22600803801402440113030140f6152104841c022030320b0504010b1404400c10141f4101d580300348416041c01c40326421f0399100c00080002030f05c101214400051000d04082 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 273052832 1250 273051582 273051643
    0x312020d0209031b01030c02071202061e03090a030915050a03050603031c23040c03030e0d0b040f0218010b040e09030403020907020a110301060303050a050904090b0108030c0708 78
    0x4058030401000054a41078410000a00d480301c03a01d1324107a04003030300e00d107080d140d030701071180340258541070004d844000c3c034000c48107003c6c44049030040d000344000280c03100325044a6034003950849030701100b140c032400c2030406a6503800c5c2c2d58100301d0110f00c0f2440d0108910001ca41e400c0041c8925564030340c13030140380c22000c03800f400001e40780d140c1522092200460100720340c0003d24800082c1c3c40300007903540707103011a0034000300c90801c00d00c0c944d01c43c03000f8071010914500980c0180c9070142801d108002140e0007181030308120003009000c103001f031030900040201480003130202c14002c50b00c0140010803055a503101d20028841e19203040c2082004120008a4031244d035032141e015001d50b420684ea940125003411811145500141c03c00e807504400c03c0003004503810700d07442c16002040001d05503a8041c225205401840302817010104000740f803a0341da41c1140302640d51042900c0004c5d43e50710390507030350790700281107005850190040200705150001203034803030308010010003116030394004490b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 273054082 1250 273052832 273052837
    0x60806090606070303060b040803070b2203050a020c040f060602010b150405010309031b061b1701060804020d02030f0106080c0102010e150c04240f0507110103050a140a091103060103031202 83
    0x413014107440750f10005600c0640030242000340b50b443e0142d03540d4815803910b00000c08004019420076601341c0d10420071882c4485e0641c1049a040c24166918503098005a207000a1846d2140d84182440700d80c01c41015a03410071000c03282140c0091180d500130380e04000600d904a041d80007103030b409101c100042d61098110b1044d1500a0030000700c0c04003171708690145a249014103507012901c2e40180480340d01c59042d80d004002c1c8074035101314484404403d00f08820010720803081003040900105003550b68548002da103450f4010202e43d070000c038401200d4007131b003203901c5848810b010b41c10000300c5a50040c01280303101c1c03686a0180c8080d0320300f2442c4034800d0402405030b1164031418400800c07541101010a000c8414240304810b1281000f44010600b9821541a20030400144440e100098120003280c000c01e10034280810f043d910160408018030031b484140c0c000301049000e01a54680c2544400352035402140c802c241442510141583c4040078440200065900004801e41d01141d601 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 273055332 1250 273054082 273054097
    0x703081c020310060306141318080c0d08012702030613091a01090207021f05070503070b09120a0215070e0418020a0503160e061314071e09050103020c01240e01060806090606 76
    0x1030340080100581341d00308035811000c0001da00f940100cc1d54042c20340c2040859004002c1003040034803188151039400c044684101c50f00c514183c01101042241c0e40e00e02d6040c403461100403040247d010181000d40143d55446076495a600c1464000300b805800390084600c040e40142c18104e111102040c543c10b00b10f40c0080003010408240f040d0380005034284010b201e95030007500e9044542c00d00c12901402c03c21156401022407004020f18101030383c000c01e0348000160560b41a0010b5a50040162265030080e030419900601d89a040300c10114060701007802c0e21300a4030020180c070b407944280750b690322110303404c9002508225020400300303c0c1481402d0340903a0180102e90300b511260284000c1c0c4285030f4201075190780000400001551011600c560300d00c07180d07030f9031514911041c0c001e042c0c200540912410140c0004900750f26a4094100148100c083d0b400f40300403810541001030041224082d008610310803000015202c0e214071141402450020300380c160742d032500c10802005900604 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 273056582 1250 273055332 273055361
    0x260606090d02040b04150806060f011e0e150a0915020606150c030a0806130603030f110304030804060201090317070f081801050108030307200703081c0203100603061413 74
    0x204e04052070b2942d00800e000101d00d004000142810044014148034000388294000e00c20416034905983e40301e1420000c0b12150101b0380f03a00c00c031031001112540b40d046066038100c0c003038a401c0b42510703400d0002050f0380a82955800c104a40b15000140000400400180140e03c1036000c10306e07600e0194030740d40c040b0074040b407154030308070149069074155040810340c8404100e500d400c004281c14411038002c1d40f4503040504011407401c0d9035000d82a070401e98010400c0000451441400000400443e0059034011a074140c94035a510030085c083c195140d421000a16044a200307140d01c1108002c9005903401e84500000d051001011103018800030044940303484c00504c0b0080700c5400780700d124041d008100103950f81e441c0c200c070003402e0030350343e00c0103465040906041052113b00100f03044042e43d9101d08081d0340c4903140c5040c42d1810948220786185184000240001d0001d40c0740716034110b0b4540d440034400d04e030b40c81d0703150130030102d2001400340c00618203002d45144030350302d80c07140d1284100762 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 273057832 1250 273056582 273056591
    0x20709060305030307030c0302070210030c05070b010e060f01090e1308070602030a150812030f10080f0c01080106081314120d0603060501050301060602120307140703260606090d0204 80
    0x1400040103035449075000b900c075a08004203000b1907681c98000c00c191714103d41415483c02d506a800728688214004075001056940c2008440e018410412078103a80e070410156041d5584030a480752100400f6207590740328684480d503140306540541800400c951070300c54400c200b55160390b05120300360b101400840f030200741044120009031580c80914011a020440080c1e40210710030654800c0781550001500d0b5800148008001c844034411298000011820301200d919150202c0380c1d400c4682d00b20710400e0081e000e01c021800c000055130502d81c0e409030b8845542e07980c0c5090031358120307200b6a5000c400f203540b407000b0710200e508040d1006c048146c0e442200c41102000281e40c01642051040340d208540342d6801b007091060a000349405840b0803002000302d0b904d8403002039500d0300d160115400500740440000d641d50702031702c0040c0451000f00c0d8040d5841840345001010051000840300f1640c403204031442303040f0000d0394010321070300e0094025032030410b16000b080360549006004a80c00b640b034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 273059082 1250 273057832 273057839
    0x40c0f05030f04080d06150e03070b1e1306111501050a030305031008031605011b050a080c0c01050a0c02060901060501050318010605030a061e021206060306060730020304030812070207 81
    0x5445030318014510070760307e00c2c5442c194280041c0034101d24000140701e0350100c0c4060213000080b00440700400c4603001c009240188541c5108050300404420740006460358900040b256086100d51046500342419107200041e032400d00c0c60105d030217000301c0e50401c2400405000190042005540024109260710010795840c240c2c0b0389141d00000304040390004110800702040006d00a40070b41000c4031401e41c400500742d0f00000c00b1801000d8459003040201d0300400c850714102001c841007241c0c03d000a005526001081d0000b500c40e40d0740000042c0305900000d0182c0d0018401c03a800d603241692054610b442d8101010750488205510034859541d44100148980d801c1082180c9107105070804652403250315610204200304101000040e8010080c0000c0780904403540c40d0700150840e40281c0340e44680002c00c8250203185401000708a140c011b41c205e940039001c038200484203070440740c001440716080880e1640984d10004045900a12420f509000c0d10780d103180c0c0c44000d610407688480d0380c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 273060332 1250 273059082 273059107
    0x1a031b0702091812030f150a0801060308030f060d0c0b030a0b12070914011505250b01081605010507020409030c020d030c0c05060c1005040302100f0506040c0f05030f0408 75
    0xa8441881c288607001408031040014440e088060030004c0907103085140c005001104004020540c1d4030150603c404e04205607544400c00000c0c2c40310a0080020549924024409500136250000d0b56401c5400040c1c4a00d0146454155a9480b4844450f12403820200445681002c0c0c03803426000c0c0c80311310780780245c0c40380d0303c900320740310740c00c1c401403444501d0103101004451812425600c88003541c07005020090004110165000840ca81a942c5c0c071401102000510480d14828080320082c040c0342c4107000c54450300c0d9050350300d804150381c0401c500e90000f228001741d0b4422a401306909212107805071500341d00c05190b46000f42443d807200d040d10350004c2d090038138012044000c6401200c0f04410302c0b013120000000b0b04800d40c1c011f8908218900a0781e43c64100803200c06120741ca40f80082c0405200748544068448000b00a10001c11201d80103409403c0031640240208d1170f1699120159202e20400045036031262a039034034680b82c1003600840824004c009464449042282101414 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 273061582 1250 273060332 273060349
    0x504080a0308190506090c0304030507140c0315011202210102030103050a030f030507120c111002070b060901030341090907090503030319060302040213050a1a031b0702 74
    0x5101e6036801c601490008544200012a49144500ea9240c6010825140c8401c00883d4001c0c034244440d580700d42e140e20b000c6840348500500140b00350001d0503200340030440000c404455540407400d4030b001948182c9055101c100920030740340740b013602007121805824007840850a20f02c000f00301102105881250038260791080e4012902075018003442428190f22030194000043d540c68144140d04015000500b000300001e45454241c1da0380e09a21300480c06110000c410403001004d0360804501c3e1040c000094008420540d090103000000415238070b0726009182c16298552680780032840001e820040c10007a0040050340b4841c1920384000c0041517020b6102ca1105503001c40340d4400e448000d0000000010f010901408010704050000b6900803095941c00614444070b00903c090983d01c550180881d988080c0d0040d200080e1440040304c200c010a09440c6e054525011a907a98088541c802c50804503608810b0000c0c40032070401062040d07190803082741803004034202070040d0000303a01034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 273062832 1250 273061582 273061603
    0xc110a05060711060105030703060e03090405010e180f1213090501090504020a050d021e04060b040b0d05060904170915030a0605130b181b03150405151f050408 70
    0x2607000d6020000c1c0c007640a4001c034180d41c0700201400030b6501d42004a542c503051400000c081c103850b0940e81c01102410070558504203001001404256500d800f658103a010a40b44880301446401840810200024440e0842046400140078420505c000d40645411203c100c280d0000c0c1041c0c000b800c07a203640105400f90280d803000144a003032a204000007070426910803800307184800310b08009070703891010020100c0c144240c0c203402c1050450006005000d80d40008102c00e01c081404500d00503c03401408090003480020041900c9180030011400001c450003040160408000e071107050012028200814000d840c035801002c102e01c1050440d0803c071007500890b0b50340c6000f01314515041403404008881210100458070207040400c41055482d0070940351f2207602c1c004151003403081c00da88000340c00b807036000c95200e050040c44070380224031030f0b00801d110340c0c00c00c0701148006000340da190560385030090284044040d084409410038200480c9001441020321000492044c28084400b20 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 273064082 1250 273062832 273062843
    0x609010b0a060f0c140c120a060b0301111b1501060513050108010b040512030d021210050f010804030f02010f0e0a1505100b03180a11010206090607020606040c110a 72
    0xc0309015400c1c00345246441e072042003000307082460303801c2041c1c21942d2804d01c140c01c880c0c015a1040104041c40c6031075110740c41c082e00302040e41d0304003115600220720501c240340b240e0380512124107140c3c10103003a01c404004900d902907041100315030b0303821404001c0303400d04021000d9901000f404c407080c54080c01c0990000c070201d02c000406411004c0240702c120302801003424100e08039410300440f0103040c00b403405458090070b005030740090940b40c20001c0e160009042c200a40d40c03003034040103000d0208000d65280e020110400c1c00841c040c0343c00404004100c2c07060351780d031003d5980e90f28102c500d01c01030001034080d55a41c070b22907915001a0f00810b55141000001440030003164588071190850003d8440d46090bc0c190a203c5900001c40d4590119103020500649070340310400030f42081c110542d800241886910010ba00f0004480c1d407100c0e01040980980e80207030b4481c001292038500c1101c2840050301b0110000310540b5065102d009901020319000d0300301103040721402d10740900701070241c03031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 273065332 1250 273064082 273064091
    0x80702010b0a2d080c0f06070b07050423100305041b0312121107020405220f0b061f1b08040b0c0105061f080411130f0c090f0b0306010c05060901 64
    0x402540119488081508400d8551070285000e41c080c3c1c9400d205d03402544181c1d0402c2a19505a031101d0544955540101c0f03400020b090103036020f4940d50051240051240b121100361424086400389600301c14000741030000348000d404070860007800010821120300300541c038050200e18400080c4400b039403080a20b200c0241043e40d0113480310b901c02801d00e00c420304100200d90010845010b035501250306a03000310303054039040d84a0f5000d009804030907541c603038100310940500100b2040040420b004e10440213894403804240000f040ca8030f04007455140d8000c140c080727a9846150b90340300b07550490020200d85440c2e540c03040d81590041d400140061804128801d8400c03080c0725454128104803058410000c20200340e055120150144106010400d80010305100103810700d002c03000401044114010355144a041c0103107018915148500e180840d80c1c0407042c0a101003105650301050030b03403d040c0c600b000324103176540014044c1d81000011940003000030003c001d03240c081c41d088400441d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 273066582 1250 273065332 273065369
    0x4180902090a06030c0e07020304080f07050126041511070f060c0507050a0308060103060b0708130906140d020d1a0114010c0305030601030e0a0c06020309130504030807080702010b0a 80
    0xc180700c060550342980d45800c60800014200817010380840c3d90b6140081c2441c2d894280503800c5004903480b80240b4003400031800302214000c2030740c800340c03202602c4002460120100301c0d4046007217951680c0b01c7c403d000011402203502c04074074120300e141c01031003c00c800711905c1c2900880e4010700c4040324011a4032a50804000f0180500c0c04586010b1421034101203090310742c00d54031400a003010307050202d041c0118245e80d00c241c00100280080c15181c540e82c1c251840c006025501041008074034000710400803071250300364041d140c00c440e20517840c04801001032081001903199031804a03031003202048000005060006064580c1d408071129545640c5440080f80c0c0c8a40701841160400803404840c90020f60003809170b03a000303e420310700022280b8040304001e1500050940182060504140010f001a40040145108201034800780a800c90b20510281a184142c0d401004182010002054244a1900c1c16800141380c4000701e80c0c0070700702000c180030000d160800f000c150007000110 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 273067832 1250 273066582 273066589
    0x1805102a021f020703021906030b09070207060e0d1407050a09050601080a0b030a0f08040f090204050f042304080304030806030303040201021203072606040b180402041104180902 78
    0xc00c48803000c11003018800c0515400a401840c0500010030840807240d403419040340708224042c084c0d0b83c00307850252002d4941c182c01041118520034000001e04000c20140581130907100381e409450341c0d80003001d10a05240080d00d41c0c1061011442d000452000c81c0c4d00410000254102d40f01089005000468100b4082c4412490f041d0010010141800c082c0503481c0d0344511481d0f80152014400506540c4a000007400d014103114090441c00d1601d00a00c24044480000c000b110244441e0442e440d503584108401e900580c400c0715403101003600e50120908003600981c09038020300500c002d1803224440d80008a41090750117480003138000c070401c000c0540022286802c154101c0045045242c244c0c0000d40e640091480840c0c8108044007181c0524010007207595051501c0b01c070030344500d680807030401c040d8904a030007602c594184007034020941007085a0883c44002020039200c02c1e59240c080c0000341c1a070102122500c401004001080210119507510070324500901160029060042 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 273069082 1250 273067832 273067877
    0x8040201210609021b03120415110a0e040c0e0303071511040303020303011505030118091b06261905060a0b04030b040312020c0c0d050703060501120507060201060b0901180510 77
    0x311754582c020003411105080031040d1541c041d601c03044010301c044a10304a03002800d03002040c40d11103900400c0020790382d500010ba46501c00800e607000c00550401410480d0648500c01c03aa0742c040d04100400004142800303184c035031403100e81402007113011080343c6840e4658840d500650060300003100511030f0038417403d400003074402285006e50865041800141c002003200303444181003980ca80b40341d0104284240e1100d484030b1280500c000a40e0b64510207800c1c02100f607000520b071010701c0300c0b0094401d406241d4500a202c03030000c421100114241e1440282009000594030a12041c0c00040c0050008010800b55101c3c9103500c0c03c500709891f028011031000c800d1981c030300340140056251401c0001e003482d10300400301c1d07a0b403090054500300755040003216000902820300f0f090000c035960044640640300244a1004c8038403556a565040b0b00300c5007140600510480d0800c4400c1e015032003101c00681c482c542c4070401612552b6100000d101d0006d14049401086410605c440c405080066 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 273070332 1250 273069082 273069127
    0x90405061b04060e060a030b04020c0d140c1510030609060f0e012d020f030103111002030c060c09011806030c0f020a0f08070519050a0c12030804020121060902 70
    0x15050415040400103481220061300d5030b809640b001c02c1070002039100e5040b0703400400003d0411517842c2c200710942d58541c04424484d80100703d140300b00d120125681800c0740c403c2c00c0c000d00900120140c001000041e520701034807080742c1c3c415459010011680a01c01c00d4800e510400b4001003100500344490251040c03950f4004160740341848100b00440d202d48011480001552444840c51810000388002d026846401450460120000c000c111403006800303a040400c0b04c016a000307050140c200c0c0e40b44614000c406d0150440f402160507099120080c01001e0380c141480303400307242d01402e00d080c4041c0e95401000002c3d210040d550510760070904d4216511954070180c000e0166549aa04040341c0b19000141803400009030b41040c08800e0013054811074491450800c2245903040182d55009006402c5e02e0196540c94001104c05003005000d13b415496190074060350340b143c00542e0004484406100c0100026070b001c508501c241c40ba50002c0c01c2c80c4440144c03030702d41c01506202c40341490274 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 273071582 1250 273070332 273070381
    0x12070801031110120b030a1b052d0f2e0f0f02150402030708070e0106090509040321020c0a08030a1b14070503040e0708090606010923030c09040506 65
    0x38029108158880384100c0354480441d1301007010143c690200b49803100c181801382147c030030244901222401c1c00804011104211a642c01400184807018680a04101441e0900070104002503450522001d50b024040c40240b0906036031104100044021011030b070300c03a901424401e0342520254201503031800c50060f03031410b40240f5142d004042d5444100a890a0345034210344000b0b41196003c00000c0083c05090054521690340d60440b400202d0080c0900400b0840030400801c90782845402984604e070160b4412154181602c0c9044514401c4454111416006c0141d202e6841c803c010480c003c07440340701100c3e41c07403400240020494000c2c103013001c801c00711044644807941c2d224a810500c00f1000f80701c1c680d21002d07460007500e18030641c1d0095003803144060030029540d40068010340301c8c9105905407116659503000444901c0d10038040c1e0f2007030300c40c00c44500c40d00e03070781079141d40d290410080c0c100c03045140280c002600d510000c9504842c103500010420030302c2d94148071000000090320 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 273072832 1250 273071582 273071599
    0x1a010b090f12030f0f1312020a121a28090f0b100e0a1b1e050705010902030708030c0706090303050a08190615030b06030103020901031106120708010311 67
    0x40000e0641d220440906101d44104030044044500500440c0d0026001d101e031103a0b5160540721915940e00300d4030400d000320301d506100080d02c03102e05008000703995004000d40003050624054000310040482c007920654080d4000ca80418140c1d000a4020050b501e0407402c0e0780d542c0031001410100c281d003856001400e028850002030800001c1c08882603001080c942c480d40c03030b59811803040c04982c3c44a08050120301c14880d007202e9903070204c4440b034644108004044125801901c064540740e0881c1c0c0c10250528410107014494030150003818031a60020030380001c240c00007031038141e298128036915000090481c246513010007003a0020882c0c1e081c0043c0840c074644024149004a110048c2803015440c00185803500500302c0d8205000340c0841001074a40b52180e003140d04000b00c0a03403001c61300e00100f08040c0d01c1d01c03400392070481e0b0b070091400380b46a0071607403030003000f41242c0d01c03c5402c240c007846498540803442600781e2050602c1d0381c50705100d40c51402c3c8031107013001d80a21140100880c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 273074082 1250 273072832 273072847
    0xe03010b12100b121903080c072003070302030102040b220815060d0f0308060405070311041806030221070501050702011d030708030a090333090503090405041a010b 72
    0x126440004421480e00020f011001e680400c103807940d008080d1015028101003018020b019842c40d00c2c0b0507000380d8542e0101e5861803610b02551090043c0500342c030418a246410714101404483d0320f60602605032081a540c1e5404a800da1300942c0210450b1003010074903203081c0600c54100341003100039150140381d5a2a103843d194651450300c0d0000340720a8818002480c40d11141068112158400d504100d010098140101610019500c0c0f92080e410940480c01b824481c2c003d01c03881e400d414500614240c5800101000000c441100c601c0f19a06d0b80701c0080035955a02c2107921300d03291301501583c0075514050882c00c0146607000b09060280030b20140003d42d034810301e0048040074038039004a642a5400c0002d20388103481d030004415100000352450244d034072846280899102d0000920b80c8002c61900c2c3d05952010a80b43c03403081295007116291409a4020310b00140c065800e580c42d00e4141800300f000c1e40c03021141500c41c02480c0c5c908290043e004266203004181c802c100320b090501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 273075332 1250 273074082 273074119
    0x90f0406050a0b0a09270c030522050f030313110316030602130306020408101b0f0c062c0f0607090909080c06070e011706010207062007060e03010b 65
    0x2d405540c00d08000400c3c210750150180340b41303401a0040411100b00f0394a0200c00703202c404000c00e1280344807410b1408020045010340100d80c020103545480c0300010310744c2540110f40b488203a00c1a5128402c48840b220612000d01c000d50182d030a40c0345603400b03030b001230a00020400441c48103038041e0b8054007000c846107620f07903141c105981d80080050390360289292104040c130450b0304017034001440040c0002d900d02000865140e8030341001c10078002c1c11240300b407004000f15544510400b150741e00005400241c810424840200d21a140c00a548001174a620086a00440c50401c9084140c940d0f030520000c00c2101e1035003201e10034001c08070f80c80c01e002e006041c0403280c4101283c0c141c840e000441041000400e6645840b101406c2721345a14040710004c007802ca000d08114007242e04030114107800709403000118440c0c2030603002003040c039240020880c1c0401c1844000034070722909440300185044184003040041800303030794080000f01444101403c548500d6002131181000a03840c650b5000c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 273076582 1250 273075332 273075349
    0x20f070b0d020306120d050306130b0d02090405030d050f0f240609030703170304121b081b06070306060210090c0909170c0a0506280e031b03090f040605 67
    0x200e0260f01d81c1c50710340108441c14003601400e68140520a80008030560003405180303e884111003034154210010451005c0700c801c103440b19044a080d1400b10050705001c000035401034070540451b4130b008007129441044601c280c4007144c441218109100d2486c42c2c0c1d806498000400e0346424881a00d0b00078064681c1c4100c00d480340c0107032404034a0500540d800d200701001140c04c181c201c94400172400d0b5000081e0b0085070110744040204045455a921a8041e0381c0d02c522010070006e83c2025075218503234190801030440070706140c10446031410500502144c1d008003041c0c1c50100b183d60038114040d041504021056400c07500e000440700c00700c0c1400c41c0c5a01101c104682c00210105c060800040614800d80b625138000c0001031440303c0c14800280c0742c0c006c14002c400b65040c2d61500001c012480d0110803421070101c41d14141c00e80d1030300c0309501c407940b103070412070407280341c0b0881d02c03182034083c214408003040c1c5410104120306182080481807020750800c4504008142c01c1c000040d0782c41 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 273077832 1250 273076582 273076597
    0x603051204120320100e01060609080d032a0201020304020a0918140115170d05040612021b12040806150105250206070609150b090703021e04060807020f070b 69
    0x40703410508040401382a10b03802c810700b04940b0075182d500b400c0c2820300c0d010303007000ca621085a40c641507000403c43e01c0755031504140e440020241451024510b030490160800d88035a090a036403c154540b04a11020203d03c0c10000341d40000d1b84914150042140802c02a40500166418620f40c0c60050602c4032b5490703101035100103001c44103481c1211890040030320401c86440100d00140c0410504c003020101c06000f60b50303108440070406100c01c200e68a004610581c03000c507030a5400d00303c103012a83c000c3d0441c7c0400c01490030411510368005440d01007401e580c1d4010f0300000030103008001050111541c41014141c034061850162000244a40700b6a603a210740450341c145030100001c04c00d030900c0c007956002000e850b2038542e503040c40c1c001042002e1044484002e84030a8008102d11401000f0026000a1441078a0f81d2840c2090b4081e6000355444520100c06800241841001401400240100c1d5540444a1034121006490a0700c44161036a555001c400200b05004511044803000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 273079082 1250 273077832 273077837
    0x6040e0d030903031401030803010e0a0606021b120d030e0c031f0510030f080d051f0608060123070b1e150f060d140612060406051806040606030512041203 68
    0x48100c182421002060364001740a03c401000300000148422080610305840780010210155190303100c80300c1c122500c501c142c0780560410f9001042482c25101110030104005c0d164048101301d4511641c1015007034259040482e68071605440c008604204280d00b40000783c0040c855401034080c0c1150350020707500d01618280d2540c0c0000c8030640c03d40d1a9600440e400070803043c0300c280c3c0d45000c110039045409a15a00d0717151200044d004001464418212000240c0c405082410200d0032249007070014407242c10700200000044000304008070021300300e04c038040d100e40c5a40d107c1c40d117035155081c0503181c0404a1101c483d021100b42915400c9500103004000c0b1010421955000c111849c10320a040c0358045000301c0c0380307035810034075801400482d4414444080319030385810802800c1540d240b451419640854002800190583d02c1103410810044101e03401c0100c09100ea07241100c1224100d400c0d0341c5076601081001020040010b40c1c00780750034010b0070f080c1010704044c041d00707821001404 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 273080332 1250 273079082 273079091
    0x50a140703080a020604150501030305031b0f04080714010c080f090a05040c0201050a051006200c04020403050d020c0109050928060603062c0105121002030f0402040506040e0d03 78
    0x41201000808019a8006012901c035080c60001a4550004a03010754040c08800c20740390800e2030710721800741030301d50544819041d526000309481c04c0030825005121808800c1110601c280084005440182080402070a0440c105204c40c0c6840314083d11644c103201d031101108002800701c00070346450846164505031119040c10000707608000c07a45c00160080e16000f4100b0301d0560640000740b0500c241e0400303025540741e4540303400d0b4408540c410b401c0011281d080072020307241400c0441e030241100c00202c460320f405500000b000ca030700552040354158800340d0f20b2010a074050140707040381c4600742040c00c030440ca400003160750418002c040c21700b1820281304580c2c40780c0120021900040446d442004501d440b901c2c0a80200014040c01c07420f121100c00c030441103840003600c1c2449030780d640e45842346a4038000c180005040795200c401d8040c061202110b912503035610203544148040359002c8010b050a005201c21501d0150015000720b00f050110745003010001503190990703865140008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 273081582 1250 273080332 273080363
    0x6010c0501060e0a02090f01020c061603110601060503010305250e04050316081305030102030c1218010908030115050c0a0201080c04050a170c09100b161410060501030603050a 77
    0x74014803680e007018038580071003002c0c0119400554081d0528180544d112020000303110010380c1d03118005000300e81d0107042002105c0c01d01d4020010a814144030303040102c1c042d684611171a0810030700341c1185000440200c010414000d00304121841107100c2c800c0b00701e101031800b0300c0d450744034110f00030083c4903403070480400c0c1003100c1001214840368040c41c07210406441ea00c1c1c1003001c0c0d40603c60b00e034211041c40c42c012820b46070600c00c45c3d00408440c3c504d249040301c1d1441c801c1c20958002c010310400c60010100b426105028010184014860140140e996051001005092401c603030701d0b408003c01401130300c0042c20005540301c40d954090810003055603d60070300072414071a42d0000c40d0800014440002d80c14501d07100074038803412844c20360745006000000e01039503400031980060300c00181c44080103402071040041c02c85018501d03450b441110340361502c3c921a00400d100d4085540104410758409165100e200003500b0709107000d1081074030315181c843d5614020003018109401c03415401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 273082832 1250 273081582 273081593
    0x3060e0c0427090507051302041409180a0c0603060b04150e03030903190b06040e0a111f0c030807050310050105130801090f06060e07050f090d0b1512010209010806010c 74
    0x300e07004000b00e401d011032030092070041d4681d400341c455103014401d1914104c2c503103c2540240c1d026101c0c20004000314551803000c0000d0400c0213804020300208030717440e03244041c80a101030192a80030b00400c40201d4a800700040480304161b00c21510218188014010301198510000203000d45203400040000841c00003801c500c20502021b074140b055400300c5014141c51655102500d000e0680c00703d16903140c8050201f0f850840e40b0b0000d140c2c000030f40c244001b58900412491003500603100441d034038500b02140c40c01da06040d44100120b09006800003c060784107480652020182c40c281e4290b041002c600e40c0036000720700446051140c00b15091803242441c980b070030014078855000748240025420920b00c114405d41c404d44503d420044081480e0303100341446805548150344940c40c01c450703c0b03000090360b00704030200341d030150401c07103da004182066000c40c0109014440d030b61030000900100402e1b4081282c610702a64014800c1c50700e50381c4c0003004c00364880d50a08103c200060a460031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 273084082 1250 273082832 273082889
    0x9020a1203170c0f030601080a1413210c0816080301240c0b160e0a09060f210213020c07080304090e150403050903150a090c140a1e09020403080a03060e0c04 69
    0xc001d81c50344c807038007000b48039083c4000310b854503070244100c491005c1100733040800c10700403102040d0204074070411000008580c10000d100d6038100d44401c0d45849000c1da50306045a1013a40560b0111028890b41a6417500908803900b4000c9182881d5514505981d140303981d04d040148003a0a0754444051440305600a8100c180b80c29402410704070f5032030721407050030000c11481c010314840c0c01020b04e0106903d419181003c1e00843d0110616401c2c030314030b508001d802941002c09107031040d0203005808041c0f008005c201c0c00303448090040e6444908000c42d05080701c00c08030000b262648084207540005072196401070b006030301881d00e41e40d200040e1010a26040e086001c81e4000c1d00480100500460554024041035210324040132110760b0324004540b101003803074010350b40803c209200b001100f001030014090b03000d0383c00c2192a220b6642417024101e030801e42c401da80410000a5034651183c1c54860f40014041c2e80f1102e981034140400c0484260080b40241a003840100980b04810003c40701e5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 273085332 1250 273084082 273084101
    0x9030c030310170f03030c0d0b0d060b03010c0c0c0509060103110c07141f030906150e01030b0f10090f022a010501081c0309020a1203170c0f030601080a 67
    0x850360359080003042c01041c20203512400019454581d80000030340030200d806032003210840c00035030a58944142d101c206038803a1034203244280d40ca50601c0c0c40c03502c840e00c40783c400702d0080d00d0004000c0d0300c450915003511035003074000c000c002d1143e401000042c0710314041c0c000e462742504c00380c00c55034074400183c000381410700340c0709080b445c04155132030580c00c0000d80006484d800191100541540424803a81c3e00b030200508000041d4910031141d040c0c426031005030f13054080c1d10f000c18030b00603164413920000940c3c0c00c140c1030080ea4000507c20300c070703d07c440c0d160059980043d00195103044504030501c01554000c4940b140d807982024010ba44a58055510042d4044840407066990080ca2011202d042801c807295500b84030000034031020110716050f05040c92070020f10f20840c5108101c0082c40c41c42d0b022a4000304421022901c0106c002a4018240c803d48a1820720f00c9100206880810011f2000b150710400704043c094400580080d21f030005800c1c00c0603000d81c0c40e46011540034103000c84 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 273086582 1250 273085332 273085357
    0x7051305062403010303030f050708010e0411120708120f190e130609050f0708060d02010507062c06070906030905010e0111221511070f03050d090501030c090b030903 73
    0x41d501c000707082d00034000e5040342d11a4508105140000e615002612012107855000c11604401081190704400d51107500c544154071580080000100082d0641070413404080194000c9e6828414071004002194201030004d00c1a81030900c4000550303502d00c43c0e582a000c1003141820410002ca000b24425458028000c1c0b030301e5280745100d00a00e004042c948181c02400c1c1c14000452400f5049c0c800050190392290380e0805580d4075401807000f40c052505040341009000c0058201142d450b204810302900c034083c40140c1100c1c0310500c8d02d540400010741040303540110083c003007004e402c8554101101d0300d500300884d4502d02c03410300a006000311500c524040d42130041c09800c40d07044c200240901ca03040f03181213110a64104c180180350b640b40c01202100020610809a401c0c0a0800400c00c1c900c0c460444003004c3c1c0710354182560080c10b50044465902030004000203580111806014000c20310f800c212851900f00000c0030340307031148556000a2400000705250302024400c440e000ea8404 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 273087832 1250 273086582 273086629
    0xf1e07060c020604060b040905060c0c0a0c091407051809060105041d1f060c02090402030715020a061116061d0102130510030504051c02010b0a090e010507020705130506 74
    0x2944030034003100e040300c145c0d180126654540c645441003154994101d00100400c0d41c034680030300d10580c401e4403200c006200e007a20600009009010754030103001c29000c04a03001c56040780400718840090001003d10605109184046100d101100fa242d88102c60101960300d40c0c00041c0c1c3c0c0c82c800d51b08001c1008180c0300c4000a18044000440e0084004d104105401175440402c0220312030036004403800280b8003001600503140020201c0d401c140002c0695100f180d03501e01e05c10b07104000d801d0800140c0c00921504081c882103104501005c600702e6015480c0001218060703036440300e901001406581e568042d4120200041c00c40310303e25800380c008568079144444003048658480c4111403140d04507071200003070a8424020280601d61010040511821a09580c030503062001520b40c110341d624920f20015a41c0d0310380a00041241a500169140322081c1803401d4510040540043d5070050004011039201e416010780d003000700c01d40002d40d030740783e0030006013640345902017842044589 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 273089082 1250 273087832 273087851
    0x9040308060d1713052d120a0506150103090b01031514180c0307080c060706110d09060507080402010e120c060301060e090907120f0501020d090602130501050f1e0706 73
    0x1030300051044c0c0c503842c40b00843c0c1550340c10802440d40702a10341007640c2d00000c01c0ca400c402c10b44c14101001e1800050040c111000b0403040c0300d00c2d000072081705440d203501820078012550550703a00391007211020b203824400c440302c0b6101e00c8400702041c400200042c083c940707003d0901c40258031042c0059088902d5101074100f01d2901c094859808180d844c0c0c1d0f004042c18401d03245400a2200c040b500701ea800307004040005070400c8003c0d048004156006911380108241305aa00070003050038408581000070113500d1400c2480c100c1b5401803000040c0308042d4140400341c0c0c2c0141c0c40c0d0341491011643d2108001d1601800b6003005403400c6a985c201c1404000401c50340c0d0488000c0750304400548211403107a49402c0c00319520046840f6034000c001c2d02000c95400b19480403002c020150041c0c00145c90a0300d0307a45040c0444140140546d0480c0d0b003c0748040c1460861100f02004090920f001d03810310100601e5841140310348125226084c030788000e007940c2c021881090b505030a80140f4100044890b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 273090332 1250 273089082 273089123
    0x503090a021002010b010212070b01090b0112060602030304140c030705040c0306030209010b09030111030c030411010e09271203161107060c0b060402040b120703180c030c06080609040308060d 84
    0x1445560b1b400742c0119404003910840b0300c02900c0560780c000490b14102c0e4600300105006140c1102441d040145d84c1140381c1040d00c40d4040c01c07006001079401917640785428108480f0441061000500581001600242c2d664002400c1415950226000140710001301401e074001d1a41d548001d400000101c00001c0038504613014007081c0100340d009001944c0703c18003000081c48102c1e500d0410741c1d400c0c0702013408500800b6404446035018140840c640351000d000038880d100842c0c5002d41c075040321074802c23900140e29070490205108103000b0b10308a03503821012400c5020040c109804100c1035070250780901c0c42442e4541c4003410354000e44941c15114071008100c0050640151214490320010a41c036003001c1c42114100c030a91244242007007241203e1203d003590142c600c40802d0b03100c0700540da203210101d10306940307030f8414800412a03924506e8040034281044d440700c003c0c8502e00c010001c2701c2d100d810700503601903414074000c051941c5003070029401901c0310078040d10042c0414050002d800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 273091582 1250 273090332 273090341
    0x706030218010c03081f0306051303021b03030f0d1107030507031d010503060103050a06080105010b070b06092a070807111f0f0e01030b03010f02031608010f060503090a02100201 78
    0xc0721808900d00c0c541d00066828540148006001561901c001059107036002d81589150b450b450f5180e900c4c503a241c032350384181e07407054480000d5170352915021020107030100720103096412507040f1510144440c9d40042d0b20380c0034028102101a50000f80403005004590110800c40b2040701000c3d254030242c1002045604862030850109211440c44514645013244500100405a40305859075039a580110040d102c041d11110300552243c8011485010a001f1a07010b06001c01d00c580d1200a1410099001c00000d0034050080b140700042c0b000d0803101c1594220002c9440c5020954506900b410a00307512070b010003d041030300d0204820042094402c2000001c901c2150301c00031030001058111035050801c910f8002103240d0034240290301d40282548403030b5450504000075058142c501203429651640e40500d0031542c0081000303c0a81203012000c1440d01c646481c070342d59810012003454007540ca0107500e090000110028041603070401009120582c060034041311030106840180c080e1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 273092832 1250 273091582 273091597
    0x4181b0e0112181707052e0509030406030b03030c03041d0105010305151207031b0f080d02071404060b0c07050f0316150203070503072a051008100807060302 69
    0x8000c1c140040c0030b8141800742c40112415050103d10843d00d95445924000d41101d24001c01070b82802018041030050011540d15080b45407001c610a905508100f01052900c0903e00101e28100500410f280000107a17401d82d041c60900140081c3c0c00300c0068070714007840d0000d025520000401080a08060028a40e52800e469404010f6603d4900540030f81e00129443c40040501d0a411405446d0141c01e60015405d120f06580c6d10a80300d440e03201313240500080c008401c0284c48420880031010b15440b40c002c1000d50080c01c22072a000d07200035243d001070311440d18030100d0320350025026070301c0c0c4d84030350000c20020003480d55911029055a0f195a07052060034400c080381420010a8100443c2c908408004a004581c042e400c007854000d20004d03035562002144418000440000e10030001454094001c0305240c800220307200700450349000d4294200480391900d0001c1105445a01e9000345903400f07400d00d0049a0341d034022038242c0d413079203521040302403044c1c410000701c0c160142d00801d00d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 273094082 1250 273092832 273092837
    0x250b0a02030c0709020c06130c15020a12030903021015260106081f0e240a060602030403020d0b0613060b040f14061c02070501020d061d070504181b0e01 67
    0x2284c1d9180000c08030301840d003500f07115402420005d1070680c82c901584814520441d403030f800c956240d40d040d0f078001d0074070102d08015a020300001c005002c05075221003040c0266207011311004a4554000351500f698900c1040c0b0140c942c10040d0303c3c118a102c141010749081c0200e40c0080944040c02001220698942c810a5191a0780030883c1c40001c52242001600000c0320400342d04001e5200000344140721400b002e6000e00c0b04251072400595840f0300180101c01c2d00c0501900f40303c2d40c200102e4107143e0000702558020007003007005898502e0351a018642001c1b140305580c1c1c5c0d110106008ca282c4400e80d042c11403502c400820303105074a00181003610080d40d45102600d4030758440903440e100c52160254400c1043c404208900c5000c079840703071407032200c3c01d026043c07080c1c550341e036401ea03000310304010a656100c400911501d1599000030044100b000540319040c10160405407a520031800b44400b007101d818074100704500c99402107a0525001b034100c094130b40c2c80d03103001407586000080c03c500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 273095332 1250 273094082 273094093
    0x203011404031205010e0c0a11010f05091e060f041a070f0e040612081c2a050a0903021207030f0627030f05070309050402070303050406050a0905250b0a02030c 70
    0x214001885900d041ea030400a03451207e8031102c4051003550003008844040110304403120510f0182030003446149424160041071170f08140c40114248401d0aa00b00512110001d0307800e2405000604290000c298188680440d113403802e090010140040f41150034818035406c0c40072055001e0b105007058800c90703035629040c404410030407040d660341c0c5c030035a404107084001c0d5201046846000b00000340e41c110200c0072041210710a00240c9400c03802200d014407845015002072650b22002181d800d07a98600145442c00d00c50340504000c0740d5000103030003048520351032400450f0030070030b0320701441d0000c108001780030f0071749080c601501c400c100515581201c22004401450000001d2861a0349900e8100744100b0510040b6541d0700040700a804000200303030006080d0721207200070092140030380c2d0003003030518150600340c0a50304003400100450746090313100c0001c1000030074174900700b040d020a00303420340c40f0500300710b84e400401d03401442d600040001d8a2034801c0c0c000006008005022060b2070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 273096582 1250 273095332 273095357
    0x504091a07181a04030212031b0a03020106050a0e040f15022a1c050d020f04080c040b1e131103130302060702070315022215090f030201020c0d0302010207020301140403 74
    0x220303003e514072426407520020702041c4010b24144e049001c034801c0304c000316810301000d80c040140801c002c100d40592904104140c006065082c0108400b400c0282e0b481c01c01740d803811100f001c540790014006000891022020f004200568101c3c054004c03030001d0642d00e0724250403410041e80d400307d0044840c0c1c24155117000341054082504206094401d40644000c08403072019140386d80915561400e4690801c00301400001c01000b80c006844110001c082e8080444240400c84100c40416131144c48200040509401e007800066001c440c290f0301087c203a500300051030041d20842080c65000040841080440e10112440c2e45000740290700311070721381d140c4d92804d90300d8800ea030102416503000c40c10140d007502400c0d002003d40000440190400c20312411806070503400c107030001c03140207090161034080b0b990b1000d101c0c0003030074045003119201807465001031341d0b50300b00510050060b02084241d02c00d15000b90305895585801800a00200a01d05503d5100c1e100854048011400b00b643d1302 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 273097832 1250 273096582 273096599
    0x50c15060303030f07140d0c02010e0a050c060d09020909030702011205060607060c11070305031806040513090c0801020a0507020909060403080411040f0f06090c180504091a0718 78
    0x2802004003401a52030f60f140d100245042040003018001480031704d80d11089030b03030107403001091055040d9400040704865210008d00b5a080003818000d136502c109228408240f02048001e84030000720b8070710b5a21105006410050f103000d820280d4090501030410024110220041c10a24800d82c1c40e12102071341c2080741e0040351360076103015800030780a2001c00d0000d10745a20004035550076040c05040051424249450f06030150000c0394180c00103c0c80d4592001458425880188121019420300e81003001060b02501d441c1511400f81b40c44030104418032050101c84009406440c0095580c0e0301c540001510982c0501001c901070f80342100010000380010403403038003070b42c0e240d030364982c0544441d1074491255400e95512070303002c2d9039210300440c840418450505454001d070720100d40c66140401d4901140d41e070400d80024000301f0444504d84c4203c44a0345410384604640001d40c2407058140302480040e000104c413880043c00e014000926017042c58080898100320914100b240c82c0c0d5041c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 273099082 1250 273097832 273097873
    0x1f2c0907050304031d01120905250506030f070c0212160608090d080402120a0303050f070201200c031b01200f040323011107030807030c0f030b130c050c 67
    0x6000200181418001201031194504034600c0501d440600e8034130a030f10107000c403230950b501101c09500100401d14051a84d040404200041c1c80c4c00300e4190b0f10304070105a5902c8010503009a51030b1000001d04032a00402030b20704010f8014090f00c072030f0540141d41585d142441c0c0c405c000c02208423080000e2103071003040d025108400c0c08010b032444807442041511942d80180080340d00c041c40d800356040300c1c01c08210b100e0304603019039004104c80c00c0c030000d074080000d80904008210f90508540d030108640802a03c40b9a007d100345050303907130750013180d1281580a2400750307003000c10039000420b02c1c98005400903802c0c40b04420740d080103c060340d41441f0302c9220303030086c40389c0ba804248002c101040461900c420801b41c451540c24006442454503404c466080302c1200c0040d0010996006042d03101d003405a01c1007070350904021a5415107000b500e07034500606001c00b01138517814100210b03200d49142d01d039594034059082c131554404c0c0c00d000c1c0c142d400c180f000700c0452061a020700d4409411150 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 273100332 1250 273099082 273099091
    0x6060e0112030c06090b090a0308010503030c0703030c030210140f060103060807090f240627030b040819120b01050304080708030408070804090504021e1f2c09070503 73
    0x6100d004203070303070640300856030000949000d82c0c2c0d64445d002040d518429188918400d80c00361800c0b080d145806402d0202c1a08044d0080e40180600005288006202e000b642d805062507801c03407600d0301c1d040389080803050040c1070480c20070300390300303601411410000c0c0140448503603142142c2d1414011801c0360300381c1c440c1c01c80991211204101d0320000e0703403200b5075800c458007010a04651840112010303842c0c1c8076075034900b00305c1c05074100f2260b0317400041e1090300c00032800740e22581200c88010f9010b07038206000c06015110440c001c0350401c1032440803540b0340d00d854096542c10103c03420016100d244408003400d80c0e41d081608400d0290300c05c004480c0710b1a03100e01c0d40b9051540b0f0307841c0c41800ea0002082100d2120782001040f0114034200060401409494800709480c5064810f002c403803507000c500b0544000c42500503100c2d660380c14440d074075020f0040901003284103962400302c81004000058103e80d0300d07200d1480b40082d50002100005034010349464240e900c654508662511040342d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 273101582 1250 273100332 273100349
    0x9020906220f060f0b090f09040809060f0c06090c03060a02041a030604060506190909020306030c0f04020d0903090f06090609060c05150f0402040b04020c0307030503060d17030406060e01 82
    0x84003920803548951050440b01000c5400069594a68031180084803058126103481c51010540542501d40009092100702058841e10905d003815901c0007030078010030f00498071420010907007240600800041c0d071b940c2050041107a116081400704151a02c00d5404054080e0080600080c00000300c2e0007181c040380c0e416219800700d05800d00424695030005844140c0c000c1d00c13240300054541c1c1d184040e084a4540244040401c003c4140280104030207501c10a8810f005004020880d540071035074200d1a84151013054084200b20000740c024403540300143e545174500480d11041c9a400740d08042558031a5941c6a405506e0b0030302628805c0462083c10002085030805001c114071030181350b40300501c2807040740c41c0d94500045810120b44101c40d100c102c50443c070200001e5103000c0c002c0002100c020f071021854070284c02c5540c3d07200d204241c001ba06010b00040824003a403a40c100200301e040e001152600003c030b480344d54074600d90003030b101038820504051000c00c200f101d000001f4105c2d00b503003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 273102832 1250 273101582 273101629
    0x60b0a0c0b090705060a0809011b09060503151e01032301170718052205060a090c1703120901141321050a1209020d2607050109020906 59
    0x594900318041c0d4000c00390700d0b041c041c9050000d00303a00c1e084003400c29000c071521a04024540001030500b1503458541000e010725900e0140e4400c141c02514006c191103c5160403552590307180c0c2180841700e81e103401c1d81e411145000118000040c0d0360200782208209980030710880d0300151090300700c1c08001d03400d039040100da0740c0104030700103d464040c51294480ca00351180386690b11414206072001c080e5003016140c071502013054294440c480c03460f5181001a403601c8240490704c4056484000500807641203503284054000c0c0725080310418000e1102250b110106800700e1141a06c90300200340429040e44200c0100c1c0d1419010301503c000103e210b0850703080c650710140c808400300c0810405441441c070290700c410030b843d540401610610706c5030f01d619a50328039009008209813400030040e000e280c646002ca1005075070b005c40100303440f0342000c8001c84c2044090450b0700311800c10301107440c64000004451041041c1900280f2001703008813402c0415070780756003e000354000c45191140255041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 273104082 1250 273102832 273102857
    0x10b010914060a1205130c09090c090b060d0204080a03110a0503030402010e0d05011407020d0e09040f03020c030610090b0609131d0d030501080601050d030c030804031407080706060b0a 81
    0xb00d0301401e40302d005880c02141c2d114000c030b0010308583e0242c812550802c5052400e2041c00b0311401d03a20b0050514000401c541c2e64691140c080440d42c0e0302620f21100d455081d03090700d590311102501d039039120040d400c551b00c41d514581565944640803003280496181e0904c0d185024002c10350712400b58120026500e1552181d0045030ba6071100301060340e000b20144041e40106900340308624585103082c01c403241380c4c20300d0080130707107800200c07010201041451080d04c03141e074980c82001d58000c2c1e030004c1505480491843c00307078240000702d141c1540620590f41041421011042881c0071a8003101003041400c181d14203102d110302c07070031060a0b040713880d000d00040729400c194005000385c0007811017039042244040440d0704084400200500080d1100018003411000b40301140c010030040316882c0a5444c140e4003c6c08040c2510409170500060f00c00007800e060040542d01401c0e14821102e5a86803004d10f09201d0913040b08206a454902d0101c020901c44000c004440a03102c540d224000700360700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 273105332 1250 273104082 273104089
    0xf0901111207090905010e0f090d02120f0c0d020a0c0608010302010804021c0b0118060807050f090a2c06090a02060306060d0207060e0303010623030a02220f08010b010914 75
    0x1400341c4010108021004001820070b0548a291b01a18074520401e9660504200c00729528001601c06030403034224500e504801d640010390421281c2a0441389620b03401095280c40c014022070b041c0e0052801441000807845038040f0b0b031881024840e8511900c0e890300c4140440e1001800d01000780032620304004507016180107680c001d02c0000715002e0203140a10b5175600901800282d0200221880708840150328845a0180c5d43c0030b030200500074084240b8000000b5681100c44010a003d0021038002c00d40b0808150040c80e80c0c00e04516103030003d010380010034016400c810407122000c0c041c0c800410b003040808140d41c50460b40040505085442d00ca003005540c0c0c3c007851603114070560070886000081d85902455240c0c210100281d45c6a62505e02c001d00b100a002d5880840c19907081c01002041c2c80034400c0d80d402034174880f0016111541c0c40c1c4000790782090882007450101c4108000241002840014000d0300e00c0079000f4031444980c0f10040d90f041c1e144c0d0080108500030750400248030309 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 273106582 1250 273105332 273105367
    0x1150309050c010813020a060305010906090504080d0e03120106020a0c08060613020901020127060b1c0318261e10020c03160f02040c0e010e090c210f090111 69
    0x400c400c0e0703104c1004880360b0005d4400d08041d40248d02107a118030041003044a1449054010000002e0901c20340c82c0550700c1d0794841c49510f0503050050b50b50364034895226410002d8400c1c900b01c9004000702961110006503039041608021600312034104c0700030a1a000c04204640075040c040c00b031841d10013103410880c021350002031a40d81103640e1200404500c1503500214255503402c06400740c500805800e01c0800d0303a440400705030041039580d500200c10f011007995a840150145041003074080d5a5003d1b000742d05480d4842000c5103500c0d25905030b40316004205005401051048a2516004410040c03415040050b08086a0480d080600d00305601d6002010240322200540349440e00700980044030404c0e07240166900300c48a488442103041901c50013145107500c3c180081821507500009020301022181c1901a0030130001246c601840d0700b09a8001403444c54441ea21001e1076101918070b8601200e030300c0c01a000e00404541c250030b062144a202114003200d803840c0034500704e40c5500f000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 273107832 1250 273106582 273106591
    0x90703060c050a3612050f0106150c020a0306060305030a081503030d090c08070b0d0b03031c0e0a050f01022101030203061b04080d050d0c08010803031303050903030c0601150309050c0108 82
    0x2060113141912628281038002003d4403040040d0f240c0c0b00110300382a4901a03011070300b0126603151034000e2101d540c60340c0d0808000c0340540380009243c07001d88040340c460f00d50355000604041c10301d04048100320010000d402c000300c0964071170810f691844d00c1c20001034890012107405420420003100c0d40c003216080010458011031041101d20fa590906903d0141c0583c8800d00340500420003d1103c0854024522111801c4009604100581c408108a640081410040170b07941c1c1180903468071040c06030707210300ca0b005029111103100051025000c0c1d030141c000304c20300c000c2d80c03001ca80200e200c1d8102c8d50b050f242c0141c020310300c0d0303694640140c81c6900a54040384c02d00344207020000b403040c0108004200030300300da95030b6030301e401d0700c1c900070070a44558041c1c082c01d108011005010891000055960102c400308071a560308aa605055400b407054070002601400b0008402c5810b0f10009807060481d0300c2908034459401c0c0820048003141c21010005200360499441a10307158842d40002c0d403c03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 273109082 1250 273107832 273107897
    0x7110d0e01140403140c090108010204080c01030c18090522050309120a05030c0a0c05010c110f04091505090d1d0108060a0b120f010801020a09050607080909090703060c050a 76
    0x4054580c1c45094807445c40c014034005641c4003110100760350500c80c0c3c07194010b2050000075400d050034503040944480314014030b107040513030340c40c030b2114458480c5004101b051580e034200064a5140c48140024040480f0b01319030050034070031002075141030040c0600d0a20b4000c000b40d4108410b240c1000111000c141e01000b145c815050020b001c20400d000524000010f04010940c81c926840d05626440c1d59030311840c140040700f0f035020042007078403803203000c0c0301d40440c3c3c0951100507030400500180081c0d0720180104410114200c103403191580300700d00611001c81158200410f44201300c0f11180d030703c05034920003030542da414000c650207003031800d400201c01800c80060580322000c2e4241c030b400c941d240510426127030b4180942181e0352054240508034400081d403030128440c4000d0194861446001c1c000c030300c0001d50341d042c0007500056a000840007081c00d10207007090101a0f5580c0218001910000e1034042c2e001c9003103026408131115600d40740c850b080107544d0100414104600040032080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 273110332 1250 273109082 273109087
    0x7081605030301080c010201230402010f03020d1802090a091a0a060e0705073503090f0a050304091a090a0c03090203100c021204031e050a170307110d0e0114 69
    0xe0018005140a008800020203140c04080002829140120310134405d116148101100208049100c0380d407003502800d014000d890340c544c08400030320802d101142d00034601000c81c81e41692409084400c0c1c1d00844d01c940a58551448440c00c41d146154024551b0525105070b100881001480303651050ba8000300140320340d075983e80041104401c40300c040001d0000100311007044601d001c01c501600da03000745804011806031190100004105500d0300240c0d0120000700006010018481995440001ea555500291906c0c0e96170360400d000c4e00741074a052400c03084180c1602071100c203000340d0003045004147c80f203410010082281940d11020141c6401000b000341e20104007040c0050300984d00010501c5402400900340b88030900043e404000801c010000307c1c815410061100d0b02e50400c10b1454911860103616003555a0401440340300e183c114108184100006940704003020703100c00d1502003503428400d8451000140340310220f00d00d0140900c4651098240c00405000c2200b075a2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 273111582 1250 273110332 273110377
    0x801120317190e0601080c061303020604030c060f0509060d0e100504120306090b03030d0c180e010f0b090d0b19090809030d0504080601060c02130c090302120309060708 74
    0x116020044440d256040710190309003003101903d100e110754105142010701165410050b111f038980b039844200900c145804144104011154000e480045074024540b41d6203070b84ea40750203103800c10f043c4070b8100401c240c000c40104035070007403003101c60201d00101a1803078035500000400040002c03540c20b5489104510040c00c1c0e0203041c1c030619024074010100e054070782400b510000c0980c1c030590884991179040c00080101e0341c070008240c440940c100c03280807681000b02c20b030071206642c40f21044240d0f03030011000010680d85544041d81030318075401d01000e2954485901e1225031058034011508043d48100420100d00b0a50f40c0581004580407000d000c2000703042c1c3c08003550300d140410f071521200020307031801c94507007000100b440881c41d0815a0800b4900740d541521b42105105001c103001e50004c01c2021560741055404800d040340074100300003c0308200c01410440075000c201c0c0281462840650000d50001c143c5149500c0213100d586040c000d0b0703490703074480e0b0007000280503501c9140c4400d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 273112832 1250 273111582 273111617
    0xd0207090c12051e07020732060a050301030b06010c0f0312020c0304091e090f03120914060411120c06180405010305060a05010e060a060807171305060f060108011203 73
    0x54024030256012480b40d0516101030094803502610280a40d413082000700b11285015500e103905160017100c104000400020740323103123242002d8450b80c0c050400107400c69520781080145058030b0294a0303064a59a900d801550982102940130b800e00c0d00303109080340000e10520303011001c0c02e032004026040411800120780b030340d04241c102c100c80644a01381c01400d811442248001c00c040d484040c083d0600b1078446100302140c0803405001c1041100002c101411290406106a64010074000103052015262031300c40f84180c83c2142c040c980d864203e4100d24050701c106000c0c00e0040040c0108602c100d0402200703621003030700802c00004019054440303550b94400c0f24025401400684441e00d0481c14000840380141c100344809029030b400e014440d11a0440d50b8180c030071a090141c4a40c44074841034400c207044420360b4040c0440e0b04108081800c5e125000102140300e50203c0308691034944200071482e804842c00c80c0081e100600400c110750707400c40000301107800390070076480544001185 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 273114082 1250 273112832 273112841
    0x50306010f030b0f071407170d06050907031512020a0e1008070801061a0f091002031e07020d0b060d05030301080304050109120201120209030c031e010606020d0207090c12 75
    0x541c05881c001c4104205021603803200d10750108003081164018030307009601810804001000001d480404201b0780100f29800e65a5201480103052981e101c6003072880b10700184c41c2a018040c051600b01e40801c1e03c284c001d00443c0000b0081c84d50f1110610300b810907030558101c6504c0240c0e0320092100000811140f500480ba00842102c05480440d50500003c14035002c400d40c402c8410740e14004e0108491800107001300f1001126a0320701d55140c41180034001940a822501075008000521729045650000000d25940e0440d03034100c10b0805040e220044e0758060123201175004205100040c00046c0b00c590100d9202c10000c0c20780d182c096494a13054a10b4100b40c0000a85500004083c000c41d030f00b0140c070348010311a0071125540903a2950008103480210010890216004112545681d805100951021a015049803202e0b020620581614150000042015441c0000c08502e080c13020800c0c846040303803078004103d028905041c1c2e40c000d03d04015840c04025501d1148408403038107008 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 273115332 1250 273114082 273114089
    0x209090303091216080a030618090303060b1c09031e0e1306260c040212010509130f0f0501140717010e0115110304030b07050c0609012a0905030601 65
    0x650322403912248080c0f9010785194024460101031000420b102c4004c0782d082c43c4245e00562160325107003041000e0b000740c00a5002194881e0031841d001505031050b43c00512080c0c02507a0502146555100180c2540b065000608440e030050b4a240c038080c2d01362f0000c0709030901c03038984480000d4045140c0c000800e10900380e030000807a8550f0139415860507a0540c100140d181d28108480b40c0750500f284078102d880102c51b02d044036050144640b5020600184400c0e40010b00159a50002400c0c4400c02250902490b0701c03c0f61050b01150702d43c0780c0c05909000d02035005186414400701038582582801c6125130444e820341d201c034501204d40100040060242c2e0f025141c8842029034058003030798101050b000409042d17480d000400482c07020143e0020410b42508000c542c0f20134010420707040d0b10503500080c2c49000084240401a0703070150060482e8444141603500503103503811060300765003004050188038500d1420b0902050040b80d50f5640c840c0607810101c945580d10342c0440e050500036071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 273116582 1250 273115332 273115351
    0xa0312050610050c120415030f021201060e0109050a0b0a1d01080408070c050a15020606041514010207030c06081e06130f0b030d11010f1e02070311070306060911130311010c0209 78
    0x44d11007c05402d0f00035220010110f68056092a03009255207402c040c051151004029289010400b41c2e4040c02d928400b40401510080341603441d09420085a0f122003178510010312840e14803620149080c8003140c1c5010141d65079820350300c80340c98960340c40d00145802d69280b1100c1a001602da65000d00460007071104074080703d502c65103200b0107420440e0042c0403038000c03810801c3d5030b00b030f4120705071000c0b080d03401c0f40c00524208004500102d01c0c2200c5030700001c050484905001c10300b03d800c1816144111030201101035140b90a10b0500c000c50030a641842d04041d09449040741e0500e07a0308921890441c03640700244030080c00c0002403405e0054000540802d441c0b00b0359100e211020300860340301c0110400d051006154440d01c00c40c190b10400311840d161030b40800d1031810144034240c400a11600030044900c00744d1030b4141075009052070f00c20b0a0416150000508030740300c882e002e8440115014010944c00740c40c6840da50602c0d0b0b02c2080082c1044243c140f40c000681e90060301c81e00815207030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 273117832 1250 273116582 273116609
    0x60d090f030f1d04020d0e07081b01090e010e04020f0d120e0d17030406090f08030603060f07050d09050102160807020405070c2d020d050a0312050610050c1204 70
    0x41c200600301400205034002049000704403081c620300142003041d01031206541c0145e1703c0581c500000d00a0110308001c0700180102d84002860000000394016220032188041114000c05c2c801034540c840b4a10814112050840041007902c003940845076200340060310310703445c040d90800000d8600301d80100c212f0382004a80e00c800c00c280d030b11103821011080d0545a031600c10010b038070703a901c1d01d41c0034241210342e680c40080041c04102542c0c211002c50f81c1d02c159019030402042c502045160800c8812600900c109000101d0b18003100081d0350190b2240c0e12294a054003860313820019106145083e190b03507400300840781c166410035501c449443e0040e000c0030746489017441040b059507006001c000c10810103203140400310300c01440c03221640d59000301582c1c0e6010a4502c0102101c500a070103035001e03500c8940d0310284800443c0303020044e032007070ba034400c00c4005007920740b400c580050f40e030144c105c1c07504079011600074011001070000d00d2008044802210031103140c0300c0c1ca03901c241c101b42e6015010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 273119082 1250 273117832 273117863
    0x70f0b0903152a1e040f030f14010606020a03030f02090a050904021f02010c121a0105070501090204050f0a0b040c020d110708010203040602130801020708090409081c060807080303090615060d09 85
    0x1900d00c00e003d5910b0301c6403001d02c1c1034601080180c1e1086c1038000036000b045c40d0040e04003080741119008501134949002400711990f2018040d403201000c0c80c042d000b007030030032400074480f10080c82101d81c01c6000621040600f03040c2024418075400040040340c120b19840022440c201c00140101c065400079400410482d0713281c3e0008200e041440100c40d64a13042006281100704480721850381d2542c01c0c03800c245c40f00003908003140506805480650001e14050034041c0c0c100500b580c06100e80d8403404140883c49603802404102c0b544000c002006800000001c0c2d0a54840c030703590406160300004580c0c05985641849089a10a4804880e00c960000b500840c22455001403001081450001c50500c14130380c1381c81c1224803620303143e10b10540e5204046410440702100b0340d501001e2036401e8029200c04070f0307018001001c95001e1504d0750f100d0351000090401c2c0c000100e900c940c040d0b00c01741c0040c2c2c60f10700071140d4031382c0020f4101d6444841444200342d050f070303e44114030501780104840310280c0103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 273120332 1250 273119082 273119107
    0x10506030708120d180c0803030609090631020a1715090a030e041e0e0105131a07140708130e060d1103010f060305070f0b0903152a 58
    0xa41c2c1e00c030036201d401c010960b290400025080e90507044000e000414540d9180314040c18641700600000d0011071000c9010564031070001c007071840780f1011b8800003c10340f91120001c6d0b880f1030445030105510043d8207903000103240c040307064101d141100411000040c1ea6800110b480f82a60010100e442c405600414022030420032004540030a54180083c4d080c80b0080750380712030580b10050180b01c1170300610b004d15200c59121816058814006c110400f1036040c041c4080d03c00c2c0150780602d9800c0c000840d032550000d0b0040103010340c1c48402c1800c40000320b20701c0c03440b0800052000c010300405e040c0e40140d00c1c101100410245201e80e02d150380e03070000d8038000a0442425048012414014000c00c011038803030602180f403084c0c104070b41c1100040c640001a01420148003040900750614030004108400007404000303442c400d20319110140e40354851040300d0701900300525815484034407141d9500708032810590b0030040e5042c201820710213030620a100e6100c940c080e500100c40c0084c20310520701 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 273121582 1250 273120332 273120343
    0xe0709050f130c12050304180504050c03010219030905100203250305010e01030b04050111040807060e0609010c12050c150420062a0d11071d04060b01020f0f01050603 73
    0x40101640003502c255114030214000701d0180c02080c50001d024542449000c00564004001e080d0b007902000c2e201034290b42c058041a14115401e12035140d034a1550314041c026581d0181d02d20b001200000300c10f8078110f0103061150419102030182d2070b00510485580d0009500c1400d9640c8030169101c04405071050742c40c40700305500b080610305401805511141300c155070441c0d400c28800c441d140c031a4106140103080c46180b00010800015000541640100d803000445d8001d8a6143d0006c1e03844050241900c41c1048a900183c2d4180f11200043c50205603589112075500d44141040f201290652a2030301184a50101d800d5140801c01084050f4a2690a080c803803d02c82595a4002011440c0c42c051800c0d0315004980401e1900704520f02c0e1400c4403884941e60003111340000001001408030002015005414054020f01041840107442d10b403070101c400c181c0c28680d50f0340d5900d4840c02008645400c0381140140309404078940000c0050005a070071040000074103003800420503207040c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 273122832 1250 273121582 273121591
    0x30c0b040302060f0322050d02150f0c0703090b03010605091002010207020306040b060f06190201060509070207060513171b030a0f06050c04030c0f05011202070f03030b01030e0709050f 81
    0x142400c01080c40180c8408042d00c500020b007090f440d8032a1100745101a180307148a042c0542403080c105100148440001d003180541d2040d0280c07a81c0d02951180c2000c030140c100e40d0201001d25400100f1004510700c0014400d40e402450031401c1203490320162b030200c4d0b0080c1c2c0b04030300003400030440000d54030301203140c0c40b45001c132030000f145800d14076800f01351a00001000070b0310741605000085c0003500c0da080707000004600108202da440c021500309001c4d080100c221100150328000c00070415042030010140030702c45c82c0d001003001900e0410129001d46c00040d8610241003e44e0001800c581c0e400b0700c04010041083c0a401018810070b080c400010405010503c0703a804a01d0080215203400c03040c4490f59004034000c00e003a40c43d0f5031511100c1c030807039100402030789a802c03000480c0070303a0800c0901075a000760703180740102e0b24440101d0240d004402c4050803100e1401b066900003070003036100d61900d28040c100440c0c036030004401d030381c1406c600e41c0c002c190450f02c2d0010031066040702440690320 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 273124082 1250 273122832 273122849
    0xf03020a0b030403170c0d090308090c0901050d060c1e0e150a09031b0305060903030417070c0b13172d0606060c2803080f0c030a0b041b0207030c 64
    0x80d883c0c0358074001d110600b440d42100c2581c80e4100413400c0100307000203c50010807010740c14001c0e201c081c54014451403007116030b82414010144075010518107001014101c420050968045481c652a03070002840030304080c90603c10702a990040701c1500b8005940b87e10541c0d11030070103044000081c058552201c0440011042c13003041b4412480c0d4001710701c1d80c15260010511802c03400c8102582481410366003000e045842540304000d4a290004001d501c201d106000c002c8d03590016100f00c0d8010b00500000810700c1c2140302d4203001c500e8503540035090f03403825401c0c1865400c0d561140d038451000f080700904803640208202442c03150140303000110a030604190b00140708401d0380804e4075400083e0025101c1d036400a07101d66500810081010018400d24401c00c500d070000213a504014a0013004a011421a1002911440d0800c00c1c00d4400c1c6091a00c0503d5951030b40c6102004010381c944c2d980d13010f640c03940c11300c50110140800b8450703c102034006083d00360035403c0c10703040c1300342d15480450f4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 273125332 1250 273124082 273124087
    0x40603110103140c040909050c150301081603020d140a0b040606080c0303090a05240c010b01031d0d0f0507050304081011190806010c080315120a05120a05130f03020a0b 74
    0x111310800c0030031201195101c01c0009411a540d140060402512500255001d8002d41031640300c17280c0c0d000118100c54006084070b51044c01c10841d030038050082e1101070360080800075100041454608030701100d0005900317507001080259a60340e841d800558044c1d80955071030005103c4e1503000c100000382d0400c00c4000f1420f100040c0d00050ba01d4016000f820700940303c0e06102c404000c0000d0303280700e040c40a42c49042d26030104040c0d86008040c11040240020f04000c1020714015403403501f19030700d030007002c0074250030780b1040d000341e4203500340d224400104102001441c0200360140080c00142c00e1a001404078810f4284114080e0340c442e18600c03413948400c0103000f0b0005071814003000010841d007095030303455440d0401a510900000e0003c0d081840010800c0240300f00401c481901000c2216590410020b520805a40310700021004005500c5034040003c00614540030f00381c0c80e01540b61840c42c05028080c031a01d41e90103a480303800141d0080d8818030842c82c250f043c3c0d50140c90418081070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 273126582 1250 273125332 273125341
    0x9290a030c0510140304240203012301090b0a080609010b09400b01081b04091802030a0f14010903141305040e0c01090803041a030c0904060311010314 66
    0x640d44001403140074403d02c6031415038800d150050610083c4103240e43c56282e10303840c2a0411007105581c08543d07540400040c00e44940d0701443d4401c0d281641d0303220504032407102006a119443e42c452a4542e410301403400f0300000d0f0307242c407070009007641080d56540c4107103410410b052040720101a000105e820308140609a0a52210300240d50703544081c03488540c0c4611f4401181441c0c40c03500b4202d03804109007040c0580150740c0c1c0d40100b007014a082c0d0b01d1030038594a046540c0a5105803031140c600c420300400040091003442c1d00107220104108042c00d00400055002038603009014a00b181c035041c0c1c050040c424080804e283d480c01e050428002d1150b0000e81d9401080720038142044c4080500109583ca02107100f040e0314800b60401400411650500c0c66069070340d4925030503494000b604040021403890408000c1d281150890101e04203100c0325401071910036000103101110104082c0f00140d4641d490340109002180540e083c050915840c800041c00e60b02c0c80840000c2450405043c030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 273127832 1250 273126582 273126593
    0x714030307020621130b0f04120c0809060304060e1b06040509040318030803010510030e0a0803061c08090f040e0d0806032b0207061409041509290a03 66
    0x481181d0390440c1d00c0d0b40e5039a40900f641c6124030021413040101c0012608001000c5d0900c990040541c0c040c00039021156904204440b80d414200d800816414941080307000d030f54000d10070b800c4801d00c540d84c00e5042246040100d0b12a0b00101e409039955600d41c02e982d004001c0c03d200b10301065281103454a015195400480c210b0b00c100d00c59540143c201c00c0004040c14443d05c01e00850700301d0350780844d50490352805c00c0f4080350028050039204820f2603a03a1100c8a000340305000101c005140030b40b00c2c0f11515164042c19410082c00c1c180c11540034440300c5c0c04000907400c9460103911074194280c80759413840c1404202401c03c20500c1c003403850400d154413030900000d04242c150380b0501c2c00b01e40360b586500100b0706202120745400940c00749900720f03008401c1750200044250500303600b00c07840b10399205003c458442c0c684002c404462400c1110451504040d00141f101402685038038002135a19821541100c40c40084101800d100c1c0b20044800c000029031101c4890b02190008039503810364455 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 273129082 1250 273127832 273127837
    0x6210603190f0204020f07050a0c081f0c05070c06020d03060905091c05160302241015090f060e1908030d051e0106231812010e01020d06030507140303 66
    0x2802107038a020300c08003156520703011111078a804030046c0703441d0307070403881d00130386d5039a0211041300d0307501d070704407010941d8200050312071030a540a201816a1000c41c0c0403580051158041100802100704101004103021400401c0100001e60050110010381e010040c11a43d00350032204a040c200010310000100c0000c004080100d41c1d20b5454403199181c40513240e03032180a00003a429181c0200003c14103801080b0072002c042c9010b00100802c0701001e080d180701e60200c0e4000403112030300d1000d00210000d44041c08025209013811440381d902c0c0c1130302100d52071103640b2146c00184c5006119110341454440e66070600d10700700b140288103041100c0c1d140c5070300606041004807652200080c08021841507503d0151400300600055544c45401c01011401c000800c1403c1da000d0054002c0550360900c100e4a8948144005040145e00700c0200300341c0c3d40e000e0900030386540d29160020700402003171004010752060b44100180c0581395140a90800c1d07042d6120081030a00e58020000c152804000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 273130332 1250 273129082 273129133
    0xc170f0403080a0c060f0204080708060f04030c0c080106091a0d0203060c090402130b0c0d020606030c010804230309040f06180207020d05010c0c140d270506210603 72
    0x60b8143c452004000480e2143c00c09140900481d0500e10020041c07040e65008005555a0001740c0d00041d44481c40f456075208180e58082030300c0602e10003e40800c0c440c1c43e91928031031142d10807080c10380c0d49081b010b094407401c1c4c02c4011020f0b621140d40e58116030b60000780b090b0241c00d031561303000700c86241c0020787c46103401004071045078400a04610141e40750b0341141c174207010f1036640f080c50644a2007160465001340b000c1e40032511600652481c80780c00010002e00c40d05004005041c0c0c10030010044400d0b1324040d00407501c0c2d0480c0300e120000c416043c0720301040281243c2c020b644a003144001c1105a40c01442c0610805141060910015007002c007007203a2480070300800f60f554080740c0702150070038090100c05070540d46040702d80908c07940e2002a0005c1a405101c8601c000b0700c203404230588076204040050702003400300403c010622031550030b01c1000807030455103221466a60020841c140d102d60b00800040b0461030342100c2121021103143e0300048203400030f0200d0f004442140456482092 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 273131582 1250 273130332 273130343
    0x181003150906020f1809090a02010c031103031503331315090b010e0f04140106090c0c060606140f0c0319120507080610050d110301060c170f0403 64
    0x4a5998003403500044001c9602032401c41d0344a92904202c550b6070040c143d251004451032582412919020026a00404d66170340680000f504039801591564038050040b0144100a20b03801e85082d02030002d14451340d000000355500384c0d61441010704041c01d201c0148095000300a4030480380030314661219079034a030740c0000b850740d840d41080c00305021102200184082d942803485040d808064014820303036841444114001d907200c5180d12032090b0200c600448103101e050000d00803456082600b40703203690090000803c03035119440d030340545207110f44000100da5045440c0d810080d0702d2007240010045845d12988881c0b40e4109212588240c1200941c161004039080309400c03020f00485008071542d48003a0480d40484101400360240140003507849841c11f0005201c05000c1e008152203014010481c0c442c010032034100b547c1c3c90300240c2c205524280c1c0e41c0d925203000c0d40100000e41c0a009240c0301c41054405c0341c5401c0c0c0d001c0f20324401c0f00d103017000107021041c0f1107da0b41d005d03102961717800b9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 273132832 1250 273131582 273131603
    0x7050405091005090304060305130206090d032001020403150203100303180e0f0403020d080702030306042703180f031128031b0b04050a0b0a050412030e181003 70
    0x1001e040d880e0541655400390310030715041c01d00c040458008010b00c2100d40c0c544003032210781d85410450040c00d04c101d1001c3e40000e0100541102444d0200650307100038400c0c01e0000310006110401001d503c2e40700065001a0340c001410300922180440c0d0410204496030309520318502150107903180030f2070380f00c0101400720710204000030804000c0d4040150400352240e034810f140034446800d40301c5064070190094000c014618080c1c0e80f19180030fa10a007070540080d45181c40d4801848010024004d06158000242c16130121910801b103e5400e00c1c0d020742d9480b18a02000da000012050003948483d90000d42c4140800000b11b059283c600d100c0030450f07245c5c160340d0000403041d90342501d1030504881d1180030040072080180444084a003800803070b10400c01d01d42c6540182c0041d108500580c0c0d0701c0540b44500300503024401008207081c2e0041e240660030542d40f903031840004207110900702c1c086548141c450381c140c14141203c4c048240000701d0840c190901c0d40c0011101d03a800e00001e40042c020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 273134082 1250 273132832 273132841
    0x30a1202032a0d05040f210807050901050c060a24030b040308150301151503020f0301170c090117060f130308180d02062719020d141c03020a0207050405 67
    0x20509603559003008007024095454240f920b00020b44400100711f860f403888810604080c20301c5080e010340f505040d00c404c1015105d0718420344d01c0350000f8004604100d0104151418200180051030042c0020440424a0207610b160780e6000310004041031036009070700307900304007050314040d0076a0440e42504040c4059114140c90202c01c03501000340c1034140d801c00301c0035149030032519117020440c4d24a1840c1e855416803410200d01386e12402007080b014000902c0180140100030900112000282088034002c050003404600e00704802d80c0402e909220f59100401c44240910005038003411380b040000144c6409241c2c2c0b0315003c1d101030060100b0080d08005401d200c0140b00e00410300c05003204580280c62000070003941c0d00030880c1e000816004084000703201c1c910000d6000e6a4030794080151641103540c03050002c0381944034009a0348042c0130152440400c03112194007103050644400360041e40400340d001000703c0100b05410301007520400c88084030550200700c090580e40c00711030200d025210f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 273135332 1250 273134082 273134161
    0x216150c20061207030b01020d0903021c1a0103050124120203010f06120c08060f060d061104090e0f0a021509010e0414010602070b030708010905180f030a120203 71
    0x14110401da03045080042c46400d48850005020701c10308840d6400c0c00080e2801004989403541c50100c9400b05000c800140014070b021443e41c3e03c51441e10344900706140103038a0360003030101c840020500d89903902006009121007801000303c000701100c40c11000b164010416180007000e4810381e815141018a9601195401c0d0410824209a004240400c40d1a0440d45080c3c02c1d03440c10488030700080d0b810001da8403070045a41c502c5078120b200000741c0f80c0d0700d80b801c1c0b2008030310143c01200d03603581d075890030002d0510040c094400f400c14800005400407020f00e421b4500101c08400c02100c0d848810490010303582d60902c4034103030385103040d019125100707d030040e26041481500140c3c00b0341081c0f200a80c8c1c00b842d650b8141202c02960850300d48941e5120000c0c1c6034442a1000b00000f0307500f000501c4840f1094015903040307103100e8150601d8624080c286410310100d20a000c0031070f0400034002c810954042c0414401c0c6000180071450350914000d0560340f0314100741d200188404034840c40c1a50315 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 273136582 1250 273135332 273135383
    0x4240b040303120c051c05071808190f0b090606010f030516031a060f0304020a05090f040f24050103140c010e040b010c150603021309021003110c010c0216150c 70
    0x806c4c4058041c40c03141841c080003134641295080c000680b0400c0d010011070403030030400220f55240c0c024001c8190765040c0f070540041810700c155600c0007044503c130002500d10014034803840800b40640b4640c00d0840c001040581020100f000301818a401e00c10a00c4249800c0900c10360a4180003c1d04940308042c8585d46c00c0440b40c2070343c408408643c220441c400071004500c154400c4500b2419141c551081041414044e1611402c060480e0006800a4200070044403524014034582c1c441500040362803c503205d001300e0182100e519003004200b0000000c40c00003031807907040058810800750500003003904180b029094469912034001000d641d0165054a20480c3c200300d24004000102c01490068030552204a0007000441e01c0c1043c1d1030903c1c81600081a8010491001d6402d00b0300100c01803d004800151007000420039000a403409100e681c001e040e55401a05902c06092445804a54164051100301c440d4044031449030b588102c180c2003075584920b12012041d00091500c0501 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 273137832 1250 273136582 273136597
    0x301080d03021213032003030405150f0f0606310602071503111204031d0d02010e040b0f060a030b0a0b030103170c0a0609030306210c06120b04240b040303120c05 71
    0x740700c450980100f6200107c002c41c45103028000301d516260b140a6018443d00c0211040d2800360075160204881d01d4004666036040f103401410305007031100c0309000c02501070001c03140940150030003650003201d030000a16800280768500282c00414a410700000c0010804440300040643e1080348282000c804001d4407070442201c0c1d4a1407280c82c0a14015003407502c03900d000e404420040300c48500c00d140c1500303a400300c1541a03507035070803003a00c45092101410f501c40391740b60b00810300d209950306500c1d031001a00b4000c1c0141c0d0040fa041000380d007404066034260700550402c0f00200014030200d07980c2114090100a400751003565010f0441d0000d007460707405200200110700341201034040c1507054020400b500e8110710b401401c0d00300315200810301200c0b000700070903540300c80308200402401103500b00b101ca13141e0b400100d45007000000040441c0d0f08000221712451400501c03072080b01c0c1109000b000360001d020102e20303141c21a00d010302103041021814800607110b0482c02c201a1003601500c002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 273139082 1250 273137832 273137867
    0x1306200304053304050310020310060e0433170303040b090703052505010206040c0311010513180b03030a1704030c06090323040f03060b041b050301080d0302121303 72
    0x2800301c2402d03a851640d104d8441d4501c684150624070145401d81d01c02c0301d0150078501e250144051030840143c440c14503403a0500d5029540d0301d00c080304c0c480202011a00f07c2003003610440c0c201007140100995020b180c00c0403081c407064001c000c2c820003001044941081e00041000840c0d500c2054030b80c9010f01d9900003c005004c4d81c10303d50300303d500300c0b145400b8042c405010000c03010788030300049030340e201c1c2180c010384444d039042410804288540c1302d980d420541031528915168006216a1120030079910991075a4844200c2d242c00207000d1140016a5008a000c0c62502050080c01000140c08240c0450107400a0010404040c041c41710300102c2940098180201c901030305018041c85100c5d0b880070390390695454240c0320540c14904039416142412502d4071a207040d9159079004040ca42111900aa40c800c1110840c00b4140c0409005442c1961419520340c103000e030450503c030000a884090500600190a58111060703000b5802041c0740b0365101d402c042800c044582034414010500d2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 273140332 1250 273139082 273139159
    0x601060f030b0918010e1e0c09060904060c0909020f0c010b0607080316020109060507020606030606060c100e03040803070f1505010b0d02090103090813030308090601080618070902130620030405 85
    0xb84041c8003400c0c0c00d00440204199103441e42012300f4450007881c00c80702d0a0f07002c8140c40003c0c001907419480b0380382c1901246881c80615495008003c00c03607102d084404072103a00820000e901e041e090191a0354104261005401c046880d915a0b0480c0405070060641d1246044407000d2180300358840c408854010f03806114a040110700030307480300d80607621140a0f0081c0c2c40080c107542030510440d11481e01d17600c0289521034912501c0c00003410b0f1010a110382d03000030040003445000c200090800f4a00842c014141d240c194a4091441098401d01c00150307800d041c0100001c420a00035119450300440e00580c0d02d0120300d00480c0100507280004080140210750a8002c40468074854203483c42074540c10419110402900d940348400d00c1010a65070090b0b0004118000320091100004188811109060303120380281080c1c0e081040213000080036800c04001c42c07580540c00301507010008000351080c2503c042ca8035100e1146003d1a030048100e1507910060702d68010041008200c244034940 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 273141582 1250 273140332 273140353
    0x50c03070b0c0c040e1b0d021002011b030516030515040617070902070b060f031c03020a0906030e0c1005090603010e04111f0c061d0601060f030b0918010e 68
    0x1600c68105081d50b810500c01c003d1540c0460802d481034607151100700c0010000304800e07030080e908202203e000d61350011640c44001d401a150341d00e9028460607584c0001c200460043e02d0056030407804a28041094106020f12003646c400003904010301c0b1461501184507a901d44410b00200d9800d40519005413428030009a030112480d0040c41d0b9061040540d02003130ba46888107016130050070030180407010140049841440c01012444031880d0190a440c64514091460194039034482c6290000c650005005c550860340016200042c0010b030038100002c61007003080c0b5599102152080780210100d0910102250040003550f003c640002c003007680e41d6071075020b440002001514201c50040c10002c1d114154039145a6180720103111140464100f40003441c2102c9030018040180e811954410941e0844640e000340d02281c1d94100d4000c0c1002e51610000401c044604d020340000c02d403030240e6000c2e00b6625040c4041e001010758503031090340c5451145a900404840f40110f0071841450601c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 273142832 1250 273141582 273141599
    0x220606080d0e01020705030a021e030c03030d020c010606091d060102070f030c09050f04021815060712090806011a07080d090c090b3a0203070b040e0a27050c0307 71
    0x35107030b080a0703098902c200c0d038401c180741c0e54030030912000394008200c80d0300140c0c114110000c034004103802012550105008400320381594000100000310310340008c0c0458000100b4040c0a00904440c0361040c2c1140c41c010703201030000c1d000444000c07001c0c201008241543c1c400c1006070050301000c40d11850042d503d03d0301c86c1c80b00c0040c4c071801c40140e090100003250800c203403015520641d009801c40721a0308a194200d640640c000b003006007803515106043d0034030345a0b4400303030000030b10424a400c480b113801c01c0041c0c039881d01548052080d45c400e00c0180321011b1000b41001d46240d6090302c0a48404081c5009480c130700402584446d814588619102804100002201140d82101007044502c1e036810611001d011030700c140e0040300c22207040b50600c5011444554a91680d40001c0030f91040c0c0540c0081c0c20820564400100c6140104060140000d008001900140510000c100d4070342005130320300741c00b420901c402005031421a070f03c005020052140b5004100014242d80f0500d03281e0218 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 273144082 1250 273142832 273142847
    0x1709070905090f0a0803041a0a1a030109020a15050708031512030c070501080a090f03021015080606010c03090f0e0106090b031005060c0705180403030c08220606080d 73
    0x14150000d0601c008190610b0002c034058044600440c05001020001d0300d42c4001540080c0003143c2e503460f66103041c110316580c00280790042e80360f000d0105180e95980c1c001090a5845101c00703101e649000f54950050343c41c504c14400725494101d15a140f51102c1070103072068066003034043c00c189000410490030003003103a11150124400c4501d0602d10284c0c03400250b07240650654203106070300151090000c4d6028855056000c410740c4404248001d0300d42d81c40e900212514021809030340400303d04200b0820785d0180000f04480b840b003002d121071420b141543d45100152066060141c00c817210f100389445203c40b00701510030b0000c10411150b98643c3c551a010003403181c00c0018103140004501c088002088034000c07a4094420785a40d0f00740010080c4581c0aa40c40702854440c1541c0021941c40f20035000914030128000c4a2507890241000b8043d80e2815810000b0480d154082040180b90240003085020491580c40d91010191404500415103608005040d10690344c0020019610404 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 273145332 1250 273144082 273144089
    0xc1e2103070c1d040b060d020402070b010329060d050f0706020a03020c010f020312060310060801020409050603010204030c031502040e01080606120c060702010c0503090a1d060a03030c06050601170907 88
    0x40c0c0314001540c0d00c60340f104584419000351840703c64140032a010030400140503400400042ca145501c22441d40002c04a9020201c1101e4034a413481c0100141f201c6030014a0080300b0403c0c8000000c146801000d0f20103800400c981d00c82c0d0380c40d2104505200b41080074020040c41c000c02c44000d07640300c0c64041d685135502c980460051240014030000c1e548907850385684a000d40e00218202014005510000c078401880e01d501841403004501c507404481c090800186551000141d9641c20401101d09a803801004a4000e0f801040108002244040d0280443e17402c904141040c556a20b00c0c0006403007a40e101888101000c00007181e24100882d565000740c90480e280c032005401c08000d151282c0000c445940d0000c424090f04025500610255250b6842102903d00c5c0c1a460400200c283c003150b0030160519152865410f814015650402d410103002c0318101503192450350028240c1e900b4600c01000145c49402041c02c0e40d005440c1c0807840306507282100b4091406111159944004d8030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 273146582 1250 273145332 273145343
    0x150402312c01051c120c0611041e050303030c0f04030606090b04050f0105090c210709050a060c0b04060f090f080c1501120b07110109050a0201110c1e210307 69
    0x4000282c54034151481c24035200c00080b00e103d4042d03d0b6151008000245000702040c4140c1941000001c7d0340d0388503507800e9885207259103858900745410340718200c542610f84480640c00007810300c01c42d60000207072648a04c401002d95a102e08440c4000210702030390b4001820103042000101e88040c0c1500030245d2003005490810050b43c40c0551400440c10038032a0302e42080e0350a01003a00240c0c40d100a0a482c3d0032418800076020100060340b0401508a500c40c0005003140c20502032854170316158001403545e40b50444418100c4e455901c0c4a40020b0b100400981c1d551022000c00007554210411030758000717040000e1799203541818841d07507201c8000018036006009120440702200c2c80b015041e02c04046046854281a03a510192400c020b001c0f0424004c15002e840940d600034041d00000c944200003501e4546c695200250811000c0c501250840c0c01050644070152202c5200b07403042e2481c806c4100b980706540f80400e05503181041d03900d049848880f24454081000002444510300c01d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 273147832 1250 273146582 273146669
    0x30305040e0705281b0605010611060405030f0711030a0303090c1d010902070c0e01141008091f0605030d091802030721111215040231 59
    0x194021183c038890100307141d1403407244011160808403005810034040140e820300c8803443c00e404180e4101542d403608119851a120380062161640c0803021010310070110f00101f00c03d017060740d9125128000c416400c001410080340000a200d04502080301d0310f40c0203000d81f03503a08110b0038010040d2450510540d8640701d0070341c0c0060160182c3c554012405515200c008c802d908008800010350300204040c0c9602802000c0415054288281a0300800f8075500c4134010b8050141440b0089905191480c14085818200024003002240341e81008500c030170041c511641d00340003000100050341149400d4410740c400b0f0205903400142600139541d48980300c1441410b200c40000a9200485134000002d103841040c46500c3c0d129000506160f4580300c011510403e43c203e860310b15002080f0415002c401e0005000e82480301c809038861500c03003901c0944c50f2160409090400414001807100e40c01072041405400d401503984100140c0000400d510940403400d407008103180b42103402103402c5e03200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 273149082 1250 273147832 273147841
    0xe10051f020f0730050105010f08060a05010509040308090f010c02010914070305030403031409030a060219020a110111030f03131202011a060a020a061d07210b070207030c030305040e 80
    0x1102021035101443c00890b0001801a8140c8444c04420031213000d611070000c40b00242c004c1c010280a4104075050102041c0b030002a0307440e01c1405000414100e2800303006001d141c035000485540941c15043c0031080ea110030098038030300700c0043c0d078801c440e5103046010221942d044d0040304215005032a042190000854082e44480c4039210007400750f8410002040041d000d45480301c03454424503003803401c01d032005000c2400d000b20f100b4200c07107169000034005c0c541450306464030941c0456100a00820407165241000e00d10380032b0856040c40b040491121108404100b1205803c000c1541e0a890b81048883c9800b030850a00c01150454100006401d040c1e00c1441160b03c00241c0b01e03030b5900b04141e011300303020321139109032002001c40c0070b51850b980c049401c602502d0320201c0c10500710303800036111100c1d05040504a410510021950440c18080c450003c0d807201c1400c2c1d00080f01c0e00983e158507030160300c0c1c1901030348000c1503486503000c00014107800c00090021904902000541e82d0344 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 273150332 1250 273149082 273149113
    0x301090c17070b030a090c150302040911030402030c041104051f02060c0309070b0f040506030403110105011a030408090a08060405010606020d0309050d14091305060307080a020a0e10051f02 83
    0x301030103002c20520f010b00c00207588402036003008824034040e202c031134903054580d1000f2180108400804001c0380d00000d0821201f100c5104030000d900721440490704605080d4002602d40b14803245d00e500c2552601e1706010141c80341d4084070002c2c40d0041203210005070385801000c11540c4c482e032400c0076009a03800a0348100001c02224411214480a441c600d800e010910f442d50704442c003556000d00080c0300100312904c03890000c500860203030f00e94294000741e01e580c150035600160486440128400038018107401180142d0760810391090f00c198840b00c4580100e402c450403980841c03400c0c4542024001801410740c0a4010744581e070342640e10885c000101030b0213464007940002e01c540e101140c2e0b40741e0548141051004403402501152901541704001401c5181107440240790395690010b01c07089140170410780c00240740c900e000e0700c0b20003403603000500a50a607104140580c07074494002070030440c9200108003e400001c009500c00d0312182c1c201c0040303e185042c86809481400100002c420 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 273151582 1250 273150332 273150343
    0xc020d06050a0f0e4b012d0615020703030309051c0f230304080a0e3d080105130e031303060c170c0a030902180f220b060f0301090c17 59
    0x541d070b1074100150b4600d070030000c1d005c40c3c0721103104502550384a000448401901c00701d040300070340e410a0301c00c441e214040380c04222002503204607465a10101c441003016004200c5a04903a05802c0000d80c82ca03180c1802d0742001e119074012a02149490415a40c20380c005609080b4000240d4901d2188410740d0686e95446442401d44907540405000040002e4518001400d03002100d2816442c80c54080021811070704004114100a2a00c601c0208003c42c2d02c50340d003005e500341d03000014542e84801c00080c120031418040c050081c1503a10f00c1c041c111910342c2040e6800c1d18030030100c96a403001c20290036810545800201d030000d042c0040f41c1d04042c420400e00c03150030601f0f81d59011075182d05840c00080d40c84003056509058580726001c0140e603a4684500e025140c528a1040c98038000c03164646803100141410b04034000346c3c0381044820701c1c04100d4a066907000040e2a07803526902e000a500d0304502c0c0542e03030305600b00072503030040020000104088a00d0102180908442400307816202d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 273152832 1250 273151582 273151663
    0x2031c0f08011221030f0507091e121205130e0f0c032502012304050105010f0303050706110d0f06080606010201181106070209090f07060c020d06050a0f0e 68
    0x110183d9070307070441500c0d080110304040001400c0003e50340c0506c01c00003007514000c071010b1011800d1902c3c01c2200c00719103404d0b01c1100c215030303030f480910300d007044285042800e20001c040d103016400c46050780c50900860440e40381d203d46091802003541d4400c074100686004035120f041071120040400d0410410009a90290380c3c01155640c903c08200075107545100e80c084214215920740050310084e44606400403003003c400c0c08074401034942402c0403400d50300180c0c8500403015200c0130810100381e101c6c05680340203070f200001154122860011002c00e001d00c0c1010501e41c1d2818142c044c0b00940fa500085c103d402c80c0302545c01c25901c1200681c201d95403103a4503089a240c41d250761001540f0000040029040100320ba414030810303401150446c00102c810b0450ba034811405801840c0c0104003443c0201140e181140240300d09038081407408041d180300824090300c4102003498030703035150400201580c03042d20030403841c009010041c4d13440400c8040c02040340035901c3e220001142c10a68001300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 273154082 1250 273152832 273152843
    0x1c1112070e0301020409090501050a0b1c031d0604090207031205070504140d050a050a0c140618030c030f010221010b0301060503070c05060709050117070807030902031c0f080112 78
    0x250351540800e80345150034081450703041d5420480820a18490311881801900820001480b441c01c0b2004100f00c9040441880c0300d01641c095403045041c400e42d014002e01e0f030600d01152070301c1c1d404403250b2040c0c070107060381c030b034000d001007004180f51f5529805014494040e17501d0344070445008415204413134040d2001f0b80060000c0000303000380c1e800c44100720000d0202800c90580450980c0742c0d00d003400e480360001c80789900041985414010080103d40c081c1aa8070015801a480700001500398411411061040b440011100180d40d4003031089011711400a400d4500450075040080d0003940701000994001d40e50045100f10031003201101810f0715140c405003032460342461800e45040c1c000415180801011b01c1d69200000d5051045a0003018107844240c001811b000014000b4800329804c03140030b01080e800c000c0c82030382c41024250044407605001400b0211400030a0801ca2450200003480031034aa0f08450b00b50b0040e41c8848030300055a0b03040040e6224800440001701c42d4501410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 273155332 1250 273154082 273154117
    0xf051507080f1b1e070611070212010e03030a0e01140414010c05040503030a03020c07030c031b0b090108060907020a0602070506060a080d020601030206280305010501020f0d2a081c11 80
    0x46260034138050712520f0344400502c2c1d00700800f039914202625482642d50607140004101c03c021410440541090088082c00a0102c040107951560362400000c040100c055219080c3d002c010360b081d03000c00540a40740e01c1d4541c4500e0942840c807010700b02c2000205440d840c115000300441d10809c1a40c0690f030009024600d00a01203800301c1c065004074621000c14000c4e400c1c0000080c00c3e000888008603c80c00381449024008607801c040c0705040c1c1e0017440404001c0202424581c2d1043d8840d0b8042c101703c507002d030680c85083c4220724109141500510300b500c00078024003800b400203400d51040d001100d0030b0301c04a4035041034079110400c1445000140e48004014030040c0762840103020980711440c51101d144025110308422800404100300c04aa40d0300018801940c1c1030140699400303000008060445807104010701c0250000d50718203054103010408040000e030711550480707141d001403100d6104c1c81c031440116031112a40c40007142c134a180c44440211024240c0559602c0c17483e0000442 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 273156582 1250 273155332 273155347
    0x1020c04050406020f0418050105040902240c120403061a030a0602161707020306013002031002041d0901060b04090e0c19061106010f030f051507080f1b 67
    0x50000500103d42642d0240003050307000d181c0c04040d00081c03208548850300003e0a444800494906800080c083c0703082a510b0005a25061003104030108100074007500d2034601d48451100d8003602200110501a07000700c0381e0490022006481503074000c440400491103040c082412503200001182d400d90400132000c0085461b07a07024018040b85030032a5031075010300e940c40005007402011034500c00c1c08049203000035030504020450240c040d11001020b1140c4c601072031600035a040d8400d030401c0038100e1040c6c003151000c2c408803c104450100540d1101c1d107030200407200c2a001c8001e409107a19080001d40b80c0041401048216100303c00c0f82440c190030f0562280244c85807500341d18881c460800030000e01d8880b014012700501c0000f03007800074a4144070004012110350b1507030144a03440140140869103c1701c1c010822030f548020b405040f420145401341c00c04810328001c2602d42c8104080040182d00404082c1c40f07030780c48400080680d5941a0215a0f014211200c000c0c044018000320 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 273157832 1250 273156582 273156589
    0x1090201140d060522050a0603170a0e0d080307080702012705030903070b03070201060b0702060a080601091703030402012d0e0a0f08010603060e1203040b0a0902060a08060906030a0201020c 83
    0x1c004401c800b031808111a5180e601090350310b100c514461140f0341101c0c804d92030300100c84c4502a04254040004d020a52441d00c420402d065039400c810420100050540c101c075025031503044c81c8060252602074582814280580c03030390011250303640401c40060000c0c000c0361041c82499003240d2100c152060107003413290075864a14a40008955900c41000060420340d01008480001c0209401c00340c1e403460081d01c0242590200d511116584a0a00000f401642d0b00c0301641c210014614040d9150741e5500e004844d504520f5100e008808032104104800f00d80c080001c41c4914000c3e25003c1c2040301d41244500103903254a04c0082c02d00d080030760f621010b44600801e00200340001c0c05004d03040d4030740c1100c20300600700e58041c05460b07546410400c108002401007001c44100180600300c1212084440441d600c801040140542d001e04001000b8114a42c0080c00d0700d038003d03040a4403004520405040704074195100e6120b0010000051803506c2d001401a0039150306034042c006c004901c0c0c052 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 273159082 1250 273157832 273157837
    0x5121504060f140f0405010b0f130507180806060108010f0521010f0f051b0a0f0f02030d050703140108061b0702030c030f03071a010e01180e0607200109020114 70
    0x2c803500c401640d0610550500101e002c0d00821100d184181420f00d015401c540c040b0342007600604255a45000c03e588a040141d0b4100000402003015a12400b0403241c2e0304510241425441c200c0c1f1010078000c0c800a00248149000e803035584869880d040900c054404a2055941c400d4141115480c095002c02900800801c4400003107001d4a1180041c01542c17480b0751000c08880c0d9580c1040300650b800e118050294400740141032528011190040810104080c0c000c2401000a00700940034401c100302d850208c01e2000c1004141025403004010f0045100c2d6809003400e244000310754031a01050707203402146100000780090644a106c00c80a400840081c0d0740b40c062111451000d840070b110614440600c0f43c041c60f0b680d0744601e0710354995100d01003400904042c400050103903034444118681540c0e010b0b00c41031007007440441e419001d0203400e0500302050041100b804403180d0408602a40100318a1600303c0a6420888540c00c0b03511640000c0d001424891070030885503282c200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 273160332 1250 273159082 273159101
    0x50f190e011103150102070509070503132a080c120d0e240304050d0c0c0506090429130203040b06010e0a030f030c03030b010c0b010510051c060512150406 68
    0x4241c16081400d900b15541007158440100c516801c55002c2c10760f4180079080c0644801c5904002a00f05010000c0c46400010a255041e40010081006000d42c0c540c2103144951001400001c850b6003161180540c2580e10402d00f4074444c2c0c0c0a05011481d0902d559030403084600018102200b450750100c0d21150401081d6400000707050400003d800500b4a142c500840001041d070f036810603261280c5001041282e090401c070b803003200c5000041c0302420f400110341c0100c8500381c4440c10000043d0042024500d251017042440c03e00c04a80d4a800b40c0c0d1121111044078a400c140080061080c16131104850040c87c1c8902140004e0081d8056600255440350182c4200c0300309890380e84040304401005400ea0100c1c840415000401d0351500502c240241f0030300c0c0c00010030240b40d46920004506002e00e5104811420340703408864400c1d000d4500300f040701c410b00b40c002c1d92002c02e04001407406024180c060f1300100e8401600b66000140c10721070740002c1d054980d1b669034603190340b00148403402 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 273161582 1250 273160332 273160361
    0xb0c0d0207020415030c1a09151b0d080c121303050705030403050a0209060f030d030b2b05061e040321090305030f0a0b060703050c0a020d0305040603050f19 69
    0xa070015803103038810304100d070180003c41d112650075800d0181101d803242e44804404001f401c4041500180d00040ea13a81010a86122038480d003101d0b100c0d01d460289141d1038022180310300440b04072501c006910403071458291554441c540300d40442c0340c2184648110b06088042c00c1c0007050b000703032030744000180c1c0c54001c2c07030414182083c030f1740c0f05401c50344180d04c19076056110300807150940ca004510550045d90445d8112044084440400e441c1d1074201000300500d075440b092070056071501141a04804440109201d15500029108960b1417054034140c2d494483d5070b0000f0200d910113944034041c0e100c4540340100a9841d903030f0071504d12041c0008058034040c0500d4002c0b881040b0300881070261b20a403113941d2a450181d000721035540b00144485c61407818840c0c000b150392142800c1700c1c1000d13050f1503e107560303030125000107140040d19a0001e4021207002c0c0035005140c2c0c0103001e8002d8902a55050105483c1c10100f120405400d50344a00060f5404440b4080b09507544e001c00317110442503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 273162832 1250 273161582 273161587
    0x30702120709060f1401020a02131a1003020a0e030a0b0c0a020127020f010f1209020d020306010e04051506130c0315081f11031302010c05011802120a0b0c0d02 70
    0x29400c12081c3c036110341c05040d0400880c0b0301881100403480010408807000e10040100c13803d6500018000404c0444d00003940d50388485005489100001a01d18440041d1000b5902c0b600c00c00018000d40c800c04d12500040c1600c0041c060700e00d03010501e02d032000c3e0088400c00c070700e880d59102c82c0c22681c0440c5009041d507503516030740e0b16501c00c0c107440704100c60b098410104518440c4e00522602415020544c0d0400c01100b1554005541010030750043c400d00c1500005c4401052011811071925480041d46c503205440c000112000c40000c0188100c0c40340c41510052140b0714000c0801c80420b42c0d6065100a0b0340b0080103650760305511600365004549004112140c4001074000b40a100741c11a00f9181c02990345d40724640e100452001400c10740070407c00001c04480d400f81c0c910300000e0003444001015415030403d581c0f04a114209094000f0300801502d0700c0d00d0401c46030410837442c00c0380a040044451855407402090242c031850f00402e10410558480c11426084d910010105214550a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 273164082 1250 273162832 273162839
    0x90903070c060f090b130611031209100e030708040302010509010e18090f0706090902130b1314061206040504060e0a060e07050603010b12190e0303150603090307021207 74
    0x1824900c400520b032645484884814031540108004655013001000407010041d05071441180507401c002c41d000c1c0d241c013100e01840386101c5070440c0700d140200083e04482d003042c0b103001d030000300740c840c4600c99841041100f81c41c0c00720301903100d004010000e00040c00912040000d94010340c001c12038220145052417100c04100002a101103002d40b511030080d40307003403c112024100b00043c42050031000f00801c030709403800e01c00030b051902c1c5000340540940c0204143c1d4200042010039000707452508041500d602e1441100d014441c603500c40c40c82000024031404180342000390443c1d40c442c124040c3e183d50f59584006005c09040c0184c0215a0b072692008006403c11043c01070b60b082600c030301d00104040d09100ea01c6490120107070015446401c0c10001017203001010003c0300c2e0b94a000c0c0c01500d0890345c9502c40740640e441008098152141855a01c2401440100086125040700800350b46150740b24003d0096a0004031039213103440d801040541c01501d08583c0c0c0c20384402075801202e200b03945 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 273165332 1250 273164082 273164093
    0x306030f0f0308070305060a0302150705011415060403170313060216050106090c0516060b19090c03090b0105061b1006030b01061b03030509101118040504020d0209090307 75
    0x2040001aa1280c1c0e01d004003030100b681c032405480d00602d541c134042c401c6082c1400050000b044da440001c2c4143c035000301c061080e0f05440281c64038147c1150003044050540007100250b0340d000c40304c0c601c0001180d40345519030300e410801c2e281566004544070191804c8485813408a070701c0501002c440ca07440d5090b581c0015814001010070040300740ea03202c6005580e00c0c18a00b0b41c1c81580250301d082d0b080c07401c0c5452203540001501d9018400c00b80070900c0000c1410000000e01c4400c40094200003050200b28064050060a004542104208001014009030101c0480706024002813110301010010861440c0c18405400d0028204401406103038460508070710b451240c0300710b040b507552502010024000038030491401062b450400c540500d040341d106002103200000c0080603d9510008151008810812a0f000480429040091102a682c030140e1500005000d1000b5000e03160385e54400c1c2046e0140307500460340500090810384555080000988005001402c1403000b8400303003001c110b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 273166582 1250 273165332 273165353
    0x230904020319030e01180317030601050d06030c03020117090d050f04051309020306182d03030421020a05190602070b01090212010b030906040b0c1e120108010c02190201030603 77
    0x52013a180c11070103940001c005466141c92818050f80003603400003c1000c2064103070010315034590010b09542ea9607842006071030a000d683c030a024103615181000c410080c1030740140069038003d03241d442e0b09548001c54440b003000122403400807900315032108802e1500900c050541802481c180380d04064454000c15001a1016021000e95441e818040c055090921005c0e4001038030400b4021200103080c929580c603c08210000000e10000301b0007042803d0350724000b61464130f11000e032580c9003424240b030301d030140101e240741d6207403503111a20342c0c0c041b03000040e50410b080d44131001d405820000c0c1010750a60540311010368100d5000c0004400203028504d075140a000305030340c0140c859030f00c603510240389070f0141c2250703503207140c10400e109401400003817507a0300c5507000e003403924240c0d5006492a498080c000003040d00e2075480380c1c142c001c1641c03a0081d120001405440000d00c0c6e0380d9412850a9601c10810f400150704001480d500c00085042002c0c0c0040c010304010031026030f265540031200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 273167832 1250 273166582 273166633
    0x120c060204090f09060b03070b07030e060904020c010b13061505030406020f0408070e150a030602030414010c121401050d1b05030d05030906060118050f0114030403020601030308012309040203 84
    0x3c55680030f418040026903c901e00200303a06038000c210282c00d1000c009807034810001c0c0a0b00f840360751620300c2c1b9244d0314001283c0400001910540d101d080840e00c80e8060b090002c045440348254200004441c541445068101e4180220003920303096403050035115544050820380701240c00300301440d50940844020802012460002c2c03400501d00700d84030301c0c040f030003170180e40d403031500d13541c0303480e180d5507025600b1040e66004207006030f40340c03110300d4141d02240e0901c2803500319500b00300c542141030b40c00c00b807030000c0d0804e00d00080c055260003d880c07100852003402400c0e800700d8a40351000100e075007000da081c2c2c041d0881c0e040e640f20580310000280b07040527172030341c400000303100004105041034148003254100800317007131075520101000014140c25a65004813030242c0162080c039501c9030710540320400c2401e40300c42c3c030641c4d90910b07090007525801c00f400203802244004000055007005070b10484204c0c0c0d0440c441c2c0c0203010742ca0080120751030000c0c00990b03241c81840034040004c0010203501510 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 273169082 1250 273167832 273167861
    0x1a0604051e10090806180601260105010b1317341509080c1809160e07020f0a0f02090711100b01091203120b06070c0602061f03120c06020409 62
    0x1490500c45504d490700c002c144e803410346c0e5002003018608400103000f5054400c406004075585082007081c40c280b102d01d01e801c110540c03c0c180005070b1440380b0748c01420800313460004034a01c1a15204220742942440741c001c010b90b80600e60001d6030844208904440e401042200c4003140410303e441d090705080e0f0741101ea506000038500102d0560800680070050110340d010b400075420090008a280c03001d0840301565910420004d000b01d4014010076521011015a0000c490746070140d0b8000060116803010240c4640e400c00d40b0007100c00141d20800325440420040030305500e609210b488030000c0d1440301440a00c9242001000f41070000c4911500205800030350000d101c40010110300d9180d204580040c1c01c61103d5011982c01141a0307202480350402003540420417003c91f1940c0f2034440c010304008001403000c00c06680c0800e2242c0260500050040c00340060305c0015002e030504d100051400107440b81d030b142418010150b2130740e014040d002c01402c0c55038a140701000e6032100d00c0d0030b409 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 273170332 1250 273169082 273169097
    0xa11070b0613090f06050c0c0a0305040806060418060b061204050c03120c030406050f09150316033c2d1109061c060303050702041a0604051e10 63
    0x5003001081a003110b1001c0d0340030720400340d4645400101d09140c1d0750261a031034462000076100f0210704210760241e1103a070115000d006c402d09008010b50454010501c4600811010410503c0c0034017683c548030f039a200c0c00310039929455480c0002450a00d2089420007010311040d80d000201c0c440c1c02d032095000c1c0014060719202c58080608043d0b0300170540070140c40a0100316100fa1000081d00c0c02d480140c100250303914040c03450201580200803005900c04c2c1c0710200510b0301e00314070303015501800d43c18070b81441d0f0450f4050160180ca80c00f014041c0d5013552000302c007003405585040104a100400807005001a14241c1c41099640240361191800000c1c4403220008480904043e0390040c0c011040201401c803031288800b40c803a2401540c030a00c008290b41002e6540c00900d42c000300e400f88020130001b0b51341c0c46c014160740c102010030b030311079031809610401da0741d94132403000c5070040b0080c00da525240c1040c003000221120802285200b00d100c0140382c02c04d8491140341002c0c08200d403079010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 273171582 1250 273170332 273170341
    0x80d05011811090f03010b060309012c030904110d1104170f07090b01022e0c030903140a0903230c010f0c391e0501080f0a11070b 57
    0x200c50100034400e0000d01c42c0b405442800d061541000d6410405044551100c0b092951001901402c1b4000c4002e50195000050091540d015171101060085142c90001c21440300050841c1c00514000148603542007002001307014940755002650790420150350604100c074840c09002259104401d800008100003000c0c4000380c040c00745407008826103001010075003640003800741c03100f04d10321400709015103039180804140c3c02402801d070080040e0396051782404140c0904600c02c0d51164060f01810f00c3c0000b078090180c42070041c40e02c0749803da1030380400c42c0e426043c000d001d03034012440300040285980000c40045c3c40f110702e0642d940e2070501c01070711004038880641c0c1403000e10300c6c020f03061200c0c60300107104d110341206545c008180c2002000c1c00240c01d18101001003907000955103607005443e03403001d0300707860709180103801e944441a20140e1100404002c0e9405240c1d406840d011881d2100040d40420030260b03120343c060921040840c000300000800c900503041140c080704c032180b0060400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 273172832 1250 273171582 273171599
    0x80c030a0309150204061b050a0206192604140708030c03070b01050a0f0e04080f0307020616091404051b120406181101081008121c05150616080d0501 66
    0x83c51440c81c0c0000440c54103180000243c1803000c2c3e044100c0e02040c80d80f1081c428000d00b840840d00954015201c00c2d40c5900e441e000507000310141e4152008108007496002c2d02d081402c00c0c41140000c5101281c2c22915661109041e5024440c003840f114810b41e040070032500c006001400c0d5400c3d00c60029520303400c40d4039140f850650143c01103030103401c480108125030703951401000100d0f4a40e4070a04910344850818001b43d102d40004a03c03510340c00001c1c41101a80042c120348030b19200400d512100103001401caa4100031b6100321006140908034070015450b00398800394100e18801d00f281c04a00c4424030010041d0400e1065030100c1d56054200003d00445002c0c400ca6600c0c00700060840250550701c905241300c482c8101030400200c0c00c00070b070030a107003507031001d0150040c402115901001040300091a5214925022140080d05009000c0217414040d03c1d006500804001c01102d003a072050002c00e410940d00c0084410040c16a00c3c00325519500400c003450b041750b004580c3d03604203440c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 273174082 1250 273172832 273172853
    0x31b0d020a0318030f050f090d0b01050117070e040b0a05030a0c0501080a0e0a0807080d09080301080f0c280f060507110d110111010905010501080d0206071407020d080c030a0309 78
    0x140c81d980f507000c940403002a62058510303200342c070f444c10318607100c4840c00c1d020307245809042c03511a04200d48100c50014002200e050314100c03582641c0d02880c41284008a100b0a002526041301103420200300003902c1c0b4203a0080160100050214550243d030b410000c0e00d000e51460094404a80c072001c140034950b481840e056000214440c107100041114109954995a01501501000010484204200d44142282c440b5152083c0c2441581c5071820185200e900a126544452040703074020a40c490020440603002c03a1300031700e00c1056108100c1b10010058500303502036140f5120741808112001240e5440b1302803c03031f40d511180c4505040c03400300904003041d02500d1107010a111501c001071485041c2300003550b42841c10b243d114022441c0c090140000c1e00b002407440d420440080744482000501c000c80100a9084410076120300c0015a5070041403004840d070711404200c18005401c000404458140c450b049207881c000a0714245411038015244901c0001d8441420b0814849a80394 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 273175332 1250 273174082 273174101
    0x90510091208070807180521010f060e040f061d01090b1b03161e05130f050a090c0216060e01030e010b01021f060f0612060801061a031b0d020a03 64
    0x40540503810324110103410004001c04c61710821641250118444480715004001480d01900f1900d82da844010940c004420030508072483e076180191405401045010b40001c1764841840000e80d500da40c1c40b44902e01c509000c05843e1282c5400d0442c0002070352405511103070198800002c3d5100881c900804500c2000e4a084061207020641100d90001202105e8020124005a40350f10510710f1050f50341028001a010343c0603840101b910840350404000c00c8100d8542d15075180247c0c45500034414812a4010729412080c1c954040c024180c29070b001c00f04141c40c9004a0320b0202c400007046a02940e55086000000d40c54014580103507058010343c10034502050080c04a4400d51000075514904420414550b0404007084045680c01e85e0100740980300d02d09000c86615101c501c003500700d48946041003009450b0a1000803102010310030581500d0290290400d0034170383c003c3d000a15040a08541103802502103202c070ac40c5810310041c544d02c101c01d8400350721a51f840c0b101400715040781c0d1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 273176582 1250 273175332 273175337
    0x90f0803070e01020a1208090c03030406020c040f060e0f0403090302100f02060a060509130215030f07020d0201060305031c14010e0a0e121207050c07030309030b0a0902090f09010905100912 83
    0xe0741c000403021022503846d181c0c58a443c02c61a074580c0c1d1080e1030b25645141e400d4040c0000500403442941c045290000000c0507601800304c505603202d1401143c01605c0ac40c52081d201c2004942c042c00d83c0c04000303411034041c0c500020002e8503a00041d1040c4c201c0b100100105006510740b0904680502c03031254018100b4608018852420000c41d15a9000030b06840c80c0d16881c084170001c46d624441c5840010701c019200c00d031070746000303090346608880c00d035a03070f401611810045040d031a1050040f131080e01c0c0c1c440c0c050350810b11035903004000802c0b2102010142526880b201002112085e100c4d4000c00c14421038002c0d609082400b08100c070000104200c280c3c00121004090008a00880b40c02499030b016500c50f41c0d5501000315100d01848440781103a0045a03400400c2c10341c8100c24005a038001d004050365a101e12107014101c5080d200000d400c6150040000d00d803010b40640190700004030800401d400c1100d617980e40c1804002c110704600955944031707000500c040e003441280101c6003070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 273177832 1250 273176582 273176593
    0x7030606030b0a05090a11041d0c0a0906080414030d0c0813030816031506050702040f0c0c030c050705030a08030108100b0607060509010b0a0b0703020f03090a0612090f0803070e0102 80
    0x82d40450382c4507160f030080b113010349912804152040340c990300c2a80201c1100c48040d49035501c070460090b110095500301c4e1080d1070304c000410200c0d80341030200c410104907900d072140010b00d0100e0542c0d0302d480c0244261454400601041e41042050009000b8040c860600050954040d034014060910160001502e200c1482c14100041e41048a090b005100110014441141d068007100580404203e88901083d4004006081d541080207400014801c44d414000e071b8100d1180d1070100d03606d10000d003002501e0410410040f9005044803d0040e0244003500c0b001030301c038000b181c40d11400700800c0300c903002e00000411071100140f207070008090000c01c050000c031201030001070803030041000c05072030a903440d0702181d80114250321040001d10080c1a8100d002e550b40141c8038203030401802503025001d2512920446075011003140c1c4d204000030f00d0704800d64104007003100d0b04182c02c0010840705942d201c1c460080f40310000d007101290300c505080c0b0759a01d8142e800900f011003e55185041d075011 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 273179082 1250 273177832 273177851
    0x15011a09060301141005191809140a110304030e010c03090e0c0c0f0607022d010c0e0906010e0a091a0a030809030d0819020702010e0d0b0a0e0a0b010303230a03050703060603 76
    0xe02c102900045107624058a450f44900310040b030003091030380109c800510b8440706400802075950326602c11450120100444540035040c0d003050f120459001b40041ea11005140700f80d8041d51261071000e021b4903015800e2522041810041201912003040c407507401b04400045020400003c0202590b0101600c80e40c1001d147c084d5443c50355404200048505620001c405c208501880104120520085c050312030b120801074a001c660384071150144200e9000a5440e5010b4407803014144c1c4050b00905105140c514503000070070782e03001c5200da042031800e0050840d1b82c603124003101450144410590707480e42c2c8410149400c1c1450882401c0c84002d10400060b110020307000e038440b543e490710142c5e84580c2840122111145422010b5000c041013044509005040c10118031130000f10804028030000064007581e03800ca07800b8028054465440140b0000740f01d4003003101d500340c01c803140d085800001031055081e60030400400d00025178a0b800c00844941c14082c820060125080c1080181c11 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 273180332 1250 273179082 273179107
    0x1b091a0402040b0d180b0a0507082815050d0b0a0c090e010b090a090c110d051608090a0e0108010e01110705030720060f07050c010215011a09060301141005 68
    0x24013480510b650341e540015841d03103404240c10038040707903000ea8030340c1d424500f188010008141c25605032000030944c00000705c050082e980006004d0508070a8212400004110407010700251004844c5008507100c000600d40c0320082d080d00c0310703403050030748203058901030000d481140c907500035400420901e80c50400030034101484c924151042c1040442c2d955401d1000300381003148a5101310300547c0751a02841d021030b4081004007000c203203401510420080c100c0300b115940104d90340241560207003410140018495402841550070280112000039510101004014800da00c040101d9450300951818443d00b0720407070f10048816404d0604000468032000d03941d005100780100304500d00340c0301d801e0b502c0c0c0e1004003030180c040003800b80d82c0c0d6070001380342940300350000c0344200c4040c402c3c000380c0e031041c0d800030854440320111071301c440909a10349a00038042c54030780910714015180400c40a80c0c240c030759030011406055100031151388010f6110601000b2096006080708010040c0710b040014075 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 273181582 1250 273180332 273180337
    0x91a070b0103080c07030b13021203090f010809150403020319170103120215100f0f0302180a020715061410081602031902071e0e0406091b091a0402040b 67
    0x290000400c3d9221010440d499282000c04d03000500074410001c10004004104410188030904c242c1d20f803000040c1e0400c00c1a0341c1c1c0100980c00d030340600a0003041714594824141c06038000b0340001161408082d481c0500031204054406800503040042c030714401500c0c0f04900001c4500500d488410320301d5145614200e00018000184080031202002c0311700c502c01c2154001c10586082c0c01240360400c48032000c3d0f540b109200714540e81034403010010b4040c4018080754102c07a00a8001c0760504035011141417031500050a031034003540e003071004c0700114210015040030f03142c0d11440043e180c0e080100103d51203541c02203e5100c0e41c00c001c0300c5406550320a411680010f90310b00f902d400f548081800341e0a50041d418030320300a142c0e0000311040642d00007210801c41e92002c502c114079600b041641e034070628490040c20240e00310a400b0600040d07180c0c0c0142038a0703002d81d01d200c4039455103801200c00910345500405000380c40d606208901b4400e102011031840d0112021072910785810074101460 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 273182832 1250 273181582 273181589
    0x150303090f0f090c0c0611190206220201050d11120105120a021011060c040608090a1a04020f09040b010306050123040e030405030f0f0606061c0f020408030a091a070b01 74
    0x2a92640140400a17000c0c1319141201c070707400030003031140068205001c42a600040d0907014807445002c0440200340c00420824005c00040030a08100b40202c840684400d0804004904112040200c80c544411a120301701c004468540a140e0754a00301c001040c54a006820280c070400a0440c55280d04000058602d200ba50549440300008090b000c00c0d20003641000a15450340a503508108012804000500940d1071a496400e00f540f01c0c182d11070740d5103621400c014819003028408200a1070a00c15055000d4402070a00e01000040800b00c1c000e10303010340c0c040b1440441c80b001801000b125004140c090031842100d0390002800111400500241d100641c1c0503c2d42c800074984400d20502c02c0302c019000181c2102c020140482c0082d95403140760311040118042d400c0415800c3c6801000c030780300e00740d40d410266204a45140b62000810083c0c6003131500ca0750030030000803290010b2018044088464607035038041454403507418096280807440200d030480400c12400064141520507065 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 273184082 1250 273182832 273182849
    0xe09011202041512030e0418080a12020d0c030b03060f060f060306060f13091107030c240618060b040f150e0a0e090d030e06060d03030906150303090f0f 67
    0x211032207000104402d201c5400130440b00303840f15500720626800c086205c0f0841c20940701000045504c10154100d021640c0000384101410800210030038070420900724800b2291800502e0110300d80000e03001c5a100390721800100c0d03159080c0090914007840829400440118001341c145848000551640020741030070340304030300c0407001c1040c0b922900156011403100801781a61410310a0171194581c466108403c0400c0c00d00e651145440c43c0301081e1121203a040e00ca1ba50380a0355070341e400500040321401d840301142d08008400c250b1005014280045c180f8608017092582581201000d5540640200c82d2030341040108101c90503c0304c1d0b901e01102c040441c9010300300c455000c00c80f10402000c01c50780d0f0144402d403000c140c01440c1c1c2011b5025110020440305000b0010506805035000c080382c80c01641c00181c001010303800c2c02d03260581807911034500040d003602695509411202d0f40701d00c0780c030441072811051040641000640014103030301c004004071030340350200301c9480d0300c4d00e4002e03800f4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 273185332 1250 273184082 273184091
    0xf020706050a02030c0a0b160c0807060c030e121902010902030309040b06040e0a02040f170a230a0812100b0415030b0d06090201030f15052115070e0901120204 70
    0x1482d40c401d2050b10710101084081d41c4082100d400c00d0072030701d0000d07180000850103550000740b00360b0044001400c01075005140c142000d015448000c0140712043c0548181510740380040c040d040b0a020000c40c103045036507035640b00c01210300ea181030344054007060015a0314182c45000580c2e4000159081214100c0d0081952310058011884074016948541e480d044d00c182405101c600075005402540c40702c0001d044110350b103a4280c07290220605218409821828080c40451030201c0e20368034694181c1904d40c200d40600940920303000e01e40c9410348806001180d8000c1d0003920000071034001003403c00c0880414282100e90740548a00e10540070307125140340848494038003a8000000d01000141403009080c118188131014024004080340040d05c0d2a061b60004440c030307c03075104a2040c802d0074003181402c1c1001c2c07040400303101110140c0030074400c4104560b1041000300030740300740641900030810b092415019041941021102d80f1905142006102e001f03048108040314540440300845c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 273186582 1250 273185332 273185347
    0x515090d030e1002071406031e04060b060a0915050a02060a0b0a031a07171b0c100c0207080708033109022d0c030a080403180f080d0f02070605 63
    0x11010101c00c64059080140340000c90003413a0041696406c42c4c501c044805020380828003001801d10084035155862407a0a0b030010a141c0c1e00f11307525502c14820040085d0007409d54000a4072074000030100c100103134030341200f44559801e00a103034400700101d042150500e586903402a4903502c000305000c00450340c0e449031007010355402c9580340c01160048408035110784500341c1c20004140480e030150214031038543d9890703060204a0814410202c14900c4241118403034000050f96004840f441d1440c405c00d480000840b0052280c901c40c03c44070340007001c2c041c0c50412900e0902f00300b5403103144160424404d508031400d0b41410314010380c00c10320138007614514690250058004c07541051041910200341c903e1145440c40100e081102e8082580c1091592003d24a04034454411644183d4000340212080c0a00428003107400510034100051500f90000600605a40c076a200004d40d4000d41c20410020505010f020030304081c0b460003610702502114060740e1050140f18080402000203801e4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 273187832 1250 273186582 273186587
    0x1a0f1516050a12030501080f07030c06030b13020c01050402030f030901020d0e0102030c0607020106171b190b0d060315020307020c0123030a02090a06170403050304060f0c0f090515090d03 82
    0x10b9500641c001c015490080601030000c00404090192a903130703104000807100104000910f07001181d0380b0a6001e400241445800c4000e441070b400740c1e80e040b00c1d908030100304541d46800944076140d1040c00001c0c403860203004062030300000f011004480c1e00104480c08050740d010075440303002c9aa60410f412600c25500c0100c0c074520501d0414807040c0a80308c140b110b030030b0f419003081080b180b03d0030044010109501e0100c1d150384d40b07078065603488141410b2840241c00c1c100743c03194030030b0301844083c0c41082c1d460120300b54036031104d81c140c1c1140340e4501003403042103000c2084443e05000c054046086160200c0040d60b0380300c00040351814007844541808505582c8400c040070b00307400e07400c490b4483c245070000c1000f03900300c0ca49a52285a924002103161442424801448403c0307003079442d0715886d2918169003581c0060415075540fa1620300d424100d401038003810070017114950f80c0703041c1d034510050018105421341d00b000d4800c980403009000040541010381e0036070802110701480030605454207 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 273189082 1250 273187832 273187843
    0x60f0b0f1803030703090806070905061b010216030306050102061302030309010c1407060801170a0c06080718030b100f180e01200a03050a1808070203101a0f151605 72
    0xa142c2c0c540b10000381e9000700360303015880804481c030724401c0b6122030300c0e20b80058403052618098a90896422b109411f06813200c008010004040c4400061410351480c0070701203417055a54043d00425150301e810000d5590401109c0d50016910702d0700c07020011198002a00e134030413a00010304110265407102e052000748040c0c7c84121035074101300c4842c10340d41e141c050f080380390921072810203000700c100d40300c81420b000c1800b05071281c0c01f40c6410442c0d8200441510801400380c204420001850090146038098036400009507014480114040c503005980d580d2080141d003207646142d1402c80200312072a00c03603001d1010011400f02c04240500d8003c1110700410a901201c9650b06081c6088a58109030030b000380400000c42d07600340084d03a02c204102042d13a4121185900d60001c2c40060b02c0400c5009014000c2d04e4801810b035100b40188217000d40945440c1e03d000d00200c01c0403008a00603291100c0c1007064202c082d2901d210f50707103000c0003240c028024101d01c1c15146090300d0841d030401009018 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 273190332 1250 273189082 273189127
    0x501050f090405070b0d0f050a0506090129030403051c06080712140703110306090c1507020402120f0a06060c020a05040905100204090f06080a02030601090e0705040e030a0201060f0b0f 81
    0x31510303240c04403029603070068540710711f041304c46030f250902040b5400340078001d143c880d5401909130715580e46000d20040c200d000c003403d0404610700f01d401c40b02c00c50011000440c011030080e07071211344400290f030f03940050040082c80b5540983c9445010060b400303010980c48100d5034000c00415030245241040742181c10203c90580050082c03020100c01c0003201c8918640b00314042d801c5540a80e40d4040150f55110500034040d84010364038034404078048010002e10079948050300250414002d0284840a03c03002d0b43c61a243c141a20100f0414210901c81c2c140145220f10380a540c421507030b0046081200f02d0f01425003c0c54842c550386050240070044800001e44d206000c6603201d680c0d10482005003210b06000180380d00300107000480303410000c1d120314059002005001c03542d1034820940000c01100010307420b01c1c050f5100009190341da901c11040144000400340d0b50301c1c288440000e0071102071703810000b5072174680d000c00d00903268480c0580f03030301c1612064801c2d52080c5540514078034504454 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 273191582 1250 273190332 273190349
    0x610050d0e03190e09040809090c09030a03020d110a0c180b060705060a0b040c0e040e070816080d0306060c0f02040219051216050702060904090203030a11060a0501050f09040507 78
    0x78601050f65032030303961881c2a01e0541e030f0300c82c90f40944800c002c42854141c0d0040d000c810103200c02d0f809403a0007d9196008804032241c14540100f010204e800c102036a8001d8015070042055501716070342102105142c0344650300a0b129101d43c0750341d65002440319010b2011011504200d1203200c003d168004045580002e00701c13905c0d6003040c540103607507404c2100d0750751000c0c5c1000103607042030400303020f001020851910f1310951150404180001403503403000201703c610035001c002800b1081400030102c2427004402d40240207052004c0c40b4035190220314401c00300f518055080040c2039109298a0800f0b521801407841682a400002e010303004401d1034081041c0f940303006681003504900205800a186241c12031641d56038408a00b903007040b601000b000c2a07040262070010724140c3c0c018040d1000c010000240d1250513004a840c40c1c0001c0e0400004c81e440341d440c026884010441e03150301c03040070b62062110b03604110104d68070385108036405025444001c00f0904202080c414900075003000e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 273192832 1250 273191582 273191587
    0x14211806010b09031515151804090f111306091a06030f040b04030c0b0f06011704050606130e032b0507140f1902010606030608060f180a0b0907030c0b030610050d0e03 73
    0x849489640c2c406000b1581e40380c8e03028520306290500303025199410381c1200f02c0d144124403a0f01c64501c0c02e21a25551a8003182032500d0640c40741d211700c02d0038080c105041000070b044040c11081441c20020700b00e110310076501841000200802890f5295200b5804500420a5283c900d015101c002c0004001401c141c2e05c0c0e000c02022104240d900c903c150400d0342c038119030020140702c1044c102016140582190000c80004244ac10182c034000407800040030b0001e2090340d2483d9441c1180c10511080103201d015510100c40d03c802007140010380e02034100100f14500303080d40064542504400564444400840d00300e1900620205844400040085014416a220710b000307008144030301070480864503144000c507a44500080c0540b213103d006002c810117489005502b2a826020302c01094a8803452442030001030036400303040e024868240c0140b80e0981945441c0d440d00c0d4030307a08400000d0206008201c81c980d101042641d4015107428083c0da140001d201c0d401c042c252620000b07440d840b00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 273194082 1250 273192832 273192859
    0x5070314040e100e07020607050a0210020f0901081f0513060305011508120c0c1201020f130e0a020f0a030b01030608070e0417090114211806010b09031515 68
    0x7010020301c034a444106140e40c40b501c41813081d6101e0340503541c200050f40218002001540100010010441a0300441d0000d41454010b81c003607900a00002c44041d1000c2040e0f0003030f5810070a0150040340d03581013010035201640c00701d0019911485038501c00d524202d21024540407691003440559000130090050400c45034a2005248052150340c03650310840038114214018902511150b00800d0086c0c030302106410200514050081072108455508009068201c4080d200400303041103401000c1810318908022940d018000802d04100107004001101d104188002140c84000c200d00b800244048500012002000030f034002e89914441c403d008108501681d01c49131256204444012580f400100b0003003840c01103801e91070100e070040e00391240485070788019003c000e202c0e025511f810f074100345c100111803c003078440d4a8540d01d8810300d205180014810300c0e000d85020032805240c408007901090351040300c10810340d94501c00760041429110519800c6c02e080700020070f086110410b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 273195332 1250 273194082 273194099
    0x512072307030809060c04060f05280906030c03060f061805040e0a0b1303020307080d0f0203010f060305060a06120c051c020a090e130b15041e0c0e060a0507031404 72
    0x30f00f07441203111031254100040814105004a86c02c0d0340c05503807042c1c0007a0302020103681c982c00803004038068010b4103520100c1d4020000156105040b1503852105007440d0403070107001c4440d034150748020103081801c14042110f13494400b90440703c0c1440c00d030340c0c0680005806103010f1031304d0700417560003410081c0f1500321010000309043c415005000d1418540c4a9062540b00f01c00d8000000380540c10502481c0702055442000d045610b0803403d021501004c2807240c44103e038404d82146a100e504100d00303005c82541445016400501901e4810406080c41d0000e0601110610801c034075607103030359443c211075200e981614805c0e049407154605203040300c1004400703500724030341e0705000401c0b4000004504887e0201c1c01e00a030800000c1410030031280d2101070703c03214001c0c201c3e00b80f0b406946c3d0304036035512031303100320204503a900450440d0b542084000700282d07900d81051a080001c60f40280c00a9030f079100071104180502d082082c0d407607215140035a851100e10200120036031010400040d5105c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 273196582 1250 273195332 273195347
    0x5070b0709180501051c1e05060708070e030a020621010f24120207020f09180729031f1707090504120f09080703061407051207230703 59
    0x8016082d25a2414080b81951084503001d01c9081d600c00051201e804450030b9501e40510254000d01c40c1100480c060030002541103100d000869055000108101c00d0341d030b0080369030380c00440c030380780100ba080e14600010f5a50403007a50040e1044400061b08049902c51020b208103c2d0382002d1644803c1d1f0750780b4624103a00e484c5104540c94030f010900444286081da05010040480c182c4600181e040c84c58000c200a401c40715080b84c10062a49160002daa604000184102c090b1405000b0034994002404c1c1820310300d9100140440450520030320390a40d00c564400600f1a000c0100d0700e0b952010401001c01c5010345000002d21005400801c0090006030010b20104d4a042103500260382e440541c0201c0d54122405001c805401034842c2546200e0344c1c41c10810310541c50012211902c610040b0b0510310b0f0791f0b00c120b46a50741d840c2d0104a001032951070030350092041c204142450303105444400f0b00d83c0000d101c00100301101c81350109032070900351461050900e11a8054803441a032402a0101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 273197832 1250 273196582 273196589
    0x2d020604020a05120304030b1909140d020d050703050c0c0a24050703080105100e04050a0f0b030303040308160207090c0c021306080c0d061d011b18060f05070b0709 72
    0xd00e020500810f481c02d0035107124041d01c1c0007500452034140b443e11208404503000c3c0400504104004101407020343c28000c1086040c02070450b40001c1d00000e0059103414054106403055411902207512a40d40080c25282459014140f4550b0340c212114841e08149291000503440b0070100030215200141c3e401d5040181c000100c3c0e00c01c1e1694424090b181406100350040018030680c0051101e400c10401c0c040d206411400c22864030014100090152103007103e0b140e8906641c0c43c644481c940c0d5901480381746003025000b841c50360915460091110100504060101e244000d00303186181c802c05c03900c0010080003100300002c04851700014101d0905060a920900704070401000f0726089104000c11690700c040180b20305500c3c00140070540745c0401c010341d405540e4000d080b080850f96010350b108507201000010796088040410782401c41301c0100642004442440e001341c61040c800540c09403140d5007405051030a00d00e100312010f10030004000d02e41807506040c071201c550481c0c031139801e4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 273199082 1250 273197832 273197839
    0x509060d06060c0314090306010312020a1502031b0708030f130c0b0a110f1b030c1503270a17190e03010e0307030c060203072a050c0a03050c012d02060402 68
    0x40c2c42c0509881c0c801402075040315035042d003022004200080080070103852f512024011b031258056140c0303440194070007070054130140316000010003200300000341c80031000308014200b00d8104503140d21000c945001c002c0c03111080e0800701c004502403a881c40c0d21088195030241164403550344a94803012550414102013000c602c81c500e0f200c17400f460109042c0c14141c207140003000800c0600d40c2655140340348501158140c0039240c0207450644400310100b481c000036450382944c80c01c140b0410701918114821103600540c41c1c0f8941281850003007600c2081941180754455111103411040b403141c0b03c0e0340d00f254104966640940d00e40354216003e00710110b811002008261a50740702c0b240c0740e20501c400200021725240e4520001b405541c083c0d07401c0703011440c2c92403d0f0851600702d400e0584181c0c07640d10400a2f01d10402042110030031210180390300c150f40380d00c070451460341d5103542c0387c51103190141484804124070b143d8002400e01c0c018604081c06150110030b200400c060348071602038030107900 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 273200332 1250 273199082 273199097
    0x3060c09100305060303090d0c080f1f05011d0a0605040e0a11120a141015290406111221090d05040b0f1309020417060c04060509060d06060c03 63
    0x181c1500a00c0ba040c403c07800036010303602d0184500d007088446401c0c45400c03641c83e40500c002040c024070400103c002c0805000c0200720500355607082c183c0300c4003000a09080141010014813001400d0380752200c0c051441406030f01d041e204e01c414a0081c207600c0d002107400c58030b40004401c60240004071030700064040c040000604000005000c8549041c0c148020280d000f200c0120000c3c940a40040c0303e00044070685442d0001ea1030800181c9203400c2c001c0e064201c14050a000c048030403054500d1240e02481d43d1340c88407152031400d03003181c042c0e84030302e42c180241480c541080d49000d1101c601c500814103903543d580c1d11756800e0600f0388084541500089100140010304c1070500140010500301692600c50600c0d20300980c4021070f030720807080107401040c1800b914400030b04034066a0081c4c000390b40c015031164182503c01c0c07407410101b401d421541c1e00000030f01c80d400701210119010b6507150304d0b000b546e403031801700807661a1080450746800c5034a04980042d0b0540e03c10b85c0f05002c0b038883d599050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 273201438 1106 273200332 273200359
    0x7030c0203150f10031703040317181002132903070819020a08150f030f03040302041407020c13270c05060f070609050106030203060c09 60
    0x800e105100418020038002d5076001c40c0c2d1241940c00042c14117860350315818004480f440300d001424000101050a1511034070001214409054000300345003003a105803004400482d142904c2406428400301491038a4001c0b9400241c980d411004524203180071803e41c240074010f0015802034114810544100c1403000e144100a00c0e2500050361414160110001400c0e00340c5100e03030b610420941041c5a00400c46070740003445c201014050105d000702003441802001003003a03052207004484004c514001008205491090301c0c00c1c440d40c2051080b01a94500a031031140158014040c0c0004c1d50401881088060051300c1d80418223202c00c64100ca00307110051684111119000404030038811841c110354028801640c44928024545100c0426400ba6080c002c280341d85030b5aa04060010075080300019680040c180d409a04040621020070343c481b20800e40246900030744171 = true := by decide +kernel

theorem cover : BRFrame.Cov 273021582 273201438 := by
  have h0 := BRFrame.cov_init 273021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 273021582 ≤ n) (h2 : n < 273201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
