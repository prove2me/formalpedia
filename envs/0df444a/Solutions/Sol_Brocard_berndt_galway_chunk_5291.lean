-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5291
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:23:08.126395+00:00
-- url     : https://prove2.me/submissions/47be14d2-4346-4ecc-bed8-7effb2c4ffeb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 951438848 ≤ n < 951618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 951440098 1250 951438848 951438871
    0x2010909050f0a0e010e120a090803161b0311060901031107060504030305090f07051c020a0f1505070302190204021b01020304050d0314070809070e07020d02071a040b0918 75
    0x2884440400d5014030341c02c079013100c0020010030700303241d4510395204130310801001c80080c042507408a10380600c0f910fa00520a02d0140c9940e2841041841c0d007410b170700841146c441000300c2807a1442034069541e102038071342c030000c100307014003070a410464103811440d00d182c10580c555051031390b030040140c05060480d02c034460108032424980b4000e01950001404541c8592000800036106140025070380c04441003519018581d054020600414000901010390001400c140001e80185150324040c200c40b202d01c184c00480030702c400200c400c2c0c814540058010382c02170720000b03d5a0010010740f081140b00800042c0740c203a41e502e04000d0518092220203003a54003004100c1400710038042d031030b0089043e2604100c60075882010b18042c500240c480020080c0000c0000c8410000b041300b20041e000e441e411000d05c0c90f02d0b0380020765840c800d98903c40103014034080007441c010309109582c00141c05114035401c2505111000066400000115034030075003188018024100d501d14040c052421100b6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 951441348 1250 951440098 951440101
    0x4050a03030201200f12060a090207030503040302250e190e0106050f04110406120212040b04021c03020303070c0804031a0601081311010c030e04061512110306060702010909050f 78
    0x1050344031500c0c1552260b6600d1340820114010950341d408896000042c0480944640c0740c08002c100c081d11540c10a80d070f01c80c8001060b50034107030002c0156114500c40d81c200d511420712030b0004221005820301801030340b0a41001803000180884046900131f0901c0360031501c4141d43c02ea250706543c1c1c0216000885c0c1d6503224148914149502d1b9844846001d803014401041032010095062159220700c0c400c001110306268a1076901c2d0f0102c409600c051020b807405800c01e03050001502500780c0e001c034420b808a0341084044a6055600d10a407900340c0c0144d0304540d1421800d59100c0e400d40c00494500000300400710000301c40c10341c1e01c0c03801c294480d0907400e01c1c13410318000745c01503074040c00e044001001288000c00150103c610007115440a20b070181c03410a540c50b040e260350302805c2d332003503205090002c041032241c1000d145000c3c8042540d0354000c46c070491245031040f00c002d200c00a080f1202000000c0050a1500082c65030500c1807500c015110b41d120030401c21110142c038510a4a0b61000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 951442598 1250 951441348 951441371
    0x603020c070603051909020d0c0f05010e010e1e1801030809030f070311010f170711250308030717010b0306180114191a07021c120503040804050a03030201 68
    0x20301e014020700d0404100c2e038144428150114840300208080c100e84416055085485280e018000140d112002d144030b15150134000650008034018140003e04080c5040401d40c0b29001c801308200015118142107803038421080b03074011808040a40142c8541c0c884002400e41c02d0351540214020889940c4800b43c0300100350410a5002c3d014060754440c4000b400850201c0d210407258140908140650501c50b440c02e842c0c90404400c3c540348242c5603400c000205400100181d603511000c0240c0311030503014045802e50030003c1030301c0d80b4004201e1506100086601000b15008200c40c1824002a0449421000072007000d030840d00366a0008001d101182c18100c100c154103142104500c0030079030614691011644510041b64441c49c40039a40c1a840603941f944640640813680102d0f43c2c101c0084201500d5a1017050101c0c02001d100c0001c0c1444c83d80d0380b106183d01540900001d440e880c1701a07080b01c50350009801520000d0080100140c9941c8004001004522a8001040b400c2e10031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 951443848 1250 951442598 951442603
    0xd0203010632030c150306011b05010e2a040207150204080f1c050f0306040e03040b040311090108030306011115100801051b0d15080307111003060b070602070204150603020c 76
    0x82d80030ba000f64000c14030321241d42d032070030003890342c00076400322040d00c99403007000407180c039503007014a1203034048001c0c40d1006100d0103401101854104800300ca9215080496980354090700b00d4246644414801c5002c855180c80d4006000640c0210801007540d200d9140c0801203a02503805007180350b0019010142c1c0f10720920810300140c0d03148020042180c5078a030050500d00c01c0418845907440c00000042e6155150341c000c0e406c0303403004021640c0340c2d502e075610002198481c0c0001d40e40c0140145101405241000080e81070ba6940310165045489103030042d00d5a140c000d0210f8054042d9507401000495421039091042100c1310b0f15001017841c182d5501d007100c3c00034043c81e4510f540400780707590311000c00e02103c2c1109080840043c40114610350205603040940002010303020005004092003481e10500d0f02103001100c000121341c1031800c05408542841c1b1903808425000e11020002c81c8059000c3c00000d40040c101140d8000b80c003180d03021000b6a80c01c1000801e9020a03041140b9008 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 951445098 1250 951443848 951443939
    0xa020313150912030f11160b0408101b031e0905070303030518061b04081c0215090a02010509061c0e1605061623030d0c09060507020d02030106 63
    0xe81580d140080f001d0f0720f00401149800645070248603c60010195121040000b071071003100001c4031060060701c91070303c3c03425a403251003034480303a00c1501070304600d5030254481c82181c00d030160000c0b07550a2030400194081d20204a5126002d8002c5040071280d24560040000d0180305001a00021b0705615014040f18805410b9072041c2070100001e5154000001b022074122103020a140b070b91110440103150584565004080c0a0003242e01145141008252064188030590241e403456030b41c0036004008084100ca180407a035000d801300c1070240d4002d0300104041c08016102070701e4211072201c45040b07850426800b0744c0607a07030b410641a406205100ca04642c2541c1141c010380c4514081c0010404d0052042408038801580b00354020801100c1050100d000c155805140c3c25442c02c0050780c5a4010000200402d41442142101d0342c1c4184074000c01ea50640d120f0f581001c2d11502400740b1206400400c0317800d51b581d04404154001e840d40c42442001c038518044c0300e002102c1c010520210003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 951446348 1250 951445098 951445109
    0x21f0e010f0e03030a09080c0d030b030c030d0221190806090603010b0303091302040801050c07050106080c0a030f0c0b04180e1507120902090a020a030510031101050a0203131509 78
    0x80c08840701d20b03502010046a4119034004000b0a84861a0a0680e150310441c00c81d520b42e88102c54856198981640002200380300403426a82004400010305131034aa0b401012001a0400414000c0550601c15075000b0340e03074242030f010304010340940402d0411601641141c0861a41c6040004a2416440b00b03030b8003220030f600a11066507041c01081d900d010394150648a0982ca4459069100b11035056400802c07040000f84001d080601850115510a5405075615400c08a01180141000400c84151b54000d05426581071031a1114040c001003030070100c4210f05034050002d009034680000d0006081c100c0f0031905900d040102e040d046407180032840c0915002120140f856400451025034030514604124101480e010200c5c00241081d42c1c0096201402d40b01340b20003219541e000c0c2141c8500c9031010012a1280b5100c1c0301d44150b1031100803e13901c03031118800300651085001d07000c00c441600449043c10f405038088003540c0d803541c00c00543c0703540ea600c0d007032031103603202010000801 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 951447598 1250 951446348 951446351
    0x50705093610110f1b072d0515032806050102100509100203100b12070e0f0d0311010e03192303060d0809040e07060e06040501170601021f0e010f 64
    0xa65181c8602031400b400042001003900403ca10b40b0816044600c2c410210705081551907260302c0f814024102e00210a103070000c4000145030b0b07d00c0c041ca0240400c1030340c00042c0f4085a1440812054055500060403580091007022030f00134510302036074540ca43c480c0001e90201d100c03403d044c0020314209030400903101c55400c060602081000204000031400c0443c14056030700d9441448446850020b50300400d50b5a0000a5404000804401e110300030551540d5003500c402d002410002c00415050745254032444038054080080d00031040c5503c0b0110359000404c3c5800c0160b0981d0640d04983c1c1c03041c024000b181d1701ea80d111644664450b03081c00720b2000440484e5503061021070301d0702000303010b14000c40301d01103010107014a400607202000e0005209005076194034030000c0e200c000c02c1c8100804501005220703204ca01c0c00100b50707403d941c8103035600c281c0f8104880f0603402104029000703e0550003010414000f82030000d910200020009a01081040c1000003250031120074600b040344a9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 951448848 1250 951447598 951447611
    0x6150a0c020f0607150903020f1009020a09020712081503071706070215040311030d0f15091107081608040605070b0901061a09030106050a08010e010f0207050705093610 74
    0xe00700c000d26401420084200181b03c2106283c1a89072541c2c0c40d90383c4c4044e1040f502869030101c4103402000c0c0d00c0780709644035640ac82d0b46500304400d03409444001480d80700108040303100203204580081d8070880c1400a60000703480140442e080194a0f001181604040c1c41000341c81541005a590800021310080c240d00e80b1280109001c010050001000c1081d1100c03401c44440041040e9885506540810012907281550610042c08003100c078065264040c2800244251310b4418039001c0c40800c901180b600c4007a40e10610180c1c031040c00c41442d206034441c458045403001014101400881c1c03980f41e540e039268200365407245801012544540c0c1002020320006003040c0944075900b40c50361f10280c5854680000034058401c035000b02e500a00100360000311044150840e0a0011004008208220002c0181410307403084807005011035006c0d990401941c2000202d49902220040007018064858034145505004c1a0400c14200b0746000605000c000180042d5000c0100c0c0c1c0c0301007000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 951450098 1250 951448848 951448853
    0xe12070e0c13060c0c1e03030e040504020f010e0a0902042606010b040923090706030b010509060301050603250309030e060717030711030c060103120912080306150a0c020f0607 77
    0x203491150040f50b080201c007a00000c200301d0710803201c01c06080350fa5a48018900042d0324150748840c64481070b000034089502400003814284145801075401401d0103003460703941001901e20b800004105038004240c00e0300080c0041951002d0b001800e4902c80c8000c1c85c06242e2402e40c0c51040034070307115400d034103d4001081038000304403c40c0c048820340080801d191741e640d0706a40e04114100c0c400240000c0204c200a5088408204502030f42c0058030104400da080e2001101c0900132440c9040d0018400c00c01409070f490024091a4002d0705420504481101c04019203004002200e0341400b00323450705400d00030541c1250b0751480324202540c145081c244203449211150300003282d003141e040c600101250300603104204003d003800e41502240d0703031740306804425503440c00244800d640e00b030344401c6060003080c030501c2c4041c1110002010040c4600868641800740c0d0b0018029990041c41141c24180500c1483c02034412040c040e01d41c00450139260050000104240c40320303d120701002c00c1110700 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 951451348 1250 951450098 951450127
    0x1d07020c04050403030b19050102010608010c09170f100506030613020102060a0f060f03080c070b090105190903021206090d023c061911091509010e12070e0c 69
    0x2803101280d0114450700e45050aa00600740c0c1ea02040e04101030071549205030741e40560007022600c080e40200a036a42ea000510300f01c601c0c1d108054006062100e080081c01c2e60801c0c0c02c0b803288500e0042c2c0c2c81940c01300c0ca035503281c00b20580001d402e5a0311a0100041031070140085540880c60492240e03100d011039000035180c4a000b440c004c032044e6510102c14502500b940b000000e401e0307415515a02d1030f100e0801c0d604035000341c42c05110f20b209504010440200e44000d4469004068607040c0c00c040742c0091000030130560306030b08c40400c5100b00000000d1303074480c1070790300d400c1c0182c3c005001a0b02340013000e682454604e0b0480800d550007041c1d5130302030a480c000301c000b40c0d0058103442c0c01c3d011070b05a040d4044003403215062005100b0f4609000c54820340e681d04c01c01003003007810300300514504540102d115000d003454050740309030b0816114905841800040182e00070514001d2000e42ca004000391190180d400c8a501c02d0303101c48814801580c0003c8603541000d0311306070017420280030614182 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 951452598 1250 951451348 951451363
    0x4020a0302010518100302090a120f0f150c0509010201360201050d140f0f0c0a050c010b0a030506010f140a14031c030b091e060103050606090306010f1d0702 69
    0x20b0400c000000c0c909003507240310b1018801e1000082240210428000c0002c0c06034100a25040c401e090781c060020b40807441650010030154010f00d0304840034034540b00c142c0c03e852185030540d21924903041440146000d4401c3c00d04030046030f00d030035484140000009085030101e4042d0014000410070058501e90700100042c008070a03803240c541809406d200480e03a6000f405200d07400b237802c020745072030b4010b2403a15642c410840c541000005030794190f800f1054104c10345101c1440c0404102a81039284100000e0060384642400843c1038000c00300030885185450744161111b42000d00140f1007011041ca00c0002070034000c414100105003900001d040f03021521528180048040011040352018030800d803281c481d0103080e900c000030901c0064040c01100090310310600c0ca4000080d07100141c201801c1403600c5402c5040744a036201d5005400504025041580c002400e121001055031708004250103000000c0410194528001e02c2c50a500c18a440180682a5010800420f10350008864 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 951453848 1250 951452598 951452603
    0x150c120402130b060d0f0c0921030c0206071a0703090c050d030e0a0b120705120432070503100903081f0b070305071205040518060310021c0b030604020a03 68
    0x31240026007076450000c08564410715040341010035101d2002c501c035801b5980c003c5180d1414040342c880c4540c201d41d044220f028038140d18180c000000c404070741104411944500c20300313040080da0b6890700010540d82044004503804002504d4000c0703072828140306183c12031810304080c0900140c07681ca895171643c2034080d1b140281d1501441e80d041c984207007151842e07140c015144200341c0d900e0b01091080759010401c01800d1066075404103415504c80c42c111140d41d0301080070110240c03a07a9581070b10030801c166408480000700e00000c48a070700300c0e00c148117241134541c008000e0b152900003814203020700301c1c00c0c1c903d000d450f00f088400031940003000300e0343c0001c040030b881c1d00228801c842c0000300480c0390080c0a030f080000c00c0d030004154110008003950307401380d4441c0031385c044910400c6a440c0716070701420303420031031050081d02c031040f8003503c031900010020300750b0b0140110021103d040341c024049080c6c0c0c48006400385042c0400764807035071040c1c3c10203801400d1181f815401182c500c01203032000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 951455098 1250 951453848 951453859
    0x5090105030406180309090c080408030105130905010507110f030903031c0e030703050d1401030507052e030c12020304030801150e0a0f090b04060302090a0207050f0708150c120402 79
    0x140400038154402142c3e01070350605009181c13400e05000b0241d41045c012040c801c2c6c5421840b002c4a1b00408a1a216a50014909180d03a0070207080c8402090b1185200380340b59118040c50780040c80170f004191140345941e95840c1003c200941e41ca10708514035442140642042000c021a03840110442e10400305407041c204c06080c50300189401052504e210b00018040892a0f90030954064021b001c099452a0240a05a2906003100c10101c0c280b10040a60740040380401040c140091000c900c6d810001d1605071401550101b18a40c034010480e610001360384004c01ca201d15002500c940c8000340e424000c42c15440c0c0350360003500002060207401c041180c8016501c184510818014210320301c0504203288461f0340b00341c8041c480b070701c80c0602440641080e2280c940d5017080d114180031290010700302d00ca103441d40d51001c0000e5100590070f64450103503c00781380240e2010014100100040c2d402000000b542d068004100d40000c1c00102041d05d0400c005009a40d0700740ca203540044e0104d84 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 951456348 1250 951455098 951455101
    0x120807021807050a080115020a0b0702011808090a150807140405121e0109080906031008071805070903030f141e0d06060e030d210509160501020705010509010503 71
    0x790103074052081006540000c0820401c1c080e0740a0042d202c5150301d0b0712108803030b90b01e840c02032203480301d0400340c2c0700107034003100140c004903599404040c3c1040140c0000202c0c04000584d1405a506240d425a04030400217411101414800d000b000240100c000204010903100002400c0480150030b034810444904000c1400c03e00c403004079801810010541f2042c05070b0100030544680000038120f03484403040313544041041040c0940b030003131035001d03060a00d81401c207001c00440d9007014145103c01203084c44003107000d18041001001501182d00c2100c840e603040300440003503a5000b00320b4000c004040d44100000303900000c000002203000d040c0f45641c8001c84950041703a0003480d595880004910280f87c9080c5e141100400030301403524000e02440761500c5c8141c442e8003412030b2841c3c15500035041016400d10550882c4030103c0c04070420b07525070b460f0203102c0d4140c4400350780591440d080342071050396080c1010450401840300303001602e0300c540b4001c006803c6000f00103855040c000b0020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 951457598 1250 951456348 951456353
    0xd0b040b04021c0e0c1014070204061d450d0f110f0712141204180507091403011515080703050f19090b0103060e0c0109120807 56
    0x41088942003000740086407241c042e009000d0382c00032540c0700328900502d42440c4e45011680821541d41854026008282056a030b010864035148804d018081c254800d00c0300038010703a1140200c00c010004045025085400c481900d024410003419681070b412202e201480c5003641041030b6601000c5d00400709014000d103103440d60401206410710b00c410f001c0d0400d62542680c102c0364100a8030071a945110501501780600341c1e80d41d40c11800c4502e5540f21020402070307204050803c08180f482800046a00c0380c118802500c0d0101040c1da0b91502d15020038107000c840c280b1b2a64a1052001100502c29428050005000f00c041c0f8080e042007152406c214032043d8030250054441041540051304840b6655150080d0100c810040d50000030310700d0001c80c0080f4801d0040d0ba00810582d44041c400b0348a4840040c00704007021031207880c1503102c014110101d002071407104d0007540901c1e80414100010300d03c045c203084035400824144103031410103000110710019850212540040303011f980d450b007030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 951458848 1250 951457598 951457601
    0x6030203090a0606080f0c0102060402130518010609060e1f0b1e030411042f030402010c1e03180f091a06040b070317040302030d0f0b030a03180602060105060d0b04 72
    0x2200050f04550401c080020440000910b410380e126621007600e4400c0f940100483c0c4901050b1000303544074903440103130200c1e80001d50280f504800c560a12001e85c0403452000da0966a0a50000008503943c0008118010100c2451540f001c140d203000b941d03100d40303008a0b542c020090701540c81c41c0000490900d924456030f400c00c01c418480d110301280c80f40340c1450b00900c071020320501c103406281051440c40a580c4070744402191200e1044001d0400352003640d48044030742004005074100400031003840d005c152480d0f020b10030440c104413808600d1041d420040c10140c04a00e8507a10082e6698040003101c54082d040344c142d8000b40000310310400481082c1d499203030802180ca5109100040024140030b14000810041307119031611000c808103003010703001800040b034025025800400403036651040350380c442c200d0000c05450000300075640c00c0100c0e1074028010402c50106004407016040504403800c1100204040d2009181030b605120108240d80200190458165100e2108030740984e2903 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 951460098 1250 951458848 951458863
    0xf061809030f0d2304050a030e0f090708060a05220b0d06140123090f040c0f1d0108070b091504030618060c02070602060c0c010917070b010902130603020309 69
    0x450100070744030fa00ba003d0035402007002c94403c00504000908401424413030344400ca11640d0840c010304681507040c0c8040d01c0f0341d907400d401283c7c04800070080d0900c41c2c1c1c03661400d500500256803004050324040090025061994020600c82d10290368615012050010006215402070f000412684001004184406c10300e0100608842c10012174020100328450341c0344c100c41c000c2c541c1c280e6000303102c201055070200488407107800c40d80d82c00003d000640704160316070b082032107040c86804003540d6598841c45003600d500201300d40d62842c0108100a4100c06034140901380510203031160318a444440ca409200b80305242d4001c803181c0ca590081c01d061842990020f540198050108026101001008000c03440d021a40c1c1c52411b22803025032440000c160341503500380c0e00100310f1600c4814a054094104043d0a42107649484007a000134205400e15600b42041c4d840385900e82d0740c3c81c46c1582403050146c02c6469064030500108a0380069000c1100464509090040e903940700c041c085400e001c1c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 951461348 1250 951460098 951460117
    0x7030f0e062b090525140402070305160b1503073813061403090d12091502120916030b0a0b120f010c14040902030a1e0507080f06180903 60
    0x2610160b401030042c0412400284849000240049062240c0340c5c0400c110b0b41c0603510384d40d00820121049806e2a9000702801d500a0906c40d080c510710702c00500a81f034400d00101c4e904805070060258190241503501e0580c1e000320080c1980710705114002180c40000050044000e8000103c8985614046095080290003a1b4003564071005040c075180ea0385050302c03450380007660300c0c5420700d071502c1c0d01c02c1035074010801c50019000c8098001011140840d121001c0c8400c0d0b9580c1c018040011515040c008a1401000000da2a030314100c40009950f00001c0041410782c0148400b1860701404e04081402c6d2980100510840d880300341c0d00b04014908410f803e50818507040c440c0080e8940001d00c900340380e032070000038000d201c540c0d902114031542561280034100e00a00040c000b1042ca03030042c0d6070150000b0400111440307055107083c4520031200d50f083e240c82d941c4050003072803980040d1080c0e200c2801c40402409050640104143c0b812141007001200c041c074001c189901e8090048524024 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 951462598 1250 951461348 951461351
    0x9060711010906050c0607030f180b0402090115080103120c0c08060f010b1c0b1c08030f011a090f040e0d02010f0f06030203120304081e07030f0e062b 66
    0x10194500180d504a05011050102d1a40b010029811340b14200f150349490118000c2e200c82c0d00c2e0000150702412200b024406559120442401c1e0b1124424036850780d80d028800100e11410240184100b480068001d0020140d1100c511480c841e003040b120750450303620501c24400611256001c60300d4441c01e5100030700801c062200042e01c81d800140150081101070501c0307003980d03070300c041030a80b510480c01c204410000303203c421052401558020b503c4a0006030911750050281d000682e036041ca0311104481d241030100070310640044440d20a40540b6091043c01e010f440d040325a03a505008070501244034004194200c10700c0e880c0d03501300c440e00d98113840866096181c42d0b20082d002e41541c503c00c60300c0f030703150811200ba503203103a00900e802c40350090060415003546100304007096000801c15245c5190420041800c1900e83d50600c0346180800000e688504461800800803488880b03428100000c0c4410f9001d66a41c0304100c0e070b04112800550b48107030b05010404221030450041012000b03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 951463848 1250 951462598 951462607
    0x12070c02060a171f06200304060c03020f16090f0e0a0510141302060c03130605040614130e06040e03070503030108070515031501050c010c0c0b07170408030a020906 72
    0x6036003000c40c1c070008400207041c0002a603100307210140f05014082280c0340320521320004211483c003130580c08032244216055600302e401c3c000f024510f1640f195005000140e41100b061050503414450030200e80301780c0303001c5d00881e08042d2102d2003c42541c001c080b8000c0d030300c40b14000096496400b003080003000748155000d060781800c0c1291288130843c1c502c402c5508043c0c05800c09111061194410080740c4581e0114080503024402e8980200058a0541c402003050445131045006040c0080615544090356242001030041550070350f2060343c0014501800700402084445420744c0503500e0b43e4a001030349594950005015103040b04104116010000d460410b1003008002941621000d40c21542c140d9030f6042403040c42d1450326210514254240086030102c003134185020101c00c014502141030213402060720342102c0c3d1068983c00070a1041600d50100a014000190b2020090600003650100760349030055009005000420a181c00400201100c07100d078140c910652002c0c0c5156140c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 951465098 1250 951463848 951463867
    0x9060d141315022104060b120a1208060d0204090314072d05062e06020a050c03010513020103050405030417030403060b27042103060e091212070c0206 66
    0x2004100105a6403802ca000701c0b03411401c0d00d40215540c1c28140b001038981001ca2000d0b605090b98003810842da500c3e124800444e01c2c1c0c1d03980785880e030ba00c00c004001d0b01e8441c016203801664485c2c8210100b060090403400c2050990358440c0701118950140d40108241c00545001c60380301c0c00307180381071000100208105082c0480c032008580c840203c001b034240905044003c86000500680000701680d0203000007540300030440360a001444004210506040c41c110007291021079260001c400581c8000d441c541400713020040854076110aa00800c41c508107100c9400400044220113414551240007207030421108000300c074010300340c0d0601c00ea000030240e0486506d035442480300342e62076810072002a201c2c0c42e08404070211101074040481107180c1490702d070450568010419288891500c540b0760052044903074040b6502055a40011828101145010f0803103001d0002001a8482d0302412524595130048849400400701ca10313866a842d0b8600301c5d9840100407000b50484004602541e2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 951466348 1250 951465098 951465121
    0x20091906050d11091c081309020d0b040606080612030d0f0204181802041e2a05030417090a030c150305010902070b06011b1a070e06070809060d14 64
    0xa200e41c0b0344824489500c02c0389400000380a2455aa0750044401e1103c00c0c0c860403a28a40b51803522612804c4e041c030340e64003100d050514190f405000c500350001003c1c4581e521500c18040b40040484007080b001d81050001000d2100c01032038580103003401c50441040f88800c00c20340e003a0b4031220b00148084450111601e01035005403041c001c0c980e920543d80101082180205c210014521001500032112502040301070800c40820f84284150b81d458083c101200f4000c2e003882440d1030800240c0002c0300ea00184109021003140030800800344103000015000704080042e40d014110300790348507101c01002449091913544014101c1684030400075100c040c0d40c40e90b40700690942c40c1044281c9c1c1c0d6003070b02c90070791248010003820107100c0800990958003440c440344100881c00b030003d030312011070f44e0340030181100500e07141004100c03001040344481d84402c2e5500c010f8010344015043c81c1aa03034900500e401000240c138480d0401040014101c00302c0da000301c403203c44d20120000c80342084900007030f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 951467598 1250 951466348 951466357
    0x30d0e0c040c020f0a11010e10081803071106030402010905030d0909110301060f080709091d010b0f030a0b040317041b0f050d1e0c0305031b012009190605 68
    0x24007560a11104900b242d00100301002c0100014010b00071a012a5031a02c00b2494045078450601000d28231845d0030351100702910800380d0590700d4000d07132820302030b014490060391410788445580c02000708c4800240c00e600a05030b5848165800c940701e4465100682d18034056800c00b507058071580d0300070994540d00503049000c4510b01c160800401450038039900c4d1500c400d01031030000c11600050100c045114a01e6079501c041a071424403d001d40700c40c40d140079100d040c0481d04603e1540030f1407501c0c0140070b102c0c0c201ea840d012107055030341220314008a038440c02902005405d030004040080d0a141c081c00441401c032a07120469251407070107103016000c45940d0044007003802801240030030300c019000c03481015640c00400501c207129059440c2650f08500c3c07250000c0030070244070b180780010b025029030005107203d04040c2d0380f60315a42410308000811450389042c80ea04000c60800341140f0f0f20180748041114200c0c441d91024502e010031091201800100c465601000b0b000500303591200252 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 951468848 1250 951467598 951467623
    0x70c0e0c0a090801090321140a06050a05060a2c0603070c0b0f010b031b040906080a02100c0807080a05071b081006030b0610090e090631060509030d0e 66
    0x50401a48401001c4d088420340c0c2c100402044030040d503420b00001e5411000b1510400c0d480c04601b42d103503900b0911928000b0b030b420070300d0b0b562aa007044c442c2c2d180407002c0601510050740c95a040040103a03000b08524501400f40e61502e103418202030b0164440c801445845c400606959a20b003045038005002c400c6031407054400400d904085149041e03200fa285049480c0c0d04030941c11610b514001c0b0091103206082400400010000011a0a071a0260500030110b92000d0401211640140903000000c0c02c103403010070120141c1c1400040c540380c15505160b401a03026921446481d13825200e5108050f806000010100d042020b1115846c1010050711035950a4581002581041009a691a00004110030382520006015003410485990310081d40d1815124160362040405131480054803212460342048040059040c000d20035171214000c94203060030901c0c00c450515103102c643c8400140116100c0c000b040c108181001a50003000890404102d480b24462405075500300031040c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 951470098 1250 951468848 951468857
    0x8070c0819020a05122a030f1b060715050c1c060302010917030405190308030103050d091220040b0301110715050f01030807020105040317130b0309030f070c0e0c0a 72
    0x118060400f0317900c000c0d41c00d03c84030080c034180c070341100d004e0220b1140d407404004442d21070304010220380d07042000b604c622401d580900030740d07600b200018001180c404070b098010582040608000380140c8120841039421101c0040c054490302d1844401340b044981c100218244c6440310201c0603029407000e1700b01c2c0d200741c80d21b00c80c0d6603958450041c400ced000803116402c3c0c2c2042c8010010785c1414410004c4800050b18103c060030349a980d0a111030300280c0007034031325a100008044c0a590411050f10140c5620100c245800180d6a00c09101040100300580b07803002c848518020b41c0c855070810390f004d22005000b4440044198583c05c1290003044080c2c581402743c5141c0c0e240c000080c403070140a10b40010709003510380c0c00c6071143d01440e03110100890410008020020114141c40100b100100c1906002075480340200104240d0034035030f400c92100c0850070018003609400000841d00811a100311075a12425030f41003c92840c2c402d40e2003501c4034400725003008414021800140008501c6844 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 951471348 1250 951470098 951470119
    0x150a020a080906010518090a0807050f0c0a0b0307050a03110a0e011403040b0609070203070b1006020f0706020304050d0510020a0f180f03020402090f18180102090d08070c081902 78
    0x80b40d039a078400a20540d80c1004010400c07081d550050003800b9400080142116480350203551400902e92151706e0984150b0080e10012142c0901880711001c01c4000711418101e032802c105500d643e61002800003000d1010020b2880d07170341800b03078110003520011189003949542040001a04090400d1462400600041c800b000c000340c0c2c3c0c8094038012500034a860605075910400d00907541e01c00b510340301c29440705001480c00900b0400345284140d20002d4125985450400060714240e10b800c508851500300c20028084d4990000c2a02c0844004503603112180b8a00d0a00504000007220001070345070001908480540d0080d08084500341d05545800302208019000e4061039040c0c010100b0211f20340c10108050f140035000b80900c010010b0510386018a003000240740880141529880f5800c80c8003001b0100460194060303008540100039031910701041c000070980b26941d4401000490041005000d012101d840b0a024007005822140e8070403d090308040100350b021001c82c4100d41551 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 951472598 1250 951471348 951471361
    0x61c0f060f06061e05070320010212060301020306090a110f040b0301150f021009150c0807020d110c060c0102040e0f04020a0501090b1813020a0c11010c0c030b0702150a020a08 77
    0x1113120038801001000812600741c01c00841d0107621011080d02040a0000003104211000c0c070f0007003070340c4034a10005999032203841d1051081744d0000c001c0d40c1321380d1052040011545426000e180d112051140002d0030f10400c02c084940e07805800141542d011010901241150f0762000850583d02e5003440040b01e00690360b4201c1e5001a030b941440c1c0107070004142401c1c00c921300c0e04001c80c1d461040540e6202c00781c510300c9000889130f08030031f468001252141480300042d010311880064910301d00e0075030a820081e1100d10703640c544100c5c110740103500000324038041c0102981a900078020040e0300c0d107001d05101902e0b03080d21030181c3c0c082c0d106a11035140042d896001d10600c00445074040d0311242429041880803201d030401c0c2c0c1a00f03420901580b0003840340d28403440101001103058903000b85465143c10700d0120360342008016418003489821300404138000f40c2480003125405000313840d2030799510303034100d0802200200d0514598400814492845000c2d0042c003001203a43da1240a03556412 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 951473848 1250 951472598 951472607
    0x90608120414011e0c02040f05130f02030f150106020606030a03080106080a0605041112011203090510021c0c05060708190e0307080f1e070209061c0f060f0606 70
    0x604003204280c20070001041012098101100700450504010042829003c201c41e0050710b4060180c0000700b80303414800c11840c29128620151343d044004000720301e840780c0210f446605c2c003200940740040c004201c0d400c6507410442c003010030b12100b041e40c0002c8414508032488140038002d410241c040c880004055050008461210980650b1412000e918243d425a480c10001d4000100d40c0d4541c46c1c0410b1030b407110702401c4002c2040389005a0340d1600d65242003080081a0005510034810718103650110364030030002029110125500d03c0c40035407a81045c1e141c4003000310804c54074003100d00341070021500404950007803030041e826a1541ea90725030003290b18a000f103840314151107200d040c0d5036041c0c2041c6d0142c038803c00e40004580c44c02c2101d840f000d0247d0011482d07042d4400c0005402240d00d9440c070f06c00880320901100a03401c0445980c005121380000600f40c80c010128800ea00c5040707042c00310b038141500d42001040e64640701d1410200094058816140d082c607003042e0000440e17030b106 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 951475098 1250 951473848 951473863
    0x171905090303070b04021f0f0311070b0703050c12130213020a140a0323010501110a05072304051509100303090e1e09030a0914010c0204090312020c07090608 69
    0x107014515028080e51032048280000d0010781e0014984000340004e501642c0301d00100007030301c0d1961101c5070002c850080680346800812000000248440c800140c1c01c0760300140c110015080104050703440c0300c4080151f000f50143c0c0d90015280d0418007240032145941c80d07032264001e0390302c00070011800d41160183d10405a0f0100080d105010b4041c0f0001510301030034040c42d20307150102d40c0d00603603084204005c50908203d400100000f0041020b9070f08040d20805840d105000313070489540503202c01e5110030b102d00c00c0b5004c0601d6000541116402c580744d107074070b0440c0240104000c0c184080d8041070402c2102416004141c4000865804007060b00284101ca5050b650000c519040c42c02e020703034a44019000d2060310031010b51401c00c0000a00f0303083c2c8102c1c02000159144d40c802c110003088c101042e404518003205040407441c150760b11103c1c1c01045178064402203000426841c5c212081c801d2044421401403010a01500c205404a035440840301900c80c1841501d8a91034155281c600c0e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 951476348 1250 951475098 951475117
    0xb0f07050f0702090903090a0e010806010603052701060302060c060712050c0913231e010609050105180613051807020d0f2a03032a0e030703171905 65
    0x50100c2401440c020f22403a510211a1007030328200150300c8045070384034002750400e20542160f800148503040003004024014451864144040e0a0060300c900b010190300814001c0c80d007500d44aa00c00d05da0135044000195400b03081580d5a160014040d52035203030640d03038100010380140200b00b403110f0304d001e11030080c250f08645600d01805801004140c06801115628aa4480985c032107002c1808d1328101c0c002d848031490b01c59900e03002c0c40b40b41e000710100f00001d06001528005000042c0c0c010241025900300b030070031031303500c400820724100000c400e0341c07002e5404000000e5404218400c20035070021500c043d240300308030418501c61880d88210403910000182d00c20200c000c001e9103c1d4003514410811420604040d110441c0d400d00e04480031440042219108610b82040603494460360040495102d00e1310b007001c003403e071003041e4500401d44410030084410740100150781c0c1402600001e44e07101405161580030200c1010490f08542c0c04180e00c803500e0101422018000d008031901c444 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 951477598 1250 951476348 951476377
    0xd020703050c0625140f0102040e07120e250b0f070b040206070512030f0906040308010611120409090c05060a05070b130609051b0307050306010314010b030a0b0f0705 73
    0xc0d00e1805100c556042195200799030120703010b014014107100114204c204d8001e003e0074440c400c2d09070a103498031100d6200e9882681c0f042004020135410140d00940100e000c1c9802003043d0301459006001c0c1c20455441d0409009001900c115800304143d410b0f110b00c4400001f200080d6182120f8015028100c0804015001000040f000a00a030f40c2240e016100030b0010781030504075126540740c4007020001c82a0040004180b00c010311850240c1d9034006003078001091070b4a007036500103100c0c0c001881000244034450000c0c6101c580c0600c07e0306100c041001015485594640c204009410403035030550f000110340b000030400b0305001e001c4a002111580f22280b82071015074035803400420003807210b16806d4882c2c8a03140003401c2c5005400800c3c1c05080102000320803003048520400c507540300c0d0b51283e80080e03010071954801041d8141143e030030141d0300d817100110108090140c01c0c1c405515605001d411082010000704ad501c0c24011003000310700b52503d0b030320030340705440d184500c0b2040011071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 951478848 1250 951477598 951477613
    0x516080606040b090d05011407051210060e0f040b031b1206060a1203030b04110c100b0d0308100b1201140d080d0e0c040203130506090a0c120309050d08030105030d02070305 76
    0x182040222100c005d4070507000015048000b41c0e1902d901c1d142514a0400580000742a510b03021000e2011a046406141848440d92602c000075240b0b103a030b034031041d020710705030212030106980e1980030501e80f0030b02a0035200c0c5c0d240701c407003503500303001521040912400d1301c11980030302400005815440f90f035010740800462402d1008000035800900320840030580c4512099010f078989002d082184181084500c0d1160054042d82d81014050640d01262a2420105032225581c1220707a207106501414054820b80741c0103107106e840c1d00290000c1c021820700080c4a9000d076050007800707040343d004840204400f0071728410009070340040c2d58082c12500e41845011407580141e409206490b002c071048600300c04040001c42d083c0d800840d0142e401ca4045070345041030000c24410140d0060790b02020340b00d590803507175900e00104442e00070720340c11a491075410000c0500460b040c5001c0c04005040f4641850145082403075603109020302c0c2c4c041e000d031b166001079440c000101c240c2500d50260260920 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 951480098 1250 951478848 951478867
    0x1020c0105030c0f0d1a042705010b0307171506010e1e2e080112081e03040c0f0b130b1c0e0c010201060b0316210516080606040b 57
    0x40c0c0010f07018152100707041100003c030007031000040901c00b0180790b001c207004841303210300008055024802400b07039003044c07503218207494a158540b42c1e42c45c8285007999090040c1c24094014511a000180c00d840f9204001ca031100d045803076006102142c404503101401e16424036a121103042d15200c0c045041d040c4075030703814070700202003d402040442820030740d490110005900c01640040303426006000300100b1040f100c000c03a4001c4008043d00f00300e811545050700011149182c2c1030064500c0300c01041d102071041c118440001c88007103002d040e91b268141400c10080000b803510800620f03400101c1c0005680c01c0340c0301900c0d10700c10100c402466107881d102c00703400c082d40400c900e4400403140b210b14038400d080600c900d46c000c80071140203081c0c1d090001c0029084403000d400070a500b0200f0300811001e00c0283c0811306c5400401c0c50420812540d41c00702d1481d0f020021f07040c0d107003181818104540048158088005034105555000303035500c4040c03d100c0c42c3c2c07145014421843c103042204090 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 951481348 1250 951480098 951480107
    0xa121106132309040308060406060906120903050705030d020c060a05150405100b0c030d050906010803070f0f06090b24010c0303181a0912090d06150902040f08150601020c01 76
    0x2100001d0b108502c1c0480908001449104110740480110303603507109100040c201407161401502040c20301c440c40342c2c1813090142004e060032a10480843e15201c4107020140b00350144d43d501940300003280d8482d102855140007a400c5903034017540300c7c840d070030024042c0c4441d8040e41e4012000f4a900705030300c80000040c440503110042c071302c6c84224034401c000540c00c40e102009162412011018540b20100d4900f81000d0380d40180255070242d001c0310040c4412407001c0112581d543d44810300450130780381c0d440c0c0800d2064040c1c5c001340069141c00003032024010b07a41282d81c0b040402d006904070060254885545e815400d181c20303800241b01c80820f40029000707521400c0814941d900c0864036a00310341d00c5004912500503403043c1004040e003800400300d01008005920300580021500f0030581001040300d0000601c000740440e51182003140c54040d80c24400c1e07014115100c0159035494440d00c0030b0010102c248a10901ca00c9415682105604c001002d280a80016400782091018180c01100c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 951482598 1250 951481348 951481379
    0x30a0b03010b0307080c0f09011a07110616030206070801030b1b040803070309050a0e040209070302090f03010f020c0d050322170a0e0907081b180a12110613 69
    0x2034040d0360310021002c10380d5081000e0720042c0402c10042185980310000d0150010107884403a0080080c50014002c84081c2d014020549545110030740c0c44110500301307441020b00342c1c0e1203e07400480010f40d400d0000004003488000c14065001c54040c3d0311041012100031400b444050f0160360081c0202e61307040302207150041e000030600802030401341caa0500c50300316488540110086402d03117100700300508000f140b1030020701e01460100e06619090300405c030400303002450403007095800190401c069403503c3e09001c10800140c020480f00d1f020490403030081d0301245180465100b05140002c1c00d610407401c8034468407604400801f51603000b400302800c0c041d1500b0445000b80e1141c5154204003520000c2c0a0740301e6269640c4d4407102c00d66080c03015650000d000c0c20200045d4200300105403580b508000030141003000a01e07a07801200d408232400c0c00040c4100c1b0303808680301e440012080c9002d1400c811546c00f50b500500075081000400091784103000e9070041300441c92a082191001070403101c0d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 951483848 1250 951482598 951482621
    0x290c060610170a0e0c1f03020d11070501062105070302040207030917060f150d030e031606031505010f0804080a1205191a0a0509191404170f030a 64
    0x1da8603901c0c030b90b00203242007070103d515159960391440000b10f00311003004050300500c41034440c1d44a00f1005091800d800c41c8140000040c1500040c030b08a884416a00c4071200041040c0e009886202e10320346103020301114070131106030300300c8018141030f40d01c40031500d4900158403078010b201044c074503400d000194200ca1001e070141308291200089400950300c01e014030140e0580542150314010104000001d03010b0100760508800344401d46150720b82160b0b0b0b484080e010b0600c501c026039030000180c5440070401c03100c01c504e1007122f00002e0843e01a01f204078011346003c00c40b0441c42e1074800440c0e1000c000e4200c0341c00a010071021501041c400002484242000e161180400c601c841c5040140d031015134104450120111015071441c2492045404d03030040d140d84620100420310004002c0c003214000d061184003110007150b68110010040c0c96407441d00e40c824011412000969950090104e034140c92104075201019116031748001101c4c0103c60291040d429900ca40d18140002c1441c401003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 951485098 1250 951483848 951483857
    0xe010f1116030804151416050c120f0f030702030a031409040216021e060a110102070f0506070f0206040b0c0913050a020306130902030c010513090501290c060610 71
    0x2100d004481d00082006035028a1659549901d8200000d030111001c5d0107141c10400551410780d01d01c608001284c080c02c46240c6400840040750030041d05000e80d101000c2e6000d100c08003040e00f50740001c6921842c001d08041070380c04020002240c240c42e481603860080d85504040846000240910f09602c40005034041c410700303110000001c0707422a4020812004070718000e501d60001c5140c0649205001003d1040345584801d02c40c0100719140a180d10725824007a00c080203080001003581960b1243d078005551001402640c20702030780384d803410384504d40010420000c2582044c00080e070140100e5101030080d0f100d80d1100641c4100b43c100100c005d900202011240d0403100590203100e000d11a003280040c1d82e070420008010003942043e004e02210341c14440400090b81d8045840403040d0302c20308000b561003881a00b260380803260758220035503040c640000440c80004414807801c82d07010003020005e82110400c0350351054021030300d203910160f000e100014000e0130003100424101c5120b080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 951486348 1250 951485098 951485113
    0x405090f060f010906080a050a260301090501030c0b13030f020111160608090c010203120612060c030105031204030b130201090b040909050d21051e15040c0e010f11 72
    0x10418109941581c0002c0d02180d00001400000664860100200f00c03007401841814101c6c0d0783d158460300c00d008050820800c98185220240040b5180c480d10142902c01300da4a40e180c0000000418080c003040d07440d1032003144003285004100003204c0c04540c0222029003294a180d039180d28806009070100e04000d9070b05c04180d0045410803000c52008041c85400e120341f4101000145441c400904001c8e40b41d014140c0b10f16580d03004400c50741851420401148244c1d00c007404148204000d891090440c4905410840303000031076030245041c0c65044050760307017110080125080c1d80c000d034040940072494400116148032860b04c0c1348507a052043c101002e4241c2d80301000031007600301c0c1d80321900180d1149158020800140800820101e660401c0c41070034010001d14810000d00c0991103164039910004211081d41009950301003400e034854264007403a242c02d40840c5220a0000300b030281d401c0c940c2c040704017401560b556417203040c1a5100c2c40740701e0041d401100e52000d0000d0814503401a401c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 951487598 1250 951486348 951486373
    0xb0418080c1f0903030c090510050f0c0a05030a0f210b030a0204020307031a04020a02070b030a06051e0108100806070c031e0f02150601020316020105130905180703020f040509 77
    0x801c500014a01c4100003d461001418003805407078180080e03200700000420288499660203028520600386450199105d154442c004002803283d0301c00c24002c0d06c01c4401f14406c201c1c001008080c901d400d66181d011404000006071002c2d54807a0001509280c041c548c0c0d1503240c520340c13141e124200000c08071140c14031990040740890384186c50440000341c503003800324200c04013810344643c2030500396021841c003480030400940301c01d414011480568800008115505100c0d004a000391074000c0243c0c4102c1c15101010840307014028820f0b02190070200011811980140410111840400130b0400303540d9211b8120b8401c01c4040c011828444440c0d400f14a1480c1c04640c1c40c040441c81c1c448000490356002d0107032a060405c6162095040544108025030b603012064a0880c1c0c02201d001c0002d40e078503c01a20b41c0e000710346a03441d000c8042640050100c1107a0800380c0280103451009180c0e04240b41d5994482b41d0502000e5040301c410704c200c0c003d0b800c141c4c3c4070640c02000401039801144404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 951488848 1250 951487598 951487633
    0x90e04020414180c03030c07140d061b0806010507050a0b0c130807030b0f090c06030601031d011d0c090f25050c0606181807090603080408010b0418080c 67
    0x554038000b00b00b08404a000e00103d040050031031302d203c114010342c00d29107034001d400d5950384503000792140850340d140c0c50031080e1a04031a6551642c0c1c07181003070240500f0900c40120b81409640c011f40010002c001180f1954000c40843c0e0310356800801900c540b40280e1035580b803101d009001e119080300100203031036541501d044450b001d4070042c1c01070116545141480c4054410103800c100e070b025605002d000800500243c5072464650590b00c1c151280e07590300040e4010a003402800780b0782c07441200c5186282c0c0d0117510081e503049036210140d2070540544030316503494100c0c03605c25410080b0706001c2007000c04c0c42d01c0b4081d4010002d0250340c05241e01e40210014020321807001178049a004504040d01407030a1081e036034044415208841d5061140303650801170320000d4241c002a1014040d90981034030309100034006411141d40a12034075980307141010040e401031082c41040d519164001d40783d45401c2c01040c1c145407a200e1200300340f441c00d0300c66005551050b240080c042c4500040c0c0741600550 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 951490098 1250 951488848 951488851
    0x1b0609040c0e03011a03030412110d0b040b071409061b1501090608060f0403050703120516021212011710090b1f1a13080703260406090e04020414 64
    0x19507198420180b9200c00c0c0b609450b0000300152503003140d659511100e46002080e50100c0d0300070424405680f90505140c00c1007110206510307084440b60440c0400e2020000311540928804d0190820540d6080e070221402e60009400300c8100400300308980e01440d01401501c981d09044450a01243c0c80c0d03034400c0e1504148440301c0140c2614103004009501d075910842c0024030140b00a00f0540c035101c000400f9655005200400340310010500c0010316204480008044001d800d0400041c107018000403071030b00341c0562020040c4103000d06400365200703a00584038000c0340c81c114a9402d03428a00240c00035103001c0588500d602c5102038418040c0c541d4080d20b50914056180a515400c04440e140d940d00041a035413280140c1041c410090030220b5014007030415580c46000d6121185a444544041d01c02ea0004d8560b114446012003400701440441202d081035406a492214171a02c10700c006002d64030030740b804030f0002e03001002482c01c1660100d50041c1300410000382c0704840308006021880 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 951491348 1250 951490098 951490121
    0x110d0c060e03101b020f031c050c09090c040513060e010e06130c0c1a151504030804170601120f0605040309230a08211605100f0c111b060904 62
    0x200340344c408404513018066103a20003822006145072015510302000007500084e00c19200c540e6413400105520004020340341c608400804100c81410b10a904000790341190040502c2503240c804035286c2840c0b580300da1000c1f24075801c02d031002c83e0320b000c1d08003034420310040c009070300100c0101c1c0c903030101c0005106428905d06a0344400910b0702d41424401200c20500d0015050b40d00f4260910500b00031580c02d0400510040728400c4040308400d1071a507003400b0340d900c0107145090204000c00c1d41620712440400d024540d40440320180c3e652013100082c003200d41c030301a28991864074140041241c030380009034864020b0401d000120341d40e03200d1420320325a15111000c0d2030701880d85100c56240c251044030003008200000c0c00f4121261900c1e20401418842c4920b000310001642d04020340d400d5150502c00703070028191a004c1c0030303042080c0c01401c024480042d0091412400000c140e0044010301c102c0889400200001c609000c1885890070305000c110350b100ba024030000c2e0190b030b213500803040f8088 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 951492598 1250 951491348 951491381
    0x6030204030b1305010e0f07030b280e01061205070512031905030c1306180e010819020a0f0308030a050121030c030c02100302040f05090601140f09040f09110d0c060e0310 75
    0xd2442c00c001d003427604050403420a000c9580c843c16004bc6400c0c0301d01c0e0205032540700c000b66140010044071b0041c03181c0d41c0506080041030350b4100c14007401080503400c5035416600429209030040806440e4031421020080302c468030810000e0345032140010715800700920f10303000d00d807c10a040d500101d0045500401c00a150340c84c01ea1010743d070400c10300008140720801d1a15950504440903103031011004d0501120f614102540c0965842a066900802c061417141d5411912414492501c2e40100d034030300d142c03500b40340000030001071066050458200100d2a182000407e80d4100c405504c2200e0a030300b004101011f43e800b6030382d14880901ca403581a140169903034545070751800b1090450344400d21440d074000070803000c0d0745c001e00b070900840501e0982540e0381c0211680143d8030700500e060075030402d140000741b0b4807120710303507100100b82c0d170080504010440c40041003090713011074418014201e00004104010b024003405050380300c0103000341907a9424200c1d9205400300c5020441c0d02c03003400c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 951493848 1250 951492598 951492613
    0x30b030a11040c0309050601050f0409080c0a14030403050706050c0c04061e051509013f18030c08090102031b0106060905010503041208100803160c06030204030b1305010e0f 76
    0x146490302c03e603143d4030307401d060074040c03c442c1d5161a0b403640c0d014030a05003d180501c88002c0c490b074450340143c1e1041da100b0441d0342c94600034211030b0354800c9006011101002c0d4128210851784000081e241181e41c020001c00109003445802c03075060300107240f80c1c1c10301d109440345255180d80c0e60198801406540740249511602c00f040c66001d4034042d400103004544400034000700c000e8400072034900400a003010101401004084c1d180004074500c0c010b5456018007581c0351110b5402113a80e8021505482403258010100101c0c14171000d82e90300030013245190002c000010002d202a2107240c1050056900b05014041c03440d528180f00102c09005940d40e6100303100a507000458040507040a1805c5419480c283d0b89551084500c0f1002170280552900010401c450802e400310107825078406aa0300c510340e041d02d4803111100d158085810605440012a01c188603109450403a60443d518410305d0700c90710704d20004104a100251402d54a0742c5010503401707802c00070303600300514650043c60305d03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 951495098 1250 951493848 951493883
    0x27021c0b100c080a0c051504120503190e0304090c111e1002030a1503030810060206060a06120902092a030709090b0d02030d05040603050c0406050415030b030a 70
    0x200c50280c110284591941c1100c032006542c04000e44940e640c0c0010356950740e0f88040c2e010355031900c07807a500030f20303511aa142c0c0d0241c4c20300c3da1b034410b400360b440b0710202150011040c0342543c03140001c561204007480110200400c210958000591030083c40c02075910702074903400031206070345680e607156020851640d4000d035450000c100c1c40e45c802180b0324102c1031181d51080700d240c484030502900181140c021020611080465000106480d01002207070b820075524900030340380c1c200c203c2d404074030901c41d403030009027140c00424102c3c415940149840c0c0d41070f060607000d840790001c86503500c80c03480e80c451240c801601d400d1542400344001d0200504d510032400742880ea40d010b030a14a4070002014014000e10980106200303040d0b5251501c0070030710781501d0002c01c03c00404044065450700c504070380d0a40440e0058028015200709030f03018445e56848009111452003203201c0d500001c1d2040004000d040b801942c5003003c540240350204009044400182c500315120b0000e64040384241c8000d1725 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 951496348 1250 951495098 951495101
    0x9130f2a0504200c0c0a0617092e14071701060302160210050d050a15080601151808150f060d050c011b0501050f100503070f27021c 58
    0x104411182400b034101100d190b03410300f10505040c02e03220740011410054900c41440016102c0c00c01424061120b5a40ea90040241d100c41b90680419009100800c0003120085034417004520510030000c0181c41c10740c10000340207403d80382140305c1591400301144081d191346001c1e000b08100d949100306d0261620400f031800d00184d0201d014503104000c408080210709142806294046170100a5042001c03c1a121032082203005061549440100011802681c1c80a8454211203140d42644e40d242e10501e80c0d00d076002e0047c3d5030501d04044030001400e210313050801c4080714101d0b10a49084c2da46104900c0c0549100100c1050064102040900d20410a99903400b900c12100c40307150a40c213458517178440d490308642c0340c10803004c0000c03029941c1b85400b150141e01d50100c000c001170301c0e00c0e840c005511442a00e00b400350500e032803800506858000340201c1a5003004c08080000c41c600500d454040d0300030f6484d00701003a02d524900704030340464805020b69050321810218014100004d810 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 951497598 1250 951496348 951496433
    0x3120415090e1f08011d01060803090f0402090d0f0303093822080415050c0d031806020c0c0103111303060b040b0306071d040b09130f 59
    0x80c01c22655903002c106103042c2c1c0b2030158001d0040348445598060500d80400c4075401d94108407030940c02c1c44000000101d240360f0801500c020f0b08020403040e511204210f441c2c0c460450720550103890760012010300d00c0c05900070003213820010410014001540d9515081400e060000e0b000b0a03524044078003881008203a68a44229602040b42c111070000314220419800d80f070022140010000000c7d00d190104003016441001c006125041e041130b440e100c440d0b541b00780500f41c21614007039949a6505d0048066400404082d00038040071a0341070012070041036000c0d071070303031042104a80c0d176004191103100902c1b085010710080e0082135140e03070014003951805080b15810603400c0002500500502c0c44210959603c442c01240d8a00e200c000280505491501103034140201740070310a4050b007282c8408400810286801c80e84048141000700702c890045906801c0070316000000c480c13002988950502130f108a0015420360340c00d480e6800c0b034408421400c2020a504076006407040c1c003200c1d824 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 951498848 1250 951497598 951497639
    0x4110a090911120907170a0c05030721081c050106180e01180204150806190308030406180507060e03163b090c0411120c130302031204 59
    0x7809884000658901d040c03160304008108901000b0210380310b140e09005ca640100440446a080b40702d00700152622048081000c5910399109840014103081c00702c2c0303490480f1400c9c80c0c602d010841c0a41034503060504040c0031504844100070325141003000c610400c100f008207010001d00396040801c09010500c00145c9940a5040d40000300003401c0b400011906544100d40070400002140d0f400c1c002901542d04a00f00c1c0b0034030321624124556112400034801c0004903014100030102c424000310014035800058043e04007000010085041a000140b030740740301e440d01040c90348664480c24208961900034500040c84281c0200b12071a04011041c040c059250610a00501e001c80100444510702d80004001c444030100f000801034202d58000c03900100c0802d0f83c603502e010400e0546800b21444014420b519001622503507000750740c00c0e07980c0307403088060800341034891000403d900d800c0b00a4a0940209076280071005032802d01c02e0150010152080315111070400310101641d25405010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 951500098 1250 951498848 951498851
    0x3100f1e0e06061002070b07051018050307030507230c03010509160311030304050306040b061e030a030c29150108100b0306041d0c0f0f130203060f04110a0909 70
    0x2890740380401282d16504540c044821034101080c084080c1e0034a042a4014061880042809024400c020545841e5071b04040800c00880036901c0d254103000014038400344c043e510600c40303080028003500c02402858021480000c0c02071410081c003440720040b1801503840c0d089903c948855007824016260480200c4002d40300036000341ea03400e10f03c41d80e00d21015002a89141f0440c84a03181031044030042c05000d019965145810b003000c00d0b480340f0a0325002e005000b90f058212414070140e0000481030313002000741000c00c2d100c2e20f044a46809596082d2029010b00c001d480b03006070250500e0760058007095200800c1c1c5402000c00038042c4000107224180100039080012a1058100d0f01c402d8845084203141c90b9103c21001c58014030a03900b1804080d0041c00d100c602811000402a200400803501d120040403140107000d00001c00f50b1442d44c001d01c0720300f07112000300e0060700034592100340900130840c0c2990398000141030f82c40080659042100010b05036400b9607000340440041c0010110 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 951501348 1250 951500098 951500111
    0x4050405010218060a050d021309111201080304030327170c03060a05010806040b180601062d050d18080a18091a09070203160b06010306090e0309040b03100f1e 70
    0x178080c00d90b05c154280d03051001c0d400138503002c1c21082400000007414400740c3c1002400d081c107080c0702070350f803108000408001c1d4103000080c000c00c002040b07500b43c0341d250343d8117425090540890181c5000d025004a51001d500c60041065105940a9000c07000303140c1c01050412022001d1600f0148080c06490009081100510010a00140b03864100b64030107003c03059599500045580600700070507000450240000018242d03911a10540750100ca0302c01c518001849012004200c403201c1c1c1e010400701d6410b00021506840c1039009202da110310071b0107807007480010b0b41d40c0d0400707074446051403010a06004c4035060382d440c034400020140003002000c01892070b8640e20007010840303c0709403e206400c104001044240b091064400101c40c0c841410141c10740d500d85800090012259140024580100003e0a11042c040c10f5600c41c1c003280998170300760342801400003900c1d01300d80c915003621401c280c0e000c00356140d00c24884252001c80002070f0702000720480105000050004007590b07420002c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 951502598 1250 951501348 951501367
    0x504091107020a05100210090813050603041a0c040b0d0525080c0708040e0403080103030201050606040e0117070e010e0105040b060a0f27060c050d0c150908090405040501021806 78
    0x4a070b4054804c101e803044080035601071300328980712070702820f400b030f140c00c005a100402003c4009042c01640b64000326200b2901c074000d1000314007044901030005090a0220360050220a5800e1303000181031402c4ca180c10384070100441d0b0b6503c003e41108036140e0740e0040029108402b4501e207164070030028000c04014400100800ca000c1c060302c10f00030450009042c1c01000b0140c0100c40040c042035a185c100c0c0c0c5428100a02008424072080d800740d4240000140c2d28500241101c0036030302205102c040300e074204078120311003901481c45c1c2c4140d80b041c00801f00d841c0b25a500780d14000e18114041d8109581420103020507105030100c6240507031000c0c440000d0b0280c103c00081078403031051806211207120310110720300d64aa00c50850306d410006000101e20780da40840035510700c901030790071110541d403980001c484a80290300050a01c2103090500401038006800c00d83d40103024a00c6941006500b03c00a0120341c82510100c684c1d0394009051000c04150388400350081408860a904010609 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 951503848 1250 951502598 951502609
    0x5060a150b0433050d050f0118051302060c0601080d050403110111100507170f0f010b03130b01171b060d0b010c08070602130e07140901030e0d050409110702 69
    0x6002d8001400c81c44203840203203079250040078020f0481c80704040d070f02c0302d20034101410a6200b50417076070380f07142083c000640c0401e030004101c0c101c40802031038041d02d5640301e101e240104405000011075003170151803a0096034603203025098000030003025200e00e52400c47c080385803c4c281c02d0700c1d8045c00018401007011235603000b0140584102030901030050040f0b407a200e03040000b5510702c03400c0302e0320701018400c83c00d80c05691141d50301003001081040c2d444070482060140c200300c2d500303506001e10200600031701100308040c54100c107100303448610200c0c4540d40c0c440081e80c00d80080300c6010741c0c41200048160200580c01c081c0c0c810421603400105400c2c0812214890b2552815106880c0c40301025940d1040e0018030b1043e40089031240c4568003807900c80080e600491903850340b001040000f0800101114440c0e005100c0354441124402e0140210b452a0b080407050758140355907a4100c003030580c002d103e55081644150390b901d40e207a00303014480049881e400d0f400c4020400c00d001c03160050710750 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 951505098 1250 951503848 951503857
    0x602030907081216030c0606030605090705010c110409140703030302191803141014100602030c0316060608030c0c0a06021203180304051e04181505060f040905060a150b 74
    0x1801c5640344280c01d030400b40ca1411b10300c1801040c00f4640f034000414860310354003d60154030b406041c1e81c5015511001103c4083c194240030744403078260a031401d40c43c40c09510544040744286921203036030315000040d40c1060065801071b0007281d00002c0c00f50008441d0755400700001c8030f80c1072444483c810614021340d001c0c000e0000410401d40320040348a0f03940300b04060441030140c0e4006212465003070f00c0f440e02d00441900c0341404440b100e800881c4941c00030064407840c2d8a060300441c100340d13050700070821a070014032050700d080d44e030340c5400b10b84414140010580700c900140200a1a00f540041c425100003030362090046402c121441ca803079071652011aa00010f1040761000c80f886150340c924218425940286d6004000c1920f4220307080c0b65110003002880121010080b05541200300150640740c00c0b4000d1076945111a03502100c2c801364007087d0030070b901400c001c18503182d04022800300d9440100941d40ba40c8810100700e6080c95600401d50f01c06c1d20000c803000b0b45450031f21070070058000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 951506348 1250 951505098 951505117
    0x90f03070303050a0f0216061a031b330304020d0605070807171302010c05251503020331170408280201080a140a0c020606010f0f0e0d06060306020309070812 69
    0x8a4080540d01c184200000500500c070080c05e80d2582d031061480f141e480342d01049a24001c4800c1002c10b0f40c2100d334092481002c0c2e14206442054002640c2515125440200200c0e4419206218000814803074032600744900055110003480b4103168602600c1e007000315010010010f00542049000d070030442c415005181d0a082015580865180803402c00140000c48160311040c02001c01407000410381480440e4110700c00c1d901c194841c4001107099200451300050303a001e03220700e18601c500030103901030150441200700d4601c100c07240d914007800d0b10801c00c00d1112010041002e000b180000d01c071180c0d030040c04e403c44020503041d801100d825030b10316a0020b030503c90200001844284583c01c005440891003d02c186280b41440b5402e009120307440203c8014800d81d000100154090482140c1540716611441180c2e21490422600741007001041504010038040e040000350b20f45c0550030243d131107140096241e240c80340c0c5007480c21809034000091507015080c4e0300d00d89403195040380e08468 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 951507598 1250 951506348 951506351
    0x1b0a021f030b03010e0c01080a021204021c0507060815030304050a300b07030f0b210106050d060606020115120807020402040b03040f03080726090f03070303050a0f021606 75
    0x2030403400c194010007003071091641550031318040c0d859640c000300301442581d600740c9031100d950300d40c26103c4080b0f00900405124100c02c0c0350100340903103841c2000072041d410540386140342038100e81c1c4250401d4200e81c0550f0101e0281d2040c403207101c1000108011824081d00154107161a110010746c0c902c2c940d100304045105104690342d00000300000d13200e5018958528000700079040d2400340f01c00c4100b1503201c00000d1620500300010840c13805030010204006000c1e0302142d483c0310720080ea03680c248c08220b400390f61710395002800303440307001040d0702d00c0c4d008000001d0380d1403a0440c042e0968002044907103640c140342000340724200e601400c840300321f80c00024144d2250740510100c0c0081c42a60400040c0400c0030080004102024008400c3c541c0300340d0f140840c40d1a9100c007540c150b04601e207000c0311140781d520440313140e1b81c40565480e44001968101c4004070343d05060542194030601082e800039440704100711401c1c149028042401c0a031503000c40c1780c900d10004d1f480000c4010700c0d00a1005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 951508848 1250 951507598 951507649
    0x1005030c030c0c030c0304050118080604060b1212130b0c0604030c03020a082b0e0307020d0c03081b06071d060a171501030608030a02060129030403051b0a02 69
    0x41c1c0500b0300356590910b560048969442c140c0202d107581c0c0c0c20030b20031603001400c0e09818016158150000303d003280d00e07030802054146c5480e900c2c14040c16286003584e40009001344002d81d00d020420511400d0f00c900d00c94641e64001e652458902d112098000700c0501c10308220225010b9000580940d00c0b41d05841d00000da80c0c014078080381882d013041ca01170411100071a42c3d03203628042c4403020f0300c0061604814803482541c001d0400c01d8818114800c0d120360024084c040140c140310b4080800e0314890311850320120341740d61714820260801c1c50f0203040344480c2c0501a40c1050104526030f000002d9003881c0740b94452403c3c00b42c800100308000c05019160105141c07001c07500030a2000c5030310500076101a110710780a6030f120780e0f074220702c0304090000b0304040c000250480040116010001c0503170142c407042c3e00303220201940d0944144001141e01c2c00d90040000640b0107000b46014500c26980c080d0f44407070030b11000d480d07841c01c0380320725210380c112100380c10050f81d0308211160001c40711030012404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 951510098 1250 951508848 951508861
    0x1140421120c050309010b0a080d03020c150408030612150c1c060803091305040c030f08160f0c061707030c09030f060209030624040f1e0606020c1005030c03 69
    0x9840807200201814140b2907482c0380140c1203800381d4451003501000b08420100c0d6010460306c4081880303107445c0d07500079a002a4050380309400070401140c0101c1114240800d4659020318403078212015162910701205202603032800840b07251f240030b4880001c2c54800130341c2c2c1d00d4182d142c40c00b9051481071000043d000c4155281c84e1002c3c00070042c1d061040010565500c42252030b58044d101c840d10a0703d180444841c4102a407107442d006681228035a5a043d04580d00c20070100c15030142900e80710010320550403401d80344007002c806135106500f8801e00f881d5501e8045807850b4942c2200f000d20011003101c0c0c0b141040c0c600300e03a0340201d071450089035444001e80f00f525149442d0300007512000b4010151020301c8003030340080400180a0701120784950b54031141c981d0900c0d612040d101644480c50b01e0030300c03a00d0a5002402041c42c0344d400040c01c20740111071071059883d00c0c0360052080e17840340400c100164041c40a21011003095500081000e80442e0040c428480146188580940400403e00307 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 951511348 1250 951510098 951510107
    0x904080a050d0b030d080f0711030f071b030c090621020103090c080f010e06060904080403030c060f021911030c10050c090423011e0308030403111b010201140421 71
    0x7071040e01800369945d160f04114010101101151a00d110f103140201003154907200b0400c006949591344051030424840d03042102c4240c1c4400c80640e00c4c14020103400c0e00b940c0040e40a50007c500c11503030800483c0c50208407200303682040c0c0c048209007079240e00c88000c403120025400011642444c3c0010000038900e0601c00d030f641c3c0c40c0c003c1d010912440f0300d40c1207541815405140f0035403005003110096610b040030445040700031178000b812140c00741310800c000f0b4040c4103401411481080040340301014454032034100c0c0c100c00801800e94690301400c6040c1904200c168a030212444080e506d02025450306666600301081480b9035555103a0015101d403400c01c095440d0f03030074001c02c107114a1036a0990110800440c1200000250a00c2c0c00040c0700c5100e082d030250381072000c03940d0207811869900d603100e1075000100183e0502c9902041032002c000c007446460301c91045907000071156004140020700710b031040c8591810301428401804041100c6d507030b401d002002100031880000300030840449 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 951512598 1250 951511348 951511361
    0xd0201051e0a1b0f0809010c0c082506020702090a0501240201020405090702010203040b180d1110060b040906060908120714061e060103020a0e041d03040305010903030b0904080a050d 80
    0x2c1600960f580300344003213601410440328800076a803800a10303241c183c1c0103402c0b60700000c0303040f000c109100c0d500070000c0c8500d4082c01c8030074690300c2039014524448500c0c1400c0c854010044030103d9000485404528051240715004845988200490341c140503c00007211010755032804c5c84950241407484480c1300b50116005490040c000640f68101204040c0c040d420644007240d11600c4000091000e69220002d24103c41d02c640050181503c24281500d500405149044130307405221010002c0d801140110070081102501d2207684901d002d1001c001c0342d0403074020800b040541c1c0d07000c1259a5001510010001500c6143e40c0e64021900d01941030303100040f00c0b190315019290402c034a180d00042103100c00324090360b80d02000d03501c2900460407889480b01071804500103102c0107002e420503038810342c00190404c000054610088903042d03c0e5410951080302c442c0e45030b008010805602d40205440300909881d6643c550400350398050f0103000d514441401c101c03000c50642c5c0000b00d141c1020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 951513848 1250 951512598 951512621
    0x180618010b2805030d050703052809061413140f0d060608011d190206161506090b010915030906020409140903041d04050319020307050d0201051e0a 65
    0x40c15504105071040c180000b841d595080c25200c2e0300000522400d001c1138000303950b00c2540d41c0611f801c0c051b90302512290890032405504c04d0303884018110b600c50714070304008400700c0303500c401d0240c5d46415070042c258022510007003118042840a810844902014401541c0b100c0960a1107100032001280d41e80a107082c403186d000d61a12290404c1c082c05078070600641d42440c00034426281e0340c40c042169252010040035060f801030038207805414407149002c40c02c6d88000c05a610780003001c85c010403200340b60042a9020008085206944001403151000400c4001c80c2401704081c00000a01282c81901c00d0007a4900c8000070540064801e52140151940c400360454590303072120100d02c018284080c085903c0d2940501081c0101c8001064034100c88817600d0030074131004c0840d0f0642c04004082c3c4100c81c40e00c404e200c0f4000d102d500c003104281d815510b90040d91030390444d0a046250034038050500c0150791400062104109010428901511382c0c00d01c0d50203d501c8002244000f800300c800750 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 951515098 1250 951513848 951513859
    0x304030807030e06030c0f03070210051501020105100617100819021c0809100c02040e01140a0c08161b1506050a0f09150312021005180618010b 63
    0x1008104001000e0503030a0301a0743c0d481c0c003403400c041c240000ca01c41640c40a4501c0002e2000124500c080c0c1c00035644028580706680c0ba140ca00c500d0842075540c240e5010304036049054400c103c5581c24030485030b00c0280c0e5807031a074200f45406400340c044202060b85500315461200001e82040f817052101d0700611024049410020410414640682400000b24810344ca01514103510a0852984120080c3c2040e081881c2510110402c9450002034102500740600316203c4800350703071203200c1c00071741a90360b80000ca4500106034505c02c0c8000000c08444030585048103d959242d030002030554032900744201d00e061016410819114803044040c0290105451042c007030820583c074140204c00610725009110300c1d52242c0030450b000f601d5014585c8081590042000241103540101c071040034826181c90301030b5144d480d03441ea40541c0d05402ca015030b00c8408050041c01b85849450342c4410040102d44d91140b17406040d80d207405000d0510010461544070041600000b035002a0011b00300606 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 951516348 1250 951515098 951515107
    0xb1b03120f2a030708060103051005040b030111040807081c0507020f18040c0f051c0f06231905040201210f020c1c05030c031801140703140610020705041d03 69
    0x60b03400581e4812a48080050f00b20400b0440c82d501030702039140607594403400c081c107190131b0009200092800a200c20303411364a89d551604580c5000e0700400141c180440075002c00c600b0000c0d100e28084c600c42103040c00910004400c80a180c0c030505448083e981140c020140c80404000110320b0040019a0342985416805000410444400490444440d40c07c0d80c080150303920100520045200554844d10007210a403c000032500c0c0e501d28042071040e07000080724100107940d40c000d000101c000421800c2ea0b4020f2055000343c0280502c00d494907520148003614007a40001d00718124040b8000b615051607038002100121a0000740110031049000c64550341400d20003075640c40400c0c04003801c2045c01e00c1e4665141d104000303d07403150f0080c0c24164a1902e4141e209800d1042c20204801c9555842071030076685061442540d004082d65980803441d0f0100300d0010005d00c00c05440180300e00403c0324880c01094020805d10122041242d00059182404002c3c0c50095480301081c1c000d8040041c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 951517598 1250 951516348 951516421
    0x40e072313150f020d05030105030709020f0f21060607080901110127150c27050a030b011e0e0a020f0c0a0804030c0f1809020103020903070b1b03120f 66
    0x320300340f0403a54140d08440300c03c0e01c2c4a9055a60b80f01c00c3c0119a095006407009120044d401e800600810b190302c41c10900e0b080c51450748a43c01c1e00072a00300c64041070344001c200f4040185160441d0440b0044441c50f14103085079440d0301640c464420200e0500804034000d8012a82c00c0d400900b0303445c151003155021105d103040b03030b0b208101c081d01d04689211003c40f44040383d540a1013480c00041c415210308480c500042100c0030300c004400d61001e10350b8010000403959171151103065000354401c604913249541424040703d0000307a911203040602004c541c04011446034031003019000300040b800141d5460061742c124000b0300c1080b000d00f404c0e200e5240040108065813006004580c098600c80c0e890b5034407085010004c041a200f0030042ca03161540c00f80511740c065003c0b4501602c141030040c03810980c000407a0400d4800d0380020b11074040801c902c54020386280c2d650f04e601003060040c510340360061100c202c0d81c1101920b2040c2185c100700000310041089640c06c00880140d500c90001d003a51507 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 951518848 1250 951517598 951517607
    0x602030a0f2c0a1a4f140a051e061804050903070506073b12030c060a1d060109150e0f0403180504090305040e07231315 53
    0x702c0d1882c041d210407800080c81c524107260401c203100c40581420f2030840150f41c40c4200c040034000300342d140c005100d0404120481c60f4480071130544040207442c40b07520b041e08010b14008030f640c403401d28504171600c2c1d0b1240d907445050250607a941140d81041e2261814403045044a604c2109500158000355503840000d440e0080724440c04102c40c00e100310b5407813185142d124014414010310700c0d405000420744181c0100a210803d0708401c0390740d6041c40940401c80312500c0450061300c0d4514020094242034145610b1300721001c1855001945020142c2046940c3d426004095059555a403001804410071440c01c070074040f9950300072204956180d030300302e000410070a1024280784040c4172001039000d0710f880d0483d1041c1d50950050b90107542b1074509490303400c2400c242d2502d0802c4201c000c9125600d40c412941c605001c0e941e02900d540c1054102c20101b2005003d01d018800804090a00d440c85100300d0091410382c022403d0702d94000040021402803582c0200341d1740162a9100c00e0b066500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 951520098 1250 951518848 951518927
    0x1b06120a02190c020a0515031506091305090d0504060207171e06011e0308191707090e0f0c030412090306090605040b070f050306040b03070e040320070602030a0f 71
    0x1c651902001b0fa44804000c0d101d01c0144542c0321a00c0e00b8000602c401429442c10580c095024000518ac0b00755100041d1b24024140000c941365681d400c14442d004104015042500b1540c3c10502c0c80c0c03030305211020303503a00000c0c840c103135540b110300c0c4008100703e4080c0300c40c0d440660140f10000410305548209038851030309015055015808440c001410520b03200c0c0c82003140c1d00301c000c0c58640030720b42881c80c1c1c070140201c030390f0001d03c28003a649010f60b80c2964a410b00c5440306983d4074241508000e144044000c015080c80301c803449040500c02030a21080c112034000340c1c4862804001c000040090b5450790069101070034007441e0843c0001889244e412042c441c03485152620702c0d039600c940080c1e520301c04c0540e400c03001600030310000e6102d090170760050344182401400c82c2d429a0f42d864003140360110449044001840401c96502e6001c500400f40b213480b00d2180291551f0740c10504001d6607805800c603810304120603207100e4000280140e1071204041118861502000e03175884540385503010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 951521348 1250 951520098 951520103
    0x90405030c0d02120f2101080309041a1f1806020106061116031b0810090c08070810050c0d0507200a0317040501021c05091b06120a02190c 61
    0x301c0075a11200b80c40801c4030001903041e8440399080298042e0040d030b881d000083c000508801120390f4051080e0700303040c0c003402010a031004660742c1c41031a0601c000e440c03074079842030310300d9840b000c02203102e036a904440e041d2007a8107041d24003d0900e401048400030085500d6071031811784203c0200c0c01c540d042d04400203072000790f21a610301c46143c40d812a0358071440703c40e2801e41c480c0c451003400000c501c010320b680489140c1d103c0042c41504d034025542081841c212040e6401e0f0303210441c1d4200081240000000c0840c140a80616464010040d45a0241d01003601c6290380d1360000031944203064054521148580c141007000785002040036080f8500034407502080d05165010940c1214001071040744035602d80d035042c0f42d0a0310340820180300c3c071000d00210f40300d54084c00703410030107405c50b0140100390501200205480c00e0141034203082540c14500e01c580860b480d01e0010490312900115122140c0040f10b0030705907560002c0c184c009006641540c6940045c44c100f4000b031541c4128500707130050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 951522598 1250 951521348 951521353
    0x30308091204080c09100b0a0203030f0114130b01090e01171b0a06030908070f0c0314030a05030412020c03030d02070308061c02010c06020909250806011b02010c02090405030c 77
    0x40c0aa00c070030407034007440c071581000350301c1612610901e041a41c9126040409071440c0c0c00c032952203108503490b5801600402c40180c0c40801040030b045060b0740201d004041a000c00180300c110756011961402008801c00e1500e40c4130f41308840130713900c120031031030040500f4000314200e541c4404050030b50340c01340b81d02e8505600c03442d808543c02d80c1c01044030b002c8900c070042426034014a03129040d0040c1c64841e1050720340c00010300c85000460040d04004480c18400d1441601d29400d519040c03070407516a28805080742e1041c04110811604401207075005600244990025540107204034908a90b81c80c42d690075004c045021181c3c021250054640f040c0300c0e031906262550340d901440100311130710381c2d512082c5000c98107520140d4010240c6c8a060342c011003001d4680b880b002d0214800e4201998020000c0284402200e04468108101032207403615203483c4105040800000301150120b064401070824600ca00e9000c5a0003484510282e60740640031890700e05d060b00740b00351a40c020145009550 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 951523848 1250 951522598 951522613
    0x209040308150a0e070e040c1b2409050f0d020307140a02030a1103010c0c1104051906120b01051818100e030316080c0a0807030b0d05061006051204062403030809 71
    0x5141a00414a4100059588034102c9c9034021203143c0545c0e6048050720400c203505c50280407104d200424012140a01002080ca01c2c80c9107030040c903114100781403c210781c101c21030882a1310b5000c4112042d094000a40409204014183c0382c100301000384020340c944100c0d940142000008810241554021802004407840901d42038400d9402184c000382103011180c00c680c2c5901e010382c0159000201c002862035458500318a00c81100c40d81c0d0003101030300d04001d21800c1004000580d1a000d054160f91340107610341882c0007441c0b00310014003408510704015803200d0951100300003010b1001c542d02d0040c0003081b5401c8010381c59520941da00e01c50022840f250310f81c040d00500c881c50042c0082c0120070724103800c01d4000c590342403003d080c0340c00700f648400d03001900c2c2e500c0184c12100070740688054103240c1089002515144101c0d444503050080c14004191484c60030a0741c19071164101c4404101004048070641c024242101e00c058040341c1e148001c0203060f8040440740c86540c0500458001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 951525098 1250 951523848 951523877
    0x17010f050a0207021f0c20130608030d11090a3210030906150e0a05010e100b030c040302090f01170a230c1225030209040308150a0e07 59
    0x981c07142a1002e500300000e8038400d0301c002c00c60030a880118000c6d11b49800c070000142d9441e1021050680d01f45015001d13100301708040c3c500450244405035481000708900d0f407422610070346900a481e00b000f11582e90f1501070401c1c250300c2c400c966103110014050400d464650b1110b040302d125500c1d42c00e030050081d07074480d0801130368480c800101640041500400200070003040f8003518140b0412560191504404840c03d0180a503400c058031004024040c50316001d8056000c5400c140d0044548000c44020701c541080f064180400b81e40705001e00070f03503036a5900703100c40c11481594402034212060300c0801504121100e2000d060380c00031070741e210b82c01c0e11088101e5036444030800d0290042c44c40545400c040e211008842c1801009802039481c6106503000007a810040c0005006807900450906556020403241800d1840000a03100604600355004521200c100070401414042c17400e02103442c505808201c10302c2c41d071000700fa05041e84e840c0d41e85080642026241000460711100c0d10400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 951526348 1250 951525098 951525101
    0x101e0207210203060414010204050d0803070f0215011e050319031101020711130b100203210c25080f040e01060305091027050c0a08031801030f0617010f050a 69
    0x10a0b400600030041501d50340c0b900b1910401038030b11390000759800c001c00544c0c2c0d190000c00c080042d024440c401e499142c8400c000e4220f0f05440900c10840d0828005003031b0034045140c1c01030640383c0052614024400001340151840d41540000358184170320308502c600a080400c03517240c0c41d4440e030741c2c00030400b001c40d402074213038002d51400a005080d100d010640e1401c00002c40c494400302c400700460f8004002002c10605040c03250300340010f0308009842110f40d0001c44140c2003c401c0c5030201080d61400301e00d40c60040c0116400b100c1100900e0621080c1c507821481d060b00048c0d0003001c515a50506046802000d500c079220314902c1c080410000501e15010740304140c0300300c1007100501860604c162680f0000c2050401e2501c464004410740004107070700b01302400644c2d110314010110000c5880420003420000d41c8042d055034801c000016144114116142c0205d03401c0c00e0200300008440640750141031030760401c0c0f44080c4603d02c0056800015040713001410280b0404002980740c0c0c080140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 951527598 1250 951526348 951526409
    0x9010b12070f0b13150e09130b090703020105180a08190c0509040816021903240b0a090e0a02060706021c06050d080f0c0312010e100302090105101e0207 67
    0x360384c06001c0d400300043ea02d50f0300d4181c0c81c0e070050b1030441c03154580b120001b001c401c0180c8000d0750009403d00c02e01d04000000f1505608014000028121145150b000030b15520840759035244000310f404615145880340b01142014000c104113941c0c007502913100c40d00480c240c0c41c1c2c040e81e8480e80000000755a06003c2007072401130b1b4000f40d0300345c600b4100a410000d4101a0402203801582000001554039003003038920000c0d40c8200030a240c4c401251180d4050814000b28070407440f45060b100b60302940d1550307081c00480d000b601d80425155102c11185080106094001c0e40005000403031070200001c6a004000074000304031755100b40a507050002e002c940030303800740d80e401454403144107000c0360005000e800c00324086842146000d07000e071285415508000700c0c0c8600c2c840c1000040c00710030080104030b0703407081c0d045204010207891600002c101a6041c0f2aa90082c0340700580600d503d44124035071080002c41d00e8421200ea545080c0007940c50f45c1c070340b0901d0a4601c5c004102c0d40072118010906 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 951528848 1250 951527598 951527617
    0x10906030210032d061715061e060a080105240f180a080f070e0c0a08060d120908070608042d1205041409090a0b09010b12070f0b 57
    0x40703440b10b075404002c1e0010074107101c4070541d2080c3c0b03030101c2d014640c1c201d03244001c608080c80045203c5190141103101c80c5101d210f0142c403174101d01c054015503400c04090a0b441441140e413003e41ca9080c5080480c0900c08000a03900054002039001541d83c00c05803841c101c59081d92100d4143c3c010700050040c1d070303401c403201e01e0440b5410400141e800c0491130260903c4607825a007020055550b43c0000c4041d0925408410301d0340101d680a1845170041c0006001855510400c1c5007514095828824a01c81d14004009001a002c0410b1140d104c0d41c0f284007040342c2c0208c181e03039402450781c2d0151594540784603004940c4075100000c1246441201c90368000e643c0f1620b9007a181001d61181c104d20700c2c0050b54000a10b00558004001c200004610502090300da04d6035582d840c10202044410b81455520600034045201400100e03080010b0b121282034000e0344284142d100c90300c000b03014000f51840300d58000540c1e07860314207021020400780100c86100f000d400d280e65071080808110701030051036 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 951530098 1250 951528848 951528859
    0x6040b0112020c07050612010f23040908090d0b01080d0f0215130503030a020a0201110f07060f061d180d08070c08040f06020a11040501140d15050c0a080109060302 72
    0x1a0341c09039180350060200c081a8000351800c0c20380703c0300410010307009640849000c0000310f004201d074042d41c0311361070301401c0e00d540c3c1e01010341d0304000100b002c00d0342c0b22852800355565602003018403000f00e055441c001c000030079403480c3d24002d04111150f82000c0c020b02c8002e00030442604c45003801001b1404000c0c0807a00030300a580c1c3e426880d0070a00b600208151341e56030808804900188050006500c66144c2100041c0c03500f0028800a0031503184000070720462400f000490b681112220a0f0781c4165480507011861000801c03082c00030384000d03401514105240c82d81d03140035900109204d07108000c052000200d03010601ea80a0395002c4640305400410044004101c4103880742038401440d6000d05001840d0543d5954500c40c6980b4543c040c1c030058102152a404110714035080d0381e0483c3c0101c800b07000ca541481d4221044000c588026882100008010340400c440c5200074503c0303d4910804101501d02550000070541c4000c000c1c01c0014090000496901650f01c07405c07064036000b030070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 951531348 1250 951530098 951530117
    0x1206060c0206091c21020c3304080106030312270524070e12030f090a0e0f1e0403021504050316050319110a170c030f1206040b01 57
    0x280040c680c842c81c095030300004040c8000e404001c0d010211102207120340c1c0300050001d0b007110000383e550040e05d00c034021500540701d95180d0755a007103e001107140c0800300090b03200c3c1500f95125841e070380000c1a40f80038400410005403c20065004504485c0280c6990324101300004a0b00c007220090303008040c0c03950301d81c0166204940f83c03403000944240304008441a1440414080790b0084a0300701801c2d1451200080007019641b0400d031004058061f1555400c084460a5481e01ea028034a107031080c586020403c01e8281d5101d0414800515042002d08001d040c400314040710102d0888000e4a0124425010314050303115280031449140c140e03014200c02901000c039402050805403068406100500815a81545007030702c074400c2c944100011941c41d01d0075140389865004003105030040c040585aa8100103102051503a68580d000061041580845049020f90b000303940c1454901e20000c1961a003180b1014001d11650044008001031941c60700200400d803007001924074002501684e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 951532598 1250 951531348 951531353
    0x10f0f090209061206150712030e03090901030201030e070f24050c0604031d030f060601080a180b07091a1305100203070b040206160f0606120c1a040b191206060c 71
    0x90321600320308000c100418004121040081580203450282d529048c40d00001502941501c1132400c00d05050001d58202140100002d0303454005200180c1403607261228845640c0782486404040c10002904205541d12014a04a000410201a5001c40c0c82d50711004140c1c0c0907005844080c0b0315a0010701b150340d1307a9a0100d075001d0807000b00910b81c00c0c05100c0d0400d1580d05112094400c8440002031400380381a4000510010f0080c003052126450604d00365a01c111160b686a80150000f16008907522840c3c0c0c01c48283c21603600201911303e000e0110b00c41488000b00400e07110ba000c585149c9825114800c109524030f80c4814a000350b401004503000007010211007581c444d00042046003000004901e120880506550885900100381c080c4020450903109840180c03161410912230b0b10f90583c2c51802c0340c402400b89071040500b40c2e4600004d480410b0865020300006620305482c0c0101d42d0008200c4100142c54501042800c0c2101615041c0d500c1074a0840787e0550361482c0380072280c4c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 951533848 1250 951532598 951532627
    0x110408060a0b041107060e0601090b0a0b07020d050a03091508190f060305010f0f060801020403021507151a031b01140a05070206030c13090606020c060c0a0b010f0f09020906 76
    0x44214036040f903180e038110544070344e000001d480c2c0e240c081c0e0303c0411440b06080301c1a061180503041041d280d40b5184134007580b6298040c80e0015591080000c940d22040d40c00041e10384200104000e08074450710817507404140d444505e002c2240c00a4121a1071504c94460584d0303642c02c1104c10310310365084100d50300d0700c8d800281c0000b2420641403500041c203a0f141d85820b07088d00d0b46401024569910341d11000e18940080c49104000e2402d08001c50a00d815540022940800c00d8180411241c020401c20305104011014000602c0845804c01100e00d218002c0c0c00c0e81044100002e1080c012405043c000c00466100004c642c04169200c407a94180e010281c0d4094101d0440503003006028000d9800507110100114051070304100115169a590358022501d602e4540020200301d040020401200703400207484010754208442c8203881d030130b0810945c0d10345080420040c01e6032502c54000505039030074000b8403055481406981d1716464030f50241b8026441140c02550b004407042151156106c0e15 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 951535098 1250 951533848 951533861
    0x140a030902011101051f0602030c1002071509030323040b0601080a0905011e0623091312080601180806010302100203040f0b09180c0d051b0c010b0301110408060a 71
    0x5043c2034019030740c0d0421003801c48504aa6091010382d00401640400e01d5220303c3c10018101c030300c000c1d86046640d14225445d0b2a40a0b1500c00040c0c002c595030302000dd0203114028282448101004980d0301400c00401034040d11078560008a001c500b01c1c81c0c100d1001605600c502c0d001500c00c889511900c00449543c00e00408c8510899600c80c0040c0c00501c0c2070040c414900104121074480900510060089a140340d100300d02003403406100201c000d01002c1201011802103600d0789403961030104244050300f182c0c034002d10040c0c081503082a400d0b000700d0014010324081e6a1000320805055550186e07140034042d1211943c008001040189010f44601c01821000e10650b070505550b04960080807100390000c0022003008504103032141400f540350346403c11840d220811a040c0080f20303500a10a500d141c0004507111030006910800410540801c44c00d443e150555440043c201c5034000c000a45400307100b542041d05841900141d48242c0d001d966100c1d001d4442034950b410403400a001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 951536348 1250 951535098 951535103
    0x609011103090d031e02060103120503060303071e060605040b0d150f05340c140f1b090a05010b0f030901060f03030f120501061b0611041d07140a0309 66
    0xc21504010340c9803c00a00e04140c0300307890748051070a002e01890a00c01d0b000082d5003c40d40300c0401040032582c1103018140c02062810b10655940320710002c81d0541c031580300e01801c810443c104465190152084001c06c041c041c15007000710986413410081a26800d80899511100300300c2c00c50f0100311604c0700c030042000400e60004045046010600a490301102c000c0042140710791351201c1c451500080da9440f10702d4207141ca544444855004e04800d54481c0c001d4030340020f80290020100c070405c8055440700707a0034100d0b411a03400071610840480007c130b02d40d000d0028207001ca4a018854090036050f01e101c40400b9041c150b41d080d0f40354403608002d2031420503648030070002402d010742a445102a40c0a50745100701c84481c040d0140c50203640c1900154107c0c9040010440c0c10380c086507007a109a1407004841700410142420000380007007051000d0700050000300007449000d11804068240380900d40d80a081c0d9a4900a03a802c040342d4484035114a0100314110216129610030b1000c2403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 951537598 1250 951536348 951536353
    0x3010b030a030801140a0906030c0e10051011030d0f0b0f1203090105070503070605090303151c03081b030a021306080f010311040906020a030b03061003021f0c17030a060e040206090111 81
    0x941daa000c42099a0541e441541e02c0d02e12b18070b0910100c4000c0c44103da11051950951039a90710b4840440d80103c0d40c48103400810003000081003420000384200d8003520507010003800001c00191500d030086c0448031005105928041c00070119040110086076000c100e840a9410002c21750010740701644900c600311088d00041000000041c41446114042c85909004644a20f80404104e03085c0751601100d80c8140c04201010695035511030300c6045030361385450b0504158031110350b80042005d181c540840b0140d404030070800c9142890303001d4500e0000c0301c5a0081007950700c000c20707260305400740c9000c0c0b0500c112078014804a1902c0c1c14044886a000c0c20010f85004540c66103000ca07005808000002601c1c0e00350715550345801c028407500a21581e0058107054078650015002404142514004080c0c40d118180410b00840b4400c1c0200d400254021142c2c000700e1130543c1c03540c4116000c000c101e1802c000803400c011040c500703e11550303001e084a8a009020380055400000c0c0b000790300e1251 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 951538848 1250 951537598 951537619
    0xa0f06020619061d0a0506180402010c1511030a1d0a0f03090f0e06030c0916110a0c03030c06050a02070c0e040203120d06090608010e03031303050d09030e03010b030a03080114 77
    0x1600f048144e41d1402100941c1d04005003420b051500c00d60310b0103031a1034400c40106840c0c2a031800342d00901d07600a6130900b1b100403d1562031408000154581490805592420707515201000d0300000441c8030300a0b80404000303081100c03884528190086480440c10750100070800001802684041807040c000e003020705d4410f903621040b00001000f41c00c402d00424540c0300f4400c07541410010701c1c8140904881c0c6101619010720300b581102c46040c64282004900580710702c0c1d44505011000c03100c3c2c0c03c840369090454a0b4100034254481d00e10084449514020000318015618400d98032103540c0700710400e008525040b68072808603000351040c0e81c07500480d0340350280610500e00404030342c103115102158982c948181142100c0055010390389a9043c07030240d582c0d0190100441c0e0b88011000b2402055107028141101d05000c3c0d48203070500d440c40c1640800a26812020f241c0d1000012070090203d41d00f00400c1c952209051100100810200f8005010168016501511004003d810410b03034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 951540098 1250 951538848 951538859
    0x213020d111801030608100f0212010311120703050c0d0602091e0a050a0b0904020a090b0c060a1a0a09050c0706021c050705030c19031d07050a0f0602061906 69
    0x444440038041000700c0400200100c0026a0940010540100f42410002d591800d103203a52220680103011640310740c0c8600c541d000020381d505039104210b0440310101d9075a100d240580c40c0d100f18181d81c41c8160b01120350681650f90003d4914145d90f0312202414444401d202481200710303142001301d0f5141e400b80b00f058603030303110a88c0098000c00006009001540c428050100310492138010328081c00c1d9202e4144080490b0320121107080101703560040e0f0344e030540142202e4281d559004a4031a8000056004075902c00040680c010740030004204401c02c410210ce602000b104c0328803036002405c1a1003040160155405980d0004600d17400c80d181000594599080381d02140c800700d550103e03480082d010002520078980d022550303060407840c0d800c4c0b10040b22442e0140b402c94603400d0190005540581d8403a0b0003802c2e18000203424030202c12507041200382c441c1e04078040ea41c0940c2c8491070000d203a10b940c00103501100c09a4000c0c10442c4c0f01c2000d141e5481c40c800d6500381000c0c0d1214000613a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 951541348 1250 951540098 951540101
    0x1091a0a03050408090d0f03081e0112020303130e04050613120e1c03052205060f070809060705030711090c04140d02030303040b012904121403040602100b03190213020d 74
    0x1b5103880b071661701003154054603001d004000c0142c03201d12802c642e40d8515104500c01d0090a06499020303000040e01c407070500c00030340303107104480c542d10386010440000150380c00201030b0707107010300c1c0b1610507140386640f000010b8801804246006e4849825040e0319404c2500601c05280e42240140800c02c034001d20310700070340c044120079900310001800090030241d0b841044110300a40480701c103031649041d04e4600042d0b0240a11905803e02c03003000107a610400c06070170100c42c0b100e20090541a150912420a03039101c0e000000161801c180c0d0714441071191800000e07051140d100c3c165114141400c00c145508409001c0081da034218103001380140c00340e98104050740c8180d102f15800f69466041501074030b02002da119100b025841c002c1c00440700102c3d142e00740d40c2510480428007005501c00d003821b40d9107451004c03800711940800280820004c0d03010540008900500c0014801d80ca501c0c0305066850400ca80ca800c10b1070785a00d40c82006241420403007a03205001d0b030003d428000d0803a0081c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 951542598 1250 951541348 951541369
    0x509180108031b1504120912060e011a01270801050c09180601020304060503150a0b1806030603072c070804031707082a070606030201091a0a0305040809 67
    0x203907002151004801410040f034543e0407040300d000c0d0080030300120000c5484600903000901200320501c03059a076500c00c10040005241004003411041c545042c83d0f4003e01d00420040702c2c45d424a0020324018420050b00342403260183d45038209110320103450403508101500d4001102c520303180005940070240101ca0140282803c1d1566450900082102d001d000b28002034000908504101d41aa00403056404032026802e00e0341d075070796840ca40b00c0a01c1310303107150555200c05141d4000c94a00442c5000d40030041e058008a82600340410800000b40411209542d15078405003041c01180d600704820020103800d0400e003250350b190044130014000d02200c1c0c07180010425030810040c150300c05490071401d54074071840001400c0036000104801801041201040301649944881c52000f01d070500d0400c40c03000006403100317010b14101004d02810b02c41a400542c078400c0104540e0840d000700002d14140030941d52504120590a5014010040064074180c105100c2015903465070840034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 951543848 1250 951542598 951542609
    0x60d2006030103060506030708061302090711060708090d2d051201030b0f060103050c0703030510090e010f0507020c011b170301080a1703060a0303080612030a050301090b0103091205091801 83
    0x803851b07240c400c0615240c044141e02c101090380c01030082c000c0d8051101e0012070300b550180e03241d640643d95010b007070b03451504c4441411002e204050130401c0150340503d6403800b600800040d940c0c240c5001a0440d01e4141c0f12010018100040001200300050403001200c0c03000b03a41045800c008001e10040d0b01840268030035a0040007040400081c00900706146900c1002420108031074109880582c2c03041c06001c0006040c0b40d650404035001c06281c8070018001c2649007c18011055041c56049c081c1c85194542c41d8045e00781310205086038000301e008000014103a40f19042022000c0c900c52203000900c07001d81b200c040090221080180c0348000b54003034110700c0c00502000c00140b408500c640140c0c40551041101482441041e0340d482d8100c1c2c0c2140e40510f42031116488103030010b0003009514200c52000c0c44006030304c14003e900b00020714103c4d06c101c2c004004030082d80c0010340554880304001032000015100135400c0501a201078800e0b01790140150351141214040c106107504203070002c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 951545098 1250 951543848 951543851
    0xa0f180b030f160b0a08010e040c090e071406040501142809063f021308010b1002010603080a050a02030c12130f0503070501031e0606081608060d200603010306 70
    0x240741001000c40110004250f0a10013920703080c1140c400a100e007206010700e00c102c004410100c1c09020404410401a01c1100340410000303072141e00559803000b151060700b40d1007005040d0b130580f5151050a840803118107864030070002d00d000d000c084042c1d00034030b03c40d80c10b4205c0040ea410598400f81c401c102071070064940d8240181000b1700a081c0304018003001c408a003200d01c0f10607054107c008600840140030780c040f4110310500602d0000790143c01141002d207640c0100000311800305403c104c114804c195003000b6105101c450490076109a0700020707141400401c100640140714600074160f001b403038415242003c040c8207020382440c21a20714112050404140b40a011840b494008014880034184505191808010030388a0215214843c10705540e000e0b1406140705480e51500400e810f640100001c1b80c036000d02a2130b00f041958440040441e00e03031920101401a00080d00881000300003811041c11070390b0b5210800c0c4810b9071419480030701038500c8115110080614040c5104140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 951546348 1250 951545098 951545113
    0xa031205040f050603090a060b01030b090c090901150914011b03020705011407021c03180e0a05060d0f020d15060603061a130b070204150905060108060a0f180b030f 72
    0x242e804403605140c011034818182041406015007001804400c1581e1124000c1031410559006030001c10243d05800c0d0084445004c00122816400080c000741d20125425400c136602c40c4092070024021819800118030003030820b110b04007141082105240c0e052401e000d9100a0032885840c0c1d2103042012405648541c03014016903070003140f00302c0c070001281d03108d0b0300308100ba800140421000407850b1090641a0764250241481a038600c50801d412280c2907400e2a0355045403450b00104450004038140f8040114045181040d001011581c000040d07548201042c1c080280254498404071019400e05c40b10408a000c0c600900b0002d14464134002802454081d40c1c2d48590a0581d401c0d280060401c10726842c14240030b010015640022a02505c0d1940383c80814000c00b034081d814109007035240d100280c2803106801044c8648408e98031944140c9945060050000650180040c103040c8035009201c020700d0604000344180c15064046040126000400c0c1400d205811011042e0410340 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 951547598 1250 951546348 951546359
    0xc0813151409150601090e09120406020604030f2c01030b280e04170d061e061d060f2d031b0f03010501121506090911040e0609060a03120504 62
    0xf0b501c049200800a09142c2900000c1080c0d026014406e00103e044000c182e4208040080440b10035103125400d81da0b0381c0350034001e552107004890031800609201c00e941c503900d108201640b210b00f5040c441143d0f401d546040c091a0f20034180d9100c0c1050303502c0c0b111440d01e5a94049284510b007000e82043d5440740b405075000459111904000a644545000d12000600b1907520b0082c440700540c1c050b0b01c500c126a11500a0146a4840300e9080c12201500c0710351201400d40c1411a03c1c2500d40008881c035030050000302c41d510b05400f0354060b1080c4140664240d02c0c400900c1d4011104501e012700e41c030320851003c02d280c1c44000040b0003200210801004841f070010403009424103151071030800604034035220b078502c41401114100002100444c010310b000f80c0190160200010b90843c07004e4035600f00810b0028a481100c40d11400c0c000030401e8000c62104a800b990a05400074044e03076075000900500c035401400fa240c02c6509008000082050109441d41d8820075aa4060f42c640c07428 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 951548848 1250 951547598 951547603
    0xa05090c03030f030105010e120a03020c010e040c090501030c0c020406080c0108090307052808030f060307060309150e031b0f06182a100315090c0813151409 69
    0x11406802a802085458800c43c500d005076811103400346000031001d988280131400c220340e440050000c81c490001035004043c0c0106400746103c90a03641c0994604502d0101300598003021118070104600740014061940707e5040149405c2c811708205055000c01ea000c0743c100d41407a4403251290b0440d044203080c640c5c5c801c4c070305500140c001d002941403440d1b0740c0303406858140788184011140c1000c0101004641241c6c00c034410242c01410349522440d040e2090320728000d040314401d1007802025404070b0040c0c000c0c03084000e003a80000e072240314900c030120340100410202100040d2b0b80300c1889012440c0e041c0f1000112042d00140123401e200700880b8000d40750500c050404481c20102d82c403410040140010302e2152820480e00080c100b00140c0f181a41c52500c0c1c000d0b080e0404200001d100e80540c0640250175100301001042c1480c42e92504440111681703d0000d00000320390401081e0a55032039070980d410180241c43c08010001c4640103d8101c519984610407030000754800c00c011000305 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 951550098 1250 951548848 951548863
    0x715030f050a050402030303010905070210050a1a032a030f06010f090506060a0834020a022b030f02030405090a0b1e0f0d030201180807140c0f011110050a0509 70
    0x14202d0a00003410079500094a80c0030500801061982c0d61f400902954030070080071030b03140d0003148100041d003401800c41024000c68060400c45d150301c2c1035440d800d410700151b40115182c1c402211002c046a10300c002d1200c502d0985055403600c101c1c40302c4004004107000c01402040c0200340150b1103481c1142c00381c01e4600051400b88201e03070030b00400101e00c2d000707101903a003d0518480e00400c0110040700d0601d0b543d002d9050003040200b800500f0750203800003455113415000b210098545040301c0f650543d21590040754000096580c0e91100000740910310040234070712907006503400c0c0303515400800d80c00c000c115440c13140b1a171560780041e180d0520480c0314820074100c108590704201d404005c41c20808003552803502481c41001b111052504c01e41c094085a138088015070080d056a090920792a0800f601c156040009005103609502c0e000400c014440e4000d80002c5000c0600c44c010b4800c3da0282c11200914050026040201442e6105140c803542206000181c2424030300f00c85031401c01c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 951551348 1250 951550098 951550111
    0x9122503080a0e180703023f07020a051009200a1e030b090c040b011e18120f05010c03140408070f0819081302010804030e030715030f05 60
    0x50401440411400c00c02c81d15100228240543c1007003c42c4003041029611104054030007141c40113102015502d6001887d08001c1384402c1242070b04980c525000262103414070103070458406102e21001400d1400701e03513008030180165a9942e075192111400c004c103505010310703c3c603600d034030000400008800660b4001424880d00341003d0100020030360240c10b40c094102e01d152103c101015000d1200402000f450f4400240400e500380040c46581c0c61004210107445203007899880d0b01e280d48034051140010045203400303108407445aa056511084184070100700000324203000c2101780b80030070820409442a0303441c030645080c50500508417914006103170105800c0a0f540109103420440d529041a00400150f6807070b2200d1030000b10036402100000c0001d1700214100c490001c0300404103603144503680750300c012640c515080d14100c0313000e4030700280422081004540800e00c51809140e2034003018044070802c944030b10802d440300f80005d54050009460300000b0441c0149801040e030800c9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 951552598 1250 951551348 951551413
    0xf0b01060c1a0a020c010234030c06020304030519050a0305180a03050c100c0915030b01140c0a1b0819052104090204331e050912 57
    0x1202655800c0c004203800b031600b0031031030481010501e9603243e0350464811000b044000c42d981e80d08080030f641d98103200c1102c60f044440404801c45d982030030341e00307a101182e0315580f106000038540c0d9034000250005401a0708102080c007020703680300480b00f511881035455458407510761180703810050645000810072841250425580d44dc00c01c000035144140343c2c1e050a24a80f142502120203180c43c00048006100d40d041403110a92180c2042400c8250784184c00e5541131048610003c0d07055840043c41e40c0d000075016100c9404026005029011000c80c036800c1e50300c0d180340c91f290700030f036145203c800c080841e000c01c2003046426400c21500c5001d80640c8200c05041402d51a45500c0e45065540c840060b03859280100485800d41d00b01e070080c0030955030454903151134980842150015000500044940034420054600f83c080d0300b40c408403a0740d0700c502d549018400c01c000c041c0d1414840780c1c180542400283e0855480d090300c40ea41e100355030001c00003071000c440e41200401c070b070201045414 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 951553848 1250 951552598 951552617
    0x5040c05120706020c2e030606021005190f1d0d020f060f042a03050a0204050c1c020d18050c240304060b12030d05190e1906180f0b0106 60
    0x89070003045009000c10304a40c1040004000e0103071801c80e0303021040311403640c40183c612844060309a0308c40d50948140741e003114001c4120381c603420111407081da0800ea844591804241a0b4a00c030382140b041b050851501082030398100e00312000c400305c1d084c0301c52030303d4108080b032090740c66040007482c80d882c5130f181c01001103040c55104c00031b0100e0054409000c020f90740070400040c0c0f4448012240d00304010800c82c2c0c2156072420407545589003203100328031a0b8100404950404103010030b4500d10309064003178030112031141000d14029444048101c540503203440c0940e0000109003034400700c0d01e004201410f0601d00d1001042004c64042c10750000005184440081441d4940142d0364043e900000c00608800004002640340004502411803444001034120f8072080f59042640549002643c0c040282d0702c5440d15030540e0500e40c8601e240781d104004108007070425440c5511140c0c000c00c00020020310b482108100c00507a07010a6075944101051641000129030381c0c2c600400c1c0b145401d001340c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 951555098 1250 951553848 951553859
    0x3141e0603070609030605041b0b04032303030703090501061e05041803021b011416050609010513170d141b1801110c03071701060b040e1b090405040c051207 69
    0x159101c0e4000070300306c0355441c0006020800208800207c0b02500e103600028281d95107540e1380c8951060000303ca81c0010940802c3d00c0070a0440f008203a180c468020b541140e503101400c400509501d64265019901d400b00018865405644043c034045144184945a4103100030700043e40d40079900c3c144100500d80b84000465030100d2055540d51140d003003840032814140049810a480d04110014254001551710304201d86c0403245e08114445d905440e65a61410700d20303400c0391000c07103408400c0c1403481c0f0203400082c40040044140084040624201521203100a00300e40640040849110010040c041c459807194030b500700984400341403078507100044100a10200082d15400c1c148007517607800b40207200c01407100e0150117034042c0494600c0c81d504c1403200108144032a01540c107528009020a59440101c210303025142ea003c200c0c0d256440d10202d102c1c004000e0504140103441c244080c40b03103a9540d00400c2d0113217000c0c054148085050600304100c141c0c4035030414940745d01c008400c004c3c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 951556348 1250 951555098 951555107
    0x90819110d02031e040509010e090d0228140616080a0501060e0f011b0503030a060512150c1902015f0406060e09072403141e06030706 59
    0x801980b1050307407140071980c0b40500d82e01c85c020f540010390302c48160f90001ca2001d50074075520f403181442c8012141e83c1c441121042e43c03500983c000840c02034500c052200d143d09001e004040c1000e22680441d4044000004214180102613a5852000082111010398198801c1d10b09820103050b00040106503d840e00281411400e01d050701d019003452521141070703a024200c001c0c10b008986414580360711861500b04e48031350048442092481c6001c1c4080b0f142c3c103188011070060703102200200300068014490820b604801002448039010804c10700781e1400d502c600141c280c039030a400120700d034101482c2c041c100c5680180c02d0284018850740c002849240b12014900d4020a03d400d2aa00204041030542050b20143c2100180d41a9018001042247da0004040700c40c0404c09010301c0d00c80c03003000d5446050a00c502180e00c9030720a002546409200b61002109000303090000350740200c001d00406a0700c01301c03040358800705402006d0840d04643e40d14558441d004601500300c41d42013010290 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 951557598 1250 951556348 951556357
    0xd0809031c09080d050a05010906060507020d1401060305030f070303110703051207030621120203031303180504050a021201050604210c030b090703030f0503130b0406090819110d0203 80
    0xc9080b9269040c00050040700030440e12036a919107000c0c01180352842030b080c0540021700c250360699161a900041c41342c41001501d203216230007040001c00021a49a03650419140c031407561780b41d580d5410000009000f00010020700280c0500f80d0345550440c24081e044480c20134807142e1001080041c1400030760721100311803039406000640015501e4500c4101d0007880b094200c884600015549511880865002c000209200e04145a4040d0f5194012030b200d00064071001c041c0910394a5500000340900700c084180211009510743c1c0030b0b50b440014041d207000741d170210342d0705900141944506000d040261702400083d01d00c18a00346c5440d8080150713603034000c182c82d0394202090600c001c00c4414064035000b540c00501109003401c0103c00c0782d40b81c0c1e002d0f12044001c185100768003070320b090080041d280319200d07218540d20311444548036019201703001002220207580d03802002000819541c0900a0800c55040009840d051002c0142c4071100411558800758403282c005081d0650000844 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 951558848 1250 951557598 951557647
    0x5011a060f1e03131b21050109051902030d091a0a0e102105130b04152405041104090c0c0618110603060906060f1b0d080903 55
    0x20742c0d070120300038250500c00480b000182ca16800005000c02c220105428070a12400b035581c1d203901c41c510307424210603401c840c0b14040d8203014101113540d00c0790099a10140441c0201c002244a0420355106400c003c00440080c1250307901a0902040d420100b006145401071410079001031030030b000071568403803a0b0b151000d01c1c551000071021420f80c8603009842c41428040d090401502caa00c0380030b4100081c41c18801c0c1a8180c41c4002c003503d05c550300405029aa07003201900804449859032642e10704024401da5400c40c540131050504a01c501c141d006103201d42219852000510b083d50068140303036880184100e04100c880004c01610100301c0f01111131045c00081e503402c5100c02074585104002d0040d1110386003103a001d04810440e0b40c0b54180a20940d00c20075250a0002003100a000079188103402c444064000340d11400e240000780f55590614504a042c1006209501d90880082d9100c00c050340104000901040c0c00c035054942112007000039500b01504e840e522801c015040e11903 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 951560098 1250 951558848 951558877
    0x60d0803100b120a05070801060c03030b01050412050c0a060c052a03030f03060f1e1e040204170607031b0f12060b0315030705010c03080901020412030c05011a06 71
    0x854040241c40d0040310003010100d6100340c903002054040d204241044a00e04149400c080014004520440c4000d05940c1c05031035042c00031010f03890071001404510343d0786051050400c0042003141145055049052042000b8030b41c1703012840074040d6003121a400760045c8040010000700188003c2441d404854034039804904500a02004c40c4007900404803e64150000140d040b1080c44080c0065110b081d048c0d0744101c14491890070321003907400909454485540307054003103040d85400300d203075000c2505d61043c2c800001d10340c0001a04a90041e40009c2241600c0c11140c06285000c0c0022980304a507400c0400c038445405030b00300c40204044060707100b0403100307600c5445038501515454071035200307254041000d943c885801d8076441d4010780310100400c0e02c82d44e480590340340005201c4191801a940d8540c90700c140d5506407100c0c0d001501c58000341d5001e11021400c03140318064894a14060350b540450f410b86401c00b5402c603071b0214040c0c0000008068200b800c0c1d2955402c84200d01e200c00340 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 951561348 1250 951560098 951560101
    0x50c16060908270a0501120b030106091112010504060e061003020c0601090509060a29030705090c1210030c050906030a0203010507020d1d03060c0a09080304030f1109060d0803 77
    0x400300018240c040d8024805030020480701d014400700c90007080c2040c042907030600c00c02c10039010042140b60a10880c1e00144104c9030241d1181f031142c004034020080a800424403c2d180c40101003520080a07400304015004030b650003824103101c01883c0100741c02e82d4100507103420f0000d1100c1c1c0c482d0040c0b4440c041e41070003003180201c40c4a941101c801000980603202c1c01d50b1039030340d19800f91400740e4030440c4a00c1040082501d4201c240706a01c0b56025031781c0c0040f00c0000245d02000041c28510800c3c0d814025070f00001959100c0c0244207200702d20f24090b01e56240c00042200b1a030b00f034042c00c00940c03030034045000d00000e181c0108030001c3c0c4404855408465448400191500c4c011402c02074040d402c200910802640008030f24010444c0f980b00d903414015000a11144101c0302000c59900d60b0100300400c08a0b880b0000402d00580c0b6440d0000d0456101d0100d640341d9031042d40300f05d070090f41c103614030420b015111416081c1c0c08411140d2122034200403000420050110f100038005140000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 951562598 1250 951561348 951561353
    0x303080903160813140a03060c090902040b0415020a05070303031107060f0f0c030e0a0f0302070b190315060c03110f0114060f040b1315090207050a02011101050c16 72
    0x503140c00d003000b20380b661065107191070480000d070010001c0c0c05031030522481c0441d2510790f4209010028038042d181120310351454030f503840541041c0b080c40f000d118100002040742c1c80c4034001070026100d44084a41e03070318a018210340c01c030201c070410403007150401da00b074100280d80419480116034051034007149040c020500407410b8810420000c2c55285064078400c442d00082d0080e10484880c00c0c1d040107136a12048094003171710f942d4804201c891300092400c000041c0342c038254a011074002c0c4110750b1003640380c2d00122020b5004030004000e4071104c21035500b50940c0740c0140d82c002d10010741e80c0500d41e031a09102a102d2101d401004007032001d00f0165078034001c03080182400004011000f40b09041c4440d41c4503007000025110a0301441c506030408902d0708141c00b5035482102c6c060400503103190a520001c0003440e82503107044099041002c0002c0c0074010b0700182103a81c0c003480180401d2609880003400c0d14130108245c6241e81d04000070012050b2091043c1c0303403036015051119540c4003152 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 951563848 1250 951562598 951562603
    0x4030e060417010906060b030915040501090c0303090f0506130501051c0f0b010e0d050d080702010b030105010303091d0f010501050c0715030b12031206010c140f01050a0f090c03030809 81
    0x140c0240055a800b003595804650054104e1803405004a00400c0400e840f010038001d50320048441e184181d11410108100c003e900c0340003503029005100000304058a0340d0f4110940850782d10a83c0003995880341813103448500804900100300c00c41f040c9103000b101d03c040000c068102c1c0318143c184500400e50b00321407041c44d01e02d0603c0c0c0c0b84200082100e031514041c0d2788020408002c1050000303070401098903060904103030451600f90800e000b0024034080700402c41c0c2201e0300030700710b404654a60441091a807001d00a0070b0103540b00713840d001038560070035203103806201908036801220024401400202c0d0329100415056560a2030805c1d07031044031007900f6140010360b512005406900b856801242e0b0343c03540c04240c0485048071041c41c100003056407290799002e0000410700d0a110100400c0e160341c081d16610741081e103c0c00f00d6170360020021160364200b4a0740c0d1544c02850351501c0401007580d14500c43c00d82030405400c820441d511264450260364810750000409101c4290040b540c4203004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 951565098 1250 951563848 951563857
    0x50c21100b0609030f06100b0f04121b03080301031703070f050313080f04091409060a18060e1c2615030a03030b100801031109062d09061804030e06 65
    0x50300303c5c0d0104030319104480e42c41108455005003403804600108413043c1c5030080b40c1090080c010105c1c142401c1c02d89841c1a1002507100320391107180340988001c554008691130340258016154507450b903265080c0340500c0d881c4c514810101e44410810045e00e2034205189a505e10014900070342c40790303030350f004031001c54401c2da502410003000031803441280b55a55005100350b854407034003441054001c10312500214016600810385806c01000248400965170108001210b1400c0e10024803589450354400c403030301441d51100030b4006d0f41d000c0f0803902211070000200c00461828201c40b50386c440c1408070624004030f1416842c1c0304040481d0042180325503042014000a0030f480040300070b0301d0302800030881d0000b40f178000d54400048a960034000d410240c102e07500018682244170301c14007000901c400c01415158010395054800304600408600c060b14680c01c14070f042900c9900c6010003007180350081c6070611810f104840e00c0c081c0340c540300c030050704143d05092951004100c8030010f48180503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 951566348 1250 951565098 951565117
    0x3030c070f08060c0c03192717030c0d030213030803011d0606090d03140d050708040c1401090501031e11070b0c0a0e0108070c050a06022101030804120618050c21100b06 74
    0x4211005086407004840d60b812a40c6031b440c01d550020702250086e42b00d018404261211390020440040700d1030280d00244441407000a1480b0269204e030360f601c0309600207030441445901c011800c41e10b070481d9140b03429004141254141d0628014030001144840180001420418841070b4030f11002c031914252240e0300c204100900142c0751149005055810881d002c0c0c1d0f02070313540440040c034910003c0b076000b14490f041e5107a0006904000040d00909000340081c0c035000a01a85e48010781c0d024419802001e03181c110450f40d5045508000048070300241c507002034000100074440c1c0c595040400007207030030420700740050f8039a81d03c0010348400e0ba4806000e0264080c40a506e8204042ca5000f0030015425103061000079134102c804020b40740d02400010041081000140044100c403009907400c82c0c41403c2c00310721011032b0b4282c030141003403288084400f940b204481201c0e520b0010b201918041c131018511401201c1d880015645115210042034115a50658401c02d41c4a03403044031050017 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 951567598 1250 951566348 951566387
    0x2a0f030922020c010902091f03030f181418091905240a1a0109170c0303040807081c0c060c03090b240f1e03030c070f08060c0c0319 58
    0x2240b800506003e170000181c2244941108000582402d0b0114220030340c111860b032140550701d0030741e901a1003044c04080040c05005452004501412003060020050a500840b00c0010f1110030140074000504420088401030300c0010840748010000b40b030099543c8050500340c600d445400d2050030001c1940c02d000e009130018074481380c540b03c204203042c000d0654000c10800d543c00c80380b0307081103404d2800829000425040341040207403006002456640e4415080c0d42e4040342d500002071079980240d011800b190000034040165100a00243c29854840d80049000191181009207210201c1000510071135485003159203981c8280e1040d880907900c000c0d02d022034101109090403000049185048441141e180c81d0082c3c10495000b02c41c10034064082e0115003550020419020b4811414036058441030000841c103007400c1041c8402040c04040c52407606042040340b608011000701180460b107400c0001d4060014000201c031403010f070301a2a0441d01c079034080d04407090b2070300c0c1c150850000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 951568848 1250 951567598 951567607
    0x11160c120b10050405040305030f0402040e010c0c060e070605030a09080f0a0c0c08011a1c0b010b0a032d0f0f050a1515052506022a0f03092202 63
    0x12140e010040d0003000854040b24005a5400402041d2901100c000300014014400705581402c0485101d400a200030408208403450a031b00c1800c4130388041d00307000050b46600441040c032005205142d509080031016041150130000003402d01c0c40050171000150b03079100c4496091045607025281c0c55400115401da07110203003030300109404c445400c05d031200c1d030303070200d00140e0b41c00144104002c408003000411040c407038040400102a114445074004840d41c9440c074000910090500723806421070040c0c2e00e44510308114000e080342c4a080034948100303c04242c4e000c4e1952041c0b02c3c0b000c1c1a0304a070010400c680c40105000180c01d80200c80381c812800c0c04244414155aa0409806111301100c0710880a0350f0311084406140c4000215000c110104039944445018010401241d00d5800031b51305010303069030b01c20342207901c10071501050800c40c40404241c3c0210943c64690828450002c1c1743c0000c060102d1501c91041664140c807460560b0300c40324000c050761190352002c0c17038065011501d8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 951570098 1250 951568848 951568853
    0xe01180603051c020d020a0b0a361a04020102191e080405030c0f1f2a0c0608040b0a020a2007150c0b0106080c1603020c031011160c12 59
    0xf400d40d1101c0440540956165140715500c00200185156040407142071161035200c240001400165034100c0b20b1514002000030040c884030540300f218451007058140082c07503050a40307a6203554004200f100d013074203083c40050b070780c000780f101441c50402e02032006179242d901d448040d10b00207980c41c42d0304000e0b0720300400034080803201410466005800790f03139540c10389030b0030418001c11060700b4607840060f08034512010381080105100300075070760900e03184103546202080e000c0700950420900d0310015000c010100f2070303420704810041142d802e1060050170140d035400e0050f0340040c810050760b43c0c046a1000400e101c1e0340072901000740c0303002040342c0700031402e0142d031150340500030455500b010300d0006000d14071602100c0c0d60725806c505110087e0b420000c0448800c2c4c405007043c1484032051042a0a107071800051000c0140b00e500182403994401080c1420160507a4135003035501d01d810b0b09600f031504ca88044a15401a1412205a22140f45010305511420340c000d0b1070070300d1000040404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 951571348 1250 951570098 951570133
    0x201030b0406120b09010507020304180e0a021306090605010521070207270614010c0312140c09130c0e010c02030321070e03070303090e0612030a02030a180e0118060305 74
    0x11001701d0000c0c4284d948118007039a0324400d600c540d21003180c1c13484000900c0d40095100c08080d8140c10305541102000790005016038216200700c0e6551607442c04100704245262040c00c0c000c00c000c1c20082c4c10690762040d0700c5452440036002210749508100041c0b0194800d001b00406441011003a00340508403000620301c0400340c07a004ca0700c040c030b0080c000c22011103040010049e500b059403009010011583c0843c4d50b6040c403c82244100d03220040c212081002c42086071091190001c8181c135080d4000402c018183c910387d17800001860700401e41495940325801802800082c01c1000f4218054808240b551158a6560507144603501049808241c0e10714550301401766641c0703c425882254080645501440c07000a001c1210398001300619101050450341c80f1b8002050141042c03031000b07455046078440401d83c00140c00000710600c90319084011900e2a4002280450360341381400003c03c48003506000d202110f480c080d2440c00d07500429006070000d0766011054446103040d0501d0601e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 951572598 1250 951571348 951571351
    0x160605012c0903090d06110313060b0103060302150a0c140a0c060503090d0f2d02070e010518061c06050103020a0608040c0b0a030e070830070201030b0406120b 70
    0x402909030090250792048a6140da03806000d80c680603610380001079081100c00d1034001421140340792600c4c1040009514074016501c100750340d0500d050707a0f4140f441c0030000c0b1000c4d5101e460501d850f10070300784096104d91207540d5101205000c1c143e610307105200c081d222031100ca00024803400003c4241e0b04c0c1640f0102d00300340300900c21001070081a4031200f082d80c1500045903045070756405507031015105071003000088100c5000e41068483c0c60703031180741c00b40ca015000320780c0c50101070b1164140035165410040e290081010690101040d418900020f01d0945c0344c850140f80c000620000c58156030350b4510b8011400c40c1c04808c1c4843c03890626204003d001c0900c4243c2c45030302c01660000c0c80702e0180014a2203150300541100046051091940d082d411102c1000c080503a10345083c0c104a00c200072502c081c1802e9001401c1060610009040d141d40d040d00200d00c6400440010010401e003030700355400590b090070041041c07021b0a010070300810f4158443c1e0441c0c002000100306100d90320201c1d5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 951573848 1250 951572598 951572639
    0x150103080d0b06030112030c17070b07020712050c0907090f1202150a080406110f07110f030a0317071b03050705060603010c1407060e011d0705010e010e0616060501 72
    0x42c071600c000d802c01c001c4180000d00c42c080c94041005040f0340024030540c10101ca0030310454820015a0320201800300329040800210303243c540d600305101125804104141c000d100002c40c13052901203982c0d4550b03e03490914010340c003030030101e40461183c501804240f001703041c0100f40030030110781d45d022901c820100c1e400240d006451825403401e0314210304080b05d1122036203446a05851b140c0703a4480004150054802108201c107003d22040c0c001100c004007001e5001d0490426682c103440c0400100c154018a607a100c4d500006101c00000d40014a252002040104d10207060b43c4c0c03218190f9841000c04002803010303100b41c021030101074120f80039280440c0a6803c881c82540c40b8800c0c0b5080380c40325840400480c407070040e044040610310008200140c0310b068007003003030301c00d212080d4203485540c0d44014005540c2c00715150001030420910300180400d1806204000017440040c00720f40e0800c8070725014480024184130000c81e4401ca820f14154030800801c40356a44404009c1010f0416045 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 951575098 1250 951573848 951573851
    0x10609020f130605160f0c0305120705161d071209080a030515130c0201140f0402091e130f02100e0a09020408100b131406091e0103080903150103080d 66
    0x812154818425107180d20010209040d02d05881e1b01c881c0c0189604110440b09201e203501c010002480502403d0070900c1e001c1a825203c4001d45010307804c119440d03510840400b4012410007080c100030103405522482d040f0900411349803d0f6003141e146001e0207072403e10504002d00742d01001003032002044400660b03a0200400d403180d40c00044041e040a00c903540c044c8002000c01415041076200d1360104502c3d0000056a1014510b1238080c10001c465094180041004100a60030100318490b070200807505141500840030540c040c0500000d002c945406000304010010004d800b0f44003074000340c000301569450000d58100a0200b5002070519011391084640001d1900300c60098605a03540d0078080c104078401d66582d000100708400170241c0c0301102c0014041d11004501c1070240c414240c0a08031258502a824810828400340c4010302405a50f6401c14035139a107140c02d1030540754461000c907500c40c103c0d00040d02e8411040114504401e10000001c04c001d07c0400134603615002400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 951576348 1250 951575098 951575137
    0x1203072a0f06110306030705040e070509042105070506010303081b0309010518070e0a05060406050a1403120a1b0305040911030405010c030b060a0809070902030109090b15010203040314010609020f 86
    0x3ca00d41c1c0c0d804190740a03500755010700010b00107898660006842140141d0403200413540d1240042c4184005480c180d4504c4525000c45520080c202e101b18108803d900300309142012a03900c09983e540e0520002d41002010404500b41c1c840b0740946100c20039503102c1083e1241015400c00c0d00900c41950b40e40a0030b1000300051107815008a008030880d101c0c10b9101c45241c0c0e541c800900505402440580c2c485d5440e580032074507954840403440945454440070f4070b04d90381d24091500c1c11014400d801c0240c4001d2180c00b00c1d04d030340120040d414130b403038200d000c0103030840b80303800c1e5014051500007210507810b1069002001e4080c0c0003851255000c2c200a10049101078816400c0710f0185441c1e94001e4001c00500c1c00712405104041d4002624000b1524900c0d81c0e411480201c1e002a00914644c9442d881000f045c0030000c0343c0581c106000103400500c0d0014400080d540c0c4c4903e20000304281d600404503400201c080d0f0000c0018904000103558804501c014400581c0c80200c034664401c0700b091 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 951577598 1250 951576348 951576371
    0xb04052508060109032411030106030f0501210201030908041202010206100305060c0307020705040c0305041b0e061507170c0709020a021e010e2d1203072a0f06 70
    0x81010b07005007410307112845118210389480f03800c0108440840343c030b80030300b80070508400c04070305c1084a005150307103503103440c3d505000e80201603912414030b00c07000d18140001840030344140c1c402007121025400c03082d100b4040a2006030040d101c0d06d01d002e0312a690200d00090492400c0c1d44255045100340c0c29100e0a070340700d000c421180c05540c00060140d0b488003001956011020000716002440303401214000381c5d17a00001400c3d1041e80200a0000e80c542c0103100411120802c0b0f521400302c4c1d6000d4054590074107416040590006000d14441c440125000405840400c22901055000400540c0b013140c48512800e1a904ca0048080e1601c901030700010394501605c20b0316080c20310f0350301901c20780c081012860b0740d0002c844e810b91f00d19540c0d0000b10340d8045d01000644280c3c610303207814504008020300980315445407003d139a00c0f02d401003212205a442d81c082129446800340c240b610850070041e050040b481c150340010030800313806402c010240004000c01c01441c0d48500e00c18003040c080304 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 951578848 1250 951577598 951577607
    0x1030b010f06030516110f01150f2112050408030304051e24070306082a01030b030a06180f060e0714090714090a0326040302060415030b040525 63
    0x100c030782d24801e2806455404d01d0b940f086d5a28100c00c40504111251141c42d014290308603090300ba4031190500c46140c0800050007045e0310f100003800d030b41c80d800341410380c9400914000d2400940007403803a00914060303034035180920181c8000e4003100044903264502454042c0e60751580b4040491740030301d074440855081e6000500d546404041c0124424681c14600e00e10360850006006d031414562a05000301d201c0208101000503c1c4804411003411481c0522034dc41d00711115914034100760034516040d0080d00d0025005825641c44000094668100403000c0382940881500519194840d5160010f104060f0020f030981c107001c90680d200950f607440c40400420052440075007152040e00080c0c4e4160080802020a00c40058101d1510500c04005048100d8941044542c0d2030342524911008100d031041245141a01c0c2d43e80346464150303000644107015510500544c80b80011286403003e101c1e42200c40704450180c8140a1350800561003401040100984040350305c8807412041440c1c840d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 951580098 1250 951578848 951578851
    0x4080c190b0f0c0a1e12030c140306040b0603100603050915070c0317070c060609020307020c061c0903030b1905060a03150e07110f03070206091e040501030b010f060305 74
    0x580c4a0a19240d0210702c0740e8a035400c0200381c41928003c00c840d0001054044031000f2050100013a96010b00d20640780c5001c80380710581c040303002c042ca03145141c0000e40e04020802c202950078603003640c40b66102c3d070011b4090310682003582e07000301c00071050001c009590601c140544256481c280b00e10b9842c15000340d80c035070b08030985e2450814034801041d6030a0141c02620391181c083d00c0c000040c810135088a2040c0c400c1a960080080c601a1400d018021031707100e05400381010701025895400c00c404000d6840c040e48040c035104040000e082607008000245148161002080600c03444416007800783c020454450380074001c0da000c07042d0320031414007084403400b89c0d20b00170210390900d60f40317460031402811844003040c11001d0680000c540c26000e0324100e4403900060b552018850324034a003841c180301081100600e90f50090082c8801079441c5030070380341101415a119a041071a041d007822006c0c03070034101a80c0143c940744c000320500c0f030811451810307038034480a8801ca540e0b454100700c045500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 951581348 1250 951580098 951580109
    0x30d02010209060a0804020f0405090601050f0a080c060c0a060f1d0a020d080c160905090c0109060804030c242007021e0f1005090a05060a08180f0304080c19 69
    0x200034a8800c1070061178926082130001d0920049000110301180403118259005451944041c0041000340b80441344848101e106a03814901c031841e000307141d9580c00003032100138401d04010502001a0000b0032680c8143c5401210a00c086080054130030021f1503402ea12800c160740800141036620000541c0c103000e41c0e0301800c0214403282a032a0400d05400c0a0f4020150380103080112190b4040080326102516401c0d01c0044c0900b00258100c0c9002da1540005040c00410b000c01c204490700b01801d10b07801078250030810440c448910349018904062022894402880203500302c1200b000d600080d00a169401c240344503095204040410380076003a0020341c03011003049400501d0708800380114a0304006020207088222080c0000c5003116406070010000b00007040c0c42c03d1783c2c079113100320000420040d0384451a0010340b04000b01810b030000e101011044c080c9800807164001003008040c1d40c042c980a881c2c941d61100da8282d01c4491103100c040c401c6a80819103100200c6005e07016084a4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 951582598 1250 951581348 951581359
    0x10308090111032b060503010e0307120c14060a0f0510060c0c08060711010609050105060d09170f0a1206050109182307030c020604020f010e0a0b0711030d02010209 72
    0x1051030044916000d14100580b8500091184100e07591002891038400242100f00b014910340700309081003201c0d129408503102c0da040800d5280c481c48040304403017400703070415448400d110340320000f0341d410000b0752401407502c12920481c0e0039000000c41c01c2401210740c40c8043c80402c054482036405d0321016283c02c2c0350044a02ca00700407040c01198003142552066922000440d070b07811446062010840d20403001c143c620108400300c0e2828071505003c1c015a840c01c01555050101140103401400000d0f02d00c40d030740c4c4d201c880c14800f40710f00003940750900d8006d03155905591a0315600d5504405807039030201d400d030154141c02c413005001d040152081a541c05a00c50300d410152190215400c104412480e074811180018000610013540c0d405541c554030412030a01c200024100c0782c2d902005400c540001007484010b0b9030340b0b219401c56000900e0700803019166807001403040303020b44e0b0240e15002c5000908100700000d40d400001a010f04405803845a10ba0b40402e034241d01c6242c2202e640302c03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 951583848 1250 951582598 951582607
    0xc010201140c0d140c07030f02010504050a0f0614071d010e030a0b0c1303120f020102030730050a0c030b18041e2a0b120a020a171602060a0203010308 66
    0x2520501824591000c0c20001c04c10590724520300c04181d2041c0c1d100306484400103026400e054107e10551184c0300d00f13200800c00c41c60291a490b8551b0424000206004240403c6005200090300440454030340c43c44031103c01e0900714805449445d901444e01d004142140200c2d1156010307216404011001130060300d4044410fa5801d1040b082c0184075800c5200d0a229600b50642c40007141000b442c4603a036903000703490300c51001a012031b0008964004681c0100304201c040e0740c0c082220004580e07090241054030b161000e000702090140781c80d8800c81460001046811034450300455818000c540303040100c2d6140c0340601408018900030b000301100b00e24045000204010b6a0042c4080840b55481980d00140e40d020303109004620700c5a603134125000740d94642680f6010100c018804101d02c0e0b851300200146902c50070b48003d0000e17800302d038081088480c06000301050444030398040b42c4403040b40b4000c03000401e600040c140c110018803542c0d002400345461442100d040c0c9400440d41402c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 951585098 1250 951583848 951583861
    0x30513080405130e0a0308190204050f130f020a0e1c051b031608010e060a020a090e0604020f04120b060405220c050a090f0b0a0e0112080f16050c01020114 68
    0x5080f514589001c096a88840020700c0060034000361041921954039650303a401c2c01080701400c05280c0004401c900e20400040290b0f40c3e84040e001a03004060311200001807c503030121000b040103c4407540464000101d01c2541d580c04400481280e1081742c103240f407140318512041c1460001c0e0001009a840202c01c0041e500e980040c07900342c510300800725551902c440c0f01e44203512100e58815941030703441e422962a0102c0c140141980104415801c6061022044c40204071580381d105030308180c0c2034032001c1900c64403150101c0340410b204511055995503100405100c50400e900145c488003012004503465242c0342c001c03603015000040000603a002e8a0b0204180086040003c0703034110f104803000a280d0701d500c6042001407040b41c0700003d9140003520042c00b5030b0300a08605100351034058060140b4a04042c0746410349204047c0e030001d00344140f0313198583d07128140c4030070703030801010520000030700042000c800024818001c0e203181c03005500c0107909a403c0ea0341d14442002891000401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 951586348 1250 951585098 951585109
    0x806060906060c0f010617060f070e040c030213030819020c0a0902091201050702060a061205070620031204150b0d0201080a1107050a020120100207030c05030c06010501030513080405 80
    0x10b003d81040688500b010701d01146801c645840c2e0001070416451a091004036109001c400d901c80a1054050308a01e400040103044071550600301e0310035980c1c2c0c0014400c1d18440e506550380ca10940d0303c3e298500d600c0781401c0c21681c1101a842580902c24450403040314400318080342e41c0d440160540e103d403805c013814100690010010320f0f401c81c3c02042101c018820901825008261070f402a0100e41440d0145405444040d00440b0300e9140d440d00c0803000420002d0750b00222003541c50f10456600c4215801d80d04c07001c400c034501d41c01d03110100303012000e0455030959501a0380310310030750403901080710b00500551b6110859282c2c8801007001003c0994042c07154a640601280743c0059814240343c440d110f150007120061381d2942c0040200b10840d600b01450700080e4000c418880e0b415061400419900d03071080c03404160031034011a0301c608250003040c04400c2d80754024140c0391101000407100383e54503000d2049900203400c01d40481c03e045400703c0d041c201c40382c1203034a00380382500b072000348030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 951587598 1250 951586348 951586357
    0xf0d08040f080d050a090c080a11240c0d0e012a0302030d1503050607080903030112170307050a0207060311090f1807080a1103010e0f0709030b01150207080606090606 73
    0x2070b100c21041203803403540b55451040341e118031250180005d501c50182085000b00640c2d42000e041a400030000f400400c041046d400c526610441d07040000e55905044071b10070301d00c01201c01ea081d60001c01c447e5001c15020400e411000e0480e03460b00c40360303942c25004441c1b5100111501c000481d0b0085e00d807406507900c202d080045400f9004482c90703c05d116034201c0403111205070301701501c0003000381403041040138000d454009200b0702d40b6a03454204811120344910061050700c000da41c030100d8200412440d1103550a41c007401c5026645c403450510000303481ea0703101220700030050151220124000e4041d1041c40c01c9001513850031801d00c0030380c105011156800700c2c0303c2c0d0b500a9000c01b507541184805900c19205100b40d54513429241040c82c036030070a58680b035180d4071840c0000d00060042e9040e04031419407200142c803100d805601c44d01825980d002160300081c0030b21703100e880042110f4040ea01180d002d04038a41c02c586015580300c413201c0c1ca602050700c045511a108001158407440c1120140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 951588848 1250 951587598 951587603
    0xf0b091603230304120510020702091801140c1206100504061110060807030309140907050304110306040c06090503030f0d0506060f0c0c0a051c020411210103050f0d08040f 75
    0xa100000c44980c424695000395000b0035817080c2c1d2651002c10000f00380200d41480103101010750400142d9400a40c240000030801c5a1f0004071310819085104250800044c50320307100401d130094144406083c44a5200c00c0301c4030b4921070384001050040c101030086803240c0700300744d13282c0b420281403520444618a2402d20031700b031841505032380c5041982c2e070b103e400700500c415801020801c0c41d41c50060140045a0701c80c0110b590607244000d060b40302d0180251784094949420741d40c0e075840d4502560300b070702d4002c42a505031055504210070030441040510903034070340703032078160b9500d03075441c00c043c3c9e240b00700500050004c1c000c1c85040040744140c1c00c641c5e04010020021802e100e9199903152a40c1c0240d90400010703030040058603c9400c2103080d10001d400e0548031200a5205c034411003040f14406100240116a02c2d01100305004040041d0b440028407000071440c40651080400ca103035100380826100b60084041e01e403c501000280e01143d0182601c600c2d4280d40d41e40c0300d407821401083c40071b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 951590098 1250 951588848 951588893
    0x90a03271d01080f0a2d0f050601031e02011b0305040503100606080a0218010e010915080f1617060112050a09030315080c0f0402090a030f0b091603 65
    0x2042060404410644004089800030070310741c9002590780c600400c000d0480056040440380d44046200c29181480c1840342e01008044c9600320414164000410b40c8043d0a2021840b01b00b0100140421503504032401040c51601c000040b010a0001800707a00e8003c1c003085240d0070303607840940b80c0e401c40d18165001f030605500f0b0903680c1c0b0100b404c00d80d01024460600e0303606c80c03040c015a50001c0b030150f00000d00c2da01c1141070070b071840340101c0c02d050784511650500c01d940360540056031184134103c01404895100c80f0000711010700260000e07000f0340d584a200d00b600400100442c5075070044030b49900700c0d641c481e00d2a040918442d080c1c81c0c809043c541c100000e00040500313641b014068140100b00e0094001080c403001d00703005040b91070310350100006074180c50b02000070000004100440c4082295864109080c640c0000e00921400204c2c50b00000382c140000140101410805007580c00348007000da156644004598480016081e0845200c0c08190b00344081290718100c1c2c060464003015 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 951591348 1250 951590098 951590177
    0x21c0b060c0d091508040c090b0a0306020d0603231e121801020d03111b102301090603030504151715040c0207050904020f150a0512090a03 61
    0x90079420840100c8680c0d0210f26907403003c211034400f02d0400340104056150280309400c080d580c44c4d5148005101d2540c2141d1110380421160382c07066546030043d6400b000440d55840642982000b0302024802514204401c40b15190f900c1c4410034156840d0784858058a41b03400c2808510a03d00300ca040711641d50b200d0300c0c0b89044001d059078000c00440440d81a140d140400400c0024504203403031100c00100b50070213540b12020030b8984d00b501c140d07448020142c0b200c0785051000f14a02295002c24003603c5051041da9084001c400c0d550311801e1885251841c1c40c1e82e01c6401c513000340e03506444001c0024008210402c0b05980081c404000720b000340c541840380e50300500c10840c10910a035400d98812880d0348448045151900c076a000710034050000e0450b00e445c08002858039140144041c1c05085a420300c00d81d280d0342c41401a200488210f10a0744410b401c20740108039810440c0080b60042c28100852040c0c0f40000c0c41581040d416500c4240442e012403203082c0501340d58040000128190740b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 951592598 1250 951591348 951591367
    0x3110a0b0a0204090b010e0d110312130f15090504020a032409050603300c03030109090606050f0d0f080906040e150405070c141c021609021c0b06 64
    0x50001c0c014200c25002684403410150394000b1101d0703012905050040022604100d45c44107145420b14a41040d0445441c0b400c47e400710b410030090b90343d0f038407c103100010411003410218000030140d44029044020340754550080e17649038401a036458003c1000c1316010401032a19030020b12070003180b840c000c2244015200031a0007078001d40f50f0365041011100c81401108001d00c25560b1060003140146040f01341341c03411940f441c070074205183d52a03612070800e01c0900428011540102c802e40100c955943e59600c1d088020074241740100c503034904103640000c1c60300e4505079842e0500d1000708002142d200c11307518580744451000e02240c4000c81480000401e07560b901c0038000800e203000040303a092400303015000c09010501c0100748501d1a200c1400007041d40702d0071940305160f1003020b01c00188245501035141c400440c1c06001c40100e214070703042c01d4503404a070ba1b1042c0b2005d51840318601d605c80000906034081c00c4e00c0c540d00c0c401000030640c4030000d207070811001c2d810040c00141c50600100f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 951593848 1250 951592598 951592613
    0x1b060906150a0b1605010f0213050402180d030801031a04111e1504090509120f0318070b04240f050a0e0307060503090f01060e0412021c0f021e0a03110a 67
    0x303460341c11284a04d2903408103004003030185019140000b681145000361034500d0800c20708007801340718003071940880d08242c0d280003a0750801c29400c004000d080f03110214a00103249050900084400940c124603c2140b8566541094011a0b00100708800700b1904030600c50fa5003601a00300203039903401303607a0044980711011075a0021078100c800c2a81c46040c01c40304015154064010401d81c2c1c042d00101c039414007031000b03486280b407110340c1440d980e032180708030300d401c032001010101c2144c094403900291907810032009200301c030314a02c1102c40c1c0c002d08a00b4450120700040c140b00102d0840d5404450203440303071000b80140003450a08050040101021a00d8013103180c1118001ca02c000050065040d020808400b54407400c02c001d01030b00f0f0410788480180c2401034401808043c1007050404891300038080420740c1c0c400001c1c51040c134280040700800800c00303d08070700c0c09801904000e96031041314020704092940702c1e02c01040641d0b42643d007180c8030240000480c00c607005540100c00000c0d0754 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 951595098 1250 951593848 951593857
    0x503070f120c0503010812271801080a03030b04050709061209081306030b06040b070809040f05070f110d020613141b19121202030910051b060906150a0b 67
    0x155101c071303180c1d0b0600c510309103031410b65110005505028011203a07121032460343d215503601c070398450146001d01c440100f442021860030382050220500b0000c5898100043c4981e401406a41c007440b820034101c0620003102d00070b49040000521a51091107524000e50f40303840ba5100e4100000351300b8030b068465400319000303201016400b100c400c41c00c20a05506000d0f140d000442140d0a51400389040c90a413080c0c82203d40013003840801040104031070741d0313690103520382c1c1444c040c0a000d580341041d8001d06042810700114003180441c0707a42c2030f241d4070005c1c1407401040203400801454644013108001c3d40503484044079103aa00111100079040e05000918042d0208400244d000300c0807070030481c0c110036511015600b2011840e0802040134840c8090002c0f030b4015030480d01c1f40714070f01030490442c0706000b502c98020303524a13018441c27994050b0040900030301d403160b441d491500544845031103603000c1c1d80c000740c43d520241c0807409440400d02c0708202410000c0c1000314096580c200c04d01035802c07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 951596348 1250 951595098 951595121
    0x403120e01050414060c031b09060307020a031106100b13081c0f080708040201030b13051003141207032d0c060b010e010915030902040204170f0d0503070f12 69
    0x4542c4203100410101509115004072035801801c018a42080c400a00303001c000c1c030144401000c158017034950308148044900c4c5540c06491030340c2e24602114041c1d40c5c0d22842c2000c8000480e6901e010600c1503021840500606500c008030759a07501e07041103507800b0340041c01102900302d0340305000543e1810806c461100200804030251920001200180c261041c3d07445c60420b0180a404108080358001195030b4001c0d424200011010081c0c0003280103070f80e802c100d403070115140c6414000c0808030380c3c01600c1100c0c8110120281842601c1c1d8a90301c443c000e04280783ca01d202480040000b0380107900f080511103045840c3d110381801c0e030015103c080201d4591a004c201005114402d2000c20b0040ca10404000c4c01d0991405180d01d000800c131f000c4520031019a1800c0c0c600e14070303241340310f42c000d0b9801c1034000f003041d074403151240200810003d401c00400024818900c243e14210004030b07901d400224503444003420b540e1a01030503030798084a640d238141084084200701103056440e218903200103c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 951597598 1250 951596348 951596351
    0x30414040b060408061b0909010e1305010e01200c070504020f0705010203010b090a06030905070605030a021b100506150d180503070506010e10260a140a0501060b040503030904050403120e01 83
    0x1400403501c0401040e07801b40d12100700c0200151160b03501c3d640501411078591001503040d80d074803202d501400303c1010070014400d50a2154088602c14150801001c61070b004010a41d130701240c1945401c68400c8183e0311480c2e400c07008080005107400d0303000e0428886400300703803498041c06540380750032a4402d802000c000c603000f0440700300600f00000314401811301c0d81020007404d2165201d4540e245010301c205006c0000010014a99084e1341e0140e071486110071241822030070a41002e1922036110125505840740b81400182007442c00302c1c805100c0f9801191440c1c80c02501446910251401c21b60036404c1700c1c070010034040050400c0000b4108640910003800040d4100b1030322a03072403040507140b001116039028092026508113441802c5281000000b0382c3d0709110b41210381d040480c0380300080d001000248941100e40804520420b08603c1100200044d40d02c3d8442c0055501030f5000d2590075510612001901e41443d900660b00a4041e0900c0d0010305902c042820a68940307190858159 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 951598848 1250 951597598 951597601
    0x140408071b0e04061d0a0c081018170412030e030c030c1507171903050a090c05040236030712020319140d05030105090a0e030414040b06040806 63
    0xc401c64490303a14000020410056881d14014552151000d40080c0105030381e21100240300b8504032811810741c03038503000d4a000c000542024012042c1a20039107400e80591f514441082d1050f100b1403650750000307030525070b150802d41ca075820b580034208031342031582d60100408110100c1d03071009080440d00c40c1d41d5003244601c6a2061500304200203490b04e000794050803010303c01d5601c20411860944480c01a00d480c0d6406081404c8001310b03915260104a000040600380440a5110300030603800c55202402240c58003c041004c03500e001901500d03014980f241031240d454039400900c2807860620822000d004140e01e19140310039080039400d9803290034114842141002c0c444940204200f4512030180c02d000d801090719560300d10014070740f05600002c07402c10070906031070f04000044220201c6142c0101c1c007401800d154400c3c0522407058007950005100781c0c92600410b0403a880d440091420030346040078640600f081b04001c2a8455100d030020860341d121680508000c010040040c8a40d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 951600098 1250 951598848 951598853
    0x6051303080f030a1505101d06030901020c0f0a110127090f14011a0f040b030703061406160b09070b0d06150813020f120a0303090c06180b09010314040807 68
    0x100d415080840040030000e445c00c00c615903404100316508490343c2410740d68020b82d02c044080c04208031001d194001008010310201d480158007801d00064080c0445020b08800c8507519078030b000b8160020449681b940741d03895a54810500d60030041307241c14000000303039100350080f040d003c01130b0000d03010301f03a0380c0310848098819800741b2811540e400480850950429071400710305142e100c000200b412002400a90074160107040f00c00070584034194580340c1c249290010081e2a040c8500d0809540c7c00700f1490385071400000705c400100300c0c00c041d0a00c0d21800e95541e48102c1d002800c82e21039008448001440480c00001440340c141c1118000807407504060700038001e6151180440300300001903080003403c24000c0c2ca050025a0100c071240c5103403926030700040d5149440d1981da1924050724241c2010035030150002806036100e00e419000c10358071020f045400c6180003480030004e49540d14104540f8041c0c1c07000b004e4100303040c90042450481421100100d038002d0702c2c01c83d05003034005000000e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 951601348 1250 951600098 951600101
    0x702220e0606100906020601050d03090812040f06031413060615020a0c151209170f0a090503010e030901080c16050d09050f01050304030f2a150c080106051303080f030a 74
    0xc903c5034905190000d9400d018000750782d4401401164002e48141c00c90806150180003904c0080c0130283c01c5075140320102c1882071141e0010310940107000040c6002080b094001c2c0140c40501281c03156107805c554a000c480300c00c0e205402d2054600c0c0d0340d20000454044802940380c070700c00c0960b030014040d49400349400c00c008001603000c480e00d40190b000c45c01c03500b07a010203400e0400e1394068001c00d1742689401d00140000c40118032103c0d41000050700000d40c5c486502400a000703243c0c442d030040d240c1e200c1c181400d1f00c040c2c141c500c0f241c1d00100540d52096004480542d0410001c4024074149440460f4520403001c00500c02d40d0647c1c4041c6e8090b00150341b240c140405003d041c0d51502c0413140440020f85035000150000b818440401c070b8500c440e5101d000100d01d107800f8001d01546514000c5040004442c0c07140301a1a0701101c88492591103a4034098040042c04070354410785241c0c60180111502c0d00168418000c0f03030044030000000c201c050700074000311041c44030400e42e42d0a01d40b20170700 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 951602598 1250 951601348 951601369
    0xc070c0e06090408030915151c0c170309190e01080304030b010311060c01090602030a0c080f071115010e0105011b03090b0912030706020702010912080702220e0606 72
    0x6404000310003004407640b9414101504540c2c01910f003500c903120303919502c5c1016410500703070584020300340400c10407030b0008207481d00c0040c1c1918244401b0016101c203088441c030100d006440e6554503c410000920101445860801d0450503031341810109d000080300e81816070301030720508120755020b0050404101030180100320402c01185840c1c030350364a486090805210191858022000300b00d103d40b00d0388101e417980a5480002c01200099180001c000e4006503926640a03140c01b4074a070080e80a40580c40c0148124040c1044036500d402c41185e0910500c1003554030382c003440c603200c5101460480d00601a0002440035015507050100041a00c4490b505010010940b54900b10100b90098201403c0d01c00c40140c039075442ca003160100310550b20007c901c00840c0300004141c01805069409003407c240300741c0e0351070380c2d03d07a460310401c5044100c0000a01002d508000400040c5402c008401041d0f040041900881c1030300c1c030364141202c40d2042494141d412907406c122640c5030441021 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 951603848 1250 951602598 951602609
    0x1209031502071e03020607030207020f10030e0d052a010b090406020909060915014a0102070501021002031f0806090d0f0215040c0305010203011509060503010b121e0c070c 75
    0x506460f1013614020b41c1c401000d04040141035000034040155102d0305031a4040c4a00501844600750130001c0040007050b00e000003146500801c001151014454021208070300d5101080054500440c6405108451180c01e036904a40da00e40fa94407443d2036042e001441940182d400584501c910003e100b0030540c0100442c4c826510381c01044000a00000d09060040080ca01170203000c1c0d84108030499408145c042003440c000c9032003c200c80480d042d0050403042c801950032030f2612001001681d65032078a00402c1d0251700008480d41c50031410707a000c2c680c000b40c015070107030120808440c840c15217080c582044080d5007000f410484204000c11400c08024400e16020041a09203100292581c282c143c515210200311000304050242505042000d1504580211b50702e5941741081c0d0000b508524008004c190301210005000b030140302035038100c840d62440180341c0001480242000c40005203840020706000c000c003043d50070805180c0340303e10740d544003c03552507806050610924a640c0e018 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 951605098 1250 951603848 951603893
    0x1302121e0916090c030e0f160b0405152b230f060609040905010e01140906070905100c0b1512010b0a0b03040c080d080a050106110a120903150207 64
    0x340900b8441d060411040f107501d140c0004102001c00c008601030200c0844e40c409511a0503c8010502404030740050101c164400c1c018200e903588094441f540200c1c0303e1103901c07140091031000c01900f104001c200040540c00d00ca414691000b011040441002002d1410940d591941034100011000100c00c500300c11820f00d0200d02e000f2424400104002b01401d002cbc0c8400304003000c1640742da0704101000755115001303004215040448500820204140314400401e41c008181450b03000700c0c00a00911081d9140c0054504010621a0044401c0b50900810000f01c18440114a003d884503000d1140090704600781050390003000220604201071401c240d140010000541e92024035010480b4069003400c0c0d161b50b29424412603880711580801064041c4840c0181b41e140c0c402d12141c440c03403146504000b6039803200c40c1190032040c4051456065404030701c040c1c0c04207000c021001a621000e103071000e28035442ea0384101d817442c900b48004019a801186140400642442080052940914 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 951606348 1250 951605098 951605113
    0x1c09241119171308100b010f09210605070806041b080103110607050304090b04110703020c121c03020309011119050d18050a0209070315051302121e09 66
    0x42800c00c6403850301c801060320103603044002040d501d080590b10a4680e00160780815981c8a0240e0f44448041d07240102c054035210310080c0075030248104040c9a0165030700d9808040c10321a45140454109819020321013015584100080b043d000b05407141136140d5419407030341068000d000a482c154850b44030320078003c507866000c01e03604c1000d03a81166041170420030f07808a0785004c100360b48110134024105010006002c07407008900d42200d000440203842c10044401c024035040b00e1402a2040100181c00640c0a0000e52a00d100001d0021319014103881d501c440302e0040e0704524140f0082e00c4080b0342c02000300724451100b88503e0700f020501411103413400208510141d0703e10800b0441000b0303c2804502071040000603400b64224051500b60074500892070f0030700c159111000c40089110f1001c3c00c0001b204144240246e100102c072900070799503807a04020400120302450a404640154207008a810000180b82028011003070704c461a03102029519149880c2d010040101920746c1c850300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 951607598 1250 951606348 951606373
    0x18082206050a080a090503070c031209050a0302060903010b10200a08090d05070509070c260a050702010e030105070c2001080a0b0117040c261c092411 66
    0x301101c2c4003003600d1074485040d136121000c920050480040141081c84080351400c1004800a0144192070055820214007951940708480b840321a001e0550400749205082006060103001340143c0341c0020004078044207098080341c0500b65140001002a6500071510101011260060345441075000640400343c280d80720809240f1035184600d010b101d049624105002d803d02107100a407800501d0264a170912000042c8090003889080d10b000c080707968001e0344107440703c801c1c840400c2d60603c1c150034002000b07001d441c40d0700700c40d0007a410300100d00c0301100d09030b50030321800e48250740c40e8603940120065418800340d001000a03240c46440c55003040e042c4a13230303004401c1301c2e8012103000d00403604e00304d011300407210980b00010181c403403074030442400f0401002c10000da0a50302c903041d40c5564a8041c1c01d01c40b20200c801c0c5c3ca0b040c5c0c584c11843c1140f141e1046035540c6084c1d00c13901d0410b40d9407940c1e994240e80207034000f9401c184d4401201c80c0c4140d40c540d0b100211020f4000070100815102449a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 951608848 1250 951607598 951607607
    0x6050f060a0f050706090b060108090c030a02040506040e0604060f050f040f0f031103031528120501110d0b0442210c0503010519020a0318082206 64
    0x30340c4a209100109152114580c89042100d0065031702c4042405480c01c80d00e00240c10304000d40390035021070680400554480c0000895001040005006102d0b141564091100925001e8002c0ea082611203210743c40040d02002058000c0d4401c220000d24550040c07080002c4900190900e04082040302c14400440c0741100380345202500141c503102d6007000303850103850602c800c00e4400074501012040141621304540b01707441150b000d4070094114032082c4035010a4440701440d00016140c090002d10454004481d91078006100700300004108200341680c08003030b0882180700f5103098071290812814101401549114030042c40c40ea015100000382c0000c15004440001108024150314030154400120705c041c0240441001e6004200c240310404100c040d428100b501e10043c40355001981d810140306580c803c02101510320301c195500c47c00d00000e03503c0500108101074a505696210040301300728440802c0c85440c005a85502d10f44440b000282450303106441c005480030200007282c1c01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 951610098 1250 951608848 951608857
    0x507090b01390b0a050714030919170c03030411030303010f050618090112062007021005040503070603050a0e060114100c1b030b15150c030918070306050f06 69
    0xc460300e81032100040b62150541c6009450180048485800f801843c40481e4041e03401810f4554909100102c1c03401c407035007244810340f01180c1c00d904c100000d1310250300c3c000c00000e0781d03032007402c60072001810a402c2c02c20980140003c600d9a40000092200f00844001d034061a80010703409541190b241001075458507a03c1c0c400c00c0d000d0030001880400031160074951480b51b4070300420401c4a542c64400c00d84500340780582c200c0e901464101044c544d02a0650308030890780041c01d80342e25084aa038280b0800c0070302403d003402441028000800c07941c1c0d050007850094005a0350006036485c0101d000015900307000c510380c2d5143c01901c0103000000c2070001210b90401c090343d85034208a20040101d6240d10a010064131035021001c3c1d5042a50650000030200c9014900010203611194111000c0c1d180e52203480d5440700740c04070004031041245020f40119100301e02602c0c108000c15010070f00c2540340913980e8140110480400480c9501403040c40c0143c00d003a5035681103c81c4020100703110b4880c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 951611348 1250 951610098 951610157
    0x51303060621020a1802160302100c02011b180e0924060a23040f050a0c080705030f1905282c0316080a020d0f02031207030b0d0507090b01 61
    0x2400e170a11000d001d1540445075140801940800c4c0d500d85030500944804001d602c00c4152420010740c0c1c02c44c03a00c14003403140c003a0340f000604070390713121910703425100b0825011440b010910f020b20000f80e01030801040e00e00c110380d801c0191251843c0c0c1800b4074210070076030816140303040ca02400d020b00e54844c850454261840c1d01001c0100500d14a092440003c0e031454080c0d110b41804545125401c0540000b4040c24400100340030500c0050420b407421802200c001d40004d0040c400a040c041400405941246040401066815007003c2c400181d400440342d0701341d4103458182030301e84c403005000781201c4440300b0a01003003520312940351405120708a401075800f003868000304442e140c0040c0102d6a404903100c03011003454013140751207009070300841d403004094000c5180402d8050301405080880c00d01c1d6502039071a21075000c004480680000d0104001c05541ea02142c0c1d8684a82102170300003030180008102d454a803413180d105a509280d01241041040b40451840740340390081100c0041 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 951612598 1250 951611348 951611369
    0xf02030d0e0108250806040f0606020c0f1c110d06050903190201052701180f1106040b07020d0f05061008010e0a081611060708030610020f060115051303060621020a 72
    0x1160500011f02500306810301400040c0751540010362690002104441004107031420b1561a804008100d041074a0241449a010903c0c44800003c0c015600d225040c80c40100707078940c0d2008540b2540c1c1112800c4591a80700e0348006009000021190003c000a0305288000c2c04a0b141c20180b00410041c50112003141700700a88000c41203140070b41241c614082d1140103070034500c0c52410201c1c5062603028007542e40a86800000300141814011a01a150060346980c506001d1368240300321284801401d40d000c4500ca04104002001480418014101810f4a18046d1b041507102821100495180903083d40034100440004002d0429903a1100441050710790100c0346050200465100c4100e1a6000c0c4001071000d08101651010314002c55054403821040456050280e07944c1d590920752500750b91004004100320302c070880c2c0c0f48030401d072503141c81030400d200c80603a1200c4000a820407110103481d403809120074071002d8148150100d2a051125805410f034000c1446070010780940039140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 951613848 1250 951612598 951612601
    0x705030403120801050a140f1e090106030c11160b03070917010f0c18140105120a050108010e030708030f07030b120d12021309090f02030d0e01082508 66
    0x4001441628001c41d0000000c0003590322490700142640800d01600e40309100d030b881c0100b01500240c410046590000d09101420608041002500c0c00d0305042180c2c6000504107824035a01c5401c1c80c14000c1421f0f40b0040740c14281c0c0381d000382441020701c2950095900c1110400420001b603110740c4100d40010b08000d50300d8882180403680540039805c600f0100014000340041a501580306802c0c0d4140c60307034100400200c801c4d003140d105020002425160000c1c0405000006082c0d034142903111050402c1443c000e28044800c2c5040b0040b0340c1507113545e0b564001003101e02400e029240c80700030041c0185240c03d03040c0d41c40030b540e4000070700b500381410001d400044140d8002d5018a800314401850000d41c90311050300c2d2a56464070b0700707a500016403440140495074109000f41e88000e103042915001d101d0424500100404820b001038540e500b180642d00c3c05603c2c2404851000b0002e556041d1100e80d0040003d8442500a0958405040444441c0c0804c0e01c050803c2039180e10f80713140c8595107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 951615098 1250 951613848 951613853
    0x12031d25030519050106060e1011010e01060b0301051833130f110901050702040b0307030614090d0807051611031c18050906131404030c050c030c03070b07 68
    0x1a2106900010001d2148503005004a548060043c6050348960000c0c403007a52075400c1152801c138030310351094000d0360840191702c0013400303008007030010103a0f000002003407241d140c003907403d40701560310119011200000500c00f0341403550b07901c0000d0100ca201c8041070304240c1e0b14120520b00e0f5458100302c0d8060315069040458018101611440c40185100380445525440c4402000c108040c070880030b14000341da11340c0c000d4500035991120030507106c00c2e0904075141c0a0002625800141c41d506014110001c80022110311411003c403094081030000f078a05000c085141c1245405080144040380301045040c0794044101c600e4803903004108000308007289080007100504209880c0d02d8040c2a109443c1050812a08610b402e1241d80d8074215001c00c007042a848001c0d4091550082003d90000b11581400c800d40d00a983c141c181c0001c100790047c49c602240304090b54100c000580141c4040140a001c01500c801d0f03030012005000a2410500002c0d5a410188201c5060748404a0031105 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 951616348 1250 951615098 951615163
    0x14040503070b15030604030302030f1303080c0c03040b070804051201090b0402062a0c0319150b0604031b03060501051e010e030a0605010e10060203040617060d0f12031d 74
    0xc080340044c0c2101c1c0e15040524018004c0d40003210100000480400081c28030242c2c100c0756030942da05926001d0698951203030200781540310340d0365805070f88020440004e40d50200c03030060103014011026035454504210421030080100c0110204580c1050741c00c00100350300340c10707003500668115503241d60f816041a9030403140b40351240c44c1941480f2031213030202403040070503e071401c001c00f01c1c281c3e00289441902022556800c1d240039202441010301c400c1c41072142d078896100b415000340309604082c0c0c4c036550b4000e21480c032420001c9140d5050410000c100c0640602405030804036500e448104403080003141000c100418141001405001781400e0b0700c0500000c400c1d16003084d0188040d6071039503000134040c0000e848074a82840c034480002091407001c4192810b544603030f600e0080140c4403540c09044902e01811103980200414010350016030712104d0180054405e00c600c51120103201405021034a80d0b00d200000a580036182c049840e20205441c00700303110000030303103a20380700d800c05200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 951617598 1250 951616348 951616381
    0xf060801021c06090212151c0302100f091a06041104030c0e07030b100e011e08090105070203041a0d020c0105010e2401200a0c0b0403050114040503070b 67
    0x24480d440060b444261904101e04030041d1640808140100ca0341c03514400101e103e0b140b54412188400c80100f907c110b4008541213103860014204000464100c0100781d5440f0307d20003c42c00b581c000e40c210b042c0a01e8600482403d010440030811460110744c40d00301e1001c10001000030048813810000340240d6596024511500403818259183c1d5140d00d0003a0800d1168001c50072111400c6000034a650b21a000b03442d81c1d100e01400544208140140039110301c80720843c4a070512407508404401150905003142c83c10415580b90a940e0501e80b090b0781c01c496000e0815021500200824099160111540c04210300690349041e591404545d2000081c0110a400001c5500b03000c00010b0f403100316010203000e48a92540d04546010040300071000890712940140410204c100350000c407440e04131501d214101400c1a6002410744c0d035100903003140715401203000c1d0840405c0074024060244110a600f41c64841034a02c64201522025034900030b259009000600007000942c0790b00341d520001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 951618705 1107 951617598 951617609
    0xa0302060304030903050a030f1b05060712020c0304140307090605310e0d18210503070501050a14092a21030309070e010b04090f06 58
    0xc05919000103109a062010080002020407024840c00903428800d0792502c020100c0c101d001b80c040b82d200360f0300120a5003441c50113000a100017407115006000360030400385081220200c44003a101d4212406118000400e002a09850140d051840c5000c00c80580d103901d030712860b48800b112010f00c0760641c015a01500d00c05060407810400407003516008103e440145242ca2070303000d0380c8484086001c580d105108400c001030340040704040941004442d070300407610300b01e4211680e4600c0c14143c090001010f03280000c000e010001c0710b11142d4480000d204d0382c40c0c1280c26130003e01c03543d85110007588802d000685103c40109603061000d000300300501c007201e1000e2406004006544600380c00241c0c1d40480362851040b0b405a240e010204030045913a4070304013407018144002c691000c0c0c8444c84100041c05201c05074001d840a4a00f00d440008a40712900303400805841e095001 = true := by decide +kernel

theorem cover : BRFrame.Cov 951438848 951618705 := by
  have h0 := BRFrame.cov_init 951438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 951438848 ≤ n) (h2 : n < 951618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
