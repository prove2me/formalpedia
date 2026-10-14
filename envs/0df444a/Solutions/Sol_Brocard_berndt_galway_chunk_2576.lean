-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2576
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:07:36.731981+00:00
-- url     : https://prove2.me/submissions/12861145-13d2-4dc1-9d59-481e298eeebf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 463129496 ≤ n < 463309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 463130746 1250 463129496 463129501
    0x130608030a030c090f03030c0212030f0f0a180b190201020301150315051005040602192015030a060603060e0f060114090402040e0a0b120c040b062505060f01050102060609 75
    0x1c035040c4c9901d130b00c03074220300c0300f0354202201b819441154007c0d81c500a44d030040320b9100041c0d15a90382d1040c055a00c107071540900020100c020080c009148860541c078000c0740648040b02002d51080c002c3d407040c600c031580001c441d15000e4550a50100c401c50b80d0000f141190b14000c0e4403140c07840078034001d108060b40c80c102404400d0b001100b003070260001900365003807045070380d03400361042d0700c14041c84025201d80f81d404814111090444a0403a900078405128044d006200d44c0003000241055644072050640064130b03041010069807142c242c0318004110f1a1070f11901404481440c1c0180c158519071408029600e0008504160060320030702e4900140820b0b540704013554003c0a40c80c603840360001400090010900720401e000303a00c8400c04200d40005c00d020000006c0741245900c406401104620403035150541c007080880f400a44100e10749407640c82500104804180ba0030f0008846d03000caa000c0c803008000b0325501010300c0a00041c59410302c40041d6881c4c0c80100302e00d106260300b500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 463131996 1250 463130746 463130771
    0x4030f0f050f131d06030f0d021203042604050a0503071a03060114030a09110d020a061b1406040506130503030a201305151312020a0503060a0902130608030a03 70
    0x4410000b445000040401043c2c001d00c84500050245c0c1d103039100e032161030701901040101180080092038940c0040000341450f13100007546820061042e00c00c140d540f0b0031002e48480300e841d58241c5500203007841c1e90341c3d0300b460200415103906d034111a000b0f601c402000d00016a01c44040107a480b01d5403a01034032961484d0040301c0c44410460800007002c0c001c000c1c4054589550402c0180900c01e15100e4444562101880720182c0a40c9001c0c0d404681460300304005405104550782140301d40c2c8141000c54204e4030341c1030300740c2504e04291146a001800300803e02c0010b100c1250040307c0c04081c030030941000c0e01c0312075590002500c05940940e86901c06a00380b200240b1075020454129103464841469059504081c13015201d034034041c0702c008145101e402d06c410201d6045001640541820508200354040503031420902241c100f80081d1010402d99401c00c1018800e030308000d40400c03005038034418003008000e000b1804c43d980e820010305000d240408000da4080040d18500090ba1000161 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 463133246 1250 463131996 463132027
    0x604020f040819150504020108040f0c0b04030b01140d0201090e0a02040f090903020606040506061b2104090b0103090b06270c090102013b0a05070b0304030f0f050f 72
    0x9000754420701c2408203050b205200f880941d01542d01a04034980c0f2843c0c0300c40703010180c44c001c690080c002a40d000c0050300082000004100040c020801c50907d55242c91840303c1591254000740c4500840380010040c12090f14281c69000105a60200790071080d640043c0c003400d59400f0301c4602961045c0007804140c620b40c1500c0c0102101801090f0003503031800300c0d10061400701c0e81900140600703000180c1e141064056540506030141c44240b0700842741844038102c20003132841180a0103010321b101c145420040e808a900311500b070741c469407149070040100031a81c0300540300c1d040c54140800180810810b40c0d6466006a007900c3c4456120070b4200740c90203400c504a0781280280340b040c1440181d0308080e0141c00e04050a8001b0032006141500744498081b41c05080c001103886001c2d0024074059059080c40061045000c8510003241c80e80c41d2410200f0035001006071360400f1007003005060b4482e200202d6054241450700703c038149400003c0103440750a804c2604140000b40000b81c0300c0317000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 463134496 1250 463133246 463133249
    0x20909010b030a0c080616080c2107030c0215060907030203060631050603040c0b0f190c23060720030304050307031107060504061409220f0c05030604020f04 69
    0x500f40e0b10000d00c030385842005180c036070042108034480e100000e811036000ca24000515100741d141c0701040d550300215a08960311002c51070f090200d51021a80b04003803a01102805800c43e41c40100c0c0804034018020300e000c0031401d44d4403100c0505000d10005845100b6440d40140441c83d002da5030350784180100d4040e1142040341100c0c6040c00e0b62145030f030486d8840700a0035a09141c800d50443d03950f84100041404151006001c0511514080082411501c024030700c1010b08180141031201e07812600600b900500b54810200d050840780710100007103001d600e0300700b003c214000c0409811001d1100c0d40d0745001080b800c107000800c840c1c0211081020380c62a20440c1c0030003225a00d20349490f01c0d40c0c40c0c1d04407480480125840d40d1845400d103801103140c1c419541d060740c402e030815141000848202428a0300401c2c19001006003094580b40c002010101c103030801e00d07442e000c51002205800b1124601103500307600d8a4140390802040c1d02008803504844105c40158680d918105140780a1041c0d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 463135746 1250 463134496 463134499
    0x150d02060a03050405060703091109071b20041e11090d080c120a050a08040201030f050c0a0f05040f060534030f0c030c030c06091e1b030b04020909010b 67
    0x4601c007110a54103421140c4100d103d482581e41d6a12400d4054058402080d802000703880c418482260030300700299000d611030100e10b490000e4038040d801d0403c651140c541c054907110b078080008071504004090303105e02c0c00c3d01542d04200c1c1070300700301c04519003601c1c1041000029889201c2c8100c0c0712a2001900c50389d81004050000501c4545059905940940c2a600e401d000d0408494a14840c40058440d4417001b6280c0324074044085904807001d01000b00300b01d0616a0301c83c1100d04e0304540d0f202d05071144001c0d81130755035140b0580001070520f1001c90250320410204000500c5240b82c220b03244400c90385142803007a203400062980380c14140c0d404020b81141e000404100340342c103070540c6603403680034041d844014400d20403e504903640718080b500035000c22400390038800020310403070801e41841d001c1da8001550b050700b6500c48501215162703075000c028004105000a00840c1d03000d1a501c1410116180d04042c615034640480000052000c1e1040d640480002d207140000c0d041303184500c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 463136996 1250 463135746 463135759
    0x2090c0306130c021e1c0810080a0c1d161d06030403090510030c0f110f1c0e0405010509040303150801050108030301090c08280209060706240608150d02 67
    0x20104000d5503080003100813800301c80b11000700400c0e0032000c80c000200050361b541041406801c00ca0030b844401018062034902c1d00030390400a2114024010054210f104003140480039151201c14896003100c030380d00090100582e002c1c040e2034a2078514100300322006080c24041030b450070352151002c401c0c0c10071094114a0010810041581c013408070340036114202c0d500c89181c0c01120f001c80c107d40c02800040c0218510b035042c1007016000d203d02c1d01c6108603c1c412114000c400c1c0f00d0441c01c10340954074800244882040c01191950049042c03d407000c1e00743c1d07040080d503141000081c3d04510140025081c160b86405200f15400a0400803010f807409000910580d41d64121b55a89c0b42e009208034004c2d940342c440441ca403070f8424080c450041c1c072007a20783d8458084114243d080c0b4040183c0306591a40c0c200070a1910741c90790303409001418003580c40042d1165400c0380b010b488d0507050b200c00c608200044014080b05070441145900044c200e0702d0324100c48006000b2401001887d440603602c80c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 463138246 1250 463136996 463137011
    0xa0204020d14010b070807173603010b0105041202061909090c031a102303091905210913020711030705030d1413121b0302090c030613 59
    0x12856001a02c82a034121424081682c1ea080064018061100d0040c5001c80410007200400c00944013005c00c50003014406262107030307a00c8400001904100d01c03105042180918001050f55034881f01412502038000307000034028080001c184d48203078014003880c08010100c038000d5444003410707108918419030032901c4840c0c940401904154461007403d6145007050304001c4003c0c402e002d9640c803184000b00030340c00d0700119410020310004c00c02210080251101c03035007041c84a02c0842240080002142d0366480c14500318150406000390400551016100f40403400a45c001034810381c04080c0c41142c03014406801003803042442840807099004c0040300b40303102c0c05c102542c001c002d00e5102e0203640c8605407481080c15214601881110341c50b4008107103580314140034095603454010b89410140c540f003002e10040821a6403504201e41c45655440d0040422030302c41000d2400044440c000ca40031031548c0d000444284000740f030344801c0103010002c64503645440107441d03142c4044a000b03010f03d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 463139496 1250 463138246 463138267
    0xe1905150c0a0c0e191811040b3303100e0a06050315060f09070e060d0615050a080a050c0316020a0609240216060e120a0203030f07050c07090b01020a020402 69
    0x304ea0030b0703520f0f00ca001d011180941501040e44544442e600969912842200d510f03210b600000b8518410140c2190b182c00000c42c165030745443d4116180e541040d034480e421030140007041c48010004207204c1486040060105046070302e42c8280440c0c54a501100d480d64484000d04040d00e5180e00c82a0148150b0045517800711800c140306103c0d102c16201b031080350306c00c0c5003008580141036402e840400c2d1400240e09007802c02600410f5000b030072003808614641c0d0340100c405160b030180e611a00003500407074150352541e44680095000f28409006100e0b40c20101e0751a9113034840600300f001120b840c0c50312007038141c0c020300c180c00c0c410341c00c14010456904c207410700c8100310199041142c100d00c0c0a03040c0b01072300c00c0c032842511042500e4a03074440c40300496548072030050458043d207554030302c00c4080b504c06480901004100d010400c1d03025644a00b031907900c5c8116003501902035802c3c84428404540c51080004001040711100388000c6181000c03500107030f040541100c0003a400500015001c4401c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 463140746 1250 463139496 463139519
    0x120f010212091507030c030221041a012d080d0c03030c02010608070317300105040e030a080a0f060801060e060108010605041503110a0e1905150c0a0c 66
    0x400e180903110542561002c5001e03850b034000c1c0515143c19090003000c60116032180d0b0202000c02c0031030400620301403068044051800b1404814592020380c1d00801041150003c1004203c3d075081489600075410100080e00c1403500325a110141c00085c2602a622210700880000419408090b2000050b04d5000100102e81c941019000300303003004d0712200c1c0240305200e5007013140e2819010f801d0307003410341e43c030310401008185000c3e0f0121403e00c029041e500d1070022100d5034403042002401000b110340c1010382c5c80841640118821450905204425000032048030307441c55552130020803039690f001b06e1000811003c1c4001c0c2c07080349043e5000c22500415404a02036400740c60301050b42e03035250801154000c80900a00300081c100380010040d86603011030440440640e400c022445154101500410342c220046060001344252820001c034204524400c41054081e0000c10310f1a0404011400701001c20300922101c02000035031a003690402d225482c4410b6100e050240d0350380c0d445c5511080c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 463141996 1250 463140746 463140757
    0x13290301091d28020604090c0815031c2006090304050a0b031b1e070c21024002070506010806130303020c0115151713060b120f0102 58
    0x60603125010044503610000c1c943ea80d0310600fa010750ba0440607419200003110702d44500b02d030040f005200200b2115800d014240d09911141e4456800c0d25010120700d080c55100241540030780c00510480141c04422035582d43c00d0000c50800035284130400809015101c0c166508801ca4047e0809000c2c85040200090017112011181d500070580c46400803901e502c41552090304002009e007030340004440d4400070f40111080180b030300c0b0790b02d08400701c032a04035400720b00202c950384c60900040c003401284104a02100c4810340c03c1c14003110460780800c8401c9202c150460b030000c1d0042101030900c464414042507050240a00b040d080003203a4508041d400050003194140500c0002180e2035900142441c82103412030304c00e03050000503031130a0f4029400510780d0342140d501e40d0a009104c400514001c4028103e070203641007500300641c0000c206010711401010301000c030005200007038248142c88194180c024100088040c090700000301442860f40540b40d107405200b00f0324030080c0041d40580b2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 463143246 1250 463141996 463142021
    0xb131116021206190b0a1d0408070b0106022415060c011112040317090606041e02192c12030403020d1109010f0e041104020d0f061404021329030109 65
    0x110f00c4001040030400b054050101503109a860003c111f580c110000d03a0000d000e680d07600d14045850b02d600e035001c142600400050303441302d481030704c0b400d040d4034080d8054541600245001d04206a441e0105286c05800038030401021a01c416803107029400301d8403081c000301055540b80110552a0090002140c040c2c001c561040440c640b551a43c0005a20030601d5001405031651982e04010040a101800da00207003c00503a1481880e40d910082c1031f45004928210340101d14007400401d24115414a052807503000c8100c90020115024040480d20b41140c1c41006894600e00d450b00c1d50103141d00196111500a0718101440b11344440030201007804c1d15212a41da803960300001360441c0c1407113403420a41030f950014000c04d04c0c9811400c40d5245c014005880c06149031a408251034803010f851054680d82e41003000114203c80300d0401c201c406850641c00c20300c44227510000241548150b0742e20304c050040c2d070102d25240320525a0801c1a28500c140c81e0350b103840c401d1004081e0300c40c119 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 463144496 1250 463143246 463143251
    0x50327120a061505011407030203121306150b0d0e0f0106120c0f1a0903070e07120b12030703120b0a0b09040506030a020a140303070b09010b13111602120619 69
    0x1640f909050403039a054800686464410895842c0c02c2c22982c0d00124054003140003c1c060011711060341050306001344084c140a10140403141440c07402c03910440e11860240031408c00c204400800e240c00d13a07011001910000070a0300786000f0b07a44c207100e02078200300c051394a4154041414210b002c2e2000030716000c1d1111403031440d10f82070140d030107030a68000c0c0014551400d501d4400180c80000804101801505540311103070303a201946802e42040e10808045013900003000049642880782c02052501121240031010070b0f0303444540c89104980002e403c014440840d84492a0950481d07400510068051095160f4034909411103030084441244241d013000c6c0800d44625002440740349182d0010640091356107003a06414691802d800d40700d4040c002488080c012900d0405c0c40780c483da00007400410314280340c0b030030800003903081000381c200b2910b002c5010907500840c2c815903082940d1140a41d804140f0b5000090340316818114400c4c0c0c81c030030b20b0704002800d545442c010300d81c01e0042806 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 463145746 1250 463144496 463144511
    0xf1202211b0309100207020f12010522020d033204140f090a0225051b01050a0f080c0412060e101a2106010306060503061003050327120a06 61
    0x1070194600c4192400a8190300c4402800244600343e4000c000c802d00c0180140a42c0c0402c201040c1c4502c072003141c0c10740d42e9564404101040d282c0c4541c11440303030305240c0f0001c0b504007164001101a410f81a0290402001c00761550328007030381c5942021018000b112400388540180c24450507988180601c40307a0307010742d081d101c4a90070880e005070742281c401841140e8943d113440200000b50401420912005011103142c103001c00d40901c0c1d45d2603d030043d4041c10701c0d01b00510910048800384201c10741001820003a03980300507449288a0142d110600d0940d1040d240d0800f00040303030045030000d21000311b50b80e0640b0100700065102c42c80341d2640d402601c096920400188003141d420100324240c00a807001d00175a1403500c0d503601d03e620b0784c601d070f40d24101c02c1c0a032046505c0e1a00913007084074000c0c0d890205100b24a0b080000c83ea21000c0c6122602006041d651030f16100c1c091058442d049440300c180030341003840040e8004000c1316000d011303098091fa08118141c0d46240f200c00a58134649031058 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 463146996 1250 463145746 463145791
    0x5070c08030316030608100f0f091b0b030601051914030f09100203090316020d061d0c04020306011713060507180b0c070b0f0702040501060f080a0504030f120221 71
    0x804d4201e404110144c11000607e485c884040c21445103d15134240d80c8107542c9901e200b641c480c1c01006070141481154039008180169000c00a079044006a00c0d428410007025a90060488200031050400004103106208055079142c5040194400d0f803030010040240c0750381090a030301e00c20b1900c0411a100424034400030b500b03d00c815900010329400420216403041c524144401e80d041c8042d0107281d0700c100c91b8644100304c2c0c500e800320741018280c00e03140c8400e04404000004c015501201d00b14558140080040c28aa901c4003002142c4d00c282000500920189400c0d11000303600f0000c180800d1034403a10082034850b040110400e03040020740c0100d90460200140c07403900000d10004c00c01c03a0304010b4140300f290083c842030322043c00100319036030060b00e0300d00919000708041d4484144005004001404c01c1c0f000514558110707190401304004654002801a079650041c1000c1000404c04030300700c80684580000e05a0078084000c49092a46803503041c540f01e00510401200b50005959 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 463148246 1250 463146996 463147001
    0x150405060a0515040b0a0507021009060c141504080306041104120318030f05150a021305040c54091a040c020d0e060c070b0a05070c0803031603 63
    0xc855a4010000c19070512003030604400c02010191243d21841c189580d6680421280c0d100e005d030f40000400120b449000c5041800541096512a0074088049414000c004011010b1142c003c1e08220b100055030032003400c14408176a41d42002155080e46103058100000241d005a801d180224a4203c20400e5845030b03200f0b4606581c000c1040e0017481c0395070b132021200881c1c075400ea03440220070340c00000001040703450304003103244c810005003c03021101020a118110000c1851400900400c16280310748070030413139a0705641d012640001c909843c90404c851069020a0f203d1440c2500802148180c8080721035542500d40b03d049031190910380840280b0040f036200180d0b2086050032401e000d1100d06800800014203444002c008201c038030000074054600301240200581c002000c030410003603105280e000c0070360080e075869260440c02c90203569038100307601c900240c00c2c80106000719441c1c403600445944035080030301500f03d180c94921031170304c81c2e0080e10101c008d508142440500c2c94041d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 463149496 1250 463148246 463148251
    0x618060703060b03040f020a170616030209061b1014040506010501050a200a0b040b0f1807050103020717041d0f06090403080402210a02041a030303011a041d150405 72
    0x49103410343d21586e8a08042504000c422a40b1105490740494070400680c00d841c610544140205070300c1c2005201a40d80c040d004840c4030805004010400c1c0030385402049404040d070f901058000142d03c24810743c00c00e20b031515045c8030181070000d215008160304584501641c0a0000d880030791341d80f9001983c552086110a801250510040f6848000700107c2c00a00000000c1510b0327981300aa90342c040c10204c220b404a584050040620250441c4411255402255050062014000442c2803a600d201d140329107810103800051840410260002d0108041246c3d208551101c1e140c8001f02001120300292800b200c0f088800140c5944030195410300800020340b02045580b00d5031801c0f03c564030300800598002040c1a4114201c41c1241c02a1140d0300c0c2d802c0103031002c103040d441000140c468561540d030010790a18031140e040d07034012007200d04480000da00d0f010f40340a1b170038544006010b01d41c0105080b100d0346415200c100f29401c4241c1c4262503484034a030b5285907800c100300844005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 463150746 1250 463149496 463149509
    0x5180c040204120b19050f0708060a0305100c05040801111225030b031c110f010207080f0a120501060305040c05090906041712011202030d08190c11061806070306 71
    0x7141c0c01c4a02042c1d103441c0d04e54000fa5407400b200c0d45203181040700015114165803110752001840204107100350301112003500034504940003480c0a180d42c80300b5130390302c0341d810340082c10681d81c1040c11f00c694003032011240280f0032003000f8024451100000c06894000000040341c801901c40007030940b0340f05d000410140d046a03501c003421039100101c210020401d215803540c162161201d03189503103051154003e80c980e40d0782d540c00701d091080d2240e54103100407005080035aa0044c00854001000041074070605070401511548a14a040085541c02d070100b041602551071b10300049005903158001c680b090b40181c0d80440c05a550310140602048110385d10b0400b9000311020500107103040850202c20314204220f681440c0c000e80805407000c1c42a4020345011210074072a074110f040c05c0c008801d0030310550030600c40910301200040c00c2540880d00070010700d5980c010004c2000c2c0038510039050949020101c8d0103604c0c08626440c03880100c6290110b103407184a00040400f1310900608041c0c420 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 463151996 1250 463150746 463150769
    0x5090616050a08130204020d1509020f1b07050603010311150403030f03201c0f02070f3003051503161a1204050d030f0b090105010c0c0905180c040204 66
    0x51503104450fa0b400151108521081c100d00c0b4a01598a9001902c0010445140040d08800400b5400903c00c050ba2200501e40d0050001f924003c01d8030041c0e50401501808a060342c4600200c1d0764100741d029000542e00c0003003c0004800d0160410081040850540d0482145141081c01e4401c42c0154400100094406070b940e094041c0300390400d1245000c0014010380d01040c9039846607a030780290000c40401c11064040c080e100700e0740d001c1d2108441a1480461034041c07240c80d044c501c14907182000d400c00c80c82c8500c4039880c1c882907401c01c0341000920082c0c041120520340041c0500004e4458040141d001000307403200c1e150201c2c101f01c006501c030402243d810b04e40019403038242e421060304103040d85c0600050401590b0208490310451081010309100c110f40f038030280480d0107000c0c1c250401864244011400d882d12031413241519400d080c0a00c0c007895918001400400300e4001c40e1469041c281071242c2480752041c4080e4914505059401e00380c035403014030049010b02d202d0400140d8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 463153246 1250 463151996 463152007
    0xc0f0f030819031506050705070f0302150c150112120908030912120307090e011d0105040e0307020312030610050f1911162c0708070207050a090509061605 68
    0x16042d40d050840303000035003000304071648001c10340c50700c6401c690301401c0882c5d00015404104842401400c001d44801c00b5000c448072b080d500400e101a10145100b21407000020303503894060f00c10415000020b44d40030301e82c2c0c410f603110891414100c81d02c50040706c03009159511600a54011b0000318256040d000c021403c00d1119401c1210074801188840e0250082c003a1440c10112903030f00440c4141401d84881001a00c0c00c00e43c1e4824010503072040c1080d852488445080035201100d070740c1150070442d804540c0c1201c0710b009d80e0561203034200096062050f110351102c0d00c420311001d14451807040b110415814030009003664035201d811948a144d400c00c12000001c00c07141107a00f441c3c26440d18043e4060440d40025514000b0501c07201050040b04100401040b000c00000d00480348901c001103110aa045821108080010300700d041403050100002d0141882006014024100103298008099480b400180100b03020b4403120b125019290020314070144840401c4a4540076955140c0742c1f0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 463154496 1250 463153246 463153267
    0x30b1608150d060603060516110619020c0604140c0307120807030c170702040f021603110309030307030509121c0507030306090905300f07020a0806040c0f0f0308 71
    0x20100078181903031203a0038038001000714906124080245118003c006140d080a0541140480089801404008409001406212001c1005170708005842c03c8580c4d403402c0115011f005c0d015500a0101c2032050f00108000d07c162000030304041c84080342910a02001a0309054541d28030f07000715002e00c08070900e540c0008111100502a0754080d1904404004c0c0350344d284039040445403026042041e01060400661409200c1d2505400d01054114501400300b40d611001d0144c1c8003002d402e10040828010903660244112212a003000302580e0740e0b5101850048e280e6001125814000c51070420b40c00241000060400b0a4400344c4100c240d050048200c1200c00f94401e5900b101007503110000000c1c1c000c5d9038016403102c188141c0152038031070107803008205810080b400d00d2908d03045406140c00d0400d042c4e0101c452301c4480301e01c0c140d540d4186001185102c503003580100c48600c00c8d9800c00052010324440039041d240c0c2c4900c40c820301651044845030150240c0006041903c08100000302d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 463155746 1250 463154496 463154521
    0x3311030a0c020d0b010e01031104050709050402030709150903060b0f0a05060c0724080709050a05040e0c03030a03020408070902030c09120c130c120207120309020a1a04030b1608 78
    0x8600c018088031850403c0d03075030340001030001c0e800100d03035410680c014010413841c0d11840c454500242d40401007031815a4004203010301170b00c2450701496000001c9400b10340306000c96070103440e2807074079030510803e0b00c0f5009141480b01d100640320245030500c290400d02e046101c400166000030414de0303025041030200070350340d40903030400b890510441c040022001c0301c0556203090920100008214038852603806032400b00002c203080200600e400c018442c5585050050051381d030162400100d40d805654101c0ca40b5500d0b441c110b605120228040b41d18030b40c550010703c20345200800391903000e680c03540d2400c140d000c291080d0500b40014859100c5900746032000c00701007800c0004948607203c8030741c08981074109126002c900c1d252182ea08100803a000318469202c00a0094210b203000d0039a00c0310000c0c02e00c0d40310100205a254841401955036264400d4050030848001072201d011005184040d50721034802101e005030b0500000f43c1c000e0a036007030034503000f145490321001d0b65602180f4611 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 463156996 1250 463155746 463155767
    0x30c0507020a0e0c0705100b0f030f060711030f0c0a02030708070605030403030b060f031603241502030405090a0f05060a0b0d090302031e030109140c0d0c05043311030a 74
    0x4c103410b040c440d103030105104002c0035150317500910b8005880100d002c248496030102c2c82401d4000d500120141404200c0002d08030b600201e28500f2000111311039012a00314455103030b015204076004103c020700b86e8408074075180910310860480f0707d49da644d02e2002e174684103d03214a8011603001d10000e00800d0098001c030703201d002d0042140c2d24145441d58500940d4006a508107158003030004d001081d6a0180b00b5000e43d210001d16850040d000080c00c400485032034040c1d80108601c4070303c0100d07024003c10680d00038210051060049145c00c00080008000181ea4000400d05003400f0a40301d040030480c901c25a11440010740c40c0004c000c078140082c2c5401e403411421440204010070000c00156424040c130b100500c40c00c2d50783d500d055103800948050002441c00e046038030b41408010198541100c400c0521802c0100b54540c0080c000c1c1c45074001d5601214000009600b50130a01e07080e03003909541c00d44110618545c0d00d0a00c84100c4d08041010001c0b0b80302e40c03041140c4860301c1c3c0076404290 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 463158246 1250 463156996 463157011
    0x150f0312080c0706050a0209090603060606040b070c12050a0318050a0b1e0301170c18190603080d09060f060317071506032102010207050c120a0c15030c0507020a0e 72
    0x2840c203c4a991140300300c800440340740c00041e81c0455009601d14203500c0342c90300464100d000304240d091800c0010395a01c00d0b031241007651000028800e081002601c50580241020060000c04078481e0801a447d1034407050110300191041810f0703e52100410b4004003524400307858140c11a092820503640e078ae1000100a04109101640c081240745660055018201e0001e030050149074840e070291a181010003168800e05820500e01d82182c10918859400449008880c101030f1a00198400401c3c007904050601c1200040d550b0800205810032440786100d00c13020086001461407600845a16020003084080e211513038400d52420200588a40b03800303041c1c0180c413010030303406d00011282aa441100c03014225400b80441c0b00c030945252903001c40c0d5000035403800414bc0d4038140c0300e111040416205091030505526031800810400c408213501c040061074090311a0603041c11074419411500000703040c40000002d1911502c01d13503d0080d070141c183c000060500030f40102240c001803015 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 463159496 1250 463158246 463158271
    0x26010f060f05030f0c091f030f120813020117070909060f031b0f0306021c09050a0209010b0c1c1e090501021902182503150f031208 58
    0x208254921403050800508190100004092410007858200305142030324100940040e01d8111058a500c0005644428040c500103e88501025240d030090321580000d4540c0c611800e009041001e212042d00120301e49840d89000740d0b036842c01f1600021058040203000a04620800e826041d0180445401030100e0414a9105449100210480d40290701c00f640c022926407080060150700070107892841c84141d01d4881c1c40c0d040242800c00c00c5002d10004100c07543c0002c507140230114003411000c3c20340d81d040080c80700b11400c0c141165158010001680b2800501000061401e41c03801103583c008603c1c0080d1440da000100800540c0004404000038003200912160032680e10f846140b48120707880e1500d07507070641070000092401e00030801f00c181d1400901c13188070260303443d001248000f20b003204c10024159112003901428226101810994840c019080003445815400a4240c907010381e0754440c00f20350341d034404100005184005401101219a402c40d5140304803291a44800d45080c02c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 463160746 1250 463159496 463159511
    0x1c020d02012025060f0c0f02010507120513050907121a06030403080108070803030c160f140309090f0c0a0c030903080a2a0c1806030b130b070503012601 67
    0x302e00f04483c00e00384000c1e00300019000000d0340500c1e9180c2c4003800d0180340040c502285d0450240c034952540703d02622082c1550f080c2c0045a201c1c00c1240c0c446580704041841d02c841d0000c000d4840d420410018240301075802010413a4144449401e207c0c0b1000d07600d48003115a00f01d03000c00100b5500004c4070036034807204a04016901c0320002580100d10a565005596240c00800341c1090100e4100c1e5849400800500401c0040740c0c050302c44a950102e078080c7c240000349800e64804d0480c42c0024003c100f0541c04000c4290003102034001810240c86844c1550b40e10511589800b82c1102c03e2020100700380080a103440c400c005002c41c1c54030038140414070b9034603611684100d4202015010000b1280d43c0c002e012514110b1625440c005890342d91040310802d640c511491050701d00608080724032290651600c00780c1c41d00884004c40d040007041100b8203040711b082181508072a000e413801040304008c90104c4d482101120b0403603070032a2411421011101c80003c000300750341f400c10000c0d921605c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 463161996 1250 463160746 463160807
    0x111c09170c0307030b0603061f0329070504080c0411030f06150d09020109120201021f020d021801020d0c1104050411100c02090a020a09050f061303060501051c020d0201 74
    0x1550f000b86000311100c900300d2810500b00b40c170b0b0400007400d01e070015003206103550000d5291035600c0705803a4090396030044a000c4094003502920610503040d1a200c0d50400c1c4150741d41c0100080041e03501070400c0d10f6088900f42d0a00098800c080d128000e503860420000e0307801c1c401c05550a030027130380060010600381c1040000402c2500b00c84400c408040c0d0fa07007203007000c547c1c00095010043c0000342c02c51041e04040d4002030f446500250742d03441003c1070300c8003803940b019541c2c0c100c3d00c82c0c022948046482e01c1c0e00b00c5030b09140900f0140142d000d40302c0c0b01c1a10182c0c5000c3c0881041035540250040210301c16442400050003018004441e0749003800d11aa801d540e401c00141034140300e994401000488600410146040252961b150544100103140034250b004003c1000d640d000d68814001103a03400c04249540b0401c8200c501040b1201400f10400299400260480c2d20403288210310800390194082a8058070100940c0540902c0e00c020040d401360b085000902c80c20f660fa5595a500d014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 463163246 1250 463161996 463162003
    0xe16090b0d05090115030f0311010e160f0801060b07060c0e06030f07140a09030318092a0f05040509070905190501030e0a17030901020f0a111c09170c03 67
    0x1c0c1c8901503607442d0700400480c2c500c00d100303401c0b00fa412111004034040c55512400789400d8042400b8080004036114404291425000040c40751601d170100c0d003911003800180d046180303960140c01d8078541042c0c00000c000c1e8050090005030303680c54034240d00d0801d241e030b5038400415001410405004840780385180c1030b0356410185201d03502c20f820780b03070b11858000001400c0c1d4541d4808182c00240070300c0b141d4041684024a8815264103051a20743c0d4035400c54025440071180d4800c0c8100380c10400300701e40c1c05494104c10a4401d8603003440d82c41d00705a681007036036458400210342c0000f9000b40010400d52505a0150760000d005044c039994042e1a40b000c41e03803070001e140d103440c0c1805407940c040000b540d0501c04c51044c0d01108016050310040c950300c02e0860900c981881c191a0004008110704010039812241c541c1380c0341c0141d81d503440b0440380241c0a0024800c1895482c080c1c00c0240c1d0040c4c0924103a0b002c00500360b80d48140c0b59051042c0089490b141040005c1c4520908000300b20030348080 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 463164496 1250 463163246 463163257
    0x5090a0e0a060615020106060801050d05072c010611060415020903070801021314090c070822060e04090b19060302030307080403110a03080d020d09061b03050a060e16090b 75
    0xc01e0301140f91401c0c003c0000054010300340c08011607152207420040e1550026109043d107008803058070507902e1609001e45403d4141d004580500c45500030030341c10341d44001d12000200e60b81121806160b80c1c1b203c00b070340c03225004440305c1565004a40002d00041c00240000900e002d0a80d00509000c10000400d15111040d044081e07a6940000e030300100820610f0010020074a03150401244003051011440380413014151301c0007000301040e100b0802c1000c43c1031f5004040c01c090b1088011501e400c00f44001d00c1c0c584a084040391071030b00189214245801110085038210003000080d031a9551820f0001d8845c0d20020b648a940b45c00220060b03400348020f00c0e445000c2c160310f9827640d0660400f1200e016801c5001d038810b0240f020308200013103500b001d80b00954080440181c852064102c0030b4040c09003d40000c146038506100c50796905030311000715001500c0f80e0340c10086a510131b80c11400b185c803a4000c50007140e001600240345d0700c0000100e868008250b15000350544d94030071101c18541c102 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 463165746 1250 463164496 463164503
    0x5060a0e1021060e0a0207020f0d0303021c061a16020910090608010b040b040c02060c030a180b0406051f030b100305072304090f03030f1d0c130c050405090a0e0a 71
    0x854030104242d013441c02d00e45820001a141c11850a1301650000e2100c0d020000f166010b00030600a50040c94040d0707064444424000e4120340705020300b070251800506181c000e0b80d08250507a41141040840d030400d0780d030140c00c038071440301600103560200b042c80c55005080400300340501c80041055201c0d80200d230018645903002003850300e5a00c04000940c0c080d4800c1034004ca00d0715103694912341d40025025044038005605076941d464240d1010068200015000100407004004804000910074035a100e82e005480030041611038444986440d154600c050032a12004c180070702c041080d4030740103a000607031069668a0940e80c1e984240c11b01c002503028042d40640c0c4400040c0d525425240004813040841d001c00401c205566841a20411400f0180406645541240c0d81c52003c3c0c1c821010040518a048096001101c0301a0359400c10032410f070088828106100c586080342c014212007120507143c0d28280b43c200b00c240240450f0007484101c0175334a60721015040b11061052401c614003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 463166996 1250 463165746 463165751
    0x510030207030e0f030a0b09010906020a0c060506120607030b030a0f03110d020303010b0d02161b050109081903030c05040e040804060f08101a121f05060a0e1021 71
    0x46402c01030200e180d415000d90160b603804042c100e080d9008a04200481d80c0704001c48200d4440101950051600d400300801c124130000780c044d100c5070440301d00990316105882c1440b1680d0744506201c01012840c1d01c520040d03100c200498a00303406900083c90584c0050221071540203103490701618005051420343c04a41c0144208030950800d020350641c0d0744040c0001d504d15403502111584030321507170007111f16640e03003c1100c020b2850305d0041e070003070710340c0107540c050a0742905280010000d83c1780c03040e01e000c40c03025080001c13100400b0441d0082d0440001a4400d001000d407030075800391004117082d8040003000c006c00f04101c190841c0c910300550081e10030503151410030740c010740b0711440c0d14685d80a0201c00c0d8200300000b0b2880c0e05c00000c0d25009030314410b0703184114188801c1409441c03c0710707814412000800c01401e0716401084007002d1802d0031102c20740da40700d0a01c10307288605442200000d10103850105117042629255034001082d1400e80088103e40c400c07100310403901d40c0c0415250b034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 463168246 1250 463166996 463167007
    0x6020f0f1201080d050313060915050703240605190c140309010201180f230f030304120f050a11070b1b061008210f030c130602150c090a05100302 64
    0x20450b1341000d80082c02c18525500303011b80781a6102c901a0302c01454a9143d05080c13041110b000c0711000c100509800c10b0140b400e00440c00790141c08480d4151030140c000c3d80c1c000024000304114a4200e40140c3c80741781c50b10200d00e041e0003e1454100c40e200034811521f040300b0000e1902d01201c10300d026100069074135082800002825a10150303c111003020050510304e010407500c089480080f940301040c001c4402d41e00901c6440c990f014a40415140140701a248080708040001c51082d4800e4108505480401c401560321000145215002030000d0000c040c0540c02020030300d0b21882c0260841d0b2207240e5864200c0382d41e41c800181407164040b00c80056401c1a41001010303003040e03202000744100d504103011a070307442c4018a00501d2045661030020040b02042003240d00c4070091060b460b0384d074901003e44044640c8090721000101c456071a0006082c0c0c800319810701440c0d04400c001041d620341c58003800541c4c10280040b0380c0b00540243c0051035558800e201060034005071409a282c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 463169496 1250 463168246 463168259
    0xb0402090604240512160c0c12110612130f0204061412010515040209120706050304030f0e031e0322090c020f0a020922030302030f180a06020f0f1201 66
    0xb240f00742042052050510410201140a0101d17076030028209174180385a40078134000301c2e140808114081c2c4082c510480200305041209130340315840b406040002c4440c6864000d000080c4101440c072246007410b0004a01c4000c0f030035940410b114040c010445c031a4242da0001400c6501540c020304010b030713101c40140b1180c2410503101c451022400000c0056145c0065114601021003010b00d200c0e42e80020000e50310703607400100000700300c00c040c111014151070301c5010b01664810354095020804659600c0180d83c030070b04da0004081c5000e406019021300c140b45940d002c01d04100c0300100d42c0010310400d4a0382006154103e102e035054001492414a130840c0001100c0005140c201190800f00d0004003c500006082d50041d40c1904c1c96209a0348a4900401840c004080d01d800c01868003119018554550080c50040c503107140c00301a2525890107400406841a0000e202d50308044c08034004502e481c2c1c060407503545030321041441d02c00611002826a8020359901a01045460051001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 463170746 1250 463169496 463169549
    0x30a0507030905070501050912120408120307090e0604020706141816050f04060305030403032c030d0809072606010b070206030c0a1e0f0e03030310090b0402090604 72
    0x1401d0411201c0c50340d0321815103800b25405414140440080d900246450b080000c3c10701d04055820b840c1c0c40300186138401c003d607000740b00c2e0300c51030320450101c3d030940c48049003120b0040c0c02d0380d00d40181d400c0c900894040d030100f0040c40c2d00d9115a082c00a20046503031402107140b031100406c100c0d4041d252055106000304455503d080440d842a4072000c0113030b1414203001c06958088406e80d03503082c15400000e0140025800003045404086000400c00d50843c10f480523040c0381c0c4400c0490070111400300404032a0088010343e156010b881351f031031050700071440c3c1504011400191803085403556000354007580414142800c42452100c40d0203802c0f0240700c545d01610328448107514014942c0c0024800307010181004007000400601d81a425000300407407556501700114105a154643c0805402d801c0e1035260b40c0081080640011014900417044070321030b111044a0140d12410000220b00070042800c42641050b8200080d00140d59040003900c010045440c408030003501000401380c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 463171996 1250 463170746 463170751
    0x140109030801240507110604080601090f020a050a2f0309040e070b0403120e040c032c12070c031515060905030309061602120c15161b0b030c030a05 65
    0x203169031034115003510f044401c0210040180b10b80341c420345402d5941400300c804c0da90600c84540c4030400080010350680003040c00780c100c800f01c00301088980e4984c0360b504260f10440c00c00400050b02001803411060180e040310300321000c40700714a405040300c02c4401c040e0b14030b080b0aa4100b82d0003c81d102c03d0170b160034011701c100c0d918000b000d040503d2610520904501407800020b103025801e088030f952041c0315041140d000b210061084c0210180010042c0003840300d03110715030440440e4141d503014041c2c0300f480500b000034640e0050009404c01034100b070458000610454040100e2200000400d01e010345410603403d00c208001117400004400c140815000e60001003071055940040240d40da01001381c40c42c456040d01c0303850b03540a00941a41c030301550100003c0d8000007103e000103c40c01d000803c114440400e8900c48005108440c044c40d450041500f110f03030310b00818400200141407c600d0140203031030648103502546d1a14009525900101e071440c00b418000303c10001950313a9401142e4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 463173246 1250 463171996 463172009
    0x30b03010f05150415050f13050708040606060215071d03030c0c0108100e010e0414010c09080d03021810020c0d05010f1b0c0605100f060302041e0b0414010309140109030801 76
    0x84007200c4c60080380e15441252080fa0311500401100d4200740d11103d003000115823004c40b04000741d10f082c1501401ea410251000e40d000c81c90008045000da000240d41241c02c601294944080d40c0d40d19401c994001307200301c500e141886200b81c80402920200083d1440c000f2040180003003220302000180403010080408070041440001005840d03c0f0f10645415140c0340c4a519800c2c1e075440c1800810082505180c00d0b00d90b19001c500c0d0005540a8007540690307140b80165003600f01d260000310164011074103a510250b1042c152044030345442b1094a41043d44c1d80141c45d0204007000014800d604000d01c1603515075100c0300c3c90804401c0c18424010700d41c510000c18020300940d1103006005400c0e614009102560355000301c0c030a02c1c0c9005480e0300512407425140d00031601d842004020b900130f03104000f22048904c40301180b4600c15446c020903034183c1d00e43c0305d0400e498210812022600040020306040e990202c80d00440d040b4072203201041040720010840700380510340105080016444034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 463174496 1250 463173246 463173251
    0xc121b0a1211090114091c05030a120e07090b031c0507120201020313061a031906050f06030c060f1303080909070806060307030b150a020d0f0203090907030c030b03010f051504 77
    0xc2c1990b1380040841402609000c5170680300c50140020a000303001a84501c808404a4080c0c0000c000001004041c08885030f0f403161046d0840034026410340d142c550b2001c403541c001750400d00050300182e010b280341e480000e0440c2d0350b00307110f40300b504a40c0000c2203802c03001070b05c001120b00a20103010a2b5251000f1148000c40c41d514082401441540540f44020086030b1100b4210174a140070b0200c04048403001016602c1c0a05402c91481140119050407150b40c3c0c14074000601d0700b40c3c82420144656009405400c10045032070030400540d01a00610607590014000c1c113844191200e000e02c050b501c2503115941d1600004200409090001c00304d9040040030000c2240c00d0301d5400c10380c4c1e0040e40500300442c03a00046000900c00540c00d03440c0000450340030400800040d4002030300c400c0906252140e141c0c404000900b00d0700c910070308000a41040c0c01c10082020503202c1c1d482203914410703610300001c008407024000703801c0d0ba0f0000100058151a642070048025504001d9100601c04039000c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 463175746 1250 463174496 463174507
    0x1302130c0e03072408060607060c110705030604020d080f120a060302040f090f020909010914010219021516030608031909050402180405060103110a021b090c121b0a1211 74
    0x4030303204184d500300d181007280034000b05180b80c6031074007910b4800340e00c000b00f0700c220780d80703000020402000444100c0c03061045040008082c00c0c0416518021a001741c0110800300030b5444a64407a40710480040c00707d03030104550040d00041c402240e0041000042c04034025256004200c2907e0240c00c0d610f0506203842240380c00100c07010018803030282d0641d084c0015540d10a48503004005c0154090050340c0c8500d22180e800c001940103000e08010b80901c01032485941000700d80d00c80e00c584030040b50507004408645103c9158251041c90103952801290b01a243c6141d5030640e00543c0d5003030396040140c0e4004000d2030304107920340c001c1c2c0415902103041c49007444809010700d01e18100b0a000342d64036404100d00d80d110b50861609256202c42d031907690221100700071340d5601c00c00454062000c20705401c15462038901e05c000c1c054a0381105103420a0541800c15007100c50181c02403000307409180500b01c40c0554140034082e400c400751250a00c0401f5001c2c4c0405850700b218100c61800d404014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 463176996 1250 463175746 463175789
    0x50901030f171206010309080f04060c140309031207110604060507120806030a1106090901030f0b010e071707090f09020a020705030f0312101a03090f06010e1302130c0e0307 76
    0x20fa0340ea20640c240b9011403c41143e003064000c5204020446061003400600490000d400004203d102882691290464444d074080f6035164080e161540750700d41c0100c1d40020740c0c102c8513405824018020080c05040c0c0d4820700010710558403d91014001c1080401d00c8000d0100c107040d07180c1d0f078013100d04101c109032802c64000ba440d40d004010082441c0e07629002140103442c6e400031b07201501e001401380110795840b800d10311601c00003648103c034044042800802d40811415021f801940070b916140074140f441d5941400161008018004025100d1000916079401d00e044000600e400600180c1e59181d00e071000342440c0c3d69412880c042c0d44a01c216508030040001290314030411401340a0740da40320001401e207415200e90240a4640c035100442c40401c103004000d40c007480a00302142c10020200032a02e84a080920038220380c1031000b0009040d19801c503d0310107901e031004006589551410544030205e40380c500c41c8800055240d0b0800749541405c02c07049010700480f803041b8250b00c03176504 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 463178246 1250 463176996 463177027
    0x1e10080402090105010c050c0604030c0302090714030f0c091e0a0b0405030d050c070f08071404051302040c05090d050a0c06110c0402071e121d061207020304050901030f17 75
    0x3003442d0400c04448464807d100c0300b031000503082c180040c0019911581c0e82030404140445000c00ea00c0b414500e8041640d0b640031340349203014480134418442c02c40c3d4444580c01810600144044c161900c1000101c00303c1d0390340c0b02c0b0601c019a500c0e0f044031119140000b0300956400e5a0080701500e0010842400940c1d1300142c034800605203460155510110340b03031482d0504949911807902040504c1002c201c615005c54404240c810b142d10754445c8050440422050342c80030344101c101805225840405803e281d000368401901c2e82c01c004d4940054100490a0820484402d03181030300b210240204104c07040b4a0a030040009183c0841303007000c60042c0c00e482d15110341100e03124550006100c8104641450070300e40e4030101d800c08144054090400c0d64003200c00c1c00d1031000280f0101c3d40072070001e60240c1c1c20700c03040300003411031420b1051050605511420180c09002580710502001500c2da8450840c0d501940c425414410131503920703d081d0400b0740032001310b0b0307040c42c4051103885450010030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 463179496 1250 463178246 463178249
    0xa0209030c06090d02060309060106120b06091002070b0d0e1905071401020a0b04051006090606050924030c0a0314060d150e0102040602032502090615091e100804020901 74
    0x4445281e0b6030f1440c0c1e03000625503001994003e402c40c0e804004c020418070081500c0f4108c0752951148600301c02041050004c941d0074101e59a0f03c030809214001c1141030544c09542d82c42102d0045980580d00d420010001d50031000c80300018540707541c1c0c22084010240008146c20443c01040b0441c0c1c5016a1040d0b21030360f02d40995668403040703040601e52603101f04144407403540c02174000c2d446400c00c1c5c01c00b2034440e048462400c00d0302e03040c0a000140040c2510801c021511960349040c21b1070390110403c500e04440710166041041f40e01a903003180c144120085020725001107100b0380c0e4440c1300c00041c09035031021345034402019001c020820303d500c61825140301d03103034007400f0700300604003042405000f4288484951010740c030120300421125000002050301c00040c0c9219450000900700d00c0c0142c440403100203400400b11004201581070141d078480709140c0e01c2c01d503913049c101c40388080790200c0104840e9803403202118140042e1828201c003002a180f17a1490b09580520305038010808001c0117 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 463180746 1250 463179496 463179499
    0xe060a08010e040804050918010c020d20010906060f03031d1f1110240f05060705031e04030b01082a0f120705100f0927050a0906050a0209030c 63
    0x10000043c0030092600210f80c0604801002c2128605296071080d800d00310a038406100e540ca080c9003034042c00e00019602100400958a21000c2494010750b80d15016410382c0f000450740d203032941c42000ad159070107200090800c042100512604c1d50400a22501600a440303015007808002d40c1040d8403190301e040e0303c082200c0c513483c180620424045030003a683e03035940c501c140102000a4910320f00fa822010241d80b03540748055814070b610018025000c881d01c1500460360440c07030100524204a00038049240c011020b89041030080c207400003c1c1e0354140700300c801d86940060141700700700710112040e015284a01c0149802010060031014082c841d0f0f488100d6003a03e0345952110b0740d2215800c0e280301c0c2010700103c21400c3c070914840d545801d54040c1c1c034441c8000048404505201e02004041352443c0e0341c0e108126898080d0096803200b1840c80c44444141c61689104601c1c140c1c0a614003039484100c0014451019042120441e000901039504250040202685940e80020004030741c820 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 463181996 1250 463180746 463180769
    0x20105220b0402010909150303031b1b17030108071a090303030403080a0b04020d020301030b090c0904240501080a03090f08030405090603070302090711060106031803050d0f05160e060a0801 83
    0x44500040c1d80101c0164443c10400d400e121b40790348089500d2600e0030489100b510b082c000a4500903d2006888004822f080082d958209400840150400118045008110544001ca411003c50080e94026007002d501c6500c407100030000b01200312001106004505412400c0070810000640c480c800074201070104002e0501185a504e09940300c281c20342c01c018011542d400d44891000040e4000344000d9521080c40707000104099408111240b02d08001007061200d039503181e85142c80078036040200c4941c0d0700c41e10042031140d075681c403845001e001c000000740104696460011700c420441c0c8c0094013907140c03561080102030000002d403019203200b10307100c103002e07560040468603002d00750703201070741c042c0003c4140094240c000444082c00e000c00c03004c7e40c0582ea200d810036015107094120798080d0201c5081c01001091180d4068094580270420104480d00010008410303035200341c0b1010700e00b04901d8201356005070003402d4252007407810340341c0c6c078141484500b01824235041446800744051 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 463183246 1250 463181996 463182001
    0x2160c0b1e091c030c170708030411220608010506062a0a020a24170a0b12030f091f020601091d01060602030c010c030519020901051608121e040813030f0b07020105220b 74
    0x43e074000701040342e001540014040c804242000b4cc0c090142403081d10310075407030702000c514181880c40807100f02d9494410081021401ca10710900883c0c1450300300501400740006600c010383c0d8010803100101654450440c40d4455003e13485102601c0c4078011040c0410440308076082e41c1001c1106d503029001c1c660000b0500c400c403020419400210402020500001031305000d100c02c000050103501c2c0303050310b00c51200f0148034101c0b02944031201c0c00034056441030780100941a06074010340100c0403040c82c48a40d18040a58040c25510b540c4c0207000544c001242c2c4625180c0700b4820038401c507203645024800c42c2050078050815a10001d45100415000140e101544e40038000b2a020309008441c1c88480c46070078246810309070402e032112000c07070000300082404160f01000d9144241100007164409445a580d410307103a80c045062100324051211b00000412580d040f440215400303903100035454609900000c1c21511b006141c030070840d031400f1840381e520001c0d0620a885507800300b00e580030358 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 463184496 1250 463183246 463183249
    0x70b06040b0f0a03060c030c0f080a0504080c06040b07020d02010b0901031202030c1204050a14010e0904110a080f010e190b0a0f02160c0b1e091c030c170708030411 72
    0x1e80c1c008100d03a00304010141c004100042e42c6c1c002240c8000710f5074208491000000100d03446d5a80150000005076000b0214202c505c1c95400150400d21036494a03281070304880006c0c0c18070604440a40b001840e0804102c0c00d01c0d0180032110304014140b0003040000e0080300013690781d480c10f002c0503040f01c49404074074841c80d0080003250001c0721003a08940c0034003040342d1800d415900600880d0300484030310b080056033f030213506468410b81805864040030000000c05201c101c540c02001691042c3c16000c1c42420394030303216284009408aa00a00548600034807202d094403a500c5c4508a02d0740700c3c443c040c240c40342c00c0044006440d8001200180c548a20030508043c00415100b0000c8910020b003030b81240b14171007003502416100307030000c080700e65a8101c45d2545000d01e01c074140c0304120480c0119852401c0c1d4005002944d0020a030440702070700c2c117100c1000d20714102c0c1c0031404100941c400206001700101020761800d44100810b1038403460b541c910445010241c0010415a20010b03100101e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 463185746 1250 463184496 463184509
    0x16051902030915031611011104030f030908011a0d030c061803110309060406050a05090a14030d03060501020c28120c0b03010302060703030b040e060f10050301050c120903071421070b06040b 83
    0x511000488c500c4d01d072500ca0610b034105da51901012000304250300400242484180107000e40480201256400700c080d0205100740f035041c090381202001900312180000030074500c144415100f0810b03040840805920b0060b10100c201c0003d6081a4020f0180134100e985e001c04580a4407181d10f409034442e4a581001d507454002c607041d055024061800201d60015543d400f040c04d00e034100d040f01d1603251310f1036080e000c0314800e00500380160000800303910075041c02215120880c156a003000c00780e4801d13210034403401c0440e42142c0301903045824020107204001404c9030250541c42d001350300d59407450380060494410200000e06058854582c0b07115940d0f0395000c0608460500b090f1280c5182c101403100481c40100c56102040e0688071001c59542014420720703100d80085035141d40390000c1c0d0503c0c6145040c000708501c519100c01c000510020310040003210039030070107200610800c90549000c5011036580e0051740c0400c4000c0c800c240101c1c00600049800140981d400508900c150010401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 463186996 1250 463185746 463185761
    0xd2006070f0803190213050f031f0504050c010807051c2a02060114060301030212010615020106150c03120b031c0503100e040b1605190203091503161101 67
    0x303124054481c2000d014101008500c682d40c5180f5040702044128500c0b400c07805034032125001e1240790b181c140080d06207072048002d503050017012540180c0840402c20746e16100340c5c6078445415100d401780401c02c82c0403c04140c1e840c2d000d080c240401c0c5000f24008101f40601203c1405205c6407900c45c9100f03080c5039015504c41383d04420845102c0c41118810340e07251002d5030300140184140000060302004030035002c0c1110364028003c40c0703103074610703020080c46100d115501c440555131500c000600408024400034917800c1500041582e903d0201e19082d807420442651082c0207182903246e002950200406010345e0481900284007018070011900c0e124140b03c4540da0f030300300c5d2200d03c41d0458001c0302443c0300e440d41c000980b0640d42c517001c212849610a0f10001c2c451856130f404250042082445014002441d15001e820f1101481c6040b450100c80401c4e0005078000051903405400c0100c030940281764010b5070645036040c44402407072200e100c840b0480402422001d0010302540a410600303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 463188246 1250 463186996 463187003
    0x2d0a0c1110171509040b0f0c0c0705010309050106050916090f06050a0516150614060c0d050304050a0213050906090601080d0323181e0d080403020f1e010b0d200607 72
    0x605c1c0b0709403600746102c20040e80c41c42c40003800c000000c0c050020381c0003104d41400020010780391061605c0019005400c0c481c5003241d03155203c40010410340c882d0301c5800c0c8030b28080480003191910b0460040c0410105820031036138852024424400f050700002201c00d2000da03446d0903907031401b40f810701041035599942c004200d000c0013510079125001c2034000c0e0060740c0c0091280681c0d11441c008200281c070a01d404255150085a80c0e46180c81c00f400141d035010b0f000d17005030b41136a05143c0c0000c0341141e400001c0822a940e6400703000201c40104480b1382d0118424000b06074550404030050341e00c80d2900175900800d038803810352540689601007854890aa40c005120450070722424104c0c0b0701d0760b01c0c40d00c07070b81c40d10035901441c40801000c078138030600602c020003500300c040043c603040340d076500010000c0c1e080d84203a800014038040100a40305c1b15845c1c10040c161407880b5071030390f142550180a440384c840d5680e0031031500824510802001100050b4200703007140d109440100c0c2140c0280000603 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 463189496 1250 463188246 463188259
    0x30e010c0207050103110903073803040c2309071701090b0f150409090807120c0302060106170a0b030a050703080d050601030608032d0a0c11101715 65
    0x2109501c1d000600c0c101910701c02d0303c040c07140340380120894005008203404103070705911a0008002070740a00d81d0096a005640022480b499000d9045d0213445502110420503040004100402d1007030300c90b29007001d012798000e045440d1000e01c5402048d09500c40c1c0c1148124401c0f4041031089000380d107024001b180204c00e4504542c2e4681d200343c02031200c2d00703101d030281015443c0309806103030031080c144402c2801c03040641098100b48456008220300c6000301c41e045403c00140340801c0700c010a804054503a5543c510314210b1a00e002410044107a0249007441211580c030002114400100d0741e000d429400d001885200110000c0c1c41c02504040182080c0181e082c0842405001001080c2e6841c01c0c58050196880304001101214010302c18102e0301d400038089401503c203064070041145890702103032000c0c40306c8a6400d920540c003205112000c02c0500e9150010440b03502c2c2d9940c81c0c450120f40300c00d071a0001900240001c0521010110803113031b100005260800b102c240005079500281ca038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 463190746 1250 463189496 463189511
    0x31a03061602010b03340b03070e01030204270e1b0d020a050a0b1e09010f110c06030a090605010b07081b030f070c230a050607031b08250506041101030e01 68
    0x2101003030a030560b2032900d007510a40c00701e860829944100800c941c005840c7e2841e41ea0740810454884c400b450000381010340810001460050314242001c55074660442078501c0103548010104071042603400d21060741003c00c1864511007402440e90f030848040d506182e00301e603d1b1000034042d51240c3c00071644403010600200380000d00300f014018030b00e0f124420109010055259601c3c50007460349450016004824020310340340300b08a41012500710f40c046840e6240e80c0000518142c204642c1d098815030344850741010301501340103083c01464403a5100d450700c4090744600905200f190140f0058201280503801c07222400c00031290300c103803401e148540364005072038403112510729441444545c01d07140f00307450b0104d0301d20900c0c13040d8500001c00c4051118902024405260000d01054041c040c0b03c8118a41c0f91103400307070280f0142c6c8284038443d039412005900803210203021a0401c0c0c4500001581400a440003c4c2c00d60080c0d0003001c40482c030114040103d01801d280b6101254950801d4817 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 463191996 1250 463190746 463190773
    0x909010b03070f09080d141e0a02010606140306060a0908010509011406031f0c0302090604080d030507050c0a03140c190b1303021207020f0d030807031a03061602010b03 74
    0x550702801060b500d0f50301c82c08490303504030b64081c13060180307158a80081081502c4140580300d500ba49402421100e401d100c0079021484840d840300d50300b000f00c0540003c0c000b2070594284580406003030b00781000442c600e5100c50b91003040c0030083c5110b00031a00059442c0c1100e0180c00307400e00900c04100244010328040e4001800307840e80480b80c3d2820904080400c5843ca4041045100f0380b404405031a140e11b510165440501007010340342040c56420010000c00751910401000501315110040c00008656800201207810041100c030030080140709840e0020004104401031039013514060301003440c480300b095401c0c03181e000351070b900744a40030004049500030b680c4158110f010b0000800d00c3d945030744100e00e96140400000340180c004407401800e04160401406841d0b001410441c1070350070f05008207880480e905802d50101308030300200001c09905000e09008100800c0b1151860040341d00400c0e502e41001d80307000d504c82c2c02400044038440c401d510030040c03128024125a032415100e003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 463193246 1250 463191996 463192019
    0x30102070b130606060306053a03020115290c1f050f06010305060604051504080703210306180507030e071401030f05090a2603151315051302090901 65
    0xb42254030301d041103000504103000c0d10a040c1150400380101c500c2d20f800d446aa0700074458240e45000e44043c6082150840748400d80141010344a90000110150102c1310744450760100d5000e03580700201e14420300c2510703c0d10082c40c8004076228401940340c007559071403181048030600c6001c0010b282d04c0a0400b203454030340c005074043e488540302c001c02516210011400d45c2c01c211012504440104001c1001e4200210240212402c0480e06818540c80e40c1e205030078603641d030340196082240c1380700c50405650010b0103c0c0e45c00c01340742010000d591501b8000749103030389803010700003009907203000054000b4084d07001080c800c201442640d0f1460b880309081071224400c01002d9000a1900e03200036008410b80c403030359002e044503100400891100e41c0d00e2080700070302004007011904d41c84803440c038900901c501850003000440c1d00408503103c03a0040c4403204d09601e140341d517200e0402c000030700c0c448660b040b5807041d00c106581c210001021094440040d11901400e20740217405040006100340110 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 463194496 1250 463193246 463193281
    0x20d03050c0118110904020a18110c071706010302010c030518030a03081504060e0103120203120a060315050f1515040305010507080c0f0904050a0e1b03060a0606021b030102070b 78
    0x8400a01884040009101c00030208030390003900400d81c2070040c4244a2400b60300c4e030512071b9400c4041500002c5188140050f0807050342f060860344205010302c113440c841c2c3c0b14841c80e105010028512580b450b0002061024425000307028400c2c00a100141400c2080490710a000c0c060222120541a440c0040c614a801c0702e0440001c410001400078a250501805048031060642e000760740c1d0954a4602e11821420755400a502c0b041250305401e00e568141e841c42a5084100003508a2460402400140c059054003030f40501d040104510007200411882e040719640385802c0e0344001000110300e0008040000145106000c1070020030002c054000b0f41c0f0540d0142c7d03c1e9521a19284a90b43ca28000d000700c0250211080c890034a003420310ba440180e0100043d00f010038100c6034800c04906007410760115404011541d480c05840307040400006030030103101d1908109580c82c1c080025100d4203040c0c5420101c01c12010340f8042c42d42d0940568441503080123107150310781004100802c3c0203002 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 463195746 1250 463194496 463194503
    0x61009121203050a5411060a020a14032703010b0315070503190606030903110c0a030807140607020714010e0d0305090307180e07050a05030307020d03050c0118 70
    0x92400003100c0c00c40d40e01803c0b001064402c0103030046a04c104000c5c01c401210702050449402d00076207130955011808841440140540700500d00e58118203000c50006c060481030760048804000b80d0320040d500044144c820364000d12904a001c503000700950462040400608040700b140300905036140052503800200d40c01140200400405141070603122101d401c2c034002c0d110304010020f007145010320021035000da14a0360f0030f0844441d014a0404841d040c1d084a00040ea84920400c20150000c4088190b00080401400720407814000100300e90141c2c08000e10b03000000c660001040f041d280b001d6641d10403c403e49980340b038403840080d80c40d010b922441e0b80c410034040c0d13400c0240d401042035000501e8003508030390b111501520184ca05500a022282c0c01d807042000002d026191700042004088500305c000c030b501c00d8000c40c000d1401ea0705401980c4150040d49042005035000011100826810f5541c070b100303c0090f007000e440324020f22542d007038954288481d41520440365040c000d5028407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 463196996 1250 463195746 463195751
    0xe1018020a021b010c12020a0807080405090604200c010906020309010c02100903020c010806010c0b01030b150402030618075a051804060f05030c0d050303061009121203 74
    0x14030743c507050700c0000c0000d00e01d010510a1908502007a5040b128000101c650b0049403d880000e641e044c0c1c1d030344e0181c2d90656219602140502541c03030320307020391500080d045030705000c001c40d241c0341820045025a0780000650001803042c0e9401000e40185048681191007107443c4d14181040c1070107080c42c2040c0c18014002d0a507202c0307421940d4813842050503050f80c0200503030300403040151a0004068196030600900342820000200900682d90286206010503455800d004211320320141009070700d540f00e10300503c104501a100c0d0310000c8070070036070b060452802c4e403240113003500d04a02e85040003800d440b40740d5240408400225150104a0311802824200300308411070450100c4410907140143c290f903210380000c02c2c0706201a00c151410508040a0310700803030005000c652560b48130884c1e4910604040000789814000d84055507016107035050031050b01c0e9142e0b0340300e1000030542c900c16901d080d544c0342c20074400d0761880082d24000c10400348551480c2051a102e0182c1ca991000190 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 463198246 1250 463196996 463197013
    0x8011d071409241b061510050405030307150515091308160302010902090f01030b06010c0206040b1204021302071203091a0108033604090525030507050f0a0e1018020a02 74
    0x9130000e2924840c0300e1400e288102c44003013000300603c1200114000c0708001081c803010589603400e1006281c200d01c12405804810322240d84001601c0380107019a100c0c000610350080305485d5800f84960005450801000d501102e181c00c8200740190302a090145111085020805805601000050340201c889a07042c0c0c0e2080403810102009000041c07000e074034040842c01039401207000030710a5100a001c281000e8560108050719040010120510100e50080c4025820006112001200c220805501d08540741e140c0602080300030102408041d85da0782808144900200407080f050201d0801d00d0762542d503010680d613250003a003000d1050b6603c0300c40920600d04150016006984250b10383c0060445260401c001004508010344850080301848003204070300501030181c2e500d00c841c640c00345908504241c0d1518519030007250255412814580c015907070403e54900f01d030300c0803c950402d95070300c600250940c116a40039101202c000d10010446141c00d401401248403954212014507 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 463199496 1250 463198246 463198297
    0x82103250216140618010c022d030a030926061914040201120b12011401080f010e1b01020a050105150f01211d0d08011d07140924 57
    0x202d00103c4810380c85181001207000300d642100c0d2201e80340205042c818205070158020855026448506088402d54610202d0410030811640300d40d100c03065004160b80e130b100365006444461030b4050340c03805040329074024048480d10034410590f201c0d41c50036036419081045030180700407484064185001e040031b002c9501c827035034661031510540d01655111600046000d4800c020030464a16a0300701004418202c0088400d004503594030102c0f1700710321001c1d0303d440304060810803411000c108690405481503142c400005410720f0340c8c45402c2d10090403515120060f072a02c200068001c0080d403c040c10001442c6c0782e61807942482200b5506079102000c1752004442016801d4605645e80d0705d120090f01c00c030021644180c003080340c11884441080f0f803060150745442c1801a03003030000743d05200103026201080140700d550700f0700c0818501c028140040c4c09468045622040e004d1414081242d0107155107102a010301e80c0380580c0417140c41c46665540401d25400391140a000041d401d80d40785a5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 463200746 1250 463199496 463199519
    0x7030615170d02060a0216060203090307031716140c01050a151d040807060608060a0e0d03091112011b020109060c170f13080c0604020a082103250216 66
    0x803402c0301c0d805800e143e654811503500a41061244941c190302d903001c41d00000f03005200660103034964000842d1034404616000701400a000515201000100d040c40708000300a031402409412508003003252581c10544541c0303600407582e00260543c00c03c0e0502c40801004d601103221040c4121500c15046e4440d1505458012120105408100640001400b0a1040d0003505d01c1c540720b00c00c0459441e41c0d40d03c0040c501002525104040b82e03403009100d000410801007141400d20605040c41603101e1030b1110041010750000b101e000b400908140d8600d50004c1d8040005403c200c40a40154103074014001d0080c4800b03c0200d45480c541400c01401d28021028000b004c06003944a90040c1d6076841443c0700910094403c03200c50b40c00603006400254030324003520040300c006008240b0b6261500400201d400698001c21085d0024007880428151040114110701200c02503035650351900c844501745021811040b84000004000c40042c09501103118980ba0350722542003080c103030300d411a02a8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 463201996 1250 463200746 463200763
    0x709050a1b110d051c0203040203070302060703050409060905060105040b090a080706020a140c090c0a0318030302030603100c121805071706011e05150d09110102011410030f02030703061517 83
    0x248005c0c4400c6000004013a90000c50303000340f000e401c5d5011150b4950100304d840e0170107101200802e40c003003000d019410300340c4100d00040a160f0020b02240c104240040c14a1255008941d5050030000d140c90458454003500701c000d0060108850b6020740c0c801000352945003511003180c003008038084540444400040d00c541d8100001c01074020740d2a60710958556a0007074052400703054503070914103055185070240c600721728003035100941d80b450a8001c15040a8001980901041c03800d5800c280311540208600701c1c01c46003250010b207081041720030750485003007aa0020181d03c03c1c40d40120715059110b078030802c4070500b003044408030f9072150340400b10f0f01c2c0c07910003600c01081609010040b0b807030409485500180312071100791819580034945002c1d2204a10300343c0d03880000c1401c280055909115034504629401d00500e00c40c20300c04000d200d036020b5440041c10130501c40c880c8809558080c4400401140c0c0a9410010151204113042580180c1e10030b1499007001d8141106a006000c0766405 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 463203246 1250 463201996 463202017
    0x5070810180b06121002030c0304060b06030403020c04020f040e160e031f09030306050316080c060909010e0403031d0f0c09012d080304080c1e030709050a1b110d05 72
    0x10042e540c99081c02003032441c00c0c0c00c4044504c81c40300800c0c20005c2e544004e5000310305c4030803802e41e00c0c038250400c01d0a82d42c0741d40b00d0a02604e010400c1101099000c2007400ca800c2d02100c01598a0f900c11940c68402e000390b400900005030311205000402016000c00c00ca24043c6840e0381590303040c140b04250301c038004440d070091146611814040c56504a80c00b100f0700314402d040c00640e46864401003403426201c815403800f0112840d806016a039003c004542a1160460b9858a80305484001c5100040c061103807200540064010404060007a042407844540044161303481540d580f003004e9849100703100e076031000d006004283d0b80720b00381090014103861840d0298580c0440104120928041505407000b501868a4020580590510051008020300402880310f40748840410049014081007c43d416402004540090301d0200700c10086401c04040060380da994440a4806841506641510f0583c0120142c072101d030052540c10340b07550413000700e440008608000b40c4451181d040c005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 463204496 1250 463203246 463203263
    0x51209060108030a0c0813030b0708160203070303020c071224200304020d0206030106020f060a1a010c05010b040617060a0c020c1009030803010608160513030602090d0507081018 78
    0x250500381c054018005690f101d00d021b9450825001c001c1e1a895402e0741044511000c10b000740300b559544101090740003241281890041240c1c1a40603580340f198400040c141078002c50b520f00310280c00c0c04800020700842c0e100341800602c614010320180ba02d1001c428100c501138803240075441d101d208081c4da5403054200200d880000420110340751304024000c90340100781d03019080c016241c0402540c000c0502d50000d00d02a0041d508440c180140181102505490001c035010000b421801004030f8600a0034040c403104914142140035005200085421509280c0001180c2c143c5413002c04504400501351001600c030310b100802659441d03070075840141d1001803c140c092030b000a480807114010304041010913925550340100e40c0003680b122010889190804c0211a000354041d2000c90440c03a000c1c2ca0284405402d4080558a00024050650108001d2042d4032000001309006400400700c54140e80d940e42c4241d0fa40100c030361081040da00f891200b000c004200c000071042540c0c030242d030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 463205746 1250 463204496 463204507
    0xf01020f070f1407030308060406080c09010312050c010606050d0c020a020d02090702071802040509090a121b05010f05070912020607020f010311210c0c250f0605120906010803 77
    0x819022091640b0140e40042e9a283d10340d45000c010010807000b1032094a81d0503003840e01d2020030080300e81690124940d41c124221092190b0394101d189415250300c9031101007004152002105c0c60302459102c540315603e00308011a9858101c0c000e0070740710110060510540d480c1c0c0f002281c50709100e0034025048000540001c0042c45e01c10b06031139101000340b045a80302a6603c000c44000074005441c1444164001400d01c5542803581420740e01441030001000c0840740740d56080c429264940f50700c1c041202000d1517210304212441d280d00c2d803503040303002842903600b041501d000611040d0f803403601040d100366000403139490220003090040e40040c01c260a0080c00d400740128444400321544c10140c3d104840e620302031b14080580115503900600c844144850703051280300b0040a040da000e0078900f444a0410080f000510108840006105010391004030017401d00d884145c0c2c03c40720200c04108000300b420740d4480e01405050030f10841103010b0752500b07510a900ca0b0310131701401400c3e410402c507 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 463206996 1250 463205746 463205753
    0x807051b0f150c0d080a0605010201020301180203100e1801050f01080a03140706230c091c0c0503030a11100612020d210c030815092a0a0201090201020f01020f07 71
    0x80b6000c500340d2640072500e003c0d00101414140410520b10f040405c40382c0c420320217030145a205000c003400083c0021441e55042c090792013480703080c00900e050301c0c1d40c001001500419100490200401c150300500d101360400d0645c8607988100390140008070340c6400300041031090200e4101e412502118041c0240c00403546048aa560030030400c1c0203c00d8082000100050452141c402c88410110140a9241c1c0094881d43c0240380900000200c1c90305118114040e50b1b28900143c0002e1070703421340c40c07108403285881c110b00850380d40101d501d40804100c10301015000303210407514404600c1540c40803000e03050a0401c03140d06002d008070007643c14240e5001410035461b0800442d005690701541580050f80d50350000e0760031700220002a116000768001c01d504044190341003408174803c03c00c048000404500c0c1d00000901d14204401070610a1844035500600142115051954035954494040b00030f8043d24000404074018421080403404d401c4041c429200f45ca0806140140343c007a00d901d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 463208246 1250 463206996 463207009
    0x30030905040c090510050702120105150904050a02040c0203032a0304080c07030c1517090c0f060909040606030c0e010b0a0f033b01020408030f03070216030807051b0f 73
    0xd590418828078242c00300b1117545030101c821040290303544007560741c0c185206002c0d4a038008811200f00f070303040105210030714404001c5076218020070b0381c00f03241607039442c10900d00d408800000690407500d0542c1c1d1201080d400701c011485808905010300c001c2911050401c8164000710303110000304410b02c0460700043c0400018030040d010401242ca4241c1c5076280d45160008a500040d000c02040807004001504207612554015045404503c24905400038507107503103002d41d94074415812105061069034811050f9401900c02800743c1c489850249070100042a00f800195101d003031301400001c034921140443c3d41a1084002040e081ca1060704003990746c0100001d07420103243c2c90700d030316143c1d684203c1130801038013043d050f21800e8030080e0454007681460100349645039900412090080c09000400c40d0310031030441c4589513883e9107240302207052100000d4150740e80034480c800041846100c5001d4030300b96000e081642c000c44604941e94040d4031095080c1900300321808400030440c608031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 463209496 1250 463208246 463208261
    0x150f0903110708150c0d0905061612022104021909050f06060a05040603050603031c050708010821090a0902030f04050c01050403030801120f06020a030903122309030705073003090504 80
    0x100000c940b035902d42d80d4003410180c0481d00c00d0300200f81b24140c4110301b90b1001d03056039002603902f421071410707100e1442001030b10a1212048001030b18040401c0c215103825000c244801c0209120f030700d140c1c1d182c24140014080944500c02009040c0700815000d1a2020880d00015100c6d00c84030700d440c4c64901e05601078080200426454041172120702c0805100b2501254410000400020f4900c0d00b044003510203541a008019240d100042440c52140111520b0b84c051280980075038441c10640009209046103070446005503001000307106c3d800124850440c040d034828426992410207000045403103008600c07000e40041c0700e2034010800d03c40c440d84000c41990288000080b800400c0c1c1381c07001607a00c118400c07400203640768048800d05620002410381c8110500c828494500030800b107807e20310075000355002e01400c030000302d140d90b0010021100090b50007401c1d030b00095a1801c803103101c8032200425a50400602042510041c3c440381030b030a0459041d260f01c0c1701c4e1801e0806100060081 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 463210746 1250 463209496 463209517
    0x10813060b1503071b03140919031103190206030604052220030a0b15030708071203030b0909060a1d06010f06090b0c0a150f0903110708150c 62
    0x5a0742181d4603030701d650603110321510074240b0540d40c900300040c00410001c0403580c819003103c4030780c8803040065848603000901d0082d41e9105600c5603a038900045110145030000b07101400721107800010440365400719030104008409854961480c4c03401c1a41200b0400c0c0001c1d808841040014107614080d84902d400c5920100001282080c4500c251082240e0308010340344c2c900f2401080700c031400364075514900001c0070307409071450b6091580c03600000203001c1d01c0222001d1180500034800d440410000f40107285200496420725038030401d41e00700c0a10183d081d40000e040c02140c0d25203040542c50325019621143c018107655071841c00c03d03801424070001c3d04c00041c0346a0305c040e01d0364400f089041d010780380484086000c3c030300e000710140c070311000341c1d016411010060140030803c000102e00c002009400c6001d031040d0ba48001c01b6000240410004140c001c0d103004960b00a06601680040800741c00f202111391481c0c071007030450b6403000300d07069403400c608003140022a000d81c2000035003070142c407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 463211996 1250 463210746 463210751
    0x61905060d020403021806030d2105071b110102011d0d0c0813090209031608210f0406020a0510110405060f0d0204030803150a030305031807090e1006090b01081306 72
    0xc42e17038001421070140601a0001e80101c8050000f039103001e018450f41c03070055003000c1b140c440103c5281a4900711160960b10700b180c1d40e40000b0349044c0118401c0c2e100c4e1861104031421400c803450212181c0203816080d038015860300c600c113025509003003180300b00310390000010000d0340300e0070000b15920f0780002800c0b034aa02003488562502041c200a40015001c0a0300141e15410701805040c0b03004c046450461141c1c5015104111040011076002408072583c4002050084507412000707051188592102548100207000184aa07000c165100c550b44920162104260749550f035406441406110411400080000f041907240020041030380303220025840741401d070b114000350101d80090b4030664101c5400420403c240c0c58900d009402290300315100d006007070030b680b40103040b80001000303049a401139640750760a031241002100b00038140803400313002001e94141925141d9000d452032210701814541e011548040e240524010064181e4030080540d5900c8584a25015200c1c0242c64543c0d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 463213246 1250 463211996 463211999
    0x9030b09100f0e190803010e041a041109070311190e030303010303080106090e070203030703091104090309091d1b01050c0607030614011704060203071b06060e061905060d0204 77
    0x1002e010700c00b204022001c0010f040c194420005003400390703083d035003503100c0341e445880e10009255000740c0f411745079618020381450b40c541c907084c0000d500704280707065030345038036802c01c800c228030140140c02009040c2c400d044140c5a5460940a440c4c5401c01c18810a80902804605400000b41d01c6a008405c3c50400310319080400802e05542c000c1c0c001b1380c001007002c07005021050300403000300e004000080c3c05903003519002100075103a0101512501c00c060701d0300d2940e0140100740c2c51428400000400812180003103150203441d540702817040d110704a06103281144003410121914032071520b403e0103040303292140602c1403902c001e50003405040c40403d0050104842d010404a841407070b00c0d4030001484d40c02d01c0360310041c07158400328007810005644d9112100d5170040c4191074029034805005602c0751283c1105503030002c203601d200380c0d0802506000a041c00229003000c400c8400310001e900c1191030300b40a106c8c849018406654058010b2002089a4203240c1f0040c004424500340c01030806 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 463214496 1250 463213246 463213273
    0x20108060a0b0f0d060b07080708030411060a030b010f0201020c07050904080c030f0915190c1104022709010608160e0603010b090406051c1707080f070b090a0309030b09 74
    0x64000c00f004040852011442c9040d8100c03e20030000039100585190b81001866a1441114414950010101c2d180480441e013000103106090a200300c3c02030000703484000464004005003141d9810358000340301146010f01d11801032003200e4944c01d08002400f0024201010f000325030380050300c1103e65074801c2086268080f420703c084c04003030705801202959201d00d0010009420903880c154140e030841000820351600305031107440e801c582603051100758003007a4100041440340105807a03410034000a41845000300280c03011450851070041c002542c1c2050040c405c1780c820900a1002144081c1c01260720030503128241e100d01011807800b07105030000c94010440e40d800a0344070b5240354101007048001071900740a841d0240005940740b0464214541c50740000044442c5c024010071003800e203232904281d002007162200d40c2c00900c0555602105080c08280750b0001e90155001188d000200d80740240100e003400869406554100040381582c076003607d001c8010b400201d9900c640152903070f01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 463215746 1250 463214496 463214519
    0x20f0303210916260f0d090e0a050702120f07052b0f05030105040f0902040606050c070602030c0a06020c0f0f061602010b0a092003040602040f051c020108060a 70
    0x124032081c10110480d080400c245442d0040c0c000d2000424100c1c0343c000d00c030030054640d400c6507280c08920002481003c48030f1103800c0450401c801d0b0304034000d0810ba141040d42005c404412245044540a15a903403410b03010103c443c10f441e0540140c01c00307100400000441c801400c5040b0306d40100c40c2ca0b00c91190f1741d1074581407000e40200448260f46a40401c4803103840c000310705070a124101001428221500203085100500440380308a45d18a102c1c80700001da0b0b8402d50003943d014000700001384c0c981502400581028000c4a060b1052110108140d440403050720b808506460090582d69940d64491003e50403d000c2c100282c8500441c014003e20100004e50b00440d9800140860303041a040301e10b1401803000c6030364156030602e85804940d840780d409400848501c2500003459070191164602c031803441940c92251201c000c0244000c0c0700003540141b02321a410401c4035500c50303075a4203101c0c45803000042c00c02146440b000d407401550040030210b03441040200800701c41519030344089030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 463216996 1250 463215746 463215787
    0x18060f0b07151b030b0102010b0117091e010e0f2a1c0f030e0a21050c060705011a01030b091311100e0f030304081e1e03070308070806030a020f0303 65
    0x804404020f44082860381510a0107524030342803000b484481c0c40407001801e04866807060104964520002410554062124900319a038802c40d0844840824030b01c64042d18040100c0d1408d8003500c001c84905610000b10340001c04101007485c400c01a400a003d5481090284c3d665082150500f01205e04843e01890780075652003200444518182810014035145190320078074011800da81081c000c1c2c010403c0d100403550000f24251504007890315002d41845030138000740d07410100c085220f00410006401a000000303000b0f00202140c144000110261140301e602a90001c051002081c800b48203221205c100714007848018450040490200f00a0030666020b040081c12041d0750300168548903c00342c0d03d07000114001c50400c1e062522140c0c44240580308800350200c008080c2c4030144040c401d00c20402d0100c07140d1741c004010000c501762254024202200018001400950b95501507441c1500842d0094004c181400c0d4503400c0c0840840d0500745a541440b05229420016240031400700 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 463218246 1250 463216996 463217021
    0x4051b0402040324060f06020c0f0612070503090f0312180f03030a0902180c090d0c080a0f030e010f0f05071e0c150c03050d0b0f0a030c18060f0b0715 66
    0x40100000c1002402c4074119040408003c6e920b8400304a296070003d0030620101084803110700d0410805e0004045100c2c041d91100d1901904040205581d0444051481500341da003d0340d03da462910149500c80c41a1440c41d4002d05072000410321681c3c440c1d0740c0918040032441140c3c01da850194500e40356410440c3c0c00c100850f00c540c002e00450801188408200c2074034980c0c4141401d01d02c44000c080d008021803207006600c110026014400040300000082c14540c0640701c0342c14940c140212591a128003c0c1c0c0132410204d441c041c10b511030b00e000006281c81e9650341c0c1c0060300040b070440b031a41c0070440a40e2070100143c01c1c120310000f48012401020720400c100014185003038031500c4440301741d07181071050056000680380408d0b0002e08603401d0b43c20740680002c1c0d00c030000001a04000d42c000841c2c1e00b0a1800501008010000c00044156016540345081d1020310580c0d11083d81d40ca40140241003610900030015440803030044e000c820710801e40300080181e021098003c4131250307011381 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 463219496 1250 463218246 463218293
    0x20d0e0102090a050a03020a030201051e16030e100f03052703040305070602120301030b040c0e090106030201030b0303040b07060e01060312020c041a0d02010806060f1b0706030504051b04020403 85
    0x700c9a2070f004503103000615055031003e0072180381d80c001419064180c48041e05011001079500003020b0110b8400d05c049201109136503c4803000c1d1f800c00c0b90320b5070003142200800d00f1030041d101700d490100c041c1400044656a4040c00402c40c10040f40a4900039101850411641007a6840c0e500c4e110000c020041d9080010340e03e5a1450420610f400265401002550030140844c040001e90318103e0307065070707000038440c4c0080e02c842c0751a83c041100341e030100c8a120f840700c05002046406400690442c3c0c004da0741400121204810582c4a108130700ca500d100840400061000071640e03048030000c58280000000c004d641c030788411407200151403402c801030b0400e0400221a1406100d54103811000008403000140642e020410014a03110b0190502261074000341c0d1640d6507908840c00303044a0034100d03443c0c0382c1010b0070600550340e409022426000b403010108400f803182c400c481c41180c000c001403c1c80c2e0042c410110100b0900100290050703000c1002001150010322490b04078000440c03030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 463220746 1250 463219496 463219507
    0x605032b03060b07030e060904052e1d04051c081909150f091709090604050c03011e0302031606030c0c11011206050405131a071704020301020d0e0102 66
    0x3030020844201180c0028186032003000c1c840c91400c4016103010b01c1d814289000c1100c410380000c1c889002c4c40b03016550180c00d250030800110801070003480e4012100c1c1ca0340d1040c21071a412001940b0040c01801d4280e40c00082c448450010b04e0350031900540181c003903400401445001d0405010a95042c1c00402c420310184651042010008411020f0002c000c02001d0b0b130907910a803000600340c03010246640c4030000e1040e00034441d4883c00415900840108100d40c0000e4201001d41080701e05a100d446400009103890505004461050044640243c55a800e050040144c4406000c1c010121a802c000c00b000685003088107001c2d00c06c0020662542c28a401c80041c191215442c081003080340964408001511140c003140e0ba80c0b40c2400c03d100d480c9450600000100903681c006640315041900303000382c60308444ca00020b00d6004641103040c8815403e081440100c0998040001480c82c1031101400d401d5200c0b41c0f908241f000300094907001d2141600030036510610040c82460354005034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 463221996 1250 463220746 463220803
    0x40906060311130908030406091b06121811060a09091e060b0a090b090d02150a08010605040308030609060d02030604060515010201060b090607061512060609090807110103060503 78
    0x104490050380703440782480400610382d24071705c543c000540010601616001800304000804075400b01030108540200500c5d41e5400c4024410203424487c0e002c0d0320301c2c0a8550f4000c0c403610307082c16140c1d40c10400482c402c102da0002d01015900a480660400200e110040791142450040041001d4000407030017603000c510300c46804450717050f030080440c1d40f020071070381003080d400c26141d908961019500e15103d81c1748030049541880100f10095100121031490305ca850202e03009805200c0e0710b07640d000702e141c0e02c41d241134895100300e01000c1c0c0214070500000d0700500e4041416580030a025025000c24040ca0340801c1c50214103403022610702e034640003005001c295003000501000c000b4070090210300d24082e4400c1440c40f400381000c0c021040000c0c01c401340840c640215580c0b00010010003125503841c601c0c4c04107110030700d00403a001d508000c07000409101c980245900726410078090f5191042c1030362040300d003281c490003c0307050644890f0300060344d80d4141b054524041d0001c408a000125038035 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 463223246 1250 463221996 463222009
    0x15020c100c02090103061e02070f060c03060803070311060708060a0e060102010b0901090506040e0d1b050c060a08010612060b0f091f0909050f090a08030c0403150c0e2d040906060311 80
    0xe003401d688500c1804104081000b51412802b00c5420600003e50954400000c8010300840d8100071900e110000c2c41c04109944a1301101100030000c0c1519019124030004507100c041c10360b801d55021014030400d0000d0815083e8940d0407140500002610b04c2c2000c000c01c00514003684060341131607482041080701d003001d028405600003690050104500302d040082e0000303035620b00520300310009207003507000c003c010051140f413600018007403511801e030248020100301c0240a01b1000912800318100c900d072041c011181500d0450091504080d06c80804900c55042054950f9010362007036030000a17205160502a801d07000d0b41d803189036044c02d243d83e0741c0980ea00607281c079551034603240810800a40104541c0883c6500c44d841c02c1c0d4a0310b0326480c404050281d0b40000d48810050b07240340040c04801c0e441003807102c0f465240d84a040c103d000401010f82c0640d611090044035031200e0a06d9400d0500041c218040024400604100d2903296142200d409410450b405104100648030718030345003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 463224496 1250 463223246 463223291
    0x9190c0905130c1e03020904020c010504021002030a050334020709060e0603070302010f0203120f040c27020d0204210b180a1502040806090c0a15020c100c0209010306 73
    0x2502c140401400c551000300a52080d0109008040403521600a694032a40494000980040096403605140240c082c020402624220721903103000d1070069240b0700120030b880303201c491515080c0c20740d0344440301420300c85041044a0080c075a01380d8200c0440c5581c0f0864101e490321343e07005005090510f2142e4084964a800121000b180c00040203940c3e0f50000d00003040c0c1e542848d01c00407200c0340010507446d5010310740c8804042146842001400c421411050744268042c290580c0090b0f5500b145114051114080b041d003107010300380108640440b03400a110207244044c005252694407070308082901c40d408006a40ba6000006000a00c001d07149501d4020344070f0316403c00360710403040f4201d81c0c40710011001000000c40030001b0aa016466064900a21041c0196881c80c5840b4070103548410603003a60350f116009000d40460081800d03041c1d27241c07500e896001001e0901e481410000c40b41484c24406d0b04110064003101d0040c1c41e0103a200c1c2c000c502ca0741000c18050041031074205500d0b120f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 463225746 1250 463224496 463224529
    0xa030f0f020c031e040f0902071e020906010f0e060a02160b120a0902132f09100813050d0503070e031204030b0402190b09030c09010503070509190c0905 67
    0x140302000d404030b004004c4407050300e8011160368540c40000081505070003542c0c011007941c848440001030002c407640081144030311800c484803680003102c1d030b8162601c0c26408040d4000006030001605075000c0d0100781450403160400e079a001040b5400600d075907000288140051700002640e5403880d9080704442e01920307000d918607003081a0b070001d03410b48030001170800b50000e0722000d002c000d54403070300300305034084a003807206120601c80c071890750400c83c81084036406500903016149140c0c1c00c1c007500782c4458110080403405d51900c2d020040b1000c01c00234001d501c0c40b0305442c00312000944200705410580207252521900ca01d44040050115129240094020b4005003001c040034131840342110160390303005041e052140c849002103a500c1208040c41c1d07290080501d404240100c4e605d018203c5540c2c206c04580c8000000024811808020300c559500342c3d00401090000380340a48a041d0b00681140a40c2b20900c207542101d0199440b025070304000c40c540074400c0c071003424000306a003c160003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 463226996 1250 463225746 463225751
    0x306030b060d0819030609060b0304021009140105070510150302030d0f08060d050f0109050c1504050d06020307020f1b01120203071202160c03081207230315060a030f0f 74
    0x249803982001131140620880b4a41ca42e62150031146010364011000381c011103008101c06616555030f803c03a07034804da8059200c0d05403403241080140c8120362540c29141200c0401b61050101c0006441c182c2001e00c0c1201e06000d90b4210072240c10162050034040240d0014050006145006050804021109800400070020007201d90590811003042d000101520b01c41403952003810404c0c1040d030075a610115550078445008180040040d0303052800d40d046829940c030091944486041c5c2c4214030a0302e400003a0300c0c458501085195002d107031301c00c1c40d03801540c0c041c43e65550401d0900020031400620550002001032295034405e04451541d144984218070f9030402c4c04019000c11000072500c181c0b203070002021035140d01c0024600e0780e1182d0148500b40c0d0251a840c01020582206104000da501c41c40c0c0002d101e40d22600c0305d0340d80c4201080c49521100014200c504084d400102041c40300c4200180041c000e4071074400070030b415100c0e0b5400103401074200840e00c09071188000800035050 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 463228246 1250 463226996 463227019
    0x131d06090d08100806160801060c0519140712031d21030f0f0c10050c0304201201020d0f05062107240809070b030f061f0306030b06 58
    0xa4005000705054005040000d05903480300e2081c1111101d5030030861860090809124107001400106442c210080c0c855074816a251102102c2071a003185000d4800d600082d1405813000d800884083d04c1400703181446418510a6202481c190b01980302c4410281c85510400a00d640b00c00d011b07403aa4105001c00d00d00400320301c0000e00d0086d040c4100484140303c15003132018500304000315000f403080e517030b00c030f40d180d41034904407500540141c203d00081d03001d1130389001035000292007200e10541c0c5201c540f83c02c54466071100380e00d0001c1d2981e84e5a900c4006011b120315030b5290461402000303000c40000da91404840c0c40c1078151182c0101e00003401b0f003020300748807582d030381d015402c002c0d00c6580c0345a82569036860130300d80c13800c140c640c4508440741c030028000da5502c2c07038600000810182600c42e40d0700d503101c0d890110768a468501c2003c0007101c092022440e45110300c01c44941200c07004095500310a650312410300b07408030113540d81c0003203030380e034142042002103000b2a80c0d40090112581c00701d01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 463229496 1250 463228246 463228261
    0x4110d110621070c05060903040602121c020706050711120f0703020307060603030804050d051903020702030a380103020904080306030a12020d09050316090f0209131d06 74
    0x582400c40036a11440d808500094910700d0200a01d803040c464649100c8070b0704040750701404030781c18a0070640721409201d000070040000081100e0841d00b0f640d0040c40c0035081c80068004640003840541c0c0343d40c4031048141419282d81c0007500c1c8144c040d0b400040e607070400c80c0d030140c54080d01d202140c80c2904101d05848006201c0021b64480800698820381d4030400d038039049080d0710500300010304561034590f008c424154041181c3e4810340c810012205c400341049410b8802d4081c60903d0320350900000302d5405a540b20340c020300b403418030107421151025400e6541c104076050b43d2800000c8582d610a100c041c1d04800502801090310210300a02154159008a05d00c2407000304050210400000171461a4070104150b41d00300b42c20054101e0400e4010710004d44400041c00c9440007e0900345001c2501c0c80c01040c8914282482000604c0d400d143c12040070141c440d02401640e100d6003030001c83d003241c44100c040c3c207000c55a48000038400e02c1e07500b0061440104021034008a038003200820505 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 463230746 1250 463229496 463229513
    0x30606020c1513030503030f010515031003030c031e180501030b0d08070519080d0b0f0f040504140703080904050a05010308160f020d0f02041b050a030e0c0307060804110d 75
    0x145284940305580300303010039243c0c0c40a02e0650004000d48000010403039461030380c81146050341d400300c42d19100c0c2d00f6003e050a140780000e8400c4038400860b40801c01c0002d0240380c0c00e03204103120741040341e0002403082400b090030000c550400089100b4220b420f22a014180700d203409402d0074241004902c0c04540810b40400c03070310070020406100054498240103040080360003070340e10f0b409880d074801141d2420403841c3e0082f516500c4003900b004403000d50740c5410303260f174843d40002400340101c885c40002004040c01c2d0291080e61454242800411280f0050080501950090b440d84d070b03035000e00030140f000721017000b0482034810341b4060051000582c403104490704c0b60904207006001c0a403c0c14600381c6400248002035002c100f56040408201d000e42034500d89074000c0350100003900218400c00c408000910441d000514100f01c1000023500961005c0170b1214800d00b21062400307d040030910300380c1e040d0003180104480e403080004020240c1000050b40d4410303141d46845545656a0200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 463231996 1250 463230746 463230769
    0x30c140f03090f040f05270105010e0627090312010819080706020904150306050702010b011e03060e13150204061d0103020d050a060f080c0d14030403050109030201020a030606020c 79
    0x3c40c00180220702510307a50351300032281c0c08500c85403c028900b06180307915000d000591074222001821181d102012206106d023030b0481d80384222051540c3c0e103507030402281c11078810707010a08245083e45000340c2d03a611214240301d1034041004685c0ca0512199000314071005074403d528036030000703120403611064020825081680b020071207485001c14a4884064003542003865041444c040b4020b61020040c3d0703031402164015042040192690300c0c0880c2600d1000589902085503c1144401e84192850355180070f4024138000583d1600e480071103040b0b0b442a80d5111040030030714112030078800707691040d18030b04c046550114a003614111015042800c0003005100344007412085220a9000750119040070001c00020060762038040084001007055003c1c0c00c803580300e007000115482400085080c9042c400400101d500b5034142d45040300c0b9041910841706030f00085c0710000000d4001d01a41070f01a110750005611a04400b00060484056a010f8404c40d0301c03424070f1800e00d4071020907108 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 463233246 1250 463231996 463231999
    0x11030c0d080702101503150b09060f0a0302040e030a02061f0302190b0c0a290a090c05120109050111030c1206010311040e0604051f0605180a03030c140f0309 69
    0x1c00a82d12580141d0901d80754100c40184c550420110007500c81d0010030100589118138121051581a0b01c807013406c440c00b034140340b50459920f03c00b06400d45040501d035030440e50010445541a81c82c4da021a064a00c008103c14042d030001c1520314a4a405010603039004141c1580d98811542030070404405e11424480a405642514010360078140801c4011028041080c502940c0e16440aa210f607125000b20090700c91010b82d8400b59075241a85040c1c45030491500729003540ba07241c141081005003d00c2070100c03024016850f00140035110301c03440303500007009500001240304460420341c4c00c0d07403210308100d10f00120410400c042001c050054900175144204401c117280d440c00016801040700141c0100092404940024070303c1c034101030300d44280c0080d28140044e0312450460701003201c0c6981d5420888030101e02c14001765106001600d080c1416080960701c0883c10340200e80e000c00c0030741060303000904030700c0110140114001d0090310903034200d006240c4e244160141d1074903406400c035002e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 463234496 1250 463233246 463233257
    0x60302030a0207170c01050a02041a2503090e1e0403030b01210608010f0501051f0509090c0a0324060309020111010c02030a020f0a0f02010f03092111030c0d 69
    0x11024071482c0d06035000a507000c49801c1c107403480b001071800503801c8034490311065802c22000894505044c0240d9040b6180b240e020000e42030340000450003a00300c0740142c485808210034408512000426039884035019460380c0c8285810300d030f2403850602e4000e20b01e0a203103090707c002030340420701c1c0c25001d684241c00d440c000841c000c5c01001201e43d440710703030f00c0d089288034030321307900303119180c460b40080c044410160003040360071041900310003907480910070961b02c082100c115410501d101d007004030b0a100c0d00d01d44075103481c0c4074030700244200c9002d650088140c0d03c0440e0750200303140c161291083c1d01c624091040c0c0701c0b4085810300c1e248840e80d4000c040800d0b032030b6072980d030031039004610701c101c10714412000303028510301180000c0d9a42c114030a00c100602c02c000d10303117a08080c045034a80c40d07260000c00c1e91403801c03050f07001581e00c0007508242d9800c15540d0100d0700c1c08903410500480d07110b00d000c0800000c1007d4404c00030185040000c0003013040d041005500030440d07001403035030244012428007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 463235746 1250 463234496 463234501
    0x100e0606060c0c090a0b01030b0301270312061806050301020319020c0a0807150b090f0f070e041509050c040b090f0607021f1205070f030e010b12070f1e06030203 71
    0x29042c0b03c1094035581e040040b010600020b2411a080b02d03419907070a990402541000f207080509071808814909483c12070b2148405c0101405028100c2d03190003401c11504010b0500c00b01d000315840d580c4040460652403605440c40403090041e80003c1100310025420b5042000c850310b0400c40001200c2e8045500060b118034090052008400d0b81c0d4120281580352451814541f1050f0684c20035843d004d80b83c6800c0e004280307014142c040c025035221001611326034565241c1c0e80c41c400d0160501c81404041d000d451110340d10b901aa48100c030080443d00b8607189840e54250540d0030282040380c14810521007406043d140d10150b07182150216100b401c240341072004076983d0310030300307001175002030b227108000c40c1c05240405040188107055480071025588184590100c68040c2d4004002605c0c0d04408008548039030868521240c0800c0000342c00780e8040d00240321440310103039850140e005410304000d1260652a004020301080485541e9680c44402d107000400c00f50040701c2c05d2540c00300c013 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 463236996 1250 463235746 463235767
    0x90b0a050d0b12100e010606090b0a0e010207051c17041401140409050916050103155a0317031305030f09030c0109050906060904140705090102100e060606 68
    0x114041030802c0001900e04c00011510b00501402c408440c01d54250f00300400000c03038074800c034040d0084030642041d9904100b81d20008950041e80710b4603403030451007820300c0842d455680d0708001003540d58146044594859900e0402206248458400c0d17404500b03010400021601c01c1c2280b825001c2443c02e5908400c400b42c1e4075003030f1301942c0c0100850703c2c5490b08000400000064060b0400c400072020008541e0354001141a00e4043c41c14441c110000c04042000c95103480e829903889200007841284002c103401c118004440000241e8400d0002d00d09140c1c0000640d040041000f0285d100f0401c0c40782035072220298103204449104990f140007000034541484581071060785a44041035991345c00501301141595085203000500c0b038010031541c0035440d03000b450341008680e40902211096500e042c204161a0800c04501d60402e8954000382c043c076a000c4109071040d2001d07102c050f00e4043c581c000900d0f001100d0122250546000040f01604400150550b485402207403000d030f80d9030301b224 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 463238246 1250 463236996 463237009
    0x109090c09020a180b0412060b1f090f05011418151201061b020a03080d0b03060a06031e05100f0b040c020c1504030c140f0904050706090b0a050d0b 65
    0x3803041103600c2c4042404200315510010f1050020850b41c4c01c45483d82d1100141c00541c0b09078407844846400e41d009080000342a03410046c3d0030750004006207112008282a0b0201c00103c2180e10f0001e0980b0805100801511040002400b403c0c17801c01c0840c0c0ca81c0415280920901340c0c044400c62540301071b01c3d4980c0ea40c0c84082c4202088449260f12004680e1108104803c2801600c0100f0b0410000e82e60300003581031408545500200300781105455030b154455a54400741c00711016640300c2010640030b031810481c0078080c15105100241080c69414074840b241000e0100303030021291440502c0100e03000140008030340e4480d490025610360048110710080007030903041a08181030078601048141c0204150044800a0759007501d0103036403510702d44d514402da000007004846400d4040c401d03281051030840280b0405000311103148203100000e01001c0040368100d41035072003c0c400740f081581c85202000202032085000d41482c1645102404034050f080c0701d101030303035590240041c03e6500c85 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 463239496 1250 463238246 463238249
    0x90c06140f0c1c050c010621140c0a080c04051b07060b130c030e0d0e0a0b07081201030b07181a03040c0b0f0a031b0c151512030f030b01080109090c 65
    0x8800300050040300c0003004d05070740c20000c030000040d441c1400c00600901c03090000e00c0009001a550004844a607580700501d2035030307003103808040c0b0504090b0079803a15103030580006000904000d019000f407080401054440040207c10095060b1211000c0a9206400d5a0f40e640d402039000c1132081c03e02000c41e20a505a080341d82c4040d05002c40d51154030f030581d10200701d200241c02640d041c90b404001c26103c6c506170141c04c42d003102100200700508013003040a400c0300c6114219003890800d002850f81c05510007a0429104d020880c02845034103130304000b9584403076400901340e40600e40380071070500c103401103099209400f4000100142c200708103038140502a1040e00b503200d17121400b603410303061150041682e20020919000701c0c00e5128140040c0a0070070140395071100b26508081d90703550702d003803009030304141d001e9111034a5100c00b52208904c00e001d40001000d608080d04542001816000090405024549001074140981c0d030722862040c10340c2d024250100b20300f0010300c0c08800d1409203 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 463240746 1250 463239496 463239523
    0x711030d0c080a021507050a1e05180402040504091202070e0408090108040203030919170f06010b160804030f0308010909020d12050d05010b03010e0121031d060d090c06140f0c 77
    0x405003001b28031504407014041181c2c269444014108078a001d4001406410f4580004250705001c64034440000d400480b103201405070006d4200303903807480400d0645000340d200b02c9611103000c46141041d9410048400140640b000c1940075052a89507a48a407203143c5900e4100700c4501c0025084d501c0070800ca4402400144c000786002c40044000c0c2030302d41d898007407001046828043d801c2004000206a030303104144d40081d000c0c9900e08213140d02c1c1c5034041e5034803011800d05e4054003404504c018001e0001103004110795180c94181c1d180041c2551030513001022483d24201c0d6250141c0c440c1401e40c5401c503440207142c1c00150715401e05803000d01410b40209038547c20100041060940307040030b14120b421a40c00c2c1c480d04c0e601c802082581c10610001046078000030b090700070100f031143c001040109000440407807801c100340085101a88860207110038252511000c100b04040c81d2059801094189013030300b02c100640b601c00001b0320880d40801091a8049914280050140085560820b5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 463241996 1250 463240746 463240783
    0xe07060f030b180f070e040b1f0e030d08010806130b041704080d0e03060703050601020604080304080403120807020d081501030908040f180b010c0210050a0210050109020711030d0c080a02 82
    0x280141480d44644d0304690032030000351785030086085403d0500a07440305d1603005103410842130f601c58803c4120800c002c0c01c2020015514042c0909850612805080b045c01c2d6035815021360400000b02d2401101924107004003040a1894020502c421001d40d00240c1c440058846081001284445d60055400a0119000301540c075404640c114074a9450300d001601611444d0751218829030450700e04407043c41c0960000f900160001d042d090085902c05d20910b49181010740b04d4561040042501142c8008641020f060002c403075010015004003840b00e00d0855290b00e410344410b041c80c1c408035840d6051680b0341807601c0400440e907040d60081e000c5142e070561a00d944500e141c1909142c1c6140f00c038618031b041c00c4030036903500c00d03140a00710745c2c0c000e02880342c803050302907045806a101001800c1107008112449001c0ca465009146c002c265200001d40c56414600380b02d003000d51804103480c03113170b0302c03c01e401400c3d69040071503800e00315080044030303840b0500d0010a034145000c40071079080901 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 463243246 1250 463241996 463242001
    0x160305100807092007080307080403030906020a0f080f07090501180b030901051e01080312042102070603110301080601051c320a02092214030a030e07060f030b18 71
    0x8540e10040d411902c4c4030f030b07203d04814036080100d035901c141c160181c003e0f0410400208110b0041280d41c2d0014441d10f00040d0801c4030b80c8400c812030304125041800a0040d400815180340d0002080b80c1107420b080f8000c00d1030400f0300014041112034880c10b4148400c0c558505079158420320040010000c2c00c5109640b89899200c0074000d0404640f000400386180d04540c0007000d050396002d06841a8000a601c1c0c542d140090322420503008100701c0716215402d0f2043e0058602041d2404074000c940c000b004e030b050030300901505441c15150701240b2500b00303000402021070002807060443d80c00341e800d0b09100d4840f071001810b1a001620140c50003150580d08000200030820510032a01000340f0980ca12200048964840108004c0654049402800304140d100f44040004400101103500c0120010640e500e082010064501d44555040800d800300042d40500400d9004040500a08203050508201078070f2522401904020181d0320b82d49440715881d071040708180901c1003c0b08036640e1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 463244496 1250 463243246 463243259
    0x201030b1306030c2c0411043806090d0f03020307050f0a0203010b1e0f2403062407080c15011202040c02161701020409090302160509160305100807 65
    0x640c0f40b088075110311072950420a403501c1410000c040503107410305d6101030303159500d8420100e0748440205500c15030b2100420234480f400d031141c41c044a000c1d2000c40701e003000c0145070601007220201c440d0040c08100080c01095503403080d18603c07580c0c401d00750307584c113002030800300d2450240400060040c403580311034528a800005810803051301c05c030300a0183c08008028099001c030301076201030072548003400514091420f0440100a5030000d04105030004150600d03d14880f1046c10620000728000244201030510107100d80d00c0c00c508020396001400351400d0081c4901c034804024100f508085a4560010810305c81c24803080b0310350700c1d401c5843d43c50318003580d4021000316080b44200d00c0e085100c2c00160000c50071112480c081042c0c0514540360503601303401500c295a407040195400c10020070460924030511140501a03030090192240e110207038528a4400c1e00514840c01250382007250b50b9000d1442d019500c24035140c00708040e280ca903030018040d000da130401d02c0705018030500030035070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 463245746 1250 463244496 463244513
    0x30c01050108150109060b09131104060315090b01020a0f06020405150307030e06010807090e03040b131a0f0f0a02010b0307080f07060e0612061305010b03040c0902090d0201030b130603 81
    0x80d1400c03e00e492540d03600c04403074049481d6481040c2c9034201c01d0051002c0303864134a07a00f55201d1142c0c07002040700b110a1f11403003c1680243c0200021031f580e1414201840d05d841e5407400a8402c100003040120403000020355501c01d440350041c80108500000801c220254064078024040602b5084507842503004258458004a607200c0020349815580342d40c1520002d045070494410401400c6120304041c1c4140c00f81800204c110b4543c1300c03c0000280801821000380001c0f24450803c25416007011010501098400541d483c6c3c80c03014000110607014400c00c9507400c006501030700303980b613498101c02d0340074007199a02143c1c54000c0b42000914444041399500c0d8030140d4000b80d40f1401d855050944070003075101c0e400c5410070018031020741c225080001031600014014880323030854504840101c2034402c00d0300550a183d101000f8407040215150403c00606410402076080c11010b00c0810011001c4e0302c400b80c101521007112900e1a00c0c0c0394106884804d4040d0140281601c82c02c05582 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 463246996 1250 463245746 463245763
    0x120706020319081e0903070512092d0906040e0a03170a112d0a0c0b060d03320a0806031c0f050a12020a0e03010b1c14030c01050108 58
    0x290002c4040020708258880c005251169000103081c001228007003582034901e060040074001c030f80c40104110030100b00100158002984c071884100d40e50400c1805215050001d841858180e4403000c1080020366041100c26158020a40b64000f665507400e00180141480100200d81070040b00326100a150340501d1010018124100540058035420189422150354010401000c0000c0c0141c842c10030070401c4d100c495000280d80c00b0701d40010611040c5040e8400030540f4003240040100350108008880d006030301040848000100300020b440c00740101e004500750f060810440110b00000f4111418401100502d00304001d440d001e11481c0500b0006099403680c0c42489103804000c140f807010003464411210b80c0e0703110510303842c081300c003a2100e030401c08030201881041c240c00d01c40003140e440a0a4408030b6940c407898004006401e02d0308481000c1410341c00b0b070860b0800c4402c03042104614002c0168400030040201c404010f1140c03c50040120403a01942010b0001070307100f200098080c1c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 463248246 1250 463246996 463247017
    0x2d060f12020d0506011e0c0602030a021e19020c0d081c02040902070b010906060f05160813060813031b1a2d10030222060e090d09080c0405061207060203 67
    0xc8001100721940e1140321591614500090408047c040002d00150007842d040303440404054204046e900c480509500b0b04018a0001070001ca40c20925007070203181103400c4003580c009060002d4900740800e040c00351404000d03005240000c0c00803d00a80d101010740341c2191400f0441d10361780c9840150010750311000d41075032410004030000c00c240b100c1e44682001c507503041d1140203d296140d0303815a416001280c00b0000341c01c5403210760011800303100003032041251400d80004400d0800c1d201030700030710018101e0844074041480400009070450750b050301a00368415001d0344240d0701d25001e000341c05500314484010076100709101030710780881074000d85810304c3c41c0c9040e4880380301344409001c28401c5802180044011108002505248402c0400d1014114580c0c00c541034080d450020b0300c07190360001c41000001010850104001e000d0852003007602e19012070308900e403900d001d5813501d41c000d41c10700c00c580c0c80b000705d4815035440d0506030368040a07000b07503030505644903c045c0d03c84c2c0040a800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 463249496 1250 463248246 463248257
    0xd050f06011e06030e061f030812071205130303020d021b01060f0503031804150302120a030e0316030b091e0a03390222062d060f12020d050601 63
    0x424440e00178010102035405e503c00a040c55662240480d18a842d11a400c003100c905c0300b400400800e404000602c091450800d8422171410a80c2c0020200e0349850820200607142800340700490b080e40e6000c02e5665010304d40907032202c0180b8102c0000b4440c02c101c00b607405a241018442c1490103400210440f030b40a003060381b0080c0e941040c5512440341041e140444418174250701040d00e840d80c07010082c41c47c1250308801403034880d80855020950854140303000d9104983c1c050816520039440d481d10007054004d05504282c00402c01c01e00f404600008042c00d0841001810702c00341000004801c501d4880c8544002e0460750103240c445004072402c0c0e0026241c01c0041c01628400c0f5040b5a03940c91807810f02c00920001c02c1d10b203c20001100003241d0281c40c1c24a43c1104000c440c50305103a802e59800000740c03580c600b14200c42410f10381e485074580c0f07806c1c030303e81e13001d81d8080030500c101121442d06050a0444040c5822a800710b5500302840126202003507007042703101d41e0780c0194420402a2a0f1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 463250746 1250 463249496 463249499
    0x804060e030436090303091209050105121f18060b07021e010903080c16121e0f020a06120b0a0e0a09080903030a02030a021b030c0d050f06011e 63
    0x9164903440780d030090007101003142242030200f55020920300c21001220390f02c840807200320201c503000d441600c3c400f82c0029440d004441d007409001d803244c49889103d03061408005280800180c00c0d40175580a0703501020120000031008915010312070051190700c000c0b00071449c0c4514020203080710780320300542e0303d6192035000310fa04603520342142c030050b0b0000c1004a012160218160b00c0042c04c0300e4050420040001c00000504440082d0524103443c2024151070315011603180c010150700d0348a110a0250401c01d400450448054400e40e0703106040d1041c0c10b6003681c02c2100400505010003500312495480001d40389900203100969803010300300902c0201d03e03072010855008041c0c01080780324407424020601d44155580706840c3c81d0f12443c070041c10122504002401c0d03401003980200560000245801d401e44e061040c030000b50a4010401035000b03901003c43e80da1003040204034010f023806e850100c01d0040c20811400300400b0002116030720760712a420220b42c8a90700b2200c5040040f00c560 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 463251996 1250 463250746 463250771
    0xb0906011202220b09160f0207050f1002071205031e0703140d111b120310090b011b030309140106030b0a02030601090e0108280213050a061203080406 66
    0x8000c5481e40042a5034684a180d40b070040c0d8901d001c1816012040c2d46550429283d2542082103214410b0050f40e4205010071401c01f400701400c00e000c960442d00039901c04c0c801079071600800d20640005440d02c24403c003000e64141c0c42d080558101000c500210702d0500d007005800401400200b411442c40400100d44419115180c020320304000c020540b800e0f403002c0360403207007030141c5000c846144012480b0f60300d0915001441d44000704032401c440d00c280b000403000e0340821580310100042c2890030301c1c42c6001500035036403c015020302001755844d00044a4168419000c4841e0b05010350402c0790105528174028000b401301c0c5000b140c02480082d00c0d80140340c0188540c40450781c00c0410b50b00b10381c4c0d402440d40e0003940001e0076241406500d0030003007040c0c18010b281501030301c8130310010981c20001800d010792910304400345810815601c0201030040c0c466444011686200000115554440e94030460281406800c03013280041c20f4201c04040c55806440540114080c15041094540b82c1c103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 463253246 1250 463251996 463252019
    0x2030d090620190503030a05160f030c030605130207030f1803030309050703061401140d020f04150905070c061107050613051002031302120d02070618080a0b090601 72
    0x114081c0403801104000151007201d50780104a06040b4040d1000d050200281000c81103c0f40c1094406502c040100040d1031841d229494004440300307080b5404c1c08800b000200340043c109542da0806480d1825814014040d17008807018000003000c0000031008844400300079085024283c1c0040e200c1c3d005001d809010b001d40610b044030380440d43d54101d00b55201038003d0304881800300c60038400c01c1c10000102e021480b03044849200c812100c01d10b9450905919400160166000e101e207180010b07410041c1e031030303944011204405440114000802054a5600c04c002c1e500240c1c04501341340400040d50750207070340c105c3e40078400e03282000f61900e00140700000d8040d141008101ea440500884c1400c81042c2012082511500440345024103640000041c1d820590302c0d0103000304c1c54180901103240c241c909484000211005184407045614000d6807150240300303039024003030820050202009283d403694043c245c010b045038103a224500d090a10404201c07062240e038005c550005c5181e01815 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 463254496 1250 463253246 463253249
    0x20c0c090c0417030d05180607050c06010311240309070611060a0506120123010e10060302030601050c03040e0f01080d0503190f0903020a031e12020901090e0a020702030d09 76
    0x65404900b0301e41000301100100c00c1c440a440e40038801400009914900350085a04ca01d00100d5060012152041e081e440d0250181c41402071140c18803180d02c01c44c60000300c490450750469800c01b00749000b240481d00c0354880c3c41d082c141b4010001c040300c0004500c82c00841c01045907070110f60359a60703500b0007107602301c024452115a0781c0103000800c26100254001d180c0194004113a007041c0ca00d44a041801c5450303955250919500409440c0b00c00e14010003c00d0040c401c40350842c0223407920103072558810381035008040034543d001c004104985d100b5402d40d01940d5101045030390722501d80c40742601200381183d158448498420010410081c0420000820f00d103549035181142c40b1800300700c02c6000e2807000401515038420303440d00c01d940f590050b02c24142c080c0d00a0320a0f80c0340c6040080002c0c840d80080003002d8094418045070b05d52045481441c0c20b030f84d00700140c8850028004a13124001540114503401030380b0107111031525658000e01402d4402c500300c509107100c001c4140c903582d0340c2c1d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 463255746 1250 463254496 463254511
    0x218060d36060207020103152306070506040b190606050c0601050303090d11010e0603071d01051801050304230601060e190b0d09200103060503060903160c1503020c0c09 74
    0x11400c0750300000d1601c0c0c01801d100c0384141408034030700a400d050350450301040e520040008000403d04803e090985000c801043e0050351540e00e000398503261646e5584024100404503140040003409a800424070b40060461545040c060595241c200070841d40100e030107040305004400c000106490700000f100c01b60200a070040710f902e0740743d4407007036500740d82107010318184030f0801810801941d80d100190700c0b800083c1c41c0c0ca0315990b01000320181c04141b44034501d0500004002c1d42a49075540480c100841c2030174a00240d032640c03645412940a08003241003000100d000c403100b09103810101d04541660b000d41d0311810240c21304001c00c28002d0160074030f20603c0154103014004000420002e040900030b5120205d200d01301c2d81e4400644580c40c2103c0d481c040d1107002100703940d40c2d25010b2070004140c210014025410310684a580b2442111000490b540546002d28204401c00c00d4400c005c14980b1591708401021a00c0a0040e60080319000030354000c048003d20b80e80703031110403075028450 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 463256996 1250 463255746 463255841
    0x10b090a0c030e0705180a0b030a08250b010b0a0203090a0e0106120204060e040e011404051006050603060a0501031d0f060a0c0219022110140105010c150218060d 71
    0x102d000d054a02c2d8094620700010b82c03070b0343c00c101d4161410041d07803404cada100b4031050b540c84200800342d26070428006003082c841400f020030b400100344006015815502158000c5603103100040c4140e21f0342c070035030310101d81041052000080c00544111028102c8800340c841841d03589500d892001240b2990060300c02040c1032803c001c0c010305169100c14840144038000003070070391213008001005401180d08440c298800c1150007080b42190140b08018081525081e00b1070070070078009900c2140c80d00505040580d6004075129002188003842044c0000c401610010f0800020b02520303032000b16400b0354032900300400c04401d1480040c2e007001c201c1e001038000c40090226402c1102403107a4000c240008040e030004030300450000d00002c40c1c200c0d030401c400144414403008404c0d030443c0c1680041d06011900c100f50001c00d082205130003003000304620040e9124590010024110788034600030b40c11a802094520b00b10186a120244568240c0300c068001410040710070101403001d89900c10100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 463258246 1250 463256996 463257019
    0x5060403020c060a1b080c0109150b060a170c0702060301090207050d09081b0a09020d1a0306090a0f0213050f0a05010905070207031704090c02070e01080a0305120603010b090a0c030e0705 82
    0x1000f01703946402c0c180b16180302845d2030f14411610b82990341500d0203441500c101014172160620703501c1800703401001a84c01c1400c007000700c14060410a142a41c3d40301030f020748400210f40420050132500180e034000e0103941c40e540c49400100080d046104201c0381c0c0d100b0303460402c9449010312010400c44061800421000300c0715007500c1c18441d640703490b558200680c448041380d109018000f80540403107040d0300090b412504e0025000004081107014000d4200da000c2c45181400850806141ca4014001904090040c80441d212444082040c07407a0742c5400280110241c00000080c028101c0390018003150b41c07126003d4086480075641000980c3c0500c01c01c000190b00c40da080c9071410092135103c1e003416a41c01a184c1a00c240286400042e00400c00901000d8001c3c000e040c0900810401002159503030794000e00340b40708024480700d0004040c0009010386e03030250482a0080b50142024030b1500b05440104060006072036a600468200003810402050015542040b56401403100030b480 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 463259496 1250 463258246 463258277
    0x409330b07080a020109020907020f060c2107090f150305060405090303072607091a03010f0b0c100908030115171317030f01060e06091e0301150305060403020c060a 72
    0xd43c4107150442c255502c900300600582d861100b9580704000d039802038000342c80d91488903800c1604c001c150905440c82441b81036400d100034044801c00002010304401039031034031103003030341d003400240d01040c00a11940d0b000321300002c900719008c40c04010394505011076200c8400700f100341c600c201c646d8207055100344000f8a9091040410300c500032101c5580581da4040d28000c101021011142c000100381d07926420800c011381807054174098074403980303110709650400b40343d417480e05031a02c28140550341c0450721141d0408140300081c4911881c0d03230b0802040c20245018201c40c1c1003441401c0c0841070b4100d4400305a80248801074564010400903034450780c0702030b14134070503d003460b10941d030300c1070020034a200b403036001001580100441c0d200821190300d800c1000f098104090501802004144545c4889444a8081c84a58806403500320070302d51409001c2401405030454143c404c21142030000107112000c502d06000742e000b81d00780c503c003c1c1c1401c01e000907441a604050000b442c00c15510b200f0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 463260746 1250 463259496 463259513
    0x60b010f021b10090e1303020f030c070b131e15020a0206160809060a0e0a0609060c02041a060f1308010b06071101020304030b0c030a06150518060409330b07 69
    0x70310f240d052241a01c1d4842d0f000599040003110101040c9000744402424107804211440d010354204000394a40411303400c00680300c588502c901101c08101040e0105462400d01c2d540015020011200c180150007103602c101e140c82a1140f4030340c41e909804100c070b540d80f011400000da10f4006e80301c0342c581030b00014150000c5c19515419141c462081c058050709070344802c01020f900041d81d4030100420380e844208000754015510100c10301100100800c4011b401c44001c03202d81d40c04941c0020b40881204000007000c0c00e10501c50380c0306600056614141c8501c6003d0940d503000340f040d01a0f402e4403a8855402c0764500c100d9168000018816040004c414003444101410184150303410256250740c1e414100b1004d4400d0300d031750036000c000c010740482070784940300051a030b00015000020f584513018006104502e80c0300a01c05140350800103945982045400600041804010f622007000900d000103009a945142403000200880d030306038590b007401400d8500002096150074503560340c0d4020b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 463261996 1250 463260746 463260769
    0x60906120209030106031208010801060e04140f07060906031a01091e05210c0d12050a0309080409060f1205070b0a020a1a01051003020c15040c080703060b010f021b 72
    0x30215002c00451099440c01e001d040011340c861421208014000302c409005464141c001c81c0083c1e14240f02000540592110b0315002034002c2a801c8000c00d020071418209100c1d0800904a80f194682c00600705501400e204101d8009540030400c0b100c0d0015030b1200445130608007800220916002e209140028443c0c01d8ac80c0c203900359182c4240d9440020131200310318003040ca0051b100300d541c0f4002c2c0c8401406038647c440000c490511310840300e640e5204882c16100c030450100500414403403c014040c0d0b010030070032a003200d00136845c0d981c3ea111341e42c0034152901444078051500305002a0303071503004044a14159018014200355401d0010840b510f0300840c40b80300861150548510101d01000408034415070540a006000e60404c01400300c0f851141c0b00540030544100001c041940001c070303540400c01c1c100540203001d038942e8100402c9800071500010340364001c02000204000e616400124249001e0305c40c2400303086003440c1a1380302d0107500d17010a1011000d0030941e00d03d10307000c01400c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 463263246 1250 463261996 463262027
    0x604110909070e091f0203060d030809010e0109060c0e151207050405060703020706020c030c0904060504061118100e0105120a0e0106031b12150b06071425060906 71
    0x100c0030383e9186051285070105841080313075500480300c0b0300204010640e200c0a04818090294598100b01f001b140b20200540c03c0901005441e02c0407400034882034000c82d03074804180000b030007001074070706014000342040300c401404204000389980841c01d0000360b000010000c0001c09040407214a0b00c000c110b4030041481041100c1004042525503502010705441400703980208142410101e02900e00850310813441c0c401e0b40301000f900303902e60303c2d00d0f15030754040c0d030000000c20a5299881c00801805920500d18008140400c501081003075802c0583c3c401e0700111106e01010f4065441521001c01d001c140e00d00180013001b10030898000f1055860304003403038680000d041d034040341035035084030702030380044802c0c82041003c581130101c512101405816040960102d000c16541c450100301c2c034080022002d19103e4022264036690a000e0b90980303500094554610101b40d1840350b00c7e1181030100040116107045c1c0b81810016485440041e00d007962a10a141801c080e0706544015101c188103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 463264496 1250 463263246 463263253
    0xe070c03120207020a0b0a020607030b031e100908070b0109020301030f020904170301081011190f0e0411040e09060402010e1e0402040305010209091b270a08031b0604110909 76
    0x200d0040c0c96007505c40000f40000480d1725229569528002c0c145075024040000305401c005030820321341c0e00402c04407481d500e408100594018003400180c01c002c110540340f00801c4c508005001807142507401405007d101d0041c1080c4c2ea81ca844050049020070300001d40a84503820815005081c080d80d11030304140609070888150741c00c11011403055209810680781504141c4441c8c00e01055400381000c13803003460410074209450026528036015640d4000ba0030844d40c607002c1014503005680389008200003900510400d017440d135802101e50300501c039050700c0d62480800540d07021800b04005008507416558002d2800e007113020003010b80f415080701b4801904100c0c0c46100355480340300800045105134009030720b40e042c200801136150b0004101407440c0c0741031481c0018207008141254a4100c2c96091390320b10300f0b01400720b1401c80c20380134002500310b180420086001c0900001901c44e1032902941c00b4442c01892502684681050380d0080144031110800110742c508819590391041610084 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 463265746 1250 463264496 463264507
    0xc0302071418091e01060510031d0a050c090a05040c05060f041d070305070801060c0b0c040b07200f03030405210d03050f0601030606170901020f0c0102040f0e070c031202 75
    0x355454102a18540d0180d880140508504070813201c80d410041c0c00d4000800401d85840b000c1a00200001203800406980e02500d52110401040d00820820341c80d00701e61340d0400910781143d03218882c40380d02d8070488404001914420b640d024035841154440c68060701e851901c000d100d596000451401e82c104020b00003c2a44004d0751544508071406452206660401e5507015080300d502400039810420440c005004590304681280300c0d02c2d5102c003080031507a8501100400c3c0e409181c002d064080030001c3c10b407040c0542d504104e41d080d000c082c1d1701c214810301030f001c0080e06450280c8040e05a0001e0204100034a09004602c51980008103905c140080c445145414555590b2961006c41c1d030342c5c41070140c040d0211640c03079400402801c04012940c1400006403403040141c040c4011040030340001512681d0a4064486403e010004142ca9408001c5041d02035006405945140e8000c41c100052545c00c0c0559180248895160180058030756101264560006003140450503000c004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 463266996 1250 463265746 463265779
    0x71b020307081f06050f01270b07230606031203040c030b090d090b090616050a140d030e01110f0f1c020d05060a1505090a0e15030d0c03020714 63
    0x20f480115840c03680000c0c03c0c01409928200c9105070813a40c014000e001c0c880007180d802880c80f41d281c1820b402010155541244d2114165485402c030f02c910f0180800c0c20002c2104d6501011102800031039809407a1a801c0e400300c0d03460390101c4d2800d51651040c0444041503043c24010340e0410302640c140301c0250b071a51a003208401c02074031801c0b504d5000e00008a00b05502c5003012018180d820001480c120302e071000a20300703000301150700d0180361007643c5440c100a030411640c1566580424415184a030304010940c58a00d03c0704858080703424035030791428821040c81030700c40021407400041c0c01d042a0000306815a009403241c03130010074041000e550704000300c112055007648c1ca12000769883c140c000c03440040e0380001d0700c414054520b0000902c411307a0601c00c4c0011050441c9801d83d04c0d85070840008402c0b0080e60f0051041503200021b10a241366100b800702a084402d50494003042d1514500b02d400980b4a2070150041e00101c01c184a145d8028040001c44a030003000900021064031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 463268246 1250 463266996 463267003
    0x10f03020c01111e04031a0a1b110d02060c040e18010f0b0f090f06040c03021201080d141201120609120206060a12051209030f190317071b02030708 65
    0x18250280303c100030075080f610000d240030100000000c2d218003810a0316555a408440584a0a4103007207060500081c10a50303055005240c0200d04100c02c0b2003032004800302800c80345088451007200d02071141c41103010f900005140380109000145c80e0300e064500846001c50201c00340100e101d0394035012416400700c00c03d01485d00d1066001d40001090000c500030048840e03424200710303005100a20800103065170b2703106503580c881c600340c4011440818018045009120341c03000046201e40400000c078030050002000035001540340c40360044002c80c894102501d002d80e00704404030040303110041c000c03d1824410043d00b248035000200312a511540c030401004200c9600c80010703480741040204918040c4044001051140031428070307a0328070344406864068800c0e803900b1607500041d00890f5034504110403003185e9006816070381c01c1d064007011801c81100300c01c01a40040d0350b03012501b09000110075454001d000d04d48642505038400e0f151400201c90001003680d0600030710380005044041070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 463269496 1250 463268246 463268261
    0xf0b060a030606020d08060112050402130204090204030215030f01031113020408010e160f05040908070f0b04031d09070c1703090c030712050a1401020415050910031109010f03020c01 80
    0x380c0700402e2040c10b025000340707480307101c00442040103401801e00c0707026600b00b00c0b40e500c002d0056402051565450010808c0b020f0707a4011100703500e1001a00080301c44480e40034000380c1384215409070b030a00d81c0a21740c0b000f5000070f5070641e00346c000c2d41004100040090b40e008181c100007420001c41802100b245104a81080c0d001c01a10b0351a40070240a07110284040008107000407082d031501030511010910300e503181d01501d40125550a0401d060040c06000e5521056100800949000040c5454003000c1c0099070110082034609a18040b80040001d034030b1501e030000340c02ea0a45079101c000440b5610300d0b03081c0582e14007001c180c0f8020000d0f4018015441641e13150700802400c5540d2052502d04011a8130542d1041108010a800280c01190711200c00e6009100c0181c11190707017002900910640d803115031500700d40110040c00b039412001070410303c181100c00789546d54031088190705a6404a0503c8450360741000206a03540c050b05450300c0b42c040e1440c0050504850715280c50865658 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 463270746 1250 463269496 463269517
    0x703093201020d020706200d0c0b070504030b0f0703020c1c0e0604031a06060c0319030b03030901020a08030901020903150609010803250f20131e0f0b06 67
    0x440c2a58204a29809400c41802080c401409440e401c140e0080d214071660040108005491038903180f2440d8403a6513600c0000d01c60700380c0d41140014500901000e120020031150300e82d41c3d50014040c0e034084c4058804030303070300540e201ca031954030b8441508100300001d120000b4164240034a010102080002c0303001c1c2c14540e14040107603450400b020304031501110001d44143c504210500c0020500c81b081c602801217002c81c80510f8981e44005a8980502c2409500c544030102e0200300003280021080d01d5a40705032020054416042c4c01e0640703d2007460312083c05684a5402c0c0000200302c40020f56210500e00001410201510000b904228440042600c2d4034181c0d82071201c18507102e0086801081010015850074031b824030880040441c4411000203074141b50b080201740401d650807284000c3d40007455031114804074224240742080c0929040c004c1d00175035543c20003280703103110b02c1c83c1d0101091a0702603807840c482e044502500506511000da15154925100302d0745403013002e0a200e060 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 463271996 1250 463270746 463270799
    0x1260a141302031009171c05100803070b060604050604080622030c080a0314010e09160b04091109030307150b0d031704060b1507030e030a03080c070309 67
    0x86800d034140500a000d03000c000c07844031044490006940010700c0ba0400039030f4500c0170030f10034804d003407160200c51a038a2600b0550b0000450b22280d4080c00030702c10800002c05420071440c4c54003e2401004019401201d89640c020040d0001062074001c16607404980209020310700340e126004110542c0045d4072829045d03000b03209124201c070300f40c00e5600c41c0036112501c01013004210b80f00209000c0444602034001c85001800c0e100c07081c46a0010061503960906500003544c0d504282c6820120440e030710022030044803170003071388204c014441b00101e0f8448d00c4000d06041c100890440180010400141c185008001c40c0f41c01e904e083c809080904d003d0705058183d86012800c03102950b200000e901c1c07040f039403030b440e0500113500545041900490040d09402030354403494408001c3caa0440103540c085010317040006841360b80001408814841e9880c410440072403070a01d940c030310706048014089a41540022000b000c404080c2202900a103405007909070345120004914074122060550080c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 463273246 1250 463271996 463272011
    0x50d0b0a21020301182103021215120d0e12160803120903090603040f5307060b0a0e0a0209090c0a020615031509010204060f020d09030201260a 63
    0x340070b106048444217003800d01c02000c1810341d20a035070b001c02c1e402c40c6035640204058840d03059110350f0640f01d1425404003a00d00d6400c0050200408641c0340c507406100310741540c441d8242d05c0c800320341120811016160302004110072030801003052400c8804480900c1144900c86c00c5c8402010200000c2410300061036565582c401c050034000c0c4010400d55a983c0104004109902c0710303800c0700c0c0e00941040410001c040d2901c1c0042ca200c0c031984200a0346009101d030300610014061080203030803185034041d4441c034800840c10450b81d41d40c40c641040c40100f809140085140c6400031200d51500901c80c000c040e03180e40080a00f01300659000c0f050036800708084840d4107155118a404c07480d000b20341ea06103840302070004e41d00d020080018071030124400280b40305803400c1290060b05031100720032400071302d01843c1c118001e4115101c1d110014440c60341614039680040340400048170a0350320110100c5c1550019185901a4003020801440780103d03003d92031a8441070301d0141150440128510 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 463274496 1250 463273246 463273249
    0x711120414150702040518060f0106030c0c17070201030e1c020706030501180902040204092301050909070b07030921021801051309050c120d02061501050d0b0a2102 72
    0x41000380050040c4122480100310070703040b5064460b02075040f50007080300e03503403081c5481d641101c0300011100391040005002c10301d81d40c40e0544e41a070765250303410080140c002d03000301c030080310110010304a4030010818030b17000709034500105070060060501055000c500800d95142200c642089203021075607494412109505004e810000c0c1a00c4c503050006504222009000141c1c290220318a19500c0120b00210f444a405a400411810301d003048940c9034103d00d410b290003040720310010181800c0011038113107048140c15000381d010b17030000c000707142c20000c030145290700090003501803280503800083e070043c11a81140750503085d400c040c41090b1951050100f2031118440c6a90345946030801840075440d03030400b41442ca01c000b030f0f002c81c44003240e04000b400d10600e03101d240e07000340e00f0b0b400c103612040000440d6500d06020f9400c450780c503503d4481040e0b202188002c1c1a0002c1c5081100f00300d040755a1300320300481400140300f50810f03075449112161200c480141d040c14044985845000d5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 463275746 1250 463274496 463274519
    0x1f0c05061006050a0f090f082416050a030906050c070b07110c040f020418061e03020f010f021c030f0c0509060d020a091a090406050315010e07111204 66
    0x24440000e00300d032640c149200035000d4014013000104000c02209810f0480d0320030a40c6400070114600c981000689035500b4a031511100ea00c1036450711111300d0910403580e1480c100c87d10031286070340c007001c0009500000303d03120307405070549004040d04c542c501004645c1602c107440c003418440600d1a0303126000c0c64a044007400041c40c03901401400c8132a0301da43c10020500c0640c0b24021a0001080003440038800001d000d507422454448003a1000e4940c0400903504c008159200840c01c044280b003985003020102ca00c1d4000290840303c403900803030321035024a00303200c1084101e006454049001e02c3c80080000303010b0140c0d1000a40310014050714284c18421040f49100614103a441c0005100c04100540308446a891106500041c040000762080c00b4000185c0a020701c10040c4e8020305420300c440e030700054221031240789001d070000b94600e4002035580424004440d8030401e42c2c81c0140c41329000000410790414449200f03020368005900340031142a00f801ccc0030266072101e0500111104 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 463276996 1250 463275746 463275751
    0x40f14070e0f0a092613090203060f1c0609060209040507031a03240903090603040302070305070b0315090604020c01020c0714240a052502090a06050d02040b1f0c0506 73
    0xf109140070184000704441c1720007511281040402d40140700340740c1c151001c4a2051824045081e03170425400301ea00721081c3c0041d40211011200e0204030b02c0482d00300310300480001c1400701f0101001400d42c000524980080c1044c2e40100300041c2420340101c042810781d101141d42e103000955501031070f02c0c1d1044044e1b005c00c00c241d00382c0040040050140440c2c043c400d04606140c07044940c031000234814001001205e0327a1040251081e503c0342418079020795911701c1ca0100300e03801e000d0144003190900c01d82c0103403031150501001e440b0008491005209800c2c0d0003400c01c80c1c10a40820500d20404002d00003001c240d0712001c01072054515120b075414410035020b0607544150102c2d400c00c01e030518220741d00c90707811002119182e0344104141081c0d44c144100707550003801d00101010614074046408043d013146000342c1d0b0b05409a43c486205900f207032014015942d2108842d0120702c0507041a901c80125031402805000311002c2c51009c0d0004800e6401c4880300088a101c010300c1049818465241c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 463278246 1250 463276996 463277011
    0x90b04150606090b0c0a0204091203050705031302060c01060305070f050a080d051911100204212102030d09050102030403020f010b030304061416031211040509040f14070e0f 76
    0x101c050b00780400148111001c0c0b2960000c904c01080840345a40180007140e80541c1c0104100504d601c02e24002d020300500404440201c0c0c644000141c00900602c1224400c40145c0248e540206469007045810742181c15041190341d0f80741d030040300283c0200304030b4010b88072500616040903d004100454889150080c640c2a0000150319025036000803e544c404c1d40d28010f520070b081d000c1c04045465030f03120034038041240310388855200c0e40032440d40100b0139100c0044da1010015080b884034504080f40290041a040c80d0808040100581d1285081245014419280751041c1420100152400342c80e040c0d5180e507000041c4030030150104510600560341c107000b405040e0010b0002520780c000ca114450901c15401c84c1d540f041c000100448086484188081e1540c940c2814000c02104154910106140c42c04c0c415042551650f13058504607800140303c0c04071075603030343d1303c440380d03c0940391040318508040e40c4440d026200c140642c1001e040c41c0b85051030a440c1030b40c0303a180d800d400a400340c2c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 463279496 1250 463278246 463278251
    0x7210206011802071e080d05130c0918061e02031501020613080702060a21060e06120307060f06030f050d020d14191b0b04123f090b0415 60
    0x240000b64041c103031701c43c1d0400020390504c0c41c0000da00700003246215040c5003031406840c3c1400c000c0d03012000304131504458007403442c454540307441d07002640c12950300e99281c0030f59002d0756043c6c100140c841d8001d11200001ca0130280c10f00c0c1c3e19507942005076001500d1032100b0030701807400441d1550303040080691010125122240d59001c2c1e0300d9014980c07041e9100a030180c6070028185419a0040307000c015680c5841800f0304070340c061103081400420b41d500403407402c54640e9010800600c2d003044a00d003540c40081c0a9490030340d06035646d800601039504ea5009040e200e40001021030136003908210418000c0d00a0f00a50001c030100909080c00c103919070003400700e2500643e090b80e41102c1510318581c10903030b01140310004210140c41e00344501e02d0760071301c0c0100150341d08104035001742d4150041d44580d011800607203480f10103480e26000f00307400a64103c0302480801c50800c1101c032001c8480c01142d5002c0d080c5000c010303070b9003d865140d0f006036121806001401304110340c072003007005401c1c0f403070008 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 463280746 1250 463279496 463279507
    0xb1e150310090905070e01060e120d1202030604060e0106050d0b040c0f030504051519050f07020d0f170a0e1006030b0c07140f010b120f0a0807210206011802 69
    0x800409420070300030342d0301103541c1d41450010031100300120006443d200468140301d6a6801009102614003821240954904004104c4404002801c0c22000b14161070340160318440c540d251000f50002000d05600c562640c500256215800ba80180a002580d44003a90362002c80292030a41d6400803580f40140e1824042d0f05e055648503044c580650b80c06d01d400b16245d00e850624030701d403000d00c0c10340c11440418102885000c3c2c00d5030091400301d00b5a030354240b18540e54011100e8003840200c0380040980c01490309058203d10401413850094001e0900e0300c1c0016000500042d80c0c08101c400c507030f045070740395410400f00604111241c1c0801c1c80f40700030320400b41580d070341080000300906241c0c4030410100c4c3c1141001602001c3e0700c1005107980c111035418401003d800c0c082e20f10301c8640d44c010720380c00c110710ba48100c000c2a4503070911400c100910381070b01c840da285c00301030b4411081610f4020400240b400e030380154030801c91444140358002c1c034241d4148001e00c003003040500360329040307641304001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 463281996 1250 463280746 463280761
    0x60613030611270f040903030f05010b13050307051f0c05060408180607121218050304030309060c0503030c0d14070305010303080a020703080613061e0f120b0f06040b1e1503 76
    0x504000c4003005d4078007240400e41494283d000d014800a000c0c5c0017420900003084100b14400a4051803030350200300290340f03a42e4070a00d0b4807003406010b4075401803c0059000304500828a0200290543c0d113001d01c0039a500391921400c01c5401d8508540038680041c2001428031000b400361b081040440c0c11902d1314140c0c0d542e22940001c600c2d000b0045c01a410384000000d1915400380c42d02001c00942d003c0a041d01d45003594480c0d00c140070480115000320350106009204008200800ba800702c010b5186440d0103445403541e8100b0700070880c0c403c4d02c1d413071070040d6640c40c9004680519042d40b00826154110710b000fa016460081801d04020700c1031210034042b03a401304507280c06c040309640c00d00124080482c0040501140d80000c8a86400b041500c0e2000d000d00038100111402c41e43c07002b00080c4c54000e03074421840043d01c00342a034051a0046600000030017103194000318020700014020312403801040c3c0307203211504c000d02402410106240c00b030070190003491000586c0040c40d49140741444 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 463283246 1250 463281996 463282009
    0x30f0409110a0e01080619030b09010c030903021f091e030807020d120b0a030501050c1b0c0108071b06150503010f0209030a170c031309140c0306061303061127 70
    0x5903d03904010a8501188103510b400d022071100c651480750070181c140e103074140740b051804261400c60240d868841c070300e05594401d21500d01c0f1158194040c1c161401e501d000d0b8020081d042003580d82c03140d6210801c1001031400d01c0600a0020169460302070001d0030704003c1c0c4400d40040602080d50088041040b00d00d6020160040c082036104c000a20700342500b010034003401a0743c0000f010303036280c80c0a04c18001c4c0e040c009000704200c028042c0c801e0110000d9101d88400d5400d8030280818480b0b4003147c1120b006003081e40e0002c005903643c02070034105454140a54088200c500102100c6103820712035810207010340032158806c0c4500750320b401c856101107a5984800d40020b003007407994060070200080300c101250450000a8222500c50601840c900204129440740310982890a100c0c8045140125070052081c0343c944401c60a5580752014001e0b940d014080001059180744070100010314030b03104940e007040066041c5a240c10103141c0706000e900c64480c00d101c003003481e11903c090655513070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 463284496 1250 463283246 463283267
    0x813080c1e0d0309080f070507080a05070816060203040603050601020f0709060f0b03040c05100c080307030c080708161101020d0501080c090609041104020904021b0c0a1a04120f05030f0409110a 85
    0x24050350b0b87c0c250504106040860507000110103000382c000042c2442400524036043e0b0f1003c1c0d0030350308601101501c00c2d0442d08148a0000503800c240b004000d840c0c0640c3c40154044010300642e04114842a0b01c24142070154000100050f5030701002c0c00360070100020440a0040e2107020f40c0365040648492031511b00a00c00d9034400c5003241516a801441500c00500559010380d56980304d0405030805406040150706007000903218100107511588114042405080c12031024003d0b03a04c00b40e402c5401025201c50b0b103900d91340070480b48019a0023845000d00034550b071800341188100301c404120000b20060f1640c2c1c07256280c40c0134040407841507007120442d0b8400b2203005070380d44124404500640118690141d401c48401144801c00340c002c82e600d40c85900488400581c00e0f1201c202c100c610403c4020b107074100109000c107211010102c1001d020351380c003031002280d105480361354081c42c5a1080d0b000402c0d082c40400c04003d0b440270341c01411410034802c61410704041c00d10034024012040c6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 463285746 1250 463284496 463284517
    0xe0a05181f0f0204260a020a080f011103040f1205090607030206180a080307080411040513020102010507031a0f060d0e03190207050f061b0601080a050c030a030813080c1e0d030908 79
    0x1403003017120216100b0005554003681c05003902c1010350352142d00644407500c1c00101e41080d400d11010444080e0003030100c0f8812988a049448046820384801c030321023441c5821901400010030000d080e640d22a4040c1c0f03032f002c0c400d0380185110710300078019032164800710351418659403051581034000354114054039401540c84c58014071a80d90360500c13202c110b40c11071080350440d203450203010805400c5418518158000e80081c001d580f60070404074111442c03490300071080c00a1420070a41441c1074844803d0750540101b0080c100b1000c945d864040320420342c135503d22030380001380c1e4840b2080681e140614210980c0050302c805450100862003036154401050b2041c1030004000300d40b0500420030600c520f015400710382056031101200c556807050b503d0f081c0d52a110ba29141d001302d00d000034200c40c41d150705582d2002691a011121700c1d000c0a031542c2225416418021008081c804102290342002c002042c2243c0c542d105207a1410039050740084410541000329010116030040215010201c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 463286996 1250 463285746 463285799
    0x2010e0d020a03031d1008070824010f05070210020601170d1d1311030105010912020609041d0613030f020c1e030109060f020d11040e0a05181f0f0204 66
    0x140c5044080240b98400d0300c1766000b150105035940140d03021444611405007511803402c0354407402014001224051001403840020780107141040d4426100c130803d115460400314103280341503000414464404400b08010b0b4080c0004105155080d8102a509011030010f007969008440000b42990912001d4003c00f080c50603444d061512032020650b000702006004101c014055800504c26610a100d5213002403c081c402140713205408040c0c4107160740c018142403602c110300040c8400391a40d100d0b0459114641184c024143c0741c14808181f10721241c201745002d085640c40c01401e07201400085000315406481450728544858044510340301540000400e200d040d0b40000780941400c100040c01d040c2000340a1400c03250380d07000f91050414411050021226400c00d051160203544103a0600050107070114603070303c980340e220301c1c0c100301810071724100804032680c1c46103003000e04509220b44540076100c4005e00340291190300e580044a201c298900b510f8407000c00150b501d003000b24040d408 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 463288246 1250 463286996 463287017
    0xa09030605070e06070b010e0a020408101107020607080403020103050a141302041e05010315140a0e010207021810080f07030b090f010501030c0e010b0915030a09061802010e0d020a0303 81
    0x600550400b404044004d24482e5108818500780702640800e100300c43d8080c0b403060228138076003403600a50341500d071464000c118003800c0c0b0b62443d016144030241c259949000b0400be2000d622580000d21030b15001d040c00b5a9030f180745100040844000401d408101c0e0b2400305404042103109502c40e81000244a08610481300c60000034000c03c2e005143c41404003503131302c04030b200c0c15160308018122406840d4886052401c118000c041c4c841c205070505900c035407480022045480c81c2e0001b00c0c1c403121140018140201540810085034404404d140303040c040074100b041e214140c0c038074040644007241c050100c0074000002c9580d1041c0c02e002c0240302881d00d1002909010f0b0401c009510100301304000c2c421544d4030700301841030100a000b5000e40c81c0e036000000c941144184219180f10602502c2c1c40100c2e0a00196000180c2000d01110000317501c03038200c070010416900607070000c800f00c51100b00e480300280c8005003928000b825801e008a440b442581c3c0541e944540c01c0301147d805090403000071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 463289496 1250 463288246 463288261
    0x10e0102011401080106050a080d080112150207111c0201020c04020901030212040f0309170d03020c101a10170f060117010f0f0540060b0705120a09030605 68
    0x40c1000c500d18005a110030000184d603000540090040f2a82600d01d051f69507200c2c1820754503410040e08071800316843d8001049565a03050100030958011050b5002d003565180e1448140da000280035030700c104020321012800e160941000865007417440007428600244e600203902c560000907654810359010507528240e13402038040702d074080c0d00d03d60040e116151a1400c03203076a0302d4524096001816080d4041100400031001e0040c09034480014219201000000c0700a5032115000c04d86500626080b0b81d01000c0d1800346980041603d080009608140424400800f410711001000c200e504021542c0d4a00c44441380b40d0404848000d40282c3e80c8e800006903a10102030840e0070508080000004004480c04140e00a8a82c18161790f840140d50303100700b2031403528007031001d415400c00f0204062642d800300c503030040159800c3d0820b401580c1c401692001c03660b480d8807004001900280c5036040003424096079060784600410b00d4202208014010140310b4980002401a41c3d0340020030b200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 463290746 1250 463289496 463289501
    0x10509040617121312061b02010e120f030a090507120f05060601080408121902070302030c0709060e01030b090304030b07030e0c030c1003020306060c010216050c0a050f010e010201 79
    0x90400a03009114032540e80c080003058560440312034000f80291071081901c01c44110444602ca44030303102840c5101d061140d000111854003404665040d80c44008400f520744180c1100c0224009400020f04491186001070822000e44034242220004100c098041182da005894200001c01000503c02895103011850032a8941010480703140107540c030713820000f42050740302025200b40d0590382c1c180ca5000041da1003400a54004000c810180405240000003c42c0746a124031004042481513092440d0b110032a0301008083e00141c10002da1200ca0600c100b006400924a400d010440749203001c00f01d16100da4180401401c21000c0000f040500c8010401e0358051034220320002501c0c144600054003c1c084030000c21514000c100708044146404100c84401c144045e22184480c0c098075021002988000c0003582c0c010f4040c0207101024000744040c2c9041e400020031265074081c10305041d4036020b40111500c3c480d51500000f40140d85034a200e10006040c2828046017900405005074007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 463291996 1250 463290746 463290757
    0xd09080702090f1005090c0412030e040c020705010809060121080904050c190207080d0c141518010504051e191115032e09050a0f0e0f0a110105 63
    0x50080c025024012810148801d031401341c030103100ea19042c00e40ea0020b01c10a020300712210b2045d00700504c0204040c84040c6041c182892280c5071090745491030b40c0c0028221403c242031080160322032002071280c0d507048041e058105003440000c2400e585044850003510101314111034a413080c1702c507098208104402580e81a1400420a00580c5000c40960803550446103008501c0552500202005800802c11806984404000e0104401c10f09404d81e0001c00c5520102c80660a10300416450602444071280308059402e007003507581041e0100f85a41c2d00b1505160303a80d03914280038480029400124100c86909059440d520309110126844c1002480c51110001c2c845900e202001c111080b02d03140810f91003102c00520800241c082c0c0d090500003229800d06503000c1100c80e5181d09040d10100320144407048820311141d4440008106580068540011503078651840783c6801d00240100a003003411360f002880c0b000e022984903552440c8114001c2d000c005151000d8400da40314008644 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 463293246 1250 463291996 463291999
    0x60a050d0c03090c06050309060a021c06080f1c300c03090c0f03030804020f0a05060a02010504031707080f0a0e01091b05040b030d1101021b0607230d09080702 70
    0x120000c0c1a40018024212021085441c4e480050f008144640602c00f540d00806224004104a0303840341984402944019602030404041402e040000e008074005d40010b00074220190000f1184195010315060307112072001124481c0302e46d500c140541c40002d9400c4000d801880c607031007504c01d0b1701d030480f02c04044920340348072810040301c0d8181907050b03042038089034440c51080d120b41c0d80e50b0082103540d28150000900140146001c41d015141c900c880d0728190400500c10b602080c0d031a00010034640c003000407140541d444900f003105068010410118001144012440c9413070400b10043c41c45800034080c400002ba81d0700404d180d4400ca81c054403801034a00000c001e14900307410300c60710003001d400300c1003000c0f8646040800c4504050080d2800c1240190050580d4000103c0c00d88114902f080d22801642d800d00c20541c07101d44131a1810070042c50207003d0103180c1000310f07000b03042ca5a80c0c002217046954035000c58140c20b221404807480000c01d49000103030402c051a00c50b10621a159010f0b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 463294496 1250 463293246 463293251
    0x120f0905060f010b0c1002090414010f0f0906050112051816090f150501080903120408071a040b130c05040609021b010c0e01050901050d0f0e0f150105060a050d 70
    0x104000300091414000c00907003441e115203a130380d001c2d200740b28400c07441e00800a07084848003040010f0950090030301480010b0010692082480007400d0103c0d090303105c0b02e0081030a0a0411101c040381c94484007600c40800140082820940040c10b482200555074954036511400901781c403d643e030308140d000a000090f508038001d03250768805080020300400c03091034507200303008860002034800c40c104c4030040f20300c01022510303040064810380d00080026525002c100001d00103402d4102000d449244504180341d101c100318241030109100d0140e4080c0507901c54000d20004c6400800c4a50344184040c884580140d4140780080030300a007540002d400030309041c0041542c04040d00a0701c01c001d00001740900000d02544682cac21b0700c1c2a8040384010803803400c030002195101e400103102c0d45406062280c034002040b60f20000b1036400308542600d05035140203280b802c10051084440440000703009051740640d8807400403250308103120b10340c440c0e4400a0b024400b14050000d0b554a070040c3c4504 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 463295746 1250 463294496 463294511
    0x2106090b091b0a0305120a17090d0801090c091806050301020c010b090606031b0a0309081314040e07090207031808060f01240e060906070309050f100c03120f 69
    0x1c540d91035000d088007003404041120941a18284803c00c0c10440760401700a001c2c1c002004c16000c2c09501a9240404105544a02d0655280c200f400607021300c1085000b4500409501802013800d8410780180e11102e040041e09140b40741e01900075011f40b001c01d0140b4000002c4111031100601c2c1c554030050300341d40045880c015100d010b51102007550710964900907203650b240300300102c5100c1101da40003014480d8040b10003e12003403003d40b072120030130709000500d0b940a803510241504102c5548000313400e155010300200d80f4480c0d200b0440482550305000d0303103886651076901da83d6240941210141e01165480a251041c0c20045501d004850480b0029480d002d07200c0c1c03900c0d4200e812030800c1900000019040284049001140990543c60409941c0030380d0225002915040040e52203502800f19185964940d0001c040203032082d11190203940c50081403201d0640c0b0b01198610501c01010949416a040001d1921140d4146030900c550140382c884d8100511051205050305403800300c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 463296996 1250 463295746 463295761
    0xe011401030b070c0203150405160306091101030c05040303080c04050904050706170c07030c020f040507210603050a021011121810090512150c0702010f08012106090b 73
    0x14040c1038a00552001c4103070b0361000c0b401d40303070b4240800b4025050362000e1010310000360542c550747d4100d07200e8401d56800d154000076a9582410300d820076644107607640780740c104200361801c080504206c01e007030601003400004400342aa015a110260521100100051200340d0b4401140d016020092408a2038281810425039038285401580041501e1055a08803600403550705403160800c06101c40c9030420701c4e41c080b0740c0710030034400490f081a0002040c1216640301d000382e520908155507003034003010100024500140580080c2071442d0316018040c008207401291a01d015070701a03d501e00300d4000d80c0c1045a20b070b9078084d603405a83c000c000c01c5942c40d00200c002400d4008240e500e100c1600041010003800181c400804000b08420701000c001500340b000008450740d00340302c04d45030b03426400300c640040c181d03041b2400c41c08140300080c0e11045603009040d01120076001d00d0041b00940c109400107064401e820200ca2401a0305203a040070842e9a8200350300d1180e220612401e90b080840c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 463298246 1250 463296996 463297031
    0xf0f3a08120106080c07061a04090b09010b06071a090f010609020909010e0f01060e0f040f05010602071706011a04050315150303070201170a060e090706091409040311010e01 76
    0x40d0380e140441581e4000a1003502c41c035101400b83c40300c01d02480ca807424954400c4002c10726003455681e41a00401e102c44d85640d64400d09543d980200034005c0c2c50704c4d0601e030440c2168120601c143c4203c806020603404204880ba45035250300c080800c4680b142c44024065207800c051500c03003c520f40c2040c5011072103403007035000340079640c100703480e050000d0743c840c0c100b6891410125810340200e040e00004110281c4181003541c1c4000000d0a80c400d8500e107400484c06503180c1c000c0c1501610784440040115503810002d10005001c0c5910340c4240b807030880b0f24030341c5540c818822840c9071038a6080400300070a50108450040c68001e04642c19010341801640401d0021901d20440e0580d016110300b031401d0100c02c40724030540c16964217401a03000f41950407034880103015a003032729944850204c1c0c408a0424564021400749008000b81840e003140200780b40d000303402803541030480c0d00d910b507036984500e0b0b507140d0495414100b884d000400c1d141e0683c010f102c45140c0000070760a089681a602c188403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 463299496 1250 463298246 463298257
    0x151203121517030c0c0604140d17070f0b1302010507060b0a090509011a0a1d040c030b100305060601180b070203010f050718050a0b07201e0f0f3a08 65
    0x40301600d0385c8039480000c11645028602c035101030001502183d401ca860140e101103110b510400800ca21140401c402c0c0600d5000440102c0d8a20340d84611001440b022003810395010003242020f1a41000950008040d0300440b04007e050329116074034003c065646622800240000328410007103403078502d6109020344004103c461030301000d0088006c0c141017580c1c4240544520416402c8140103140d80d40c0ca8500d0002e105481d192903044010000130041c140f240e003d0b0441e90301078100300f030850506509058014018034180f00f40c10200c5504400a01c5891045860340e90016855071000d0010030701405000800189240c540010002840c0e00b10183c0110031800e1903d55a01e0307900d81050004001540c01381c040645414002e020001c0c0d4502001a0081d0450031079400d403002c40400f19125a0380c2404142040c5045100c40540341415003080f41681c5085076030b400080311500201c2c3c0425003074114040d0680b509000c1c614580400b50744c5e860341517024000c100400c0840e051506058000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 463300746 1250 463299496 463299517
    0x22060e13020f010c170a021c0302250b0f090c0904030908120418090311010606080f09061509070309020306130b01330309080d15120312151703 63
    0xa8074401c482c2d5228009188060340c0c4521410018920203081119540095440b20308500c50011080c0e24540c090050b45103841c009c1d10b0168481900c078000d681c5034010607040c13590601440f0341130710108408003c4a40c01c0045106070b20f0040d1101e090740e03801c005500c103000703800071403800500080541c00003200d400c80f15040180d461656511a010246100c0d500c03807107125405c0d40989602c1c044180e80000b840318460309003480355159624000c2e0a407581c90744141c0111f221103080050003044039408591100650000d8140362a042c22035050303068030030f80c240d030081940707000290300c15009a01c801c3c4030a400504413661442c110038940086031403a0340072500e40202030b000003940c1421401410a0901d02010810529034034401090611060f100d40800c050f03c0702c170f4403030118240070000d00b40c1c0202c081c8041500500a4000190b440301303540302143e034000a52641c3c0109902001b55408089c181102085454450040c200c0414081d084100e428100282034000070400000411030030a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 463301996 1250 463300746 463300759
    0x90f0b010801050a1505090c090a0e06030d090503210408030408030301090e070510110312010b03060109150e04020711030304080a0302010f0507120e1509010209040e0c22060e1302 79
    0x403844000800d807191100420240c0f001e8645c2403160740b03440b408642d03011004542c8141440640c400181c15151690702a070301d28288001404014141800416101d108605001100e5403802020030b65a0084403c18020001c9800050b1080c41c400c4084500425005040b80c0d203480c0c54035151501d9a1003071188145891401c0d00000d5a5000483c278001110001800c0004c1072519542c00e81d0100c03112007840d044c80c00204000300e0380b0fa08a05415010380a510f00c202d450303103400390000d04451015007103240c3d0348252040c141e5800703510034440107002d80c0a540160700c83c00705203013030303001d030050403070125803501002c1400b0030003100c0003e4004000d8000c0c1d0003440780c0011060324400b1a40d041d940e00740024004640444a03a025821100c1c1d011414012240c0c085556907603908049805d03544861140d40006032103145242c01c2c01000907240d035032400350204404210000c1c45041b0f108410406402c11581c0740d400c680c0301d580c40079004084954140c805442d00500d404015240c0a0049209a2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 463303246 1250 463301996 463302001
    0xd0617030d0b041a4e01050c0a030c140f22030206071e0210091701140106030c0215070804020907080402130506030a24060b13030f0204090f0b01080105 67
    0x103414010750103410503240181490400543c1030181c80d0b41e454004440002c41d603010311003550500b02ca22020b2443c1601303110785207842000201c2d24170207901202d00c0302d6810305003408090a100011280185018240010235086001c0b043d144080900380c118501d003404100c0c40f4034490444003c002d0b4098000e0005d4080621503008030324007003240030203034001405000c00c2000030101401e12041c28444844042c2c1d011066000034504100882d0103400070b81d01060800c01551801480000285560b000740003a40c013200d80100e20410510699082580722a1403c021900901004600c1403002c8a0048285030000e40984868020750f012805142c00c80005102d80d8440d02c0701500480d801410402d0310140000715002038400035080d1603046c010b100882c0300007001c00c0c40340c6582119064501054030300151205040b548503078000703203660301d08002040180701c1c07442c20281500e600c07a8444e08004c02a0000c100100407601d4002c04000c032500d401424460301400060480351810300901869 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 463304496 1250 463303246 463303249
    0xf01150c021203040821030402090a06051207090506010203040e040b0a090c080a030909270c05030706020c09060a080d05361002011a0d050a081b012f0d0617030d0b 72
    0x10b440004400820400388080323030042c900850502c1d00051101004200b550300d50000485c0d4031086c44594215034014401003211104a0081c242c1c000024000ba40c00c1c10300d8101c8601800000420007400c0c4440000002c01c2c00480341d10030061150003d00f00c0007816241d10480d0f5941e101d901080d00071585c0204001518111806060b80b0303480341c001c901851a050b2094540750019840d412540340300903110200e61038030708004144c004d0140758010076081caa00410300c000306034050700540c024140034900b4006080e0002da1403001021038070340a599410340d518000c440080c03415004007642e0362070030102e0440007220125655040200c0d162021031802c0d041c02c0e403c81b4481e50b2404540c140c8452400c0701403414501c1019824000d405442c040401d507640c640c140d5220112006d000400b101d82c403600c0c0d8009200d0080d640c2c0126039081000c5141e12070b00814052880d202c070124120004003422030641a40101000345140d091803815400d81c40c565a4a07a006911185141032403d26043c0c0385 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 463305746 1250 463304496 463304533
    0x2130203040f260a05070212032205041a100e1503091510060e01030609090320030304030215040201030b121e030414060306190b070b07080f01150c0212030408 70
    0x881e01003001107444c294404005440300d401070503007a0ba010704003106400c0d0f212801e100070500d211600c0b4004c5048980c0b1310400300a0381d06600802e005030301d171108d111012b03a4410704055003020200d900441010113050101d4850440901094111038460880b5000ba02c102002d14013803000d1006950358803011656281c1c54031403c40c3d0b010300030800d816003041414011200c0740c5c2a04418074000c912591100941026a140090120000765001c0c20115600140419901c00340201c2400b440c5142010b490096131130307103052000e0307003516216408942168020341c44030180c60406005c020800e842d05060581700c1d1070030421600c40541c54541101401700c040210390681e9813803280b01c0c60540e0644203010301504010400780d0000d4141d02c6120f401e40800402900402840202030740d0f8003518030304044811070182c01107051191440503c001d41500c82d0f0a6415541c6440303402c0e044407010300341218200004040a900440c9891000c03a80e190080002c00079969120210b0321300b020110640b610 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 463306996 1250 463305746 463305803
    0xa02060a1805150618010e0a1b0905011202070b040f06060512030f1b1f1104050f0d020619120c0206070206040605060d0204021206090c090d080702130203040f 70
    0x8a81003844541c80a0440030700c0035070802c130040c0c84000050740c2810340146180e020380080c018150f4070410402509407900541000d01d020344040e00c400100160040e00305015801080d05000c1001c64646031110983e040e26112a00440302d804d45003000d050041801d4074000058584506010001c90942004185040555115030080d40707094101c2c1181c4e00d1a030811141c40203001d01982e00c1301d141c003004000d0000c061000702118100d101600901c20211a0050404061254140000c0085030b541da200d0300c1468005640d0008014128800207081d4420481403001000c9107204c00205039520201c040b00c0650032880800540005400c181e0366101d08841480040e840751000400144958205540124003c4e01403e440705c016800541643c0144140321a803806050070050301d40303403038000260003149100d0101d00e0074102c2000724070806901040580103440000b003034030440d110041c41410300d1286c0141151a8185460400300540c0342c15410349002a010807a141545100c84540c0c6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 463308246 1250 463306996 463307003
    0x1e030907030605040f0218011e0605040b18090c0c100b061c061d0411010e28030c03080c1011030115050c0f06010f08010902030c010516080a02060a18 66
    0x1030440d01d1030b9110b1000d0403009208480c00d420420009005032100c1701a20392a650500c91500c481d0b050030440c95560b00f4132203080320101d401d0300080090071f4000e0102d0302912010b00516035901329616800c00000c10307541e000c5800050a1040260b9010010b01404d24010614252100130040c406104292031030020030136480b080800c040d44044248043d0007144048407140070806030b0b901c020144181c40318100355841d844440b0300300400c000c030914000c0307480402420300441b140d03009000b03e00342c0c4105000905e911442100031400680d0354403440c00056a100750020020368503441c0209054001e40c01303608081c1f16400007003007115107901840070b106104041d8507045070b20302460200540e2840d41e441302405405c005600041703005100303101400070400c0003402d45514000c0507001110a03503100720450f0b49080d0810005079008600d00840316403d103403d0380c603980c0c1d0807500401d6400c42100107207010703000140d800c3c3e020380201d01c181c070541c2d21480c03c100f1343c030441034106110701880c43c008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 463309352 1106 463308246 463308253
    0x120c210303050601030e0a0303021e0315011403150f0a090207060b1207030503040e0c040f06120507050315040504080d14010509062d060708070303021e0309 69
    0x50f410010030300c0c0030040e40030241052034548502d00d0700203081540006481c1500391000010242c0031500392422a500d040c4000040c0c12111410159800324007012003a0901001140981e8410004c07501d5801d2074600d12001c01003400340c0780c1d80d901c0c1d1200c10401d001c1030800503407001d054501d2290780000703040344102081020400a11412648540c0401310500c00184003100b5601110443d440200046c0c403201808a00c0d409160003079400803122070710020341141d02a003a014104480d020412503612400c40031501840225121038050001010229280c140740d441a035005010728036450801081842c24020307a100207103901c0800c60507000610451904401c410b4018000326404051100c1c6011140c03e42c14100089141d0b11046468400e401e40f91001160295580004092740d620290b00c2d0140c004d400040c1018941d22401035288402d07001141285e00500042c0c005 = true := by decide +kernel

theorem cover : BRFrame.Cov 463129496 463309352 := by
  have h0 := BRFrame.cov_init 463129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 463129496 ≤ n) (h2 : n < 463309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
