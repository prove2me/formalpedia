-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5383
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:41:37.166217+00:00
-- url     : https://prove2.me/submissions/218487fb-8c35-429c-86d6-4692a7116ec1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 967985611 ≤ n < 968165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 967986861 1250 967985611 967985677
    0xf0e0c0f0f0d05010f0503012003060f0303250b090f0c010e030a0203030409020c1207080a14070f060b100c020d0b040f02121b01210f0b060a08061203090a0b 69
    0x110041e03240d00b010b8501003c7c5403d4a021002060b40c44202088030071144140b0000e80ba0003072029110184898a19804a8a144180c0011410000794001c02c00e06403220081e50305801ca118016034090340c2c80c0c000c0d4055464142050a0b20703d40c002c1c15205c0a994456107020b80603c0005080b6010380f41d0703a802180c119071054001540c0750740c00040d041068501081813200b00390050144501d0442c080d1110714560052074503c40811940a2038450103480740d40039541d005400020700804410140f8045000740001048035020703009000e0017500700d50142d0350741240c0c40d4003e8180103680783e40d41d8850101e070344002e04c11034120707070301e0742c070020140e106c1075403c031544a541c100804203517202c80c000004803495040340c2410403501010090061182c04440c14a00b5640d800c01310743c07071003580021805064041c14142e0000000315a02001640c00104240100c0081d500315a40b0b0115490380c1ea12882824051070b002907644504200344280800240a62026010402c4000c1682130f00c00544076 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 967988111 1250 967986861 967986869
    0x30f0f03090c01170a0c020106090e0a0308010609140f030a060c080f01050a0b0f2805040513050408030118090204061412070e0a0c09030512040f0e0c0f0f0d0501 71
    0x2940802040750a030810888180b140409007004d071186010340c800700c00000f000800d41c40c14651243c8280b007005000b504001c0c00346c00420414880e24042c03400d801c4d135681c82c0c00001e0300000e4589000250450003540078405031022115020680366100d8140a0305401402800385c06100354a814404907200c0d02c10004450010b596141c500c4c00c14800447d091641a00007520404641c0780030802e0880e03000844200013840b00100d501e0318030041800b0103661040481501000080c0c003142083d6a000c0c00030016124215a0800c04902c3c040404040700c6003100d004090690070001401300c1905600129080e14000e9001304070003c1035404241500c41076440990311480035213810090b0b18010012000510104000300602803030443d010340f20540291065054965034040d444c07041d8030400c5050051504072040360300e20301404080700e14070340c401d200e442c400305c200c41c0010070781c401c44110160003010341c1c140315410810b2100c181a030035409050117000d2824200f1042070080084d00503e4000c0c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 967989361 1250 967988111 967988137
    0xb070314040e01080706112d120a0f030905190215070609060c0215070f1704110415060e040f1b020c0126010e0630010f020304150905030f 61
    0x55140021301407514502d60030a0050000001c054007000200150055030010484803104d006c0300d161110444210320008032000d5800340962680000103103400a140c0e030010366031882080205071800300d08076041e81400400382d8200e060320700001082d0070011461345000501140d400837000300450650352104008403016601c1d41c1684052100781d1003000440c0c2c0c0f4900141140d58441640503400c107000600718014401800707001407482e44100f2401800000003000800300e420b150802100c904c50200249206a040c603003000018010020500c003210310a031035400700500800104809000c903d0010b110310359980b40602450344405d2030b40b10b9180d60940150000a1148000520060141003d100f000c82c440301d10015000980d17000504640700f450400e90b0701e0321580001800d030104e140074100011000e00c1031714001910886154001c4420400030051011110702c8007050f40402c807805416000c80c0100076032605183c0e004610118460000e4038944801030007408070a030030034941c039403007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 967990611 1250 967989361 967989389
    0x603060302150703051603050903120405030c011e0f05160f260d0b060d020c15240103050603010605100201090303060812040320030a03110114060102070b07031404 72
    0x41d81094203520303151601d500016460f150342a1409445441115001400c811600c40c2000c02d0520400c10346000c0e04000302035615241e806141960b0582080c0122440703400f400c0e4045040b503000300f51000d50303500305d003881400507448120305031100700a040007282409020403103040c2143c121071803482010701c1401010460203080c1400801c0906003802040742c1140035040c0048400c1013800d42c0c0f1814006e06001c01d0120129020414a0264400b65909a400810003403012500414494441241080207142d40e5941c0038038a5001c1d8881d506010702244d6821030401c0b2540300c0d8211503403040c0d0160001c10b18550f54400f00700d03146005801903006075502c0254004241d8140500b00080c00c014000b80801c1244202600340b903c80c0d4840180a580200422403400c00d94550100381048000c0c140d410419140c01c0c050001c40200d0a0301703c030b81d4079084400702010203083c0c205002d50010790081a81a08001500d4050f6100c114290107101201900403a0f14002800410103050a1004608 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 967991861 1250 967990611 967990613
    0x18091510050c0124051306050402041205100b0109140d0b040606050f27070c060c0503041a040b010302060307051209010f0c0503040f150e1507090f030807020405150a06030603 77
    0x2003140d501c440204c0c1c00402c90a10803c00a00080a840a5400840d985410b000c50050b201004005503401941c001e40041400200c629150702010642c03406203094071103c03070703840b031503c0c0c111250b1340359140c04580015000c1c0550709010a80100f060005080ca80802c405038843c1c0b00b6000046400f101e171152110700c140154203040113885421002038401c2020031021440c140341d03106e40c40d10241030180c002c3c000512101c0c4510041c03101c1d907400590800c100d02001000400329031084031b065a50071403c440cbc408921400e00e007028072940d042600c2140a9003140d080040651000d400042040000d01031800c01c180104000341c0120304d81c40002440210044480058070900100d0b001404420300400c004100c090380000c0c0b280b5800b90798034040310800d041c81402880840d46a034058414041e06401307000c03031401c02900541064a5a02c50300d5a0740c060070300d69046602004080d03102c140440d00c018185a007050750440c1000a040c180c00b0300f0400031840040c0c859001c10006526040200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 967993111 1250 967991861 967991863
    0xd0c02010e0c0307140607081204021e0d260d0501180e030d0f0f0e012901020a17070b041a150915010e060d0204090f0218091510050c 59
    0x245600c10308006000740d1002d40c070009440344040e115900104060580d0001a070769110115545643d01040c03180d1510050a0a1000d00c40100d4049000308054400e003240581035000b40740b0b8100c00204039042543c00360751041344203001400305011481503041b04844600184000d00340c060604000000c041d89880d400c1890b801800c40450f8509161440c019402c510100448049009402c001305948010008034001803112000c0d5070407541ca0308132010b0b21343c6010741205400500340424200540c00030303e905421006030b0100e90380960b0150909000142042004548031b00c00d42000f85e0400b40141c445481b03d40086408407460b83c030700304a80754110401d50100b41c129001580000d00c0744070356000b14640c0d10f030180205200850081e98600640c1c0b1409280308040801340c01c8030380707490b0b40f1055a0040c2d001400f0303a50400d810100840701b550620320a40f85000094801100070002c81c1043c0288580c000d80266203030490090300204503151000448814010790742c8042c1c0e6841e81c11821 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 967994361 1250 967993111 967993121
    0x207090f0e1525050403320d09091d0102120115051608030402220b010306060318021c142a0a2c13060605010c2d06020d0c0201 56
    0x10b144155516403d00159001d51052007462038895660640d8a001d80780099407203004543c00101084004403400380a052408000c1070030314030211401502952011000751120949201003000a140410412812400d500614100c040c0316802007002c92010080300d0aaa011407040c254040d50800104080030000354031000c82291450800d042600c0903030242c00c04000c0c4d40f8054400314010002c0340a555070004a100380c50080800030103a81d592a600388094500c010340180403030729028000461030301900601e030303078404007110000c00b05184d41c1c01c1080440d144406034030000d2010400c81c0000c3d05d110803444070210302d540180075001e0301d420101490b0800b094440348840c01e507007840500751109990f480c241c2d20304000f00b01c811b81e075a00b41303451a00c241d9002c2404448114080c0074182d1041c119040426000d00824008162140e0040d03440c103034180c0008041c0300c07091100c80842032991012000400c00080c3c002285480307038464030b013070b030300302c1507200510940e03070059080780c00e8092041c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 967995611 1250 967994361 967994383
    0x706020c0610030804030807020f092503060e0a09060b0a090b0a0b0418050c3901051b0d0603060c03021c0e030a2a0b0f010f0f0303050702010207090f0e 67
    0x18602c86030441e5035041036401030703202c014612080800e02008554a2000c0003100100142c6032034082d19010342c1d400e241000c07000560007070220001e40360241c1132080c042c0720182c58010000da005a1180c003000710007040d1101099400a80d00e15450742c240d511129064010031030300303102007030f40034100041145000060f8005075240c072007084204a00c0401c95603c00112a800900107040d580f034404942142c804e90801842c0700300cac4025858000c4102004001441a04040070040c00e0f400203003507400c075182a501e20461090542e1450001e08105000784104074800388040b400313a56a40d101c00981e13081301c011300d010a4020450010022164403403136121480c0c4d41c0f092240110340392302d054603481406140410851034001c0701b50104000c0c0b60174030205000340328018001c42c19013030500745400c0940d05500b034800b1580000a00d0801840d21800342d92041202c0e914a03480d41e0707005c0d11143d00c4400100d056018407400080c41e0030b41072258800c5101e14003000f003072041221a04038100042109 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 967996861 1250 967995611 967995631
    0x310090317090114070e0111060709090f15030f0302030c0d0905010f02010c0f030f090c032a033c0804090e03180409140a060b010306051014130503030706020c06 71
    0x100c00a07004a10103006805c4001c60400c607081709400b800486400c2d149103051103540c85444103003c1d000794002d070410704403403171404100120000c01101c03400f5900e191481d02c0c902e2088003c180003103070030a0740c002c2c40c03203219004076407412120868550500503014605400b1900c00c1604100a58000f205204117040e03138402000b40e1080100d01a00041e4040c2c2070b1000c0566582e521460407030380c1d5008007100c0b900600e8942100b5601d15000c044417400c20440341b54000d010841c246910b502130454001d99502c22111442e010344d00910007038000312400c0d88221401c02e81035100e80b01d130318001d59914090256462954a82c209400d0708180e6807881c5a042e2154000c0201c082010800b10302d0100f07900c0c040703a000c6042d140d07034100303042c0c1805c81c5040c20030703e4004c410b203801c00c015455000341c40c0c420003030320107102c001da40c0d0f400c105040603c00311440100d80081c02c4d415018284000030054500040044c48026031078401182c41c54000d180f08444da03541c0010001c442010410605622280c118 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 967998111 1250 967996861 967996871
    0x1c020303040c0e0612030301030f060e060f0a0b06040509090609120a050417011b08010906051e09060118030807060b060721020a14030a140901021b03100903170901 72
    0x1940ba400389401a1180e5402c056464000c07800c1982c07030009261942c1c401a046a489584904100b501e04092441c1240c01c6441d02000400c4013401003142c1d44109860000100309503100351603103001e41024920a40c0c460410000410f80f507a80f0100c40340248002d0b80280240d1800c04540d41c82c020340044a4004000280710054881da8450116400e942040c900c0880d000181022140907211080000400d400c001240c948103a50107035080b03048845c0c6840501c212070f50703002030200c5400c101c43d40c101c3d0b03003c042c465600c1b01d04104600640047c1d06151218404142d494000340b5021583c00840d98007400190004c140045030040c840c3d81502207800500d1301d481c540d0ba07909441d2070641c0000240794280c02c02d120180c000c0c000741101541004540e450301d6075140b101d50310780d0b00c4000c0031404200d401c50114611b100b95802e8404902041c2c004081150309000e40d003610358910007501d54984110724284248030000c2c0109a081c51090b19080340e06808040c6190360400300801d104142d07031400d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 967999361 1250 967998111 967998113
    0x90f04021801141e030411060a09030201030510210b10050918100c030906150b090628030c020d02060907061d10180509090c0603060102031306021c02030304 69
    0xc4580d00090381c4242003641080d4041600c660301030060100c90404103d0310042e040a02042e90000d5115920400c02021005130b10b404004041c020004200c0000c0c3c81034030188010f5000c0d6124580020740003000c08071545e030b101c22005000036006481c5c9910340244481c50100810250328035003001c007002420001c1e40c01c01002c2400c00700000d0540040d015840244000e0344820310004a41a071110307410700c40b116416502a0242a140404440003407908940070341e5841a8406c1100781c8805221031482c041d81c060400031580c215a07040d010001145070802011700e0303040791954010403161000b00701100200070180c100500c0013855425900074604008210704040703400b00950b6060300300321680751042e05110300e0f44e113181c0e50344540140c3c0303d00c8294043d64001902d1000280c2060009002541b10380502c020b030001a1643c0c0101c0d803054188480b0b921b0441c000c1c650141c3d061040780d003003c401d00c0301c4004443d030981c480c0d00540c01c40e000c5001ca18401d0805020300a515000030340c80c6d8241 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 968000611 1250 967999361 967999387
    0xe060c07060908192c10260a200a0c0318030b0406050907050102010b1f020a0b010e0a1404122001110c070807080a0303021e040605090f0402 62
    0x2401400510071956000d0308820808040c041c1c58402e00e003403584a503400312044c07024101c03038243c0100c100248140100f003c0b014249081902c8040c802819080c80105e01a5090700d66000e59031088020039031349012a40c010a9003141d06102c1e8040000104214510080d04000501c0c01e840200012a042019000803504001d031a880f6940c14500004482d03142d040c9840d41540030b410040091201c04107000074810f05810107802590323a0420390740b03619030700e034010380c00c0302c4624600703c0e0420044440060950840d20703545268880c140107031078210881d680c034403200b0307542600203081000c1c5410034000c00e44980c0c0701d43c0d002100828001040b906294440010710960769030100200b0008038103202001d02264a00000741040030001d10031085c0c01d081d0f508083c1c001003060044c0e8800c1010025031601f000864104890541c0c000e0a16004a80c8045004e58020400c4a513040c041024140242c130007400140024805c0341d541c1610784c0b0b0120204842003420a0785180315a005001070b80d40c00c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 968001861 1250 968000611 968000617
    0x11010509030d0e03010b0a08010b011d030a0b1008010e0a1a0f010b07020409052d07290c0d050904140f1909150b1c0c3302100e060c 58
    0x102e103003080010b600c01040042d015081a010340354210058000c0085c0204054000a82400702603e130750128109440c0080c60840003584a00d0745a480074884a01103a02504440d80107070ba500022180c994541c00c0c002c0c299583d00901130500e5204500c2e034000e100c0300340b440007144061514248018103207008285003540042c0650011900300040707440071551580c0c001c40305203a0240a45480b0f030400b80030300450b01c100026202c416541519400b244803c003007228400c0c0d4060318814032110718401c00494601004000c034a111002c02c104c1250402c908100c48012228940d48007a0f50b05503541c140f00945020400c207140d4245024180300208081040960780070140c040c001d00c68100400c000c03800b5003083d89020b061103404d01700c60450f440c65500104171800c0c050340e580f04004d02c000f041c12001034103440040c054400309442030040c0d208203010280031503038a040512100c41c080900c01c401c011002c0500c0007580c80345481700482c01c000d002c1c02000e04a0071018100c64584440c2d2240340d48 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 968003111 1250 968001861 968001883
    0x1150e0f10090f1407081e040209040f05070b0c100c021b01030b06090406030803040302151003030815120f0d03020922180b04020102060a06060f080402010224041101050903 76
    0x540f9200703800300c0d104181e0b0010600b904c45800a0920b400c11200c0506402c1c4280e40000fa40c003002c1d00501002c90390554010300866025140c85070983c1e654a8003114a18800000c9855010303442c00024040069800f030240b41403083e0151000f4441040300004484070890803e0564000b0b5209181c0140c139142a2070a0300e00c2801d01082d40d6240b0341c000b8400384100400c2680c4145010302c04024448280041d610403882602116034480c800d00450034207a1045a62129000b9045818000071384148011a00104404480021060981c002408892000d882c00c030540d803100d140da00f400c0808000d4094030b840e107800c3c1103103080b05480109010b60048424138103400b040394406142d148440c1c1c04600320003404006000e138038402d8034101d407a0b014140ca081c1c0c0140701d001c02090b01e158851081008590144d03c814406411600b02507600100042060781580070b2040b0400b21150a0b01c04807120904100c1200c2480c501840c03d010703516504090681003090600800c0300c183c43c002041c0c00c40c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 968004361 1250 968003111 968003129
    0x11508071805030709090b0108011e0e0a0f060902042406030506120d020a050d05131202010e06130303020708211810050406030b0d02010504050f030c0301150e0f10 72
    0x240e250030854001c0d80c2030380d211903003500c911a4005183c1030f49500500076140307da002c914460741d03503041c01c0b03090300e20312425840420500603c800c1604025440200542000c0c016605640850713240c002c0740140f039000c19135a40d40c95020250441c034241c07046204203c80b07500160784101c900101580b0380c9043e0f005443c141036481012428998610205a800d0401001103030050003003500700a4840c8075040d0201e034a44142401a07103102e0085040e42c034a5103050b00303540005842d00030b9101071144042c0c0140e061100d01c1c0320401403a2104e0000f0f141d50180030101c904401c0c0b1b58503009103081482d40c0304601e160061400141d5400c80034103242960307001d1810094903100d80c096a0004095503000306ca41c0402c03500b010b01d14880d0014054811240f0a88080120b2a915020301c20070582e07a110003800600c08001c05d028620f08138410100101d00a0f0440301c2550003013000c44d0844402c1920041c08186031982000403000442403a90300224a84020b641e508098020011240243c019404070b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 968005611 1250 968004361 968004377
    0x62c0a020a02011805012702010219080d090804050a0e0f040209060102070909030e0f06131a13030c1424160b0709090b06070807020402090301110415030501150807 72
    0x74951003508809091401010942c1c00c81400e40340030703402041410600c03202d02c0e81110f125890b4203001420349080300d4068015021000c155001c074816180342c1c02003241d07060740c1407080700c020191500c1340031031040c82080d02c50303901c1c1e0030102001000750103070f03208600950810040080440080d00141d4000b641500c0d0360a8a4483c800182d0510b203054200360b00392440d001068050503402802c1c00c4203490700b5182d170140d5881340340c03e221182c4550380002c081d103101048104288c4000d0488920100e43c04101d80b405d101041c0d042c000f803c00250301c1a6403814005505020446103d03651110144048580c03c082c40c00c559642d080e08100b00701c0003540ca6002080c0e102c1d030400d0b4901003a0402da40074440480d1460911005426403510780509401d03640307400e0199070300d41046000c540000780c10020321400c103c6540d007000040e500c680c0d01c2582554907800c00004e00c0382c011001d00301416412500c1d0781444510940102100d0050f03014182e241c0410010f03154203500010742d0394000714a0319003018 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 968006861 1250 968005611 968005627
    0x1e310b070f080306040204080d02010f0605090103030815190306050a0f06120b071b0308100503030f1e0c01141801020306010f0c0f0210090305010e0c060f0a170a062c0a02 75
    0x1000f8022523011015600600c5007005500340e040d8001400a0b00c119403c220303650f02c40081c40211242400014042501200440d01034692018190300b1680c1c01040b405003069031001501c050412070303208a480710340720024000d0b006248d0180700d80310091000d080000e0703440c2c00c2855100301c0307405002410812a05001c80c4269110390350203c46a000400d000c040e5a03030500d00140f01e10400c035101200810010350126281c600401220340e19640340301d404c0e041c501101d03402030750140401050031010100b000500568042030080081102c484201144513190200507580f521144e01116802640704008211090307802142d42c1c00200c3c2c00b480c1c001851101c038500844a181d2040c0c02075401b20341070b46070144942c0d00940356403d89200707000034081c0e8100150010354400c00060400c0d030065090008900200d000d50180c4030780252407034481e1860403e2088440c0800b02500d01d2581c442d16446c0522001e203000902c0c45c1c0d074001980700d000e08000948481515500c010b42807a07940303034000035408 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 968008111 1250 968006861 968006869
    0x20102040b1303030813080a0e03150106031410050d0b04020f04052a0301081213030c0602030702040e0c0d1119140906030a03051e310b070f080306 65
    0x900584207450300c4565600081000c5110000036103c00c400003150980020049015403503486641c5900014450804524110a4410004154150350144600e1845800b4000c115000a000b0101500c0010740000758440c0ba05030507600510b03d42d4022512501000030782c840b041500ca68640019410500d80c0b140d00c001010f404008441540c02410b000c140003040c100c0720308052455542440e0f85e0b0010081501d01051808248620750064101c80c00c03c00d03080701e2800082102d5400d030314808119039180e0743c50040000d803a401490050348007081f110114141481034009580c91400141106000b100006030780003d0a400181102e0600400c60680d8541e07004820061450110700c40c4406e44803440c210a240146905610844111021491608003c11906501074156031040e240101c20610010048e444c0340d034561070a2004c00c0030405800e00d600c1600406032221020f41c03021150002201044062074200040d003d1007000300c400003c400c0011444116031018141d070301d95440380001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 968009361 1250 968008111 968008117
    0x6020904090f0c0609140f0f06130611060a14060d0602040801060905190e1e15040b070809030a050d0b060c060f01170102190c110a0602070801050a0e0a12020102 71
    0x1420000d0141d041010440f100b410304040c2d4400303566020b5005e81d203003100c0382c1001d544040780740c0020040c1540032541c28680c00e03085a40b48042c0c900352504040300b203c420f03224625071080000a9000d60014003006c07050050f00c0e040080d40c8414852030f1641645000d50342000b4009602c100c190040301000c20806405580050100703000030403495a482441d100035140403074130111600014946a10104028441c9615824001006100300300229040001e00d0480c404d0340b0038180315600f0300302c0301040350031a52441140f00d00d8040405042071103029100140241113150706803c107002d15240c00341e002c010b460b1b10b56411040820352244141c0440d195100e18a07104001d40581020420359500b00c1420504075403184450700030303c0c065400c0181c200c2c042c6010501c00d02c004c034000c650006100300448040c0c07901034a11741140001010014009030400e0307001c0c0c409a04105810480c9200a1152640c484070040045c800100e400041d10740311004020014080300203c5181c0444c103100b503040e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 968010611 1250 968009361 968009363
    0x10c0507260c0a030807021306050a0f1d042018090f10020304030905090a02132408163002040312022103060f06030f0f1003030c0602090409 62
    0x200d4103410920700d1001031014140701d42203200e209076010300810b800d101c06608212900000500e0410020750700b085010f0140b2260101c2c5240c60390000304044d6030750f5014000400e40d0503222a040e61a103a026101c80c0010091107030341030514810007010480180030034590b4144410350038070f623105100014890000758814840b1403101201006000c000004d81d400c07034045c0b614116040b002c001c450307440c01c1c1d210403200100018041c030020050350910039402c581082c14101c0140c141480c5052141e50180150301c408c0c3c8044090501c80750f40301000d64081c000038110701e00304440d4036001c0c1c800c3c0910342c1004101400c000c0b00405c40403004100d0700401006841c4000ea0400c01e40e00c1000c82d20194010f4001540c22107100c00742d813036089000060404089005070b0350020a01080040040c0c0c1e074000801c0a9000a0088007140e0a65160001103114a0b001070102c211800c00e6030680e1500f08004140000000004a080c408a5081010381d41015031100e40569580c0b950000700307010704400c2d54 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 968011861 1250 968010611 968010629
    0x409050606120a050604140c030d050f070201120e0105070912030203040b0904020c070b0a0f05030601020d0c0302120d0204090c020304050607080c010914010f050a110406050d021201080615010815010c0507 90
    0xa0004006000c0000c0f1f0380c1860b2a402c491091903110101074403511088280404900c040154421410411010b01501801410080c40009d600542d81d426503c50b249525440d954a4081005242c2c0090803e000f806009a00c12007600b0744d950060341c3da1113540624410b110f000f044800e09a81ca90b01152601c5511109031200c495481c100c04040340c000484440125401054150340c0300d20500c10b803441030b00140e00401444a080318203580600d0001e5080d030450041c913107102d0814030500001c00b10075114240044e41c5900e040c101070100e8040813500402c40d00b0822040046964100c10b4440042d00200f00554803200300d0700140c0104401200106926822401000340900641c421154600301c0b400a010b02c1d62080515400c41e4440080e0580c40fa03411700060202901c07500140400701600c140c0140390003100304981c4450fa10990012625502400402200c4185040c1c001a90142800c003100a400c003035001090514030000d4070f0b8100800e03800b0b01028800708004050082c41880707 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 968013111 1250 968011861 968011873
    0x10e0919140a0c020d080f0604060306150303020c090601020a1419110306181207051e0706021009080708031905040b0601090b04030c0b0901120f0507030b0409050606120a05 76
    0x340001c51a1200300e4000c1881807030000e04070851800400d4078001006240d44241103640d4900b41e01c02007180180006810035502d02c1301200040c264428a00c00c0c0c000c8000c0662028a50301d4002d1a04600906540c052510b01c403e1003080d903000200d40c500164480c21a0658484e1040c0080c43d00000542c154280304015030a041880140c2401440803901503060302c0003607076202c103603081d4041c1d00d540c01070352540a1000b80c0000e51110020b440058494002c1d5101010048100b0f5809a20300c2d88103401500001400c121040d0104080c02099040860602221140342c640040c240030b1044058487d040000000303850741b4044c42080840102c50310200400c4c1060300380390005040860b51140420358251000c074020f01d008043d18104e9500500c8111001c1c03d11200c4d900d26001640350303505001200c91501c503001c0040c020407104c11954800001c05160900b0000c00742c0c0c404014490040d031800203154085107000c1031090b40203078182d591910780780d400703980185881c0e0711a4001d03069016003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 968014361 1250 968013111 968013131
    0x30c07090501030c0b13031515030c050316180f060e04152306130b0a030f0c090515090601020c060c03030a050604050f070309020d20130b010e0919 65
    0xd680258180c3c1c0c000d0103002c1c03440d07441d4a9000d0300340c03003000303900610364000080c02c00000306420064080111006000300f58800b072000400807640b01d03500122011544031000340310500341003144000760b5900700c2004880d54a00110040a65106000c0d80091174407640029030010b441c2d0080710040c4410608002c00d0f181508222850300c10205052820750304101d82000a480c0c40c1c8441110a80c00c0f865860268031079000700541c04240250164141da2100081d0450780e0312402e0040c01140281c80d896a0890281b501d0103005105402109140e450031051011440184550340180d00c0145ca00140340e442d1140103030720344140701407002d034071100025001c1c5210001102460051400d21801e0005803076041c100300030b403801118105400b4122400082809100741c0000801c0c40c00a0b005440c80749160310340e990035500700003c120b807080080d002040a414482c1e541c11406071090400c000e01048400000c18440c80484001d1040700d040740072980c8003103007403104914100c050408201c0085d0b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 968015611 1250 968014361 968014379
    0xf010c02090c0a1e08070e0f130e0c061c060603050f06271006090902070803041502070503211003150b040f14040b010f05060f030c0d0603051f1418030c07 68
    0x2c02c4580386c000074005201c9503d14100b0740c201c2c0c812064020b01801211074801c0200008002100741440c2a2180c3c0304409000d40314000140342000e0240030002281030400210015110300b03511410402d4034100801188584908001d13070400000c440d03d0703026503100014080d9000c03c00e0010031410f10f40c40c0500040150109004003158001e407140c0a4099454044d50224040c9400140901c1000c04c0042c00183c3c0d407440000c0e6500f000113005090a1090321400c1c03031030b0484212803041003001b40c4904006c18000b20016480404c0d0003511880e20300715501d004074a580c4150760301d0000c0e22491401c5144c0d0300c94001e0307407165910131020840c079078620f41c1000390580b06413015aa400c2d80036001103106001c0d04400416200041d00b160300d81055402c24900359840141790342c141c28418881e00ca02c0f0405405030100a60154004103850b0501d05000030603080c00d0081d100348645864150481681c441507050b60101700c09000180492303004800609611840110040ca800303101d5000c0b91110f0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 968016861 1250 968015611 968015627
    0x111070c24140a050702030d2118030318080d0b0913020d14010e030d090c050306040305070206030c070209040b0103020901120c0e0903070203101e0e0c1905130b0f010c02090c0a1e 79
    0x22703000d4910b031403130380d214446408aa40d01820349081a50890300040481d02030b4001c00c0c0c0b60401c1160710703900d41c2d01a8540354410b410107440c0704081c03510b800c407044451030150a110f820a44954030391000319030560008400d0081410300622084000f07440034080c00c000e5001c4e0102800300e009a83d51045011148002002c3e0820101d030485020080401c182c100040c1c95071140f07900d03803100c6203810501d800f00501a040100803c90300581045000b0040c0c0f291450140a1441064030901c1941944100804418140c10126040f491003103400302186609200004541d8078950310307406a02c5092800d4114450760720003130342610800d484040c2d41e08007503220150790240301101c130314500308407507038035041e079000c10047d120302c4c0e10507410300419140a90f8455900c2080841d070b8000b41d03603240e0108050058985180355500c0e40e850040081e414001ca040c11440000d1910048081131640002c000080241004000b00800300f00343c82840d0241550075030142c0c869a008211241420004007a11 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 968018111 1250 968016861 968016887
    0x30209030a0b190c0309050f06010806010b1e0a02010f0c0807050f0c0c06070f0314040b040b0a0e150a02060f090604140a061811090f0c07050111070c24140a050702030d 74
    0x1104581c071003e048c0c600403d00c241171710030600141180ea4030b08651071165801c111050060710b4106600d112490505800170881103005400114122605850701c00440c0d811032402403c0c41603503c208003030698004202c4941155002c2c2068448404080b480e00d0b20320804041500601c001031010309100003104142081403282d603c8802c1500c80d802c0c0c01085014a100c1c0d006941810300c01484000a81406440641a0740c6044a820b450580004545c203c04c203582541000b00002c070a02d0180e0b0505c200c40e44000c100c4990f031607604203210302507660b600081024100741010f00e1000e031030072410300000c0e5845811a5090000303e0652a11144c400241c0f04120768220041d03480421609006400500c24685421081015a00e40b001c030304541d0b001e800d084503155030750700020101446440290a00b107011782402e12200c2d09000601e110042c416540f0f0004501e0990b42113400ca03804041c02c50586100012103482d154107030000d458a00640100070b41c0746c01030410240a8541c0900b181c9102 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 968019361 1250 968018111 968018113
    0xe06070c140a0f1e05070e07030c05040f05060f070b010e0f09010e0a0b09070302040e030301052407110a030204020a02011a01050403030c0f0302070b0309100c030209030a0b190c030905 81
    0x180703003001d556985100711034000303001a5400e0034150224045510700640c0701d10401310040800503079070301c3d00c1c00c00b0266082695600b440304284083c040c1c0c1841682065605800d03d2480c15090225440b007101d000c1c4100c0d489030000055001440751503009031801582d0010100c505541c40d2090b2800d5800300f02c1d03040c101a0071107000a0194401405034240c400f0f000805020b090302c26880341e520341d0000800c00354051003804000401a202d80c070411b0a03444210025580701d505001c1048a004900750f0520144106568070400d00c103280800c8074450741c0c6c1728091114174040a80450308568040e0b02c00303580b05c2d00c041009982c141c1c040d0001029018001d4805110310048001900d5a00071400f004c0c0000d05800c2981d0005800420b010301824000c1c01116540f0780ea406141d01e26070b10071210f000f8a9045400030190202081c041e0501c00d1140d4107040d814107265501081e0340e201402005042805d5250104c0c05213100c3e1000e00c01c2000784908188a11703070f44043c01a0250011020441c1c203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 968020611 1250 968019361 968019383
    0xa180b04061403010608060d020102071203051e0c03120a0f021b0706030e030f0306030a1407240f03020306222403110d0c08060f01050108180607120e06070c 69
    0x2c01d00c901c1c0440e410307200144c0b1703401025102c1d1800c0c400b0300d40046804a06603c903c04011801c85401200c8180c0940302e85d036580e03a544e294a00e52111075090740521446d0b42020b108107011480d000c8180c1e00501c4d040c00d00300b2120303620f020a20010f4600703005000303141840020841c50214484490192841240d0106c800300b90340c0d0f04c000c03421a80011401ca4031134100342b150185000e4030f6070056420020060845a640c41c443d200e9080250b9060030040855024130310070010140c3d85e0300c1c5c40d440c101c0c1d41c1c20200c60410084401514090f41341040d001059400400036505070b48044010140783c40c051030350081100c13aa940000240425002d00c40720070020329406800e007600c204907806403680141000b1006071580d050244400c40e40c1c2080b54540f08049010881000401c00507100f8080c0c2d004c401c121307501d000c001404562018040b00e040c2e00000c00c8000ea08a80003c030b0540204007071505108100e8048603020040a0342124907a8a01514062090030380d804605e46122034001c00c20300718 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 968021861 1250 968020611 968020637
    0x31d01020a050c100207030b100302010f0809060f04020d12020706020c0f031b06040305031306080603011826131e060f0e04020c03120f10030b010b0a180b0406 70
    0xa5100540340006000e0307403008580f00524145480c2e044000030385401100e84590b103036903a138001140100d500d06452100450100190f42e48000b02d138142210303d0410720042d090441103940c40720380007455003401503c01d001203800c41d105c1500c40d6000303e0b000040c50152000c40035000b52600498401c1c00010f2046514200c030382c0c82d024080051140004005050503003d5041c1c007424081d042d03805c2c6501c0017050000002240301030004000d56403082440080143c20030f400541181c030090840c3e40260700d824907240f65001c0d500f0807d070341c00d03800c0b0440001010fa40c1e481046c25403003c0b9140b1007159030103d00900400106080b101c142d8480340e107610280c040c10100e1070f512034118451038001503085040c000100e40507581403000c0c410081c3c405031510041c2c010b85c601e1640107400c03c1c140905160108201640001d84c100e40181051800114171851038954400458041c001c4403416500098180e840b11b0040b150500b805498500441d40c00355100d45590940d000703440703040003003944460f04e94 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 968023111 1250 968021861 968021863
    0xd09032d08090d020a2a060206060112180b2809020a0e070210090606050d030203030609010f080c120102040e0f04060509121c0603020319050123180118031d0102 71
    0x82440e0f0902e5009284642c3c41b502d90302c109003e4003000995034204030a4080400705400d8141028180359002880c10313082c0b210004081915075042c051180e0f24100f00c100c940c0d18021056081c40d600071440e80d2064844010780407036101210120000100c3c4c00c80254003e030301a0b0000000103000b11340b516001c558501d01041d880c60225081c41c01600048003610304ca0502c0e500c03a00f9118010000041c1c2c064a640c041a06418005020b07000740c4e00200412540b0300d000c211540c0035101140c4000015454000348070703928007000c10254800d03407041a00c081c00480940c180c5d002404c0d01c0f1441c03901c50820442e64901110182d506132405410034000420440000695845900b2040005803520200447c585252041c0d25400785400e034a80c040000566010402c0742003582c110754111a01c074440d460818211198480c641140754001120403518230b2400070741c294452a8202c0c5480001402190390b40100000701c034040450301400d50b45003e2549c00054100b0f041d490b078803450844800a4016 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 968024361 1250 968023111 968023123
    0x40b0f0d12050d060905090610080303060d0305091905010212070b06010c15050109020a11010b0a050918030301030303150501080402030d03020f0c06011d16050d09032d0809 76
    0x1a40111840d020030000451480c00da680d00041880e003582403250f021440d006552856102104458948042c405080001e029082c0c104200d0326801d9001c9140260b01520303400f00074001d030b100d0a18000e400c414140280200d4607451030040280801080394240c07040c034042a401614014401c2c900d82c11071610042d0203c0306540d8111242861651358000112440142d100701144c1c02440d111001030614041c0c0507a50182c50a58000361b12032080f400c0007070a00e6400a510354241c0c1c18186076080d08d40342c0020040a9034002d4032204482c0c0c1c1c4071702d1040c80f00d11150486a941d480000000000d065040c3c0c45901d1051000717038100031541d542c10045480c003c003543c0107941500612010400280258010f140c0c10b8004401c040c284005130004a0420f18264000804d01210603201e22002030001d0b14181d0103111100d0340759942c03018650041103805040e03620008a82c0e0342d0340e810103140c064854608801403208800e011442d1040c0110341e80d880c0d0340c00d2240850a41000702c1c0c4405c00c04125 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 968025611 1250 968024361 968024389
    0xd05091213030b0402040f020a02210f040b0904090c0b04050a090b01171503070e01181803050f090d140c37050d0503030106140304030e0d11120705040b 67
    0x81c21406400c64841400100c1c000d00200da1150340c0b90844440c40f80580042c05907070515030090080c02d14802c0c4101d807960f40215641c000c0f05810400e07089055148001d690503282041040d61b1110032420100e00109500d110107070601d0813910002403180c0c80100144281c0d81d040d0765026005503075601940c291b81c60100c1310b5002c9549461142d01c43d084190800d0b501c4005603034448030060200e000309080074903d40109404081400060003004920042843c0b81b07086c44200300500101c2c103440f1900b043c40c04000908009002400017085005003055a1a10790020f0890f048640340e03140c002218102c52404403010301905039542110702d00520307503030b0040d21000e41c2c81200a00340e1903071104001c0c1c010004a40690150740200d1240c44120120044a101d1001156a541004c10103803450440c0403002420400030410040000e5000d40c96020412041c0d070780c014425290300d4000c2080c02030300c80c82c2c0c0e0451610140001403070800100e5104039441507408106a9035504148051800d940c2c03c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 968026861 1250 968025611 968025637
    0x150d08040302060706060b36011e090f0608190504031b0f0804080303040507090603020a0b032509090b0a030818011b06050a061d0a0b010c080d050912 66
    0xc03080025007881c2004200d0300784520310000c1c500b80c65241c3c0b88003941115500c80b00e901c454000c0e42c58050b4015800c0759003d441080d194042c01e0091000030320711001c3c0c100c141c10140b5001d503194001c13401030000c0300c041c0504020700244c2036140c80004207000021240710003071303910b11050000340007414850103000e0342e01641d9100c205040c0214205501ca1600c1080320070504810042000c18030480140c40a0103404025550f00e0170a81402d40ca85240ca1b00400b030701d02d00d0300d03c0400042e0b80750300c0e600048500680c2d03199101c3c3d403a1401d001140ca00040404413500a10078004080c903030046550054501201040048100c9041400700f140780600004080d20130401c115905402140810303505580149441030610700200e900000685610b1008c666140c1c071601801071440b414028000601102c01c41c64000d90070400050481c584003030b1001100c0c07a0b40e2061178240364454018034641c0c030307045103060b951801c15803006802001308036446511400340007169841d024070141241c01481003d9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 968028111 1250 968026861 968026867
    0x15130905040b0106230903030702030601030501020d060f180923060603010c0f08040f02061905180f090a05060a120f051b0d120c06091b080c06041a0403020a080303150d08 75
    0x528155542e900120540387d1600c4103100d54401a641003110358041d5200c3c000144e00d8407140b0a500003030340c9a9400c65088400c1007182807001c900740f02d05102c0c00306200310010400180030300340300c2c032241d02001d00d011480d504400e0f4112032102c0022802e01a600a60081000c60403042084908c034200d034102400142d0f4510202d03020800461000d01810700040c031081c40c00d200360b41ca050408401c040b101000c0741d400310b1060656448101404040c0340c058659209070402100020303030041000b080c250181d0395070800314400e5107809d41800d010301081c1d8580c42c104039550801502c44540084112150303c80c041c10711031510b03085000c00520403001b0b00400809901c560312034100c0b0a0b4183c0040c100804078010f400400c00700d010300c080d018016850728200da001c500310406031012940080b0243d174003800441459403030b500221000c03070b10714102c02e06680300180300c1380300103104035031002c1e5002031003810100754034401000840c0074610081700091846122402c1c420103903001e12000d0f24208080c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 968029361 1250 968028111 968028167
    0x70f031427130507020d02010c0e0604050915030123060f03070314030c1902010305060f01050d2007060c111603030e0303090301061509050405060f15130905040b0106 73
    0x501000e90003500001e003108040a00c2e164148101d580483d400c1005174000d540343c3c0c402c141c080c4280740c84040e0525042489210300b4002c264a4410352240e280181c1c005030006403644042c2c0c1030348900d008010000d00010070301c03c141400541d405402407015604080104a640c500b002c202841da0b85c0180103064828a140c89401110300d4480d14900d01d40810007001009140c280000c00c843c076070140b01c00c0400c0ba050b000040071558001c1c04c180c0141824051302100360303081802d948203c5070a420114030581441c0c6500c100d610800f03030340650a00b01041803000c202d0181c00601840705203580f108403100070500310660b2002680081403410350a0502800400d00c5a07041da0074416010f03040701c1c40c14420b64046800c40360154400c00c512030000c0090390002c0c1e44201f00d01c0041030101d405104e5410b1443c0010000032943d2401031040c030202e07284c008840c0c2c1d00001d9422941101000d10b080070b5440010102800e0100d400300c600f1102d4800204003240580124a020401076444600f08460 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 968030611 1250 968029361 968029417
    0x60f1c030c08070b070c0c060503070903120201060f090203010504050903042d080f1507020307050304050d1109160e060a391b08030c030d20070f0314 66
    0x2220090320b098104000301c0d0042410358110358000c04050b52901d41245003401c14502c101c0301500f061042000030000d010017030380d0081540007682d8002e81c08089004030780b801030740100307581c1c1e10113036030050840400104241c450307019504852041e9030510060742e07080d511310380701d105034001d54a02440034100640050401d0384140d1002c1d4210b10408001e64886101c00c2c83c0185c10b543c0088940d001c0356004419142188107146c02500c10b00042d8103120361603640a0700d03030150b406601c1c002c40944800c030041c05011900b02440c1d074805448048241030400b408200644040035280203d100803c802c8150705200d01201d246045d56542c10b100c102554070707074211664603680c052000345109031003002e03207592840b402c20009100b202c101032901100c1595002201c1d5550100401e42c205200403950010080120f5140031508100001c000007510ba178a03080c080307014400706540801041d60410050014403e198140c003e45030b54000f89031000c1c44e0300c090301ca080c071003a04403240c48401c0307020555 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 968031861 1250 968030611 968030627
    0x1a0c0d080c04050a090b030d0206190e011b050408070b0313020f0a03050d03060f120807170c120306040b090108030a030e0c12070501080a060e220515060f1c03 70
    0x74005804a14055461001500c540480d03006200c0443e61129641d00303d2504219903080802c0500142403d40b4085e0607d0301e841c0169002c440c005920f8038441e42c0c0051081d8080d060f02c19141e030120400113400d0302c00034a140c00078081c048291007a0f91000c00c8103404101a64880c42102e51804003c41a40e0701303000103001001607494004101d94400b20001c0c9042c465a4079001540c1d5002502c103140104114044295500c81c00031070b8403400115000c1510b02d81243d61964220411040c03006461940074900c2c072a5600b03900090142032941c42c50395400100a50003034030209da040c021031405204002c0c50710000c1c031840b1030982c010811045011b010b0b400120313a0104500603034016080000c041550783e9000f10000c04242c00002050201d581c11480d8a034100d100d540040040c00c3c100070450304c1c0382c41c02400004521742240b0024240c07104641080e41c080740e1010a450000c40f01c0c03181c0d990341c1601510103900c100001000800e050600002070319102a1402000c0c1c140c0341d8540741034032011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 968033111 1250 968031861 968031871
    0x10b1c03050715020306191802090117100f0605210705040b0f0d06080f1b0609060705010e10020a080a050a0615080105010f080601022e151a0c0d08 65
    0x50501405002c100b12920441400048a83c003598903d00601040a06070002c044482c1e180b030b0f0000107118640d4511012400340d03030b040e1801655007419400585841c09010b08400c04454020108440c0540c80303200c4508076a1000c49801c00383c2e4444800760341e1030160f00448030492031040c4c5c1001940c07801c8441c40d500a00365040140c40d090b1111407101301c07544803018228500a001032680314094003071103000000c0c001c030000780005030851038005407070707080c1e211a05044c12504402010581d44540c21600c1301a0000c040d184d035810185000c5000c3d020134035a2a00602038100c0701c41d92400f2600845203051074031354600f4041c1d80c0e0201810024240607040f505599521600455402003c1e007103a0301046041d00c03248101d40c074000004080c50032005642c004c00000b03034244620359800207504054019001c0350148400d08950208003960040c001c0c8950f6242031a52001c08400ca000224050b507003250b807032188091601840701d090303204240c00c00f00e03070790301c003081c9008103d01c212901a042 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 968034361 1250 968033111 968033117
    0x110c0108100f03060b0901060c03050f0901030b0402030f06030636070504110c0607090e0114011404170c18010e070c050616171b0c0316050c1002010b1c03 68
    0xd44440c2c21503000c0303600b0b030022546140c2d80c0b050b00d4454600010550b004280503c2c2c0016415a159401400307405000c080f40b0444d1804100d40c815680240c006030700320171014000310740b2454814007103103100006946040c001d0003500c010601c3c203490042c0070003c0500000b2040030030140311840804c0302070032824140880c00342410210f50b643d60340c0594803412820315000c0e41c4440d21071041e681004800751440c014030140310010004071540c1c1030582c0c1101c1c0c11000300c00d0300a443c440141c601e0380e1603144140c400040040c010844940e003006140c59002118100c1d480340004605210380d081542d007200031030418000c0100070041c0100689984880c0c0e501d0031494050310b6030b4849103085d2007070700c4407104000202101c0900d2503002c0401c044055840c4c1e014941402d04480c00038400c01200800100e4450002c2c11900840d01001192034600a009501c107400e002410519100c001059419100d940c0c008c030070300002c51050162600d03104000701009102341c2e080c590401c10381d0044d0822818 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 968035611 1250 968034361 968034391
    0xb0a0f11160201020a0c24030b0d110414100f1e14240a110d0f050d0605030f01050105190e06061b0f010b010e120a0f050715020d030b01110c0108 64
    0x80c21b0154240014400421008482a000c41d80c0450051081902d041018074000a500c0300f0303514000300000c03154010410705228010400403601070007038002034082e444542d10621001100181a00040300c5800401c1c108081d04c3d04000c0304083c0d0840a0382c10800007152041c40308042d04592641748002c010624084506422106070100c06000c00b2488030180101c0c0080f1202d4100705c2d8071407441320090240050014a00000d8843d0540c80c2000c410007002255409458020f0303481040a0040181180c2c108944800000e010b0042405100d0140030b82011601740142c0d00000c1034280c0b6860a00e40c42030f5620b140a024458124846406000c018580c101d0000034040c082041e0040301c0b080041442d060b00340c00500fa0885211216000720701100d0b25060040c00410301154a950048080a2011440c100749107440116000780ca032890107120380035403140c0c0018050300c0302d030b101d5141407100380a103200668001c00030f030241200a8000c03c0d18811951710820902d50701800309000504 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 968036861 1250 968035611 968035613
    0x150f0405150301030501060b091008070908070e040618170a030f0203091b060f0a0c060209060c03030106080a05010f0b0a1205011e0807060f1202160b0a0f11160201020a 74
    0x801d500092040800820002005000b80a820b0140c2d101608500240610349200346010030394850307100925a0422001070003060785176101d0000100107124020441d40300c0b68698402000c801c0f0141d80032a01c844c904203450401c01498401c02c0c1031590450000321317104481400d030f10000e5005008032020142d890400c40c42c801d100d0300c00345014110100003041103800000d07184000805082203980709110621090b800b1961400442d030300000c00303123008000c1040354a0320401074004c4100050b8490400308180170015000005141258080c0d914010f06449141c04041125400c0c082c1e45c0b00a080c5110500c59015504001c1095050b0340c81d0040341e010a0b00d103c0b40458000f030304001030500e2514003081540e03440d0a26400a004510301400c4400e141210140c40f1141d01307401e0b8004d1010001998101c100980e0641390409640050601030b0f000368548000704503000c0388d04116061410404400707940441c40f03401c40c00d038031030303094030b81703000da174820703001601502440102e04512911a00e28 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 968038111 1250 968036861 968036869
    0x9010b0901090905010c020115090c11010e0d270303030c050d0903020c15031e0402130e010f270b061306030f05010e06040c0b0f040506131a09150f0405 67
    0x10300a02d5045030000d8041c00e589083e030300b520b81c441813900440e0305113043d2005440f484035445e17086030030401d00012224000c80043c0e031200f45450780e5404c0c5510b030419001c03442c600440d200c0040112680c0d00f6407000c070502d210190f1480d07000103948100e0482d80c800c1c0006400303980040084000b0703042503428a1039404c12042940c1d0f54800860041e04404e011010501b000005001c0c4c140160050505625040c403100b0004468800e114005a40030404102035464000c0c01d0030211500030428450072a2014285003c2c0040700758040d40c0a20f01f10900280c409044034003c0b4000601c0d40c040740c0c543d0349442d20320b50301101800d501ea11040c152070000e400c0d2020320a0400451003521424102d02d19420b29608441070340c000c00301950095410480051300400b041c42c00e0302c43e00b40e00756407140c052004001c4180103e4004d00c3d080302000442039081e151402d40801101c03045100925104607190140c1d0300f0f805044080d41c1c00c9a0f280f200d40d41410244000381501349840600c1e54107041da144009 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 968039361 1250 968038111 968038129
    0xa0b0f07110409020d030c0302070902070206070221030d14060108280e030412020a0f15080a0f180b01081f020706020d060b1c021e03041110171303051209010b 70
    0x102d01284204600c001050b0301403100e12b0003004400411800c010f2180c000c15464072030000c000703200e8180c240c1049900c083c403440341c00f0420b100e201202e80304d40d100e900c58002403610702c15001d140301003040010142d610443c4014480c0340c03424801400032099000d81c2913a0029826582c11051301d40c41c4e0000262020005400108000c440020140040e801032002041d40c6401003012003413214010b110180d0000c0500490440c90301d016402550340e0580300d4000d080800800030400c0c188901d0f6180540c001e004016501d0189007528501e0340d071200300700e545000d10a005103c007480003404240c4a4901d5004d0002203005510140c60800d002c03100404581080e0040c83c016140441d50345200f03000c0c907203070340ca1010244004500d002e0500700c155405042c2c40f810307a030329494008001420000340040c8800c045902501d40c14811007040b07000341c010709564255000c0c0c50101000200e000d60810072401d28680c00d501c0d080c0c07600c50b14100da00c0850b100201416030079034a0704115642c0351510111 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 968040611 1250 968039361 968039363
    0x40f0503191227080d020a050315090f13020d1a100608010e040821180c0d02060901030c020718020a080105010e0f10020a1e020a0b0f07110409020d 65
    0x1c11104052021406003a5442642c8440d0149103002400c1128031124043c0e607003880d122040300001d1940b42d28044c0312a10590080402d81400461802c00d019081006103001364040c0c091590031075880000d001c0101001c0340d183c5015841030002c00c4034418014070381d0b19050f00252294445200e66210840c811858090005400b051744003007128001460030880c02410841c50a5542c83d4907002d1080450359011b0005000070100241101c075503212001031000e0a201c0300c424688614020074500300d9040010300884260040d19454516480d0060045058130760040a050500d50804011001040442c4c4405c095200701c41c00455240075905c6c108040311840e5002613910070f0310540080800380c042e40700398107000400c079010b10f26035941e58034403108070000c0d18031031885050100101d1074440300102c05002c90303141c85079002085039a1450b4810907030090b6640e41840381d0311035448060b8400c4468105110030b044c8008000925128003482031002c00800104210304941c0003c2c05005400030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 968041861 1250 968040611 968040637
    0x606030c060e01050309030414061611010e040b01050d0f180b060a14090601030c262401021005131a09070602010606020a0b09150c07031101090305040905040f0503 72
    0x4100075071544150400c080c08003e107401c509505203442c0040d0f5074000e60081d400301440b14854000d05442e0b030f0054501440c0c680340382c825118103a003485a032208810010318001022004100b40314105030082118510040e503402d841c0552805040307004108018601c142d86868404035092000b01841e05100c007030081d6018804c60030a03008000460105c0d5000101c5031011009950880d5522010281d2204080c20045080c0204200c01c0380d0f05c005410141c2d911070900f45044017020460ba41c40d03881448410701c070080700e401c008440ca490302c81c1084c90a006030700c2000c0c040ea054505810a030b0300101c1d15006515120402d50302c03202e00c40040c0c0c203143e003200c104008003d88440e0400200006054a00080000c5400c0010094403400741c4030340a84404ca007800030422440040066007022003a00c03281e06143d00305510492002c0d4844002a4001859001031340304201040c8503007184550305403034081c64240b5206524000c0c000c01401070b44c03007001d64011600451010b1005041e0040910 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 968043111 1250 968041861 968041883
    0x150a14100e06030712150608060709080c120a03120902060307080412030605011e05120a020703020610120b072105091204030f062705150601050c0d0807020a060603 72
    0x1030401c0210640040110b4031070307400f1050410a40c241401ca80b0301c2d954210040d20020444070301034101603c01548000d1040c882e1704104050294400518426580040d060380e1940710342e4010041c90b00c8007180800d405800200ea0200060b01030400641140850707500458190103640000e01b2130b0308201c1c1c10001181603001040100580c10650030702d9640607041c01c0007220308000000b000300001440c1058031841401d040d01249000b10f040d1426601c200a50003914540380600030040d40041c00101d01521400e0003180750041c070181510300381c0c2c8084000415030007907612100740112000d070424041c407661140c1c44001c0c5e4138400722089601640172001c2610708001003020314000001018104445051006000003940540e01c82d0a180d001000451140d84d051015140710700119004590308440e02402402c010020407030040040c1d0307200c1030b54000d03a40c501c010340b01e602c03c0700121440d980042c90310300291405034032035039003141181c4112005000140d50740b000325112600140e401c07000708 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 968044361 1250 968043111 968043119
    0x903030a0b032407030212011427061509031b090618180c130f060906050d1b170f070504020a12050c070204050403120b03010e150a1410 60
    0x10740101814040305a0041003c80442c01100030361180c1060070b40119810440800d4030300b4440d4040d9940f2081004004100d545e5850200d15004810042a805070306000303c007604111580c500300d0100394074403a2802590780c41104100d50042042c140e00b102c0001400861169181041501048884550310b48903541c00750041000c031a00c0141168818044020482d6403a140480c64541251200101e00718440101c0d01a40c100710444036586c0d001128400202800003854000101000c5e030310500f04a0103440e210040280c440c0e5000d19500034802020300380c00200840d48102d413400031210240122519601c076500c0740100c00b5868051503200f0a2000312800c0c040c404400100000c607011460300068140203810322500d040004160307661a0000b485c20b4000d81c0848401c1503004008001902c0d1500e009403c507181100e5001e0b00c1803030003000c5411420140328031a83c10140100138101c0d20260f0040c0c2c0386141c0020101c1da11541c030f81c45854a03c0301e140e50001d00800502030071104040c18 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 968045611 1250 968044361 968044381
    0x705130b0315030f030a050715140a23360c0f0f090c0a0201020412060c02060f071d041107061b1403160c0507031b0b0414190e090303 59
    0x80c040100d00c41c4d0030000c0c490071800800821588106200d0030300c940c640c0309074100b048001240d980035140e42410309002a107080320b117030002131240c0c4081200700140b00760160307800900502c0d5112500e09031142c50208a8407040c5004414045080900c08100c000200d00e50400000c0c0004c40c0140720707845500070f0159031421010b420701000060701c1c1c565100810600080f00c0a00c0a403450107500000210143d03a00d200b901118007601031070f25000e06425051608000410521201c580140501d002190420a00c40c0c2d80b00c0c042c0e40d90350b80e441d03807226090f500c5684803683d1040d880d070b0099595104202444082e0068543c0b180103010001d4018645840502c16030210b4802c84200524411354641036580c800c10340340c0280011020107002800540709603030301035001d0800741852040342400410030505003500c042007a074040b07503a20226a40e201c0001d55000c0e9000d00c5029078003c0001035014140004480171180010500101c940d9a03460b80b4580b10300140e80100c2250000003c00c03441c0342d9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 968046861 1250 968045611 968045641
    0x14012f030417060c03070c02030a0c0b070b0717070e010314090a03030c0807021b040b0409111e0d06200c0c030c010e010c170d0c110105090c10080705130b03 69
    0x2000c0805402ca61404c030000903010f100c020101341c24058071503184030a64804000d0500f04980c4101900c41c0503842d01001030181c0c0010904903408441103001500f1240300703403000d03074a584004c21107042e03d4640540640b40c150610002e6410103980f19185600d031003211a87c1350040e0500000703418180402e0500038281c41c43d0703800500610100713000340207045600085000ca00c0ca007151100c0c240800410015010f0904030052582c03181c10074010000f44141151188251b410071910f0300c1c400740080890130205021a5001d5a100703404101d480c01080507600701d80d40c106021a101c00003800c58001c02c0060390040c600307001065101801c1d4940900b02081581d01031102421309105000c000300008000300340022000b4404895000080603040c0c6c1d42c1c0075110035035202103003403000a61480c00102003682e200000d203025801c10000c0340c00c0d00390100d03900130708400160004003102044241922500c2d0050802410030504000048500e401260440040c203011000c01c2d649080c800110136142c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 968048111 1250 968046861 968046899
    0x2070b1801060e0c2506020a080a06210c09050f15031219090b0c030a090b0903120304150219121a01030f0e0d03140a0614012f0304 58
    0x20385410010f00044003505a040d900c4242c0c00c040a030b81e000e12450380d200a05101e0380485c600f40401ca5820208030705070300a01209021540d5a55055841034100815500c1381c0c4210060198140031004400c1140703440340c1c140740d005080244c00b03075903500b41400441d070086540313050322a144c071300384000500310850904400608500800342a03141200303040703a500c1400300c441840590119500d030194014400c810007000600c60031a02c5800031b44020340ca981c006060300c800541805000304500c0039020584107650406030050078203400080c103c003180d81c4045c00c19076601500d142000a18442c0b4002081c06a1006070071000e990724046015207400070a107840480c06003486000e442911100b40002d45260f005d280c04a942a1010305200007059100c00102260055030208108140c0541069011407504100710045596000030707030085507041e0180e50b1500259030030b10061384d07125100614a070840c812070600c4200480b260482810b604041d000c030182c0000c5000c1043d00001c1314002c60300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 968049361 1250 968048111 968048113
    0x2a0624030b0f0c0a082511191a22061b02010c020a061e060e07020f1515130509490201020c031204060b0402070201120506040f02070b18 60
    0x3608094143c1609406200f244900f0400c1c62000030b80801c0060b84410700c6030b0010013251a400c140600020130f003a9070000031310414811903030700101814001802d4414950000c90742500c81d600d81c14007521145028091402e81d01401005240c0355a00c11741c4440864030802c0005601c690303084030884413000d04041e00c0705691410b00d5400c01e05801052074a015584980006102e82d07540d0050072400400103283c0c1000c51900502240c419440b44805002c1c468540803600c28140b00d49807a80c0d101c08080b00340a0601031078010a6804150729840c0840140c0200b10b1419001071b140400304441c4100c81c105000e9219140c0c10101c03051060f0f100d080c0000ca01c0e121844070b00072940c56081c2012484941c0751207607603442040040c1d8801c1d0705813240d602600d800e50b941d81e080c440201d41b80402c191025240c1d645000281001441d2078400c840d08103506840c0c070240c0b400c81c08010340040900030406500036460300036540041c90180700038950944600b501c09442d040c003407282108048000001320f0700e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 968050611 1250 968049361 968049391
    0x40602030a0f08150904290a050105060301080a1202030d092001050f0f1b031303050624040c11010c030c0315030f170c010504140d2a0624030b 63
    0x40c601c5413043c8980340c041c2c150b6003030b00d5940f511324105801184194111600700402d0400b1800740c0c2e481c401c60b070300407203104400b48511303602c5504112580c4000e1080b60600e900c05800c800c00109030002c0c12614000900569040001445044082d140401411900d0b40200318070b410441c0344034001005d407450280b13000d07400d084911403500d00900c20050240c881e1040070601a00e40c43d80444400103580e0038600380e81d01c654104240080c0e03140d281c04216001c3c0a00c0000030101c040b20a606489411038003000990440d510301804000c0054000c1c0c0002c0101d10500d8641d603200034095556500b0b07882d87c00280c08542404020b0890700d58800c01040c01580d40c4082003c548002d200001d110741017001c1204d8101491554407062061214110b0294200800c010a00c881002071344030040440045d02c0060303e070080e0440e5007100001c207486402c0407016802c5000107a01c040400094498180050550181c42d4860248c0552648252000d82200810b00401540c0d003100d980080410920b214 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 968051861 1250 968050611 968050621
    0x60f0f09030e12210901090e0f060108060324060f0312030402151204051e2b030f4805070804050909060a0c11060604091403040602030a0f08 62
    0x10890041e81c80852040c400b44a41c51580d40040c001c040303c00c000c00d82540f21380b1644915802c219000b0385409804101e241c8800584011034a180c07510410f40c01054050940e50b00d0b00541c0d41c0000503082540510528601481d48c074100b0f103140c400000310081c4042c5910b00803040080c007031066074215009420000e00845404401802d072604207071b04403102e1706024614007a11825006160013303004448170320070f101c14004081603210ba1400340c0410a103c0c0c1c141c0740205580e9aa220034030780140a041c1100b212841c0814102007140080c0740703004581c0d804c10390002020f0f82c10000c0308407010001901100c00c455a0303824100e103000f03410420b0300c407881482e44180b00d00c003c00f0f040303010074000001004000c00c1011002c03540901001003d00e0803a040820805a4418007141c03090b2a180c034201c000806a40a020202d220703020110060072950f440c3e100380000303800542e40484504510249030702c0407820500c05070025128990065448a40030341c401007000300042ca04006010300075003803003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 968053111 1250 968051861 968051867
    0x906080c090d0f030306140a030f0201110316031d0d0b0106050c030409051501030b0301110d020f090901181109130b0a0305030301060918142d04060f0f0903 69
    0x26840103021900540700e400e00e4001c00c0d220260080c00400801c80340344070b201055003541c4400c2c107443c980b04a031300c40b10520710b081c030100c40e01c43c0c003014249a281e410034600542c407600000034855040b806482c208255600b026140d003070f0900d0101c001c58a4800d860030b400d180000304001201c01216149260300094689855441c010700810081000000b0450b645240804c102c030001c0640300f40c100309070300d8001d4100100070108230310075002074100307242a1a02d00d014000c0108200c40d03001c01500c2e20700e000d40f240d00290721900390a6215002403210400c16079445403824002c0914902c0048004010080c1204845110744c088111040500c2001207035107602d103000364284413482c2d0020b0640740301d1000030400220b0354402045840700200120342107a201500701c044500341440d040d10b00a201880d00240c0d0b42065031024003030044030000303414200d000c00c80b1200f819002d65543c1e06e02c00f22904403030f0781e5074102c8064078402d4643c030a81b16a90190300c1040300042d9a0942080040455a002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 968054361 1250 968053111 968053127
    0x1203070b01030f0804080304090e0d1103370807080717060f0105130603290306220f061a09090c062b0906140c1207031410150906 57
    0x3c1d0080940340001d00401218034220340141c010304046030f4503250b40340b80380c1024000800c149003240c042e14004a00c0c043c01400d0700040d0a03031010145082100803402e1001030301c9024182d000140540100707107110643c148400540c080b21b56180c4c407452603ca000079040e9540034000d42d00f080075803d500505200c1035201e00344c01880c00c4600107410a41000101d8103030044002100d0a400b42c0d5000041a5070540e2040071119006840741d0210450b8034002070b094102108035542680080c800554852007184401315101004064008524641d46803031410260310202100c0f2503699030701c9100101441c00034031550b030004541c22511490280c103200c0e03c8401604810380155808516036509403000b280b4404403031114211401d45262140f0000c003d00030740b03107042c2c91841c90b24209004c802c0503892142e00c24146c40c40440d280054000704818441360040c552820140c1d078491220046066445682c000c540c07159180c444c050400c81440b000c44d85908031a018012015010041c0741d8109400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 968055611 1250 968054361 968054363
    0xb040302010e010519020606131509050a020f07052b0c1101120e0a1713030f0615031407061e052808041b031a1e0907051203070b0103 59
    0x2001030400b4400141c46900445a202240d8600007010707a40b40c80c0d0000b0fa0500c200400c032a034007660064001090101e03100c4005034081440505c0041c0030b03150300c81d00940c7e0840900c0710f00500d0030800c04142c075859001094200c070150410030300e07041c002e8140010354828a04620942100391004003000d40111320400009210900c4005080034580c01016595022444290103000520f080801076484411039a000ca82100e226400c40801034080c2040d01c0c00700e43c1d81c2590000e0141941c40b16610342c030f20000101c6200d034883c041c02c0c400d003c40c0c45030b91000f584281900d0346141c244002483c01c0c495070303400180402800c2c40940c42e00800122824424500e1410015511181032500a0b580080e0f011040740300d24025400c0344030240d120507003070b2086000c4c00112441201030a01c210300c1145d680300141000192542e6000e00c0a040d40a0642042c1e214102e4090302d034002070b0007060880102c50080f0b130764000f414200981d040c400510002c40d0081c4000e10724004840e503d10340c2100040c04 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 968056861 1250 968055611 968055617
    0x30e01091e05041107050a080304172a120406030b0406080106060206061f0806220609020d0c090317090d0f1101090501022d07030c03050c0306100b04030201 69
    0x100151059018a411001421150300340c1e94440c054801003020411082c41590300851600c44403201203040d0b081504c401030390140181815080130349030310405400140098400f24219518050303030100f0708004254941298144016444040020342c6920305e41c0320303440360103806c102144c240400701101103038103407010303800c0010f00c840c0d0500102d00107198a41040b00e00f50700c1c100020940d81d40010744640315080c122032000406140100e259080ca10b081c14903004982c0041c003160b07132131504564010f4955124812111161081c800740c20030b80c0e0702984451021f41d400103a03c01403034500e024002d00310755541000d0b1044e6140d66141000701c092101c04000f101c4020175400c54660710801c440d00d029811942a012801480c200381ba900e5081c0c08510b8003240c1252400900c5500214492080700711001075418484082c024041c403150440300c005601c1e004119020001401c048d110502a40c010780041030310640d1401854030b041409010240c11440010042100700051021038059070390a103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 968058111 1250 968056861 968056877
    0x3090c011d09010306090b060604080d031109090f0420010203070f0201110a060509070609080c0f040e0a05010603050d030506130b031501080c0102010c0f020703060b0604050d08220f0303 82
    0x2010110300015807044603400710090340000240256a0481014603011758a1140107072110b904001041c46284140c40040d04041402c941050007980808581c41981400a1401c0c0c800000504409401c03200850b070701800d0801d200511000780c0c242d801d545156a0000200e241200010303559004001001380581d560400240840e4892000f0050803500c00040b01c90102c69450702c08041c00044a011006214401c0001145031203440410100c2d20070602504030325440c034090081020b4110112504a501c403080c40c02448410000e548080c0c0c0584000182a8110700c1c00d01e040000c0d074a006020503040070b050000c05d5495500500d0300801c00e183c00100d8200c03210201e4207080f003a0311010b00314400b000000444050100b5120710710003090780200100d40b40c0007815a002d44601c2a01380041c1d00600b0306100013080d551002c2d07003420f4000d107083e003816524000112008540701c3d007100c41000102e203e1859680da60042c4191001003010a240f56091444010f070004191002404001600c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 968059361 1250 968058111 968058137
    0xa121b05181305030a0507050c0f092a0a0309020901050a030302030301181103010303030219170112050c1e0a0e060102060408090f13051914070f110a240203090c01 72
    0x10140d8030001503401070580751154040b1780098850b07009400240c4103801049200c10852508d01c3c584841040c006049aa2a4031103400c90041403040e0508640702450f0700c0e0700480107400f0b0002600283c25542c3d00415041220f1050003034601c0181c0c44a40105203140c014000240c02100b628107403070480c04e4050404020004540152401c10b000e2081d036080007002005041c3e00d6001408a044110401c1c0c0c00c03c90781150072031f100388a00b2042d0450040200051004403400c1740c4008800340100708032003001c10b241000801e150400e090000302ca501c50b44001c00d080c07c200c072583c0000c1c000400030103120f1a110001035281d0701700410040c8003120005280d091640c5007410f501c10301c44080d01b142c208108050a080040205030745000c4c0007104103600450005a500030000642041d4500c00e4040e12686000d4805100b01c00c4001c050003081070303071110302132070400080c41118000c003144010003410721815080c2e10071060182c2c07101801041001200d51000a8100d1000004e2078200902508 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 968060611 1250 968059361 968059381
    0x18010f080f07030f030c1205090111030a0c02120304081f05060102190204093201050c0414060307020a08130e06061206120715030b10020c01080106050d02090a121b0518 74
    0x2000001820040607c01d0703551640d52000290188000030f03201c180c5c2c000303d085030306540c0380a480d0044000485419030341c0c00604042140842011820041f07030300b4507840d00851410218103605050700303803c4064182c1100303140ba004194010328203001929144092551240140c074810780040e003e0b98503071484104201c9016210812048000d40d43d030569090002c070031310411203603c040c903015800c0170041041601d20b00304072422120140c02001c001c41e08481840500c1d0801480401540034035080080403410300b400800c00b6000340c020b28162903051a032006c0d41c0d44c0001d000e083c0624028000d105520945401541c0c01c8042150000c0304d40c41c168480524000ca103410480c1b05a0540701109007198040d004950440c10444800d00c0214000070304030790f10354121b0f0001d40065140c80042007002c0c020740c000d00045025203400351a004183d004140b654105a00111480f2000300207001400380014007140360515204031001c0807071030b0400084084010040031910700b92000d010544001d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 968061861 1250 968060611 968060627
    0x1b19080f01180804210b01080307120e030a260316110d210603060c02070e0c0309032b1e0c0e130f0b040e010b09180712060b18010f080f07030f03 64
    0x171b48001044182d60f181e0420a449800800c811a083d004060201c1d406c280a0428141e082401500600c04486280c85072a161340351080c010b0802c6521415004441055800451040c542e542005041e29403500d00104030034444941090f44e60000781103282b1080d4418440341e0004600e10301c4210210300c0091040080c100e82e400140200c0c54000c14141954000c43c4000c202c0300030f40c0a040c1641c0d82d50307a40520501c811100c40c24036400030000030300045007803401100701c030204400e89072141c14450350103401c44131050500090400c01e41c4130150800082d010b401c1c0e4250180c43c000d00200309020200303640600d215003c0c1c1181d500d40348d912143c0c400b2036120301c141da03100a0003400107050401d42d0500074040004c0c240c0c001c2c40d132070001800c61908065403d220b10300c0407004144d16032504541e40c0c10540a80021034410751550701148256840902d0410010701c603680c0c0d0803a0794507101460074001303119444803140e41c00c95840c01c41c00078004501d4200b1a80c2180e40d10056044a15046a07655 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 968063111 1250 968061861 968061863
    0x7051803010b0d061509020705030910021204060302070c051905060a0329030d0807050d1e0c0e040e0a03091214030a03020706050a0204081b19080f0118080421 70
    0x403c1514184003468000111401c13158400407034150302c9450300d00580c031036100080c145510800c65450315040c40d42400c49060810b10564034807010040c001803950340594003410001740c001ca103c00a20242450280007003030200c644032881403400d01000c1e85040ca0344521032107400041b403204146402274008041005d00211100035180104850000c1e1400160225000f8490280701c0e80c0480c2c042e142c0e56000c0d0b40c40d40c03078031400c0c45003120400000c0c0c81c0030f0312004081502040000101e1940d405911380b1a602d90325502203941d41d40041c0070846280300300f01c0c0e00e10b03070018401c80d0200350070080034402da170304540c6c55440341440d078249040c081641c000d584106200008030030319200d038180e01404ad824801c00051090f500c81d0084041a80118021007816410000d041c0d4140ca0300c19921a00c451800741142c0c1e070b8401007055550135030703a05a0124042d5000940409d00781c001c00c0c840c89400075080c1d1030810107039000ba150040c043c0985d009035040750418541003282c20707101c1c160080100b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 968064361 1250 968063111 968063119
    0x80a150209060a170a020a170604060b0a05071202030316120605030a0b01030c0f0e0601030b12010f1a0405040309120c03050102210a050f06010e0f0406031a0f07051803010b 76
    0x5140d00e0340f4011320703607480000d00c10a0000d041c0b0108003001418001c490f0440c03002e5841095000300802254030700000900900c2c0c1c41a03840800091041842000d0280c40c40580c540a0b1039903e5418800805903040d04c0b008215003003041000202e00100d01c5c0e800541c0458034141003500d040301c2468000340300680101354035100300c00082e41044071012149040e28810718800c0741259440803010300001c15070040c6504002d000001500c603521a50106030a2040140900c02040c100741c1c1d060700f100c800303100e54460242c8412461814407528884135203640307015070701000a880c058500810f1410180181c00100d201c1d010300805000d61006040d01031074000000b1990781385043c4448015507074000c082070301c00e42c0c00030006120f111984a5144076180340082030fa410b0380e0309801103e10000d200c40703641c1e0040c240c041c09110b64480b4442c00703024501c243c40c1e0b200084840300000307000d0340005081c40312402070003003041565603100c1c007960015800099182c940c403191000181c003525031070131020f0300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 968065611 1250 968064361 968064367
    0xb160303090b0a020a140a1205220b0907210201110a0804080601050a05011715060403060f0e0f0d0215040204090503120117010209150c161706010f080a15020906 71
    0x11200b820340c024050404c1d2600c07446c0b04494801041038443c0078880440012645462000003500031a401442e88040100701c0509184400e88100051460360207040e90b600003600108201c1180c104110006007000d440900084242052012402801180b00904115002e03185034010740003088040940ba6110781e03159180c64031030301180da86240c00d2040c40e102d4806c1810001d21075015108140c2c40140640350b401d170380d6070b40103601c240c500e04954029410110400000003c51030b90712a10580b44400d80000c5407066098011514000e02080300390000c0d0007101c1c2c02120310350001954040038034403d086604075900e0f400014020488504003412a000011b0702d1003c01151202d068103a41010b441c1d0130204070500c4095080303001e0741c0c0000f6000905041d072483c0c401035880107801194444001c48080d1603804404c4200107103294801c91032040200701030030140344107002850140144000d43c0002c10b18155171641d454a0100000e030202d22329050210400c03080d034048910340e04c03002d050155 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 968066861 1250 968065611 968065621
    0x17070b060607050304170604060b0109080607110705191509083301060c050f01062909060f03011a0304082a011a03120c120c0106030f080c060702070b160303090b 71
    0x144036241248c00700d80d90382c0b5101e450641503015110b0641561100f500030006541c0e811000d03101301c3c0e410b14022086104030440054580c0d03038200c1c4142c240b00d44545c610300c074924201140101180c0c2400c1e0605126000030b0a1140003800181c0ca42903601c0000e0104050a900e03003404090706041c030085450300d5285c0008136049800040c1021501d01c01c008132192100e81d000110300f2103115000d0200b4050950ba0302c0840210804903000c100b80d002040c0515000150000601e1359011240a214146002c001008081d241540c0c0c4425100031801451a6180582d5041c0b1603220b8903400302c42603102800798110140e80c100b00607000313502c140000c000005054103440b0341040e540c00c25a11a03c58005441f40308600d000658401140c51002400603140340c1c0c12102d0160005201c8404a42d40c03140000089030f60020a03291080c028020183d440380002134090a10300010288000e540c080030082241e036140704100c03011802d10494890b40003515150480c040c03c1d819502a0038096206e05010b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 968068111 1250 968066861 968066863
    0x9060204120210020f1905030c0a1a0112110907050903010603110f040603120c02130501090606110d080402131404060c0e0d030e040c1b03020a17070b06060705030417 73
    0x81d2206008450b8108142d8034030300c040f42c1d00c08148041c1c220350380080205041e210f0340481c4098070306120300d09aa00f009006400c0e513103080c11210094540c1d07904418135100948500c1030320b60240c02000c86a010300c030020b81f14803030030140260302d0718001c500c213100080b2032600c41d0b07050320342c4184001e00038013055a0701d040035844440c205400c5840ba11300004550024070f02032181c2c20860342d00000b0905103000100041e21100ca480105a82080410000040c02000c80c850039001c1c0101070307000602c06007130070002050741203604042c110b03903070048007021000d07a00031101541c042e5048070b10036901d01c2410342c250003504030038a01044030075508040c80100f00d21a044103825180e6035840c0e1004440701403c1161004042d00050045441c1c168068024101178020042a01803802c20400b024024908074180d404120801d0b030058200d0515082002194010490030081118025083c5003854403402015940504075038400c00300021018100030b401d1003a42c2c010800505524020704040500d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 968069361 1250 968068111 968068139
    0x10c02060a0207020916030e0304030506040c0501082203110a08031b0301051806031504120809030408070909020d0b0f040b01050603040f02040f0e03031602010e0a0203120d09060204 80
    0x10094095000016032002052080e41c01040e001803482c0d01c644c40d8268080c1102401c1c40d0003104060300c81700c4252031035000b040280001c5108100a00081c505402c0100e484011500f01904218076030003803003c4504601c2c5d515444050309400c21002d11218502034031919801890900315008001242090011080246101e00412680c10549a080e811201e000f88024015184c0c803c50440300082581c003491040796215401400b16418180d2041544541c10700c21241203c60001507180c24202d03c0e4004940c0784c003c11b0450086040a0500350143d4075040e00340901003420355142125015942c0303507030741c11484c25003041c950502400c0c401040344515200310b0741541c0c0aa882c40000825050420807244203941015000240084550030000503000058640031890307100c8018041b0b01a06000550080c01480e50481103601c142e0320113030030348a200c04a4841a00310401980150306c01040020404000c203800c265181e0031003011000400d42a2409042203101007008600821f000c006 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 968070611 1250 968069361 968069381
    0x6030204050415031205160605191407020d05070512030a1506021609020d0e0f010b010e0f030307030f12180b0f06130b0604030206031f150c0b100305030c01 69
    0xc1840a074041c20040260f00400c4e1000808010400c0c0140c0394031803003840608072401180840f40290001a1104802e8510176545414900381140050201039980e2040e000d43c0700e50ba0b2070312101450046006500c81d4034564204051007000144007080020900000c0c98000310010065128181800d03084007c009882e55825410030f0003201184a0340001009410143c801440c6103016042140c114042e4004020034490243c8407818070584640902120080311002c0340006010052600010060401501568011000c003070079036545403404003c030b4005c541c060038070f035000c201c000804031040164140444580c92078042d605281004000c0500c00103406218410751030740360040c15172029074060328186d0307020b80035203200c8503603100580042d0038091008040908040d0f403500860541d070b0045844220220316495201c0c001e180c00300c032000182c540c100c50500340c03040e003040242110340800c0c0003401450511000500c071000491900005c2c5901c481a45c0d207a5203118691406003080d01a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 968071861 1250 968070611 968070619
    0x500304050106032603152d040f1e0c05120f0403200604021306050a0603090605011410111207061a030609070b0313080f04060e09060603150d05070603020405 69
    0x140040d410f1030f0428040c5802411489403440d2944000c030107480d00b40c0100c0580010080310007547c100d0f2107200002ca00f000101800302112240d400304000c0300c0d5034181200b46241f0384404240389024040340008200160f5070001a40306000005a4050040500b0310002d1004582080100d501e9001c02c14041c07071007a168401c0c80c04010700c250000702c0c0d02003201a21a44040009805031a26500c5008251507a92000410301d4440011900521480d0080400f280e2181070240400c03005115181c0101500401860444105400514010920410300c0e04000103200100340300101400b102203491044000d407540c0d0241b0b4a00003000d08202403002d9006050304104020500b400b00e071f09445556884c3c0030302510b40c03c0100e1440a130b003000e4180300003450110743c0c0070000340c46030005128802d1000080364445142c41e10003054544c14000480c0600e541c0c0d4240540c030346400007074a801ca800c11003140032b00040c003404550150003183d030103850b921802c0d20002d00e080e016030040c410784c0d209407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 968073111 1250 968071861 968071883
    0x90204060212090a080d021c050301050f0d0c03150e0f0c0d0f1a07080a0e060405030318030d0c210b13021b0604060b010e031204140d08130650030405010603 69
    0x20002e0f076042c0400d20039180c102d80110301e3710800e840e120754002800c620540341c030485261a5245ca105070545e900c1a1000315940720141a600e84003000f08403540b105035001892410b01e540c000c07a10b512144400100100c81c1d07000380e501002401150301481c84c04008403100c9a142405000f071034513200342d4140e51035a18080405607a06000310740903110740d8020006618503152030000840c1807492803405440743c0018042c5510704c40c0729005040d6280d00c550350389007181d00c2c0c07012000004c0340c14207046c60326580340c80208499a10343d542d0340c030303c030028110005880300d2a40490700303603a0240ca02002d109002d0b00e000c01c000c01c01ca5038081d481070b00003039840410945982c02816512080b1f03800d034500420b400d100170405600d500b0a220171684002d481a00c2151542d0b51700f8400c0c0c1c220f4030860300b06d00b09903042400074903401382e100c0600ba0342030010844840c402c001d8200d440048d008540781071502c0e41c4290b1040055400ca01c0354500500784080d076580c50203041c824001c10035400110b400781001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 968074361 1250 968073111 968073163
    0x2304170903121813090b010317091e090709060903020415030b04141606080406090611030a0207050105060a030f14030f0c16060f091211091906090204060212090a080d02 74
    0x510817600f60a622455482d82c41e400c41e214168001249800b16113913610804c07580394541c03100c50040c21843c4103a1000808100c201041040c56080101000304001c030400f01040403c0d8002100b5080726019500007494140a40f140c0114504030781014240120040a001c20401e0317060300e041000d641c04023a110500010071040e907400007140704100018400304003280104902c0d0340300048441c807440340000e45240e41c5542580c960801c6545a4540d0b5020448109222081c012542c0c40f407030032508520f515041d552005605a00841c0140441d5207410403010901e000700101d0300d440031954000c42c1c44a080d014100d40c1c401900c80c654000080074000019820300956141d40c6d8950a500d401c8901c40c20041350a282d41941882650092820030100300c030b41e190108268051070103000b40500c41c1c00007691900c1a16655446840d500340f0400c810010190701041c2441e00711000c076803542da20141c0000107440040580c102c0b034028056a080d0b00601074001500d9114180d0092180d82440c0b45 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 968075611 1250 968074361 968074399
    0x1305071a04090b1201050c0a020d090b0a032f040602070e0105010923100806091e0a1a0312121305030d05090f010f23041709031218 58
    0x200d2501500442040c4820b10814206403c09110302c0c00c00b5090102038201c03429240d0070f552060345e141010350070010301d82802d0b41d4103205221008101e070030100612854100984001c2c400c00b0003010405030346002a50742d601391240402c481d0300c0d0085101c840ca0b00c0c501e8050000c0e03885481200302601c90020000b0385800d1507000103048030816164400010300e01000704880d0746031031502551002182100b914036a0f070361040c0914490326551644582d1502e40180829100d001e4032440290034040e0541040395211203416030712598031a4007040ca540c0c220103507140c217904120616858010503016004070311800024000d0821504451041d6450f05070b010805120804800303000c68004005d12a81d450741600120380040e198812100c0b0080b0b01280142100d6901c4480b5020300c0e254140c05440d08112180070a481c0c404034540003003400c0603031b07510512461a00d0354803542c65000c1280c0e801d595042c003550044280d0002440c1da038000110000c03074042000740400c1d10840c10290700f81d080c921 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 968076861 1250 968075611 968075639
    0x306192114010e03130914010311063a020c060408090d0b010b030a060b070c1203090b0c07030c0501020f071e050a060f120e0a020112020d06090f0509032701020312130507 75
    0x1e92210f03600916421518ac8003d082040600c40f90017010402107980c4661060701c0090a144080c0c14034a00c000c00740c40135030f80b800da00c22807003024980107010604020001051050f00507912600c941c1d0341d07168000200d03c1441d441d80c00980b034080035000000d070ba90110401540300300324100c030030800ca0b6103d207600784460180c1d980140160309242028800b81012007214500306000e030400d585819901d1541c2a503036448440d2050158000782801c108111019030314a015100c24005002e00341c061040407680e82c00580300340300e4003034500700c007804517480c061070b9210103030501500901c5e0b017035251403018140703140d00780d044000641c02d04031252800c0050700c508800b0185180c058a50510150011507116503028910650950b0070071945401c440319200314001071607040d4000c202c1c0c04e4940316600032560001c141f140e65401c01c10019201e00184491a0425601054100400d10047e00100e141d40600d00c001c40c241e01d441e0b02400b240740c20703c28155081910604c1100d540c951180d4103114141 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 968078111 1250 968076861 968076881
    0xd02030c180f22062a0c020112021e03190e0304031704180c180f030201180b1c0b0d030801032f0f040e01110306192114010e031309 58
    0x700e0b5000042850300110f0f540070000c1c4030b824180c1017902803095a40d410381260000700d40d150f4004421540c1054000c400f161150800318200140210030301d103400c0609003015001c002c00000928511502403440016540c9034204104402500802075034981c4140410340300060490400c0e080304030b8070300c102da083d10014003506400303000303001c03071a4003602180030310605102c4c11446596503600c501044200030881c4240c1070b9840b81c5035000140645c400c400060f07c0030200b166003801020000c0c0222014621030b1084902d0b1800d95507240001482002c2e00e1580c0913800d82c80000c141340c2e10004140c160387c0224440211654200100390910007041c00b203e03d2008800104200d514012090010620018101040c410040481d80c1e08540c0580b480078404540031040c050346080a4006290240e40900040c02060501e4035141c55015040c55003040341c4400300c282c0c0104512655241d0f40020000d00900c80f50865119081d00c3e508841401800400e2050000802c00c8030b40c06424054 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 968079361 1250 968078111 968078161
    0x20d021204140a230a0510060906060e242701030c03021603140705060901140117070e060d02030303071d18040b13080f090102101a0d02030c180f 64
    0x1440c24400c66030000c2e58011203504c2c06004414080380070903018810b0014580c503012002a02c9801d005c03480c03084070303080d40285c410031496203064012512204a1a1700d80390201d400d000d083d101640400e8100c0c03048410001e000c00c104c5240c60070722981420507542c03546098a0601130050354a004804a0094461b240695051800310701c0c04a4010b9411790b15207990303820581c0c41d009103600c1d500d01d861030580d60740b0641c1e95954a080aa0030306014001e001d410300c0c20204100704903207510165246540d0281ca0f08039803034100030a50554034914012141075002c1c055988a10384540003a1141103a40050808810440b4521134645406c41120031030300e04c0740d003c20365280c5032a141c5045240700201031911400d42a200382e070215120324042c052100c101000d6941e0f40444200080c20070300800c0d40c80b0b882508200b0000c1d2024548848860410400e8402c5140c00c0c1c00c50000915103136098002076040b400b00756200d0781241c400381802d1f20424801e040f4043c20340703a007000512410302550388080c003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 968080611 1250 968079361 968079383
    0x92108040b060105040b0c030c0105150102100e010f090620030903121e090a032601090504030903021201060f05190b0a02010b030d081609050906100201020d021204140a 74
    0x180110740c85581142d010304d001800d154583c0c80c1001a43c3c090b01015080d54408188140703030040c00d018490b801aa10a002c076120f038400300020350707142c19180207585956181d240317042d0110402d5000024210584006002109050a000005000c085200038032032000b05080c070524802c0200b202d000c2c205e400025460070507602c0d800c2041c6e07100038014a0034181000c0401d079058040783c941d24056030304600038200c107440e60710300601124400b00c040c0e007052290b0483c8c07407a401e5034101e01a044811140003c500c0b90f4840c50110b9041d0842d800c001e43c8101c01c0d1180220004e01540500d0907690701030000c40c085034130b5104002015000d039030000c5026090303003400e00c160b001210107010103030381720700000c210700034518002424411240201c000140c1c10801700501d511f502840e1204003c402e041000b82d003410880442c009450060010380510b98071a8027002c500d1007541152146941a24110b4035a02000c030118010304059605603075007842222503410b6900e0100e102a00720781d0100c10012 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 968081861 1250 968080611 968080613
    0x3030c05010c0207050303160204060b07060501082a1c0b040b1b0f030604200d020304060c0309230a0c0f05010f0504140d0215070506070206091b15040f060309210804 73
    0x230005288134220b0b0019103500700015480d090f10f010701240752064102040640c10221514a01101e0760011b0700410440742c0c038080f0324a410070004004420589020518081d41040c1520008000c0c1e401444115080100820300142c206500d011b50b41209480810a0b8186092035040c002d26420010301001080460743c0c500d06a0310440e1882c60110b5071142c415a140143c64064003c150726203109500081008100121403007a00c1201c01141810420307100c680e01c820b82811490140c042c06407601d5501d000b02800200800d088072a0300440740d11106032a640000d60000482c85103e000c10941500440700a01a40c15113043e40c2c210004100029051010850310940090060b6045100c002c88800c0c0b040d00c4070002d08101d07001300700504090910010003843d002009000b0030f0180c202d80c424140c01e07aa686500441c15808440700c00503441105c1032901c4a12980e800001036804800b070028116800d508070701c0d241c1c1e000320001c034071860b140c000010b8111008a04c8100041c603501c0020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 968083111 1250 968081861 968081887
    0x41e0501180e240a0312080606070b1602030c03040f03151b2d210e1002030402060405042a03020a050a12091e150b0f09180703030c05010c0207050303 66
    0x70f100a03000f90340c90620310300d800c2d01140601d801a00183c3e00c180c128107034000825000b040644c0c020000365030141c50000c182c2c580c006c800e00c020701180c0c2c1d0b81c2c1001c3c03560210b09100308280c0c3c04890700d040c1541d80c1c0729950b0032500762800b0b451008480f00d511991141c000303020244079601900e0861050446462440700d801c0b500c400f51403501c0c0c2c0303540d40119000480522410101d94070707001c0c10303100e800040450200950b50b420740e40b010140d0b02810101e640868580114449241840000c0c001d600e03620355200103a154002c80d000329401c103103403054164082d42e81807481800c0545110340b43c100a0b0030840210168805d040c6140c0200300100258a803041c0b10f003d92410608003c5400901b4946542e16041d00c115540e640c501a03c0b42c250f030080c02d001074961405035003200ca10f4100700d2104143c0c0482d0b035641550700714511810003103000805a40502250030032810002e0305803804e1613103138600600404c048040c15241580b034031003a10403980c0005010400d03900020002c2d41444191b005030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 968084361 1250 968083111 968083141
    0x30828090c0803070f0212070e0408030106110c06190c0807050604170c0703030c0303021e03180f0d050c0a0b0103060f05010e040c0506212e29041e0501180e 69
    0x6200c00348202d08c80000c800c200343c500240150300c2058030b04d40d00d501d0400002c0c00101105210740355608191a0640316655482c100c0d100403803214440ba401d0100310f4030640700c00b4001900030317100380384c0021210108040400c0d2a8400e0344606804030304103103c4c4400070158014049900d039a0b84c0001e01c1130010078065140042101c0c880c1c500540781a407031448104410000d506101c81c0d040012050155030944211014509024880106a152030b0f4080359955000403181c0c2c00309001c800500121965418040c0700c034103680207454403945517580c1c40d000000340404d03000174000a1400f4000318140d110b540006016030303085015402118204010846d1690000c1d1203240605100481c0c0702907401001d0182d40304c0c4031541d1341e1440000c808150058541c2010503504a00c148500c1c0c14080c49103030359000310242d60a440081c8000c0b200060214803480746070010403422000d0070703e010340300200e400014140d440a995001507148845542200303201140180038030701c030021000034080f00001c024 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 968085611 1250 968084361 968084389
    0x1b030103030e1219030905060a02031b011d0a0b060906010e280609050a080606090a020a0306050604031407060306180207020d0b01061d0a12030828090c0803070f02 72
    0x660b0400d5080707505803e00e03203130001103c080b00300f01c0409100b06040d0812000002030400b0341e40d861503c185030b00c00a44078410144251f8841303d884081c0040c8907800d51045002240261001d091102c10140b125503840d940340c0c08481113142070000076801d091406001d809500c040e141d8070003800d44682004034294203000c000030049024003008001c0c0229909140c01440d2a4440c40c0e40c0c40d003440b0a20080d03048941004009900180600c00c40b5107403140304551004074a600141c131403036462803c502505896104590004001c0380c040103001841810114500c0a502103038900345e5a0320003039055034910321442c0c6110344585a84209004560000c01400d80300909c412196201503031005030100080c0c00c0700002035a05442c040020341281405c200408085620080301ea24004c0303034840701401c02d640101005410700104580034017401c0ca03046c4503c0c1c2c0c80383d41502d29070324242c0c3c00010000c240c3c0079110040800c00000c0c68510120403103841d03d40081c000c1c030036408070741c0030b02c0017032264210 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 968086861 1250 968085611 968085619
    0xe0f04030c0b190e06040f0206030903120f06010e030703030807111c050c060a060b0301060f0219140c0406030c0b0313150c17091e120d0e01051b030103030e 69
    0x21030300003545082c0000d100c0d002041d03000502008544004040b03034006545120980e10150030301001c60320700b00044401c5a8101c0380913a40b5626140d07803d0660280c41c0705840d1501d080020b005040c1c0d040200d05210b2202a030f04c00b020380d013481080568480c05c40c030024002c130355000040b400e417a00c0303110a0401c03404003030300f25040300109070502c1d96881030760002d2100054001c1100e881c404418031a25030041018582131000c0c0e4102101078400f40700c1840740e80c0c00c1c0b1038411850040c042c02030028150200c4003280c1201a19a10308280441c1c900044c1451924000c0c6641c1c81414a0700b80f1488080e0307900407a03099807050602c0240c00301d603403020301081c600e00155080c52000580f00c080ca10402031082c00003142d918200040036180c2e01e1303031900705500803d100040010450000900e103000a003051500141c0c0b1180e40701c0c090504182c09050151a140001c0b074030b201c200079411080b408601400200310310340d20800100c081409440301242c218004000400200384950907000c20240014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 968088111 1250 968086861 968086877
    0x40b090102034b0106300c20330a020f1204061b0504050d030c060e030406170f04020a060509041d010b12030307052a010207200a0e0f0403 61
    0xc5041004610f070044810410794440043c8441c4d64060502240c0c4000710003409100c2091441c2d10f4903121070100c259030701a907030384020844148500d01c0d6211010110a995240382c029501660300d40d002000050140380444d00280c102550400300c87d0100c540315401d83c2820713180e03410184007039802958181c1082c02c0c00e0183c08610b81c4803c0c03400707000305d03c02c0c00002000108103400ca1154446084080c042c0030051000704215100e4110b10303080f00f42d243c03078440c1d411041440c1140042008020385442480045404030318503070065000d03000524640c000344c406030744a201032440040300f290025081001c3c04001c11500303010350054503010340b0085c00801d0708440d841e1507500c01403929400444583d182d0058a455062100d4401c0840d00600041d52442c50401c0020381288180680000180002c02152400000c100041000110f03010b000350358440700c1e424603042d280155442500c100181013120301d40c0e407410b01c418108840d04075000700303066996404416181e101c010807c3d4103011b604 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 968089361 1250 968088111 968088211
    0x1e0c11210604030e060a0e01030e012702120d1b030207090903121817070213050f0f0c04060807050307050d11030907050a0b0304060c120c08040b09010203 68
    0x403034100314580c4504001040c0034505400c0080002c03100800150140c541005a01c0d111548102d140440c114207003008100c245501c08024018803a403c41c00042581091142d0244101c0d4600208200c2c021140f45c4140d0f44980d40042c0c8603600300a041002c43d4400c5802d08000d400194803690355806401950b102035510300400c0181c0b040414228005017440d180c0070014060743c0b107526802151007036600c01c4100655140703c00ca1400404007484802c0c041102401c42d59018002c07410311420041c04c3c4054107001810a400074070a44203503680044100000b4441001201500c00f100c0b050b03031341c0400030f44072005c040e58103900140c814010001c040280c4840d4040b103004402e5040c40e0400003a07034a00c1c2540016050002c01d4021620600c000380301000602d841070107580c1c20a030440000200464100020399241c100781e403090b00410704041d1414a09504030503164480e501070075642803a540c070075903868200c0c801124003ca802000303016410100d90f16503144a480c00049404500b02941c07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 968090611 1250 968089361 968089399
    0x3050921030927090303041a0f0703201201030210050a0c020603042307030606170c040c03060509090136240f0e010e1204120204140103050c011e0c11 66
    0x131030300100940c0c400418003003007015507a40c07805a104a060b91000328100907000400f0084094160010182c8030031004000204510b03d039502d039001e02461682d20b080c0d46840d0441643c0909c0705038480c001e1200ca450040340a5400c803491414503079038440b0000400e030308001c1e0395003001d08284c4044840f0004170101c1140f0b2400e00c005c1c00300038002404024a140380901c240d50036600b20034608c18030004e11a0320f00d600001e03078002040c01100c011843c109a060110010600c40c4c0c0000c1d4400c1c00384050111554044d440380c1e0404640e00c1c000f1440da181c0030040b292209902c8a100040b07191213511402107040d02443c105601e281e07001e669000b003141c403101019515000d000139401581d840518036070b1182445034042d405190390181276000113100903103a284c0168843c0c030b400c0042858400c0210b41c0c940d40100d6034142c08010316400e6584908169039150880922a80881d0300e80350303039000200190481c2091420b055495442140403a96801e900002850034035410500710790404a070715034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 968091861 1250 968090611 968090689
    0xd05010308030a05071d01211e0e010209060d2309010c1106060a1703090d080d1805190302011509150b03040b0708130f030509210309 59
    0x3000d10007082d240d0810b03240410407140041c00b8242032088910085102c0d4680c0b6001d85c00040007401d00c15203454900f0000c52814030818041d1031110f2809a02e1181aa0071540490810800d0308041142c001d8805046080744190a03e40d5030194007803140d420303001b000c0d400040401c0b50401140345590864903080714511800d8500b144165140c4d446140c01c0c80c1d000c070140540e002d03110000c01032810514007148170394a032400f81c501100a030301244c0781944020011940504009001410342c591141841001c582041e110524a1410642c0e03500c80220b00004012195820501829080419503010881e0205120003181903540390400464110b0080721600000c10102c68003084401e401e0002a401c0b640030f070400d0742411028030912000c10710407040c0d0f940c0f041f214141001c56403503c2c03006107850700a42000412185e4090109010103034440c0127010ba5003002c0c5c0c0c2080111042090b84081102e040d94aa10700b60320900640c219440c22000401e5004e00c04100034001c22560383c0005a860 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 968093111 1250 968091861 968091863
    0x20d05061503121e071b0f15020d020c0f010c06051602060f2415030907081603150b18010b0403030e0d1e0c08010e100e12030c0304080d050103 63
    0x789000ca505039642014401c01043c1501802c895182840c0b070035200c0340311003c0001d01e00740c0300404150041040720280415800921115520079969680d41510341500500d000d030301e01c10354004082c6810170b400055500b607454016005044c5c041c0c0303240c0600a442541620840c10004d40c13184c5580415014828640950704684c00c01300320800f41030010b8074140380030b030191340c1003c1c81c2c0041000315500780802d044000303516058905100c8081002500c1c0040051400023460000014010702000010310002202c48400c266601f00041c50003035032454a55200203420034050f41c0c00c05409103425405900c080720010540c07000003104802d00d40402200f6084041d40c204001030500a06400240307048512008503005c8584075070f03503a41c0844501c0d0500d041d024008880d0208030410410000710340c042e000050003000180400950596104c281244407010716291074400301c1504004141002007100e844401844c1d501d5420b00d4910135480284140d440d9001406001140526805114021 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 968094361 1250 968093111 968093131
    0x20705030d050702070b180103110d090212070f1e0b04120b0a05060607031b05341415040503120a030b03010501060813060b1206040309060509030712020d0506 70
    0x80c500300302101c0212030000e4030100955121010400ca0b0300e00d80f07400c541094003840003445118810000607006003118505410451801194082d413107178040c0c0c4024480b500071034450659285201285456807014025000c0300040b00c030080c016008000783c000c0c103d107240c0140706130740f50340d0310000c1c80b591f003103a007145103030110f003141110901880005403900401803d1042149041050001d0b4162103015401010300c800c090090044c40c054090380c1d188190464265441120041d40d50b0030a120704071030002c0203d07407035105561560607025000701a5401c403c0c40380309030401c440030000c1520300f500c4070710528401048041410b407801c5c000d04001040c0d402143c2e40712103804101070103440e102c3c0207981c004ea2501004116466100f141c00d0f07000201280c2d2006401840d040c410042e04000341d0446d08002c40b088910002e03100040d14503c182c0c0240e840380340326501d0351800c0340c0768810031035901c0d815803158000740006810754103088043c0f40f00030a2003081c00401d46d40c650400004650356825 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 968095611 1250 968094361 968094367
    0xa061e020a2109091e050c09041b0f030b10030513120e09130203060a0f0e010e07030b090604030e010f031d060405010b12031806070c0b0a0207090c0c0209091002070503 74
    0x502c41c0c11501d4000a4000fa070420301c04407469100501019508544540b0441d03120004510204610011240132404c0030741306003d02101c0c400d0310424040211205000203102d1030004481a02c00c2c401c03000038100090a410081030300d550118058280a000b820401c0380100320134002442802c2c1c43c00c0d0b8404c85440302c1024400e18030410410400003072045440c039688042020060741d0200751650b004540380b50024400e0404040700004144103110355609601c2e00701090030400000440500300da124402c032070419074884038219210401074034000d020a008100c3c0e0703500382d1300503603141c10f241c0f002d0b20b0001103801c26100d44007080c590900c0e800006070410b00c144818401d080c00b40703003406103081e00c1c0c02420440750080140c0c0e0307220f6240d10700740d5150180a24081e9544100c12135003407035013100325014842e8580d071210410351b0044901c10b0140c07164040000d04006c05010300110b4440d1500c1c0c2004044d0300b502480000c00c0300400d4030b00382e8051414002c1d6003004d0391000d8205c05019100441d1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 968096861 1250 968095611 968095673
    0x312070506091e0607030c090b07080c0705061e0a1704110109091509020903122a011512020414130b10080a080d0b030109110f0a061e020a 61
    0x3083c2460483c2e001d8074110329903040059100001130b55074121201d0300c1c0c006084038640001f21a0010207401c1248070312000180070301400b000c1406042000b46407000d8030501584c0d4400c01c00c031403244800c082104080c030358114117829400c0000e8040b040103814840305000c0b1134540c11540c0398084508803030018080ca00309201f943d0100080000d4403242804102c40d425854042e6100202e070312842024540000710642d050320300f031004403140a102d1407030545501c0300c803404002e0b00d0024a9005200ca00120401c141c800050040d002d2a049003490164072609028611103510404170050741c00540760242103c5440c1c540c05601d10445c4220034030300030040e01b481c0a0803103403400341503010203914661003400401d1f004103070680c00541c040f2820396118002d40e00b146c00342006030f0400303605519040c104c20030301c842c0c1b15041180c031030120307200b01c070420405040103c1c200060081500081c20180d0f811902c3d01140e0007850b900725107004444212040e0b940b41d286c0030a100d001d0300c185851103130100c2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 968098111 1250 968096861 968096863
    0x3060b0427090201021b0d0209010e06120d0504030803250f030c0c11120f0d090f050909060606161e0c0501091406070309080303131104060e0a0902031207050609 71
    0x101d5003034400318140102c4405400007035840d41c6a01e0482201540203903050515031301c198542d111607078090b09045140d17a42d2002d41c011a60210b8025000d0504d400030802c281d1f00119804071007000b0360b1580b40c1000d046440310100d81d0170041402200420300c5604904c040c07000c00c107101d4400c11701e6480041e4040c031400c00400355075901c1040010302c2201100302000070310b09038901403039800581d1205032514099802514201d20034440085034002d4800401607942d2201c142c1003580d100402c80c505050f03490003400f6411350100c49910a40d0403000c003292003454038000410000b01c00258a83d40100c150302c560420180203110703881d1304121900c0c0c1000308240f61300000c0040009090201145280c095801540d81c1224001440303003a000800780109405800268040c1002c030088036142d00c0d00114003004072400c0f840c02c5d6115000396180384454031300750140c04240c450f100c0601c4d4540d1200307445140541002c0c0001c03681070003002680310f500902c4201034289a0301030001082c0c80c0c2890300303410b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 968099361 1250 968098111 968098169
    0x706060311040b2d0d030e1c210203130f0905101505130e070c050609070f050f031c051c090f300314012301050a03060b04 54
    0x2040c056803c040c44450160384007894650300d28410620340d94001007492130048001e00c0c03000d0040c0d10131100600d660034142d018a0f5500d2411058502c09111311348481c2c801015882c000303005214015201c1c1c02e0b46000581d5101015040b02801224103181c3e0b05590342c40c400049403c42480d080110070b081044070614020315803c81c480140f0003420380c0c01c1902036001c120031442440184040001e403c510003025103014402803101c511462103504010030000e2415aa17076006860510841b804075010040101c0e40f03204442e1b03120381e002080c41c5850184040341140040d100d50500804141041d1900c90810310100c6840f6560751030707956001c14603d508001d030307030b14150305a00303180040b404002100d100c0d01c4202250020b004410b1020303461001d01e0860340c000c81d06444038500800103412107415802000841070760310025002d6a8032003c500380c6c2030001640c4004910350b620b14046440d4007030801860041030300d02e03001c909a51510070349519a80581d004d54515400100c1c880c860300100540 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 968100611 1250 968099361 968099393
    0x3021228020a0f0806060a05120705041203110f0609211306021c03020307090e0408070c0303020d0207120f08030c040e10030204180309050f01030e060c090102010b06030f07050307030b040207060603 87
    0x401c0d42411500c00700105a40141440d12010002780c0003c1113143e40180203880041c0b84244646041c15180c1c94000c02403580c00020074203d10070030840c00340003c80491510f110700c090700001c01c03206642c203480c1c941c003601c0e21a014508000c1088440c4030101030078061800350041d90010011002c25400703189058041d0100c0b070f010184103100b030148076603001c003218084805400000c1101d440300d0401d0403441c030036010010040d1400303080020400d5004a0b050700c18040715000d58110580e5040c01d140010444200180454414074030580010b1001c00030f1508454003903501c509144d1070b041d0303a00c0512800c0d201e1844a852415080046117014002e65114080c00c80d103054182d0030701d40e805460000c181c0101c500c00c0111840306c0c3c4059100354005808124031030200d03012428400e091340602c1e4815211b250055013072000d500940e050240c1103901483c3ca04040b007041d5520f4510880b02500b02601d40c1c4101525010340c2c05d2265900c1c0003606507039010f800009011480c40ca0604108504001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 968101861 1250 968100611 968100619
    0x6030a021512250903051902120d17090c06032d010611100e100c030f110403060c050309030d09050a0f0b0708060109121106041706010e0703021228020a0f0806 70
    0x4c0920000300c1c081888440110b4400d0b40d082c03540c0c40ca2000540386100a01000034034442c1d9510800b034240e0008030781900020000248801e91181c051154070780c040a41c5458100c0c00810205810781c074001c5a115005803042c80481c000b28100b1451440c0f102c00f03030320080c0000c01d89505100304000038400d004200d89000b400300700094040e021541c403030040d24840074409564000d2030310300d6400b0750030400700403500044c100001050300c40d0070129034100e4041134840c0e1b0314040d190511140250126405000b1000056040c0380040300f0b100054603200c01300325114000c12840c09c0014a0032054a02d4051052034000040d18201000410540f00100180d0420011300802c202d0b00688843c0f2444440d00299180c04404650010400d5849150b00050307820701c407002190032078000071601e581079560f408907005481d01c0c1d029085042e4010120640c4544000c4400f05001d2400c2000034040500c1d4144100c101c044c60880160890704900311200121b169600100003456029400542c481c400316 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 968103111 1250 968101861 968101877
    0xf31080c0105030f0412020f1c09090c0c020d1712061c08031305070e0109020c10091a0a1409060105040c09080616051606140f06030a02151225 63
    0x104885104c2000680301a009030160302240000750310070b000b2100410041c408580360003c6901c3c62108068403c0d203003000065441101190501841c00f0707411150780a40d50780c1c0e0414909808000c001827040c03c0031076099006001071000740b10144003801413681c000f22a644146007840501c400800841c0130100e1071150304603140005034030310050b41c1e04444442c560348000d805e24504180b5200c142e4100e4410304c1c842800001d10104590020700f245c0c0309110980c0c54068000035040280e8003410b4004041200f00705070242c041000c1003c043d809400d03c0c1001c1281d940c1d24100d14030642d000c0d1200c07441900100c00510650505003e01424905980f0309070031300c285080f00d4240c40b0b8101500c4410b030000e282c00e407907180521941c1501c003031420303901500c8980c03951442c245005110040038030492103000400121035140011302c1d148594409005010049000d908001d1885034542d42443c4241c404e0141c01030304c901c4000700501c291800c1c0c01005002050810b02c110304d01c80d00c1c0d03882040219030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 968104361 1250 968103111 968103121
    0x60803130915091b030608120a0c0804050d111207121e080c010c0e040605060a0305270a060f05040201050a0e0105041a09010e060f0f31080c010503 65
    0xe914004803004070400098042c2c400a24031555400795000080c0181000c0840b8440c00c00b44c5481c503400c4000792001c01c50705075929000ca450745060b80015001e808103204400340c0c64000d09040e80400d2003640794503e0151144000383c1d440700080340646000b40108a40405d60030080d40d0950300040d014001c2c01800d191000c1c5503d54414485c004081c0743e5224030001402000003454644241d10030002c9031104c0c42d0054860003028103503078070400500307811183c48540c1001d10440302660350140003545000040142640602800b402c503102c0e07166075001030060603150710003100a0a807514042c081c00360290030705a090b5a001c00c5007640702803030442400f006030b801c80100d035200c592a0070034949120342c64006807054005d0b688400110090488070354000c83c43e540043c401040c0c03d03201c03760324184a0060200324022031038480202401040111354a022410103880c3c101d8008081441180313040c504440c00180344092503c2c000b95650050001c500203100542c4104400e2800c9070440c031b00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 968105611 1250 968104361 968104387
    0x30912140d02070f050d122301060f0207050316050910060c12020114070c2303040b090d1709030709020705071502010b03060129030103081b070f030506010504060803 73
    0xa1898800d070724070360002d84801084803588011000d650404c058490440624402500780003804040c510345c0342c9043c1210300d078800c640004188003844c0441010007a03003072440544440207800e0408065105020f00080e150740c0800c0000d40385483c040d4140001c2d4948070a00c840b010000e8a070345900d075541351051002a60000c00040002e8108031800c01a080d007680c02e900604200f1a528810075001e000c1001d02c0340c000d24070340b0445110791480500e0180001d4940700410308102c0c001d0f070036001000104400c1e050b9030040c126a44000b80002006045030341c1e500d4508000c09000c5d07183d0307440400c001280d8a0248071042c000c0010030400c1d032409403103607a141c0d1102094003a04501980f41c9002141e1940b00350b2144480c04005001c071122541c660f114000c0c2c44100300e441a03522806043d4550414000d80d0540b8122a40304004500b0b10700b29442c56441d510388000c3c205410303c0703110000a80c500f40305c508003009500900240500354101800e020a03940141c00440c000d5000308400240850 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 968106861 1250 968105611 968105617
    0x1b0f0e0c07080a050c1218010804050a0620030108010e061006052d070b090c030312150105120a020c062203030b0a090e1f0603030c1502041503091214 66
    0x251002001e96181007a0500b030703d041c085e00101480a1150042540ca0548200018101507422040124800104c0707401194104000c540041640d08034015140010b60190090b140440698226442000f41c1c0d201c0c08035140c1003680701c084981e44a501040342141e06022142d00411200d4000b41441d0600f403010380503100b80b05103c0144818002100c0d5401c003684140500360003004042c070b990391050b042421600d10300360750184803802407681400341494000700f02d440400c4414103070070f5183e17075803d07d0b0710304102e03070216030340c1445410851003540120b0703004107a100e000d03540e80050302e84020f2140c0c0e62414000508411040008000c5070303c41c80d1660b0001020329905103008915114900b020409804240d4003d04080e030074000855901c01000ca04c00910340d554200001814075800141826103403144400307070101714820381c058081505030001c41e00d0a442d003000946015602c203210303500180304070036110010356110302c6c0721700300659104038506004152501d00c0c00501c0140112803d44 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 968108111 1250 968106861 968106863
    0x10020d0807050d2c0c13090f0506100918020a090513060c0e09060604141311040617070f021207020301060506040306090c080d090312020a1b0f0e0c07 66
    0x1031400000c024a01c2441210b82c50b00d8594014045072043c010001c9103204003010f02040c404100580b075480c4d07034000840c0c07501c840004018082d403101c1854240002c0201000613108075a019001d0f402196017040200e000d6005030079840c044910700181c1c0c904840d400c82501c40380780c1d03010310620701507650501c0e04015521040d90000300303030300d81c0c2000d80b40f4900542002450282007a98030a121900000c6461521600740e40b1080039a950404107d080c0c170440c01218000100441140d0302824518200d44c000c2c0e54404c80000c00101d000d0358114150016032004000590821411300b8102d007101e049900130106007401c2c200b680240700040d4036083e88601c1da404407140031403408203640d001d4024800600d0043e00943e959512070410f4006001e80b107405480c5903032500c0303000401c40d1001580e01410001651005411030455561900550380c80c504d40c0d04521520440801007001d080800461316580b18000071481d140000c10746c40c801c004e07403124500358070000410140682e140c080f940c5007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 968109361 1250 968108111 968108117
    0xf0f03310821041b0f03120305131707060b040c02070e100b0403060b0405010b04030f020913051c02010b0402090d0f020a0305070803090406090507051c1b08041110020d 74
    0x403462034402c44180070180d800840030300d040106000038401211040290312a07004034040c4402d803180c5154409180503c80148040c4c800e01758100002e00c42ea00c210f420280c04040c050340115a42c468070910422100b21880c070640c00a000b03007c01c20320748205409102c0a40c0d0034040c003900b00f8000b03920382c1517074481c02a0620113200010301c015003010400003d0510006041c0c0c071107850307090102c000e0000c15055030065107000008115000c01c50181d0f0201d95210603200c0c0054480d45c203000302c0d94005031822070005410241180041c4081c4000b16640400c0314002c090040c040c0b20003429240407005150140303204110308070b40740d151000410308040d08040480003082c01031002c611010f44a034000b0340180034a003804107a4500c0440240030781407007102c080c401c5648078030b44d400c100c620036149a0089001003002d51001402c603d0410855110755000040070310000301c2946a6800325000000090550b008103c03c1006020f41004800d500b03994a426454044070080c0d0345100d095909000c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 968110611 1250 968109361 968109367
    0x60603060f01030b3a052509020c010b0109050603010f0b0304080c06010f08120310060f02071e0611010e03091c0606060801150f0f0e060f0f033108 65
    0x6a40d0082d0040403c180c006002c800003e01c01050241c20000d0f01050340f070041548481800104072100182a10745d9004005406c1124a01590642c240b00484401e000b2021a840014000c3c4151000e84550f60204001081c2c0c1200c10000422038846500914803d141c18001070041500000819064482004199a50323481c0c03820000c886014110010a9501ca00c01c00400c120715502c021070101d991050440305440740c500f0840f80b05001c2154002c00d070000e01c400c10441e41e4452204c0304444001401501d5901d600c4901244241440801c140c41c81048490100036183d40260700d03122046150008000c100e400c070f10742580360321520002a02c10032132000c2900003001003010019035103070f0045003040499039880b4094540e01e824401c00803591481c0c42040a00c90080c803d040480400d50340e88010044891000e07100d0b60800c00d203080c0c1180c030600000c0a00e1a4850060208541000d04603840e40360280e10041810074194038000b5150507054400c2c241e034001d2041d0000f4903801090361752 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 968111861 1250 968110611 968110639
    0x319030c0305160c03030212010b04060f21050606090d06051b040e010b070311010212070e030f0a0209090307060f1508030715050c0706180c05030d0c0b07050f0a0201060602010507030506060306 85
    0x203802231031079040f81c00c00c6100001546207107004c010421a40f150f202e5012402c0c240805481d0206200c1e41411078400c00c03818401e440180303a01540d8485401000c2d9401c20004502140030618521000c5541c903a94000740301044a250501e24000240c10140c103180034186580c0c50092803040c415030383d05400101d07840040501600028441030104402151903a03108040104081d0003910780102280100360101014280403403102450a8128000d140707001155007417100942004000381510701040c03104030001040f40c01a151911100c9402140140150a0340c03000306130907911906056104000c15000a00e80c1c00c58420700903000710f8005280ea55915140209104058000b0881c52801c805a00301c0d5440c10080724410740544c01f5401da254491080c160790301d81c0310a5003c04034800542200c0020305000206078010b01c0f80c40c20038240524a20820001e41001d11402e0140c1d440340c40611401d5424418035034480d45c140307411710050510b580890b04601c17000d03081d41d00540140250b04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 968113111 1250 968111861 968111867
    0x606040320040612030504090b010306030203150c0f07050601080601060306260c0622050906011b02030708010e070e2202190503060106030209120109080306090a0e0319030c0305160c03 81
    0x1000d44613007214905102e490300034240d82c441e0151446c000d1070600b889415503c2441034030203490b40503004110321100c4440c01ca078203540023804807070480c104001d40c440c0d00a008001e410894480c2e80241501d5060400c0c0e01d00303240050704444101840c1c4803040040d0401c90210510540c2c42c0c10f0075134200c4824180e03450510004001454000d8400a000040d1168101c981001009184401e40003a6103810400808500c240e0f049400207000166941d0800c031045809003165100078100d8a103d944c402c034850940e40c40407194480c94101c3c003400c001c804040d41d18964001d102075042e214404d4a021045603002500070302034001d840b040044550341040102d6040542030043c2120703081d607903d043c001c010350300c4034030028052000745001c000400e00500132140000d034002c54060441d81d480041c054130780c1c0010701c00e01c222a10f964440900e144140300810169a0ba0410000d0010384d05801170207441d5590143d400b010b00c1c001c100824414030700f402241c0b26a1a180040c50301d56541011 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 968114361 1250 968113111 968113121
    0x90e030d050f31020d030f0f030c050a0e0d0f1110080405070314010e1606031109030a06110d14040c081b120f010e070303020106061b1b080d02070806060604032004 72
    0x35003005c07842101505140d0030812224884286a44030b21018440300f0342103060381c90384180c01380410014400c0740042805441540d404200c040d00c101404804d64a591f074843e401c0701c40030396800060880303900c56030a08134154441515141450422810b01f69503032a034940c26840003800d030a20b80e03081041c21400c2074001481a080040484112030650702c038020100201d80701d030038040ba260940013141c1000180556800501c020090f00440409490303000140c1150861a04118800c01c00d43e5011030705882118806413041388820b00d00d00e05460034061060054100900c0707030780300700d0510405144110361388283c032005403841003001200b08000e915048a1241408083d402e16080c1e260641c80000d980d130840707009074002e0051580c0d507842503a0380c4030454030410540c0c602c0070b0f8580100303107100ba101c9003220301060324810682d950b000c000c0c10211007035030100044c1c000c004100417094080103040d0304904100d46162030f041c0307903540d0710181c0c04641e082d121240e010b2043c2c4202d40c1d551343d03110f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 968115611 1250 968114361 968114363
    0x18030809010e280605210a0207120e030c0a0b030606030907030f0c061205040b070e1c05030910050a050a030908092706010e010e0d1e08190c020609040213090e030d050f31 75
    0x50302b154000800080d000010f2103a005003e0710810b2a444124942070301b9201c00c031203504009070300d95140c94060050550000740380c9070b164800e04600000141201610712030b4107010fa8005500c0c10f052a00080c914894240c502440740d080c401808045070398041742c3c503004200c81c00c0169034009140013090b100240480103000d4640722524482c14001c0100080500700c004441c8024000340300300054625016401154002038418407100054501950041c50158042d0b000f40d400c1108140c0080c840c101c0c4101c0344414a030701c511002440e6001500c3c142d402010900300740041c0034000300002d0904206800991103216010980402e000300301c0944117594800500d11030554015003060701c03070b5030700050040c03800c0718000310445903580c4643c0c0024443c581c01170004d441d2001c840c08000c06508150b1040909000e800700020b616011481000001584c0002941d1200c0c984241c04088a000a101c0c0c10b5441c40002044101c007100c0d49000d040011070310a500404000d01040c4070300b046140381c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 968116861 1250 968115611 968115623
    0xc06060b0d0518070303050309161401030f0b1003200c1e010501030302030a050703030f06140f0d0c3503090a0618030809010e280605210a0207 63
    0x110200e0555503480c02880d0310001e060040c00a81c481e404841d49502c0c0b940c100c43c00d5500305610a2000a204600440d040420001142c180d11305507280300c41a102c0b580d214400c2802400700c2800e00b0750709030003501c020b1740b03000c40d0400c2454519408602e40f100422100c0c001c059541c0c41411084038412000301e5034106800d6641c1d1900c125050090780c13591400441a5280f013280181c0004900502842d4143e0754141d001d0360510364650700a1382d03c2d81000c3c50450525440b1514400864504c2c07068000812140c04486044074601040c40a281602c04649000326042c042030000b00d650b10302c040e02218420141d0700d880c40712500504e0010380c070b01e0020284502e24120074404101000001e00740d000303000c844007031100395201003d560303010180e07082d01d081400c1e8076010004500301d4030141c5500700046c10038a0341c08852000007400306040014100244003011103044440304034100e04030181c490750030308900d08050202c0301b043c040c5594050036000071004000034040340b810340640300119480b034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 968118111 1250 968116861 968116871
    0x12131103030723160902041d1b03060f0324070201020a0804080a090305100203160806010c031d1003021902030918040f0816060b09070e04050429090c03030421030c06 73
    0x41c101780e01950003441403891448202821030302030184500e505000d14480490000072204885c6203052980000b0441e42d40800c400045080d0341d10288010003103280f000c8400c024090405800310351002014041004582c4148008010144c1102c14a81c01c1900098140e03114280070700308a50118254000421034001d80000d0409801c01d80c01550040f40c11a1141200e84c1c1d500382c0c22034404004484030750004400000076004217014031441040508040c2041c032008003001c02142802c401c07008000c000030790002d644c0030307107540e16410070003070203100c0c8040c51034002e000f0700058494040d4014040141d04460224040014000d01d00e9402e41d030002460b5151603a0441007403600210180c10741c0d40506100603040185080b00900707106c1c580c0340d201c003040c2044d8001072200809008204598645882a4030003049543c00c04040d80b05201007064011480d08191a87c24141c801041e00c0c000d0740188010702141c602075907007144400c2d5204c2c24110342c50b008d09041b2041a100c4001420751031801e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 968119361 1250 968118111 968118119
    0x6030c080a0311030307120504020a050604120203010b0906010818032209200f0c070803030f180c090c090d1401290f01141213110303072316 62
    0x1160600080d8001d0311043c03d00b114402156480e48000c44e5003000150724040d81002500183d0f200380d80003800541a440442d07140c1c0041101544203411000e04041011070180c00c5207401d001e24030801c5030650740c444040c1040c0d40080e000410182444008035140201400c0c8070404005886000320305104459440780610111250503c0c03e005000c5814141443d00400c1000ca90300741010501641c12a0314085000c80c80f90400e4000c16a001d80c0c074010081c00040c00202040554010b010390100307201c040c184192040e6402c4200e40c50740b50300740c07c0110703000e12940d902c0c03c1c2543c2c880c15035240765a40d0103480000684100c680c1c4001030806017042d8041d80e00c04ac056101a15000240701102c0e000b100b21000e01d090a001401007680c40100382103d5030701c3d54864905098004104c1a81c0b9060104124480000340c804907a0b10403641040380003001480709980030420301003002d80165150121646601c98006da0300b0304045400500700c50300d01130040041240303d01e6400000c0352060441c2c0c403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 968120611 1250 968119361 968119363
    0x1809070c0f0f0201110d0804030e13091a100810230a0507080901090c0302191827030804030c110301110c010c03020901081612060b031b13061206030c08 67
    0x1e92000d030300040300c4003804c000c1688001b503082442c00e2544c40e032507519519a68115040c0000250b20383c0c0040e00c20010740343d0f25407103004070300515100360001024044407484480e40d01c503000741109240305008204021250313011640030b03080702032020081240c012403e40110035008110702c111040c2017401c01c110020409501c110b02406144d521b42a0688070000344038241c2c1c0241001400050100c50100010716008604091a441ca40048017616503102000500215034044a450454030b8624200420a2981412010a94103007919000c0e00c0d10303440081201c01c00400003000d20408018010a0101c0c40c27041a00e00c640040c02071180700002c60300b42a65821030304040100e90300302800048114000e00030ba4014070010380d202d070b910303503551980200c40c84d1a518680e400d0011a4005118005090180001170802c0000c01d07696801c1c40c19844280e081920b45900c2805070034003000c0c130360181c1c800254084071864a849896000102c8003507000b01f429030301c014146209005e0008030020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 968121861 1250 968120611 968120633
    0x903040e04060c1205100621181a0c0417010b030607090302040b15070b0a0e120c0d0c120c0821040201080c03090c10021f050613021809070c0f 63
    0x1a42d40c4c031810100030301c07900681522429038048080d81c140b040c00713200881c452440280c1c441c28000000d034404c800907c0ca001100d9984004425422030049940240303d40010700c40c8203000d2300c0c0350381070381864003684c0184c4600960050402010741c1c4d081d044040b403000d4201100608004090b00c25074100140013404900c050700c0104e00590a158200398503240101d6440b18142005104c02d152915641c0e8141900500411980d41c49074cd40781074480300c0c0c001704244200030064403034480d91803010105991030108071100c1700d010403521454020014003003218159060410b03062100e10500c3c689003554036400354125582440d014003035010301c0c2e95168402e0500a5000fa00e4001d05600e0b00703e000040c51208859440841d4401e01856050b410604c10790354692100e407041d039061074544d04020652540e10f410081907143c495091104514000710082015100c1d000c046103030242c0b010850804004c150381540c0320306440700005030014010100c209039140c0c07101c40180b01c0710003841c10381c0c0014 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 968123111 1250 968121861 968121881
    0x7051002041701090809090403140313210c06180b1603060501020318151207021e010618020a1709010f230415110c03040810050c120903040e0406 64
    0x281d04600824450754041c444c9a51583e00300031214170742000603050148001c00608114104441c5000546a144031031010b18001d04480303005058803030b240e051801012400382c5103010508080745484107a0341c2c001d002c006131503504c5440418260303a800e101d07900f44080c03000c001e4010310280c801c01c42c1020300211400c3c0100803c1d1801c03c0010b07142c2c4012652809140c802e801c801100c840c07600800d1514800c0d40c40d2420710200f2152030282d1142e414246144291800405640040c0618103a5455542008001c814090080148503e002c403d061840c5152034a005900d03400a14888510302c21600001d5101c00a003080a007800e010080500a007641d8075040c02143c42d020100b0386014400c0d008140c000840b500030042c0c0d41301e40c0c41c2c0c40803810074107181c0d415056890b0305a80b10607862001405d0701003a4403020b50b4903680f40000803410420511450100b407480c00e020440740e40c0c1858213850002600100f1240f5079510840f02c40d01e0351240d40c1008041030b0b00e00c001c100030481d507a045017801c1703 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 968124361 1250 968123111 968123129
    0xf07030c0b0112080315032109090106051603050919080601061b0c0608060f1f110706080f090f060f2a0d09030c120203040e0106110d030902060705100204 68
    0x9a0b81c0c0300f4000000c1a58410001c2520404002188114035006248503000000505441c6510072081d020a000da800606014083c0070204003010f2034584603150074010001e50902d1490900d0088010440c1550464001c05004021442d207034182c4804102800804198900540ca1900c54510580d500e000740314502c000351101e40e008030415000c0707250644103903020105910741d5003414010782c0c00780380044c10315030010b0851131803c030340fa40d590154120040c00100701c0310340c0107420703000100b00701310210318151030740e00889041191030782c401442944080d00e0440f40a2607102d0071007203400d000505418580b030784508e205100c9042c6009138003074020140c009001d84425420007500c52691aa41552401030350309015200c002182a00724944980c4070349081034140010b5a2441032203a5004104001644042018081415004250303805000ba0f401e00d807007280d0503141a15590390349080b00c0c60806455481d004115201e0000361014564400155811904100c000a009401610440180c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 968125611 1250 968124361 968124383
    0x3080d0f200c120721030906050c030106020d1d01030507020a2916080a051026061f140402270103060609061d181503010c0807081b0f07030c 62
    0x62200c181d01100d200c2d60380615121004210300501c014442c032000c030280c5c140354541c0c41140000d04d26124061140c00300501c85603c9504040c0000e18001d200d00401c810b006800a94014071015540d0340503042100740b80200d11943ca49404a0810180807801828010700c100320321000484070203090740030660b041d00c115a90344c40140d902d91001091541d803000c510501e010451f80b58598104c154408200200001d140f65a4580b5114440700c0440380e00301c10b101245110001c1006000141c0c1241920914802d03003aa0700410b102c0d26800d510890304280c0189036181300c0c44d11a81c043d19841e1801c000b05c903050040d500e02280850010341d210900103840c0c02404907070617000f00703100010380c1d8150740e030f5002d0007100c0d65107244181c0010000036400003611510080540403125441e220703802220309502129042c0c8103042c01d5680c50302104003441080003c00130703540e502c031a4640d44034909a20b0303005102c04001a0015138840c0340d01e207080c2580006038200505800010310f070b61403442894007040c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 968126861 1250 968125611 968125633
    0x705100902091006120c14120f0c03160503062d0f120c060304110415030311011119030e07060215010806010501020a080c07180912030603080d0f200c 66
    0x80401c054011980841e804012145d070b500840d5202030301035200f5081c00110049146003140007600200d40110740151400b0421401c1003194034102d030003d0400113001d0440c00d0280400c1c050341f80010b0101c0411801100040303107a591a1754107000a0040381030104040e00000050240c0040f5040c000d000354440a01481c00382061111a4014203114018114047c0300d0000c000c9158400740094911070199040b031049903489104440e80c0300320b29070443c10380a15500e400b500505c40c480c4900c0700d5074504440d607100b200c401404c6a0051a13811031003601030b6021001a00105240051281d50784144000131501c15000200c0c5600088140c100100310780e83c44002c280d94650901426005820400c1054001071010703002d000f00300d0070700082e40c041545440312a2071414060310811240c0340c03107524030014444441c50080420b00c01d807030140710750350031500d0350f420350310560329103032822543c5001c104040385199126011005a0707240e00804942640031688180e0452401444c250048a03c895 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 968128111 1250 968126861 968126881
    0x130203150402130c0e192d0b1c060e0621070608181c1218030e030c04050109020c1c0c080f28180b030a050c070510090209 54
    0x64412a40206900d00303c071200e264100280246081d41c8080c004040d00940260381e44000310018041ca5a141c4031441e490408101032641d48808085001010010308070038102d04100c0d00410b0b40d80d2043c00e9962545c902c90b00070007450800d0380c1150600c0c603164000c1003000d50354030382c20b004040441e13410750410303c03c1c10380c8000141d904903504220741c8024410040c1a01075240c159201520101c80d4800001c42c0c4003450600c80000d080b4221840052241e0307008a401c10004440340c9109041040b40c0c040406410b6000040560050184080104150f905a0301046114440703103011300140720a50390f0307094100181d04224000e040034091240042c1d0104420b80400150803080e5a401c1003140c02602d03841801c0d4480c0d0fa01516100040001344143e001d0035511201c181c0c500900941049180e4200519004490a040c10509542e4400300660206041034a8005e0460040040c80d5102d15440d048244620800140b4074028803900ca245000039601035480180260380c550102d90714a500a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 968129361 1250 968128111 968128153
    0xc0307050702130b102109050111030f07020601060c05061302031011071703040803040602030601030213030510060e10090b04020405310209090c03060a0503101505060306030316030504090203130203 87
    0x31420006103549018034906c210341009091501540000450a559071318141080e441110001c0300340c8511001d02c41055030400900c1d00501080c54280c0c0402d0060703803a583c94210181041c040e18003054200c07020341d9800c1c00440c2c24141c40160422014060403407020080c0c10214054440440c26000503034944900707000c4038400c940c0404014515982c50b41e0f414000c0d040541600d04141d828440348070a500503402d01340256000314000c0c0020700da46028801910040e820017200a894401031100344c0081c416084207682804101084403160800810024051984800d81c480c5c8441d07400b542103000340410308141c0b0302d6040c0744e020b407160b1810b0150580c410008038640002020000561512661001d1500281c005007203601c41035503800080d01e81592007458000c0c142d44c841c0c4200c003071000c22540c00c00400040d81d00a04510340100080d441c2e00450030101c10780504d0f441c90404151162003124003500006004640300d05220303011041042070442c0882c000e01c103a541d1080c0300710b5100e040c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 968130611 1250 968129361 968129387
    0x41d090a020d0b070504030203010c111c0806062b24031205091c030201020310080f03120705040b1314240a0e0303031e1303080c0307050702130b10 65
    0x4160003211140d940c0c0543c05401004041000ba06200100060750301303008030341c0b01d5600c2e035131a161755039103618003141030440010003016185400780d00c5070980707500568410b030f005904958040e2180c401080030082d100d041100c2c1c68801c0c0003070350310040c4111142c3c01516101001d015440304450450803914550000f0b00015060b49030903007906015500c102e00401521342d0180900c140c1c252012580c1d01d003691500e9003100585d4021081000540003d84c20078001d0402c0e1000300207040085050365181d20405950401d04510403001455440c001c05c00c0b10020704070f000304c10f0754440544004403c031658074001d05c0d01c0c0300543e00d48400f0501c2c0100210001204600d00300c0180074440c80c40c10603c4d440b401c0c500080c0000742030118510354042c000b4612032106400b071001e0311202081e040702a0303079009000d1840b0646000740400461350000d00075520050f920f80e6103540340c44051003940c40340200c140003503011070781d40d0740d080100c03810390040300c0e503094155107120542445600c151044241401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 968131861 1250 968130611 968130619
    0x50711070305100527070303030b03151603020702030a03050c06010b090f0d05010609060e0405060f010312080619080102070605060a0b071137060c0b06011112041d090a02 75
    0x140f1841c1a09650720041d0011001da010504001080081c10004541e00110002c59044000104241030300b42c05111700005081b4041c0042e0401c8101040442401624001d101c400070702134034031114000d6046038540d0f500201140c2c0858010328008145911689901d0100c2c00b80a00004900e80e03801c044e0b070606c0000400703003190344d0102c00c1130000c240070280044d030301c40d0b40310900014200d54a120314000b40c0083c03d1810218545810310a1800101906c0c56801d070340d9543c0108003182c45400d150a001001c1e02d4100e40d0390300d43c000058a1781d0040c01c43c1d9881a1030f08940021030120540c011701d00248120020300c50740d5039003000c02044a11910548030144410800640000d040c00c5d41c96000c86030003480310b200800e45102103000042c07440440b0304400707a0030f03828040b5001c60090980041c5210b162003480050b681c0d807043c00d0078030060207590500c1096a072302001d0200c2804190030001018007019140c40c0e41c2c5010130030000c440c02c0ca41c1c01070b009650100e02070b0480810102c210a030054 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 968133111 1250 968131861 968131873
    0xb0a0311090601090f1203180515160804090f0c0906091517040c0e09010b0a092c0313080609071e0f09050403030501060804020d1106090303030109050711070305 71
    0x24140078481600404050400040c0340300494080c02a00c20380d00a84886403c003900303402203140c080d00044041020b40d0034408100000c103c00e554480b8900003080d40c011800307446100340d28440201000e8024000d103205c0010802160501d40b0364408480c0c0c0c05059402e12650301030000603a00300d42c040c020340c000903541c01c4d000d02260310004110b00c8070b08880e141c440702c00014034600c2d0319070304c000fa28102d4240003411010000b0261104500b134000d85c0c540001c2050000c47c02c0098058546c0784070b1140031985841c0c00b541100ea141c41c1503150b1140c21001c0900078124201400e499031300002c0300d6040c10040d01c0d404185241e0015007d0b105100b110002e022007800c1066404e0008062803080402c1c0640c2803001c40d015a41c5010000101460040480d00d030030986000b03002e44905170060380c10403410200700710250b0750b5000b807110005e410003042c40800307285a000c40e205203d41c10541e40c16200000001039000d41552003144551703d6607030b606c1301c82e840b80e00440c0d480e4040c500c40580f26900c44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 968134361 1250 968133111 968133143
    0x60901090c0807030c020709090507080d021b0d080f070c05030105070507020d1e08040e01150509060a080a0f110c010c080c0d0519060303051c0b1c060608030c0a03030b0a03 76
    0x2903030002a1740d0394180101d681060380c40407508140c074181c1904680d1038000420402001e142003100c5001300405001034400b6204140c040710411001034050ba200c1c0e02042c20145c1408542002c840c8880007031513819075036168a0800d040c00305214480c142c06580307040d001414040c450400e60300c01c41e034000e000626110b0551200032001610903810390980301403159840001d42c6000c0108020800001c58010661400d00c91502244e2140244001d11004010707050180d600c0c04121034105c540bd00b0302c0c16040e100c04101d00010002941003d091900d486094841c07440c3c600c014102d810700d40c0c0300902000389114001c03518004c060351002d0410200b4000d806040215400c0707980e00c601880b0a55074071100555501081d12000d500c268040f036030001e003250003507841400700c0f1a880f009032000d0007108500800300702d060365103885480c0042c080f90b03480ca0030010385420035070051a15900b01c80c0c031a00c070400580c1d01c8000d02d00c4124042031511021100c00d0030042c41080403250440c1140c1c032481c2c44 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 968135611 1250 968134361 968134367
    0x110f06090409060b040c0804120212040b0c2a03070f21080c0303070522030803071b0210050301060f09240c0f05071a0f180324060901090c0807 63
    0x25440100c0304503440741204c0c0100c0e02e6a01c1401e10b4030803e99a264001c0c103003030034440c00c3c49201d85807410441d00104072400002c94040c1c111005ca61400d6200307503465602c00501030800d88185c4004c0401640c000c2d0301c8980000004003c64208012019a01d0a80c6e5401c5040c8200006200e0740c24030810210ba06a4904002c480c42000c1ca400317508114030304003540480504641c4101c3d000c00c041340002c80e101d04601d12a003002d5021341030050340740c450035041d51a5030700b0a010041c940801c005282d625a0134900d44680000d441ca540604000d0000c4400100034002d50000d000710000909444640c00b0498400c00380c01c0304640c000040000300f282c3c070529503800351445100345014450101d0300000016060006800800d000d44003600c030450500790b44941d81341141503c06012a8240910000244100101ca0740c840034210350250421109002c2400d18030301d058404002ca281131020240e6196400c1800e104400c205c07011410360703880e110203204803140f0a00000000c1c18600010b000540 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 968136861 1250 968135611 968135621
    0x60f191a1e131104081f141302040f090804121703070f03021e03090109060f0b0604050f01200105070e060f1204030e10111002030609070507030c0803010909110f060904 74
    0x604000d14054944900c28940046c0c00002c0010b4010343d08070b101006000d00c1040c00407644915210b040d0308004400c4544c24100304006449541d40701d40c20450600181d025a1039141c0c00488030740c44a40da41d040850154000d81c040d13460021040a84030613403092422039101b9116a01c030180c034071041120403802500004d100d414500f403000d505949011b9258061442504c0d103600200c1e2034040ea18040c420b441f00c8060210055040c07100700d250658a600c00d803000e841096600c0c1e00145024801210748500040702c4981c0c0c00302c8150355a65010041d0412840f0300d8254031400e119090107020320103e48644018030407804030030300681c0550443d41c800030380c015001c1d1800512a0603e100082d5990120750791600109141c1c0c0501030000009004482207940080c3d4114110b02d8110007040381448000d1555040010004002040601501c2c030440c14036003145401d600ca43e1500005002440340041c20b40b90b08507a407003660030a103429401d035400120041c01050401814005000c0501 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 968138111 1250 968136861 968136881
    0x31b050106090509011b02160e100902031e28020904060504150f0506130b030705070c0303080601201b01030902130915060305060f191a1e13 62
    0x154035058005000c0c0c002d401030a0069541100014400c1e40001640102d107214550000c15500702c464807010404000c1c940c00120b8094060744038035503a8030092800c502d80c158212500c540e00c040103004011300807520000110b00056000c0106d512150034613800314080c58580d101210503103040039001c40c41500a00841c0c031b0017420109106440d000014240c0e511010010701da1110070000301320b444c80511540300100410307140c40c0c0c5409404071102d108040385015045030384070004085015070384540121000282c000c142d1111254613480c000303103016400e0b40c600340010085000081882741c40700d40c0f500c0b00c000f0f840042c0140d80058083c0e580c01d2604d104000d040c1540d80303540e000580c84500c10385000000100000450380b1051801e1900300d2103248003460341c54500701c4207200144002484039005003400e45a26180e50701c00b06140f01d840c2618014801c42421322882c0c14468510070748022140c08100c0d038208080e004c5c010032280180032115450350107000021007422003042a80414560 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 968139361 1250 968138111 968138113
    0x105042114070f030e210c01110d05090307030605011e06020321090f060901020301061404080c040203131506061b021806012c01030b100e0910050d0f140109031b05 72
    0xd400319800041c0400c5181c41c6e000140c00c2c41729144040703000b05106403040d0140900b00392610359002d03909640e8030780c01c1c10f81c21070902a00045003401e99400308112401158440740a200940c1c4400d002c019800340d1039401644141900000f058890010003514160030500000100030070b20500c2050b030a60f4040d0a10744140204852001e0061091100620402205001603a607500d032480062825032801825074102d4001d11051241074404034015803450000c55004d0f03203a4841c031180381026100c4e18401040c0c45940340500c01c040c49690800e0048608544480741041001c02c04141e10442e0b900e0700a41c800b0403035400d04a10000017004580110f410314000b0b00441032040c0c1e0b40001d003600d180141032030f1005184007440c2d6916001c0c0c0c84d007001c400d4500d580b4241545102501c0810a0807003144038500480006441040c1052100020900180744084180082c1030481000d50340104c00e40b0000e10141060104410500031211141e50568854413040000c61301070b204000081011030302c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 968140611 1250 968139361 968139377
    0x92203050f0f183003190f0909050603120c190f0b0106050f041401030b100314010e010f030215040302091e1e06010507020d050105042114070f03 64
    0xc2159040c040e003070015030404410740c1d403ea075614502196501601a610030322042420030700107440c00c80381e015020418880001c1c1d0080f5102e850341940581c130702c4052598801c032011070019500050040001c1000e48030503031421748400c031201c00c1c1c03a021180c0507055030059180000e015102e100038180800780c0000e40b66800d00c141c1c06e41c0ca00c60200d5030b040e0b90f246080d050350421700428619950041081d0704250746465000c0383e224110b400340e17200d40200018400404826079001c0d810001c8400d500070a291802c0607000e4003d00104a03003a44000c015240c54004644103801280c0c2a0603505000b281c02d456514550800c910300080c11001e14443c0c0b014440040140ca6026407240100180c000c00701503603840d1101d0380c190300002400c00d81649200c000c070340812145419956000342082c41d186a4038603060020a201035005000103006600c0c2c00e0401c0140031540075a10360b1800c04402d608141203d103003084808075905040030701020001c10004001030035035024142e2a40c030030301301045 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 968141861 1250 968140611 968140627
    0x11040c0f0e19030f032006040201030908091201052d0c0f071401410a0e031602100804080d051003291e161407030e0301060509220305 59
    0x340d02c1910303802255440c40c411040c20415400040718156100021149600100c0040c540c542e03441d40544040d05141d928100071091041c2c0c84100c1d0081e0030003400301e02100c1c40000764180204011038400c42c041c07601c10004220003604079516414149222140041a16038001d04dc415911140c85111034001c10800000040d091000c800e0310140c2c401c000040e4607004410745500c500404803040d80d02950418000100f42c208070568820b003401700800141607490024240041100ca4840300c3c4902c00424051100701c071008c3d008035205d01c00c0d1480043c00c900e8a030155920041610018140b220034010607100c05140d61050f58420741010004001c5543d98850000240d004030074603125190240b103040c0440300701c1c410240c00580c1c0c1e00321085c8120200160300c9480c03101514645c1c1c107090030500d90b005e0324810455012981f5840c01000d83d9801185009080784041507500b80c0603500b000030000b558035007111428400e40c02040c00500c41d0002c441140700052050004030b00b400000e000c148 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 968143111 1250 968141861 968141899
    0x218090a12030609060605030f0411120f061b0a050a080403091505031e01050a060c0501060f15091415070312020307050c060603010603081902010e0d0c11040c0f0e 72
    0x40c00d401c1c0c05440004000341000c0004056403a81d4025409200e4104107112051050b44d8445d907006030009440385081c80d900c030004044402045942130300348a19a42c08440560201c0c20782e0094a00c0300c80c03605c0101d4480000010341c05000106408a14140003444c100e07402902c0255220f4424070705900f110380c43e50000c211a02c0c610301018002070020040002482d07110b003030300140100150214210390326100002d40005c07440d024540c10800092a800c040240940288010300302d00d80651081700d449010f0407481682906240d80020350406c3c001500014001c00d1a00000c0003602a60030000c144a0350255580a0901241005a84001c10403513000c644003031409880c09941d119030325240305080a10b048009041345110b645084803c100081140742121404410303241c041c40300c0c0d09010310603401000300a0000c0c48500800e013040200036404606030612502c11402c145070450300300c00784011180c4017420742020480201100b001e42d07024810f010801071000700160b00c881d20b401041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 968144361 1250 968143111 968143133
    0x1502120706020901030b0a0807092703030209030d0c02150a11071401030608030c0a0201230c0a020a1401120f0e01180308010e0c070b0c04030b0403020f0c0d0218090a 73
    0x5640300755011404107103e69260203000f0841d0400c44000400030b0034410069150b000710720664855981c0c0e0f0000c08c01340a100801580d0a25040e211603101c1d900c1800c01601035482070300c105101e40110303050608198013980401c41680d802504c0f0038100701010f000d41d0402d41c044031380001442120050006d02e0f1604102d404041c00000d01c100316040078010001d000c1d01d003d81c00c150440d42013402a8165814006140ea2649809183c407101402801a406000c0d0030490542142c0c1c44001548440958000448206040c030a075030580380d00c1d580f03140c42c03060f48a000050314005900c0c20414004998035400c4114070f902441000103a0b60402c6440701d08403121800c146c2550396039083d6410a06411030840303801880c1980041800b860244c070100c400784035810000300071580a402050250790100250707000b855100714034502904003030502035601c0d40002c030708105d54407901d806120311341000010384041680c017402d04088000030603900140030f500100780300700c1840b80740e429502280e030300050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 968145611 1250 968144361 968144363
    0x315010c05014d160c0b09213703091e0f0b130308070b1005100c0b04020d08071a160905090406060f0b210903030115021207 55
    0x311042c1d08190b040c43d600d491a00c000416040010002ca140c03100c6841c0c2c411a4480c840c0c001240ea2043e00b030941005941151202420349080079402081c0103000800601d2921422284004070384981c824900007100042407100040d001600090848000a6102c4d00c1d104410b0080c51002840400000902c0644150540001c0c89105040040d56001d00d046001000c440f800d0701a40d80c2850510301010b1038500c01c28519801c0040c94203c0e08501c1034100001d5070f800255181c0c1d0741120704001051020035200030000001001001a0ba840c01c0c401c000b0101d03005450310500c071032594443d0041c0402c003c20580e000f0310820f4445001544000080600c20f2196100c001e00c0c0382130020880d40e05000521003403c4000319015013000c90f030007503a0842183d03000c0302c1e03214240d601c41c50084040d05442e440301c100d041000c603000c01c5007420301002d8801c4240000c800b01d0344000001d120402c402040e10079400c41e030801c1005010150342201c4140301420303d4011107030301c032810303000c20701c079940c49990 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 968146861 1250 968145611 968145641
    0x201030f1b09030b0a05040c060c210306050102010b011e030b0d0b07180911030f04051f0606030c08100e061807080a0c080402130513061e0b060403080315010c0501 72
    0xb805104014442d04403d800283d0010104607511f0941e0b10100c80400a00a00d400c2c040540c4200e02080408000e8450b00d40804050078030680c402440540a00b0140c026a070255003041c00091185d4801c4001e00d00c8120403003c024001f00c07003c50141d008043c040030917900300350070300702003404a4600d6660a009aa5550310b00d4500111081410703030103a02da420510b07070f40c2d08042245100c1904441a02c1d0494401c0c4c0004106844a140030391601c041e00d440031200c0c1d014400c0307402c20b00800703a110707000b2074010340c0341070150f4003c1d035904540140c01110115100c3e010030070b007409150f1490580540c49103000e42500e031440714459014600d00c0d011034921001503620010841446103500540c0381c40b5030340c1d05004101e801c055002800070040b41040780207095560340014038003803c1c0109003d403140c10000c1001b040c11070b10300440800e103160a0101004d400e01e60010010304045045400b183d0b046a4098250744031810405880258030044c14100000c4000341d0011610038444ca01c10354002c06 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 968148111 1250 968146861 968146877
    0x130204080607140316051818040203120901091e08030d020c0c06121f0512031b03090d06020a1205090a020f03010c0c020d020d12050d050105030c0105070201030f1b 72
    0x10010f1180b28100801402d0110601c1403202c180066070007254810b00318102140c480003c107440d00d581d50800b007403a562240c610001d24082a00c4d01c4481c500490099094030000b41004010a400307108440005000452078402041500340001d010b04001000000d550703802035940204c10310319000310285c910a81d07030010707008900b02420844040d0244040c0c808905180b100f49001300604401004000c241d110b440c10816410141803032007010304802040381080c0310500c02070590b00c1d00034849580c00031280445c000e8190340c000083c0e1f4a5084000c0c003910110040b5912600a500a0112030b020b0103091030000d0440082405902c2c81440008010301507070301c050041007814054008031034002d134500703110340200940c0400580c0b4566015103110310f100e9a2840400c0d4950f001c50310191104000444007401c03141c2c060024101a0013088050003542d803034500709501e80d4441e00c032541c0824404c00100b00154060b800410703000c040104c000428101c092588984995994030f0300d40003c03540 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 968149361 1250 968148111 968148121
    0x30e030f0723040606080414070305031902010f06030f1205043c03020f0d05120a02030901091508010303140c1005190509060a05190e01060e0c12060402091302040806 73
    0x1048590b44598000c440c02e00030140b408602a00c00d2801a001808840c01d10140340c6140e02c0402204005540c400101e0b40e4501d42c0d00410354010708404a05001542410301f002000b0301c2d01e0103401c0640390405071b121040000380d60b0398100f160880e400c48052010911000890050101c83c118034510b4540c146e402510480c11101000c02c0800c5954908841441d01400943c0f69004201c1418005454812810b04142080c40c588014085020540e1700c0001319483c001f03a010001c3c2c055403a0a80366071070070b80c0e00c81e0030080c035101740c06200200003100300004002003803180c0b4400c5404448d5440c0d0038580200c2400040c00c1811482c0c1004020f915074080c0880c06003821504440c040108004204d1030808000307554030703490054030450344aa2504045002c0000e000342d8508844040e100400080d54002a13103806412544110410524100c1c0010190714540f4201ca00c001c804c4139201d0600e540e40300c2004002d41104030002d8105e191510128400350b003038401040600910320081441c1c0c035103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 968150611 1250 968149361 968149409
    0x90e0304080c0d03090f060f2607030e0a02060d02090906030f0607120908130e0108460b011d07052a03120603060a0b0a090903120204030b0a0b060412030e030f07 71
    0x84004181d1502c41d6108560827a00011102d650003001c58500840c0d00c0c1070711503155240078840d14002c1d502c0080000e61040805880d1b00410000038161119155075a07000d0405888031204000201d01c3e42091000a404a2103400c0018035542c204100152040990300c540000741c1000c2e8003080c1e07548103000140629410441c00342e0042100c000180381c010039101c4160400e40e100c1d80c0c41a4090720400c0d002c017203c0881c00b030094224405996801031940d103414944410f51081c801c1c01d89050290003014480c12002c40850710841503901d8252900b0a1503202c8044000c03a01d580d0000701c0c011010f903802c12402031005048030f9100b544902000d0030007004040c107002e005010000d03400c0c0f800702141480d40360144084100e8030300d0300c00000c8815103400e081e00e107681c0450001450604c0058044200030446444d14010354149404001102c0b040041c020103124074040c03145001c0031400c000d00000e200e40d0003594013000140c103031840a40001501031500195810042d05154400c85514103110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 968151861 1250 968150611 968150627
    0x30c0d020d02070c140d02010305090708240108010b0a0e04060b1e1c0c0308130506280c0503040504020d11040f0602060903190309020d0c0f090e0304080c0d03090f060f 74
    0x6102c00703030503218200c5e010001e0f0903600b035140e000741403545640000f00b000d14184010001032070441c05952401c0149400e021020300980030301c03010703003e0750800032894980500ca514800305c006000c04111038101403200c01d04134001001225032545441ea410010f03180c3e1a8003550000c00700c81d440100d03062900c200421010780041040219602a80070400f254441c0501800c503504801c041e80c1e205034075110030583c9180b942080760070100006009021039030303001c40414403050301440c865584141d054212000341203880042c1c035a40c002d000c1032010b4a07055004046000314800001100d0190601000484e0802c0c2c0c4003002c50380044030f04105c210303014062a64811120b00c051803070800d51039490b0a01d00d80c0081c1e03200030513a84001040454481004505074907800c417400703a803013a0b650126002642f00d03a000e0b070321000d0b041040306250a00c0000907542621221000b1b807407000c01034004d0010001c070300d880903401c2100da01000266030100e00b030840003030074403651a2407030b18501280161000d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 968153111 1250 968151861 968151869
    0x9130f022511010e010c050303090a0b0a02090d0803070c2a0b21060609031b040f02070302190f080403030201050718080a030f1e030516081902030c0d020d02070c 71
    0x2a00d100c0c460000100b0002c0c1584140200342040c040300e5640c040101c440c5541200010f010344000401d0042e0488005801d145081c494040e02005550703002081d01039015004640c0e40004030003004a0000d000d45024541c0510513143c454072141c3c00b82c503100407010410b038003514442031000300e0314402d007442100c900c06420314004207450501289480c003044145000310f41840d40c00280454280e9940400701c440c5640c000b81100d4541d20804a1154111201410103100b20324040580321400342900a40300c0c405c3c0c06402070a02c0000c0800c00d020400c03600601292901c428602400010f49440080c2021b94043d40c000203ca2414040c082c0c4540c031861a14034000300c0320b0000300101000055043c0b0f6099241c94245903200310290261a0050400e824410036510344107032400c1c896241d803241303200c1c15410700040c15982c00d014017903a141e101134400c2c07800c0d44d43c04003500a40300100d800841c1c10510007444a40f415850727111000c126040700e0071010306a5000a0b1580602424940c0040a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 968154361 1250 968153111 968153167
    0x120314130b0919050d080901020a0210020312010e07020a030819140f0112080409020d09150917030f0705030408071e030e151b03090306011e080607050a0509130f02 72
    0x5003003a0001703803041000b40000f00007800002e210001644248692089240c7c050000b04101010303000294490f0022040030b509100b1500000441c0c44141ca410340c080c0c100d940141060700c1d52a20100c41d5400d0003800c40c141c007407001c00010080f08061041d1100c82c501a14860010304103800c1e00300c1980810303400403002c600c4191004011885c01c0d81242c0403642c101e00300584c1c82089400740005041142005400000149081c1c00c403402903420007182244518580b20928242041b0b0243d240015070300400b6449442c030006191a00a0004540140c054000c4900303204942d5200070080700901c0740041149003d522040416030000f44510316200216107580000c80006081c007868081d182c5a2000c141003c4003407200c40005008568100c00082c00707071407d03980c4a0303a9820311900c00321540d48280820740ca0000d12800c0208909016010b03590f2224a441c1e10341c4021506500300e40c100039800904c2d0103c40350629264841c07600215612000507031205d00c07a588000103aa2130722020015 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 968155611 1250 968154361 968154409
    0x1d0d0c03121d10030e0c04050901021804090803180a0b0a020a0809010905060c1303051207030f0c030813150c0e0f01090f12110303071a10120314130b09 67
    0xa9030b10f6410960001c012440c00044410800315550702d8000c002c070200c0d0708545010240032580780c1c103400526003203881407110344483c1d203000c05000454007031000250102c1c0042c404501d402024560b51f1520f03640040840f03c211005403181c282c03151059035026451a800184680e0b0b064202e03024643c4400e90a00810981519413546625444000d003884030701500010007403550507002d81d81c10f01654000301241c080c69000100501c103541b0085054010403040c10326820a03a20078451044c45e030764107555a416585400500c16040078280400300c80c10092900c44800502e02031080e100003e403103640301003a118002060204051050030428101302201c1030500508880c1c0c89903804451004800304148030290403e100607524000840e07516001c00190388050010504511400450040c010741d40d80c4c503510401810b015180c42040421002e1040090100780200e0302444103441c181ca1032460414945903041d0300e9085500701240c0e10101007036003c0d45052512242820140c1800352482e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 968156861 1250 968155611 968155667
    0x40b0f0d1a1e06040f060909181502030402040902100305040c09230907090204030318050405010f0b07140d050406031406012a02041805060a0c1d0d0c0312 68
    0x414010b0301d5003010440144000321612010222002880368070414140b0903151031008022100d240305055000782064501c010324207518401c41d0045500c01d90a02c5a440719501d280c0103904020000d0768001c2e5144802c40158555030300c070760551802903400288915152400821180725604410340440c036113188650320990071181500c00c0ca130364141e030600a50301d04580741c0c600a0550805411b20f8000b03d0300104158010702d0301e441046000010400180d114001c1c4012903a00348101c00e9008070b202003c20070064480000c0c002c06004040c1d0b4850600c0040c1c0c200e1074000005100c10015100003000c000441e407600c15401c0c158140d031040c0009041c80b40000304071541c0380002e104019020700e50021600361841e0703000c0103503074042c00070301c4107241d1454410408081014243c400c1d00540001412880c1c0c544a5008040101d8461425040f407004445408580c4d040311903800c032194144603004500240d043d000110f100c0c1d90540849109240010200f8444114603076056a162823105 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 968158111 1250 968156861 968156869
    0xf140f090306070327080d060801050f0c16060b04020702030601060f1b020a1401020a060507030617030c0607180f030f03020c0919050a060e0a0b1f0c080d02040b0f0d1a 74
    0x18805981800d6480b0f80c450780d003410401403040b8400c001009148c03200005d148041074001034402c40012607890b026a0b900d4030b04240608c6911401e00c10102025487c0e1300041090b4001c5220240150005051a1003640405d1516401ba00180c011400700720350703a0368582e444600c450148901c5104000740500a5021400500460007003001c5031050160204aa074800c11a80820075000101804030782865074001d401850140180e1844400340c3e6a185e04e003240020480b1141c031002c4000780080d0b034903d10119040784510404040c0b5040d00c1900080016003000c14001950180300380340c1d080d080ea460041c0c41d0aa0b104d4003280504a00c0c030401c40c1c8100e01c451103170402844400701003680c1e6a0081400001c0134503400070764552541005107e09c1c038034603a109440020045d1101c000d441c0d140c000a5142180d000e480c0800901c410402c2c60028180c50087c020103810004058207103034885030203141c0b68100320703214003400b100401c004455040358007460150901790030030380398618a580085 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 968159361 1250 968158111 968158151
    0x5181c02040510050a05040506030a05160524160c05060d0605130c08010918020d080a0f020c030a1401060308030723030f0f071107090e0c040e0d0f140f0903060703 72
    0x81031240d623440300042c0700303910300703001d25510329034002c0a80c0c1d44005c141490928664440c01001c0c0903a000340001d01f808641c580048141e13068420039242040c168103c000d20b520a04442202c10442074032000405444a4000c3c01035a082290007244150400d0184048046000201d50420f800c090254110350303040b01009042d1081050045060018402048010303011500003d40040304176015505100400002c0c1c100c0e0a040d0b90741000d4980755800880e40e410038419402c0e40764101c002d40b0400500c40010155001c0b00500010500320303078079115411560811a804000310f41c00a54070b51086c51142e0030441020300c0c20400d281142003110b9000c00070a001007400380c01d441e00311b011498544c041d414100020403070008881c029900c0da4009000b410f500c508404440c0f0681c02e1280061429020700750f801003141c4000e04503a11070207811541d040c0c5a40c840014002c140d5421150080e00100a0804a610000b400d0b80d5001c0102407524160000f050070080526107800485806029104 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 968160611 1250 968159361 968159369
    0x6050312180105130b03010b090907081b2209020304050708070608060d1a04030e0109050d0f030804081902030715021c050c09090a0b0918030a05181c02040510050a 72
    0x1e03480d4072131041910400881c40d0000c10503181d02200020b80d89001200604407800c0c151390f0015903841d5040c0c10740d0004030684402041c000380c03000c07100448601501804507010f070540b0702e0a20a0300b40850003411085a00b166081940000401051040802c400401402040010103882c0d2504200604400f4082c20350f40c803c072031007030881e03050010301e5100148102141b110071000c1e0500b8500580010482064140880c8810000050700d03d000e04c1310020080d0059003800300c07000540d4048411341401001211240410b0140302018412050f1841d01107099400a50b078521182c10900c804108401070b101001e0b004200341302003618060000d00d01c9240e55800841c007504d540e216420700e03002d83d031f4a081d08212954200315052131250040608210709580403101510f90355440d0000504200704090b65500401c412400d041c07241c3e0003030030700520040d80c00c4c04250700d502c00500c1c03006980c0e40c0d103004015201e4100041d80350a105090704607000c0c0314030741c0203286010302285040a0700c0c81 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 968161861 1250 968160611 968160617
    0x10807140d0f02030906070e0a050303030a09030201020c121314060702100201060503191101030e0a0f050a0f060507090b04120b040602070b01152303150f0a0801060503121801 77
    0x81c0c4024030740c4080e0490440c40b516440c082d5224541110000c1e076607441203a48070001440480141c0c202c3c1002c0d0f03042c00c241d60300540550300c1c40c1d6403060100054450b80404404540d807c010319403080c0343c148038448101c8141d01d00203075907180c450300c078045c084204c4c2c00654150014040301011951442d04a5009503816220001d10b4403591205078010102c0d50701c11a010301452a00c960004018002200000d202d0400b09030f80705030440c0110122010010040c403241d011700c0304403000c0751110f40c9000a4034442d008841c1c10031419641d415400780801d01c101c441c180c0307904c180080d02c0e81044a84001d02515102582007600c0c000369015415081400074005050711004102408980c0d01116075207a00001c42d01030b035503510150dd4280c0c0307148040d10381c005500c502964841d407031030300501a58056a000c6583c20758444ca1141c1900307080000e0702c2036019038455a2601a13450743c00d0414002d0803000700002d4443d15210034142809481020140000300c01c014880805030500300c0e045083c1c3c428a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 968163111 1250 968161861 968161867
    0x60d0b100b0309010b030f01020403111c0f0305030609070806090703090614010326030103020f0618090c03011e1a130b04090b0a0b030405060115030902090a05011401080714 76
    0x5119440300400c40d00031040085000040000524054200b680c4500301501207070076180c25090103034201c1c05940002080c4c038540001101c054a055044440c0c2e50710684440441028150384080002c04200030407404150080b0411001c2c0c6801240c55502401c40d04109005150100018100460041c2008141030f40c82c0c1c010000d005e5290702a90416803811805a4507503100d040031a01c40c0c0455000915000c4501041400c1c1018242903174120780c0c1c080c0801d040e242c0c04004220640e0804808070100040b2140394550603650100168080c00c4046101581e17541032040d24504600c0850207000b0400742036404200011002840f600c031800d0110324291a2511805103030380c8a000741d44051201c803008500828648034990040d07451000440d642d6030b020303503110200c5041380001c484c0a0880e070811401000301c00302c030a1804040d1045440c1c0080c2c0241c007a0f0011b05040c100342d4107098040d07600c0340140b02109030030b401c5290300c05007400d00c0c480b0f0b450100b10003414904400040140c0b0a004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 968164361 1250 968163111 968163121
    0x807140a080307060603061d061b04031b0806090f120a030f1e1a130203040201090b2107090321120608011d010b1f02191202072106020f1b06011805060d0b 68
    0x82b0041d500696400807510326071002040c00b00303414500900900c9810301a04010901c0803500045810356560b840014295180130300c0001c1d83c0c1a0880c504182c145900c4100c90541640c09108481c01600400300c0a0307000d408852080702180e65050043c3c0340c1c08000c012480882d99540200000c65040a2015980b40d03038500c0101d070032031140e6010f08207142012805802d944605c843d08840e1100e07120783c03000183c0d2900f904031a41007482c48060703c5c064074950408000803070007044990003812410000007001e5503030315003004c41d101a8010b00d0180d42d9140856074042d03440c038010891019a074001d00c80c0c03540d220006000c0d18400c1040b20b8100c7d8541c80d203051914000c2c02284001d9400da4112800700c0342500707066150002e8810050018011100003207a2020380c07842d001c420040c0f04c401c101c1303818165030302d020082d032181c03141f00c40c442420302003100e04c0124010810050103019011300090351400c4152004403080072241d84003076007418200691a1152040803c00c41d4008000a00715124 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 968165467 1106 968164361 968164411
    0xb0108060a17010b120a0201030f02030f061c020d152318010608010219140711040b01050c15070e0103060807140a080307060603061d06 60
    0x100c04002d0007160001c50041c80c4a0502d5000099040d012100180c80c4030300c0341d002d0f0b08180c0c0c02540d1180c01c40d645405a40d880c00d44590081d415405d0050200d062041c0080c18107008010b43c444910081c292101140f075000d40160a00c01c0b401041d041c1111400c4040c0d0000b015141819030800400010707141c3d5409a00d080e0f00700c013010b6141c0312840c0d8030101903c09480c4041d03487d40b0010440390000c2c03008251000c28000701c071741c405a4085010b03001d05070450004a05031400d01c01140460504101c04003100303004c03a00040c4501040d001a134160090031001c80032481201c1059000d054558071540c011203d50301c82c00b0807260150011030590340180900300d01900004c03001c1110300b405039840c50910a00408041c000c076181c0d14440c1c42d40d0008141504c0c0151500c5c801c200f40301c0148542e00640203403a01c0900e48039041901c0350b80d914000380c44c1c08910803440040060300b0032 = true := by decide +kernel

theorem cover : BRFrame.Cov 967985611 968165467 := by
  have h0 := BRFrame.cov_init 967985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 967985611 ≤ n) (h2 : n < 968165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
