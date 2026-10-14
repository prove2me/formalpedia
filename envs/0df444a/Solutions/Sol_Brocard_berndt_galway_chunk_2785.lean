-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2785
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:44:26.990073+00:00
-- url     : https://prove2.me/submissions/9e6d4cf8-6c96-431d-9e40-f5b429b1d2b2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 500719424 ≤ n < 500899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 500720674 1250 500719424 500719433
    0x10e1510020a1a060a1206020d0603030806011803170c030d1a1305091203041505010e1006210b0d12081506090904030f02010e0a080705010c111213090504 68
    0x118071402c1d02c950081d800203288030780e2aa18214046452a4101d0303040a000c020641c10000036600d6140601001850107103c0700f9410203a982d03a0b0415000705030008207000303507964001404040103840c070740c05010841c159941c06815a41900c20b05008040101f16403010100500403581e00c04100c04040000010440320f100410b5001944c4030311640c40d00c84426544801402054890b2207001c000d003100705141c0c14240b04030b801c00740003519002c4c4100070041d4182503510485019103e03c8103407072201d01d080c500540cec2c00c4229810480c20084201d01c1c4400d84903003061540380d510008240400c60f0644000455011052404094020001031081614883c0c202c85514052010500d0b0140c90f651a44144402403140b0b10440da00282000005804284204140f4040003581d2002092200002c0c1c81070f440c029400340d06840b5290b001462504000013441950b010340000c3c1480040e440d210b000b07560301c0712810740309000c00c0000014400d45000300d0a01d400c01406c0c021004111500b80740c00c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 500721924 1250 500720674 500720683
    0x3305090a09061e0806040b070c0614010923040b04050a08280e030a1506080706030b0918060a1a040e01020d0501050a0f260102071202120a08010e151002 67
    0x80e114510510200c07600c04000c101c0001804d07583d81100418040e240e6035244030041e000102034601b0030070050808000110140181b5150580c0d80c504010700c0e50511f48000c0c12511a5105038010102e600c040044426080c501b4680c4190484080c24041e6101d04000f41094803040c0010580c4200245c001440c146501032855a0176001d01451040000e410043c1e440c02003226080c1d52560009203c1d00c009101c07241d030341000208084c0c0118495984a08591030071806810000200391203082540342402c0800146902060f0ba202c60381e03249020280841d11550b0240c4161002d5445040c0289054061441600110b0000d01b04100520500195500075004030306404402400c00c2c0000400d417400106041c10b883d4180340d03c3d0052890542c00c2c00e20003126241c0348a0812000240800302d032428406850030601a2a10548602c00464024109481482600c0791030341c5c06c2c016565019400b19481d410350f000105090f400340c44444081c54910500f05c10242c0c018039030000000319a0340480d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 500723174 1250 500721924 500721929
    0xf0506210c03012309030f040e060307080d0c0201120c09060f022a10030506010203030106200304060c050709020f0d09030e03070306020a0e2202071719093305090a0906 74
    0xc284056210301703580e903460344a40044100c41c40700c00e20003403048001c42c40116401250050444200301d81d42c40d212400c02c072800d06202c011942907521072080d560064207441c041344020030100810080e019020f80140200d000d0842040a00d001a950681c001c0190341030884008001c42100c030399200c00c03103c2080d03100030500d00940d42caa0416910034000e003e05070044405070003035810750303080000c205c032100081101c01a84100803030034200f0000d801d00050014240f1030740c03036800c1d60f40c00381041481c103100c03548600013903441080100300c09880e107000d9904d21203180340040355020369404c00721b81d20540c030302580358107000f08040042044510740c0148002c1d80151036054414119104100c8820941c41c0741c40346591071104c1240c0103041540c003c2c0705c0c0d03a104007511450b94041081c9414981c1018580300c07440620b00c4001e001050304103050800511042c42104400171030b580303801401030484541403580003105805031035039500030010384015410146c400000d840c0e0f1802074502411462 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 500724424 1250 500723174 500723231
    0x11030705030402130203010b0901110a1a0613020c0303070f02061b1602100c1b0503100234061107030c11030c030a05010204090501050603040201080c2b050a0f0506210c0301 76
    0x1107010b14101d26021803d2233003644c200c40b8035640da034041034000d1030000005041039800340b00949000c5a105491010300124203041001f0340e102c0ca07040c1c00141402000c0c4602800f07541c00a0100945400700c00c1da100315440703000201c16102d64650080180301607485200a501112100d00412601d5101881c1c132040c90150707040d91301e60756003240c11200c403030010300a403174143d0080e48070084195015002450311019194062421241c000300070801c000c0842444000814484014401d10040313024491407280c80c015130600d00481030743c1c064580004070500420321a26011020f03226a030900112690103000340503103690701010f01d04030b8002c0d03101c1d00610a02d02d10f8800046058180304080d24411a07040c1c49000f0552200c1e407000c1e550781c22600441303c1c40c210760f006680100708403280303246519919502c04a4981010b10300d80307060781c082c04030400c8805e15283c200515955007074686c0b20940c0c222020b104124200b401c9160801c02e2000c0801d0b019030910600e550980e11014819600c000f82 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 500725674 1250 500724424 500724437
    0xd0c0203120c03011a1c0603031e0f05180d1e1401050603031606150e04060b0d020303090f04061205060403020706020115210b0a02041811030705030402130203010b0901 74
    0x3911054040c0d40070a0003112008188105c1c5442e042650380300410b400d1207101c2401e100440b07041400e001f507403c00d4000301c000482d02c00061001c507810300c0740300034040c415041411008812440042c800e0003170f0701304c0610030811203400d40240c0e00d409520501061b0043c00c1829000d83c1808d07000110707001e2a0301110000143c41e040c544683d01841518040d02e801400340d0310300000c41a01c2c0310114003000381034035a2070b40c03802078400e81c0303036040d03104c00044c2003864003961189007500b01217040b18801d101d2640a0f04049040500603500803040300e81c0200121444200e07c983c82002c06c0c020075054020392498420812108140a00020b01c5489603200c2e40c201c90300151a20412403e07610400d11186118601c9030042c072075000385108181c440110081890040301d502d49402d1320150741500c0c464001da50002e0207001d80300c0b448098a24288541800340315108410340b03600900c1c03000804001c00c003e4044041000c40d620358698117503075a0181303c1552656140d000302d403001e501540380710707021500c1c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 500726924 1250 500725674 500725681
    0x405360c0c10061412030c030c01090c080a0210030218030604060e06010815040b070c081c0b0f060d050a0605130f180206120703110408160503150703020901050d0c020312 75
    0x7020f01603942503808a01d0044400c001c010140021607100962440032070100344011007800c0801c2002c4c090315480200041603041150424540114890b0030101c0560000d002c00400341c0c0314400070444c0c183c01464010707a110b00803483d2501800680804030b0f45030003010140801d00c15542c1081d5001c0d5151000d82d0a81c0c0da0303a2882070b0340c658000134a46107120a160020300401c00900f5001d078020528200079802d50240d036184e288542c05030391004c0040d03088800c00840c0d08410710404e030101c041030b64070781d2900410f80c00144071401882081030009031540005510103626030018801450040e080312860754800c06580c001d0980c60300e16508075403500d00300080000d83c1c51041183c0b03d07006030185240902c082200780c0210802010300041c940c41e1800c021201600c1401040204800409054032140402c1d03410301c03080d0039502091080d84800706500001c940001c0c40c03608151103003401039552180c500140d620f40641c2c006d200b1b203d45000c01802015402000900c4006c00e4010b180d100c0c5d65 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 500728174 1250 500726924 500726953
    0xf0a030e040c0912080c01020403020402120a0f0c050f071115120c03150f042013080d022503051c11120d09060b0a080c01140405360c0c 60
    0x109031280e8100d1030200c1044401141c1c5910090507811b80f660700151406842c3d40203d01aa44038801c09000e2041070f40800001000511545422101e600784c207200c0f40403e10340091042c064540060350210f800615281003001c81000c1200c0d0020140084100307441800d01c451180d0441124800e0310100b1070b001a1500e0340e4242103e00c118003000344c0c2501300e206c3c43c050287d00008440e03c02d0300665110f4942c48401c102c009103180301c046508080341d503441807461401183d0000d6100011650081070400d5034260089a458052043c020342003040740f50641e4101c9140b11703d0740c406446402090651910034490b0104a00401c0e509c1e110701d015404050350343c0c0d540309036880a130065a101800140321310112600040c81c050b00030b040218024070424002001c0d02400d81c0030341025031010341c813105c2c256081a03480c1c18103040b007482203051914060101f02028030302a0000c82a0010a40c541c110144e20101980441049075030b5011038681084000d405601c00380e0000e00e28480c0c1c144000484 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 500729424 1250 500728174 500728187
    0xa08070b07020613060507050d0501170c030102090d02040b010909090507060f0c0c090e03040503010e03031e090703020105091f020a020109090e0c060a020f0a08070317011211030f0a030e040c 84
    0x4100300070321007500b40c1d02c17502c0e00030080c030700a000c1c6010000308101e2030000c4074044c05030f14060b240e80d100012540c0b49802c4998904030900d01e506000c0d9005002c1015150340302c0c103010010319015140415100c0400300121804803003070300b08140c000d117070081a20612030b0020700602911500c0d10f42d003407010021034050b100120400001400052001d4007841049610f41003481e2441d080c1d01140d04181d00c440c0004c0c255000003084c1c0c05682d20100030440030b4109280c0080e5501e0320b0702080212800d105c3c0403992a280a030002905000002403445400e4699100310f1022400031040d140f40c1e02c20708200251a10b501100981c0000d00505010035801c803141300e092250341e4108014504e40a22000384405600030200c4407003517020382152290b2041003800a207595a2240c3c11f180c1d40d074a000e02c0c025000d01007103403240c00c20b860483c0040c01102c12210703202410a0704100624400c01841c030009140c40c810021480d0a80a001030901c101500440c2c0a542c2038000c94042c0558842080120380b80c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 500730674 1250 500729424 500729431
    0x121a0d0c0e010e040f02190510031b08040309060822060203040303060812220503030712080c09090727080c0301050a05070f0804170a050a120e0c210a08070b070206 72
    0x40b10604217200c0f0041c509911141c054056800129417169920302c000740e5490b5044680101081e200d59003806c4452101d240010003079250304000c0b0503410f060300d004203a2000703406100d052180d0500810000c0081502c401070308200c500d428181e03c800340c03402c58040d41042d2421030110b41484004100300c0c101103407682c3c411070b60101450600004c803424001d400200500343c68904520320000c11140c400703200a094440c001d649040500310580030042034a030340180501c40c40f4909020301100750361007450700e42d013040d9980340c042c0014190080c01070015840d4800d60510390007800300022000380c007141541c00034800310006c10840c0d441f0b50307442c41500c20860b10f110014200650289490780540d6847d034005014010150303044410065041aa601440482021450200f0000c0307000c0e40c070408886038040041c07024485010201c1c400390340e4400341c074560f9208122040c0d006036800003903000c0d00741c085100c20494880c0c202074180101180c0c411007003a50420803020001e40f10074000580300e4007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 500731924 1250 500730674 500730683
    0x18010218330708071205040e010f08070306020f0c0d0e01032f0703110102030406051009140a0515090a0c14070507050402131203200706121a0d0c0e010e04 68
    0x280d40c145607458100d154800c48003181d50143c1480a0b001082e500505002c214055490301c03a0b03541d0500040c0901e04d80164403c10b1030ba40301600c1404071410100f0904105d960248000d40c4600204000d96941e0103010095092481800310030705200794007032403562440c0f40a80741009400fa042c01034541c070b050a401c0c1b00804948690b0160301d0740020f80002c00a250292401c0c400400d00303c0d100a09980c8159025038080c2d4403801404420b208002c02000140b80c200c0041100789640c00b101e03070620313800624409075039030f81c1c034000340103040c0d499020010722000800c00b0b401c5141128040009000c0c840fa00300004241c03000049803103444104461740550820020015140790100b048069803068125a8604d03804080c0000c0c005403c44004403074a10a855540c4224131280100688042002080c0949da10018080083c150045100f980311030300c1e1440840d4406243c044980b105103002e0030207130411014007008092000c501004010f90300045100425030740e13510154441c610f4281c50150 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 500733174 1250 500731924 500731999
    0x3090102070b0c03040b0714060c0304210509060a091415070807150905010b100f0e0108040c03230d0201060e0a0e0705041109041508120318010218 65
    0x301010580c050f2000b840d8403400c69280c00d4403550304a1154000d50f000b11405900202c2103101703128140701c0726a000d000d08144a04605c0c040c1c035005004241203500c00317000d03078010407140030300c0c0e20541c00c1392103101d805010142d0325807070b00340024210121441041b5504048000c00c20b81441c0001e550742c08080b00041c90340c1003c0541d02c80340d8007a40314401c1100c1340c800d001800f450800c0c9500802425900400000a4000c000c2c81030040c01c0003440c070b103441080903404504040d940c20003855806440c0a2030302d5859959a482c0040d00041181c0000d0308110140800301543d00903071503c0001c01582000351080d1001440090f4280c40941c05200020f00b140800502c29511030b502030072041170044101c07250b4070b549602040440d8100141012082800141005070782001d0040d0b68148014803080720955141104076601d0f40c030120200ca19854001002c102620750105410384028801002190342c1c000c40070007642000700556025018440d50b00300209088108580d1448940d440c44514 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 500734424 1250 500733174 500733179
    0x182e0c020f0d0218090a060908040e06120d12150e01080d050708030f0a020d11040f1202030c0f031608100e01140403050c07080601030b0103171809061c0606170309010207 75
    0x8112021000704944800d10940e801c1b20003041050140985482c0905070341c0b07680300c1c00e05032800200080241030500820054105c1b801401001410903003260003031a08240443c0100e200d000601700ea00402800d0f406280d00104100360040091812101e03c4412910740d80b06014064030240141031014281c0300c02800026441c001429015502c1041c04400602d40301c00d124000e02258400380c40c941c0201004601401030340f0307802c46000087c010411460803514242e50000355a2035505040301e0145020307a1400c0c0382d03501c04005201702d0060640b0604007040d220a1150380c2c5200442100020074206a03c000340c802d411b02c10320702d0070300b014440c4c0340283e6115242902c1c5548803080305e61003445014000948480b0038019107000c1d621030010803a07294918142a060700f0852032800c0d05d048000c111042c1c0c041d4050071038016030b81042d12600c481d5503400000402080d100b1503078208030204480103404104a1f81c1c8600305407400f12030446211107080d0b40075542c1740900c02401d4056803014405 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 500735674 1250 500734424 500734459
    0x80106141c0303110d2405040e0604060c1701080309041a0d02101103040f1503020a0503150d0b19050a0c0507021509030102161403182e0c020f0d02 65
    0x290136003d41505507241c8140800000100d07410224601044805001140c004404c04e0700d25400a0100310f90504c81ea01020700c0303154480d14094002131400b5a2134407040f000320301a580c440d01c1540b11004000007580c0d1141c0d09600d076404078401030310541c038100000915405511614041c20300103403181110f290160700b40807081f13107400d00c2175091026107000d140c464901000281b000e0700800c900c2041c1245440008000c481600d0148414503005114200400d40e002095a603c002c1e100d08055207002010041a5007002c510000b82010300c04004210325000800780c5960440503507a000c004582d00e81701c4e80003c039542c01507207500203501003211801501d8143e50312a09a04003030b01a9142400c0800003a08990201e01d007900d00d46107011404050003c41601d400c145c92402000d0342c90070002460f040d070030302901004a8416030b01044019500d284007400d40e91031141c5030000da8032601756000050442c106522040f8821400e111020009051503c15044032950250030f2070301d0401c45121 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 500736924 1250 500735674 500735681
    0x21040504020c0f03030a0b01231204110301090c0518070207050f0414070e0a09020a0c0f03050720030c1c03050a17010608011805100b090a030c080106141c0303 70
    0x100894610400016900050f420300c011800b84030b9204001400701d01d4180091700c07592071781101e04001e8101480004280b000302d400c81d410024910140c0072241d5540c0b51221442200203541601036180019a10410040405103000c0d9038084a100802d40010f240801401c003003224140010303000b80c0c82c200b006041580402c01d030608002c01c01300c3e00070700c0001c58816011003100c012000612200001e4a141400d0398240d01600d10140107500e82001d220014209101400c00107221181c460464814507110380c1c00d9403d1183d200081d4a0030199558070340d295641100c9042d0702c64003d168180d50145000307401e401c1c1d01000150780113014030701034500341d40c25080b200246040c04800320441062400c0c00400c40d000e401c464a500201c0e5040800c0c03002241401c030f41c4401440e20300700900030307a02c1c45806282d0031112041205555204544041007000c030490340300030105044000085150300064000900341c5000c1c0021222480c6080108030100c0c0d0403c0c12140000d4100000c6008244684c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 500738174 1250 500736924 500736937
    0x14120c040c0504050d050a2f011407060216110a08060a1119080403022103130303110708071101030203060a181803020a0201030510060518030703020d0c06022104050402 74
    0x6005040135a02c03008101d00003d1304030f00700c610f038100c1c004840400a030b1405c611407507661088041144e000514003848040304104460f8144603000f041c28420503960411200d0050303000c0402d540782c000c040082e80c0c0f1541e080b0811200c02e024002c48944a007080494441100c00c2c8030014082c9481d1003500d40300402c1d01441042c0080380800c25101e04102e10110081c0111865940b10107600d0141002802c010740920080240d00c040484202140c59180680303800051000c0d900b642040d90340380c1503008002221071400442c0700420360750240040c410162540500400680c8002c00c10000110f04074801118a21360015200505200e4052a45084000da10118030001000380700002003690501d07420394200c0c01688403000c02021542e15004060b003111618000c1d03144036003003060142c0f5074010010103083e013800c9008100b00642d81000801c4c011074000e0281548844a402c0c601c8a90040d8000c500c003611400784103808204168254000d07104084039040d0400c6d0500040001952149 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 500739424 1250 500738174 500738177
    0x120406031503021f0914062517121b04120f05060406020711010c020603060f0114040608010e07020d0c030e0415090b1003020f0d110d0f0614120c040c 66
    0x811000c0300507112400844415410072406a00c0c0c0e0460060003008584207030090400c600322611b800c00340c2d0303d8000a9400d5102003c0b00c2c0e00c050b003041000524441e40070300015058408442d500420400c0d0340000340740c130302e50800d008815640c9003440c2550008041d0110050a001003104021481c440c010300544c21348100d440002070070440d10303418907044c0c040c1c40c203807401a8009074440412000002000000e042802d041c000d0300100c0e000900300d03000c01081e09002d52180c0e4000746d0b01740c0c4035483d4005215501d024203500c81c1d0300d411008003981024080c08188001800103d04854000901d8010103c2c0c1561483c82c1a00c0d00e9500f00c07040802d60f0380d50303904039441c2c1905030950310840030700c000a09101c240000d854481c101c00c0041d2800c2c010400f00c01d05204000ea07050500c2e80c40704813a047c0100c0c02010030303102c1728008003002920404040b1040b080c601401c1c0890010150466030440b94034030941041d1f61300751002c000c400d801c0c1c12031300001a03020310403da8860500e0f402000d00c0003142d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 500740674 1250 500739424 500739461
    0x70203120a08010501030f050906010306051003061d06070908031c020c0f010b040605060a09030206030c07120306080105061804140f010903020c0405130b131121060912040603 77
    0xa8104002450704100364200205101c240180030303e50381845802d2a881d1160400e00003401c003940c50b41c0e00d42c1c0303042c08040d2240380c0318400222044240308c0040000c55200340c040102000c2810003100507401c0c40805100c5000d103102290b0076a12944000c001d9030004405903152a0420f44032081c03070b200c1810f21690541e02030054290644c018000424680c24940022494020000c104030840d2100c0c0c02040c8201e40901c07443c211a6488203c00080d65170540d40307985c3c2c039121074114011500074500002c110790a10100010031543c035802c9030040b908214000d2090751510380c100002e2aa010510390401a96000058041450000c1c0085011400c600b99022200030507078150070341c0c496880940c00350344040242d00c40c9092500c0390542c442e490f501441c03140a83c1e9038404401c0b8002408280304c40f0807101d001828000c0c005030032050558010010103111640303001240d40100300008400082c01448002628890041180c1280458800b0180d15040c144603040e0010030030b0442d030042c00c002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 500741924 1250 500740674 500740693
    0x305031215040e0307060e07080c1c060504030c0b0901050c0f090d0b0a02040f120206040302190506030f160e091b21160c02060f0d150b04061d03060c070203 69
    0x44a1040d14840083e50303000d5030752495079040000a82c0c0302c10301c286001c1c0e80101410052242c002c13400c6201c445080700c0d504d18281960810901c50700025074003070009032074003003403004143c0c00400006009109820480326a556206090700b2100200d030070042d640e100300104c00007141004028010f0440007800102c0300c3c450340d112010307041c401321040100d107036000809100d0f00421907081d01c014041d84292f85200c29240d8003145c0140150b00c8000d00400380702031144000c202c90403242000e0080a8103050b141d142070f0420003001802540e03044140002143c607060a14442c1050781c25012010700202d226844840200c40031641141034460800c9080c8001903294400c9000c03901e42010580d01180c2906010620300035207004141c8000502858819213401600d40009903104012002091038079031800a00c580094100b070b0b0300f4900c840c1c0c4045004200c3e140c1140144c01a10015914004410b02d01325041d20341e58040501070741c0c994402c10009013003010030401406124806000c0e10040310 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 500743174 1250 500741924 500741929
    0xf0212060a02031909122a03020a0204060b09010c081b0604050a03020c032a0d1509121107030204110c03070302070e070c111e1203071b0305031215 65
    0x6060740e595140e20b40020500c41180b9810791001c15414120300104021551907540403144955014108140042c800030640458815641c004485415a20560102150745802521518082c0341207208e07901c0d0140105840700604161040c0321010386410340501e280780c82c2e001e52070300141c82903200e505001401c0d909402c410b0101e103009500c5003000b0070480341e040c500a414048903542550080d030080c00c0b03014080441840070050690f144010340c1c104540040031174401e00ca8048060800001c403503e140c41019141d125450b0715005000307a540181000c40103c441030000382d100001c50344148001d10243c5000d81c01440c1341102a0302c1140f4000c81c000640d800c60b04205802d901680140c001004070350081d95400350f01031140d207405920044150341301c4040011a04c0014000e0340702c00390031b0100111012814200f4480145a050849054841c40e907a95100b02c0080700e100c0c92108006c82d01c0f540c03080c000000d885e40310000d5414103464100380207000d40c00501090300d80b140d40710004081d8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 500744424 1250 500743174 500743183
    0x115030e0f07180b03060c0d020c0c0607030f08090d0c060203220b0f0603010207020d03080612070b0a021209010c023d0305090d0f050d061e030318080304030f0212 72
    0x81240c0d003010404000401c00c040104c4260000381401703078105400b0040500310500889081070014900140c541101804152802d480880e00c143c10000c00200d010a251304030780700d0320406003540d8030801540c0c0d99218050b00c4659118201c8003050b1105454030000d0007a40103158022130300c40081e0401c0449a14800c130740700e0300c0001079030f94a52903010301c20104422101140e1241c4154002d40c601020380c1e01240e4807030b896449c042c00b00b0620f40d0124440c1e6035071000003001d0949401c112910580c5400c48004d0076404809400054801d05080325501c684135802e40b012110161210512581c09801388111b020091024001c603605405241c0362004603036000d00c980d02d40c00b1900352291000e5500160483d074024000f40141e60050ba070100750282e00003145024181645809500d4421316140900a80500d8024174410701e040780d0360425a03c4c0300001c2c0340841c0d0190f541d01c00070411a400101c503058960041a034070703400030131003480454050b070031300030200d440500350705040c0100c0e29520707090 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 500745674 1250 500744424 500744429
    0x7050c0a06180803040f12030509090f060a05120d0f09030507150e01052a010e0a050607090f030305030703021b010c08010f0503010e0309090403020a0b041203060e0115030e0f07 78
    0x1242d080101980c0d030b481140b26820150101d2002980f62a080118500c41c2903075620404c002000308100c0082014428800d40301c0e080d030b001d4482c098504203049200030001084940758069402d9050000f068689032200501545094003d448610380110045407400040000758060282c0500000009001003005000070280074a010134180440707540205800220f00a180c10030006004440c4c4001010444e00e4451003a01d5032140c4441d28609818054918041c101c0280e0145001c040d05000010550714464040c59072458030040c6c4881a0400000c410b01010380009d50074400122214080d81c0100b006000003551100d080b104449082d00f9078a00d5940040000c03458801006121241400303940038080c11002841071164440d402a40c80c003c0c100d600e8415284940450145802071001e10700b5250492000381c0245828100195905503200c0e09400080c40d00cd0001030880b01090080d050311040818403050103241d41044001d0b1803600d6656a150082c0d1080c0030742c061003003102000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 500746924 1250 500745674 500745677
    0xc0c07050a1503050601030203250918020915270a0f080d09080304050102100f021b0604210905010c06110331110105071502211005060f07050c0a06 65
    0x100e0441000c0b00406a83c8003408290500d4014030070301c40720040e00380340400248031040f200c402100d2038080c101d4091001c0d90012450440340818003441d450650010403100c0d0058a105407454404200c5140900c900380b01680d01c10040258003902905001e0102c2d5520401030034103120701c1e00c40c214650340d40e500d940013020b190b000013400c06216811409460042102d03030065800c0a00d4440080e468400001e0b402e00da89540b44401e214604456058445c6420b250b2110082808481d600b65542c50099400b610800812289284245446420740b0000e80e869a01c0d8841d80d8900801580d02d40c8140c0e0044600688620061a0751311081c8040c40c49603100c008480c04107a48461558100c10202c034200004200e0500448041074200012405241d0700b840e0080c1d0300e5516041164030403c0d840303403041920f400051000401000701c0041102d461800054035601c0d00d03851003195042c480b904c991a0000b006000386c480b114207003000741070f0f654013810668120000840000f50a00f4441e0803c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 500748174 1250 500746924 500746949
    0x152c03010c0801060e011106070e0301090c0617010e0c071101020a050d0f11010207170a020304180f060503030304020a03060b0604210308072c13050a060504150506030c0c07050a 78
    0x130141e944085200c079202001e081201300b00c0c80c0b50f42d82d5a228480205240144030103209400c03803036203007544018600c1e0b801c000f400000a443d50700090802e180a03070710010341000d410000c16001c142450b014001c81e41c1d2914107180020b01c0e5201d017000b9807070295040c15801251240c2020590611070100c00c03a013582d88043d082504480003400365010515080c081d41c0c41070142d100040c1003100c0d2074074108803840c0e030540c1b02d0214400032480c5202e290132582d050b08440c920b01d42d01a00b990010032240940304001d005440c1c07075005155981c0001c503400780d8040c070300040801c0800c10300d40c404141e03c1400703003401c1e10b8591603c10184010441084881429642c8224a010300d91302c0b040a58004900d4a40540041480c03c3c10341c04030010800407008278081c4242000c050b603641044148244003441c4203102628202424000901061140710700460401081000465a1000500070b8510042c089815603c2d401d204482980025000e0015071051060208080c2c0e1285000c038001c2c1801c0401c0c8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 500749424 1250 500748174 500748179
    0xf3b060f040f0e060702010b030c0f0307082b0e030c1005130b1e040e0705030907031a0a06090605060a0302030a0603060e1c08040b1906090e0d0801152c03010c0801 72
    0x1c0b403071301400074180e50840e4501a00c091269802240401c203050040b180d401c4020381001c00a41840107940c0a150710340302e0740003051b03500050300d60303943c4103112040446040503600c0c0310107441c9101840541a4036820500012030304e0314210401003a1a6042c1c03622504248108040203d07120301c6030840d810300c620101c3d440b111005400e155555400580300058106454504100c04004000c0c040c00c050280200000300389110800100c801540c000c5159202c048c101071902c41841c000b0390b0700c03084450400c80049503142c5030b80102004c03604050f10310392420b007500301e0840003074001401103405d140d1900c1000000c20100e024240e00b40030443d01601040d88030607008007071111120003180c28040824200804501503010340c0d40e02240d13000051101c580506139203001840340b5003020498070300d0003204501c005000283c1e00f515442c00d8885421a90f00c4001d00030004142c1100b2400003074090015a450641e0b400c200440c00c03070203402c501c0308540d000000174207455852040b040040c5418004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 500750674 1250 500749424 500749451
    0x9070f2703020310090209071b080d09050c010807090501030903020a050601032406050303030c0708070b0c030615040f030305090a0924091404060b18010f3b060f040f 73
    0x1c0c507225131030030100107443d0543e001c9a06100c00400714014800040082c0c02610740104002c12039943c4030200941d04d42038050900014081c000302510079100d501d11075520303035020320480390042d8269142c040f8007d2138080110050001c3ea40102c0450041090b0600062000c003d02406188640945182c0500070030890142405401d00b1000d00b80c1031900400690320080300f01c9401680420b000c0c1e54034180c50901c0c1c03480e445178040081c11500c04208001d000090000518001c41b8100d0b02c8401042c800500e000032401680686210440c4c1c00d281040041c1c05600100032420028240380b40040c2c0e40e4003090211a40a00700303140f880300b200180003150600510400280c100135000700500800000104401c0000800c01844c1656400350360304a82d4404210801034507980075011129a1035080e00fa1402d80c19209800912002000340e4099407400000004000101d90342c02e0f00441d0303405505000315901070262a0050039000e10803915440d5030081e10384012501390040b4035580038102 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 500751924 1250 500750674 500750683
    0x40b15030c18030d0507030e120f0a1e020a14010314430c0c082d0105220303020405060d0c020c0301270203070510021e070509070f27030203 62
    0x40d0f88640c001d001c244143c07070380210a480f0900d8048c549a0446000314003c1101601641000c400c2882049503501840c000040d90100c1075104a5100820b10203440410b1062060140c000754481c0030740b0300a01440141d40211490302030149004542040f045003280760b1000265000c3c0a42c0d1b203100e41006103162000110b07400d40940f90450381c008051040101800ba561065100800c003814500d04140f18400f0f039004050700e0a1401c1d502c060034861401e001d8902074650b032641150007040c0d9490741c46010f10a0520846500c0071201a15054440f640c07c08502d1810460a0580c24407000c62142c075840d014100012003404000351209103c03901a04d044074903044c1e203100783c1c18108200d4480a07541c0900c041c01103d0301c8d40507940403080c80004e041482c030341c1050307400c02d100c2c148222203aa0300080c8003080740c00700c2103454201c524014510342c079540140215600003076030002080f56903100b0f0600000b0784100e46000005030341c40d40c000b03000100710121201e82440300e080d01402903290502c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 500753174 1250 500751924 500751967
    0x506061b0f0d26040203072408100302060a0f09030f2301050601050d0f0f02030a020310060e0f12160f0f12050a0b1f0b0d050105030c010e040b15030c 66
    0x41c0039810401e0442d044150484440030604a11124008075017191801c10207031000d440300311a00321003a0740117864042c4c1c3c8075411500000103900440411002c807922074000f001d41c2c0e00030f03005620306088040180c0d04035072425018010000e9030743d40040410b01a0284030400c1d40300c4e4044180c44040d04900e00e8121031094280c04403640b401042c0900c07030f0303080310464120401442000c00c41110840c141801804005c2210340d90500000402142810560046209034a0741c001c4240c1c20741c54000c11103400701104103980d04100396000d0f886c090301c0c0c1a0050b50303042c1c0c880400c513500181107080c04501540b540d0701802c0c032106900e03024001111700d801d15002401144e0900e54847c4207030b4035801d5440007402e9000e0851144a80031542d80300e456001c0d040d01a4181c0c804042e104c2c0da480164006920001d5440011882d00e0000300c3c00789004900c1e000c0d0720b24160742e2120343d02c0c01003040100409914860641c0810010b24402810f03618802543c403442d6a40352450f2900d8006006220000056 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 500754424 1250 500753174 500753177
    0x2190206070815010c05060c030601170c0a030f090206340b0105060a050405220506010914090604020912060604060f08060403111e0303370506061b0f0d 67
    0x1c1001059008400c42e90103496500e001c80048181401640c507084031560107405405124104101c4203040d1008500a007820780c1c0351000c3c20398510f8032001e00c09040d40c5a0240e00710801c14208180d10035003144000e412060f0300082d4015140d800200242c3c4040c03643c200401e0b200310440201e103d81c00307100e4461640c69011620020041d81d070701b1030320101402000d1203840081180705200d0300c41c0301980c0207020081d2402d1100b61144404000c8112204001d035909c60400700000c80b02d503c122031000c00c4410b200e894441d10360320310081004250340144699003282d030903c4880e000303035111030402e082c0712640c4002e0200e5040c0f00c4140400d1b14040d030040c03050f526284204024003200054210740c0180c1610b0f103404417103244c001c018102030403203000481c0c480030400d110101ca00d0100045010343c041d103207050314250851000b00d0410307211807902160000031150486013000940c000030340c042c100918003032030448041020510251442010180c1d50300401694801681c10416003080b0305c00ca = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 500755674 1250 500754424 500754433
    0x906050108060c0904020c0705030105010b0403050d0f0918110d0905160b0702010c0309080a12110706050d1505090405012007110f01020f01060e150616081e0d021902 73
    0x10f0320141601d01c60901c1e00e43c0183c0c1d001406480e41d5a082c4460f40c00390000400070f0210b540d4409040340307250018081035a407402070008609046003d11084800c441540e1600c807450340c60715020350101c01c1d0010ac85680d00d1340700c01b0034840c0d2585010040080031580342c80090110b5103030800074604003002211b40700400c800b2100307100c0280400700341d8181d1982407174a803203070540c02d00d0104d802600c2c1c1e60064030300d403058002c80030421010b03404c081c8900f030300c0d99584103011000f0304070342d0b075a4944c078440c010202d8020041c900c0d1941041d040203d00d001c6802c280d140b004d80d5800465405c01c0200c070240d07256503540d54529030110154106a55250403001c569060029a440709021a001101c03902d00c2181c1d410014002d5034004c0c0185040a02410000c100107555030300800d41d0003604071380c1040044c15402c00c5000c03618002e400d0707880c180d8008541d05c80c0411641d0b9400f090360b11125540c3c0c000d103000c40400104100c400c00410003500203500268403622131001c0049103800b40d85c1881e055400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 500756924 1250 500755674 500755681
    0x90305070e1015022a0a05120f06100509100f0e070908030304030c021002070326190e01030b040207111e040213080c101704170706090605010806 64
    0x200250210980e1840e0960507a90344a00d508802444900c2d0701500c1180c5220030328511640d00450080ea202d0071800c5180040c03003441c80c03501081c6100c80340440d80600a14001e00031030814202c094840781c80f0b481241c440c10030501d4190302d0807000701c458501c005c00c0d054040c0268149074110366000301307400789a81a5030741444000000a800d0b0301501e07030302510180001d041c180c401c5c1240ea008085400940e6603c3c10103050040c0502082d401c143e000301000710f500c00013280b00243c010300300c03900711316414540000f501142d021901040300c203815940091044800c0b0001c0c007030304690300c5855525524101c040c610300140907140035483d42885244188040c002003130111210381f920324421201c20885030545130840403841c8a4444a640091000c1a000007901c40e8081c1801552000b20071941c4481d0b06604204030301d102100c0c4d11340010740c6000352000d00e0124100030341e001172140304015856400f944020350580c02c04031003500c07210703103030100081030007247e00c262405800044080c081505c0e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 500758174 1250 500756924 500756933
    0x50613030e040614191a0d1e020c060105030303130308130b0c13090b010c020d0201030f110d0f0c050a1407060c09150f0e060d0609051503120a020c060901020a060623010903 76
    0x203800201c8920000c0003d0303c03294003041d0340d00401d02201c10030301c20409050160703c844004d4002b43c1c0541c1e100e01ca13840001c2241d00d000000da0f07100b21502881c60441e0381840e0780c02c69040ba00074000044100c2604011000201368045046c4554280d01503107446441c00014000300c44031030b034003180704180f401c13202d2003099074031880c220342c11501590380340c02880309440101d00400c01404a03040040c03038001400308584003940101025506c1d01c0d07003440501e010140d9441120345c1015624003246081080002003400f4811107824014007000d10f500307220782d036100d88041e1040900c0e445c00041e14800207002c03c0740208000d201c5c8050624120300a03404138840544403014143c0c5681c03080402090007078504506420000181c503800005018030300704424840c03c2d100c0c4000c45030b8824002e500e0410b0203005040182c5088207480d40c000c1800d04241010301249500039401c00d41140515185100411268003441004104030554285946da24500010034040d0701c044541c10090700301e10400104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 500759424 1250 500758174 500758199
    0x32409030e0103050c0d0603060c090602030f040909030512090709050705070b0a0f0b030a0f050601061404030b1801051317040b030c030a0204080d0c02040501090207050613030e04061419 82
    0x11400382000516501c0300c91100c0498011402105046c90901c940442002400d07000780302203903101e48a15a03a0303134842e142662a4001c15401d4070008505000800c015445900700203150380c02410b00d1881e0840d502e012054500c0d040703170300720401c0d8004c840401040c0c00b01c0c46000e078403000514285040903e02e035a01481c0d003c014152520746c51701c0d040051110f542650201101032401000c54480c0c00443c5042c00c0b000409180940d05805401c00000d0036a001e003081c460303aa01e40a030120325090450b56016082c0c07a0240c82c11188044241d03a00710070b01001d10500d0f024103846a4a1143c00b2854070b0841211050b0411840242d4000c0c0801c02c2500525804d0743c0c2c02601c1e02440646942c1d51044580003805943e005084a11882201e0191a0b40010390301c0c0300d00380261400c3c04240c0c2c071104101c00307911a0307a000820780d50050000600005504e858446581d100e42f8103a010080d40400081c2a50501e81028603102031060f040161454119075401640020f00c10310500c4900d01801c00d18103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 500760674 1250 500759424 500759447
    0x10f0804151e06031e15050a0f090b06041109030c0418080703050c1b180a09080301090b01081305060c1e0a1d0f0306061905090103240903 61
    0x120030311501c1540d20741040e070886003651603010035268000e660a40160050100361000f030710100845244415650031142007000c5e102d80000c0754889020450000500400d8010802d0308003079541c1c070b183c00e0100001d000380d100840c0030303010301c00b40307414010b00700710407242e249540c51901901005480b0840d200410349040092041718006202d24066890780d0310b14014081c010030075a0002020320405400a001c0c003040102102100c858051400c101605509130446407a4030000d440401c10141b014480d54039445a0700200100d174040c040d59658030560800e030444441d454560040c18615680100c111f84d00c100d05c1a100c000f01d0085403100d0b601d03400d01800e9a51420b40001e0300d491816031023541c0c01e4148180099203541c4040b501c100400041c1c072104d00c00e4040d034940e20503041a02d0807101440328a40010042d10280c2c039900e040118000403c08011100407038030301e0004007669201e0f0f2207030003180034030001d8405001680100c0c104c04814042e0001840c644001540417a6000846030320 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 500761924 1250 500760674 500760683
    0x30314070810140102010207080d0203090607020705060d0c1e020622230a120c1a070e01030b120a0c030218040c0b09060c0d0906020f0309011b0f0b010603020315010f0804 75
    0x43c001c2c1d001e004070b01910a19101030300c46440010500301031042e030383c0107502c20800c90302030b6050380e161607004030384800991107007940c01802400a2580780f0001d0b80070440a10b407900b0035a4203d182d40f0203000d11044400590005a0001c0c2c040100416100312036150014820180300441400c56541c240503240c03001c1c2da240d80e0040f007900011025810003480503025003140300d902c0d10150000005145443c00c0758100d4003000f61740a456900034860b900319000b021591240c40702d07580034100450090215074a200e81c411043d607007900d04410f01b4030071504000c0c00f4031902e0f807009040d03005100070b20409903254480340301110100800715980704403020903600361498883d0380b255500d00140c0c81380290800c001e081d00480105190351504840e074807044403880c1e02510314001020186580b41e01618070a01c0c045244000c00d8419409800c0004810343d20030f01c2e400c1c0f0b4005454036030100b4640c090300300c280400c6d800410302c0810080302c010519150f90920b000218070710118001000350070068030003803 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 500763174 1250 500761924 500761949
    0x605070c09020c01020909180c01050c0c0d0206160803060a08160b0d02040b1204030212190c060f0e0a0507050406050a0905252607021203040519030314070810 70
    0x41c003000f000e404649080c54010002005401d144080140a00007038000950922407141400720a5005900f41c1c1d00f00b02000f009042d5040841041c0400d44402c80c504990040041180c0b000c3d95801455031000356000f07151498072898002d06000108807a40c00c9442d15910028070035620205030b01c604016948002032450b00d50018101c400302901480c0c00c0b5103101103011440c5402d07c41c1201050784a41c0c043e500f2290070490000d4203070f1080c032800140350100d59601a9281c0c883e405020342c1e40085100d55000902c0003c00d6001c0c008445a41011008603000300c034550042c030604000b07500142c0400c0721308015035403910000500c60200c130b01c16540310f40d440d400050010180d4070b036070a00c2c07030101e12660305596608100c0202080302d05000d080c442121301103203d40c0d8082050105108540315001007140a100420382c42c440d07007000384111542c0c820260b40b030347c800a0410300003451500c00e450209121016a0f007052200c00000c20490400c0284420040c01406600190080301c0030008000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 500764424 1250 500763174 500763187
    0x80c061317070f150e04060f09021e0a020f070914060f0402120c09190e0f0c04030f080a2006040311070f0e0f16020606090a0e100f060605070c0902 65
    0x2a050400650155000d6503d0b818005142d40c402101d900755110140d461403a0700300d101041204070703403150041f0b440c00c084140042c40300e4001d1354020295080d04440060144401d0307181381003c0c0d405242088016003202c245009409810401000900b080010a0004202905d02c401d00070b03000a04082c45041440c8040c0e1003070700c03a0341c102c0d0010240425003103002c1c03401103905130007584141600c50207204034009000182e070381112240c040c1e8034100b4401005840d003004800c150240a011400c900c441000000001014503071b0319030f0f116128841c0710391143c04000010340f90241c90ba141748003203859890100d81010b00400d80075806581070030000c40e4169640d5000d8604200d5400880003410039030004508204e5151405100d480b1403600e600300c0356034024407414240c6991101c00e01680c01400421402d107020080300c0c1d844622400001a2560884162803801e241c0040d080001030b81c545000064003424003c0700d0181c070150900d24904052550703400d54131045480703910f03c4a540421803 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 500765674 1250 500764424 500764469
    0xc090702060a09030c081201080708010207080f03060406120609020405132a080706020c030c0d0302070e092103101401050904020705011b0908160b070f0f02030610080c0613 76
    0x80c1c14a41c0c00a540c0c0387c0f03601880c1c9a4421059080c0036401c1c5d280b2901ca40020301e10f03014001c88421641c8203980300d0601a000c8480718840d0400b40403564020b03254080400d82a81e504203034482035000d0710002c103180e0158010b110440740d0103049100b4414156122034040380154010241130404540c0060300f4134012008010050b6040d0071203c402d000382d0000064165001441944000b011002d032010dc20075035041000d18105260002e025805c0b1100400500844045c4203510180000950325103c00d0360040480903590307201c203115011800b00c01e11502c02e0145041034040c140002c5000720742c844040000c1c0040c01550100e5200d01e400149210070404c0079007000c104070318540000720000d1940701016100c5c4400d4001d40c40a42304982c24040e14074a02454801203940f1599510315281c9107403102020f03100390400035119800105d1780f0130300503281009824070540d4079101002d80f0b20300b061007007410540340e040d442d13101380400c0c40499240240c213146c0790110b48004200400c0d00c3d050313003603 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 500766924 1250 500765674 500765687
    0x909070c0c08010c0e030d0801170106030206070309170c03100e01020c2b080f130f240b03010911012003030703020706062301030e010f060f080c090702060a0903 71
    0x2001c031881c1050015803488150400c00128040b502c030356940344204424903949400103185c0c40300203050310b001008503401410340010380c00000f07800460116203903004900f2682c0030040407000219590b00800000407100170450100c54524060301da5051010002a5a10004038420b03280540c6c2e0561000c600a0941c102c42141410106071456a80e804038000183d0140000403000c0179140d6051400c410300c60160036104004410511306a07464603130003440c0c0b5040c041000c481d58521900071401040c5480352500c469102c0300c8250921010581c2e022069583c00e50340c0300c0c082c0e13040118040c002145c100e90480008001e2074650030004082514000c180e0b080c8842c2c03000c0b400000203011019078950010a0040c1c00f0301002d010069951203064042e0441c0c17070607000708803444c10b00d41446610a40201022804070400810102448084c140403904240d04c03038038100e944504100100b03141070210038943c0904a42400d01e6150001002e911400b00425440d801035441c3d440340b08060240c1c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 500768174 1250 500766924 500766947
    0x3120f040905071b060c1814030c09040519150f060303091e03141207060203061e0d02040c02070f0803070b071704080a090e07030f05010b04050109030b150d0f0309050411090907 78
    0x1400d081348d03507600f810403000502e000c0540c0240544001603441c1c1c1080c40d03d1030300072980240140200c4000c0c80051001d1103440e00c0c120b80414040030700000c0e01c41c44d4096210a141f10b49800201c1c00d01e907243c00f42c1364240c154000c1070101c03000c50801001d00aa807034000708503078010950383d440c0c0c500c01718040d080140c1e00100c80032054001c0b90b40414401a0350185201ba8002c2d03030142c00248841101e007064804001c20f141d4040b120180803001414030781c010a4481e042c0380102c07500305889035041040d00070325411810307103544041541c0080c4100fa42c0c1141d040403860501020b0070074844c10078000c542004101401400f00000c96111091040c00c02d0001041d0304040080340d401c100700b000300136011081d1903202e01410b03c40082003145030351040b20112181619445480c43c51030f42d684220b0a0b00400a11003c0400302c0c550b403268a0707403115905024071907000021840c040d45030180c0300312001d8025074066031500d10049100c860030011620300784002c451000c8a03070b8030000d007205c00c070f5240d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 500769424 1250 500768174 500768207
    0xc090d05150723040b040611070f060c051002090d121214011e150c03020705030d0207030507060e010e040528050919020907030b03120f040905071b060c 67
    0x420004407581c045941d8002d02d045030410b000c149088050a0104d0007213000d00d014540007080104007050180000420010140040e59091a03680080740304c01d40e40d03580590040f030382c4110140104401806900701c4441607040c2103042c442100080707003107031142060081400242c0c52180040c40c1c06500c8000010004810600034400b1031100941c61030002c1c81507800d805030304a0361805040070603000c041071721800707049214a2000b0200440307590148a600f90258001c00001040e141c806000100092805070001c11180d4650316201c2d1070800983e0000b41007010150307060302d060f81c0c0800b00c122610011500400c40351035080c1c0140c10050550840401d00058082c81c541c03030851f9400c21881180100c065584911030409801455444224025409480e182c000783c801402903100c5244220003408403050102c80c00e90788400381d484101600b0b4440d0000c1010440c2d0b11041c0160b0307074814000c0c0741c605115008900c15aa101124400007420f17152140e40d6000007038854007802000f01d404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 500770674 1250 500769424 500769463
    0xa180b040803072a0c06030e0c0603060f12010b010f11210c03070f11042a0203042c01060509090a0f110a03061e030f12020309130c0206060301050c090d05 68
    0x40340d090004c0d03000c0e800f004449451101c400010310b00e01038400c6110007e04480905a42e6008000b005181e501c02030003a030b40308500da88242000d85032500c2c210704004801e00000b800210b048009405080d1410942040001c91144540a4400410944020700352055080703955441420191864007a130340d800b0318240300124040f014031220070200344c1e46501031010302080b600ea50013032205441700a1440b5046042903a080038005444800c80102002540f06990a154480c9903000005200c4030b004940100d40007001e0480c1510918003d0041c032407418000c2c070b4040c509000c140100e40051041c15415a200a5150800c0c1c81d9007091084150104000e6603502480c0006001054a4000c000d03600750b4050540c4180c030040040e60040e01d03002050221102c01c680d2340e072440000c1c0c0d1071004086001c1480320319141c0d1504242482d1510b000344000c00c0b03400700a40024900540101200d1180c0c3c14031050010742031421080b180301240684281c981e11010781406840e000d80c1c0c42060008008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 500771924 1250 500770674 500770727
    0x30402030703023007150c150603030503040b0604020306010819150b0d0e03070c03290124020a0803070e010507020604030c08301803070e0a180b04080307 68
    0x4444000284403420f410b8040e90b0400d220418985d40c04c068001c8a980b2180303d084000d1079401900000000341c4070703203640745030102440c071100183e848a0388110089140802070004003c51004850f6101c0341c180c03000c50a5191003000280305039809000405d601916010002803100207400a044640f00d0319001100c99a40b15520040381d48003500e06d0083d81d2508404a06814002c070031100e145070011035001c05141103845440d40c48940702280c01e10305c185510209000007000c000f40c0e000b8100165141a02c48040c031280d4a0400c600f20100110b40103103401000249550095940152041ca0f240c00c426202c0001601c0710b00c544a400782d808400454000100200ca81d01070041d2142c4100759022440d40312121060300410340d10410710741100051082100303154001604024070034880700801c000c0040d0201e82089000e030401510440100c0c10085021010301034038207594070314084008100c00c01c0d15a400d018002600041501c1c00010220b80024460301245110040403c2540075220 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 500773174 1250 500771924 500771959
    0x303080a0216050d030c03090203030901140408070306140c121803040503031201060306050603190c03060306021909140303090603040305190f09051002150702031b060a0b0405041703040203070302 86
    0x140d004c4440700001c0d00340712101e00110702c070740035076a5126809001182454040c000648640c40c2100c06064003180a11001500160411000c40254011240001e0687c164100104058001069020401d02c10881d1411a401d205040c13030707000d10154800c415111410501c01e042d840340c1e40c000e035410300c00403422140903540b0001b000c0c1200c059441c20021a55100c0600030a40811669025000c030141540742049581c0e40200e90700e11494940080d000b900d941d0707a0012a0005424a044040001c00009441d0f800c440c0c0d9502420204400c400d810074140f00290362482440c031480d0080102002040030503010702d00791800c11600002c150f4074442c984130000c0c0550200451040000c840250000d09806d2941410041c02c0d200e602422400300346481b904003440001e80045d046120801c032400e02d01c1010001d40d4100110b05000e0505402c0c00e4000340d09a42e08001494825071400d030a06c4005075002c401c007000300a4400c0321a4483d42c0e03d00000307042041c0c90340045c1d00704a034040b4012501e1b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 500774424 1250 500773174 500773183
    0x402070309090507030504030203070b06030c06160308010608060a21081603021221040f05011b030f0b01050715090213140702070303080601200f1e06100303080a021605 74
    0x40b80c80000410690303076074400440c10740f20300760360186c0503030002c00010007c100301c4041281e100340050700301c55210301c0560120703540d030b4001195401300030300e2a8401c008050344010054018801403404103000e080c04400100560700d03038411101d442131a2070751a840020540b1207001601d802560468a07501d00003001940c0c10f5001c1d80071001030142d4105545030745c294905076420007190726540c4003a901c02c03124241d44444040c0081e1201c1101e08441c4001075000d00400c2080354040c5280102c005503404050191410780e1505c85003a41003d100b020681d0384502070720400380d0043c80d01c0b01ca45a03850081002402d0348180603410004002490485030081d41115002040303000b0005665620700d00100e132118101d0000400085100020401a610910166040030740d0002000080c82d4502c114078a418140e00d803165040d00022000201040c0d961052003814060401030011443c040d1002d0806c5110b40c00002c09000d0004085002082c0a40c140c82d0005040e1655180480407414080c0d5036 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 500775674 1250 500774424 500774429
    0xd14070926011d150112020f0f030f010c091a0f0a091e0501080718030305030c30060d0b0609070c201903030c060207020d0c12120e10030e0106050402070309 69
    0x1849110078104d034440750482e01d24100c480440007074138408040d500300210000c0413203010b40e00c44188150700b41a560103210200d08207002c0343c00044c0800001070050103410b0a0391110420080c561710545402e007000088407203420058141c40e0383c038280c0001c15180007119130030418000c0381e1002c00c0801c004c00d0305031180076540242c96010380c6540b0001e0844440941c6406100600fa00000c02c1001a010f1b1001d0f640040d00d0b60700050030112129403041c0403842c0c0e41300345440c90448500a10b0200b00344290310b508000d0071340308404078410a403102940c10701c026003054002c9011000040002e803041c80c066a8040d1b21030110b0303584c1086c1848000c0c1400e5041003103403040b15150069480941000c07007080c112649034440000d10f140a84400380207412526050360040b0080c5481030004404082800c0500f071140422400c1e09d5060030000c0e030fa8040008200d0601603c101c030400607940d581100054103407a880c0105000e4407104205004d814943c0c4000e4009001041308070805411a402005 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 500776924 1250 500775674 500775731
    0xa03061a0406090b030105030c040504150f05010302150f03040f0201021c0201200c1906090503040f08240115020703051b01140717030a110d020d1407092601 69
    0x41c0940c0301c3d95058445c1c4001c0c41141d926074880c504040481c00c0030b400c0300798054001c00051102500c901e542e00c0613101d0008620003c1da035148014400c61800000180c85075101c0030788030742489207044000b2001d2201910240c2110300740d50f040021a0310070030054032406039400900301050800c0601034040c155020740541c4461030300040101e4040c080c1c0130b80704501c1360a0028000c00d0072004c51002070400000d000ea03185a00c90034940007003001000140000d04001c0300348540e480c902910141010701441001800464411105120348009215103054030880343da036540c6448020010381c945162a40300410034001c40f50b070b52404600c1d030b1805041102080e202c26800d80020400c0c0d03c2c8511510400034100c00c00c82071002c0b209004c00000d190b00096291002400f1140e1000403080fa400c02e4100c41d000c150002003070800b450690241c81e40711261203e00002c50b09003081c01a01c0f5a4050080d220000a201d082081403041140c000011000d00740080284018034100000055a00c1c0d503010b8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 500778174 1250 500776924 500776937
    0xc0306050f090d030f0b150a12020403020625200f0411030a05270705120105101a0d150512060712021606020d05060f0102010c0507080a03061a0406 65
    0x20801c10040021601c01d2a4040240c02401e0400b04107800070402e050109010795a01c141c0000c00e038172140c050b085200c08490900c1c0d00c1c2c841d03814004201039480c070120181e5a005000800058030b6410a8806a44d058022015880500f83c406400c50841240207007a100e020001c920100a03068582d824400c0c3c103071011041d80329050244001d440f00c01e0b003c404600020400555200031350340c8465004244000c40454550f20003002c07803070350007690500d08115007146400304094581038500b0224107140600034072091410301201d040e034051610640c1820303a2074101100704004140d04035400000109410041c0d9400b1080300450380c0c419004290180c6401c0201400840300054050322a00480e40d070000c0302051281c003100030707400c004407080d05859202c949000265040c006005c0300c044c0944009800d1070104104990b00c01c40320646415079140c15400c00106520808840e0140d80040700170b40d40d403e400800f05c00415483c0d000d9010402c5002203210916074078001841200c2c9507a4520 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 500779424 1250 500778174 500778181
    0x1e060506041a0a050f0f0918010510031509151a0f0103020c0d0e1807020303150402030105010f080c09040204080d08071806030e011104060327020604051210090c030605 74
    0x26002e0b80303440b4002544041c02e00401c01c1540740c00d0346070130182000545039144620110020410510050700c030b00d445032042100c0c2403d10002441501d42c00040c00038084031692441d01c518200c03400100c070903001130703841e102410300380103482d101204400c0031004100045107200440100140551803018455106c5444980240d8407a0003590303240c1c10150050126040c02900c141d40c0c0801210400b82c003c41d80c4c40041c03041100c11300c8007905c80c030116009540e480c617210341e00a4400c00048030552082d441480140038590380310b41c84220905190401e50115100e40011101d5800b644280951240c000600400d00c0a4041049800407a242e101d648650b00c40040036510306503000048180e65001d14410002c82d48a0381014056401c6480002484044040c03000d20030752240e00100040f0381c581e0b8982800a044980e5400c0001221082d02103903003645d4001a000d101d00e116552203446294030352042c00030b0600c100c1c013005c81000400c1006500c41c1c50b0801c0850024032040d5082440c00001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 500780674 1250 500779424 500779451
    0x8010f0605121f0905060a140f0411122503140304030503030406091e0507080f150403030c0519080402120303061f090e0103060f06150507030c1e06050604 68
    0x1211044520b500242054500d10148402410903a074000d9003d10344501007103010420038001503004201000e070200d4076248a403594500401c0103003211003680e10907010040800e88151915111a504455000d03000c42d503c0402c5240034282800700d1400140b10441e40f86c200a2060309101702ca00c00c2105001a071003080e119500c902840c4006072503504200002800038117540d108007980780c410055000c0440c000301242c41c3c08882c41d0001c45650340500010701ca601d81c2002002d084c0c0120500409262011048414440c0302c040e000906260b142c6880d180c8e054007400503283c01e0b41001c04017001a03505400c00070700384c010642e8103038007030344100700071050400020003102d00c038481c050444d0032581801c0c92804030101c00400c20b902040350384040491100d1384040d2103070085000d04404501e0a00e8045041e0484403194004800c0007a00c15000d0105a00107007602e00950305810800059145030400c1c1000c0b80c903c00841c480c40002c06c182c2820414590321460248801361010400a800d5100f0f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 500781924 1250 500780674 500780689
    0xf08070509011e090203040305040905070905030606101b0303060e0702011b0f0e011808190c060207081c050d0612060b01080114040908192307030c03030c031508010f0605 75
    0x10712800b2616000f0500c2080d8940d0000e58209210f031030803d103455910310901003100c00948400e0001000904204210300e020440c2c0361304150200d82134180503140244c06840d42185246003400609500003007824107001b544100c00400091980380b2023450203040007070003014040d03244000a0315a90600b100580b055420340382205182d140c01081008500c010369900d0079a4441010700e524005011410178014407050301031130140242080c07040164034001c004410290026400c40d480181d040181100c0010041304982400c11851808800f200044825114441188000c5820070030001440b1540340750b280101d40c01480100480e04000d001100d10003400c2c89002209846d5142141c5280f07000d03801052503a2086551514180c10386040c000045a05d0802c5400f0442e0025810035070950303000f81f00c483c8600c2c0c2041600d8462aa500030b0f080f465030326405003c01d5030f81e03c4841c3d861030103644042034203030301c0da007210700c40a54403c94280645101c0c0200120981011000110b0307080c01030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 500783174 1250 500781924 500781959
    0xa080103031e1719060f060905060c07060c0f0b040803040204051014131e09021212070609110d200604081005040206120103080d06061806080705040f0807050901 71
    0x5545a024912124074181d02c5000070304400c407a00090070460031314506911808005012182008008a02d4600043c02861440e400140640710410a0301c20720400490040c0a6a0060821800c4502d9506095602e608442001000420208284000c2c0001c4401852007248201e4042c096581d51403031500507984540b00384615001040c03030508040c0b4124800280e0321205100000c1e1002143c3c480210000d01d0200140d070040c1da524221003517045c120074151071011040300a02d20300d0301044034450309101d2075201a0a00390354600c964104648440c040780340090003011200e0080d6603050102d4811071081701361030050041c082e0340c00d49041480544044800b83c001510226118984980217042c00078001c1340c1c0010200403c50013949140b002034042e60054021586070030403a1000c5044580d0382e00b03c3d034288443c000030f2030325000001d03401c101522001d14019400d030f02c030702900340d03214090350700900c0c0b81054000c0082200d000000f803803001c03a4001c41d84042c0c9a40e07030780410b0301c102c88081c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 500784424 1250 500783174 500783177
    0x50601030903021507050705150403030606021203150d0218070315030b06041112070504030c14060d150909110a14010c120216060c030f1b020d02040207080a080103031e 74
    0x20300c1c04c114143d0454000c507031080c00e40c180503250001c43d81d0baa605040b800c0260155010390002400309055042c841c06015010741c2c0014201003000700351180c1e01e8040289161b03003051000b4175403181501c800b4180c0b04070030341c0945032000b02107004980b041520811034024000070710b84036015208107112961039041760b8000e103c1364041d858490904c0054005400c800302001401c200795040c1d24080d0074140e00c00e06007541c8244d12a4118a0041c1194030b540c1c0c08400e400043e030804075003699442c000ca80500e001c2017000620200e00e4442c0d6041c2c2c1031998050120b07649001903041c10300c00084903003036068400f10b506101c0c4a13290200304050b00138035610b0900140411150100141c007690007403900e2091401141c10443e2540802c1e88680c003282c210070001480b4240d490101900314510301e101c070240341810609002040f0349061101500d04002e403050983d100b918056453fa070f81142c103081c1d04013201c5540d80d81d02d0080a843c18000380b204400245480c1803001c02c20400c02000f00509885 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 500785674 1250 500784424 500784433
    0x305090c0f09090a0c030b0106110d09050d06110a0e150a0f0f02070b0307110f010b06250b010b1e0c060105150c150912090a090203190c021005060103090302 69
    0xc041031040403140141010b18130302c43d250441d00401c02480304c4800a42c810807503991590f0502c2c00090012595030780014040e40300c8034102840366086a40704080d64825208151400ea5038240600501400311490003012000280d01003016070000142c8101541501c3e0100c009420308041c0c4414850701240744c000407400c4240e5415680700c0c0e0509020014588103d600c107a444402d0301070710345d00c2941d000004c030307824401c1c1c9645020144020b504545900008110008502c0c1c041605445414040702c0c0c03500710790300c00c0c0f6104481c50285648007608a11000c106603110345030314070b183d44030420700700100c4c0e4654400d240c917140c0d84080b520110215030141901c0c0e4138002c1440391542c2d00040d060702004080c0035400384c0400c20029400d03252030b2410440b40c24105807004609001c00d0380c80ca5035080760104180c6040d0344505012100b124408480169240c3d0340a00c0c5070001c81c030351030040000c07604108044a07842c3c0e00080c510003c0c0d40c1094208260b4444000640c120780502e400180580c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 500786924 1250 500785674 500785699
    0x5060112020607060501091406012105070201140103050a03020606032a0f1e241e0705160e0a02160f051e01060806100819061e0203070305090c 63
    0x501500c1880d4148054011403c20701c1584e80d02003910310981007407850703540d1030280001900030455030790703000f000a0815604100000d802202000d8010440e600000c1c0c0717640201d880e6a10035444040100980c05003036409507100e1030126110319004400307070300600c10344020170003900e000b02e05074031400c85c20810040c010b9072504500d40c640004108071a4000e0b41200ca4540c280c4032113140000e0840d03060400b0061206c41010822200d0080b580c240303198110007050040800500c04560300c1d884060000d0b144001c400f03503c4206071082100040c004e00400c48088501a102c0d5440b009807603080c2010582070366803040c0c2c0c00807030040800b40c0c84032442d0340304030f1000b2610346840d240e18a8060000c0d65000d5825003407078800059a4441c01100741e54820042051660a000e0750b034000c880c080440b2270a601e407100c3d1713907a26075016800400d46040720780304808001d455400000b602103180d0101f0010440d19840030003e4000719101000b081c07e180020b0004400401c840990707442c0101084030545 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 500788174 1250 500786924 500786939
    0x40504201c291e031926030a0e210a0e040e2415120f0a03080a050a0908040b07030512040507051302030105030601150521070219050601 60
    0x80e001d05000d00503030b03404540001c034041012012111241c0c08400062460348020300031015580c07030340c1c030300001e4280748810381c15640031881c00844400c610700545515014140403a44c815491250060381c0e46c0303031706a0301840c69010003451240600d51b20401407034100c080c6440c1c03500152444002090442071410f6800c80d211400b4005c210704524000312000c00050208084030017084a0307d00d103a0040c02580100d60085803080000c201c1851201d400e8181030100700f00d500000c12080d40300301f405100d1100590b1042000001d842d60006c200d03440103009040142c00359038290344000d402410500040d03029081c0d80200700380258446d50b8580740a1510100d01c805402042c803c8040100400031160b40c8500010500d000c1c80c05071000c2e00d9181e14050800804c40081070020b03000500500040105641c041a0a0304580d940c3c0b405402e041184d0108980900c10441d80c001000e045403800385000c650b240140d4440d86242d001c442080c090030ba640e0524401c090300061856000f20018032025 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 500789424 1250 500788174 500788207
    0x1110c0a030f0b0717010b032502010e0d03020412230a0f0b1e040b2e2607051512070f022a0607060b10050d06050f061608040906030804050420 63
    0x2d0044d044082c4420b011852105402c0b00150302600140c2d163398106050a03010700030b800001d1030b41c5c2021460b0901e040440200c25000400180041c04100804091402c0d40100c0052825016058412070442071400d0011401000e90030b0344d1852003800011650b1840c45507940e180086044400060341d101c1c0d0300d00b40d00100c004e11490004945920031ba40400c04101d0b816004a0100d008204990910807011031007000c4032030348201c0c4400358000220910000c6020801e030f4070140d0712425104c0002000380800d00c10800da08949000754801c10913032542c007200b80c098404942e400d40744281240040f60741000044288a480f5024481041265142850041060030306c0380780c0128810204100140602e42e00c0a10400407410000344081c00100600c10540074003030480d00d19809030107a0700802c0090240702d544604040140c500314041c4408035098900034a503109040c041991646003003005508544196802a42080840d100100d00c80c0c00c4068021418074841e4200005e40d00500042c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 500790674 1250 500789424 500789431
    0x70804060509070b0a0305090d0201020a0f030b03281208060102030a0c11150301060306080d12050a0902060c010204030b1e0609070302040b120405100504080901110c0a030f0b0717010b03 82
    0x14428990700203110614000904003030b0741ca1b5100011142340c01000e803801c044408140e04116403041051240701ca8011042a00c010381e24900001c55805140110386002840003508195802d6007000001b1000d00e20080c51440340710f007040c0c12641071401000d441e18041600c41e00c1c0581c10134030901c52803500c20301c181c16000f030051401c21084801c0101007108005050100c0d890304a0020040c092183c150041301d0080014034020a02d4841081c0002c00484140c041d08040688a00c003207640420607811601425070000c0245a6511010301e606000703500505c0200c840b05400400102100c21500640003248010500605c2a689170801c110000b10020314480a042c5e090002090b480d0703001001d860304440f5009000414101070401070b1509400d845110460760612080100060464041d514820350a0814540c1c0b40d585816003401c1040ca11031003500301c0605440007060040d41600c03203070400c2c02281e0710482030f21021401c40b40e158a010200314081c1c82c4000410210310340360005c561 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 500791924 1250 500790674 500790691
    0x321090f0b092407030908070503060c031f06090f05060306031e0f012f03070e040f021b0d110312070c06021204110a060216150207052e05030708040605 67
    0x11282070140341032a40b5201e01d00d10344620201091080c20150040490300107454040c0c008d21046e0324010009030383e250001c10ac5003034240040301244042d40080c000c2200715200c01e4400f81c8054032000000c1050174280301d000b55024040c58001001d0a043d000c580c011100540540701e10400c031300c0c100f8608000451a2820361007044654450036070280700d110040742a2022013000911010701250b0130b009800e66810640c04204113005881d500240c1d01d1446810955001c40e001c84002c0c5814000d0280010400a80d6407025084006200c0810300317159200c0a516420f11788880d80340d80c2c2e503403401b42c081ca080d60300c100200880c40b1540a2040c50f20f030144030b0100075250641c8401031103510b10064a0031204c05508a0b5441e0300b41ca010512880500724a10041203206007101c0356403014a010700c1160700c0f48070242d4098502ca482030040c58041c204c090560605800b604011891001030340400807030392801d801031007611500c1501140d00031511903949155a445d42d071600e400400c0050108403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 500793174 1250 500791924 500791939
    0x20c0a02091e06040b030c01030b1f0503180c010203030c1c060303030b010e010f171b2d030408030411030114010b120f010515030a0e01060321090f0b09 67
    0x140c0d100700e8114440d40c15074403503540c01c11092008600803200a00745038410380c00c140d00d602440c3c80015000d584807009290124070324645001040201c0b4406504204410152940184164119000318010b0b2008040422003030103c4500507164040c0c528800c1c01030308200003060320616000d025101d0140c02807034408100c2c0551810b44c1c103d4006500440102e84c03122000106983c005010000d000b03801e00f00010b850041c20b50091100c0901004800060394110100c1e44500030100380d850440014031215030b44080c1c00c02c0054003810300c9025011600149000141c446015a050b01e01860b4130001c80c9042d0b4580b1340d60a41c145e40c140c607046070959640c10b07106a564210a10080c02400718000c046c0e03031465800107076409508000d00c0a44040443d0004000c0d90b00d40380d0303a00b070321111b021000940303a4031070100c681c0250001c100488665801c080001c070030301c00c42104540c81c22a02ca20100c40e48403904400f40e43c0c00d8498451899a1030095404103d414203810003040400740c0280380e034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 500794424 1250 500793174 500793193
    0xb010303050d063201182d0e0402090a0908030f0403020f0a0606170102040515030702210316020c030d030f0b0405010909022419090302060d0911040e030706020c 71
    0x4802130640d0714a581c19001076461004956410210007842c0340d0003842c00c40100d40f800d00c0f2600003c040b0b84a003410f01c03003855400130545404402043c049810000c400460a1390b00d1004c803074005c0094500340d1140880c003003c00e8072079569210f003d0035190b0141c0c0c428155592809402d036440402130080d001e60245980751080790009211010f1001d204400009101e802d2000c4064200452080340400703a00c1000207000c0c5079501c0d8198040354070343c2841140d0741e680b201012800d099030a10f0100312601c1d00c012008031080c4004c0910710450035010300740c00360101e130103089075608450902c3d580c040d000200c0030010140700c0d8100ba98020705820020407801c0c3c4850100f011560264440b10445550764a0f81d400c5182103a0b1609541c02d00b02c00b90303542c00840c2803542d2032905c05c8014840146040c01c1484071a00d019003000002103070002e04003500d4880c6080c580c800f8209a02c0100c406064145a00c442c900c1c203445a5a8140302d810000c506249142ea034280080d801081c80500b58803814061 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 500795674 1250 500794424 500794439
    0x6050a1b021534020115090c0203090d020f060d0203040204140f07082502030301030218070503070c020a0506030c0d05061f11010b090705070b0901020f090915120a020102070e040b010303050d06 85
    0xb0030094803c60741c000a0840ca041d44404680050394100220355410442e4107034480758000295007036030508403244a1035448610009985060942031603800c1000814111640303145a40514030440c000d440074440f512456201e09411f400880700d92480c143c01c00082408544034002140d40302c86900110080520011b25008416440109080060384000010300c114102465103620800c440301e000300560804040c003400502000349000100603c1c804c61205650303e44103042d0090801078481962030901c0542c90403170364064484103a1660a00300440c4c01c5003040500d181183e0b805c0170a80b004c09080040482c1e803059100a0072243d9921801e143c200c0d5510f40c60725a000341540d854050b698240c1d0b2030b00b0121000c00420003011a44180040c101e00c810203400c0b150405000c50b0302c00c0c030301d0340c64031086000c0c1801541c0c455000a0301d031080f10a0780700002840400d9500076001c23213070b009a85101500c40b4160454000b003041980000400000340220081c1815884c0381398003050700c603140c01d070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 500796924 1250 500795674 500795761
    0x30c0804080a05070f060503010e2505031e07020c010315052806030605010c080d18111804021309030c0f082115061606050a1b0215 58
    0x307104250410000c40d0304001003088030740300a080b0303121303129103131450a50003406a0005229681c908009078001400b4502c811303d0141010b60381c181031003510720000c0d00c000c0880c0c20444a8181d0400c80d411500c41d60200c42040034800d0105a00500300c02031200d00450281001405080070003405950200d00e40d950001c01e207466290458544960014010001910011642c404003d1524280e001e01099030300040c1404a03c0d00400041c3e40c43d480135011318004d240a004107a00600e00b20426002c10000c0420304801c001d0442c3d191540a074132915a114440050314021f52100a11121051694498020a40709070190902028039a1300d5115210800510001160201c00005036200e00c030b0581104290a030708445499801071400d0314045e00f04034442c4130844d1054101190800c01c004110810800280c0d11420a015500f00310f105040501103420346080c8048405000141c81c510001d00202d0f40c0e2401e035407500c0c00d502c13501701c00740703600d1030048881c03000130300c20000c8001030040c260 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 500798174 1250 500796924 500796929
    0x1031526010e1005070809071a040e180d09050303180d020a080a022115040606050a0603091110140901051209060402030c030606030a0602090409210e060304020a030807030c0804 78
    0x2024018070403802456500300c1e100140b506045c41b58071004d00000e0140007408906030351105d10481980c4100c0c80c060801c03030003070f940441c0c044c1c6c244030200154a5000d14a00c4084180c1c40c0450300004500201994090010701450350564414040101e800000e002004942c0d100640340e130307051008940100300c0d2000e15800401ba582d0000440108600b01054070740c1c00c2040301006071455180e1000b2550305c40d0081c0301580c020391102e401080034003101d0740c05400107050040000201c00d40ea614050060203a55205540c9900120f1403480384e410060102c00c0b003144196113444900080700c4e404141d50b0009422139040150500c040d4412110403050a0b0145180000600180c907241c8105450001c0a00000d0300071b40014040c0700c1e540e200000c02d1a40c0c2ca600c00c10150301c440241011500904540c14058240303c42084043c80e0a4040240a020030320240e585840d00f501e01010b1081c00d120644009420030441030040000c03070024000742030064032a04c1c0203e00c8903031946944d4003a81198 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 500799424 1250 500798174 500798201
    0x50702370b010e13020d02221e06090c05031f050405010306020d0c110624030604080a0f09060c02011b0b010f051e091317190e0103152601 61
    0x8a0040c88003220050f0065444082c81d56218403920090f40440c5151750101002030040f601208000c42d4202c41400c41c01400407940030400403c5001c201c81852942c00d040004045441c050000c142c160640c0a282031002450325104e145468224000003408600134851090041048021400e5540d50003041d00846c0120030151b11991803400302c4040fa4410301b04081484440c180c3d0f80d244403c0443c03120f5006003c21202c1c5a0100c06074100d040c4a02450105681401600204000c012212001d0304111400b0759410380070403058001a43c81940c240544c0000c2140e0503600d00041d1700c1510382e0144601d818a4801ea41c44069a9120707040302d00b030304074155006032840284002d0406102d000540280728160030100ca9034040030a1a1442c0036011411b03102e0920007030820300080da82c410b0b030003000e000c2a090751040070680c3c20704145000000000090304009250aa81d13119000d00705482250641c00e414061030b002000c0007040b041400e4000f030740301d24555049085800c1c03258082d22100e5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 500800674 1250 500799424 500799443
    0x609010311010c2a09021305040506031f0c03051b0412140a050a1403090112020d06030f060501150e090f22030e1305010b030a02160803010303020a0b060405070237 72
    0x16000e04e1011258141c000028480c410b120308100c894071540c4a00c22103c00f41c2c3c0001e2580c0302c3c2000f1a090266100c0f104009a14411400c14511a950b1212070080340581e02041652200801e0344942030300c051242c01c1401091100b0312030f084141c20704501d124030031110303050700101c80c500082c200580c01d10240c40302c3d0040b00c06101402110942902d4000c890b0026600c0c090540c0d001070b000e40c0c0d80082440d10a0781c08280b00c800c5a0310b551120010b9500955803841102d540e01d0041c0c040c2c4401d01030400c00020906854a4080c02103145c80d143d40d40c0207141c50010b50368a10350303081c0c811b002041003201720b00320030340d0348100c4c40d032049034410241c002e0340c3d40c0c45541c0c840401e0010810b090303a81e0f03141e2503280000402005c0c60080590341c01140d00040175a8803462216186d500001440c8050000c40000000104150300040d144160b0b500c6020048a15a50b0a040104580044441c240582c200000b1401f4040100c1c1e1080141400d07035011181d050090800f04040031000402150340c3c45c0e4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 500801924 1250 500800674 500800733
    0x6180f080f06010807081e0114100305010c08060603061c080c030a02010e030c0d0c11131b0f09170703050313050306090f0309010f120507020120030609010311010c 72
    0xb84546400f500d1203900800040d03190100c0b130742e900c101c0c030b0070390480d0141480084026444203410400c543d812644000107141022508800c0d0b004152008076017a40c070300080c0a40e10350041050a03c145e0700180704504659032a030500482e00340c0f410303101031035403030700001c410005240d440584142c100c2c0f00000c549a46600c80e01070b007103480c500c03800003203944240005210600e00040c1032241800a1502e00542d220300d140031225805058100b03980300880c8016001001074540c030808042075146a084019549544140c44440903000f590000803c2600284580c0e01a00320303134010103800c0d40c12904441d03900d4450b036045810039000030b00070a400140070042803908008058000e0b070ba4202a0a0114091004ca50b80740f0172103115605000c07420211403d49409a80540503218164200740014900718000a000349200849000d401c2007034040e105001c400310058920900014141445030f2b400c1d500c410305d145610300720350360400485c00710850000388101c1c21050310b001c030044d00108650 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 500803174 1250 500801924 500801953
    0xd02030d060f03020f0d03050d020c10110a080105060c0a21030b060307231c090c060302071104020c011d0c010f05030408090f0111030f07141606180f08 67
    0x80850b88100c14800300880280090782d81c40e54044003102c000c442e0080d03614031901d002d4910b030042c09000030b54a8404204040d10410218500014510710001000030317021326400c0d44543d0040b0802200000e403c00e005106600700305009210100108041303407400040e50f958444115200104e0407000d4001034460610160540501c800241c406c81d01c4500314038003058002c04c00c07561a000e80031040200642014035081500448030403171410301d05849803d10a09810018100030070084032140851030f0000303401e504c80c0c070a03107004036840a00c00d06481140740400002c0d400281d480c2c8002d560b075804c2c5c4002d0214030b98000d20f00500c688050310341001c0290002d0000708060880c141845010810403001035548003c4800d054004c0b1001c0725018460001211070000c20700c0c05c02d120b4440000c40000c50181c98000d404640c0c440c4402000c11071058180603201c0c211040b103003550000300f100c02d1140a006030380c0d0118950456004124007035039030000002c0c0b5845503000301e005421815001d40d140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 500804424 1250 500803174 500803181
    0x8121305060408060403081e010602150903040605040302060904020f1207030501050d0b01050108042406170313231306063b0a0b040605040f12020d1e050d02030d 71
    0x5210480e1042c0c00d20380742001843c0c0b514801000282005034038000204a500344840b808190311120b00440740643e103500340655500d1011402d809090b03100b5000446200c400000c80741a204a5964141810310395400d1142e5600b00400c180c0d032041d000e004851626070024094061059403000c0c611490400d1300f0080c08541040e00b200e4018a031004511000ca0301d030740c40e8075045034020328284656941e2420640d030b50300e0317200720102ca460b28040d68502c9541c0c0b0941003102901d00c14580c48a4100000e4006940d80c03042e08a40b0f1040085140c040001d15080c108103151b0b4003c410176400c070380301544000752444000c40d41c0e0922159648900748a11139008204411a00c000d116144080c03510118640409070610f4401c2c1e10b151000704510916103030443d0707120040030b4211140340c40300e449a0000d801500903020b49240b460702c0901c005445603903d20100ca080b038001c0d114950039405611404003510581c404030541a01c40000c02001a408022001c0701c0c6605030f01450b1901c040c03510382c5054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 500805674 1250 500804424 500804429
    0xa2007050108131707110405090106061709060414120c0714040e0703020f040f02180108100e010905060d080d0f0b10050d0207021f090f230d0309081213 67
    0x10b1803402d020f0009888841903440d4040075200300d038880e00c0925108010080c5020419001810002400940c81d0150816019142c40380c40700340f98500ca080445c2e1141c0310440d2503581c00e034040d5001c6800b00700044800c4100003141030a960607110a600c1005240d849000c200c01c8540c000d000030815a06100d5490143c071904403401e00002c030403221019919001e500001c3d124100450444816940307692190314603404602082d521000c00f02d0000741020071a030122404203c1150005195980b042d400005a035506138001c20103134200380034100241001003140346c00c09417001c0a0408038a250000d080e044251210109000c100007014009072407410840c03500503514040c10014140c0c0200c15615442109240140c82e40340343d00004001c92315440e40442088409080350400651000202c0c09803000c0401904825070f49440c00c081d143c8004075982c504070700d0036a001506103026031a24900760b0191411114194881066904040f40440c618950900000d040c0c05c2090720449000300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 500806924 1250 500805674 500805691
    0xc0803220b0d050606090d140706050a0c060c020a0209011403100e031804090f0305070b09071d04030c060509010b04110304030f050c010225031b080a050a2007050108 73
    0x581034078090100c08a8010021044405070701c03800000ca95407124030564900d03810080554602c0085030520284141607014004003d0040d10f6003ca5003500800884140000039518500c41c42d50985580c1d0080080c810034a00718029910724130056500c1040240c041d250701c0814050300086401014030b40b9520f4071994410354200811100c0c2090080140d800b1605411406025079500c4d600140c010400f40c08010a0803408038824000d243c2d1200161020601ca0038180d9550b0302c0307581c0301e1f555031840740c4134550503040804840714100d203031184110f410511038100003034094410381c2e03860300b90b440445400307005030f5480c03141c14002d103001d0140b6505400544841031540c20151802024440514081c00038060700080350a400e030380940c100c4038880b03021644a042246507000141c24504040030903000202400d14403101d00c030b104860f14902c0da9101854601d400c81000003a03c1c48d80285420740103018a620042808540086100b02002d0400026088480c28240058150304002d1b18a08 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 500808174 1250 500806924 500806987
    0x2061303200a38101e12060608070f031101050702010509040501090b0f090f0a090203101407080609090c040b010908061306050f161209020d030e0901090c170604090c0803 75
    0xd031428004c0307400c000d5a9100d107440c0030010421000c00511506580214150043c0c0d285043c10b00820354040010743d50444181d03211503580c0d803080600e2144c0c900014103084103c000c41003441d8003480042c4050752040c1459401c02c000e0748000350407039100764400280310b0784814142110f4904407083d480c207040b0483d04164981002c0300a5800030600808110700c80c0e0b03850408000703654080203013085d450644c4609100c122a07010422442d4102601c803440810b5190000c42c003249000701c40c141c4103100e24401881c040114800300070151a0f40030385103050110310800070510460178440a4803941004a0500d400402841c0640480714010147d100505020301801481c00d040e00300380c000140303180381486060350b540504500404103218003c2d8052546004ca204250b001103405a20450482e010780c0f5580ea201420001e569410b040500000e803607004050080f00300a90300303034106501a10000710500c00b50b8030700701650728a4100b07000f540c0c404152501442944038a540440e800101400d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 500809424 1250 500808174 500808181
    0x501110c0303220228050a14040f0b360103030804030c03090b1c06060816120b030105090f0c01020705060d0504210903020102061303200a38 62
    0x68a9001c081c10305480d4003111240e0008004007400c3e202c1d03c0079002840300304c15006000203c9841442c280d81d02241d4050074200158528160b000241214040d0f00c410a90300c00010030080101843d1515030345141d900c024100d019240c1501c0001001000114100b41550380c80c002d4070245c0403540c40c804820100801400020750041c001c64015a050400d42e49480351481c040d281c81c0065000009118404a1240c01c80d00007044208804540c0c1c0c041004020344a040c01c41e01c0c41e9085801d01e246940f200d0b88604014400d03c0152450328000b01d00113a0b07001c1e210002400d50350191100d60703031940100407240c680101442480d19078042400103044051070a00840e0040c0240c5401c030701c4041d078400004060000e074200509030b51603440c40c40280c184404901030b08031602800140d005100d445c0008100c9114510b40846031600340d16581501d0b000000c02da0640c3e64070b02910351080c000c03059400000340782041a541c0725000e410b511000d030786010b03445042c0051341444000704a080d400a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 500810674 1250 500809424 500809447
    0x18020702040b06130b0a02100c030c0f0f020d0c050a020402030108031e0405030a230d0216091107230d0c02130b0f271006020c0307031a04030c021903050111 69
    0x4c042141d0700601003988401c00042e0590074210404041d61075a0304044250002c542e00d94041c0d0403642e12030b100c8098010050b07000702c8108414110190150b4081604d508405000316003000c1d0140c45001200c6940905a010a050340c00030380c0520745c0380d400890420440702c031000c0e01c0c40d02c550503528107900301403a0400103941d0358040d20000e494600310021044021000f01c0841202c4401e20040710803405c820440250b6075080360700c11450503540504040342040841c00755074100c02e01d6161413410807146460342200c503004074890a5690003000d180582901c42800a0703040b000603a00d808681195070300502c10744c48541400943c03550700d80245101c16a649090100382071a090301d105480d002d0782d040108641111050000950842c034003005000d40c000700803041030391415800d440c0745e11400418142d644541d400010700c2c2800b43d415003e0388410b0000c1c1503501c5802440d0501c0c0d40601c540200300d1460100e4030442c0c0340107030150148103202d024001c0002c105110081245807039a003003003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 500811924 1250 500810674 500810707
    0x303070309031203020f0a110d02030c15100f0b0901090b1c1a0d06020706140412120209060c0a0c0f12060b032503110102030f030a021318020702040b06 67
    0x51401080d044400c0c3c0c410310a42c1610107001c07060420036a2000340100203054100700c00708030300062060f1128070f01500d101100383c40780c481150307000701000c003801c4071903035403041c0001c013a40c080f000409000100c100003500803d008005840020b603071989040c000400108183c2c21140b42c0240810184844048002001c43c10035a800c00000d89050344110010072405401c1026030300204940411007481000e60050800e640300e86006c0000c0c4404968445942034200d4004d0306018000c00b00c10f44040c05580c520100f0f9640c1000186050001400140f59801c401c14080c0e07150f202c102036a0800036013a0300711300500060000c1a450a10b1f00c14000510681090001c0c036454484c6416a12500d04000d05117010000401000c40d0520754051201c080d0301c984800c1d150004441e6200314035500100460300b8481c0c200a032140307540d5520000da000383d40810315a6411100da075200140c5141c0202c0da4504040c240d10001d6540c141500400c03013500c00d1030304802d00c41c400422110f01c0001ca04070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 500813174 1250 500811924 500811929
    0x50901030317090703080a0210050f130b0910060f0e0f10060c0311060f1009020901050a0318050d031e02091e150c0d090b131e0305100b030c0303070309 67
    0x21200b00c0c0542d5048111820410345510041c0b02c28004559082d43d80d80100d41900800a0841c08000701d541d1244880c3c1e182406880c0b41c1040404520030740045440c08101c19071010b11035041b104101120b1502d4011100b59a01294801190a000f48911444102c17400c0d00728101080d0050a410b180c1654200100144102c5041c4180140400101801442c00e54ec4484003881034400720304d010311040d4450403044601010810b210ba13800b00d40c0301c401d03200342c1c1c0040d2010380d00d040c2055101035003074000388000140350802000c21030704400056801c01030b4031205070711342d0b501090b00705200c491104050090008440700c5401030281d6480c1c2c0c0c40f48401c103210032001c3d52041e00c2c406013070004900d08143c01080c1c18000c2d10009428042c1d4440003441640049155480100e0f26541ccd2040c40118060b54a1a200d1142200300030400c902040c801c251940190500c18440e1a0782c0e0380d50341e450f000c6824121081c0b541c40366058411440d0500050142c04002da024500d041d400780d40060900c0b1050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 500814424 1250 500813174 500813207
    0x120106020601153f020d020a020c01020a110f0d080c0c0a08010c020a1205040f030309050f04020301050f2101020c061609053102040806162606040b0307060c0c0509010303 75
    0x1544420312001300c54001c0101040900c11580c034854051018082c0d4480c00010b405880740c400b50500035440091a0f09e085078109903608211789800041003001020200d19990040c5805000d10100d500d000c001c1c81003034900d070001c0501140700414810300c0041a48507201991405801954541d00402e400303d1156114030440c2145001540a036894015600000e801105191000c000c243d000717071a00d429038004039542206140c1400800003603100c240a01504030031044150019420f000186551030380844000440030066440c4450898001c40c1e6010301e41e40c040402c2c46000415181c034440d800c10185003100215083c80049002c08041c5010302c011000c1c03550380b61004c18003001200043c0051070341c0541d036a9680f11400c95031400240c55040613401c05e03070382a50034540034200c003108007a50142d840041180a100100390540002c0206411503118503203900b980c2e40c00c0c004c05014110940f61100d42890b54102048440c3d101e4100b107005101080041c000300350040300c08040703940304 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 500815674 1250 500814424 500814497
    0x1050a0528150801170c0109091e021c0531060b150a02250b181215090a032a0f05010b040c14070f0812010602060115 52
    0x1da46901e40010350741d070028000c01c8407101001c40195006280b24100e490808005a0322030001c01c6907621440c50301d484a02103020090308028000494000c004020051144a50254540542541070364084604c101c800d00c40354080b00b0061886218060304081102800001140140c90f000c01c40a00303250740022007640b06119408000d0a074100103038002003e0010100d941d0b81c500d007200c0c641c02c9241d10401502401810700e04042c0e0404c0074000d05a50310740c61041c0c0744d10304400c0c42c503103500043e10b518801c0c0b80c0307088030005520741102026080703032103030010310540c02d802401a006c80b10142140078990001009100465402490f01100e0140e46050048140300807040b60040341c04504d0080441032038a0001c4244101940500244c810968080c13003982c0300c01c0012900d42a03e1201e1030360044044c0b0000000c104100d0312040c01500c07503c4280d140032400c10303c0141958007680030400591000006010080c080da04512041e0f0303682c202481c1101c69161002103140c0c0d0324a440030701c403c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 500816924 1250 500815674 500815729
    0x121c030c03180503180d06022a0a020102120c070f08030a02010c02030a0e040b0d0506040b0105100c170c030c0f0703030210060302060702040504060b1201060e0c032802131203030501050a05 83
    0x12504840c0d404941e02402c11503813045000449c003091000140c0410110f940798181c01138405000c10389076519541603000e41071940090058010580007051243d4943c46554004150040b110102c034004e00394170001035440303150041d8003d0a403240e40c4030040441d0414858070000c1a0050301c412042e000031980422001510000308a41d16110035001d0518810740d41400f091140d25400f450507118250341030143c1c10a03a00d015241800728000040420080324010240c03512170740c004d0b00000740360b481507910744008001c9441c500142448940c0480d00103180c00c00030584c0411101521503124070092000a20355000500d4502900070042d0240c0e0b11100014100300f61544800c01c100300090000714607010007120799000344007500452020507100800320303200f07403014416a0300c103030405c0404a40d9094210003240055004c02c44460406400780300d03085901c2000c42011014002c080a1200071101c1803d00505844c0c0680c492800303500c551400344240c1d1215482c09442c90042009140c4048 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 500818174 1250 500816924 500816929
    0xa0b0105070f03050720010e0105070c0f0305070e06191e0b04080a03090e0610270611010513051207020f090f090d03020a0e121c030c0318050318 64
    0x40361881c000d2400c42d5903400c04040540203805000d074a40030b05546030646001c45600f0014201810110780408c0c000c0781e5400c0c0030744c400c1000340411841115060343d10303a070310282e20020240603002161660004c2200b4031076400201c003410b81c0260102c0340a0000b048101d19200384050030300401c070411112889041c522503c000c640e0004007503501c1c03001c1c2c2d07683d50b0314820790f2213081d19141280010081800000d1a0a030903441c41e0059100400327030502111740032015601405030701051150a900c051241d08090440d00105d8000d10481c0caa40406c4548004040c0c00c40c2c4000703000000d00d01c05020190301040c070004641c0a4600640c0d92542e6404c0b9074000900c21459030003c46034041e10041c03c2001489118403180c0c01009010308944968116040c150300741d00030401900d0001c0c04601c81c8240358030f0106e40788503081c60359400f6030720310651080102b11201c025911820111b80c0741c00f1042001c0c1c0d85071080740107036540684e00c03140d1704400380d0b0b4170b640300d109580c840f520400d269507150710741d50f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 500819424 1250 500818174 500818177
    0x215040c0504090516180b18010e040f050607020a03080106170f06012d020d050c0c01050703030b04051e1014060315030a112e080a06050307060203040f090e060a0b0105 74
    0x1040c0f804c8164140346e6031403481c8606035903808940608030342098965803043c1001011031a00c0e091106045245a08201b9404160344008005a07000d0341d0342d030703c1c1c440429003d100160260340140c3c0981a8101541005841c1807010f1b4016070400c414103500c011400640030f0000d030440501611401310ba2650001240c5104c003011840c0c0508006080b00e660700011003000c1007546100d0780940d042c1c542120801d89003070081c8041d07140385411440300001c0940c03240c401802034610a080c0016200140c0001c0390407600b08441c0c540d1042e00400038001582c21420000b548079400c000c58011b0310b81070410000722081124060f500a00c1d0100100d00480386100010041c410083c0403284a07181c14100003803031203516070515005000203010100c080b1200e1905013005200d400780b8582450705d000c8129800c010090000386881c0d5103002c0816255010302c1040010100c039401103417900d00307100e43c41458074800e80c4840829803030115503400b10280415100d504c403082c11000981044101b0042e6000e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 500820674 1250 500819424 500819443
    0x41a0c0a26040e0a060803040605180d06020304083f18030f03100602030a052209110a0305100602070611030c1e010c0f08240301020315010215040c05040905 69
    0x800c0003290200b10b8007070802500d40f24104c0424148496a40e40c05601d0f1244680e01517070001640420800e48041d00e01444c0c0e0400800c00391104080701d1845d2540d03800c9800990b4110342e40300000500c811070041c2e542c0b560383c5000d143c20200114220142030705260326110b82c0301c0c00031115504002407906482c20042c4103030b0002102078a503900c0c0a0014000d66500403140342c1094800e02402007200d510000544d44000d415840c4c40d490818200311180d60f6810f6010b204100300c414081c0400c1c0281d0034001c3c4030f0200208907400340c4030045a1805003d6400c020010f102c0c1f214940c00400420b580094003004442031410000103030b102c1d00c10240e042d44074024046c5018442d40c8580c40c43c2e40803c2c035a0f50a0518114020080340b40b400c50701301c806c28a40b0600d800082c20720713400f080c9041e42185006801d0003040880090030031404020a007640c00880c0c0c883d0180962804007849540c0510000b00045480c400b041c61038900743c2d491102d103604d50301425004a640340581010004200209082d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 500821924 1250 500820674 500820743
    0x5060a053601030201080f0907091802030f0607170610030e100513020109061e0503181203010f0f081c03020c1e100605010203250c0605041a0c0a 64
    0x180c0000006858421003070a00c000c9000900d00c400003506c5400c1c01000d0340c01440c2a001801c02545001c03940c4000d0b00e051f803451080c0c081c00c2c18000005990400c15011414105000f44c942d615004402074030281d00c2c20b0b45070f8240c14072141080600d40d5410501c040740002c50500140781034214110302e10b00640c0c070390701c0c0c0075091034101880105865805141c02d140d200341c2c0e43c0c08036203855501c200c404036884c010840c040301a40103e80a000e000310f029562003881088181e01c00c0301c071404041e1500384504a070724001d000000c010710000c191f211100020b004a1010310021034505480e00d42d684c5c0e59040240d1000d40804040d1621074426011a01c007130030303500c045078044128100300034002c03003c00c031000a840c030503101e804640d007505014850403128141c01a6041801c2000039036850100a403d10a515400743e02002c001112680300002502c000c7d40c0c0c007519241801c10a5074822001090450003000c2840084001400000c1c48442c2d994010b404c0e903250440e4144c00008419407240581 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 500823174 1250 500821924 500821999
    0x507061112040b01081218040b190b4902070c030b15270408040b0307091703090d0f140d02010b031b0a03020d05120f04170105060a05 59
    0x1041c040c2c410f0307501d07060360b403c0c40c00d03a03480c0c1007203084c410704034822a66060240ca024900346c0c00725103441d078042d803034100c00076049511122442025280851003070700302041c0b480300400d40e203602d4039a403004100e00d54600410004041040e502a4584100c1132090002c08091204804c054481c140c040c2d81600d81e1241c600903540f512441c001d4004041201c00309405401100b0b03036a2a4a07000f0030112a01c070f1451841a480d440140e030f8600c0f8100004d10542e81001d0410000903c0003006009520401c629600e001a503818400c1036080081412000b40c001e60007070280c40030b9551522200040b256000001040d0391010307103825040095980880003050040444031001c164064008140c0091708078140c03007030000741c1d01080c0c00003080401c4864100000706418401030410703071840250140500122a10340e16a200d10003800d5109030020503c520700441e00300718031200e14036041c075a22012002130006141c0107005c56030105162054078400c3c0122103100169028065500820801044004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 500824424 1250 500823174 500823181
    0x30902040c0503091014060616080703230f040509130609061a031605010c0c030c120303140f070f050f04260703030c0305071403030703140702010c0507061112 70
    0x40c0143d001107801030f802d406000300d141044641031007109880780401405001301c0d01c80205000315030b00300d050340c00310200100042d0000b00b100800130f001624070036601c01c0221185100101074400d002501002003580034002030450f00380d03002c166000d4910640d00d403c481e59645042650085c17422401a2a19281c0800744086c00000c1d00031344450506002e200141410705400d269071080e001039114040001030109005a600c10503442c1e2156000304e101032101030702c80c2c541c1c801c001234603071001249400d10400d0300201500b60090035880c0701c50f00d9a02006107400c4182d05c0000390010502402c2001d030107021b41c04140250305440b6090030a0815603213170b40d11200241320781c0c100c101e4445494021070b01c100e01503141c00280d410550758107039102e19180100c1ea03002e6500d5004040b04803010241d82290140c815410000307507119070107568000c15000101c90030302910000c003078a80c1d811039041c85504103410b90071808032015250b0084000500c052426141c0005000d42480207881c10341c6403017070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 500825674 1250 500824424 500824427
    0x10501090605030706081b07151a0d030e300105061503060604060503090309060706090201030509010b0d031404080d1e09030f0f0303060902030907091a06070b07030902040c 76
    0x450680350080c5003040707855220400c26a03154051304c20b5034000b421000014500c00e600116940440c504001c426083c08140d503108010140d41100c0c0101195503220102140d00b48207020004045050b113010b400c2c4078054400500c603030304210206001c1c000c104004514800110440803050200942e4004d0600d03000020030b000c1d240c00d450852040c50328032201c694501010b4101d034025400200141d14051030120165000e800c0106402024002445080d490f0340701c035802440942e120340c0002582031114030024003211005400c1320240d07892302c481c00385a5281c0d9102c00d500b0b00d40500704200314494214030f142d10343c0b1650304180d0300c034020008000901d5800c284d9000408910070110102e00745071020440310720b0043d1002502d8600c0f924003c001003514400d2010950303001346008100c558890042034140d80c01914809400e07408100104841c1005202e0071010800c0c44024113580d25009000070130758010907001900400b440000700da00a8080d0f401310300d526070b0142c000c0c031410103891070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 500826924 1250 500825674 500825681
    0x110304120b060301110a18032909010b0901050f060403020a03030e01172a09030601030c090e030c0c0f012d030606030207030915022a010908031312111201 68
    0x90890300c1c1100031012414525040c091140c0032a04500c16a00b002c200d510201d41e4040d40c04a4508600340091000c800b00d002411410b8203900c4400840124a03424640d4829800c0c0c0240403c5c10343e49040b090014503940e4003001d5045034021500783d80e004201c0c00002e680c91195134802075210b440302c5000000c141e00041400500102600c442850754620300c0c103804543c500f00d614a021665840900ba1248084840800a0200c0582e07160403c803440c004031713103459020b80080d19408480c88040040704220301940c500703ca02c0d10042c5043c103480400c110b0b9912f8060152130f11032400410201030607481050300c4401480c0001c050b20a41c80b0508131400203044850140f000203041100110700c990183c002c40b408140e041d504ca003036030351400c02881e02c0103940070720f11000c500034008100d80441c4aa00060014003240080c1d10920142c40300140040180d580051000d80061116071251140042aa012500441a40200340e445850710304035100062040700c5d0f010004004904a1050560 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 500828174 1250 500826924 500826959
    0x14150c0c040c0908060f04240e0723060702180c03060306010e06031c09050409050304050f0a060909020a1e0f0905011112090d020a15030501140a030204020901110304 73
    0x1d504021071820600121051002801503500030382c024004141e07001c41c1005041c2e4030500501c0200d11144022501c040128222004000c03007540b950f100496580091103040014050700c0d90505117540b0111680c020080110382c1075100f01400b0801c40c046d9264900d000002094800d48043c0914200c1244003860b002901c4060003032282c6400843c10341e4840e242c507030180344001e004248080c4030b0101708205400307600d0840c04100400324002420b0f1500c0c00f8070042c2502c40c4020b15141cbd4104414040410003984007680f05220300e010070010030f80c11021160a45000410169840103400010f0710001681d007080354920400f00c410b0300509501c45018500549c0a079242103142e556800112865a2000c41c04038007900032030703175004403403084d10000e21a0000280c02c02c15242c5140d0006140004150300ca8140008204a295482541886000c0c00340060400c0818010302d942c020030320ac00e440b0f000080c00343d680010007004c070f0ba01810007240d5811141d812240e07140e0301c2d1704c0308414028402 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 500829424 1250 500828174 500828179
    0x5031f021c05090d1e0813020d02040509030c1002280c080a080a050610050d09030c050f0604051204080304231201060602210a030c0c0b0f0708150a14150c0c 69
    0x1440c8400b00001d02c1a400207003240d19070310050292203d50320122000c44400f02281d001e03080e04088001620bc07406220300c030350640d0026680799800c9060150820304420341d5180481c0c41048903940018501280210f40030f4000091509282804425960f014511b08003030600b84d4040781c00341c10598840034042c070a00301440140800d4495500b842504152003101d040400c07000e100b00380616199a102e140340e18000d28104011010079140c2600308000c0400c080300c1600658204028040e081000c08060072100c09001d142510301b038007076622800b550141000300281d0350790300303400358152500725103034058000c000070141c005c0c1602e594000d0402e445a038000d8010080c50501041c0e80082585d105101b003149649000307407007007044008106040c031400a206040404030007045010103401e200c1c2c070741e001d85c031a00b41c249202c0103403654100818034014141c9010095040ea100d4030840c10031102540a11060480e4100c0058088803540d01007004c0e020740440e441002c100300140003040380006 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 500830674 1250 500829424 500829437
    0x8010501090c12050426040e0115111c0315051e010e03010908042108070302010c1409030d1d100903060501050d020303040312030b090a0507080105031f021c05090d 72
    0x220030000b81c94080304c0c00381401c0c07044040c40804151b145c4182c2103105a407190b00d0302d070684801c400d64280600381c01c10521442c6401c28400740701c2d041721300c503c10756900000502c812400e5206441c0380d542a4108501015211030075400c0b1441400b0040c80a00720013001840200450781840009112100141e4002941030305107500781c0c107040c0724086000750020285440c10b81400362520b42125201d45e8103c101c8000c5e0700342404201604044c0c08424880e0380040751151100400030039034240c4040141c2d078520200950160740c0d40004000c1c8000085040030154641e070001c18801200740601c1a81d001403e480716014680c0e80100d0107030680340b040c030042004d40d0f21503050000805c1c1580c0000d40582c0100014004150b00700052007002c902843d021405006403404140d2a02007a100e8080c5c00c0e0f00c03042403204181e0010245809850150020300400700e0064800203032041d03d0b1036148041d039001075110703290000c030b070f2203040c140b41900740600c020301b000503226680d40d0103842e040d40011107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 500831924 1250 500830674 500830697
    0x15031a06180702250503062509180c02120d0609050a0c0c03180b121e06030c1c0605010602031b0706082409041103010c030e0d0e01050408010501090c 66
    0x8030818051582c5500038118080003c05248030100f04401d041c084101c892400941e80d5010404103104000140802c0051003201002d01d0078100700704226000d01c080b40c1000e00103100048030081481c10303088404219800c10540503030801484084a04890300005516207480e1245d0300003504490107814200020b80d40e10410100700c1d50741c8070840300094541000380020900c15108200340b40c10624400c070003160349c1c001c80c0d107031680711240b0721031041c0e06c06040042124400380c91104020759181c4c7e03102607103001c100290b141c500c21a2154496869801200701a01001c1d0140100c1d5600190130082941c5502d00656641c0103001084628581c0260281140c140810780c4011140f40e5200c510407515a07148160803860b4602e2500401c0c20f19a019024540d511030009010701d0203102400814481d0006040c01e6031124401601814180086c0c0358007100c000881c0d09561604c0d10740119400c2452004032454841e07680941200e6091000206858000d544988440c6510b600d412030240c5c2d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 500833174 1250 500831924 500831959
    0x10c0609051218040e0c0114130602010c03051303141812010204031e0308011a091810091415120f06060117070203031305010f020a0804060f02130915031a06 69
    0x241c1403031070310303103141c0014070003001650107049807204502602300d440342048400e10410b1510b10040d40042c1c0182c2d190500301d50200d030107218240c2c2045101c020b800e6030564544000c3e10b544506100c006043e00b0010b01c03000521400080b6030561040145100c08450030745280f54040d4129000642c0c1181c040840b1010803c10340d1820400c2039403503141c0f10010383c6403108c3c460440a415a1181d0210300401084495560b811012248001e90b6034001582d81415950741c110100a50030015925150070345612000700c4c444045584035814101c42d100b40000000030a003240003a40b800302c9117118115414602d050301044031880f0b80b03001e13a0b03241c0d10145c0b07021502020380020341e920009030f001007001c100781c800c2818003840ca89000e030703001040320020301860200b20f0303200e03403034080c0090804002e00080040300c3c081e10300d507070002c40000e40c140043c1d00d0409800021f00c0c07140b10082913585c3c5103418515484a458402141c00c01c290310344e4111840c51040380c00004880306449100c1c6c000c040c18412 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 500834424 1250 500833174 500833181
    0x609080f071508060409020a08150109060620010906020f120702030f091908060a0f0f1505010f030605060a030f1b0f14071b0503210306010c060905121804 68
    0x110300c5a801118418242d0109840303a09000c1c124640160722040c01e0400340e2903000c02c840c010010b00c0018281171541c9000c021050b94180c0020060034100441008055840700003282c0b0314810388825904500340b00142c5005010840303000341554004a503a46881001c0d0000c0d03c0752801d000d026000b95590752004980701d200765400b1080048050025030030311f0429422140030699a50002c0081caa19000194a08402118400341c0c00c1d031a00e046020f203402c83d00941000d030000020902a03080b50b4901d11069442d6401000e0400600b83c106845007842604014000c01014041c640c1d07800711008000c01811119072035005c09810141c00d14407403803039803d0300c0e41052420740d0341c00300f060f030044e100b201c25690768158224050002d022910106030707501030308050856541e041100c01c030b00c0d110905081c00060980490b03000388200716043c0c2400300404130381c0d00803001d20301051808002d10b40000205066900030308684100100204030040c440700070010758481c0302c03c020700d0032100020072059 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 500835674 1250 500834424 500834429
    0x1006032607031709030d0912180807170322140d0b0705090f0402030f01080d050a0504140d2103050105030c030705040b04060512103605160609080f07 66
    0xb6201041890b0400c0014003004c0c0c0044480b4181e074584803583c01d01006440042d1000e030f800d065402e00080005820a00f00d110f000c4035919001842450451050b07160006840b6944580039258400c95803110140f0458000c00d0704a9002210000942a070201d1f944050241e4508000d0f10042c14125150040a00440c150701004000c0b5646d00c06008503810f40060b00004d0300a500c0c608101c3c007035035850000d0340c8613005041580c00300d036150022584c80d2048441c2c0802c24413030208020380b01c1e654030904450980e08024628245031a1074001309200d031480325405001420a89010045a10503a81c02d51040c0c9460307030244003903600d8408254440f458400d040b54198880d44040200c0c0c02d15800c80d1030a0702000340001081c43d612004030b0221004107250b418550403188003581503090b04e109070301960020011007028280f8840c81d120403003542c44007844030b01c0760b442e07041020041e0807c42d84004501c00000103c0c4203694480140060b140b41c020f4256a0088083c50a82807000143c20403c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 500836924 1250 500835674 500835677
    0xc030c1e0f1306030b15100c02040b2d0d05071202010e0406081e0c030a2402030f0435070212071701060b03040308010528031101020610050f060c100603260703 70
    0x4070156060801d4440880030f480480e04035458654240c11581c0b054081e440d80003440241031049004042e400c03900248003300c4a1180703070aa2120b10205200098000c184e0b50380c0b40d1034850406a900058034040800340c15035600030b00380781c0007183e100000b06240080e507030b4001d4480101800011425118004007440303941542c001d14082000c2a640021100c000a1210740c1c21483e070380521b0aa000d81e44100d448045058041d8140405c200700c15040c400044115100c00c0881c001d013038800000762441b1001c05e03800a40224091081d0360703e41560505044140d4212292940c0d0380000d040d40c0c1c094454000713031035445e11000150f8020200212072040e941b42c3d503112216802c0c03d08002e41c1c0e00101641c08400030180c4640c6000d013007103586180c01355005282d0100220307038910009140c260010b104000b00100f411040000d912030b88404e020001c030860300e40b0b4481028800d0580b6207100c2841e03a1600a040c404000309100300312014158211000a15903049000c00303040c08614403034001d00a0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 500838174 1250 500836924 500836939
    0x1020604051f0b030f03040312030e06040f060e061f06080906071107080105100e060d050a030f02010f1103040501050709080303131703040c080c030c1e0f1306030b15 73
    0x294802810b40d026a0744030100d500081c14142c6440824641018a43e10022a600002c1c050041c400d000441082540451409011500380d08200c03a89401000d003004011400f128004d41c1003200c00c0d04600c0820f11101c00b110340714a0200188920060440740501c9002c444140200d80d40c0d114800c42c1d0b2081040900808031500c0d4040100c03410b90702e41d00100c00d00c0c014841c0c08102e601c802c2c0030f80c3d4050910b4528180d0701c01c1c10503804400c40c03400901040c0c800c0c2242c55418000620100301401c0494150410b458007c441250a9000d041b00507402c000a03458030006040000808000c1c40c02580108020400b80d03403200300603600701c411401108025441170000483c0c0d24032545e12240d00c584202c0401c49401049243d0002542080c2d400f201c050b40b184500380f0824004001d81c1c82090310840080c20300d2036545d0003256a40b18080101e81031038005501e042d0383ca80310b120b0509514000a4038919a910030100f0300701c0182031600003114511300c4c100c0404c0000e45180300c06000300034000e0046 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 500839424 1250 500838174 500838193
    0x703150b0f0d02030309060a020601090b0f0102210c010608010203190c140c010621021e0f010e0d0c06020607090e01140603150a2c041a0c0c0610140102060405 70
    0xb10400c0c1c40c411080f03070300d44030070009070041c2c3c0c9894020f071060150030f800600055040c0540031064907a0071403402e0081240e60501503190380d00040301a80c0072402c0c44c51307803883c0d1880e41d084040341c4640ca02c924210b601f000000270f1182c40540c000d5204560031400701c100c41160f0a000c2050320843d0740c60030001455003407500c9600b1540d03070052000e40300c000000104255194900300030080c4408088403004910340386103081d410300f030003810360b1203102001104103900204005032000310f040c0c2a56040048400c0400590307155500030320040f640280c080300f080b0f9035480009540765021200940091024540002e00840d49090319040e01c880c2030402d100c540203403060155940008044d0307420394000c916510450b0312150b00131740103006847c6010f040307002910324960000c0d10001400350304144600410001ca92425216412613603900300807120380e1030b0b1034050b122502507140480e106000b00800c2c0549103030060505000c0b904810510440c4e01c102e503005a8417500304540c003074025000040346 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 500840674 1250 500839424 500839429
    0x305150a06050d0b120d3506010e01031e09030c0b31020307050f0301140408031e09120c0f01060b0d0506040b0d0813030f080409050609070c12050d0e0703150b0f 71
    0x8101e0604900c49025885940c0360950103185001c0c1741f5103040c015100b4144001e559000130203002c3e1200030b007000e22600d2111100351640240600e100021a41e50b0070148003003510030341c3c103112502d0300300440d0030711400d2010041c90b84082081031000f10070301d842c46003481c0f48603110302d0013140c1d6001809407000701c4c40c10060001e030080884181e40d155507039410288404041d104007030300850061711032685902c1c0000b0700c070450034049201c050081034900100400c100300003486d00204010390310800d842d02d1003010058940000d06500d1046542400c501060011284002d046e0b24901c0002c1440152542030a0000300c8900603240c0380c1000355901a00d0200d038100f402491150382d007400c007050740741d0349031120f0b080c0b071042c95400c43c1c140c5c00c0008c0c10031402415004083e08100d0849a501141c00c02650240003425000401410010011503450120380607a040d00d104a000b9581801100f040c0303d203d903125a1079000c100c0300301c080150982c0782c0e1a800d05c074411101c0400f400200307080303440504 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 500841924 1250 500840674 500840687
    0x10b0405063312040b01031103010e1c02031b0a03120603020d06090203071205060412020111030103031107090c050d0f111806160f03030c08160305150a06050d0b120d 73
    0x30b4500b80b00c104211450f01c02d800c0400042c8604d028900c10344035541180303803590001108580c00340c0309130704205501e4007010002c07a54079840d00061030055140208810b042c0d0441c09459410a0b00394408107088d0300c0a1b00105152522505c00d9585294804040c0e8400e000c40d0b00c00e010180d0803031264219040050100e500c40c040007400142100c2d10b2070740c3d400b5039a4200c160034000b11180e4001c50103102c108001c0150890171850a40002c3c04100c1ea000f440c000c1c940014403001d0100f1502d9001041407200c1403182d0300191442100a10104c21124000b03045684291406174409162440c0e504140d5198815488411200d1121a20b40040c460140c4080860400c84030303801305040004c5e120701480c030a08499154440c61804081e400603090150845100a02490070f00c000d100c20859200c0091100552200503420001481d07285c48109004414800c1c10043e0452460b5802082050f0480040c0a1301c508148040c401d1503582e0083c400c60089048802145900443d03050342594000d80 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 500843174 1250 500841924 500842009
    0x603020304020f0a06121803080f100f0b0a08180d051b0706030e10180305070f1425150503060d08043b070f14030108010b040506 57
    0xc0aa03011021000002480032249600120206d010501d07411044406402440350340c02c4812030310000c44c2015207014201c610001c0c5450f00c024081000200c0c285045090f800c05030885200e5441c0045e00c030518120260311680546011404140c0090a4060300f0181541340d08000c60213401c0e01e840340c20064a01ba048272032101119a2800c0303446003245010008030300200980d960100d42c03101d1101e4642d0400c0208011112900d0500b140602d6215800c1070407a0802d91502d4880c1d5101940c0c2802c0c650411900310085c184040c070b007a8030310540c00004d0a65540107084414103410051060300c114051340b54030030252100d03840315055038500d0082c1c0c051548103601408040d0190015640ea41682d40150090a50110b0003019078610030b10f81085102e1910342c0407140040e0040c0da0764500c0e0210b070010141810001c0c0100b114152600c16000030001400184d0304580b03035610307103003418080c100020780075000b5841d040000310580342c52000c0203901c0f80503561210109440900e084c00494522 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 500844424 1250 500843174 500843179
    0x2315032e0e09030403061103011d180f0c0a0503010917070507081c0306050a03031205060a09020715270303020a0e150702030c090613020c1603050a0b01060203070b01060302030402 79
    0x240000034400d4410705800c0d110303084440c0903558071820761030404212120a212a08082c0c0184018001044101c44014031111032405040c0240c2d2585000c1d559000b01d051428411302501b09401211480003c88070a0140112a40030705251580141801c0310440000a8164034014030003440d50081000142402401101500d0130551194251445d0180088010800d1f28080000c094007661611801c0c010f070508072001014285152001014414800c0610203d1981e4602003030182d51290142802080903460544d1900c40500700900003074003580c12450010f042c00c84c489004c0001d92410710b6281c00095074101c02d0300441c0ca00702d0082d0400164481030003e0343c407002c0c035a51707940010010025030b65085580d036142e1600c145414025000703080c81c0202481010b0161540e2802e0101d01c55680c1080300580703c580b41108945403c0c07542d1004c071034182040c100401404004260f003486c0f280a44c0c00141d80b66a0354408a80d24030688401406045440005000442c0320350011074005000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 500845674 1250 500844424 500844511
    0x90b1608030a0e0114070801060e0f1e100504030c0905040308070809011103190f0501031104020a0203040506070609020111031c11090a060201050702070503070b040603090c231503 79
    0xb04000301c0c211601084001140040300c0c04006d8a5035204600c68050007152800f80000e610143c00b0400b00d40050f00414030540113004101c5440d04004071b40d80060000030203401e94405580d4025050b41c2c0a40800c0e1110305e810000420258000c0c0a10b502490703259403051610303514200e04881c25a80070700714402075500d4443c900c0c100741c003940c040c601500c081e401080314125105d0780742080b5003c01c9034012156007448010804160b01000455034090305413009079541110030b00407810b5220725044190310410100d000414480c6907404403120901c00c1c2c843c00311004c9206a40ca60700e02a03004170b03000b11505a44034141c1c042c01c603006210100c41c00e08101d13003488040b0780040c1e6100d61640050340141c1d035500800c1450f40e410406c0000428081d009003003031078204584642544618080d0380181a22107003440e01b04105581030344020301e01d00550078200c500d40209038000f580280c03592071181440c111185500581501185d001d4070b50060b211000545106400d11030211400c00050032500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 500846924 1250 500845674 500845691
    0x14060f15070609050d0e04150e09030903060a0b03160f030204020d091421040e0c0f0705070305031809060609120c040216020a06080412110c0d060c090b1608030a 71
    0x110b80940f8000b584168041c007000e09080f80010101d6410024551280342000c3c01c0f040b4550803103000c1d2050321101540e2100940d92651001d145124804855405114010070844404001c0d4051400e841c0203d040c2c9030016400c0f9550340b114407186c010703109240800300007000145010f41c001c00f031504001201142400b0380d600c0c0c0300409810051181c2c00d540041700e0341200c0000c00001ca100006080316840d05103402d2140028541400900d10070408800141495281c1110000c0ea40368507841000c4840480d200d1a00c2d0740c03070740c00c081c038036245058404c1c2e010350140ca0320402c01c40c03254001405031420444140204a0f006107145403410b443d0085101060321902d40303000401e11032103190f06218603e501481030110501540d444002003214020030b01002070640c081040300405d25180c801c104511403941c950414008941e4903520a00d85810041044036a03040b0032584c0c0050746482c04180e503100311301c00051080040440c034110411a451002481a0300907640080350070400250707165 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 500848174 1250 500846924 500846933
    0x801150207090504031d0102060903070f0c0b04030c0608090606010c061a1e0108130f0b040515011502160303020c061c05070507121812020415060f0314060f1507 71
    0x10f0041d07409500042d04c820510140304180c4121140e01b540c00c2c0b006214602e40241034030703200d00626600815120000f40b00400380403c40042c6805070494800039681c03030b40e4a01d8483e0340a180d07813013882c0201d614200010442e940200e0940c3c450001a100c85290703500b1960346400070640075000355594410018a10b01c50780f10040250305011405030040038044008001516905c001040f200c0c0e510420742200f000229049031090100f540650710703c8458407036140c418200004894a00700140c250300000440700c1c0b00b48114907095149809841c1c002140c00d1501c0003440f1540000340142c2e21848055005040c15401002030b1003001c2d81c00c101c004000254481a1038069440d00300252011551400303016000840c002034482d103050a0015102403036a0603c00c804c64440e014840307003215501000d5481c2e035041001c0c0b00006d070b1616074170151907a8000c3c000340300d88004440002c2c90b004400406c81110342c4094006d6070014840780c0c440c10000204206040795018000c90740c02c09100c903c0018 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 500849424 1250 500848174 500848181
    0x30902332101091e02032202010c050109030c020a05011b08090a050409060906230c0d0e03070506090f07240318060b0f1813050c10020a0c0b0a080115020709 69
    0xa010303a903404141c5601e00310804e00340020f0443c100304031901c10070610400682480074218180c4000c00c519010448a000503585001c010070302070415400c00506801f050390004082a185208031400b8450b07a031545c00444034003e40c95940b0400c0024520102c0200d0602400340519400042213082e03115140d07400700e03081c0c42d001c202c100c1d106500c8030020010804540602c038041c3c0d000c00411074900c1d8207403034402e0102e40003400d11111104001040440480b8130f400c41c2200c0c100d41c5045a980f0401d503e0099541d2400300c64040d014010400308181559001c00c01e0030031038100c82011007080c00a00200144c030500c421414050580e50041c0e40c2001d10780c5e102200002e40035980000b4001030201c107200c44000e080e1740c000e10403502a4201072050b100c0c49455900081800303122991082c3c24079000b07241000c400080fa40c080792540103017155039030000303101580c68410081d500c1003e6a41140902500421507801c0110711342e034005004170707512a5000310980b880b910449041c50384c0c030382c03051044 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 500850674 1250 500849424 500849429
    0x315040c12030806040b03280b0903190c0512071103060106111506191d0a02040e0109050402040b0a0b0403030e030304060c14150a020301150c0506010605090619030902332101 77
    0x19000da070b40d404070500c05143d0b41652b12075580740c040e502d40038288000e1240c04100c11051402d110701c845071042406400c2042c00c0c201c1104003443e9036940d560b418441c20081041d1030240c400e216a03400820428131940039403070a48000b8000b000603000d0321411240d0183c0041c031070380c1c11000b1020199581114002e441c0001c00321000b981c04403001000350b00180c0d0800501c03201d15240100020040114135503c0c0e503045036140c082c00603050f1610b1002602601034510041d9200b1035050000c00c58495030703c0100206c0b4440d45851840241c00d50505449001d54441c0c1d03408201d007a6400000310b044001603040495400003a11682e00c41070303800d40701d41c42058a06144030395010005203c0500c0280a840c0c1d50501400e040901010b15500c9550324001405850200b06001c951002c81da12034406407130900e001d5000c500d5001d40c4015004008010402060348607006a500c5111003202e074400000c1c480008a40000304514181c0c0ca400155200c41014007a00081100c6e0b401401620340c1d06502 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 500851924 1250 500850674 500850733
    0x712030203010e181005090a05010c0906030b040509070605030403180303030911030f0d03020c0115080105100b0f030402010807052101050111010b0607020d020f0315040c12030806040b03 82
    0x1c680d41400c0b400302004000034400300c2c085a042822008421000a901c609100f0381400428a1b645152840e030908a144000404641c28145003400094000007404161502c1d540c1c00c00422030302c0e5003007005071801518003400d16000500c0070b202c000d1144005692050007420840e8400f22004490f1480040c540d10131b60000e5503542000e000c100c85107011101c0c3d401c0c1100104403c6c03280b520719030f48428003c2c0c1c4500905600090400342500e00790001200c045001582a071015039612800b8080c203000c64001b88101c3c003948003c85c03012208015181c2e003038610007100d401d5a4690380103440c2e20038054a02c40600c0014400301c2d4204404040380e000392a0111968056945400000761080881d062908000e904104c2c120030740392518800e45000e250100c0d40000000310303d001050b152441124801d1b0540181050600c81c5c2020021035402540701c0c1c3c10001d503240c4e8600201c10541c2035444020005180311020510514164011a0103c00d0040035110105007801d412901503411032006e10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 500853174 1250 500851924 500851927
    0x6030203010b0f060d0e0708010c08091603050706081306020403080705060601020606010c02150f03010f0311030102090f0111100203150102011407140a090e1e070c240207120302 78
    0x1046003002e001d41181c4030030564248100140007000510a801038031311140381707640d0b00d80f00384111003410040307003004040b2600200304500c038004008100741e504484a01d031030721603400458080040440d03401c0841360400058100303032741481c40c00c5a01040181c00321001400100030b210108a00d031004000842c4034200c6590707610101d2504a042443c0144980e0541d0080c50410001d42d0704200746509166048038040d01d10204200200754030b000700d0f1810111640013200101d50b081e00c0802c401c5c1542d00683d1550086100b81c0304042c240e11518440b83d410071420803940000394050b5061040c103030b0000003603403070040d00003154a04a030401c448840000c030b06c00d1091421942c0a00c104024074102030308403145031816030005003803510440c08841c1d5284002a006044a20541090340a8941100c4a046a080008041881216616000c45003800440100e80741074021200500c50641c05001c0314480020380e5822210103074044100524140c017040340800061765050000040803042c0c5005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 500854424 1250 500853174 500853179
    0xb130b0a0e1801050a1202030102070b070c0213050c0405101e03020a090503060903030423060f070f112503020910030c05030703031d011b030f02061f05090c040e01080106 75
    0x8002d2200102e805010420200140b209484068031182178038060340100280250724808240284134480e030290068406d841404010b941c002848020709008440c410059a0002206811100207880062042c1c008110400030717428101a00d00e1908064101140d26680c54500c01500d800681c200c50002940050f418030142d41248800000c0e00e02907005000030f280011200340d03688070190000e0001104841d1074480c00f01d4404035000000c1d2202c05494003420005005403d01809035020004103d8000745100000d1058410329142041c0340700800d200400b040000e040401102c10710001c0e5101d0500100140e02d03104101d03805000e6000001e030010345941020b02012034280c114911076000058100042030740910b800920302d0000341e100110b0801e4100682d01f2101a42140350380503030070f021903018036800024410401d0040d401351100356681c50fa081ccc0a455064100d6a49480844030030f01103410034881d40399008645e4285030b80703419241c0f80c6280d00003c007603200d00c0b4941e4550405 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 500855674 1250 500854424 500854429
    0x191404081609060f030c121407060c030201050a05060d3801050a08011103070503220609021305010b04090e2b0e06070305030a05072a14070506040b130b0a0e 69
    0x4880080132199100208541550f5039900020660301c544035004502069140921250141810f21060070104a4000940c2d5240150500c002554107a0140d481d1100180d01d00e202401150300c10b40e001840c1c0d520300001c40d690b034083c1c40250040308241c0389080700e01000101c001c1c200c9400c200b0211a80c00b219602d414104107180c1400d40242e0460390504e1780c040a075550b500140d903044406800c00946941e950002d80d2080c020240c9840e04000300c4007500400d0110692100d03e96a009450b940c2003d0603000c005421303110280b0500c00032030f004000400480c1420b507c070180d48807004050310b00c0f061103181a40d005002040c0c09140110b08003850720900b43e04180700c4040310b5010ba440c1401e044458030040c00038000104800d25a544540004d44128401d143c94803803241010b050401480042d0b11141220b042e40800720f4a0704030640c4a19135a000c0002c0f00011540000c0085140c42d003404001a0660880300c0d40f0202c180c080e020102d41e070311100b000b030000030b071042e40c1e051035400d0769204 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 500856924 1250 500855674 500855681
    0x501020a020c1f08060d050c0904082208060c0c0f060f0105031c0f050903010f0c2a050604020d030903080a080709050108100504020a12110409050c191404081609 71
    0x101091031401003c0050249401c205426403003c0100c0740540400d41d14103006003007011190582c1d41c030200301c0081008110390f8001500300410701094403000295203400e45d82150501e8001d020b110307401318000442c400c0c100d0001300003410f0600103036a0500d102c40d540910341141520140d0340c42b00a80010300050404010022144d40c0e443d6010070010420980a85001d00c6030b1000c100300700c030009805c0f81c00d4a094000c40404810448200140250800d0042204031003000c0e442c00790a4070400110341c0a10803510809180c1c20801510381900e442c1d00300545040251400c90038095501c80c000041240d03800a410f4028040d04c8a20480c50f02e100300030004042500041e06110500c424003050343d4500008000f610f074140d40040c0d4810000c141507544003003d0003030903c40c40c1400c1310b05030481c04200c0a001110001c0c041804103459001180b603650082400030306105010b01d0380ca0113414800d90034010122040000e0364980f5403640545070a14030301900c2d1300c144018980c030400c00c00b1414403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 500858174 1250 500856924 500856949
    0x1060f0302100f0c0f0204110a1d06040f180b0303030106080910090803040f061d10050108010504150b010504030b0f0402030d05030108120f162105090d02040c0c0501020a020c 77
    0x3800c41e18500c090305004c1d14401d10030340040d000c860502d17200000c64803254011000c100c5000103e680b580c00c07012004002020110202240c000f508108200d1814408192401d550f1200e01e0105240c1c10204007044450400c02d4201c0b410385c030b6203c00e01403904c050000314060042c07aa1219210300d4044003591505e0200c454005c030941c941443c08001c42d003076001b6260030070745c001410396181d821810260b020780030310a510f4280b0806001e0706000c2c1800000d459000c4182013005000507aa00d540c000d00701c40702190f0103400c600d440504108860565448031a41c103405040c102d06240d2031341ca9a12501c242201c0c00703070039003911401744010b510f4108800f0100440d0352030039600c1e5604003904542c44c0c1c8040fa840c2d21144a000c110811200380c02015560301c072030b81251800c004120340c1804140300c6140813203128010907a20b0181d00d01c03403160040700c0f0708560141004c202e5003082d6003404001c101c0c031000300c030402c0010a400d0300021401c1c001400d001c92658002c0901004807020401901d9001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 500859424 1250 500858174 500858177
    0x9090b0109050c030601140d0617030a1101020901050a0f05070803010608090f010b0105090d03020f0307050319230a0203070b1f08010510031106040b040f140f01170a020c01060f030210 81
    0xf8810007405a900c880c50003000400799640c00c1c0c923881c1120a50018000c6904012110f100a1401e490703040700002c00340c007413044140e07a01c40d0860359000826080780302b8083c550f4009802041405501401006c2050403540d2a150451801d045911407000d10742081e00800c00180b2448140a19920100f01820b40071610000800003a088100040c01c6e91107060303c1140956020b820754001d15000303002e12180b200314141a01e0381c80354186031141d2030341c1c0130b03036810071a0340c00c4004001c00c80384c485c0e164966521022886400075008480c0b4660454002c1c0701ca030400c510080180c0340c00603805041c8540500041c0741c1d06a10303d01c401142c0a1011210742040780076a14006c20808201c0c43c02501d5400c0f03980081040c40429001d001040e47c5110740c1e000504610303400580000c203201c0d42c40c0c04008440c0d050030b18400d83c845810403c4034142d881c03031115000503644101980d03220340c0403004c80d03000780d0410710052400d007100801e80e00b520300c1a405280d117501c0804c010001e40c00e08004082800c0c046 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 500860674 1250 500859424 500859427
    0x60f0f06050117040204050613181a070f121b18050402181c0f03050405040c0e01020a11130c11010b0d050604330519020c030a140409090b0109050c 65
    0x440003218403c0010f001a20498075040420010784404684a401d0b19202d40107105401a501404000c1c074000d610407a0f0080594641201d440d00403500107001d9030f002d5441520141c802401214000b50200f51011803a40e9400300c0002220406020002d01105491310003607c2c29050305514104800c0e4040390085004001c1d6040c13420000d0703510f000c40300301140e20b90080c0300d003c101203040d80100340e0020100c00c2606402010300d604103010300b084400495040c006074191113811104490300ca1030142c0560700c118032401c00a0040c0007401c0da614030251440c90342c414001400d106903440c03580c040d0081138080d5000029400d0078040c4001541080d00c01003000c0d005540d8071507803904000d1010300030a81402c40000b03500148080c04100c01002e01448080c0d211060000004043c15210245a84c04a14412425840c6802920012020b0744042c6040801100c0c09983c0540c48a0114003075540070000803401121b14451680d04500411803203140c1d40c10081c00c80100c80303002c0e00c101300d604030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 500861924 1250 500860674 500860697
    0x1e01050709120c0302091807080106140d1a01120308090606030c1e0a140103140709050f0a0b0c010203010e010b0c12091816030c08100b16060f0f060501 67
    0x200300030244111a201d1401d120b9602a81c10940c1841069802c025880400c100501044544a030300e13101034803e00a007035580c42680c0c0da40c210300702c485a216901c001020340842103940d00e000c81c520b032010f038002c0c500520400c4044007100c040c408242c101580030b403d071800381c00c1850f03031144800354412041c03001400241005400241d542510f0011544600100e00005018070502c0d02c14140101c1c01901414000351540444540004c40c50400382c00603243c000081e68a0700105151030141d082511000b86040c00d040c14440020301c5d11000e00d4000c8a04000040e00241142c010401c4824200006859504004003049000c00680c03102440030400e00140303580c0c240110760404610a4800c51958a580070700115032500d40301c490001054503004100300c9411312100d00309910700d000342c3c6c0402000041e51003d80708404e003a0740d0b80c5140c0109940911031048880018100400c0c0c801a400e40ca05055440800380d0716981658010281c0364400d03c2c40502c10380c0503000c041c00c0309081c012038000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 500863174 1250 500861924 500861927
    0x40902090604240f0608070215040210050405090a1b02070807231003050a0b19030b0901020903160303090909050303070309060f0608160b090d120203090a081e010507 73
    0x4040c10740740c0702d075680340075a480c03c0591450f882480318040c000d0481c81941c0f0045901c0c80f901910036400402c105a000403081440850114100d080020001401c0d48a03a000d000c400180d9192583c18820b081001090076900c960301c3d140b0400303c002c00424030081812452244407c480142d100b503502402d000d0000740030108181081d20021450032512b80290001701140140200b2100d801c82c00029610b07000d10b60540086201c0e01560b0000c2c044a0312020601207a580300a4616540c200d10040500008840e0b030840354003c07041c000054205203d00000134149071401c08500c0d040420314108004254009202c0030083c25215810000541d998440769182d201c0181004109965003524200300092035000440841d251482007041c203481d02d4506070740b210401d14002a10350030708000644400c40328204d4580000140c14000c0200c0343ea40c40009400c000325410065000c01d11840c41c890300c540342035400804051b80203040d4984203007980d4503000d881d0a000382c02c990400d8104000345 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 500864424 1250 500863174 500863189
    0x2040b040e06071d0d12020c0f0a09020c120c0708060f0f06090601020a120e030601090903020c190302040f1407110601060f020703050f01050402121f0221010806090705040902 77
    0x114081c00c01c0d40298031300c01d00c000c00ea0020607002c194025071511490303090200340c4844049251541c0c0894046103150300820400500b241c540302e501021040b424001c005454000d05224081e0038112005150408111034050f00b103040c041141303034400501044145020040e02d40c1145002c2030341512414144013203008842c00400c414054900d500120f03045910130000d81d180340b50458145102008104001020f407039400b0f9600748a440340d0400440c440a0707610810141e5589500100780c04c0a0800038813040b201b00c004800402c40c0494030000c050b81307031400340440b084400d00000558000511701c0d071100200141c581010270151b152070920b140e000181c468103640950915001d8036254840491a00384250002801e901031813002032180001500142c0c015442110303a450404048540e40d40d45181c0b00e1100c1c400041040c0854001003210380c0108401d541c440c0710b024040c0d03c208001100f104017a070003445103521080400510b00810b110220182070210b405101030402900000c100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 500865674 1250 500864424 500864431
    0x90c0f040e0601050705060a0c0306060e060d2d0c080117150c090303040806010e0c21060117070807031b080103110a031b240507060e030d0f05010302040b040e06 71
    0x400c00c1e140102e003440e80903005558000b81d000007200c146282c40c1d003110020305549440704010074244400071507445d02600d84040c00fa540940030906141c04406018041c1080d0101c10395560501c1d4454503c140c02141401c20650058a0100745800e8410009004c0e810580c00090300400014030b102003500081841c01100e1040503111070180c40300016100148609141203505200c0010002106400403422074100c4010301550b900e2941d41013a1201c081c424440a1011039000e201c0c035400da840032904241c0c02c1034062401c0c08091110300128003005505880190100f01c4400400003c59858043d441031000795103a001356440d0810009031000e030301030000621082071b1034010020380d2030f0058a0340055810251000c8a009200100e804080e00c0e03004922500f003072001010b90070780d11501c44095000450b540d0a140070000c0d01c03000020440e540c00346e4102e000402542d8030200d414029031101c02400300d8000381951443c81080103d814903600790b0b00175410145003075070409011a181c1d50 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 500866924 1250 500865674 500865689
    0xc170c090f06090607150f1116050a060905060a2906070204141311030a1101050c070e0a020a1106041a09011b050702090703200a03060510050702090c0f04 68
    0x1511001002924a0103698602c0c1e8214801050401c02e0009402e001b91402560300d10410070342e90f00e84950416940d10702c0382d003010320b80c0820000614890400117841e9141c00340045c1c0c1d42c450801d0f80c88a09881203010140c6595004d00c09001071042e0a1140107911603495145640340450080c007803420500c40440c5030b109541c0030030840291b48480d082000350f030001e44503100aa103424085002e8102c500c6a0945a9220841308103201c2d0800098108010341c004032080914080c0740c1c011038140d40140a007000d1405416000210040e2400071240548001e40015881b4613200100614030342c0320206900c500e43c801c000388408512203500038030148200c28030b981d00603921144064050412081c0290304186107a529030351160b407000c0502019032007190104005d84030000120b064900000145000c034154142e0380311000e501c4c0c00100030445240c20045099035807a80050038484000c3e514401040001441900710314100c400a984256401d240d5070500c8200c00d90060b840c00b03a40217480 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 500868174 1250 500866924 500866939
    0x13240e190b16051b03071b0b0d020903010b0a080c030c191502190318090e0615010207080111040509010b180d03110a0c0e0a0c021c110d030c170c09 65
    0x103021841502180e100014402d1403440f185400c0c12025a40e81c0700365815100203c00d4106600201481844042223480548050382480746550307070a0000d43c068240c195040d0740c2d640d401403007901c8030700b4500300421004018100c00c2d202c1d80281401d1200900905208913aa8010030035540b20700381001c0c09070b0703019150301c0c01d64921107035080c3c0c0351000c031541d44864900c40b010080d04040d8403100700e034030210b200d030501000c0310344d20402e180903100040d1040e02c8941015000691680c0760540951070380c90140304a400c0c003a607a1700c11908442511108000400000030140058204114030300d0042ca0503604052400301c04c01d003071142901000d00c281d4420010300380b04205244c0308061110f070004061040e100d50803641d242c005103501d454801c0d05e580c8050000060214070541c070400c40c5411150b000341c420b1036034103101e82d9051401403d025061003a60707000341540b003d040114101504803030720300040300c504491020300340c1c08540c084daa80084544040102110500c1c0c260307008044180ca000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 500869424 1250 500868174 500868211
    0xf0d0b040b04081b010b010e0103110711041b0806100c0c03150908030a0902041b0906050903010f061d0105030a0f02120f010c120605090601050313240e190b 69
    0x40340c2c188a089003080708131540c0e404151481c0c02c10341c41900580c8003601c1d603481c1960040c00640a5564100a1140803082803004001081c03101540441001009000041b000f03202c151514484003945401c0b000184000c007007102d18100b01c0c4290404c078a250411b1a407905040e502d1207a040790a00004283c6036468003101e41107465078000100e4264000c00803134607890203903018001050742400030ba100300d062440d110100300800800d04200c1c0704a070349160f045420309100740c48941c0b0640c2c8442d015035940c840001c403080c1c1481140040c1010600d088103083e141c451080300442c040e00520300c40e4000500e010001a0000c400d8a512541a221a0000807101c0d030503a041c0303203c00000c1074036942014683c8403620391014a8041c4d0b4000d4071410003029440303d050150300c0a08580240c00303d9410008240860103c402c40042284100d0480447e4010400e503140c81658040218228585407807030b02ea00d491003406580a0828404208544003840b0b440f012002c0002070080310f080364004809 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 500870674 1250 500869424 500869433
    0x11202031915140402091308040b070f0209010e071728021605030406021204080618030d110904050109051902130e0906040614090705090601030204230f0d0b040b04 72
    0x400124001d0000e04200860b4410420140c43c1c0044800300c0c03060042034001414903010401c5030700400d4001c07072502d0602e8100b0180c905ca59101000a8139101045401d50005039240c0c200300b406001c4400d03040007079040100740a00319130210325028034011400001c1044074802c90304101d402030741c40240100b00b410f0508031400207220306071080c550483d51540e07003028008000024070131191142c0c00c640038011b05607038540c0c050280f40141c3c1c01e40d40103000031519052068528890710010501030701d24040000e000c02c0e00300d80c1d10400507c0e0ba046c1c0411000c14a02c0c0c00e01c5501e0047c20031050601440c0b4120400855880114603a011842c2d40450111601945a451400603080e0214114158180560819694003089404640f1035041c24500507500004118681c02010810014404241010704000700c0740001004641010343c20305c000180c580c014110643c0341794480c8000f095411710716040c030106450b030f40d1a0b1405032151003c02c2c00000c0b1107906d0703942e10680244900d00c0f2074403103242 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 500871924 1250 500870674 500870693
    0x809031c0507030e2a0d170a052818060c0f05100c0c0c080706120e010f1b11011512060207080f1908010e0a02030907080f0102120112020319 62
    0x840c00144034800045102d00301c0103000d03c0c1031004013a8489105d8102d00304024a29080b942c0041c100707a0000240daa0398070080c80039151044050a145080141c418401017010003046030f1022020f646501d81d480558011a410310b5a24803481000381a509062010304603140c0a00b00401c112a00b040441c00d02009206040c961080fa03c400c1c009550044001400c00130310030701c25a410300f0f04070030001e81e1040018080081311000d46402818142c0450600001c041c3c1c6220f0302d00c20354032000c10000c0c03413203580f1940e000e685106800400903000028002c1c0f0081c540701e80c0305050307898038010b150584811000c60046541504134158042c00318a8a000a4050404020000e810208509d5031340c0c0550005441502070442001d500079010300f00031034104a0a10405052103840400b0941c0c84580b500115400030140046913000d0390ba5a0300e00d868205441c40e00c00d0565404102c070340f640d0886210450042c0159907500d0540751071500081d440c1c1301082070350441e40415030b07511010400041d8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 500873174 1250 500871924 500871941
    0x100f0e070c03032904050604050402030c120c03010912020f012a0c0506040605010312080f07050304061b030203010801110c0c0123131505070b06010f050f0301150809031c050703 78
    0x20801c040130b02d20702100c845800b18400c2058450b504110000b80141071903c02e041c420354000700104981c03000b440503c0f201440f0301c40b2424a902039001c09042684090107010440303841041c40c0d1060b03403041d000c0241002001010a80164140083c0800c100940740390303c85003009210300760281d0b0b0560300d0180c4a0090101009005010754002c01040c820780d60320a9040302d00400380450040101c1e10111030005040759a410640b00740e82c0429407051080c00075680c0b0921a4000080280901112080c043d0501c4c5012000a40000050200103400e008140103040c0480315582040c1c5806034041e01d40c220320500343d041040d02c120346100d0711b05486040400d040003540003aa42d00c016900864081914001c0c901e80c12040148403590900c5002101c42030b50300419030400c642c440000441d003141105903140c04201c0244801408160305c00001c500800100b010b4071020036510700064086800140351321345e190020311038450721600d094a0492a06000d640000d800e60b52108154011304146 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 500874424 1250 500873174 500873201
    0x9131506080603011e200f03150f09240307030308040f032c0f0a05060306040c2309090906040f03030b01030f0e030a0305180309061c0c08100f0e070c0303 68
    0x17a041083c002403183e004101c100c0780940002000380e19005009030a02c1281c440c20b0404804000042d1a0303500016050503000e4001c2c0017500c402e800c6000507c0940c020345140148a0080400254554a2090b146200c1000380c0142200c1440c50318081d040c00c40050019202003001400c0000301889102c6096050b101c40e034018600d2142b82500e01c2041104607040d03400b540c45421915524541403000b1011200018203aa103035550310424000030b410701403402c00502c4003141200c02c0c40c82c0070351042c000c4000c00204a40c0ca44408004124604501038504c0c3c1990f00640b003444003150781c2a9020b4040c07905400c0c04500041d56034012402005c0d141c0300d0000652410031340d04640f5401000800712912595010301058403000810800540c42d1849120590f008011000300c905001018100cd00342c0c07810401c400580c0c003008841a90a00315400f000a0701002c2081326040c8800e40c1d44000d0300d2400d9242c1c0703036a41840c0304071201200c054010303018000d00c891a501058402d401807403100005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 500875674 1250 500874424 500874461
    0x209060c071206060e0f0a020703022d011d190309051503090606040b0a0603090c03170406080106030902300723030c060f1b0a05030913150608060301 66
    0xb19002c000426548a40860300d85080c42000100ca00881460301d000300d942444030011601d406200100a5000e04001c4044d030080031004a8000700e41d0a00010425140c0850122012582011400c403004082140d801040480d03003240002800200d40000e220702e094080e040d903289080549058100340d02040e4071450003c40080402a400f02031b60003002700c10112902c0c0e4451400300002c2c3c40c8416141500b203d03824500f0000c043c402d8000c002468040c400b594030203600c0e511411860112100058510180042c0030006141c2c00131580c0c0c0100307514981040781d01440d40c002002c18000741002c1d54444004001010183c0c8401442d40c03e071704511084980d40398ad1210121881584061001100020043c9610b418203010a40d00078070b42c4000e14036498031414002044050304105450f00d9051511066a000d5081c104540381000340608029a00c401230341781000070f94059400302d49200d07400c041c00e0003024000d510014080e6039180c04c02c0e20f521394074200880e0050000340e1030f07000c10340b40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 500876924 1250 500875674 500875679
    0x3070e07020a15090521090405040501060602160b16030302040b0a020714150d1505060d06080705010e0907030902031002070b1501090f120303020d0609050703060e060307090209060c07 81
    0x1c001a507042e45912842c50109030300120541074003140c03003507203015002d43c1045102044002412500140701e00400762403030b00700b10f000790129049903021242299103a66800c400d01802d90100301c0d66202d00d051a110324210303400e0034840011401094441c200e198400f85001c130415009405030340180c210114000c5e21642140300081d540c40080c8100403505100018401036410015040480c0c050070682c2c19144c110640d04a6000b415480900c14071192030840c04502d50359414000d241c1c44c1118079010600d641014505405c0c03c505a025174180301503116903042684442c04e2903980306919050003c1c08108500110741014090410b24444510000b44d010030092240e580318060740011080001d280a110015262841c0500401800c030280e0241004000c440003c2d03920301741e200e80307009820041640c11007416104260001c01c101c86c0c0311420017032a181e16215a000404205200380520f04090012170303200e041c0c600170143c0c42600000c404003551101021140019800021500d6066 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 500878174 1250 500876924 500876927
    0xd090807060507050a021e0115030c0f0b040f06180b0d0e0f0303060303032a0d05010915060509010309030504031703010602150127090b0a061508040503071103070e07 73
    0x340048011201d6074946400b15121920070402d0b10b02043d0603800500341104918480e148202ca00f003101c0001d0364035803104440c0000040c8c2130000070b41c4500903902160781005251000303031015402c446010079060000300001c4040f555a10100d174000d08008203441004150003000501a4100e001000d400282c102c40c4109184d200d030b0b041d00e00010030360b00c81048000352240c90703200949480e030340340d442071010900d00e0040d95920446140a4900040c13101401820102103800c9100c404820030742c1c030001081418418004c000001c0d81d004006050b40e820f158010300103000e404d0049042650b00c00c1c035502018055001c4034003441c1c118090b0412184075a80403540e640c000d0040100600580c041c4c00c551004003055141a1802c11011108541c1c90012508441401e41a0440e54545411210020620025415000701041c140c04900c0c02d04140b065070001c0c00002001d010000a0020031010400100564042c627a0003150ad444800000300001c3c5480115000a240324006005002c40207 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 500879424 1250 500878174 500878177
    0x30303020a180303200303040b0109020a0527041407080a0c12110309070605040803070204091a04120806010f0918060e01140a0f1508070210090807050708061303050c030d0908 77
    0x2105c003400354000300b524948459180e0006031130051250610318010b1125042c030b034025001c501d0162a0280c2407c546052034041080115420030111606c1b8121440342d00701070207038641c000e0300c00400b401c00c0d0400240c002e10707141008040c64902c660340c85011108034400c03203040440c080e8044060207418500300c01c1080550040d0f44000c072074418150700207522401002520100c0d2034260145041016580a1001070201e10b0011105468410b0304000da00c01c01b044054040c1d8003804086e10030020403403000d8003180002c3c01081c1403010490b40041d036164010911019220703c40440c04041100d115004003610b000e401c52804500d000001048044400c901034001030021603480c1426543c643c0440d00e5030300c281c0903840184030030340e88000035540107030243c5801804070702c101c92208040700e00660132601300140c00c0f100300c4000180700c011704c0b2040100744040c02e03103040503000034100341d0300600282c1031020004017800b40103d801002c421017807081e142c0312a02c144042c0071448180c50207040c00e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 500880674 1250 500879424 500879447
    0x1603050610150c031d060408030703090b0c070611070e04030206100605041203081902160201020c092206020f0d0606030f0b0108010513020c0a0605041a060a030303020a180303 77
    0x1010380c9500190503800400c0c2c80001c010203444a204031021503c0440b01201c0202c5245180010f008007080c0c15101c41d0003d0004001c0c250166885149a14004203440301650041e90b075a401480301d02e410b0300e404100c1c4411611f040c02c20441003060380c0b03202803c040315503000070302e05110342081009068000c81c055201e0405210402c62710f03a10b842058a540c013a0340609224405d00d0b200401c0080d01940d88141c0120b003464001794076182841c808000c0e640710802c200d000c050902066011940c040005900f000d8003155110350619120010b0031700000c4a01002480c180f8170514030060000c0340c0c5c11600c3c4080011020b07562052001010300251065110701e10011749030000b4840041603501c1103d510100594400d400c6034a8002084040402c545c00a0a02582003140400b000706c2000303d0510148207010114541c541400c083c6510b00217502c06d511042e04000801ca06c558032070608009030f030b038036013030041e2507a0484030111041110301030130001c000e604d0800401410b82213582c5108 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 500881924 1250 500880674 500880691
    0x1d0f031b0601060f030f090c030302010e07140d060921081e041a0a0b0901080115050a03080f070807050105090709110901021218181e01050303190216030506 69
    0x14101582029607200e03000d02c64580090012903854518038030076000004c1e0340110010116848401d0f0f15140c80c1c40c2580d0740200c0250390b640800500141040c00b400b4002c104442074400542180b0b0041468080340d2034004103901d036075020b00010841e00c0718515904984010001c00c2091400601904495040c0d902d0302c24031500881071203513030480e803400030301c240c0d40903010f03e10400e00e07800103140e804000f0b410040120748a07291040b140e220006041e00030f1103104004a803a210900c8990866060398100350302450300a18140b011074140da007211241300f1070202095a98896050030b90440c0030348a0010195420441440302c03079040040d1900c15212801010001c0b00f210b007101c0120b030f00c030700d000d51401b5030015428039035000c22840140600c0e18400c03603000407070070048002540911030401d11024801d01c0409102d2030b603010f0301c3c03c0d0850440c0f2224000c103035410980001e907240280708440280000545070715001c948240000c000d21400144601e081541381d00d001512400100c07072029 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 500883174 1250 500881924 500881957
    0x114010b030106080115020a02010c0212150109050106020d0f08061504030812060316050f0a080d08091908030604020903070e0703020c0f07030c0b0c191208060411030105041d0f03 79
    0xb030840d066551a441d1003d681c00424040c0760300d9005440140705490160781c45110803c46844081d0143b2014016100a602456440d81004400b1301150b4040e0011011903104040380240280c0083c144242810381b130401d180c040c3d840300c001800c4a00202c410855808012a0010401011002404544001108a0150ba0b951a00345540d0740030146005031507404a0104000340d0502040c12100c451000d80101c0d201a141c02d21145030010800f13002d0005010301c1d0801c048040c080c13106191084104820070610107258596800c0342c0409000d862150741c0c00604401c0b6540c00300a034900801e4007880498262400d00b4015000f900520240c010f2401001044000c4101c040360000035203910602007907825007414007030511900701800c0c120252160314240020001803400c0800010b110708604102c3c0c0c940d20030002d00c4500c002d04014000c07410440d0302d45c41c443e41141500c0c10344400341c07000200d2075905e860400983e656020000124041c0c03941c00c1c2500d07171300800202400017009110b01d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 500884424 1250 500883174 500883179
    0x1d0a200406121103070c15020705061024050901030e0d081b0906030a0504151e0c0e0906040e030d05130204060b041505181305010305010b0d0f0f02030114010b0301060801 75
    0x56a8400c194a0f09242c020400100a640103c03c0d0310103080c094500340007616030101100080340d0100e4420344881e40420100200e20f001c000c1c001d07005d04410034140135050080d0100c99401401c010031074046c4003001c02d550322945d1107035000481c28000d00381100c01c5100c0006024003800001d40302c4a20030844030700c1000c0200196000c40c1d24594010742030515542e90700d600c410040c540a001103403000d14111411800f110180221032581c4003465440e50a81505000241100c001191103811b2141341b000010f02c9940b100c0c4283c1c1d004000352000304514545004450461084210140c0350300c0c17920045c0a80c1c202e03280c400c054054425a810400541c036844440c80780c3c0a40d21592025500d4508140d801d5441400a403241c2c140002c0c1518a440c41c0c0310019519409846600c0e115a40e038400400601c2024028018a08801d47d801600c1d60340a884901e6070b030142e142c0c060042c3c00301b40c21440c1192425800040707081455040745116503102e42800d030941c2d20a1040b640043c1c1c011001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 500885674 1250 500884424 500884457
    0x130f1a06011d0306010905061f080105180708070806061b0c040c050f160203031603030b040f050903040e090c030118060b04140609190f06030611041d0a200406 70
    0x20b031a69a01c003c000344113a030710307200c1614040c100003042540c00201d07440e5511400c05d405000350260800c140ca0720309282d070400040c0301180c0b0340c152a212020440783c05000320b2035000300e1116044005464078000e02d82c0d480002c1119131048040b0f1040e6401c48107181556800040f44400a200080f00c040c02800d0002504482500a43d0005030040c00200f0481c4450400310398038006641c17024040d00e047c20b10514800b0b21109421200b580840e4440c8051507407071600d40b0904d901a0f0500108101c0350034180c0030150340e805103000c4e4602c10f60070750010032500c1000b007083d80f05543e4000c009001d04009200140d0010142c60411902581400c1e5270308258074040c040c00441801c124101003881d900c400c1000340c58030001d842281d40301c40e007a010899030f180c54050680180700050300410719519501c0c3c82800ca500c240c41650864800380010710070781524803c2031a200d8000203841445131a0b40d04140c008001c44c655510440410000c0320210004402c041c000316240b640742c00c105c11000c40300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 500886924 1250 500885674 500885717
    0x1090203061305030a0c0c05060715050901090503091003060e15090115082212181a03040b04140708011401050102010509100c051303060b0405090a0b130f1a0601 71
    0x2000307a0021701c41100c0e0390b4400c004090034540a048528000c0fa40c03a00482d00a60040300c09544544144114102002d00c1d40507841d0003031508402040340c4001d42d10b400b600c030b0140c05449441810303040254508a4400c1c2c00c008041e002841051045040804580050781003d81c0600e005032049000002c8a80c10780c40d4005955001d911076050305c3d500c2d07105480030307010082001440b21130308074a204042403140009140a4540e80c468907000c80302c01c2e1003a04004107981c452400c0e1101e034443c516040c0421020380c2e4020764080701240c425180c41c40d00c0d82c000082061010a1449001000108a0015001004500d0b0394420701e800c140d0300c8400490076100c04139030080d00e583c8241031201d0f2420b403940c404950030301246461400c0440c3d480d85130740c038071a85500988405407a10b280ca1900e01e4144504e075080307100240105000041595400f00c0c03001c00400c0e00c6100684090b006003841319140e401c0e450a42c2c032061214048042d200820710b20801075501e00c0c0040d4201400343c60900c50a41d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 500888174 1250 500886924 500886961
    0x102011107030905010503100b0a0206010305070f0302061c0b0d051006090501030b130c0810200301060c0b0411040e030a020c220209042703020607030506150912030c0109020306 78
    0x5032040f40c40e9050000550303071680003030310070180c00e90300700c3c00003554514a5000d0718406a427540a00381a5141d070500c1841c1003000d800416543d140c141d001c00042c0da8000894174109032100c454011001c0d15008480100880320398213800460b17032074000080100100380c0c4041a24102801c02401c0d850360170140460300240070080c00c43c54140d010030800d0f00f50445c882d0810b4802d40401c90b15a8807002038501344070704920401c01c40c9858003a100c080e007085c855612440d01307030b0350840c038290741c94650b004003000d0ad2100007030030144044003c541400108400450700728005801800340f400d00340c92a994030340c4003500d16070050280014800d100d1601020b02d01c450000b010507401015000c5031850300175809078802c5680941d9861076200428510420f4004060001102c0d91841e0858113001c0c0c10701900400302020185440c0030404c3c95a6129414001d00c20780c800055100e0200d01e0100300ea0601030b5990359007512010404183c5040e0540156442510940550300d007a01c86941a070180003411 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 500889424 1250 500888174 500888177
    0x192607060f120603020a060908061b03190e0a030504141f0e0406030b0f160302030403050a050307050d09050609010c05070b130510060602010f0606020c0108040b0601141206010201110703 82
    0x11020302101c1e4032401d4030b1071a0a15114001480c1540c81e40082c280d01100d9014401084c00340794104203014003807010580c000b480e0928000901c3c0086400c103114030004001120094000c0c44000718601c05900030303680c00c0087c20440d01184501c0c00c0c080e03c660480d10403120071000c40c54041500e820941d402c0c0f80c40790fa845070b44682e408500c80c0b082e01c0c0101c07820308264100c1d560b41000004035071a032040d02d000b40660350158026040041000404014520380c200a0500400900000a0b0701c8000c40300d01804906d42981c69480b10181242c0343d00c29a41d15500e21418003e500c3c0610401180003030191500100030001c0c0f00b407458060701e440c064200050441440180060404010023140500c8a413044041d00c0303440c02d00c00b00f880d040351a160850b0f00140e41d60340049951822501c5072002805244c00140b45052005c000205411320043c801000c55440704c0118649134014510700085000254015449041640c0147c00c88030003101c81c140151300344a130f20080424a08225205660035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 500890674 1250 500889424 500889437
    0xc080a17090a17030c0a0b06010e0904080706020322031707030b0a0b031008120c16080a03030e0f030f130e10150c0c06020d0801050118090b19260706 66
    0x4240c0e0401d0ba4003c1c107103452a032030000300900034108078103020402115201354080c1d1400c0c1045000100b04850180d0a00d001d0a4124180800704413550207490b4800d034015000340c6d07030f50380c1c0c0d140e40e41e28402140441d29180031221182c80405400c82d200c8854103c20b09122a2195101c440440950301880c03904e90b00403900030010320444928000440d84400440f035520641503a03000030302c2c6000c2c00d80c3d5045164580204800300d101d1070a00c0b407101c200c04a070115002c42400c03c259640c42d0760302d07200003c0030306a0ba071108203001d01d003e1201c200d2180c40f503810f8030344546602d6000349041d4000d051101110603030000c0441d101c003070070082d1401040c0140300050760074101880d0120540b443c5004c14203003d00002c9020000f030420444001401c42e603405025000040000a418100e06030401c50501400380c598000c80196010580112020320002003508d4082a005c224580040000f4283d9100b01010101e089401c415a115914018413400d041c11141e880f0034540398201405020002400d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 500891924 1250 500890674 500890679
    0x10f1104140f03070308040f0501030204031e030c0b070c05150408070308090a0611041701052e05040e0706110f030301030b042301060612020702030d0c0f0c080a17090a 74
    0x300c030303100030300480050100c42c080d02d1140002860480a40c3c811120300c03d0004061123101d4405090700010202800c00790304050542d5120010404ac1000d140b64480a0368040c0082c180704585500d1001e0300010b80410604141d20300a00c44001c1220665031842840708031240032802615840c8a17039000303d400383c2071413103e035012200c180c00175111600b240314900380301001c1005c500c45c0400c6000740006c426501c07840c0400c40a03d1440c2070002110591403c1c040104040742403c0c45e07051020003d0043c09800440104800607140607044960070624242d200c03441008002501c101750f461648494460940300580c1d0390b542c44c2030110214042e0014001000050040403110360414860310a00c0344007100100725841e581d4040141661981d128101000420341000061524010640065141c0810741d00401d548240c001c00310810400c0d09408a014010b68150048005074851303814042242d440c80b04580c0c645901c13000b074800ba0b036030036040034004485000300d0f008081c2c0035025180310352 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 500893174 1250 500891924 500891939
    0x70302060304051606030b0f1012150314010603110a0303020a080d061206060f0609030b0c0c010908030103060b0f04050702060f09250905180318010201090c030302030c010f1104 78
    0x10000351040f60140728000300103066190141040c2e01034030b034030354001446001d8007081140e010408040d8034060001022000c1d1020350100c550301c0c000b03428240100f070042c030303d1217003540d04261580058500c0c140b9003456100346506401c881d04030303400b80c0010040b082d1038070100000d0300f442d403200502580c06596160700184801010b48a50381d10340b0800183c0c103544660321034000071500000c40f001d80c0c0d580c5041c02a05404c2220401030f00c05481c02405c070740c0c20b66507240e004000250140b0800f0300c001c150107020031000d400c10424603500c6405140c0340e503980c3c81c4c41e4000e400c00441441c42480c10480100c41d40c00c003485550711551555006103201d84071748030381506005020380161028014400075000c051401291041d0f0f101e405507802c600245405007402c102c41c0042c3c04a04102000700144030510000000c0d602d1030383d48400ca24401d04200070040c0d00601c4582001030040148803000030a25070003002034000c02c028071000b0b1000300c48400d045421512500051490000c09000612000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 500894424 1250 500893174 500893177
    0x3051e0a0b0907051903020306062502210105150901060e1203040b130f050f010f0504180b011805100c03020a0503040f030302070918020103181a06012007030206 71
    0x210301400126035180a0200d5a05142210100e003c81c50018030458604405162a5080e1200b8035045056042443c00145a0310070f10000c200b081845880b00d103420f284410306c0c11280340c1e00411402d0402482110b02a03445001544541c02e0b502c1c000004404201ca00f40d80300c8c0f820802450440c082c2e0925070265082d20b902d14016401c00c280c22540c00300d00320200010000b8010b04190349032500c01109100100027180c0c0c20441038108001c030108039544615001054103003007420640d0780181d06d240200c0d09401294000140f1035080c102c640c1040050740c2c4108040d07402a642c4802c502c0003d0340700c2100d402d8500c14103403c81806040c040380c5074454030314071484c0c51080c410f580850300d29031582450b40e0050340107424000b03682c0c1c01c1081055010003081d401480d6208003032090141d04015012103025512011341819180c00300c0240708140703520100072280d0b120292812284001140030841a0704a07800360100f0f48605820308500d9561020f60420040b400081c0b074254210b03828071440b07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 500895674 1250 500894424 500894431
    0x2060706090b0403030b12030f041a190801051c0c09020c03090306152706150c10090209090a02060d02130305120c0d0e1e060c010f050603060703051e 66
    0x5003580c80c80c180740014036100c1d1150007070313001e83d402082c2500c11108005203c28001e05007409070740f04028141d2107440c024180d0741100e0812641505008490090340e00c1c034824444442d65000c0111a04d00b01650080402810380c0c0c800e403141d00301041010712a01c5003110041d005414500720042c2000f44503c0e54008041484800c010390741032000000101345006020b541182007000c20300006c1d10786090612083e04000b8074260040c0002c1d1000c0c0c6d41210000c0050b040e0380c060424811800ea007e0283c01c225002c4004810031921070a10b00300c070000043c42ea6030b1080388100d5800000c01c1212200145028000c0d40040003503181100c000d02880096019140031040007080000000c0405c4040c07061061481800110713603a0b0f00340d0140c3d45401c3c01040c80c042000d0200014803891507032106482603030f0000a11512a10354201ea000103100c500980c030328000c841d03007491070714204d807030054001500941042c1c0c12600c1c151030392441036040c0c500450f9a15100c0390106240072121050300c607820303007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 500896924 1250 500895674 500895683
    0x5070209060a0906090615050708030a090f1514091c1803081204030f02150606030711010c0309050c1206070810030f03050304020907030c080117010e070807060f0302040e04020607 79
    0x40b26580d1808003050b030752158803000c940756407200304120480000a51400d0400340740b07080c07450048941d03988601e601015026040ca543e0307613280034040011705105601041e41000143d00743e10402452030000e00b4011204900e07000c031550100709204c10006441411084980f1b1074428400031100c12141808060700640300818800e100001141c5480700601c08203905d420361401c0b030b25043c04c0141200d03800308005021540050b001019005540741a15040716084420303a0740c03500c5040c002ca0b0200021915501c1c03c0d440e0425015180341c25900c007500007171003038054980d0711014008120780754140700741a04030358016030001030740c003441024215070213a100c8a6604466840751501741220348104412804240004140425850540c5025921800ca0f1a003444080c480080081ca82c05e010300c1400411400c2ea180e03125506001e421500300d48800004480703050303a072941019500d81c2c1e581310b000e0200d0f80c07081d03980120511a00848050701c0b9940000c41e401e4407180d003845825403101800f42c9 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 500898174 1250 500896924 500896939
    0x2c01140409020d060209030d050301031a0403020c03010f06051008010f0e07050f041404050a230702030702041401060801080d05090f060f070f0210051215030f0a060603050c0d030507020906 83
    0x2006a43e1a0821000c081c010341d070050701c42d008441450f1401450780500c80500005000420000761414100700d24440616002c2d03110380c50300c1c03a09a00c0e0000501106526500b01411051540510b910001c102c4908841c540c424410200040e10500000c0c050120074401e581014454501e4960b6159044481482c140c0d00c2c140f454842c100d040e030429082083c041e000034050800501d418003c25402c42c0d00d91404000c0404c18070000245810582021888a041d03540010a140e009101b0b441c504c50f0050420301c680400004030021260b000d0041c6000f050004001141d6000300084008002c91103032103a9290000000401540d080008070140c2d000c43c00300300351148040d40001528285100f901d400800901c1c0740304102889070010382d440c00b00803003881420707003222907000420303040a0701003981894844580003081c1000c1e91440c5200b441d22a480b84c2d0320810809500000c1103a004a00f550040c02c0a08100719001c10070840103400a035051000c03401510340400c1c1603400c03900c02030050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 500899280 1106 500898174 500898191
    0x90f06050f010f180303030506040c05070203190f060c0c021e0a180e010914070f03030503162a170f030112030c020411042c011404 58
    0x2810011030a01c020340c114020300c00102c1d0b02035500d40310130f051031300d0b402c007e0042c20040d10504d010383e02c1c1c603c0203510380c1d2250702034600c1d465005002c0d1406000b81c40504000c01005503040e200b80c034500034600b00081c05413107030001245150b03c40f046070442d1401001000108031519600762011204003c20550311190910700351000c80e8880749980f0101c1a0810050030600c00c156125071034075114005105188420780e207070714203410854900c240c03580d1401140c80b02503c402004141d050022906082007418210014241880c1c014406a01c040c0751100da42003082045103620300c001218024410300000c079040b80e0740c1c6500884d2a024100d4100c071440d210510500e80d07000c4e4941e6410080506c030f01c1012101c6ca030020000e2102640300d001449180d8413520401081d0001c07111400c2c990392a01003e10b001181112010010f0303032809030b0780615448410401a4025a11040b2 = true := by decide +kernel

theorem cover : BRFrame.Cov 500719424 500899280 := by
  have h0 := BRFrame.cov_init 500719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 500719424 ≤ n) (h2 : n < 500899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
