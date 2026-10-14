-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1661
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:06:31.554031+00:00
-- url     : https://prove2.me/submissions/b99620e3-997b-4608-aab8-ddb98beb8e62

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 298561151 ≤ n < 298741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 298562401 1250 298561151 298561187
    0x10e13050a02010f02100f0b010f1106130c05060d090203010f090305040e15090c0406080705040302010e09040203030c0f010b0f09100311010504051002010e0d080c0901030f0f05041b0501 82
    0x1d4290350064658050400001045d0b001d860b102d917000181d0703407160845000440202281c00300802001405501007916201d003000740c4060035900f5040c1c001030561700007112709030100c011000c41c209182140d886d80c000580c04080000d035400035000d42d0700090030103030003100200030041000308070108aa11910004001c80c0052004010181d40e000c0110b03403102e5204e14410142e050000081c0c04400c040355410080d00000c00c00388405a800034089a01074864104146030a0540d0000b0301200391001c0414401c4040740c0001c2d085440030300503184503074110400c6602c04011301e24100e010742840f4644a00800343e2009110b403174685404032a001e2203000200c2102d0a043d03403640c41000c40c0c4445042c2c140101004005200c1e00d5640004a00d140c00d68000181101011550740c20289051030b001d0401414031300b40310a5840e00001c0f6803224000b420009103044004480401800e00c5c00c050300703a030514100402080c0061804500102d4800c24a90810340e07464400560b141190500003600b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 298563651 1250 298562401 298562413
    0x10509060d0b040809040603120908070608040f030c171c0b06030c070507120b090c030a15020903121305011b0b0103020d030e04090602090301060b0705190f0803070503010e1305 78
    0x40b4114a441c02d41003400f901d112480d0030b4945022900746c5040e94421200240200c0c007469059a000c01e840028110307000c06060380914084009103100c0000c2d00142014404101c42000c16004004000e80140d00189482295072080990200c2c0e4000b1040c901f6449600909400c1001d1284180074001c04010842c50460f107580740a4031054001120480d51403091500c0820b10001459004800031710801a000301441c01607081c41c2081502e0f843c5900940c0044c1c405000a041d00c1064881039500d601c0050711009401c000031700d42400320782d45d07903d081d0001501c4911101c044c042d1506441d020b803500888459001c240701500c100b11040541400f00000050006203071062031949038074000d103800b0038130346110b02c0007400715074000c5812501c041d40025844130f64142030052500405c0c4800105051051980301d8540f80e1040b04504160003400d964094100b00d40300d02c0d81d82c605e030b0b00829100d440c0c1c506200042d145610a0090000f0040d42da030029003050416040d107424580d00c03c0190030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 298564901 1250 298563651 298563653
    0x51201020c10270209011712070b040c0618060f090f0902090a0602061b03060f0907020a02120a03080103080d0608030f04180b10030c0219030905120607140703050d05130308010509060d 81
    0x800c3c1781144e00d401c400e134040e903002032342102044009001001e00404041c0390508140c0b904143c9000198014024000c01c20342c155550000001400c080303848070b08154500000c1c003030040f11a42c011303030403000311900c40381c4010610b0035240e40a0804150103441104529865800c10303680c1e041c00302c0380c211148020f13000d0b042c80d0b600684003558100e180138049024012000b40001c20001c011559400140d0005218109601d8551380240714500c5180140101901c035440c01052107805000113400342100150115140c046580b002c8000c16680381900d80300e41454104a0311548503100ba524543c0c07c44080302d101070440e01c614901039400502c11007458402100581c09826003190040a50096564108820f100000300c058010310030f594603001c00e0305103010844542845510100d0980c03017a802c019101c0c1d0060690415842c40290103525a030907880c04503040c1c071030031401c03941c5241400f0502540801d9804d050000d1407017601d540c1c0715a85c0b68000d2010414044170b0807a402013030740d14503030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 298566151 1250 298564901 298564919
    0x301030f020d0f03050d06060302090d03201504030206010510050910090e09010c022413050712030815011409010509130501030c23010801051201020c1027020901 71
    0x42030340e00c040c1c416a11440765403646044004440400c2d004520001034181d00f40d541c0384199400392025003004c604000c60300780403510300d40a00e1001003c4c0030011304006c0da00207a646806c01440742c104115040c4114a00014550b0b03602500c04078090310914001084038602900c4404013010f044d0383e0241801081810031400b200c0042c421424042d080001241c03400810b105c15110313036019000070900c0d55030100003d14003918403a811000f0200c2c0140580e454881c09206a04000d01146440c24038a940c1070032410015941c1c40f48100460401c20b000816410990b011303c150410040a0408011180150380301c10b20b0041d41649204100444403456000e000a00100b410240103500301d044d6161002c021114203810a84500070f01943c10802d000d8441d96854565454003a1601c03149a120006410100103018181c440d0400e06d091001c1642e007581a520310481c0c1c5070498003110118040c2400400c0d0360020200001880b00440d010540b020304500f4500c0d6002e0100b1206a1810f2001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 298567401 1250 298566151 298566173
    0xc1c0c060504140d0e1c0804120302032b0605180408130314060901050c0c060a0b0f090f010303080109020c060a020f070b010e01061b030e040903020f010c0c060f02030c030103 77
    0x100c0d0811600714051111001c100040d54038105070f034544080120b2074200b00160200c6504200c04080301c2d600c103060014000034240d41c00c481e034003000b041c19801c190ad810fa0071070003250b1f80380d10000000c1c0c1e1801580b03007203150021a0412019010403415031544148010715540112140c14a102d0501080020742070400401c00d00d01d10700700d1061626100e50381e1058a030a00480c1c1c4850754003c00500040141c00c0c400c1582007650002c0c264600306901e9121901ca800050290503855a0b480d1201c12940340e81c0103080c040301c4000e00b0070001c0d14104801d0110070304280801e0b00000d00c4a0008903c2141034800c0b546194044e00040c91203656070b10902001c0d50001c0460000d07910140075482c0041c500c488454043d01c0403030b60090795981400300060005d010500c0500c0e000315a0404140401c0c0c000810441c00746007501d01051500c050f041c1170f4a894a2000000050743c6071000e06040c155001c00d2502007603110b20000d006490040500509900066545c41d0b90104100010400a2614469 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 298568651 1250 298567401 298567403
    0x1f0507021003140a020d050a180201200304080703110108071d0102011e0c030501050102030c03160c050307060210050c0918100b0310030302010b04020309061801090c06052206020d0e0609090108030c1c0c060504 92
    0xa01c001500cd10490450b0485d41c040c4809034060740d03050042000940f5401c10550080c07802c0720040c508424028054020a041e41c80d40c3e459510400d0a41e074030039007201400048100c54101c40d01101c2440e280140178210521000a00d00000441d46610110407504180d500000130360405807180d080704c242110b1481d08a503030401c040c2d00080d50303032814806180104001d8014007041201d480d09007090341e4006282e420405810030143c0807542e140c2001e0340c110a00c081c185081035039030510a203216070040e0021804181701108008880032040d000c0b0090768480d50080c0008480c0f64148816400706903a0700841c0d82010000580d00e01e000c80d010710f802d884820010841c040c0584401c03250b241a81c0064001910010b040d0041c00c00030304800e036001980310285101545801c0c4000d459a103011048810420080d00c440e0380d5555841c140d460040c80209041c20b256501c0c1c240702e54a90042241c0c081602a00d5102d00b61201c44d00501080007070795496025a0520941d140c00050100401c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 298569901 1250 298568651 298568687
    0x106141507061107051615030507030b0a0e0a060b1612121a010f050a080f0a0f0f020d060b0a0f0c062304021f0507021003140a020d050a180201 63
    0xc0001c0c045540d0b4007408030411030300c4030f455a641c8903a0410f50709100b05601c000b483d5018110042003480c074201080c080c410194600081d064480100860260611050240c0d208401003000f14504201c0004280180c80b9003a007004060f0342c079030040001d03002d01003641a0400c604c0005d540840e03408041400b03060424500403070540c020202c0401260111443e00c00358101c2c65072850170303d50b007260600289880320b003461420490000c0006207040c0d0001e20300c418590402020927000e18054110340c47c0c49000a1060050a0190044c0ca000750030a07626010200d0074484000380d02c9060608440302d8191039590259540502c20041e141d668084c10212803856451b0984650320812000001d015a04401c028a840c2040e0040208100c141d007940040c04140c0c4c0c0c0398040b1160040216821145c3c1618208010760040c5000c0c1d00800640e0320246e080007803039040140300683e030703030080402520000f4104a10f80398085660107c883d1640f10300c0345c1040410041001d58012480c0710b4070306000f00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 298571151 1250 298569901 298569907
    0x1406030603161706010b090f040b010203090303041e091b030507121103040201020f16030b180f07080f06040f08070507090c031d011119110d09061101061415 69
    0x100b044514100301e98440c0b00c40310803070342525549600521015006010001d45241008214000240141c980407501c82c86a03548507180c040e2a402881600d407181c00c003c00b0340c0c0d00c580c0e590010241f060400329058000b680342314030100d60360301c1e5807160f035110900e086400300381140c005030281c0043c04040c1c01c2e5400d01c00300011b02000f8a41500a0b54078032030245040d01d445c2c0c2000e10000e407406c5009540d61095030490380da00000c02480e1442e00b422643c208a100550361903040416454940e034258003241400f8a46003405190780001d6110101c0d8100303002c40c5c0070346c6800c120071a1035601c242d800510800e011503100e00801c1101020b0311001d400341040d9507880360f41c4c8000380d089801080004007ca911890400c407142480d170841449a200c0d0f81c004e025924290b2440c4400303110782402e07482c0c0d250b800f0502c103c50350310600d001c0404031202c00848024050005024000f02524402d9100188440e1402c040d1003806008940441d184104079194a244200030828401c00310808403098801c01c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 298572401 1250 298571151 298571173
    0x806161101021e0a0f09030b06010e040b03150906070f020c120319030c030f06030209130804030f0510050705090102101d031204050f060c0304030521041202060106091406030603 78
    0x941c0d0324100c84040706501130307039041d1004004c0c09000d40755107203c05000c0311b90300810110b003011131021340c001002d06c0c201c2003804482e0000340050514144041e014429a07412600b0565003000c0140115581012a600ba03680c04804a842c0500030750b0f050016080240d003400c1c5410501a0101c0103402c540941e410640c0111240d101da440b40c90410700065107684200f074545805122f21840a001c40348144015401e50300854081140901300c0366803d03c03810304903010b011808068802850744168070210529290601c52780c2e4013403001c0d1541d061341ca08004501c056004400300d4a0142d0f042e0090622a40f500c84e845000780450b01514a0701075900c00b407140712140600081212030118000228603084c81d0034200c1c80c00050200b5150640d001070144034011100e5402d40b903000341d05141069070340940c40c4c6079142c40341d03616402d0885500c40500f4442001260710030440e4091041c1d003100c1c031580e87c60101b00c9180710304ac4a0284111041c6c042e628007030801d4002540d1000010741142c02d02248 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 298573651 1250 298572401 298572427
    0xc1b060d0f1d070b09100507080a0c050d0801030506061203040b0d061d060d29041217400f11032121090d02010501080616110102 57
    0x40c401c11110315a03500e450581d01c802501500d00d4240007454002c140c1c642c1040f0300003810340301d8440c070300c0e100e00700031900e81070100d208000300d84000d42c2c0440780d2502c4003138158002d440c0010a01e130482d02802074903680c0b82864441e01d07119040302e802000520083e00c0d10001d200b0040000000c24405020030000400d51641c20700080584000103200084c07480d02c0c001d4080742036008600c2e0010455050001d101040d9206240540c00681100c0b44503560085040f0340480b00005c02e4040040306200000c00c0140a81e090030350111030130a07140d81c0100404080d1100c84190100d41e076080d4203503141e061080c0180c43e24059181d552a6205150800c03c51041c207140090244008550003d00441003000300700c012046101142010340040170010403100a070441041c2d90104445c0c1c0c0000442da030740c0c01103440d03c40e00e82d00050040c0414040d003001100a51580d100e46c503040d02540c00d01c07000180304a0009141449000204800d14010307143c464200c4500340040c031180d075150b4090011011a00e2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 298574901 1250 298573651 298573661
    0x130206070302100c1106061e01050a0201140c0d0b03060412030207020102030702090903090a1d0105010e1c080d060501020a050a0201030c1106070503010e09063106020403080903120c1b060d 83
    0x1194882d0707452040640703811403800000804480c0075600014108014290230b1102885e42c1000342482c541b00d150703a140880c010018030488684681c08a41403181038013900f0001c1903648602203040c006041e00d07009045c0d0f652030a0b14000d1440d220000040551842940603000300c510500c185d910f0406640c0000d804d145090b038040c200c039040040e45014a01d00045120018803450484c224018030301070040020310014421b09042c054803078003d9990b50b0350f802c03006c9203500c2e0945040d20f10000c1e0b401e08111540244903041d100d18a484004200c1e5030000880204035980400103000c0f21801390700450180035810740c54030500000019450000b00700303000191140505036903080d225854a0010018002c000d0025412a042402401150017544510001d100b40c03502c010782a8207072030030403d50000d21544000c0c0105201180100400c44110024007100c18100c003203c4a41014941c255594817444c3e481010683c024140d1001842d60401c55283c4407030010209402d045244007404280d075 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 298576151 1250 298574901 298574921
    0x6021b1c06060f05033d06180614030106030206030411040e03030903030a1a01121505040f1505040203011d090118150c081911040f1203031413020607030210 69
    0x3c04040050141d41010420310307a1240c1280c042c240f103031002040f203072030300c00e820340200c2650f1092000c010940c0400d80c0082c4c000782114450ba079100390400e1403030b10052409000b148141d00c3e64440d01c00e40c5260500605043d690000c103107030710355126030ba1182c05040100311a2504192101d60651410406001440c424503511005e0f541c0e9143c010315500c08c42c1e8018103000e2100d9214400c3c00d00e10399200c1e203090808681440c0c000b811412414414217403002950006600508000d00d6182e0454250007550001d10400703030f40c40075a600d420801c0180d0100f40a41cbe240f96401444180c500d009001e10b0b02c1e044512040001141242c10022888000150354241e41a0030114444400e1208501c41c81c407541d6907504d00b4000608010004503050001d040301034550b1a22041015861041002103a000386030350104501c629070381d4490107a8072102403034243c001c00e03e4408094900403800c400c407489010401e1405c06055a1070f42000916081a00300754118420f00c11026164065440707828549 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 298577401 1250 298576151 298576169
    0xc170406090c0b0a12110a030e15010f03051b01020a0f0f020301020a0e18010b0306240c0105010e070804081219051f051c0b041703070905010906021b1c0606 69
    0x5142d215802170042d15000c00d4a41d0001d14107000000c0300307900107003541d8916005180200d01c403520045454a8031040704142c52400404130000941c007181000e00408603032184058030324143d05416100718003a01f40402030f001d42c000c4800f54000400100d5448405440741c1044214046960040307422a080500a4070105150302c4031004030345041280100500c000e144980410b606000310352040c1d00004e02078500844a15500b6600860041ca02a881f01310340d04071070b0307204d441c1d2210580c0a01000c1c485c60b19a00d00c4030010900e01c51280703084031320031600540900d00d821880c03000140503100c010103000c108080c035840e40e9a105003e00549001d01e00d0720110b43d0360f08040301c5100e040000c4650241b80b18441c2c590142000b5901003e0f40d01400740c11191910259603103040c02200010001200000f07050000100520705130824403804c140c030400c1c0c0c0c40c3c881c0039440b042c003a6035a142e5040030443c20140b0003903142061410641e441c01c0102c001d5032031030752103801d41d980d50265100c2e90800b50003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 298578651 1250 298577401 298577407
    0x301060804031101050405250b030c0a082a0703030b040e0109060e0d1409011b0c06090f0302061207090503030403155001060206040302060a0c170406090c0b 69
    0x10b056100340c00075a1555050003c003c41d00f000d0361495902d1810690342030b50140040e01c85219220300c840e20b03030000d00440d09416900e1511500c8884c1e81c0d44101108404100c090011403140d00c00728100c020075a071b5515580d043c80600d01c2d5a65490781000004604054991071609940e88850059408030355080d000440c0882e0319103091400c0d5041111044a030f81d016034402035407542d000941421b51804407061960713800180004a9294450202c1e1019400311203c1100400050801c1c1d00111409a5281c00130141c641007040c4446205100c00303540b0040901803a000c800200c17400c103410141303030305003684455038400110307045030441c2d40156110080c07811000e28541c064000e48100f00e074030180782002204204403a8082e0281003080001c81c00054901403402c0c4126a200079031200a0b104040300ea41c0e4070080259503501c115804ca00500940300800c407000451b000e43d480d00300c2b031a281c400d000c1850a4159007540b01c02001a01c41d40d40b18941203000c10024800807018091200e032081e9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 298579901 1250 298578651 298578653
    0x80304050a032a15030e0f030f21010e040b090c130c030914010603140127050721030e0f010e12030d090803090d093204151814011202150301060804 65
    0x800c83e5441e002c6c1c684150000d00001000038000300403662004940301d0a20b4403030138804c030700d61302c40480c84a000f01140c0140001044815004006a00c198460782c1602038542d144203480d500c0b00e44508031144c00c50721500d141404206690040d8403c2a524600010b0004c9035854a51b48040800c1e028425a503642c0d409205014003138162000d03c0c14048024001128088540318560080010300e51929168680c49020000c1c18000040201144543c083c1400e440400f04003900f45028000c0300400d000301d00006031410007500c0081518416110280000552003e00c481400c4140701c11400d404100282c0c044c1c0321842c400d00480c2c500a003810f0b501d03072405000c5603240c0554020f07018140308100c4030403c00c4640380c00c1d021041001c182401c070b2001c042107c2260100400700761860388903003003c20f46d080301d400d950403000c2114901c450620145100c0e00035101111030700340b14128840c00b980010b01c0742100f10280254964400341c5607080f0f03484110131000a0382c1081e0020b5001840440501c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 298581151 1250 298579901 298579907
    0x80f03180d152c0a0203030405151201060306060905030c0f090a02121003020a052e03020702060a080a0b01030e1504021815090a0c1d1c0b060a080304050a032a15 71
    0x150200544800804c454a11600080d136680113500c80c0c988581c01103e085449500034400341e94140302d41203009030f019619880050094001405107400088203804006118507000a20030300000e0042c00d41c03514909000b0501000b0b45c40200004140c41c0c08100212144920280d098032901d40d501d1400c681c18118410445107400d00d900062060041c503005803170b140ba100d064542e00340400402491385c2d229042c0150302900a01c68042c0d40100c004c02c11403115034000f00820700c1011400401c2140700c0d8208e005400300d030811700340b01d0042da0054200d03080744240c10b0f085542250000349101740c943d48101280d846220211480c030300703002140c010310201d03042c088069074101c0c000e12070601c40f1540031b19005000b2180361031384092401c03d14200864503150049480084040c0444095040c1160305091850001c1554054000c0140c0030300020081c1000c4160360640307900400c003d01171413540d00e406052104190b4942d4104501003000301c85c25a485030403c00902c40c020000700d45201480c000307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 298582401 1250 298581151 298581221
    0x1101230403020307090b0310020703030b0d030c140303070c0f0c050d0f0b01061b2405010b1e0a0f0c11030604060b03010b0a150c0807050313080f03180d15 68
    0x1045d21141458000c1000f40e41c041104482242d4900005882e00c103141800c401500d0000c80094000d04109a800d0a1562000b4400752103400313030702800c080300d030321411071580d030b00c411500500014a43d92042c1c5c0044c0c071488102c14142c3c01100c03051902529000050b0685803014001c64003040c07410b164600700480010f15a00620f8582401c0e83d04900015058500c28803260004103041030401d01705141503d1800c0c0300383d8040d0740010030840313582c5880704100301e0341c0f140c11180c0c103158800e103034043c07038455040860b07460402c95521684144401c540035500c0750b08000b0100c500c0100030720b02c2000da8a00300403440c842c40c040d01000c204203980906160031613181051490103840c00000c180150000b62030803c4220300d1a242044040f030b0603007040e81c15070262a00041c914040050300f9603900300b05a03400c0d0261840a004e5601c05c080059020f5640e00c24801c82004080b0400c0c08003105140c0b4043d21a08207008000108400304a40001411540c030b50004004c0320807502d400c00701000d19a080 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 298583651 1250 298582401 298582409
    0x190206070906050304080d09150608160f2912040204060e131101110f07030210050a140711060a020114060a08150402040204050d0c0e0c040b071101230403020307 71
    0x40078a641c0d041100007881032100401c00b070070700600021403040d5103032654428905d00c0d0300000c14440f0300b0484004580600401c0c45910706501c20f9000803950240885c44031411140078000e481c600303d25246450351070845104000710710a901c1c0340c0d6140140045402000102d1050745800c2c1540707011320401040b1045900007140800e50380e4100300002141e49070942860384c0144c03030b41103175060000040340d0041441d131104070140a8004c2950544000080040030f49208844262091003081d0741150075001d010302090024840d00a8140000e070034000400e680c07801205481544918500400d0300c0d544884440b00041c0e558113421307107180320080705064200034128bd41030701140c50248500d03541c0e541000c2c60000101d10340d02103000c55540b54100d0b002003e0182c114800d12041e4280b41310a10a248a03002450320f503200024034011504085800742d40140d84521300b0308903d51204642c10102406040c10720480c9881d10700040780d5045100c1052000b407400c2d5603502c1c110720505007000c0070313684 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 298584901 1250 298583651 298583657
    0x3060f0b0708220f03111003091a060f040c020f010c1e030f020712052101121212050c0705010b040506181e0103060b041526100219020607 61
    0x105081c0054650703401c81d00090b4604030344000c3e0011200064402c0c1c0415032054400c4003840c6000403c00000c0300074076440000c00c44518500b401e0315602138040c0c07589100018898504e8040e10720300038070700040d00c83c2c0102000d030105000a8206001c01e08542c0038000802c09a0b009480c0d04503000403d00030368203040f25614110160441402d00c00400000010004040c152a202840c25440565043d19005072f004045004464003448014100d90b0000c20307203440b0340d0540100007036448484100241210b0300c5154640040000f42c0702c41100090b0800d1b2441007001140c88403c0f21031050092902950320505c5003980c84c0024680303203003121603c0d5040e5001c1c0c5d041404100650361303141e840d15203400040d05001010741c0c5809a0000c101c402010110800c42d0039000481030050030350151402000c1514200254005a4a18107511420b8451031842c0a484031955135400980c000d4680e01c10888411030b800500d4050101050b40c0080c01403d01c0f19950304440d150455040100e60b4010509003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 298586151 1250 298584901 298584907
    0x140114041404020c1006030203061503060117030702180118090c060503060d0507030b06040f0510090f1d0d0906180303140c0d0e041b08060f010e06070303060f0b 71
    0x510800440c05184121880030010003489001902e482c3c049a0007101c16805850b116000e00c0044001822076000a034068800c0a0000360700554603c2400f14500c001001024560320703110f00c5019005420b00c0c098290301081c0000c0005841d800a40f12400001c045521030960600d003812840c5010302034018034403400c180111000c03a40c2c01078210141e800c0b51130555600e656090100b0804524541d0050107403003081000002d00260750aa90302039142210705101010348080d12806841065521000c601c80840c0b01f000100c890717034000d4074500c480910200d4022002a44000fa1120a0210300e1158104041101c6801d90244068014007902d04101c070040410034040018030345140001424030005c41c4003400050061416600c0c3c004c40d6a080f14421052503400900145401d4103860085041c20000d140002002002c40340c030242580e5802440d60310103041000c0e003808441c100d818080802030110054841400074100030b8000d46001ca243c500d0704046513008000741d402042d41e40014 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 298587401 1250 298586151 298586177
    0x60105030f03090a140307030f061a0409110f01090f030804180603050613060603210e01030c0c030e150f12060d02060409022107020a050f0304030c05100521011401 72
    0x418410040e9810380882d0805c40c480800032a1070501560030141800c0302845006081109035080568a185018864080c564030705040c00203503056900001c05040000ca40704000741440814001c1030300051401c0408940d1b10b05101c540210030750401c0d203404d100082c090021180c89041e0010b28916030604120075031641c1c031820b84915000d02005c0c8a802182806010301a10750080f50185411409107001a000c0428560003801a00d40b6800070480a116100700c642c024881c80490710925101c1811803106076404580d102c140070007460b407144504040b4048183d444002d4a0140041d80302c20b0b94a880c516800140c0800041ca003910600c0078a4032980140c0744c0c0c80c02c2d41c088034048200540c40307030040c04c0e09143e81c0e940c00c1100424000400c0400114550006403840310601610a8604490190b90a20746922440c003002c1c0000e4054282084281486040c1d000042510f2030118103002c0c1d0049092041111050300c800b1582c0f8207001802051007968020212080900b003d04a103401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 298588651 1250 298587401 298587409
    0xf030b0402060f0d020a0c051009080a051c09050102070312090f08030402040b180109110c0307030f11030409061d0f0c0a0201110705011401060c080412021809060105030f0309 77
    0x2000300000c0c000d8001181000c1d0300c1c2800c40c2519508507440800303640360142400c005210f91031000c001c0d299842105599a801c50162141403d455000700c07070b0624080c00b414050b100369101205400e2140b2a6030603410001455206012140e84564000f50f924402c6080003850405081c2c008124145414035990018280f07c48549041d64803a01d15034499581d800020010098804103540145518110a42d018459400d072410780d52040e0003001141301a024942131406503070711181d940c0c1d10800124000c0b9024601c8554007203103600d8130300140108003641d14250341260703012110f01034540809110040e0f40010000d00000d050480b00c1d0b4600c0c0c40c1c84011640007002d0310140719a540040c011042920039003000046c00312403220303196240d5841c54914000d00ca4400b240c1000b0000f070340007084c09841010b4500d066034003c0c6510742003034206041c80c44040c41d8400300700d9020071040800f50401d00c110701694810b51401020305000c0d85840309050030046c21400b019401e401c00c006141c040d0307035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 298589901 1250 298588651 298588673
    0x509030f040510090305151f0f05150c1b030d050901050706050a0b03030a0e03060901050609040b1005041e05090c21010b280e01051f020c0a0603090b010f03 69
    0xb400c03903c100f100040700100b91549650398202030164014a0110030504031340d1411540900c58080e01e111307071201001d0002001d10424020705d0314513180307545c0070465071404445003011520001001c9252855180c0c5103032a01c8994040c3d48520400c5881c07005007440c2c1482407080d040c0e05814900d00c2d00e000800001e007580700d4510003c004075940d070081021f651041c0d114500010010f03044030340e0380104000103402c550f25126024400c0c0720351000901010018058a4041c9001070001302003900c032541e8242001c0300040c40685020f40364100042c141c3c0e6540522034100c9040500300c400c480105840c40280c0d0001172034074105a10a46900034070351101544020310100d5640000c01c0710840007906070240207580005a0700003030302440c04486c20440700301142991442489401e0a6070703501340c4042000400d01c94580c2c803c40f075100440700900c1e04002c8074400509441900d5092215a00241040c0d9494020400007503481c1c1d4100c08002300214624058070440088400841ca980e8030000e07211 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 298591151 1250 298589901 298589909
    0xa170601030501030c051c06060810051305030301180b0d0305090915030c060906070b2e18021815030a14010b4303030b0609010c060c1106010e09010509030f04 70
    0x407038202c4003a42c9800021f015800c3c8030360005060003043d40d94070403c1e541b0350400740324594440c5040041002c41c60040b880185013a4004040c605682c600400266101240b0304e42e050841d44500c0781c1010b41d40c52850304486035100381c0f070700341d00c8200032030912400340801002d22500c900100070b001c089030342c001454a0700c0001201c240b0795440580340450024002ea03200107000a03036a07000e1040340c04c16107060f502400601c030030115001020100f40c040b1030a69109024600e1101744001388100394940040c44140380d400105040660202c1c00710b01c9200e07841c2c85441c107011000c4288031042d0410301400350038003c554841c505950406d44141c006105040406807440d901c03846030b0340440f01c000d600c03001d0100550644180f026824401e0031000c081c400c012130010f494511022942e241000c03c1c1c414101d8180d4889014903102e03981c09005002c4001e041c0c00b4080391581e200c40020341040030740c1c041c10441d280f1848031f003080d040c01425188090407403181c81c1c20620888448007203d109880440b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 298592401 1250 298591151 298591159
    0x150c1e0c3318140706080c0d0905100509060117031207020705030a05010b130603030c020d1e050109050106173c0d1d031f0b060a170601030501030c05 66
    0xa91101d0100e240034000300c0405001c0c82c100480c001c4030300c4420840c60905802440b408595100320103010b0349403032140c060200441c0c610804036000750034050141041c0b80000900242c800500c1e1111807802c0d51004460206940712000c1146400090100f5401000c4801c04080403100500007240c41f0f009070410254029062000199007610800c20390005000203000c0d204840b0231810000c4c040d003650a525030007255021041410704440e80700e204103c0b501940c851148040315400c00691001b001410b80301440d070417020100000c4007001c04001c180c4a14000241c0c1000e41c1381032821f403050740c3d01c20390b07480300c540c2c0032651040804655503d0540000201c420000045822080c1d94140344000c149012440010304056600c000391111a6104503101d80c604501c010700c2001001031071150450300b5400201c0000340343c40c11240740b07509000c80c02c58007051141c01071b40440c41c41c0d0801071000000034445810506007c0307081e400550407a20030710301070011398110f8a0307010707407032444d0712801d401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 298593651 1250 298592401 298592453
    0x51503010e03160c27060803040e060d141b0f0616020d060908040303051c05060a17011404060501050a0911030f0705090307030602090f0f1507150c1e0c 67
    0x410135943c1440c805000d10300100c1c1440b9950b0b0700741500c080c40102d0101300183c51300b00c01050014002046e2422102c00f039480c40d1311540c4100a10408020bc40004c40c9c1a804008640203400401d0165200d914803e01c00b11001d416200e042200804d0410035050281c0340c100a0103880c950f101d03404503015501900e40128030189480c1c26802004a55005070001c04d01050100c20141c3c04001001101b02a40104074100781d03401b0010300301d03481614140e40c05180040100f01c0310700303421201a518541c240001406d00340c8000e059240c080203c0702116044c0c0e8800040c003540c5007202014000d407420003001c00040c10308d440b04903414840a0015007034070800d0307000500c07407611030805c4035401d0718040d00781e03071026590740303085000b9400c0a145a4864a08085084880c5c02d001080889034074008207034050224034a1000d680035032200000755849035000500b480000358601540c2000e15850303032294440030320400313000c09080014210790100001c040c40130b4040f481d8200070b2002000c10500c0c03510 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 298594901 1250 298593651 298593653
    0x905030a06110f072001030e0c04051f140108010b0301030b010b07020d05030a021018080f0d061203020c010e040504020303030703050c0904060609030510050403020d110a08040306051503010e0316 86
    0x7240c01824103c542580c0c0000341a001c000c6040194000c10301405000301442024000660a0b01c0c1708440d80501544484207100c03051500e074000396000081c4404034404040c08145100210940380c102030010403030104003c030702e0750340b14145600500703042001c0341c19941540d85045444006114518904102087e00010365070f6406012484a0f84902100da032402c582c00081d448204c2c0b001420b9032185000441107001d0445024014900e038001540c510b40b10801d42c4424150b0403080426000503502e400104400d0b440360745007035009000f130f00149241081076000428603061001860f000e10300780030501c00181c400105503504686141004150b41c0e40303005030b0031402d006120080d64000e00b0502d0016405400000e0441038070b0141c0113a484a401c12061402a1041540c00a0040e4002201103a5040c0320305032031301d0201007075416101e0900040e110001d40f5040794000303980c810b90310428020343d00100c0b09911030070001030f4000c4c4101d49101c89034544900999410000001b40c00074854 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 298596151 1250 298594901 298594931
    0x1a090f01120f060b090403030506121f0e0a08040807290a08060d060609090308131a04030e0a09020406020c01020c030705010e0a03141f06120305210f10060905030a06 73
    0x701440c800500582903500c0c0c5405d0040180c902558030a0050020400bc01c1d40da000100300648209601c003131203ca01c07040d0542030301c02007020101c3e004490181007082c40000e800440200014514100100201824102e00384107142c0c0d6080b880142c1d142d41c0c2d89035843d80001c602928500b00302428001242d41d15040410540111110003d01aa1500101081008035a485050080e009698110312a074814911407038405280341c3c09014910721242c81e58400f1100d0b20701c0d0342c0c86882858440d0b840e405210101c0c40c0b4030b070700d41c02c521a5603402080521410780d04002c00c40c00034a0900c0101400301400b40480d40b0f8648500031141044607502c000f81003074442420480055038000034000c40721078041c048603141d144000110100d12842000119103d50074003600007994014064500484403a40d41034801d54062120848800759010010078001d58a035030461141000c007209005601e030408050300c11000301d8100038140101d074802404a51400950100d4082d030004000603054030140d145 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 298597401 1250 298596151 298596161
    0x1305010e10060614030c0d0e030c0f07060305060102060f16031806050703050c1201091d06130201140424020309130603030905040507050a0810091a090f01120f06 71
    0x244860384101a0000701420382a0300c0384003195516a1184103075030500144c10024401500c045d04d1158042c441c0075151007031640026814201074003100c0c03070980200040d60a02031100e00c0b5501e81d0300403000030481160107024166001e0024030150201c0d03c1c01400501c05a940545459000c407889800740c01c20900031780c0058260b002c003a1144013890483d140040180c0000ca603092b00080c1000b021851580f240301c1501c9040da03013801801d850760308000d00301c00240903000039245c006000b507080d00c14502051210b58050a04855089031140080c00003506061003002c00030700f001e004200401428501203204441c05090320681c001c816100e00d400c034a14014181050361201c101000e1015800503944090f00305c178440e844400d809551081080200d03141101c444000c80d07020003101195074031615055501256101b881d500050300c2d510b00c2c0c001c407890074400c0390707982109156030b0302c56160211100d9404101c1d81e200161660502802075148031040c1c1004045080192841080088036006 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 298598651 1250 298597401 298597421
    0x60f0901061a03090f0606330d0e0606060a050403141c170c19081308040b070209091612030309060f02030a0c0e010206011e0e010602060f100e130501 66
    0x40c40e414000c01400c0c41a03600543c3d11403010701c20541d41d0301000300041b404c42e10400c00240550192200900c0390403007240d00481007480c0504d84c0f01124582114000605189a02c0e2900011113a41d81240c80b4904203005d0001d40c4103007403d01200401b42d5015040303034103881e0302520f40742802540901c600d00e01910348605262000b4440040200c00342c1c0511030400b00010000200810b4444c0c8418129a200e4000c203400d2422012035150507540c040c8c05040e405c1510f402e9203412083c00c1d5104c41d05139030819040340c560f0b1507001620009500d440707548203401c040c20402902d280060300101d0340140c0610b01c43c000c401e600d0060a0401c1c10300a600002046401400901c030b4403c8001d00c003c006e60088032030310b501c0c3d0f01d044040140b641c840c81d4038440c3c14030b042c1c000f003816909280106103803110828065840040f154004140c45a00d500703500d00914454004246904100401c0061004020701c070b911200041c4008104c0c024003413210740e4000710615113401104905052035405080f05400b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 298599901 1250 298598651 298598669
    0x40305010207060b180402010207031716120e010504050a090b120607081e072a02040e030406032004031707050114060102010e030405060702040e070518090c0d0302060f090106 77
    0x40c40d009000e81070f005544c661a0031503840e00e0400000c5c5904c43c141c4801e44010780140d000890500014071003564610315081c90511039814003d02c0c140c0b0340760184e072420088440c0c501404808800c190084c11030034218100b424824201401d0002049461245208503201c3c251240340034921a100d0742a810302184206040d68610300e04118060284002920900d42e6050041c5620b48500b1040168501400d082d41da00500b50b510802c00740c54032561420f50b560240702e160f172210016691071003180d2040b98000c02540c0c840c3e14280000c3c0860340409400a100c007102c0509030010b0a40d90100d0301038075440b10402002c849038000801c494014030900520701e40c030384401d01c41d6905015182c46e105150981c020b00007c5a0304a4441c1c4038002d074070a4030340024050105130014a056041452880100c00444103c0b0390340704006560400c010081c50f024200b6601401904007041c410b102c9804001e03207814002e41040e03500250355610042c002c0c52446203440104030a44000c0d0000710003407048079 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 298601151 1250 298599901 298599907
    0xb27010c050c300703110105090102300d150b0403081e09060c0114061215090a0b0705220e04080c010906060b0d1416180b03192409110403050102 64
    0x8101c0e40c1e03500d41600007070301c000d040d01c106c9114641c810070071140c802d403042c1c0c0030b41400f182d00203668601c015065038000c115000411424030046400001e0020206a00408904030284680c2e1030008070080c1c100039542d41041000344007250001c03048031000e2010f40b0100b040301c2c10481100009000e120319413030707020000017007017580c150701500300d03024501c00b40c414003405441d0700c8200145400c7e0301c0c911072115004091504010306503140101d0740020300c03a007501c3d507042c40d950b94440503280c100e034020049080843e00101041d0a07403520758040070b6106c0034440c01ea0618818015540c00148000e200d641c0001d91a000d1010030340004a03c5603104074103000705038407468031172450f0304a01d42140c0e20307505d0403461120031034a000041e030042141028196181d440e5020469008001e400159103070044110005403c3c403201b8000d603c1540c4070034448800d070210f44010020355500c900540f54080203c003282020101c100072074000caa840840003d2229211050755445004039400500740754404 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 298602401 1250 298601151 298601239
    0xf03030f0f070606032a0509070f140a0f0801090c0206010e0c070b09010501051302160605060315040804090c1d0111100f020705161409100b27010c050c 67
    0x810490140720f964002d031030354601c40c1b0030000c1581086511403554048101c03401300e130009001e0ba6005042c1e11540c07034a100b140701000824504d907840100309a000903d8400e14122003944804c042c0d01400303804405215090b20705000950700c44060042c1b2684c0d03400722001c07420300c00e12801202c921b43c4d81304510510720318060384420b0007440c092003413500982108505552400d441e00c2220081d500c1038105c1e1b01035014603120400100002040d10f1780503c6001c00c4242c0440c0310083e0380c0e00c190303c030300340f86555181803018210035241e480400380c06008c19003076100c3c230500d40d00d000e6400a440078603008444600d40c0401900e003641400040c407645140c883c00d07490750274681e0010320541e40a4070458116914a0f5190101c0d0991480340185001c140c82c1c3c0480710f407924400458001000c0c07039030203800f1916210789035027030f5222401d03a40346000100d24403074000c0480c450344d07001c00308242480c40c01c443c1c803600c5060300c4182c10305445100e1001010035160869030b48228070002603004804440040341 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 298603651 1250 298602401 298602413
    0x60f0d150605030312010905062b0501110a0e0909100f150e04020a06050c030712050d06080c0a05041e0905032124030c130903030b0f03030f0f07060603 67
    0xc0d1515418280d81440004541030070004200c0b10314141c00c2074119601d0b86081e400d88000c000207400c180d8047c402e01c29641600900c20b01c81d00001032800c02101000312645001d0b82119424218034480d00d009000382400c4540102c8090178001040d108144145d0b91151840d081082c042038003121245411480c22206140343e22a5155110395010001420389039040a0013102e0200c1d0b0095000e000a501403040e14861006045000d840c40d044034200030290f42c41420401c0448440c00c0011404104420f0800590282c0001003c50074040c01145c5100740201701e1410ba00c5c0600c0e8001c5880f4078001c170402c0b03001c1c41480402481d58a0420488a0728544940c60380e10071442100344040700250f5555141c00c011005004902c00701d00050307101c0d4010440c54002056450041d814020035885d907101c0d44590b22a41800e0703490780000180441c00b450081c00320744070b0542440c09003800c0e10b8203070629240001100c0b41202010070940d101d558046000b42203200d6800000e01c100d007091400010414 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 298604901 1250 298603651 298603673
    0x1107090b0f0409230f06130308060405010315020c07080613030906090621140106030509010e0102030c16050a0f0b0115050c0a0803060f0d0f05010b01020d0207030605060f0d 76
    0xa0444810811200840401003550128180540861078501007660000303082001071204c2012002550000c890204400d07040c5902180d552208494081034042003561008180d540b11104417410032195042d51180080b0551501c0688051030b40010000c548240c2000b242000300514001c90f4160315202e58580340c256110385048010030010000456014020303001e1174291250fa644070802c1c00d503580d80c4414446040c031007680d0045e544000300f6101444440d107403406400591000f01e50f900b004000e0701d0842d42e001210700401d034070510601040010210890700140b00c0081d6000b0040030314200981440d41c001c0006164008504480080082194240341201d51006c280340e0000c8442c00141d801c0c0c4104448025540c12071221600020f07810030107545c01900182281011410100c0459100c1070150341c20340380c0c0b00310101407004002c024019400c0b03858080c4003078039500003034600181da201c0407400010301040d00c500000740f0070f440f481c80b890190342c002801a5540c09150a01203443c82d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 298606151 1250 298604901 298604921
    0xd0503191a21060103080d0b03030c0a1704090203070905030d0f14030a060b0d0506010f0f08180304050406060e150f040b090102010b0409060c1103130b0d06080717210306040c110709 80
    0x3030070110314041c20f11300071041c1c82000100c000a000c1d1481580e5404520374640010040214420b00c00455220851700c06988a1203150312100082d9042904242c0750680d0510207078204001c1c014a00c41d43c40d40512002c00c9550400440350f203e4907142e9882003d0a025002500206404954810700039581e810840c0201400c0c0c840f40403001c4200c00807254405601030003c04030345c914000c00e02034400741509240c00e00205017031780d080a880b4000101540c0580e8440b100040e401510041c00e03150002820701c0580003055094540001603249412500441c880d078800703c41d0115401d00c50382d000313402555007030200510810041c80035180035002001003401e07d00c00a000c1070400c140b1100d000048a01e0000241404818180340019502c0140d0041c0a00c01000b51141d2001441034000c124a4010f444c02541d070312140e445600307901d03103056a00300124040200f5803000002101d244000c607504040b094030003103040341103884d040d10403a8001d40c011181e0303c91404005414219a40810700007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 298607401 1250 298606151 298606177
    0x20a0b0a020703030e190e07020a0210020a02031b0f101119050c030703031407061b03050121030f0c060209220b030102030402300d0503191a2106010308 67
    0x10450017418000b116030000386404800071040414015804001e4845034000200d20449442090707550200e100c2001c0843e1000160303001c0000c55045140030310030351070001c40c98030f040d244002c11a000580056841d444140c05400c4031801c0054403031003120481d80b2103543c003003250f041c000740c18041d42c5034110f4030506032524010142050003619000c14607108481e0541e60700354106000d031000100940c03002400303c40081ea54000c042182010391340f180001d02030368500103010740c54080410b0519015103404821007440d0036054000039000020000000c64624000210410320301c1e00c00d0080c8900e2100795400481c007402070504080c8001c0420025040c60801c4c4044015001414281d003c1a6802503102c107502c1415802d0124490b00d5800c1490303001c1c48410400c01d0040c105040403422030103100010400010440501c0070b000481820030f203050320403c101d81c050188149070041004480d44200340301c0700b4041340e480501d0039801b8550700c503400303031901d950b960300d072440065022070310380c140d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 298608651 1250 298607401 298607417
    0x30c0b0c1305060c0a02040506060403020405010b07031e050a120b09040c08010e010603030804020f0a0302090c0712091203120f14040b0a1506080a021b06091218010c020a0b0a02070303 81
    0xa14107282c3d00380c54992841c1c400401c04201554200070141800810050300301c0424000080542c0d128041d990081018801407952500503080044c00d0506001c00d1004203507010002012441c1d108003101e80d0305c2d10f035190100405666909100107031800b00d112a030700c40b0543c0d00344010f0200221072042240c1b81d100c020040340c07415128840c2a03a5180c4005008510090002009410300c0c00d2002c07162880201030004d41034690f40025010300b020741d2801c6101d440450064100100707800c139142c0d079040f28107012005900d45284980210701d24503004007044481d050318000c0c841a42c1102d204806040340501250090030705084125408980595180c103841700441e10705c824500c41d84203800b402c054401803260400100703039080350001d0200300b00d03541c1c20000043d8000c00307001e40d041c840070f10001030951400c108581e5450301d81c4001404001000030072003078501e41c00300d072164100e0000c20308101800c01c405000184140301654081c10100c180040d181815580c00305802060301c0c440d40f80c000d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 298609901 1250 298608651 298608659
    0x170303061003050903040306020f0405032a010201111821010c020c0402131a0d0908040302090a141f0302060408011b0c0201020a020f06070c0312170609060607030c0b0c13 75
    0x6552066071342e120650030070003041c0003040f0690000e000001700320941d50321301a82e50000c40d240c03024070b011a0008054803075403203015490498800031030301c2d03003403000b13019400c44a104140343e40b18012010034100c20f070920700b0383c40340c54101282208210200d908145580c1d0550844e01800b00040404014005c2c241828943e117050b1003034a03100c10320b01c0f0040d502c4908102c81325581040700c400d074000b601402c0c410607000790010b00822100038490710f80241c860b45503106101054402608070540359003016a540701403006a0889076014818102d2400d140c178440c6d4110101c4441500302a4200c00002008501c80605400c8070b21891405058842402800d030b81c121084101402c00a0051700f00c41e91a2016142c040b001c1e010300c00004188a181032100d030307510841241e05a108480c0a8030807014074070425006009015901015036480d0581d252040004240340740041c00300348900c801040305010f1501c1040c00c0043c56600000390051414200100c41c3c1ca50400c015050105401c0c02c0c02007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 298611151 1250 298609901 298609907
    0x522050c0a060801180915020c0a111012020901030b130615021f051b12010f050103021309110c0304030b04022e030905010b0d060b0f040c0c03030c091703030610 71
    0x1504840c805c4010010b0388455045040140039040d07800c0c0c0d032468801c0b00c1d4500d400150b10003451022000001800a40040c1c500042001f032a0300e504d0740b1900070303001043c02240d0040700c40c002c0100b213444016a5080d8a400603002020300008090b044440d1000c50094820390b0344c450130079290b003641c001c81400c2510b0407c80c0c4e664540f0740d0050300100e801546030207900054205940080f0b01ea07a00034028000345241202541000040540c002002310042000d0110159148080c020031701c0c06515106c11072074144c107a030741140b00305160295540307020b04900c160f0000f92011804140152680d4170360741d0604030045001918241d104919423541d60800c8100280c0f601c0008420400305260340d10411000e800a01c09108213659654a6140c1d080b6079650f10750700700000902c00e40c4002140f9401c1c506000540c2e007810043c80c011480c06424408440c2c00c401080200c07545441c000c2002482d151007114200300c664454900700440d19803c00300c0030b2010025501c07401c816a0410141c2c04c52134022 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 298612401 1250 298611151 298611167
    0xe030c100204090f0b0d0803040c180c11010225021309050f0d050a0e1905100f0e0604060203070b07090509010f0603050915070c0f0b090109050f010510090522050c0a06 74
    0x3c03039001c5040c41b40ca00c00106a070002d07590090058122100306560b13540841c625602e040707585400141ea403480c064034640c0246002c00820341140085041c040c216401001d014840c40b1405004540720104000715918a40381c44448041044148500303007403803808a507900c22000d00da490a001b030030403490311030f48030764107898201103a5070381d0040903a54070003071003000c142900c4540c08404664501258940b20b5112441000c81c0554480c070010903441c1000304400420059a44038840811003001059030000690f4100b507000744c85070286d529a11402da03401c00040d400681c10441c444000142441007240b25411902e0507142800142e950202a540b54030413001508040200500841c203500e01c508410100c0900c03804085d59240a039841e0414942d0044801c5075050b0b4681401030100700c028800300c01e5040da030f074000780910708102c1145c0d20044000d00a42c3c10542e65034001810031038504141842c550403440310200d0851190510035290418888214000c818601000481521031104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 298613651 1250 298612401 298612421
    0x160c12021302030405010e0f0303060a0602070e070e0a090e070e0f090a111305010311030d090b0306090703020d1802010e030a0201020309040203070c022e050306090402040e030c100204090f 83
    0x1c41404039000d0185802504003074415100c6660b00d1407400100c80c8200718032400310b90b21000458a910f0030204100c041d030600d0300f0500031504810420808130140b101110782120284c2030110340c010070305001c202c28110326400510003030f0414240803925040850354400b52020703200048a5652a450365151900c004c0d500ca10003580418808400706108400c0212000402000300c0e10020301400d0030416210700781c1007a80e490b40700c00c213070040515003042a03503080e502d0360500109041ca081219581d031301009100b1405400880006002544294100c2e082d0010388101004018010602d1045400894400724041150402c09500b00e240004010340d105a05038001c41c6044101000e10000e0340010b0034540038403400080c80c2d03005a590400101400c80c040c491800104214040b12981502501411050101c20001c0c00116240c482d0703040d07403180d0140c501082c060b06940c070721465442062000c3c00203008000c10300300c0000c1b00c0e4008200303c40d00ca8800b845180303c140c800000310f4040c0c01e5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 298614901 1250 298613651 298613659
    0x31e171e03010b12060618040c120905030c010b01020a02101b0204020304080d0b010905100c0c0f1811030708060f031005100f0b030c0702010c060204050a090f0c0906020d140c03160c1202 82
    0xc42444a031402d41c2000340270850500d040b0b4000c60b1452242000d48001390804c4440b81c0020400d010320071002d110702d26005400b4401014050402d07008585e02d890040904010030507051101c001e010301010030500003982c04ac1c0b08560300c5c64941001410381d0000833400540509001400d08250b00c600174610a40e40000d10f44a28152085401e0720750800b0300800311128440d001c00000c01c040101d494600034088504090003103403d0100d443c007100c4145d0000c00d40002c081c018002d143e54008000c0390f120900351a100c3c1d82039140b100181c03074008014540440c2a041a040002e9141c1d285000b03011070398000c1e081c550840e21f03138141c480240022910710b2241389c420302020300958482e0484005650081c20018074003525800400e50141440d0010700c40709885009004a03c8858451194000c510f031600000382e50605500139114000309200e041000307015051b6070148241c01048984040a8008582da80c0c442440442c2d1000c0c20940155108030038418009403503180309101e89200d5034024 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 298616151 1250 298614901 298614937
    0x50f01031218050301020406020705130603170a0c0b091f1a0f060c01111b060403020d0810120b040611030705090103021602030115031e171e03010b120606 68
    0xc0c00c542c00740c5500490600030b00794100c0020161401e100920182c5016805030102074205018041090000c144c801880d030324100080000c1040c2c11140400d00380c0c03100d261350380c0e810000002c035003510041d0b0000e42864000000e1109402c400241500c0325150603e011071070084030000c40342100d01514142c007034065019075008807071810b00307882041c90358001c4c225802c0508c030840c403e013107030f2610050180e03407607001415032150900d00b1007111f820340d24000141400c0c0317484d40e002511003212410400601140001007030964001d4a0514003a00d0640080703036402d006400d000d81541d8040c0c0b81640c1c45440c01a000c2c4400c0b4508003100c0c481c0c83d09031101490202d840740110700940c000540e84102c604825198801070b41e0a0081d4500c00c40d030030140e5501142075040081c3c0d040380b0711140c80c480290719847d250000d950403a20326107051680981d113403500c40c00c0c50550480c00b03d04080340140d030300010011401c1c80c2002c0281c0504408880001010f9581c3e00502c0001c2c07090b04045144000303d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 298617401 1250 298616151 298616183
    0x6210a1401050f1c1e0c3b0c0405030d03021c0207050a03111006140f010503070c0206131d07120618050a0e0d020109031d0906060a090e19050f0103 65
    0x10410072421544111052103511580c466403104040020208448003150b441003001940c41c1e0f071010700c05081031440c40e400c06010002180c60647ca03002d20b12480d14810200040b00f2240340c0d030958006260142c02e1351305078540c40c28010001c0d481008840c0042c00131008a1600d41d803903100b5542400c0c1d000000748540303201034500340c4075003000164a048620454441421045942c00384000615403201c205040d001c45400f0070907081341c03441803241080030030300c100140141d22041c2601d086805450040c0c0c1c0c1d8410030210021500306420020800c242c103c080c4810207492003082d440ba000035a070313890356104416182000c0d41c810b1b02c0340210150100070000b04103c2c0c50782c0225003281c0a00c41c0019901d244500303041c1000410490040540d40d200c01100601d600301c2007640d0074102010f04050b8445050303001442c86240980501c1c0181004501c40c024140202d0a0078082c040d0348406141c1c900d40031a51005203003000e2103010081d410240883d50f54280c0c440b103141641e030b205c10703448192208 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 298618651 1250 298617401 298617439
    0xe060307030f050307120f020f01151a0409090b010501141e090f0a080706021203100308163008060f0907090f0e0f130c0506210a1401050f 61
    0x2100c107094600d0301017006001c0019190350118400304070709031506184800680d40103428a00c3c042c10690103070741000200380003c10104109010b0f01e02c02c03808207041051090b00300c820760003640c201c451402d1404042d40d00381b01e800070226040b18401d0313130f0387c070003c100301c0301504000d010300d07000b071501c80c000e4030821072420307902c407001d01101c00001e00b100701c0c0400d0342030008045007229408404241c2055105004070341c7d05100124800524440e820700d1824404c540c1d0242820a210103440e480f0081051098030b180c0c20700c800c01e504d070806509a4a44900c030303811000215000c4034940c010310500c20000712107001c1c0100920452004002d86900d0501400344a0141e6005140b41c0401198441c04555072042c4401403015011201c09003180d458071400ca500d07442d030060072440030340c8030f10f58503040015501d0141c4420740d941516080e460b50954010810808001568005160600b4013002140b0040d58051141101d08418140081c0d07a1281031000b050380c2034081c6504040c451460b001c0b0806 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 298619901 1250 298618651 298618673
    0x30203090f060f070c08010507050703020703020603100b0a1115010b03040209041110020f010c020c0303070f1a0903070501062705100e07020304080d08010e190b061903060e06030703 80
    0x20040d0916180001074641e0183c6079202a200f1280090100b1052041140074402c0a50003005428035a00d403004545010755120702e6480000d20900000000036881c400c92840e41c0c00410f894007081781c5401c00a4006042031103104240c282511030b515036804030444800347c1034100c0d084001e502d880c43d110b039001d000c48120004e0060b261403041070081c183c42d4031095540769030705e6103a60150038402000b108185c2921b800320446801c644c040c0912583ea03607000310448200a60200c00e0421181991034595140c0c5481c408030303250210407004200c4280403700080400c28802c40003001203640311401e24220144408105038000e403120706040b0101c0069102e00d801c03e000c0101c0340640c80d42c65a141101c480211020710040c0c101180400c03c0721002c119148195996040c01d1700325604010f1a1190517100070080c4404513250401c0b209000d0103548a0500501c0203054150380f58450301200ca50103041a000c0000a440d04400050039080100050700a10008018101c59482c6484e032540d039003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 298621151 1250 298619901 298619929
    0x1b0903010605030d091409040b0105010f030f1404030305090d050306040e0106030c0f1505070b070f0c020a23030f0309040b03120705070e06010c1211150c030f1303020309 75
    0x16581e4600490180c0c0c040100004400c40345d41d03519501c9003840b58110f5000b40c0d40b10094003891415041c40700065030481c4c00d906440702860000c80169640c04201c000d040c200e440e150300e0a2500365035003902003403004d05600c11400b0f520207101c191a024542c664440501e10f1080c0003072428004520141f400340c1000040d0840c07940042140e07600d0361109030305050150300c940030500300e0440c20000765080f0310020304503070700a04041c1d0800b140d03511542141000149200c08004040203c404841e004a8284030b01640241c0500b05030341c1c807960554106624018003804000c1c40c85c034501d40344d2a001a0010114070107201840c00c010b40c47d4144070141111503500b41e4180250380f071401c2000c11141c0075203407c50182000700f00c000e28080e0344007603412010b02407030b0400150416a10201b03800000c008802e040300c2c0303002100c440d8400d6040b410852010f402840888101c0203008800c2c0102002d18012101d035480c000d216218225480070b030000200004000da082070059109610f400ca4868140c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 298622401 1250 298621151 298621153
    0xa080414030d0501120201180807050409170d09050c0301090f060903030e03180108070302030606122205030721080a0b0402040f080109050706081302120f011506020d03051b0903 78
    0x888110142e20742540c00c241c000c03481e40e000f150780d12802d5603130100124000c4009901c80241041c1014180c90b12200c0500401d0301443c3c640780d02c072003000f000301f00c4008c4500d0b1041c0c0103500ca07068141e00001501407600d040d100303407042070380400301d0b0314040c420008090b6100c25081d003249503e54540d40a0101d40d0026410716540e18034803502c0040c14801004100065000c00010307041c81c00014100080217480a000c040c410b004101d001c0d00e0341d108130b90380b840c07882c0c0740c42030660f5aa40702c042100034501360520012420307404603010010000090901988242010882403041d00400440840e201740c1e010f00140b80b61001c64016040c9034072809003028090800351910b52260443c191825042d4404170b00c9a55490203101844001d2050101610303092409440c02d050951402400102500c4041d200f00080ca00e001064801040074049401030300c4001d000d00002d0001a88510210340315080140c0264dc031107000351403280c170139503219079410001d070228280c9010b441e80d1142c00c0f0304141505 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 298623651 1250 298622401 298622407
    0x7080714030a062c0c06030604090609021009050f090603030a0815031c031505010203091009030609080a0f030902090a0b0f0406090c0201060902040302130c090905150f03030a08041403 81
    0x10070900c0c084d604400280f0009038030904a5185508800010384402444c00e0f00301c000700d04020381e42c190459801010869022401d0034081c00c20000621110340000e41c001c041085400900d45c100000e0340441c0d40441784c07000300034541c006210310740b48201d40e105e625400070000995002d015145c083d800c5852316220a000c3d0002c000468680716441030141d1440031000160014a07a06000b042130846246c501c0b038407003514013000030703549009031001d003442880d00141c039003d40b030300c6810800002d45c1c0000c1c0c2031002407043d04048845601c0000d07598000380124480032003003030003409100d5141e60b01903d02c0d40c8603500c4585281c02060001c019540c8010000005142e540c1c840c0134040c0501070344400000c50400031a0080d08480150b400035039002d00610003080580c0d10517a90410024280a0110310030800c420201c503a800f0641180c42c40c00d1400c02842440c0b1890149406643c4003560700303204228540e07080554070700070385540c01e001071007031000500000c0c803a06e0490b80b03403009075003242c3c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 298624901 1250 298623651 298623653
    0x115030f1403070320011802040518070b340204020f070803090105010905060319080a03091203020309060105041802011d1003050415060b0a050f0d0f1d07080714030a 73
    0xc02c55115440030f80009003800700b024083c5000355900c2a820404034001c0200c907400500500d4420031341c05020303204a40d1100014000c0301031ba1096480144d0500564030000d8842e4050b6aaa42104041120044483c8190001440800714041050b42000c40c442090490b43e401c20019511941007a881031200740b03e20f10008e10090041c501030000745001003825030420001d04122640144040e00ca0b034003103008082c4c61680085900d011640000c0d000b5910090088150090141800c004000c810141d03141c55641d46e0550146010312010026501a81d0740c420400c4180d4142142001102e0700c0040b1440c010740c0104550990414101811200e801c0c030318002884041c04141c0d18800f1944030002c0008000b15190101091000c1c1402002610300780004004280542880001400400121079624041400540380c100c00d00000502c1101e050040160141c0089030610507145d08406000007100b030003080060548402600400c9500d00d800705210034400420b0030395826000d210b0b0014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 298626151 1250 298624901 298624903
    0x405060102190c0f1e4a250516021908030408060f0702010504020a06031802040e01020703030506030d0e1207030f150e0a021c0f0209070c2109360c0e01020115030f14 73
    0x80c49210b540c02c04201c0c90100000c040340c502031f410044000c1260400420f00c00050001945054640554a40c2c6840c81e0081400104000a0f003181d06144800308000420400c0050703d548a246440c078054099203402100340e00762841a0303002948041c030b08105004c010300c258080f22234600c00c0e9568425107452600030400311401a107880c42c050350006940e07014190903014040c0c0200040d402000c4456040340c000344800040c00041d84183c5940c46001200c08080080c0000b079a0170070300e200d40000c00e0b8a0448200c0105034210603019080422007082140c0100f200030405070060502e4000c1c14420b5481d41480d401c120089603401d00c9080001d025840d80c0f1601880b07005581c8624411035141e0514000403101c0910240c800ca86242d00d140c0540e9106115100f128001c00c07031005040d000c4550101c8941d404142c1d10b03800d0071340180096240540e40c0100b0200e0030780d5200e001c4280142001282030310054a05400445400271007040001c503a000760a542600a0241c03014603800741810b1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 298627401 1250 298626151 298626299
    0x309050d0827010e01090f05040216050105070810060e010206010e0606041a0c0106050d05070510050705161502031806030403210504030e0405060102190c0f1e 70
    0x5115861105510030b10650b04018915204c01003403d03e18150303850411000c0d407014071801003901860f004101c8001400b040c40780741c0c80c1258050300038000303840d1008004028010846207400201c000031750000b10b40e405014000e0380b503141130340507100c00c3e03003030040700038030302c00003500894000f60700704000141c0c07c204040185145010707100b21591480a400c045003510007907000306124000d810788110004000082c3c02c4112407040d9400400c8a5290348150340f40c1c09180300103045801a41c07981c804680c68180c21034161482c0d47d0302000e405c403510008980e28010080203560710341b03500900c80844c0c948a0301540c0d215110346441c00c01d91b4564071340d001c0e0b844011908244480d84600521003010b4100d0f203d0014a00c0c2510104520b1070a05d0000355264680d0741e5100404155413000018050403d40e040040c084449072010b80b140d0368400c04844031080c260f04a840901c091000c00e444411000d51140c0391134424291141c0c558444c0440889400544010640d0343c20020503614400c0800c10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 298628651 1250 298627401 298627447
    0x7030303050114060910080606070218090607020c1e0a05060705070e250c1b1d0a06030c0611160f14030610061412090d0f0c0309050d08 60
    0x1000c41c0651400e0b07103643d081a4080c40380d510440c0c0c00d100440940c1c40d411001074100e602442c2102543e00e131000030070700301e1140b00e0012790049079150311007050100300060035003d018504111203180d5075950081361503400240348107502c42e20700841c651070088005c294800c400c00007042040c2a40d61040000c0c455446940c04171405c1c0c0100c0c1c4204405460071103600c0c0c1c082402c1b000304044117078500514003012440140003062191245800041c448811b074800720b8002d0404040c0825a1a00c01540c459041030111340e00440c4c0410020303402040f5070045c0011030b036100c00710350301c0c950510760241c0c0e02c4240d40350320403010b00ca14020603001c424a07280e044028031541c1c64119042d8201003401490010088685003c1d40c000c506000c410160b031100c40040307a006144c011950310301412000c00a2064508004c0b00400080600442400119940d501ca554907102c0420f40e80e03001c40e00f03580c01d441d02200500420854201000f660074000c0e010300032640714142403480c1c090107221000103003400400c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 298629901 1250 298628651 298628657
    0xb03010c030b1504030b1b1605030c010c0e13020307210506100309120f0c0b010b032a0a0e0a030b10050102070603060e0402120307050706030213062a050708070303 72
    0x81042d100f41000940154501c1022a2103807401d811522584443c0d040a015440103500c0c82c0c09000b0301080c010290f42848000c1b01800301e407040507003083e540d030350800104601c4030352801800c280f40074003a03504d91b000042c010b8240a001107424002c00000c1d0002060402032155540c4003480004e00004200c085400003980010f42c0e06040d800d201c0c0f64013041d135401e011705142c400d0040100303216603900e04525105262130f44141c1c140d001d00701c0382030101e030000401c0041d01d5800810a030001e030300913612600300d80c00c04520303a0000c442a040001d51418402d40403032810058520b69a10902171900c200a025080d048107aa4030b80c4c4803255044101c507000120019604140314540c1d06202250041c816440d003070081350b00b40002520f00c44406407000384030310355000780039034a080c0510035580107035080340c15030b110156641e4005c1c0c0694000e428423001e4140714131020440d54004c078101032980900302d01090081c1c0c64040c1c410440d540c0c2c1403058410b0300c54030a0002da250300c01c02130040510300c00ea1b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 298631151 1250 298629901 298629911
    0x30a02090f2d0402150f070804080c0d020d08030718080312090d14090d0506070c0c0b1317070801020a050a02061b03070c0309080d1d0103050c0306040902040b03010c03 74
    0x410a01c00c1c0c00300142c0d82d08502d108064114400030080e8903800e403c95011501010300300c02080d1201614071401000c1010100302080754001c1c040d003940a0000c031014181078801142180040080b040161500250302080000080000c03a0f00e240142d44d00540b0740c1449905441c40400811040e102a8130050300b951000a071641c40e40704e43c0b14000c0e003008030800102900138035110080c0c0030307044140c05104024030110305140241d45505c060503e03d42c00000755505410f02c0300c0020020442d0400544510384901c80000b8250980012199010001c400d103220240c1096103100003112001c2100c3c0c0188140c09010962032020b100604801000b80c661983c9d03074200840107818020f00030411848881080c4043c0b608044400440303a00034054603207409582090300d002d50f00b01c0025000300b03d0360312403014180d9490381c00003e0400c004007181a07144c80e5459450044080d24001c0741ca0b001141010710125025003859040090200e01c0140049000852200440d085880d8040d1001c0020b44030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 298632401 1250 298631151 298631161
    0x140a0c12021905130209010201021b010e1e0303070e0102030c0111130801051302040b0105040f030b0106110607121d10051f0308090d02040b061201090f021e030402030a02090f 77
    0x2c01019010414002001d810724036002c000b840e505118080c040107280c0005052009a00c00e40c1103030540580c4040080c541d1080c500c4503402820340c21001080d920600825842c803807104080d1107607a1004000540c80c640c0c3d060011540740708a1032515040d03100c20310070701c800c2d00c100b03006000e004144070710960341b5205101c55075038103070700741d80d000c4a4280d14040c00e1040d085070340e00d10842c010340c066901091565003500100d0b960f10840d4401c2411145c1c0030b4000c802c002c99240c1d0281212001d0741c5061001980020054641002340c2e025000308210900c0028030141d43d400c0940c0396110b40461841c03e0050001043c2400790258008065981da00708004031143e1803445401440801e502210145040d86e0b50a1101d11404901702e20440301d001d86142155125003240032160310240180780c40326401c2040070841082030003003055240c2000c0d81460030341078034030a07503400c4142900300d0a101c13000740301485030b581c0c405801660980a000342c07103000758641804013402080d200500316103038642 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 298633651 1250 298632401 298632409
    0x5010e0d0f15050117070510180303020d0f032705010e03040602210901020307080310090f1e0c02030405040e1c05040e0f060105271c0201030612050703140a0c1202 72
    0x105801012a0400341512081c1005c4000361600076180e050741c0c08542d101c0301d010b003900c51210391440301c1c145041c52400802050340c0072862200c0c450b8170f51a00c2c010110010810b03070994510403280c0c422450f500000034000e0340000c0c20641c419014800016040c01045040d03030a690081c3c1024025134481107049105260066207140c1c00a8000700072404c142401e0300003501d038800d9100c00750484c0804004280d000040c000400b0040c404130f0f604000b0540402c0d030600107444080c0c1510201c6004110111282c0068020101c0c40c10b9244e000c0c61905040c903003044007d10301202071aa052043d00309545181032640608030201c1020f417101030b01c403468402c0f1000e80c004020300d29170f414059042805074a0360020306507200080c41e150400380c1a0b0a298070004510102088a0b5025407500d00e0b00c1c41c400f810b5500d10007494002c0c0d8082c480b086c1c44281c03118170b17042105401801035010507010008900260480e0540c01400e20940c1c803540c40584401c0101c0702d40790131401d14150403a041c14110310f0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 298634901 1250 298633651 298633661
    0x3050714011b0e040c02250f090b1306060905120a0614010e09160b0a1b060203010f08060c0f091503041b090b180a020d0912090b07050705010e0d0f15 66
    0x10f0121801d2008801d07541d80291038518180c00e03910030004102907aa500e803e8150b0020260419501090301c1555402d8541c0243c007282100600600300d642e581980c203950b03802180281c44194540404031464542402940754107040615050b00900c0103040c00104907005180c4600d40b000b040986550422003c020f03d0100035110b001c65511414044030781e50180454101100e01103a0819160030140d1710944c0c0c3c440d003072085840d03952a2403c07141c04110059010b14180e540902c0161031146e00d440282ea59110140d4000c074014005100c2e980300542e2031001410204405000e440b06090614030003202e50700240e900301c91403c07611303c140c0c0c00301186074014002070241e6001030080e1000e4401040094807480e41c1407025100080c0000c107c0440c80d0100c600d65840c80f0000c2141c0401c0341404151b00320000124000164110b9001400241050a0300c8210307410001810a2074a06070042d60031102512070316410900008890300400c0252000984890240c0b14141441a90342d0025040310 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 298636151 1250 298634901 298634927
    0x6120c081e0d141b01150602190809061209061527040c08070303230901170721020307020c03071d06030f01150603230403050714011b 59
    0x10407400703603800c29100001c0c800c0e03103010352410a2548981c4002c12041144100b0190318003c0c21308000740d00321864150300c0034200303184406441704010f8031800102e8503078510b41d040324038002c21519038001048520b0001c3c2102e0300014040c920b0181d03590000203890008644a40700c0d41c0015080000003116000e0070810060304a6001e880010084010b07034406811214400d02c0c2c0e207a24000a040200601c40840500701903412155050b69901e8014103081c07541021841c8003201003402c40d0725040010607107901c010161503050a00016088004104200600410400000f07002c070600d88544d2211420700c0102403100980eaa02d8000c00c080e00e04203070a8a0380380264271240d0100a4a102c072200d0b0324268111038981281c4da00c1d400002031420f02050b00460030b65107800e00307080038000181c5c1c80c94100c4045803814415845100c4000010741e8280c92001c1c200440c1700001400280b1800007441c040e03204005815691989804d800d08543d041c43c0c1c50004200000840d18110b604403902c010a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 298637401 1250 298636151 298636183
    0xc030a060e070f0516021c0215040609120f020409060218030d0509120f16030b15030c010c06140406020d0f0203060d0f050703080d0f0b0d020108070f0306120c08 71
    0x35051002d0b009140c034072010400020418040b51100103a201d00700c035030281e141c006084044440c1070342d42900c61a1003418040340b02c3c4003010100013410210784c050b03c0485541c1d49864010303030301d0710032401122040c0f0001290004026500392005a0726442040c0c2101e000da440145c5072201036201002003481c207200c02d8869030101080124040d481422a10451010344581400180b0460707428035150701449039185034003520901151940c111244141101d00500300c0403416144d0301c81400ca44a040044070350035800118420010394001e44201c00c1da2407042c00000383c1d40420444044154005850440310690009501d800070586070043c640c034404a24411451814488000317105820710040c02806000c03034103009414002e081c01124000c54020a0b16591074422030b24000c01411010305201e0814940f28504000741088500709410301d60603120171415403940e400c01e4076115640745c03110041586031400440d540c5e00c001000030354103100315500822541810945030500d044004007100c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 298638651 1250 298637401 298637429
    0x1d1b0c0303150639070e04020913030503011a160510050c04060903060e070e130507140112110c0109050304080607030e0703060f09021e0f0a06020d030203100305060c030a06 76
    0x3a040900e070581c051080725201400c0c800000090f9204c1600e80820b000100f402529000240001400e4085110f1803084841c20043c3d9142e61020302201070310321018001503418030041c0664503089104101500210b10051b06201c1e09082240c042c984000302100c0c103401050b00762103000580c0c001c542c0c00203449040c09041908158004151300005d100c06040d8548442d10040f410390144280720290006400d05200c42c0b410f102c10703014070555460100c0b8148682c0c10000b40482d00c041456440c5178059441098811307144445001800812100303018440081000140c00c540034030910000e14070400180d41ca4619150412307040500c0100400141401d10140700e501220220b8904180c0e540248000741d0343e203094000000602d10028000c2d0003242c010101110710070720091808850900711041703801005d0700c00070300ca40303031001e0711452016a00100c03035071401c54002e4000e564002840c80360000ba00f9525100e0074070306002074404c8841010004140031003480c46000d2480940507112501d0301c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 298639901 1250 298638651 298638667
    0x6020a141b040b0d0501020307111002030609040204090201020106080322050f010c080304030513030b0a1a0915010e03150f010603020403080d0b01170c030a0b09011d1b0c03031506 79
    0x3071036110342192502c581d503a071012034490380d5405801d4016a400a000319281d00d08408064000c80250400140c41e1040c1d900c0000c140849000302c910814000d404241203407030350b609000141c014004100e0555480f02c9003c24542c800b00054650f58080d0105481215480040110700c4845504124080e0034800d003a11001e9800081d0400c03815400120269030380c3c2e03542411502c3d070084c03546d20014112031440010078010300e10a003502604003008200320322100d914103a01e80710700748805a90020f11328000900c4036042c00307a03802102e642c1070600c0c2c500c0001c4800041e04003084010f01607002d00f590414461244d900c030907001e02601c0c150070118642425500d0300002c50050503a0045050b44900f51101142d11804001d03244510310800820281003040060107590000c46816645174a041c10f801000d14040000604a030030051b41c4180c0f401c0740c5078401c410044020400d540d4400d0311300080d00102c19060080c04604040d80103035032203042c40344110480e0300c02c40740101d11484060010724 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 298641151 1250 298639901 298639933
    0xa1403030306011110090303020a080106020a110907020a0501020f03040c050a0609090f06180603200f0d11030d0c0201090e16080405240105040506040e06070c1b06020a14 75
    0x1a40054090900080c910080c0483c40c1c81c08140d1007107540050301b0403000e501055050b4000d4400c005898580300b0841e031300c0f09800c036901c1d8020500070300314424604510714507040002030b25030000c0461040c0c641c09403a41c4c68050a9922000c2c0701d0344401c0c400002c00c800d01c16205040c0018010499040c15500e180483c0200200024040c510005a41d81100300e01c091080d80010020085082d400040e4400450210000c06980c841030319000d10007200000f04105015296545e044020010340012841009001e4003401d9400e007100c007400d0328200d0407002c1d034040105e40980030581d69035490000c0680700040140d01158400c042c466020014420400c15001c5d049580c145145095002503a0380c2c00c01c3e600d4021801070760a103621498204204070114510f610b410b0710010307202440a1f40301d5900b4001110440e070b00c500403940000d008200300a00c40c501500c043d42c002d2080c1e90b0040d01d03418806500390381c00e50003072001da40b00c021700f001002203c80380c0715100c800040203410510316400c00c6e1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 298642401 1250 298641151 298641157
    0xf040b12010b120f1e090f1005060d030e1915020708030f07030f18140102061e1b090415090f0c02061807030614041401150303031d0a08090a140303 65
    0x3c1e13056860700c00000b4100060000070303a580502e084509001e03404c21000981c0c03601c3c0401004969802000130130590580d46006d01c600a02c0e0140c0488681c041903103003251145150401244d1001980d1002224a01222024400b40003034102c3d04810141c2c80711b02a04c3c01c05164407400d80341d001808424441320812081d9510f140d003608000180e0614000f0407101403080c0c0c2c500c100782071500400400d590084424048a8400c01c0e000c51f440e81c0c45442c82c000c00c1007202115041900d00b06800a4a42c9001c41c88600d80c220003241c95a0400f98600009070135075294044e0340d506491000c0c0c041214504500626196600d441820402d800151100940724800140121143d4a88075100c500c0030f00c040085100464001e04204a07145141190082d0f0b400d00759404e403950030500526110011043c443c4401413980b41a80f07240306459039405801925502811202004512020b08809138090042c11005071040e0009030b5594048010094017030703501e03044584000740203502c8141988000080f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 298643651 1250 298642401 298642411
    0x92a120d080f010302130c02100509060916030b0115020f01020a03020304150b030c0105090d05010f1a011e08060d0506150405150a05090c0c070b0301081b030d0c06020f040b12010b12 80
    0x4500800a400168605070009c9601c20209140c8010098408400f050050155940340141c85084100062001e854259400054610528007004000b031040030740d150060704103180155010300441601060032a006812003101003a000810001003141c04000c052601901920401c1500c1c0400e022030754855450440c1c40c140640000c5803100350b52403500344805168848005d00506456810fa0341c0542207400c04108443e01c0c1c03042440f8075601540011015465680482d6114669070b4011540b40b00050202c0780c200405c40c00140110300300744603080c400e071400ba58001c211120281440100d580003001002c9000d034941403842155682d215010803980c00300d403802d415440b1008807406510401041200798803c207070002480480e040003450480324294295501e4600102c800d01c1e0055020110319455045240d96482441c010304001038418081da030014106150007400321141e6015800031007482c580440e200380da080942c4450743c0906113045610f402d055510f103402011340c0001d04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 298644901 1250 298643651 298643689
    0x2030a09060f0507060c0e130212060105091f200d080a0605220608011407110a1110120509030c010605030706020706080c0c1e0114092a120d080f010302 67
    0x1b8601400c1d1041c04869000100201800501ba800e16900e0340258807508030681a07610710340000c0c0b11580540700b82c2c1e0003944050400c0c0844000345090048001281412a0501601420b039100e04100540301c3c5014039011001080c42d0752a511001d070a0f1400100b03011111404c0c81802d20076a111804010340c1e031900c8059802408080e0348002014042035042040c9035880e004002d90741c4420403007a00e0181d6803e4503071031714000f13503651802d0302c94054030300182220040c0410b10070181041c01440c07664080616090f0202c0810113070403c26227000b9a610191648003040c4050613110a224031030042c0781c100c0c01001b8051406601940b9074030340e0b110360401d1011510000794180c2c1c146d011510203105180030366402c0150b00119041d03000038641c030700302150b1030020f18020f0710704408202c502501d1b050006015104d844032049100d5001d111103605900c0c0001e010401c542c840505507480e0010490281500406855008207001002041500c202c03410500400245e22008400034442900b41 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 298646151 1250 298644901 298644911
    0x50406110f0f0a0c060c0c051c0501050702060910051603020a1803051e01090308150f0915010807080c07110d080a21090201080604050a150602030a09060f050706 71
    0x4540074100480104054a240241000740710b038140003088600d202c03071007280030300c0d1641d4841000300d034081030102c00141840d01e07001061200d4a01403007201302001e550201310140d4011669080e0a44070306840c103130b0160703222a080c4149101e0601c162030b41c4803201c110411161420708030002e551001792100000f4540c0c00202501020b1003854094078102511540314a4031b42e8034682183c0c0c8803804d003640c113144480602c0301c1d0024030060250b0300013642c00d5640d403c4c260301c0d58240c12450b00c0d03804080c15801101038260483c140c5801700080d00c40c822402c40410003100c8800090b00200b0024080401c00c8502d0041028801100c015641d0558101e00c0c0380d20450400004500000645400641080c80116404103500d40c000c1c00c1800800f504840720034020f800c43d84002c10703900489c10003030100d491880002c545080070b40c4220b51003072200034003103001054004c141d500c004041e00700b01c0060300f0004e41d903500d0a400c043c141d4001c014a10300144c128070100c200801c10300505000608440e154 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 298647401 1250 298646151 298646177
    0x6020a05030712091703030a0b010318061d19120912121403130c0911040b03040204021b030a0e090106090308130506031005030601080d050313031103030420030c01050406 75
    0x20a40a4003070300151710207081000c070018003d59a0b410803a00e414540c1e0902c084100076501c00d02403a42c1c50b4591039901101e0b010f95640704030142254500c02c518400d0742d41c0300c842c007c0c2c8081081e044840d9032121341000840030f50418514000c0c0801c80c810601109800800001045100070b409480d0040d038114824480304104407251103441950b0301c1121030200510001c80c085034540c4120074032035035051098070703a1082d1440941d2095080114071800500c401c004100b8040d00456009200030401840c1203910b050590f0480c0170200c1c000107070392000c00d296160350740107818400c54040482300c1040035031402780300a20b560f485000081800310040707440303107070011001e84080181030020300351500ca1400690785140b800d110702c20140f0901c9282c1c0000790b20038004c290540303880407035500c0c0e40c510b5442807142880c800810804034200061603001c012000307000c0c8051405184180c929080e40003a483e21000300c3c07030362484054400d80203104050702c2c90303030850200c4003180d83c01d040507051000e00c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 298648651 1250 298647401 298647407
    0x213140904080d090f0b0609060301150b0a121526060403050c010f1b1404210c0e01090203040b01080c0f091302060705010e1c05040e0a18050f0706020a05030712 71
    0x413504006145803a0f000362001045040e03a0703214400c04060340c4400003076480d8000c060a8078024039801d402c0381154001480b120320710000410315402142441c642c0040b04160f21812201d04040e01c041001020b041805203e4201341c0070003102024901d6840582e01e801d18058035840080c100400744070b8005012200440300790400c4000088108007003044001c2000040000c646814000e0001428608003400d03180e1035109644c191041540c1040047c0018608681c2c0c44d40c0c00c1038142c5901509003c0003405034480c82180d03000e480e01a102603100d0a051804192125060f00071130410f4112444482c2c260711303640d50141c943caa0072514814203031543d10043d1200854040d0103500480700041410038040150403025106d5159003c44500c18059072101c00310080742030190b0300084041004000f0013903050001303a0002c80d44640007404031200003030319440c9000e5a104036029000f00212008415050000000905450014040b60f480350f540e0302d5180d115005000b404040e50880050300144 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 298649901 1250 298648651 298648661
    0x6020a05060105042706060303110d02070e04050f060108012403150911040c0503220309090c03020d09060e0c150909040c1a120603030f0301180b04020406030213140904080d 76
    0x40001c040d2074508882c6c100304018200c0350105402084075401810b20025002401c4802c00352654043c0590741e04024102c0c0c0240009803003518248203070880803c01030400c3c8446402014500000140d00f00741d0102403598464040c0a10300d100082d40f0708101048211111410b03803010108009507807402460909243d01a401c0d00a400c24a4021145c102d660064000c2d0300403980d5801404140c580720405588045095100a0009510f18030410500602c2d4100c68803030300c514240941060a40d6228604841c42000103540c0952a400b0741802c11030180403814400d40103075034076080f10310b1881c90345000c0d22484070b030980551500000181440f8440120307102905101c031140f844d4021800744403004d80c000035240003049503a48080703916464000304813448800de900f131a900307503880d000d0888081c0c21300e0b0320440f2403103490300e5603641d041d81c580c0300a0019051580780103840d404940c0410400d90115004015000811101c070f64880da10900070903407040d1b101d4600703582c410340b204441010340 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 298651151 1250 298649901 298649951
    0xf130618062a120e090c0c031209030d11070311010c020c0d0201020309060f040807060305070f0c061404060c0210020702031b15030a021206060a0f0f02030c071401030606020a0506010504 82
    0xc00742c00c400c0c50b041980891601132000f0102c0d400e0020341c40318901665148242c8820a40690040149000200080201c41e500c40200010f482c10001b1880e1508140e44200000c0c114100002400360109a007042064540f503c40e10f000300509181d140000e5503903401d19040520800e0035616a03030441e8400c208036044600d001e0903694035614401071254207500f2034058080c29000342d01e07020032031911a104070303407081e0203070381d500c824100c03171a0800e44045103456001d560441d11901030000641a44460500071031284000040f50281c81d04028100400140503401c543c2c0108909009030350b000480c8809900e5144050505240c0e82e00000c0c80c10901c405520050030010040251100180d4080c007590820650040003581d20b42e810840e05104003a00345020800d000709180c2d1003441030b1665100300d030381401201d103880b00c1301980d90318009081d0701003001c41000c0f0940c1807095a250046d80d00a192714002403c40380d103199151a1512014080c10b802980d5594400c0303003848132584614182 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 298652401 1250 298651151 298651163
    0x20f060c09150c161a0901080604181b050111070527040602040305190f061d0102130518040c0b090310090510140603030f030402060f130618062a 64
    0xb5a083d0240c07581340c3c190079004803401d111141000a80d5901401d0030190440c08114180c5000b80b0708006680200010784602e0b0055501c0d25801e9544192611000c01caa01441c807001e43c1071a03940e01042c40c1080764010504101400001c81c6c2441c40019010041d55011250540081c0c005184402c400100b030900320201c2203008240310900610340e0042041c0da004000ba6400012203004980c0c041c00b040c0c0c0020180d07103c5210030000f060705640a4900000c0c8986011903004102480b5801d80e008141071004082a0150801c40c52402c6c0c2510400081c0e01d44500a0500d8240c460143c00f6241380308201260900007591031140d0303028418802034131a101000c0245810030b051242e620340ca5403031b01c1e5546900d00000714001d0180140c3c818410342c0e0007402946000080d440070f4241c1e403c0540301b280c200006020b203c03058202080913245c980303024010070045d0b61400c28014000e560308201c044c880c21600e44203101e0107900c41c8003903134815194080702c040b8021588145100b544040006040c0c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 298653651 1250 298652401 298652407
    0x9060c020315160914150703030609050109020d051b09091803040b041401090f0b0702040f060314061b070f11101e03180303110c070e040b07020f060c0915 68
    0x40c203043c0800300b4070540c5103030750b560754800d8490a42c40080b001910303015034005101050021140071050041c070b6214828600465610b95500094003a42d40a80099601d542c021402d003883d003d48e8440c46034801140c4020000241120064010b1361048214440c0540f00d440e0000304000382d0343d015210791170104800c9941d0b6a54840e440380f000c1d0000d0040c4034506a005040e1003003903104460380c03800c2d07803190780b400800c81d450100c160f40580d120700401c0f41c2060300d410041403208820b100d080c0046d40510b1400d0100e6540c0400350741031000c001e04c2e04075480312654000321340f140b40000707940d01140d101d0b80c5001e14201504095080c0d6a1800c0c4156100d20101c41091095900c01039900c5144007900c41201e807244c041006134165804806110038803c04a00e503040405e01c00e030008100070b82429642c078900b40c00c00107210305024590700803ca03e800590144003c002c00424042e9002e0000d2010705443d6540c0b41540c4d8a07540f0107450003044c81d4005c00d050320207a5030300d14050300307080b1803040c1c03590b07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 298654901 1250 298653651 298653661
    0x307050a0c0806100902130503010603050309181506090a090f0605040e07061d0607080a0f0e09010e06010c080d020705010b0310021e07030c02130213080d09060c020315 74
    0x40c0d00d68a044084504030114840000d14500006095000b0704904070503141c1c01d810098810029049911070204203520644005402e850a01c5a03401560184000c0c0d40e56103107c1c401d001c55020503c44004900408204010300001c4040c4600c003a14003c446003a030312085030b0b0014a94080c40d8001c0820140341144001140c0f0140e4084800c0b00e0040d80c080c030402910540041e2629428400c0201040c10608980d1003035030b2040c1c0801c99408000c140504015060700e586113035400440c2d80001103101103c406a455800001205012000f20361440c0550f0410500c9407d448026001034140b01e6403002c08420095010140c41180103654021501e484140c1000b90180c2900340041d8003901501060fa907010b1241c3c002c40700b440351818003010545600155190460340030403425020885040200700040c0d94080c0c43c03881c0080c0081000d40c44a440e00106000080694400d4065a21004540d8006a04080c0c4041150380b2401d021002d00d85a0000c40e003021680003214403082c000808000d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 298656151 1250 298654901 298654903
    0x901052b0b0103061a031b0403030c05060903040506090103020d241d070903031404050306011d10060f05070213020a030e0d0f09031223190305040812060d05030705 72
    0x865000c0480ca018400300400d03900540440301a80640910541207544810040000300c0007560400e0f4054001e4102080049103c209600150030807000243c1d0000c05c0005e208040043c0358029504501462504d85080b002075118440c040105040c560041400340d0f006643d40e203c034141d000c0c11600c0c0c0003005540c40c1c407442581598020b11504c64601030b0300a00402c40000c400b80310b5000390710343c049600d045840550b00021140702c100d4440401704004941c7d80c6003400303007600805038000340c4800484103810a220565004180180100150008100240e0312000c402c00c4200325091469030f4080500110b01c85640d4440c8940d89180000741c84070b030950345035100d000c4052401c03082d11103052403000100d6041c4200c2c140d032400618600c805101044200040150324800f90500840c04807550005451421042005180f41c48000c600c82602d1002d001c410f0407041500c3c0340411552a140c0e80d2001c482c002c0862a0304040302c0f0000088140d1180504008600d801000702e03520380410340f81407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 298657401 1250 298656151 298656217
    0x7090e01021308031c02040b0f1303120806011e08040303020c0c0406032001140d0f0b091003021009061b17070b0613020403080307030507021612020306011d0705090105 74
    0x1140e1000c0c917142811002003810301c203580a580400ea1228900084076441c154182c00841e601103042107010b07400400030303440717004508480c500d40d110012140b801c18005840144600c0304400c1450b01c060340501c46981c04080c50794810380c0750800580343e00b0351031082071a204030948120340092800401100b4070400e400729050344040b060034041c1440b000b400440344040640d40f030105101080c4a51901c06032240c00651506804002c006060491440010b01d070b150f0a40340401c40803a440014425810a40c1800b5094207c1d424403048141c40c1c82c000420003007038007000341c503143e0b50808810100185000500240790240b03850544070030540c181020305190550b8202c3c41090710030943c95088078280251003c80f81c000031440d08580d0b54a03c16009050003d14403c114003c0f48458440d600b251000c04c005402c62104000d45c009003441418a480c0060b000094150030b647c1c0d01c050105960f91341035600580501e4800d44440c1c003100181c50601520080810740d201d06010b007131000f0340304150 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 298658651 1250 298657401 298657417
    0x7030e121206040e07150c080d020316030e21090907270506030c1803030313140f0601033005032e050f0f031903020607090807090e0102130803 63
    0x41102582c840d641004200d6000080508040e0083c03c0104000c841680c0746903642d00d003500700414540601d5032403a42c5540a0524003c07420b601006108543d42400b43c14100d40d03800d03050401003552507900c019550700920b60a580074840c059008029000310f4002c0c1d40f01400041e04001090038258809041040780040049998451501e00c94000c903445000174111003010b0a044d00d03680300c2d0124181c40c0e44c0b121160130700700c1e610800301c4107507a01e0400045120701d903a0342c00326008039440d25110124074003070315000c3c0c503035441584d100d0110b15010460904681e07010000700b0310160342c038503980381090303001c15000503000c0403403600b60345a600003000314460442f0078502c0c601607400c0c40b0352418000703046003440c82c80d1025840510171420444140000250018484925220250b0010389031820441e26810b540c00c503403002004068040040b42d40215090034529030083c1000030700d550b40d41c3d0034490721510701d0300c400c1c901111410079411030700c42c111010603400a0640750340c42ca0b9900e07813007091 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 298659901 1250 298658651 298658677
    0x70c090e0a05120310091107050a12030b0a050f0919051311030d0e01050306060d2405030f2e1401240c0f03020f060727051807030e12 59
    0x850920400c8418049034880c0a1000400c1201410206d410006104100f00d45244500c00c002210110f0420400c080790311b40b050024800b65080040d000b803d89081d00007250040c92140f500b401556110071810120210641e0300150a517920042010800c0d2a0040d52500600d0310003800209000803171011001030040398800ac483d44007406050341c803044983da08000a68104400000398454002903400440060001c1d003400182c40000044402c0c5c8019034540c0e001c182c10503503007103802d810940b004110480150076030a4482e40b040391101c28280740c0c0c011014880000e616050f00340e440350002c014004030b04005100d13003010720102842084c050040e080c030802c8080815080c00c0198111040d046540340c0000d801d141d5180504c0500d014021803d5000754120b402c80c5090401615224400710f96500e0300342c010101c1d0752040380049084096403990704090034030042e1100d014410300c0c80d80c12031010342c06a541510840084c64405418507860244050240c0c849803601c0c090881034000c1b003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 298661151 1250 298659901 298659913
    0x14030c0c060f07060b060409020f0d050a0c020d0e0103020f0a0e0f03010515060d110f0a09090203161107090204061d030703110d030210020304081209150c070c090e0a05 74
    0xc0400500d03001e805520903820300d040210500140b11600102c005000240c6404e08064031110000140d0700540b071055126440880d02803d802c804c2d0017801d801c10492130f8200034110003248002d4686440411901c1030203404010111039901c00e41c121341e281c5c84440324050301c440401c07000400c90184151014400c202e9003002215901e018401c090090b00c40d19007400c0303e90551000c0c000145c000c00e0100c807401e1780e03408502c500b005a4500500580c610711601550310903940002421501c51034004062007803040c410030902c1d402040389182e000300c55040000c220a03400002c2407801020382c22074041c15001203000101241c000c890740480e242d8032031400c202040141c0500d591440c0f5444007514650714075106490908148025070712003030207403060310307103213480362054000383d91003603404403044840041e01301140c2e078000088a40100c02000500f690b100c1911810310551405422945181400100c140421410411590050030108000d1099200685100b40c40784500601030710240508 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 298662401 1250 298661151 298661173
    0x50702010c092105160311120a0804140f03101a190614070b090304090e1906020903010b19090c0207180b0f2107060207030309030605060a0314030c 65
    0x190340b050094070003040c10b54840144411009400c0264508142c42900a4050a04401050459000181d80034a03540060300c104c203014050369689103c3d04408039000050308c040003910b20400c030340440e8064400c860b1782c0000203001610b14503a01941070392512400c6003484000140e900b010080c0003001d4841c0c00b0b0f00e9504c406112200d02d000750342050b0b40b0301200e007d002c4140a5681690080900300f12141496081c1d91280d488800645030100c4a5002280401400c11a4002c2c0f80901c1440c2d4050f141142800100c100d40524120005040c26008280803c02d03803001d42c804d0486100090841c4c000c212041e103c0402001d0038015041031034142540ea1036030301c2c000140034003103405070540f544005807103409140062540707000869200705584e040c08819603c24010701d881c0301350180403482c29a81580301902d0003074554441019500003102c10008a46c000381c2000889800240c0400e00b507950300002032008810340c0000341100200c001c0400700190000c041d180d80341518086940c03e84031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 298663651 1250 298662401 298662407
    0x190914210304020904030e0d0803040b0717061513060c020f1c0305031005040906020307120c0504091e0e07140d150e01061a1e03040b18070f09050702010c 68
    0x800c04080500402040400c005003003010384035600500a02c4c102e90002100800643c0101c0b46040031340c0c1c4c445010082c0b10034080d201d441d487e0400f41500b03000c13402c40e44400544039035480040c0f4452180c40c85031041c0124020f80003c8840d496141d0341c28000c160780b6044040c0c0781408202c0142e005803030241d8400001e0406c129442007020b00b07002400200c22481c4c0d4129842c1d80010844d488242103807000081e1a00c40340541c03e2024400c400240e01c0345440c90008203202c00440d80f01c10b0b40c074107080004014036044400c9400f59078040701c0108903200ba2903851000441c40c8c860696805241103d10948280c020030010161403640701c040000d100620200f210b002501c0c1da0241030360401c0f07480741582030744603445403444581070800882c01c243c0d11494286120040c04043c650719200040c2010580360407000d890401141901c0b4508504182d11400d006030001080d4a11002c500010340240c040c04101d828010880510702c49103017130f101c01c5020080d18080d0340440156081c441180382d0702d40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 298664901 1250 298663651 298663693
    0x130b1c03020c040204060203041712030c070201032406030f02130602160902031b0c0a05060a0506101e05030912041e060f27090609020c121809190914 66
    0x36041e401076083c5412b00103c4000c5070818501000980318440c14242d9602c0a02c000e94030821249145070344801041c000982941c507070f1030001616801001d441e00c20043e40d0306042040d40c140717140010354881c160071180b00074464094041040010a600095200d0707000070900d0380039203481070302036606688482c00010f0b070009079030102054902450401414001e4809000c04d4101281121141030b82510b8050904a0996041c040141c0b15020003d1904207035034400b10150540c80c100141020000702c80011504840320300b010881c000001c54410302d02000784403941494002103a076600c5d505c00d901d92040003402440007500c00962400500940202c0500300a0407240c2c80e40843d6000e5141603604102c2c1c18200052045a0b072100420503404a03c07601016080b25003005a0b00c50401c1d900f03504d0300c100506224a0003c0c20000ba00c00d24400d80391040003040180c070003034010385850f80c400900d40b400320300f02046a07103041c041009000c01005c0304a40c00240340242d501543e1116241140e000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 298666151 1250 298664901 298664909
    0x303041b0f0b0a03020d0e0c100c030804020910030b0c090103050a09030e101215091b090e042105090f01050306010c080d0e03040807030c06031a130b1c03020c040204 73
    0x502811010040b41120780d0050064040c10329005141001c0d0103404012542e4a02d030f001c040d80d1098907100c04030f040400e500802c03070890b0f041031421845160380040a11100800003405800058080303000d90403018458000f850380310b042100b0300d2030082070f2404c0c290803a801d0350340080d041c4004144d00390043e01c540c5118036050780e5103601040c4080b0600171a164000d200800f048658228040392030090300c10104105c4c030250a4403403003403801c410142521005901d0f21070011200c030a03211607a420032880c8040b1121114032001700d5440d0304007500f5a100c0090750100340c8012114500c0b0003a4014000d200c03401c42240d07031001140148004440b603000448045001c6a41800c84502180c8030801400340c141055401003184105200142c1c2107800039032141045512130744c01402000310144181001d001e0a01d41044207901c0c1d2001c080c820250041060701480320403142c0911407040d034101e07509100001c2d0070984d505060078520414045050400d40040c05804001102890640201c43c111 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 298667401 1250 298666151 298666169
    0x70317060a050d05151611060c0403030f030902060a0302040518010305060c071b0303110d050304031407050a33140720010603112722020604080303041b 67
    0x42414681440303440c1182450684c3e0078441d00c46034102d0748052000d480d200d280303803100341c100c02020032201809441c01c5840000c43c54211b02c0c1080075034000c004c160303011241c0615181e02d401c40741c154250014070390b1140203500700900203015908942c0680092048903010b80b581004410511181d2000304420700005007a40c0103070f80801c02d516403d00150403114003c560003250103111111104003002581c0c0214081100700421383c000840c14020300c4980b01840c24824991300e8a075030001c155080c0a0036034454641c0104d540414064100520404a50f01801c0e0f941c5001031924500000f289a20308604001c0d030000005000880602408001d080d0002c03815880b91598841603444901c809034119001b08458a2060743d54000d00585000310b014110b4103d0400e40601489844210f2030122218983c00302c0d044901c07031755814196640490804217211110103000e000040481141c0ca0295001d0380c04100800c084c0000300045000d1881a010b1004c0240c0090114800c0c4209215141d00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 298668651 1250 298667401 298667419
    0x70302060103140304051c0308090a0503090405070306090c020c0f2b02030c060711182509120b060f0103110d05060f09071d03030301080c01031d07060507031706 71
    0x18014420102103c140301d050707034249910b80b0041035070009442907040103810003076052410300d034121216a0300211880d010740507100c0b164840c1603592183c0e4100398003071591540082c0e5164440d60140d40584112141172044820703042c0b00a6444010384142032103480089040305e51031508140c0c00410000070500f014400741008811404140c910340c00341d81501034140384d48603c0c1e40303c070020140f003403180c117140c00c0070981705060201403001e03810304150740024107013400301034044884c00c0300b544d0022503094904580ca50700206d412100c02d07800b880c1c1000740e030440b0404001c10f10110350322640007503d1440040403200011400d40e0401c0c0d418504806042100f221a40c0c0103410607613001001074600c4000200030000f241e8514007c94600000503000c0c05c4440100d018040c40f4254a182140154155410540d4040d20703000d100007454141540c500560701c51102d002f030200c41e5013001d1400d8440da00d5a94502400030351001030110005540000d06008a12201c020741d030048a0183c41540 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 298669901 1250 298668651 298668653
    0x90c010522060801090501060912120c0b010b0a0210110906031e0a0b04050a0c2a05070b0a1115130809030105010308091c0f021c200109060203070302060103 69
    0x552584005a00650300854107040c140800d046025040203155603610f100482d0314060120f0204ca0040c0c220380c04201c207a00342000510300b14002c84440a1300010308010746150803106036640d00c0b031941e0040001c0d000c080000b032000b0410024002c48040d0380c09661065034405442001c4600c603d001325142030041c0141d08042c1884405181d2003000c0700d1540c0500b069441c41425650011225100829160309104406060900405800c444519414080390313156110150545520400304900702c040c03001c0106c00d207013202001d45007143d00241a01c14403a01c1e0074840049030720440d540c401240b80e8040c1c0031051000040c0403a10320a0210601d0484c1c0c44014503c020801d5051081d00c901d0b2007800300da150765600f0710506008601c0b0f154019542c960035014000c1c41001c0070801c001c4c0e00103401062001ca4455104400540d5040303c8411040c0d103807159405000400c04806440c40c039070300d030040d132103c20003001c00100b81c8426220220610354424049a49205802d0300600523040100100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 298671151 1250 298669901 298669907
    0x2130e010506191b0501090201171312021207150510060804080901050c0f0d030f020c1009080c101e020a05120c1e0301050405010803070203120a050d0501030b100e090c01 75
    0x100c1c400028949030361522000c480310441c0001c0034205560ba079540e0000041150307088502d0150300070038ac2d500032196183c0f0720345111201c05120409420150a800380410003482403040e1080da050040200340c503400c2606089600041a15140c10040e10b800c0110b000041281c0b180d0040f03c83c01e41d1564500d54803039441010613000b0f1240c1506000e0700f400300c03002585040c4600c28640340c4000042121038515030000f003e80b1000310344441c0e02c0d8410420b00711116004078214251046800e404038000225240400312031051401c446590300410015031069480c58011104806200d203040b088040080015022441003801560105008011621208040462a990081c02099918101003012045e1002e80958001c014a000d0000005126502e094400d8038003501d00c8500550505c20540d010a980300d0821480c06d88104000c1401c10f4454451012070340030362000c8a0901c03442d6900d1402c0c44a092080c0e5440c003c10021000110761035040c80d00c220320401c2030744000c00440403144019 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 298672401 1250 298671151 298671187
    0x10203040b130303090b010b0712210e12030c180126180f010b120c10081b0703110136030c050d080403090b0c0a02130e1002130e010506 60
    0xf00c2c00e2503281c02c285030114618100142c02031041461a698903110751820081503909605030b841841160b20071102c00724407103603428102e040362610024490314240940c42c940b6214150380c24520400000304800d60b400103000d000c2000f030004101007a030b204200159084400c0100080241048010307000341625044420380d040004214182c1c4007a01018a103414480301c0103100701180e44500c0300009130b0130f02f011400c0310705d252000035010760840307880014140c0040440380b508200c0d4100200b41d44c070700c125441041c4104080b03a52030342d80b8200d10740601803560000244035103503c0d04210414081c501d02810f021400c1c80c40800d601c1c110b1001c01c00080c044041720681c104000c8130038000001d00200b065003040c5203182c50300a05460207140046c081c0015070014440d4401c18084040d42c82c80003d5000c0c0d45550445510300b400c019121090000c05038207070411207600c180d200000e00c00c03c05500900c6160507110703118110075140c404c031044041c1c0178421590001410400c40c81a80b03945155 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 298673651 1250 298672401 298672403
    0x209011803035a230307020f0d03050f13020f060a0e04050901050108060c0408030f090f0916090807060504030b060d0506040c0504061d070c031826010203040b13 71
    0x44a0702ca01e804100001d80080c0d0440300001c2c0a9000c002c603800c0480d80218520704a01138036150600798034031403031501d82d50540300d05503400403008030109090a00a100740405814900202d49003080502c07030080180c4800e031074503800c400c070800200b0a60141d9450001c120f64015280c04014020241800505c2e071015041000300038510712000201d640d03d00400f4041d07001d03100049034950500ba80c8034280385010300000520718081200300031606020003941d401d408503880207501e501e1800007040c0d010101003552544246040c00300009007807094050310a01c0d20342d41c0d80918507626403454903174552840c00740402082080c001000000d020700c0310180c0c800405840398001c030b03000d0742d611880e10b20103540440c1ea01c1c510100901c140d08040c07203180001c0258544100300307019199810130180b40043c0c403210800102c95489001e05001d0004a1000c5040d41e8a451510381e494914950310145c1a6030840c204200c00c1030040003850500a0324001c0b03401001c0d4015507291480c00e0480d100010704 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 298674901 1250 298673651 298673717
    0xf0e13020409110c12031003060e0c0607030503071418090606090a060c0506090d090e0601020a080a031505063a0507031a1807140409050a020901180303 67
    0x10002c64144210b010b10340b501c06000c1c2000341c03944007841800d420240c0c840c05690071040300344104084a404805030b14100c0340c00490000e0f030382102041440c1085044900b041e080a80001e1f136400709980300b0002c1d44900403e40d40c40011908820002c90070788a00c500444d403980c0071112000340e0f8541007184e10380292008100750300c0c2840d050081030076400c00d503108501145031015250b00f4020103001c0703181e11183d05e2015128802080d0006844594503001358211000200006880d41c0d0081150b01065604050001d40b07601641d0402406031a4003142058100342c0e5847c0090780781060f8041d51b429034414900e442c0140d24072006907411038540c1d44000341c502e40189500c08c1014807172140a024000b581d90101d844181c00340080c450380204600c00d80207800401030300b2610ac6420300c2d2680c0210040c600403202e0441c510a5030451b0280e40c010f091014a0401130150681e0310364001e142c8081c0a89030914410005518144603c0c028800034000c50441212a0b0010703111850388010250030070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 298676151 1250 298674901 298674907
    0x5120a1106091c050409090f0b2a0304020102031b1b010804050c0103180c06080a050f06031e01140f0109060e01120611070516090b10020a0b040201020732010f0e1302 73
    0x40207120030f81f044440140c0b40000d80b05900000e025850740c080354800301400c03107080098100c0c1c002d084090200503041c40d80c0c03040400801d04680c400c0c01102c203007404800701004c0094001c240e0070380360541005441c40102850300d19401d5540103000c0244a2030b005405030000d180343c0e000540c098803001072802d1224291000d00000102401c1c2c4000c040c2840d650f0305103544c42c050403907504944002d00090000d42e218400c00c601c6540000f0301ca03403040e00f0058114900003410381c00360701610310841c0d41e00e01ca20300e1004100c41d48240c16076a904031030000c04c082c1301d496a078400c032034403104080c040c510700e00170340c5c0741c1c07500210310310381c20461483c0380300c1d00b01c2072400745036407507450510752801000c0200d0320b08001d00b040320301101d01850414400481d0080041d040760500a5502c034814100140034202e6040041e05680c004d05c040342c0201911130000307100101c1d0110f0604071120100040600b114008503604007940315614032003c0e09101e40340e658507031003128101700800481015240c200e940170 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 298677401 1250 298676151 298676159
    0x1110301140613080d0e06040b0a0e04021c14071e05070503040306020c010b0415150c26120112020d02130e10020c0606040504080f030c0705120a1106091c0504 70
    0x1103c01000412441c000340c050074542e540014030500344440315500c24a8140000c0c4290035130340044580303107021070806280c280808008540a400f40b0985420240c200d04000340008207141c0007201004502a0100200e0351490b2058461000003103141030100d02e0140d001d11412300440003444117900135412a8141a9a82e0340c0304203990102081122594440e45800c1c3c1034281405901c0c1000700f581d540950311414481844851100040b41800f0020500c0984d000c2c00480e484003c0030a40d9a036180404440701d00ca01c47c02c5034401104001c40c00110350000403c90401c4260aa184e0780c0100004841c030b034207408100b0a90b105ca40b469400541e56004560020810010032000e544c00b40405600d8071140a6a1810008010607a6020314140402c02001854800803105e00842928026449443e0828403000600a120006090384607115202d0070340800840500390f01d90040c7d47d41b0100e0890008019219841071320700401d254880b14840da500617191005562000d413500d8007904082c0c1d9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 298678651 1250 298677401 298677427
    0xc0903030711010f020f0c060a0507060203041b08030403050a0f140105070906091d1602100603030e090a0b100f0309080f0d14010b04050105160609060b01030509011103011406 77
    0x101040328001210400c003051541c006200c00c111085074005443c071b072949214540d49030101e83d01b406100b03050002c0c40c1c07001d29014a050304d040a0b04040e00310f40328034042c90242c0d2444a20000304031032940315200002c4800c030000444003601d60010207045007003042d9644050401800404030b4440b200542400560b1001348100d07445051660744c1c03854030903d0000098204007868016030000f0824403554000c0042c04549150400c05040d82c010925120710022820071a00841e004401414000008145580700044080c18a011a00348402c1d448904401d000c032030000d628150440341c0bc0d60920940d500031141100000200c0c100072070581d51507900c0d80002e9100005d4049030000101301202c40c80303814460074903c007800100020383c43d414840003e0032801240701d25410420002102122080c03a18000380381503601402c24003c000c2d41e41343c480c0140003030940280c00249014000703041343e074050044402550303e60185525507401c0007442000c3d451440055500038008001e1000451a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 298679901 1250 298678651 298678657
    0x3020301020a021f020a140f071e120507030219080405150d1506080c13150c031202030705070b2703030a05150901090c0c050d0c05240c030c090303 65
    0x406540130305128080c40144061020511415580e014814070000c800a900512051045140140c0c19915408260101c070716030b100b80b00009004641c203d503500071045d0070b81003460402e8842d02640b04450031400007101c06004048010300168010012028842e4518906c03001e040c1c090294245015221f03004203803400fa9824101203403400006000c241d29506200c1c1d40604241340c040107011625103e4010a105000381001091b0940019000340c1e002013200780400410b031150510701022481e0b070700a89049145602074020a41040e00c0b43e413402d0031417007101e00c02c0c00d00d900da49092501c85d0b10f42d0080850b00400c050302200407481c0c18400501c020448010b0400030f41c0084d5901d142156000040d20006441d07210300b41d001c401241d015035034100c035503030648012000000e012440c46900725200426000054542d0050100c5038207404e0380082c1c11032440340100112107507015421040034448510081c0214407a003d42c0c085500c090b10340c4010344d0840300381c4094504142c1d0046c00a802d50b8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 298681151 1250 298679901 298679917
    0xa200a1a070b090303040b040b0c040909110916020331030602040f0906060806013f0b150405040c0c0c09050105090114030d11120d0e0f07080c190302030102 69
    0x510042038a07400c001c8801d591a5112241801650540c1050799503400304c080c000e84003c08860b241000940f41b41054800e0b200148083d200c00e20400e1040d0810314154001d280d40c0318080c154100014030b22481c4181d4107280180395030300541c94020741c80c40e684448403c9940720319100041c070440b20700c2602440b5804002e94003407600140c0e20340c03405c103407500c081060b030384010301060401d902000f141c3c2d0007110240e4013030790a0801c00e1680b103480018140f03012401c0301801040f0130120039100d4144090390000c10a40b800c0e0000c204001030102006000519460304444282c4104020308c91400c06800080d000e50f0142003141d6101801e90303500340180302e550041c6040c1c41c0d0328030042100c0d26003181d9181c010048582a0080d41002c200401e40b40e0314450b0b60341c0e003884603803400c0d00b103070a80410445a0f5a403070004000d44540304882c2480c0640031030290358115100f1200510405400032031703039004403249100240060000c4200340401c0a4066410042b4241d11800000140c1c8081c00180401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 298682401 1250 298681151 298681199
    0xa0e0703110318010b01020f030a0c020d05060403020610120c090f15060e010f050322030e03010903080a0615020a0b070302070212060609100b0a0e041b1707020a200a 73
    0x1d005025403c0382107601c22841141103600079901e100004001004031200340956280844e100d403054001b040114004000051040c45060100701c1855404503200d03009004c9054080d0300e13242e41c0c00c81c0c440e05041155000d050f0300711094041010440c154010452404010404101c012a20704000c4910140c2d40c80600400ca031001d001c5010740c1d2000031040300751801c1c00d10ba030450424051010a88400b01a000074980e00080381500303050007401c42c3c000c041780086c0240001949450001c010702c0c0309480e221215820f1003800320b0150f0115141d02c034210761030780c02081502069180d81c0c42021003d420841456400c001410241c0c032080542c52504a90100078807150500d0400d100243c035000b07001402d0301c08504028400742d8003882c01c0320f070b403e5020703c0d200107103150090009000300005441c0b5240200c9600c850b10505030085c03011441c10007503100c04e07052030b6500e4001740d0b01c4c0c0c1e11508000700304c64806100c1161000c0700c1c1308910844000a03005204881d140c0300342080c5549a00702402c04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 298683651 1250 298682401 298682431
    0x518090118050c180d030c05030412050c030c060f280503190605030d050d0f0e010605101403072007240302090306040605041509060f0c0c020a0e07031103 68
    0x700000c50145039040301e108801c1c1494261800c00800005088409051041c0c1000714804281417007048a051010f400c103080d00d5445a660a007440e00c811521070495090040c00b480144a1031301142c0d0070300d401130150180303181800c281c1c01c542d0941d1042800425614100d01c2102901c01e4030f941c0d12100c1c44250715400c0d41d80c202250304e00107030706103920880c030760b87d0400b04144155200810446c3d8806000d09160380c907a540280d11710060701e440041d0781e8840389001805119007505401c81000c9036802d55118040e2404144125401c10002c540c0c12401c0d1400c102060119226036030043c243c507401c1e03580c001844220003896040001c242d01c52040748207000305003101d441503034100340410003150404514154600c004682c48207401080906510794510014060110703949000144803c5e0090400c0203c5492814000803c00c039451004028030b070010490a20b8041c01d888665907400030072801d0f00c0d5103070828008030604000d0401082546509425041040580185004124034001d42403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 298684901 1250 298683651 298683689
    0xc02031c0c020a081b010f200d08070203070b011a1b0106150e030703141f0c02070e04080904050702011104240302131401090f180509011a0105180901 66
    0x4845103d540003a185078020706100f03212808200d20800a842081c01c1c009282801a9410f0300c00d4210150100100c0034401c40b94181488082100c2407540110340303810b469900d980000326034074081d000300100400d04800060101e2903000202e8000111968541c40c5040e8500340c180100e1041c4080603403080e0345580e014840c00d43c9503c0201a0003c05160120120001800181c1e46412521020705513050020f00c2d0400b9a0f0144016070390548031000e1004401001c5040000070940781440d1030060007a070002043c0c0c01c03441400140502e070002011400c1c501c005003008010030002c0c0c1080d09640d6900e043c0d003000003481000e04024013052501405040f81281502000010001c001040500c10800c00d206400b1440c4100d09a5074a0941142c0307500d4000c0c01603400903140c0d0001250302080040000b0240d4202c00c4103403042d810068184441c2c0c4030300d080ca078240c03402c80f007a00b0742c0c6603048201012554807440103080f1204200060f50070a4400c030700841c0c000301007078000440100311008001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 298686151 1250 298684901 298684909
    0xd0f08041d0604051b09040e160f0303020708010203100315091401060306180807170903010603060522120e01030b0d080a02060f040c03030807050705010507080612071202010c02031c0c02 82
    0x5a01214020305c070300d00701d24003542540841c0f05041090340f04d1507803070544031044482048590070940c00810300c440056110314000000340c002d403104400510840102064049041c003d4134007a40801140302d000130b0031766031100c0d84002c2452045d14030382e507250b00c403a01291141c400c11142140440001500504504016007500c6140d291080301250000643d00011189400c4031030703140d003000250403801e482c4000c1100341c1c41146503490b031543c01c00b10040240102ca070b01280c001c0d110554005007000f0b84400c100490503001c0d02c0501050140c100c00400c03580a5031030b42160005c1454001410490b00001455070445400e055803c2c10010034880003094042001d2600a20314071854512450155250400e401445c00001c0c204200c000204112502034425140342d6607120303009016501c0d041c4401403400d08110f80280c8100807140103030360005400300c0e006091b01c480095403a0754011640040d103030344e0207202d0100e0705440358103203c1010a5980741c0d2580c980100c2c2d81e8003801140300340100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 298687401 1250 298686151 298686161
    0x804081c150e04080702090403090306090602192102090a05030a0501090611030f0c070303141e0606120c0c0705060403061505060a080402041d190c0f050d0f08041d0604 74
    0x600d0a2002d524107100c00300e000103080c0c403102d6034115060149982c072440c0403140b5018592004100c203080c108141c040041c690060140cbc080c803c1c0b031401c1c01d11a640d50480f280e90b00030f81d0010540d04007020b682800b0803650001c2003140c501130310145a071684e8070302080c5070005082e4250f980765941c4c10302104103c814090044038150040d41c05045051180c54001440303000340c82060b00c0d0b60006500800c141c000c0e04070440c00201c041d0a056145401d11180000c00175a8601f0740d200b149020014031030b442c1800946541e0b40c1a9480c06002c0e039104200b4402541c45100d020b01c0c24412844000b0710340ea2808024005184554404188045d82403808125a1105d0300400e01c210b50070b0014400d41ca90208240c0e90164045a000c41c002009009807030324109000e0342000740303014680e54010780c585c40c0c0d10024800e42c480c0d4205c1508564612101d407508589001305c0c1d500a00030307010000402e8410400110340c5014103490303032415a44900030301080080a880d40007140d088010040745c1d261034424 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 298688651 1250 298687401 298687409
    0x110303040f1a0306060a0302070501090c09020a0807050f040314030c12040806090703110d112d18010501080703060b16110904020a2606070206190b060702010804081c15 74
    0x3101d4111304100d400510356020b0148194200741d030120318202808025001025441c6e04452503081c1680c0b0781460720040e5103c1e10300c103004200f4510100b0b200301d2145c0101c0c1c0c0b480a031206034a05007400c40c0d9131180c00050310014600180720a2101000a0341d051226144001c0d800c4040b80d41e50749008606800c01d00000e100e003400e0381085000300042018041007000410b4101c510000c041120324040d4550001c0c2d02556070000c2403101030780003a1840c680c03200b081d55804e00361406101458000c0203181c00c20150510510040c050040100d94000c1c09003580001950070701013001c2e40c51700340c03c135816080703401c0d60712154100e61701d04000e10140e404505c080f800c0546507840645060b4003c0b403059001407148200c0c5641307030b849003040c040c5403407420500e0961150523540079080070b0400075610402980d0215200e1018020400000c0041c41600070000c1c01078102814000250015a64044c000344140d40500c0c040100c1414160742600207410501c201c2d000194040b00e016104001d1001500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 298689901 1250 298688651 298688699
    0xd17093f030c03030a420f0503070b16050625050a0206010b09040e0f0105150d03090603021305041b120e030f090a0509010627030b0a0504110303040f 66
    0x2020810300c01100b00c0303600600888011403000d10942d069404200001d81c0581c5c0120b10003070b96100080d8400c2e189402e40c06c102d010301041070303d411910034101c90620441d0b034503502c18035040011114040241405040001000e0300c03091035510b0b0142080f034111040070f10100540a00440c030311118800010040e5603240060514100c0e1402956070b5006001d4400307080000701d13030381a080d6140d4020710743c50300503c000c0c0c81c0b0700010080d41c18003811081e600044091409221410ba60800c2900d014490b5059510030701c0c080e1526100f42c0c02903000f120711401a242c002c0c40030601340c03030346d01450600910040c190343c41c02104c0c40c03008208441d001d2120000c1801c0103200206401c001069441070f40c48403040c0d69481038071200041007164694011a00150864000100d00c0c0e00102c12464400d60644c880c00e10000c4109022607004441c0001007048024101184031404594085580140304150640c07040300c1c010006442d41c0c02c2030307114400002c0000b500780200c456004a036490445605 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 298691151 1250 298689901 298689907
    0x20306010807030510231f020d0e01180806040215030601020a1b030614010602070801270c03170d0f05091203150405010909060b0d17093f03 62
    0x1000082505001504150403d41c5407400710b030ba60a101c0283c0360040a414001c03100c0c1e2880030924990b0500b556003e03e202d100071140c4001e003484244030402a013249607025044000d0b42e00401d0f44c0008010743d06504000a888556589001982958018191040084c10545440c0c0304121400b0040950044010400c1c0144040c9076000036030303188000e0b0b10a20f005d0401c2034061144a80c0052544090921030811002d0206000301c0001d243c1651081d9003603401041d00d410031182603603440c0d012022900c03036105039a003080d00b09078001c040161094902c0c40e5140e43d00c2d21001511035144a00e81d050910014403c45203840030310611031303a1100d604051115180c07030848a40c94a080030b07801e001080d070010001d60503900141a60380b607070130000c20421040d61201070120090400d0b030b0044031014030705250030100b4031b030070b0002d600300d29402208400401100030807044d0b1908481049a0040b00d14104221504110b0003c0346207415440c074040d0480140350740e000b42d9040001802c00d1907810030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 298692401 1250 298691151 298691161
    0xf140109030c0603020706140709031a010e060904050a1202012f0f07030c0b01030804032307030201050f070b010306090b0606070f020103150e0720070b390715030203 73
    0xe0302c0310032100b49080040e240e071a18140100908903003000002811180c2042101482c0c01c8030608013940d024240c000c4240300c01d0680c16450b054203015646160080c5070000d0081d1504d41146507105100c0c10507107001780c58239511540320810000d51880941d44500c00800c840850000d212501c1d8200c0c1059039104880845c01805840703082e400c1c0441010000d05a4113140c02f940702810029403240c40d0745800c0d80e4a0600741d145030400d0200715811400351300440f480b4035041d50800c2881c503012019090302e034034650041d43c01da0b001c003060307403286042440b0240100d6440002c4d01c1c02580192000f1800c01294508002451002000640b08480510001020030300740081140c1c1c00b40e0a00300040c644c40301c0c0700c0c004160180f40c1d2100410015000811403516400b40c4401021118006910b072130b4880c03203080680321511405945149081070041540500c0301c4010110b949108505100c1208804200a5000b203035000021560360300c2500d04204061040c402090b240885140c11400d44c240 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 298693651 1250 298692401 298692413
    0x90c020304030f020d03050702030f0304081e06070806120d020102070c051f050d0212010803130602010608151b0714060703050601050702120c04021305040e0304030201020703031211040f14010903 86
    0x100d0f4002038081c40ba100b03211401c0501660072509895001011240300e0303100d014100d035881d84130303019803210340c024001c60003c459000d080e803001403c045400303000355036100304084440c140000c0c1407a51002060320390027070b9944140b0180070890300650000d039850304a0b00f007051104180707038000c40c02181c0d40000b8030f81503132400306d03020300426003482d01503a110740408084019001c0c48150220b90780c1c0c980d00016130f09800100a29184000d9a44107000030343d5003000303908803212031168020340d8200f10f01030007100300c050000f9980a41c201c103c0c1d03a0310440e1905180016080103000b15101c0d0f10409250520700410030466522120380d14051050b072410b44002021800340080090140d440702c0080b44080c5070511440d2400711000d0070842d22040c005512450880d80b500c6060b004030300e840800c14800d1004400c85041d04e030180c004112052866030111201c4505c42600030243c0d9a549640c11081c4060b0300810041c0300310b040d102c03420f031b040c2500c401c1c000d1140181c19041c440180d0040000802c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 298694901 1250 298693651 298693673
    0x120a0f0e0a2105070906060e13090b01051201020706060608060909010216150b04050f06040b0303030108150402010c050a0308151012021c020309030307090e0708040605061503040507090c02030403 86
    0xc203031082e4410031891924901d0824070350040c1517000d05015011800d6503102c001e4021009040b182d4117240d800110001c42100c82128000d00380290500041c0034a04000c1c1e44016681c00f120001442c003502529440115030480e0080000241e0710001e2210a1401c911444e8105602a0013146020030f0380307a00e60503290710740768001c0030640901c03003005e402d6000c0d46c080001548007030000e02080ca0600368405c20701c4c030304603100c6100398508040842c10303003000000d0728180c0301d00100a2046080714540d01d01880402003040741040320650701817002400500110b10418071a44600000b07003041a2408409240c0281c601c2c02015210091588642d0200c1d00e100c40c00915400140e40d6092000c0501c483c03c402c8003414225400001405003294001008520035003507951501c801b6912080000c015200540d5900009044040401c0c04905183e00c5950400c00042c107202200309480c00c1a030281c2c0084600b84c1d25500407280400810b0124041e8a0072510184003441c68a070540d0340f16980c1d01 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 298696151 1250 298694901 298694939
    0xe1503060108370617011506020d0207051c0c0b09030106050906010e04050c1909030b1605070816060903020f01050601080613020c01111204053903120a0f0e0a 70
    0xc40503182c14820f92500b0b41c00000903000503a96070b030074464a45101e80c0a840c120010600312180e040b00021020b1003c241501c000569a0150050318904420022031208001b212003c010034607601d83e001404500c2001d0003480c41000ea01c0e11411305600f01421107820f07034041802520305104022140c2e9001d401c00b185641d0403030f000136603915209845040e0340a10707498400840400d42c9000311080c0c10024500c02c681c13160042d014103540f0084030808400e007540000010500c01d00462340041c00840103800d40a01b9500ca55802c3c03c0c01d070300d6107400d07200b8541c001d0303025030401000c1464541080c054281d1120081c20900f000341400d2003c00c498810800203503540c540d011403141905507003900701030155441e1001403901c0340c00c440607136908442c0a079000c4030b95115462001c80c041c00c00300d9690707008410070201042c041000b81217050f16005e82c0c06503540e250268201d9000c0544029001d004041800d030345048030304640c4507029001c059a005000c0c801c07402c50400300501007002c96100c3c01c40e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 298697401 1250 298696151 298696231
    0xb0903040501050f0c01090204482001050a1b03110d090c030203030a17012309060102010b1e0103060503010203271e010b010806012606010e1503060108 67
    0x245c0a0115014010440702000030762150400700b2021b4020b10913840c004d066805a140160f111018581d90a4641e942111745e2888505180c0100c5e280390041c0507003e655000130343c045140c1e58183d000303142118021a0240ba00303079615900005101e402c001c903a5965805803e080065514070b149040f8180622804000306030b031120364003020046116000c4c40290340c00340c00c690300d94820070701c05031040f0007200241469424020001421800e12109001005001c0b00000c01c4028143c0901080f018001c12060540d9284c00321b07420320b611002200703420010180c0b145400540e00000040580da12a8009403091380140b080c030038411000ca0250341c0c1c0c3c81810b002003841010307405195007800302031840c03082d0702500941c0070801504190014840000c00b603840007555034412005640700c82c8401d0065400404800005404842500f866500140141000900c410100000411010341d28008400d911030100621129513000b56115410100c0d0344020044124640340260a10780710b49201456 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 298698651 1250 298697401 298697407
    0xb1e09090c1b010207110907020a110103090c050603040c03051c0503010b180306100806220311010f0905011a0603040503070f020d0b0f0702150c0a031509050f01030b0903040501050f 80
    0x8040c0b0754120200d454807911000399100d00103400c0c480001049180c0171801640100c00054145201266004809a00080c59803645880100450091488450803a0174001c11000803031555140320140d0b00c540e1194843d40d00711815403030520b0a11860301d10a42410710362240480100f5044815241540e14070f100d0b50791034003001001d84184018424011b5018001d0800388242c00e04044411025078034000129162a11020f1404a16514400303441c41c1c6540e148103207000080c0309515002504000390004940003a4141040e800c41e02c0c214400c4030107a40d1020300c1d09680e412138000c0d0100d21402c0784c686007503251688a03941c9134480c044000340803042c1c4c1d4001000315900e1302200b417403d542109500c4240d02d0103106030b9420590503129800076103e42130780b00140462400301c0b60301c01c0c9036103540300e0b0415200300030035400382608203100301956420810100c0c3d02250740c8505440b611000140104551440c14551401d95010b49100f180340c004001c14051030342c1001c111100030300c50f94182c0350307 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 298699901 1250 298698651 298698667
    0xe1f0b0c0c13060e130c0b03060d03050c1203091b0901050a060819050103080304050c03060601050a1404033002070f05010f120c020d022808031306060b1e09090c 71
    0x40102800c0e0846071098242c54140a0500350080c0141d17041803241c041d030303d00140c49a01200d8580421600c0d5503104462000c0d440c0040d02c118040c02e150b000e65012100348034154046001c441d0002c8541c074450340e1008154021640700d00c40803201c00310042d0b9a941d1154148004123080d854503001c2e8078140f02d82100071441a5020210101c250761105c00b080107196100e10b0b000711182e00986007a500380c4030f03034585250607190201c0c8090040c041610340c14548810040c1c290342210307030a9030060300a401444000081000f00ba1000c2c000024451042d040b00700c0710220440e8880b99900d4a0304551141d58288041c21102d0350400070303a44e0908180a100c990214110750541c2c2440508071510f0411030490402d640000300c8010f46c3ca03e640a8074480745107024199043c01000d059033003840500b80c90040491600c42c01035420841a0020b00401e80c4107032a0301054820075840000c12a50000b0320300080405240c4103001c05d860120381603d031240e0540060300d480c0c3e029003405982540061200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 298701151 1250 298699901 298699939
    0x70f08010b09042004120b1e040b09100203130b0c040305030406030b060d0c0207030c060507020603010302040c0c1209030b0a0509100c02160b09130507080f04020303040e1f0b0c0c 79
    0x7503000668904136aa443d1603410220b00c1114840c4112124489180891122440350410700c0340480c00d0b400004d110750380e03501d4403200c020b40a07203030028a0081c1301106c030108080c0c5c001544103110080b00b0071950031051402d080745800c010250381c44080b0500c020705c00504048102c030200c1e5050b1a02042180d41140098003034402c07400c6100000f0301d0003010584003a00460250103d9004010380c1c002d250f6900c901762014441d40364000c1d40700c4810001440140b400e40d014503003020143c9800c2d10087e641d5035401c424400103580903804140e4900041080119104595510045054040c0a14200a82c5131540d80b00d807180d03101701c0a0b40740d41c41315214030320810900c07a80060702d0181c0ea10007942c0c2d0a0301c2040ea4070800380d0746d0041c4003895070340c181d1a0382d9015a50260305c0303aa0f40c0c035509580710070014281c054003410490745030000b08400121000d180440d80e00400152841ea072001c0a142e9451340725050540c030040b110f05042c48000d82105020400031500310060b03a400c0c1e842030700c14440c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 298702401 1250 298701151 298701191
    0x30201020d0e0f061c0507020d020706030e071d10051903060c0e040f06081009110616060c05030f07020708061302040608071202030f03070503040b0904020d14070f08010b0904 77
    0x544d80020f8042211424200b4600602600000c603420400140d00e4070807080743c5505d8907058801c00740c0c0c0f010004000c2c0c107110b9442110110070f003e003031340c01550b202e20901c003066400300b0070340072001141400e00c0941c003c251070300b200a2600b1200080b032072515210f0440c01c05840d00c0050221541e0f9042c0c020300b1030088800510713400c40240204071f9403040c6070104000385000e0040030307003d11a00b40440b0342c28074284a120313041174000403100910299441004060b41c000300800803400021200d600c00211315001c0c400b1448074a444484e240d152220402015002c002c110008540c890001003003040c4c00847c405401c40b080c40003c460000140c00800e0180416910020f464854070400103800e40c066003110440c3e40c8200d041d0b0308400c2c510322150740d59010b035040162860b0402c010800007100381400400c641382e0040e20160030300c04003600f50411034044103510182900000c0030028160341c03110000c041c2c1c80b914149982c0a5043c030000b10102c0c001e44070454001e966401001d01041c2e50308440d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 298703651 1250 298702401 298702429
    0x1e010603020301060914060c1c1b050604060c02030706092f0a05100201140406051008030c0615010318030801061206030b040b0709032112061404090305160b150901030201020d0e 78
    0x8940d40c5289c1107034039040d01c0320310082c4c2900007010103c1201480c6103002c401040e054110004100640703a07900ea820041010596140940c4010040440052041d01502415501900e40540007101079078550200c07aa441c07802140101031040607a1165980d1803c40003501c2d41030f200000a250454016401001c8070140035400415540400040100c4c60b04410304c40d003c400e80070603a82d580c4544150340c0b8002c3c1120268550010400150405038880c01074482e00c00514000c2191395215040d034080c0241c0f4041a00013405030001800100c0c0c104042c5004029100d500300309592458650045189001d007004008612210101e03850a21a071448005540c02c200e2280390181c0c0f00484020345042104620f01040581c04070940740380c0c161255030120b5400300300313002407640030300c003003000403c0407000480030702009115041c000354112808203502403141201c4091818020698580d404111008500c0764555200600040c0d074082080e052ba0b40710f60805101c00c14046001072085580000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 298704901 1250 298703651 298703653
    0x2b0204020d021b01060801020c1009050a06090305090103050105060c12030a0905030c0a060c0203120408090a0b130609050a03020d020d051c03021206040527151e010603020301060914060c 82
    0x120f42e440101402c807010905446240204040c030b45c2d5034842405c1c0c0c024894400001d802c0144a19110030781d68200002c0588503500756103036940c1c01d559040c11503013040010341c0010004180e01b140c0e0b582622034107000d080b007117500d5400c268075088410b944800804008844e15404804a10110000d8000e00261a8000107494440e80a0519281e94009400054403414108881741380d84900110417a0212213061280070120b5503075031101c4030b0685c8204405034010f6620030780002d400b0001c80c040d108010850400200c01460210010046031298000c61b2284000f1001000103942e64410501e0781036040e100304040b218942001030a1100c2c205984442c0c0c40d480502d40213440d8140d000f019048500c280c06150780d2a24010701c002c0752000c4031b0300f51006900300240c81c0d0803500701d045020300079294800c0390002018081042846c445c1500e600300340142c98032003540e24000c03400a82d80501024074046096601d04000108608514030814110010010a4020944442048a020441440c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 298706151 1250 298704901 298704907
    0x318030c1504090c0e0d030c1e020907031a0a090605030c061206190801111b01090309061805030f0303010302100f05041802070209040b091908030f09010605101d2b0204020d02 77
    0x2c113000c2d081c000c05223011206100094004207906404001c200b43c11031b0080d00701c08250740d1b0b000c4103030001c10b940501c0900e500d0070304416400c00d03a51440484c001c1c243c03424020403950700c0c001c01c0c14a06074410010074441e042c00d0000c0f40b0400480c81920b588010300300c5004561110030707403015003284030f203801002ca1542401003c0c103031400400020305a5203201c081c044060554102c00718200c907070342000100060329180c801c02160f4840c0394003500120b031300703000d074405540c3e1a8002440d1411104081001344c00100041056182200001040740441d060242003c0d1960030000c1c4079102e02c2c080c40c01c0040341214101d80d86038855056501d41c0341d0141000c4180d09243c02e185414400440300d21701580314800320f45520004031292a802141d00004541c1981c440600d171642c0c1c800c004003140d00643d0b85510000e000d658800d036a1184154a450341549001e590b402c04581100c022184c90082d00302d1900c050f002c4174210a15803004100241408100180d48001400f911444d0f01d900d41c0c180c004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 298707401 1250 298706151 298706153
    0x40b1c02010905151315050a030b1c050a060b03010203060901030803280f0b010e010f030203040204110412110d0b13050c0a060906030609140609070306080318030c1504090c0e0d 78
    0xa00700900c050305c0080c4102ca1819a940c1e400e40307000304605c4d81000003840034404c504400303001c0e41041c0c0300441c004292030700c03040f40c90030045600f030110035081c0e981da40a4000002802400d00c039503002c2c404160025841d500d801c502003407820708188401000c0400000014a6050088546680041c00c05030724641030b0b00211580c4000c3e00c00d4866890699181074150341996000f000d00d545241380c181c49a4500e40021401500290001803050303030841d4641220503005d1800703034002e2001d065020b60310b0b0080b000c50300b081812104000380c802d000311900c0402c07102041150080b03070744c070101c8212404128003041c81c10a0030a07001d040703501d0b0080c00c50701002c01e0181d0804070000c00e0350203039a010881982d80303448403401d540700e0300702e02c54a40c8004008190300713003411904654422843d007004202c4954810200d40b4561000c107046801000880b40402c161805024080740d950b01100d0310f0041e000c1d190742c3e6210718400c40c030078008082e55448030051024000e07039900ca40030800a00c002500045 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 298708651 1250 298707401 298707439
    0x70c050d030b0909011413110a0b03041403071e050a0605010e1801061401050903150a06030c0501050c1f150e010911040f051c02120c040506040b1c02010905 69
    0x800e660921480182d400101c4c2d442c8144100d041480d510000b40b5403a40b1100c0480c0b40c00350001109071040c3c051225a10340c10f445864401000300711810410f42c1d28a41400d000c600c003009149001e01a4004010078000314600310702c41156103c0100d91120700b445545003d625000750400018102420321000040040028001520840a6600481c05e603151090f21501302d0341580603246051083c040441c400354841c0000d420480d101508951843d00c0c030354200221060225004940c16803140c03420f00c10000c81c00c400d03400800003030a1840c1000c5114841d030b40c81d4508898007050008a45074840b8070f40c000c0c0e8200050f0710100390b494094050311075002c405c1d40103090198056107070a090085040c088072000301e90440e1140303030070440b9a90910341002024500c8980c090307c92104102c8000259840600910546904100810755900c4503c140010389100502961040d480d00c1c505003019100d00c0480510220281c400420022807440141c0b0001c6098002c070342c11100d0541c1c000c0d11115 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 298709901 1250 298708651 298708661
    0x2090f0d0507060323010b03100314010603051603030c030e030102090d23070312110715050a0f0212120907030803040b0103051c0504061209080a05041805100608070c050d03 76
    0x2a0f00c3d41c0c1070218203440c481584002028400e544500545240104008039908010390740254154150342d40f070035a01d0b110302a62400190516200740d550740380030401c2010030003001410305c0864580c07c0c00faa1071610003411310502c001e40541072140c01e0303582400d6540d007903040f1030840100801c0b0031881c41c92410004428001039020703c8000f20141e049100c1601f001a00da0110781c1c2c001c2141c43d040c81c20a0003258584c40d1228040c0d640c0c420b942000c140070928541c0031000401c5641c41940360080c0c808000c015880d111034220540d080b0312a841d240e051780c201207030321224240c07490345050f07214400020314200803a8005419000301005000401485d1105181205d008034110b9117803070a02070900580b00e0702403d403440401c00400c010405940141c29814210410f18030010f0701c1401c5c1d84030500750b40e00c000f40030400500009010300159115a02440d04145000c400300610301e0004a21142c60b03081e80200c006220180002030707000e42c0f1032505401d4255000d41903444200d0340c2000036010382 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 298711151 1250 298709901 298709909
    0x70b030720060609010b0c07080d171602030f1b0312060a0b0a0507021c1a180f0706080613060902070605011203120b0f0604030812091204030602090f0d0507 69
    0xc0d10003a001c40c94000910301e80503d00c01014024543d20301401e81c4060340c0404021400c80c001e42e03c00094081052002001c04009500c030080c0002e800503004e0300001d00104047c44e07007080d00c062140040e5000061340c1d1403005c044182c1c0c0d513034030a480b80b50100c12680c06114600d44400036491504209410005001e10000d44910801c0303901c8201404080c0510b038034580000d14107004200141c902924040c03d0800814020448185903032144030071800c9150a12008030300e60b0b4140410089001120300041091030058400c0241080e451911080f5601c54001080342840101e82559241703119584818410841042200e42d40e0350390401035041b200050302d00901d0040002010000c148420700010341c166a0310401c0940e0034400001080032110303158000f003002011491a0701e4a00c010000345001d2502142c440004036658142c22000400030300342604100b80c000b083c0b0250100b900c0c15294420340140e03c80e4003c0700850100f045c403070100da038440021032038001409004140070701a9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 298712401 1250 298711151 298711187
    0x30c0a020d080f0705090a080f0d0f03060501140a051902010f0f02251e030203030603010b420706051504060f06030905010b0424060206040b01051002070b0307 70
    0x302881c6400c0c0e0b0180d0341210000c0900e003903040003807003c03440381006210301c940060a41c448035032513555030f0789031000701003034441640e11100c111041903412119000404007245001d0207200c2c101000241f009900d0032844000c04e0000c9041d980c400d000b48140c40c46c075001c0c3d8003402a2aa00188000d0103010820080c0c001d0a280001e039002d200928000c4400751211200c484411170b00351421100d0020034200c041c0d800a0b6000048001c128101140b01000e5000c1d5005580b00e040c81810075084452240f0309a00c204916400d40e01d401c0b50440b13212103481140062008003802404180407044c1894038031140300342e400122501001542d500c6076024420503102484035114201c203000c103c8200b8042c842250000c54020860b03944139401001003944500004100e41c1c40c218085000c1d06e01e0060b09940003030b000f14004c41038065607001500182600d10050545c1d081a813609082e0b80750600420380509038201c01000c107039000300440c070300604254940546c0ea203004c21009090742ca240e5001c0e094 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 298713651 1250 298712401 298712413
    0x3050a0b0d080a23070f030c0602040b04030b01051e01080709081f18080d15090203090f0f0c060301211b060905040e2e05090601032f01120e03030c0a02 67
    0x140c19100d0b01c4290301400c1201340c41c0b03032034281e0312000e40350000305404804211980c214840062401d0024000800c00220000e03212401d500c0c20010344003050704500c1c0603801b2107502c1001c40c101050141d900440a0904041544454034100c503100920742000e1810322400c00e80d60810043d8000580121901c1902003126001401500b4010744c2c080030080d228100610054401076010740c01112502d40846554030404c1e9a640c0c100140d810448104480390005401e084007102c0c01c0c000150b441c0032160142000c04030703110000c0c52600040c00350142040744020006000d040d08150018100d801c0310103e090050300c42c1e0f9881c0710009600481c8000b9201c624000b0b82d82c2841d005401e80482900068608021103106000e002404294204865141e170801622401c11500c203d6005040501c007500603076041d401c20f44044050340c43d0f52000c48603144524800038030f0703980010310800d00928056007081c070b042009a0103024020b502c076140c0e02000050050140080000b07000072103940e001d81d09 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 298714901 1250 298713651 298713677
    0xe1819060501031506030e070905040c1a030f0c0f040305011e0c1b140a02130b040507110a06092120030a05040902070201020102210a0501080313030303050a0b0d080a 73
    0x200780c8034000401080c00d13614050920200d80260040c2401d034100c8030860b02241c3c0c1d81c034520001e44000340c0d0159890141180180007400100b200d40f803241d808118642d1443c01c0c81c03007520000450092400600400110b8506042c000c1141100c00440e007100086c0700e85c13a0340d00012100804001184030034203140044a0365242c0c007070546505a490000e1070b0b00708501c0307e5141e0050340300390300d407820f561401507201c40340041e510180c8221041540402c0001e4040a000034841202c101400280a1040340c064100c2e001c3c01c0010f01c01c2146074410000300d04980a4034103400480501e104800710b1244c00302c100542c2e141d00a5a03056000610700740580c6048030104415241c0c85201100b500040701040140702c405002e0300103180c0640b06200041ca0b25803541541c45503400b46400d030050110058081c00300000c481d020781405002d4032000f452402c5000f0303034210780340e614922004060603114400240d0071165580481a08040500052940d45552800074180d5103e008040d0216040c848004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 298716151 1250 298714901 298714907
    0xf0606090b0d02090f0d0305030f0903070f02100903060501140f0409210c0605010311040c09050603160e120304031a150909030c0f07060906021c0e1819060501 70
    0x4421251868481c03440c12864000c1400a036110340352094000c25a203081d5045500d40e00c114a01c10342c0a662460788901703042111580154015105c6a000e910038041e4201180e075040c00c485041d90304544d0b83e1081c3c0c0081800381c81844242c5d00242c40980b42100026041c400d0007448000d124040b01c5991040030104100300440e4042c1c44043d1103200880442a01011045034003039800810b41070101c50900c0941c0e4020983e03009800c103c4040030800901005800d15020302523100070035040c11016103040a0100c3c0d0140070082c0280c800b0316000002c0c0300d1303041c014140a0761540c000352104000701780c403050781e41d544e130310501c4101c41003801c0c920036500410030072480e40d00072001b200030302600425030320421450040107400d002c0b140c0800c11114043c28020071040e1008401c0f9000390038490b00d4504054080050b907484030095402c1101d619070140304401103600d1a5640d030070a4003600c5000c6012034185490010940485d210380020b000b00b0020590310603e03009007500c0c0610000d901c0310011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 298717401 1250 298716151 298716167
    0x405010b030723090403050c0d1805030a240b1503040201140304050307110f042f0a02071701090b04030207031b03051e010213061809060806070c020d080d0f0606 71
    0x1121060b0403042008000e494134000ca40c3d0864003e00d0721906002c00b0f8940c2e241414807104010340480d0320f00400110b0900c4150000c001004110f001c0c2508502c55200c14000740714400b04031140d8000130407810101c100562003445480c001400704d4103c0003005c4c2e03107480b042c3e1080e02d0a03404100c1e84010025003881840850784540c1d0b014002d1410a08583e60340821a00703035001341d41e88800d5006500a40b5111449013148000c40c1c3c0044010b50f0b81c2101e860700c0d80821148a03014800c030100107095010742c000a10b03004a854a20072507028502c060011030050221000050000580200f40014942d0008501098030300403000e0f4100082c1c3d003645124504950700c001410341c2c11004070300c0040c02d841c50260341c562070300c1c1e4000352500b58500c0d01ca402456041c2c0210020030007036001e0000074a21104400d02030542c50304200990f50500d80b69554858001340030404004800350147d04646a43c00301c41a101c0d80000c202d41c583e415581c2c10000390540000440003a8504000003801c00c0c4540e01d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 298718651 1250 298717401 298717439
    0x418080421020a03080d0b04022205010f0905091005100801060f051216110102040801020c0105060301020903120703020f0303071d100801050103150e01030b040201020d02060115080a140405010b0307 87
    0x2c010f0030070300e50b5545d80900c0d00000001300c0e86990340c6a04001980b642c0c00148503c0c11080d0500d0501c0101c1042a4102000340d080981006048048503459540002c110015200c0813100d44079203139134852101d003107295580c11241e04060a4007000b02ca55401015541c180c4e85203440f00c4c184c03201c0e5294203d50702d000b5010700b41e8104c101080480c4c903240288103a21140300c0701d0310300301c00701041410f511426a4010361280d821a0750001c4d01d51031804c0f007807007400e8005208400035854010010b0000f60740d4074004840b103401d0900056160200f5000300114101c003100c0c1c200b40c9480e4603100c4c40c040d11982d00126640040e10300aa0141c40c50301d00180e448103070100c5a15a07100503402d11004500030107400c3d00d0801d0765420088003044045512202c07500a5120301c129406500c0c19100085c101020112203c0035940107030011701a900c040305121010740030b14980702e00f150391400d0040000d03203201c4004000400c1408244824082c0640200c0c00e13113017003a01140e1182d5a20070b1050700980c09010303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 298719901 1250 298718651 298718659
    0x702060103080a030b03010c020309040f0605030c150c0604030e10020f1b011412100b0f03011a04030f0c03030f09180207060e15040b060d020618041808042102 70
    0x41c4002440721000d41240788942c03800180500040c5c010a086640c1c400140016a2000c64290303003901e81401030305000020b00300e080c0f00c1d442c80c00340440e07500d10100304028455040000d060040e2240c4000b0340784808908400c039149401c10f400c0c00344c58040d0040c0c65900408880b41003440d20341c000100403a040550744001d002000500c2400d98100c2c0c5400c00c02410410030301c01c80600c40c0029030140442d01081c0c21007030518141034901d030b14946000e9010f00c00e125424001f00602d040c0d180c0943e411507110f080038410b4407000e880d800304144130b07540000f81114401f005450034441d07a0500310080d2442a1100c080311604501c0554580c10544038054a02d400314980003800c160a03009804442d01c00c1002260b1074050003245414104a040aa98403000280070031050029240c036003500482c003038520301041030703903900894507510a00030301411000014074150260344440c1d10080508025241c2c4680600b0a460449a6a4040d114081c2e10301d02d000d100410210104154a01c4154018 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 298721151 1250 298719901 298719913
    0x5040b07360b07060b0307050117011a130605090f0307050a1703131509060c110d0f021e0906040b03061f090f0603141f0b03030403080a0e01080f0702 66
    0x6030500c1219a00d140e2800140c0c00607440000c1d041e41d540c010b8034166103d90340101e0450085800d141c54980154440c904001c0e01d00141c01c4028428504103041d103c0075030000c00c00c0d40c41c86c0c2401c01284114100da80c046e80d09034400240544d4030002800070604200c0d00081d585168200f0503580d44502e0040a40c401310060040012249040c400c00c483d511440070b5a0901046050189100035140e012400440205280700a01035000359a2406070601e0300340001071040d19119560001c5606051a000750701c4e549841041c442d031413000d810300d80c2d4020810004402442c03001984200c00354401805a01c140d0301003241d515090050002e50760025004040d503540320450303400c0c2c81010000350419070b4802100440c1c4020503010300700400c2d85e407032408588140386103890b0b4030ba0550600c105030541c02c554003000c000c15400240000d88100f40d0f0000c104041d0180010781944125400140049000202020300d00c1c0c00c200740e828440c0e0241c8580d440ca6440c05034082d05103500301c07803060060b0000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 298722401 1250 298721151 298721207
    0x30105090708040b13050f0303040c0617040503042304050a1a0307050d030c03111203100e06091b0405030601091b0f020307060c1b1b080f03190203090a030605040b07 73
    0x4884d03052205c82c0200d048400a550303248401c0c2c11640203403400e07500341180580500c809500014025540500843c0500329841c0c80c1c0c9842c0d03240d000f1401550801444a40c00382000c807560380040e580b00f44014030811403800c10300350700d42c000e11543c482614108a251242e1140c1e2030041405070844401519001c4808101c2d03800b01c58204841c3d40c110180403240d006211180c504000c00701c0c88060402c003a80e42c0b414007041c5420000590b900100925450310300700070b80b030385449070340682016031030b4022041741d081e2000d01c4006008640060390144034010002032100350542184440280c92661003100a048401c126041d1a111800201503482000304c8070008150b6400001d0080b11860050309403e4081c0e203c4513401c10991080d00c80c2c1d070202140902c91510160200001c00200b0f004040640c42d00c01980e40703a00a003804810140c02c0f00801c0c07000140203004549400308002c100182c580d84134609a03009000660302a144090105d00255105019803c0030829000c4a00c107140d0a00c09 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 298723651 1250 298722401 298722421
    0x70e0f100c0b060105120f0915390a08040614010f06080603031b06060103061401021906060509071205060603060a0504020307031116050111040b040b130302060f030105090708040b 79
    0xc060000c40c100b002c00c01c8043c3c0e100c031244d00e1a9000e001481e645111070b060401e5494a03180e1310341c0840301d2700c5840c1d2041c044e031403a90002400d801c0781c00c8261907810500c0260443c1308c00070700d800315018940001819210003540718942912035445960200802c11035a091402c192030240240089002d042e482403040364064611290300c113900804417882e01c149009001944144203d85001c183d2044044c48565a0140a000003800310909150070368008003000030740c1c4440c16210070000d03010f620685c000b80281078010070702a0502410790000d906043c90000c04108072a80342d810b850340340401081951500c0d40032240a40300c01010b80004609000400c4000c5d84060091400c0c16501c40c03102e00c0c8141500701801d8511001c1c0c1c108074141d000381c18642c1c02d540465000125441c01004180501c1c4001401d0b41c06950340701017026100d85981a0b1407040072000d4002940c080300100c0d0100300031031000000c0d030507910103484484d601c0c0c85d40100ae075203082d0280c60040c4640076003c000394140c40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 298724901 1250 298723651 298723673
    0xb0a14091834030629031b031c02070302090c0901020a06020c01020702030d090f08011e0209030f1c0306050301180303022101080309100206040b2d070e0f100c 70
    0x10122407142c1041c20300160320300a90015501c211641501e6600c108040c80031000d08a041c05074400381d490890542da000241c9541c007050321502c8000b50303881c5080d20ba80781041406012080045184400304004201a54420301813200300d200d0600c80000440b182500400e84501a0303068009040c1594943e890601941100061068039075090240c4800341c3d5041003c4a001c1d0056110102460f08103c200d130140f14242d00320300540d0317040109006000c40d5140180001c070f0010031005845090b01d02c0003070704050011008046501c900010600d00c0b0329030141c40058007419440c00c00406903510107141c2602c174089410000d0810111034080400c1c000c2c0c004114100903c5180f42454128100c0c41c61241020b82121003107a03c08030f40403080b814401c0125448001d180002d002e1880c081d42e95440655004066008480b5680c2c0c9621545002e52985845400c4208160350a403410240040018107102c801074861111402d4400082c107011100e104d01c02540e0752a83c0b403018242d126004135a03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 298726151 1250 298724901 298724953
    0x2220f0218010f1e260601020f070e150307080f150a050403020d0c031202040f081605060d0c020111070b060901050109181a03010e151b030f060102010b0a140918 71
    0x80e1030120b0120744403045d030280c0110f9042d9465189800c01100081c584102c1500070713603150307021040c148170350b10f49000750303030340c04100c11032444ca40982c03100100703040c084c00b5030001c03640740300b00a4240221540414145092840c2006103119a558110f5420035a0800c1d100500036070414848050b260f031007014103c2c0494000d0070003036100400041081c0c00c0740c3c09076000c101c1550a0030414841840f041c0103401440b40c551620f120100d0030100000d06520071150b041e0110b0b83c2d24041003081c03900039080414000b194230f0000d41c64401c40c0c140007148a030b0440b01503124151100001c10b0301d41c05001c14209503500c041482d500f410700c2804400042a0758200a242903100c03550190007507030240280e03900d02c00c40101800384000c501c029107016203000f80000c200d10340c464034174595114000043e25404024611a5101504c0302c40050303005014561003103812804038800032400d01ca0040300c0c190810300c291030601d2555529410401d11950221205a041d0005103142c3c403d0303485c2c10700b01c031000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 298727401 1250 298726151 298726157
    0x3031409031615020f070f2108030a0b0310060b031603060305030c010e0709060812030717011e06180e06130207030327050a02220f0218010f1e 63
    0xe103424525090050710b5511400d41440c04802c0c000342154180030a100899a000003010301d0b908046a9140c0e100031030140d0100a6aa981e0300440b00e0780b501089035078540c0140c4925960304000091b00c5c0604580f100050181c81500f041540580d094404c0c0c1d02200c002c2901c0e0307800c0d521190f200c410908901c001c00c0c0f0806440e0340c0d000c00802c6080c001000d00c902c4560000583c04200021581480c4055100c031b20340130f00d8000c0400090307001003854840c05450040980d502c0e9107260301a1240d04450a41c2481c9078182070003c101140c100d0414030128064030241444a0b503aa0700444004180403040310411840d00d40421074180410a2207810041c010020b21600e8a18000320040707800014081e00007a40780c2c680c54004112020750000104070080f207401585d40c094440e103035a0080604000d0150314003c802902035840800556240c2400140900404034000075040294000030301c001c0c180b0b0540d2440c009030b58042c0c40070409200064403208036002c4607101100740d980100d18545e041c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 298728651 1250 298727401 298727413
    0x2110090f0b030613120c03020304030b0c12040606030201090f030f020f060909070f030c0e0d0b06061b0303010f050612010e06030a022d010305270304080a20030303010303140903 78
    0xc5a036040c080c80d80300300580644a48400c45904001051783e00c0c45841034240700c000000e00021a902104071000e0781c0c0c02c02200b00c0b49842d01c9520384500c2c03140c1c107000540b03036004c04180010000c0c01d4000c80100c074001d0f42d40c414115240d0300131503181219440f0050829860125010042c03c1c68083c0001d1000020030385410020715602041900754212404800100c02d000c820424507018802c1e03d40c0da25807480c080c07280d40d00c40004206661803c0501501181001001611030b13620903080725020303010000c91400110031307007081550742d40081c0900700765510440004551400c1c000300b0b8450311a450000380420b0f034a07000002148100150016815000d007858070030260b154218488420446003820440da501c5d011a03100b824581100762504050a04080c80302038440c0c0360200c00514441c0c03c42d0010f07441c480407640d156204035070045c0300a019800b43c40381440b1408010942d5082d4020340a001101e24204054591000340030040120349181080690071105c0c00190629110180480304 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 298729901 1250 298728651 298728671
    0xb04020c0d09030c0b0f0306240c0d080c09010c020603040303020f071a070c080a180314010c0f0201140f0a0e010905010c110a020a060806060f030703022110090f 71
    0x42007001e040e00700004500203000401c100201d0181041c01401c54403075880c01c1c00ea0108514040f84805010b1911500c8501010f161110b01260315072400d603450000c42d55200d2441101940b101c00300003520001c00c80c0000010003259850044130114003050f07650aa1980b155420032285401c00b4000f6400c0540c00e01502038148280e00041c81341c58007550951441c0e03024030039030712503a1800030502010403208400402c000350040080e190386140505041700e0b4566490080d014890f103079800074021401c94a00000e4828041d0b0080301c059003681c3c0c44025107c0340300c0069080c0c0d25800f46030038440c0000c00008030380745048040250460407150f00481d0385803c08200c0c0d4255844d00d1415500c41e5590321015508507044524803c07042800406820940015000208900054412601031105c4117000400f9542c0383c504445005040d00c0404c1d84904050340c0040c000d4011100600c8100c86003001201000080400d00d4443d21401c2e06845841d400c24a074600a0860302816030081900ca2841c49 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 298731151 1250 298729901 298729903
    0x3041e0f0803073318060213060e120604150204030f050f0610081209120a06050f070804051f020903030414191d0702070906080f060a0501060e040b04020c 68
    0x2034024a8024021502e5602c1030404800860102444070034181c41c0001040d1101c1c400d030040c04071041e00c1c1c0342c0003464200b07128038082103580070007000f40200d20001d40c1011003041c02c07136024160380040d916198180204010303c25130340c0e00040c440b0400d900c40400100041c819a452101044000301702504042c0e9075a18400140406a400c843c26085000c810306c40c00002c0000e5544580404180050300d450300c5151901c5038180c0315550400700c1c0c0010000ca0700c1c0c0302c0c0141d101e03c0c0c0060608840090b0243e0510b079001f0102603440c0c000344401d030004181301c075100343ca0980c001c503001409026135071003210301c0058000080112404003a000d2115130810340d400d20107800140042d0740c22054041d8100100b01d0864078142805660b0300c20581d06206044c8138011883c0d28101c1510b5528083d110000140e140580540c402440c0c0350504001161300ea03030100300b01c0c0f080340b00c40c411100141c42d4940300313405507803090044800040c01f4840c400300707510702508000074010b00588010f290500a1aa803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 298732401 1250 298731151 298731179
    0x304051504060c020609070f031b0e0f010f050f13150902270a0f12260d05160e061b060702010603170703120207110d0303051608040503041e 62
    0x30b986450b81d41c000c0c0200d85405000103030b40036103500080c01d801400c1081480842d070f024003029000a1010421004440d03508142d0b001400f01e0003d404d807149801220346010a6007401103111080e20240002030703604124850580140004040000a590030019000204030b070401c984d0031840903040008061003148001c0c400044d0758512001c4c0d01e410703580f0407010b00d80d0216403030f4020b090b0f0348420804145440d2190059601c610600d011350441424080c07410703c418112011100c480b0100c403140c590080000b41400d04070342000340b255a5032150440090415030b850400891a00ca40051103403030f0660041c40b404400340e106800c00703c05581c0180c0342c0f00e0704403843c0001d130790b644000780181300010400c40c081103008000c082c5400203d5400815005001e44299003030303034021038284108003031607149026036400074004020340001410010050181070f038003100a8107440c2c10030824a803140404074800e54000d4000c0d0701d007030314101c51819101244000340d8450815071202241c0d00b9042c1043d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 298733651 1250 298732401 298732403
    0x504051f02070c03082d210c04030b13050f0610092a0201150314070e01181a04020304110f04060f1205070806071223070c05030f07030503041704080307080304051504 73
    0x1b600307881e0340030b14130940482121a0500e96090010030208a0461001700884083d00c0e880300714168544c82e500f10950110508280003000350181c1e10501016490025455100f0310f046036035021095501d4108000722034a86495050140d03c21440505994130b010f01d46050302c00e00d2000040c043c2d116040c01c201d4003003c0e04111092654085600d40c140010051b4034081c03c0344019580702d551402c03c44030410b544804035014216150061020010484d0f298a00c0b00c20010b041595285450700d050300b081600c6140c078510588080c81d000c00e41d800c0920030036041d901e08070085400c4904014083c00c074405650801c48540c030030481c002c40e18140a201c0380340285d050f40c4440c003040f4040c12034a0203660051001c070080000c2044070000304880d050b0b2043d0001000c2c10042510f00c6241403072411031103029400a0710080001c2c0f01402c041e400f800441c85540107003150100d0750b0040720086124402e030304c030313284940d8000d00058001c10840402150494461003c98805144515142c04a2281250 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 298734901 1250 298733651 298733737
    0x30c1e0507091113090c05070b090d0f020f0a021c0f200409020109140a0e0c04060207090912050f070b0109091b08060106050c0106090504051f02070c0308 68
    0x103010002e4405a024181202d441c2d65003590034a0014100384000d4540c922512140380c0e1501c0712000158064403c40301c080e0341080c0c03210020314008402d02d07a1552002c04810004010f14005455a880484c01e242000c100341d0292003403941c15001c1100401444603007007000040e28174100c001a410072004a140351050a207a60f0a262a00092510b0b2a1225402d0700a40c20300f150140180c2e40114100140c0700079400414280002d10301141300800f80b50007040d02380d00c18005203e030440610b4081c000302e03030881c2d00700e401c582c3d155103000742a40c0020000074460918843c0d0141002e000d5005842290001030400b0b0600c596515100758000d003ea100c000401c2e0380e032000c5814080031002406001c401562080c101c1361034411000e544650510503103007000400b1565841601003900304800820710342c0310520160916080c010346811628858500920055103003c9142460b8020b40c2d8140d900852211056481d50b15081042e40c440c4a5091500440d5078150201100d00405030f964695110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 298736151 1250 298734901 298734913
    0x10306180b01170f04021201020702130614012a05151003021c0f110a081b010315060903020f01141b0105060a050d0204020a0309020d060f110f07030c1e05 68
    0x81c002414103a0090303090075065074071034100500031484134521a0455815202c000c181e03085a4080340c021b00401c0c1000350b01c40c40c054031400c020803803600004141c42c184420904841c401c440195041440c040030404200700c00d100c1c0748150b00d400c0000300115402142a42c2c0c03001c914540c1a041c08c081101c0d4001016006901401075080c02c230b0105001c0d0448c40101c41c17a8420940300c241c000a290400184601c00300c03c8580a41e03100d40c234094004003440e600b00c03014004d00e01011920100c202a045000a2501c01040805241d1446050803140107458010a140c1036400f80503445d1400070382a03040c041e42c2c0c0ca060f02c802c944400145155180c5020348104503141c1100319081d500007a282a10840103e0070510083d40e505000f03501c25a41103400503a0352150910503006803078903c0005e035020904071481801d100680d000b40045082007030303081107601d22580c082c2180e80075040e00d2011124081c041d21002a015444d02508680907a510626181165051820803400e0b80004ca8140e0805 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 298737401 1250 298736151 298736171
    0x3040806070c08031303090f24020d0c1104090b090f150912030a060b1b060a0501120f06200d05010902043002060a030903080601020606091501030618 66
    0x80c418035401903250b00d4110302d640b030a515072800b03a00020308207416101c401d05428040501030314008001388446c1d12070401066403441594100542c01890002800514400000c0c091020815034002c1129846150181d0159101c2d9004d10024848a07600580d0329040200454440251103100e00c4d039440c01010075000181c0342c0c81c2400005044079010000c40302c148000781401140c591200c10941e040340d0f03283e43e510301205015204a82c080194030500140301801641080e620190b010001d1048030002c2d1143c003a4603081b91402d1007900e610010069803600081d99030403500e55007601558010503290b55100c10b140c00c5021581c201010060001110651035181c1c3c024140100b5000e04110700f01803600000c503001c070540c458001e003000d0382480d040401030004200c81401030340180100340c540e80c18010260040400c440241c2c040340c080c3d400100c5562002403c0c0e4443c1c41c001d00b00b129070341c0310002c14085401c040c49280d814541c607510049815080100003000d1281416008038843c0b0718 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 298738651 1250 298737401 298737403
    0x120c211a0117011e0207030c0609030503071b03120209011e0f03232d0a06030b06040c0e0f1203030a0203150114070b070512041115130e04080408030c030408 69
    0x20500d507103110f07414420301820841800901a02e00e00340340d9400343c0d456a10340303400ca520320802c080082015181100140506a028002e144038041b07a03220b8400c1c8001d52a00c1408516001100500182c81c05000c00e5100f04682c02500b07144406040c0700300400010078680c5040c00390480703e070000403803004e4582c0400350305000b615107086180e4101050503a50040e00c2590042c014008080000601c00799080340c035031010411010405411a010b060038003400300400f504041c0301c10b6074424003010104100349000c0c1300385c14080c00c0c42e46458170100444428003400066031a0400d5000c00300900b91802c011003072004600c200311102005039240383c261040380540c40d08560190400c5044030801408c3d805d030604454066802c14064200b590f07490108640750311558080a510700001810310007009071945d00306058210032215017403003015280d50354849014001392042c202c5101c800421164039500001e130703082401100c0091038a0348450b482c030702e103500064500070183d200180c01c12103200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 298739901 1250 298738651 298738679
    0x30803090d080a0608060f06010507080f030901060504061211030f01020a0309060c1b03080a020f2206080c0706020c03040308220b030601140901020f0d020307020a120c211a01 77
    0xc10f01d08200d910b04142031141d45100082000540303845e0000803940680c0100260303a840740e0701150455680548040c92101600250741064640d820490041802e150074041c00c01a1904104424207a2641d91150a102078526540c02e130580100b4917010300000b02800205510042d40e05c01049805141c41e0031021100180b010f401006680141c40e500402c1d002c011011080c0c1519246c801130b10f4a404000080c031801d503038050b5251000518841a40501110000f03c0881558071200300395100c5050700d0543c812942001284002c0141c200000d000398081c0c010707400c2d8030003242d040039100c0e41c980509501114141040504034482c414030369480c111030300054602408240e00310f050040000e071607031096010090b08901c02080015080e44200402c0b00180c003284100c49000615840194507907011608c142c0c05444084408200d0441124031441695481051803032400c0ca0300d402d044244200014104280f00e034006080301241e02007085404000f0104401c5130036500d04004c01c0c039840 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 298741007 1106 298739901 298739911
    0x228030206070503390d050a05070c0e011d09010b1305060d020d030f090506030603030d320105120604050c0f1306151808190c030803090d08 62
    0x403000400407407905c0c1c008000b03040c4800d010500307521070b00007110000c0410b03810811600380910500090070403170700642c0901c41c0651103c200354210482a4003004062040c0f6800345490708620980b1a00400580c0081080d00700300c40105168072125221140c241d03a54000061260b200c002204081942c01001d110848800e072a0142c44281d9140c51400003414290300480c880c10b010302100d0081000900079400c043d03420641c13038040c0545d4841120a0000640210010303101d403601041a110141c0a0707045a42c11722040c8500c4544940080e900b5511140070301000c188081100300d11942d0070f0b5400171a0402d240301042c004180e40e00b0042c3c0b030500e003001c00500000ca074080038049110540da107a1881500c0c45071541c2420090142c503010360441e02030a2070300c18200c3c00e0b00c0241071045200d0180c043d641d484580042e081210210103640010a40892450303000b510b0907400 = true := by decide +kernel

theorem cover : BRFrame.Cov 298561151 298741007 := by
  have h0 := BRFrame.cov_init 298561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 298561151 ≤ n) (h2 : n < 298741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
