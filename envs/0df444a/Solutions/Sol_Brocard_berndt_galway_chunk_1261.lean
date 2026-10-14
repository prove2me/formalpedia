-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1261
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:03:03.287171+00:00
-- url     : https://prove2.me/submissions/84082c05-312a-48e5-b418-5f909a25fe59

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 226618705 ≤ n < 226798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 226619955 1250 226618705 226618727
    0x6010f1703040614040e04030207170c0d02060d06030501090807020f090705031f17071503020906090d0305071703010f09090b1515041e120203061303091511060a0c 72
    0x40000c04c1141c43c00c484690310544010300400000c44801e801e242c500a540c5030128400d8801da205945a02c4a03490000302e0a03011000d409003811032810701d00c0d400c200890348440313004030000d565643c0100c0421000d10882086500c03504150740c1c0c03803000340100509111000c0d15507100d680c09804200482e540003081d240c0114030700c070b201c12a4001425201406489542204032001c01d1001da004294030001000b4003110500300d213052141c141200101e042e4402c1406e0560000c0c801c01c1801c0d410b080107645242401d009250042c10050103560300302c107443d220780c42900358540100051014980181c0024010b04601c9410050013046a40c3d500384154000c145910401020100080c291150388402045c03688004000e581c030360321142c441c1d9500003021080040c4252121001c1801e8024140031881550001d0052020356608800d210b40000c0d070010450401c101a58002120083d140208030301c0c840c540c03102d01c0000c114202036854983d00070200c0105a06100c01184119009503842c06 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 226621205 1250 226619955 226619957
    0x101503170901090b030406110315011206150c050c0406170c01080f06091009051e090708061b0403150501050f0a050a0611010e10050402090901050412050d0902090906010f17030406 79
    0xb17101d9903581040d800603c05481c3c4403500300d200108104819402d4144450040d4090722240021101c3c2405c0d403040f2002802105881c4010007004c0d000035001e00c21090030140b007842241e20b04034011000c0390035a40c031030340407000301600d4005201000b401400a545c24550a01c1c2103040c61820003041412182d0281c5601d0044e41007401161198100b0000b44000d800301d85000d1150f030500c845801518406200c088900180040102d048170300041045411a0306040003068140c85000c1ca0703650325080c070129800748240800c8000001a9182a00c114083d00c80d600003038198988400e000050a90101e280d2250807102020b01c03041d0f07102c241900942c1c07020310344a41011403411031907006010039900600c440c071452005400080e86500800d03c5240300b920300044648401800500340c1d0000c0d00c00500d107565120302c0490540c425000b501054060810100340c4410700d4002c14280d00f8140d136802c42c2034020000501c0440c0c4001d0020002b41101d10381084444103140721076889009d1401804 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 226622455 1250 226621205 226621207
    0x3091a040b0f0d1103100e01031203050702071d0a0b06090a06030b0103020d0e01020d0c020d080a05040215070b10120308040803060f19050f010905030a1202101503170901090b 77
    0x101d40b0349980d0003501e0b15411150030810007000f921a00e0325954004841c84410391203140380c041030840422100904881d4003508518102c2c80c04002500613010040c03082c411403150703100006044007240031549081c1181052081e180c10694481800d642c000324109014180c00c010f00d01c035603121030a25000711a15441c000034050031078401200a072294407a48032200b0305160b02d01800c688194018242201800000c000200007044180d8544060040080c0451000d00009034500040d40005610a20082000e60100c0e106014544e5680007924203440101420b810080c0c0d0540d40310850010304403120b101018603150382d40042440e01c1c005d0004180c0013020001c00c0710b50300c4810409d0310100c80140f030461442d0b038844611035458501c0c41982d102d40b101c020800e00070b5000c0d070303080300650344003501400144689841d100440b20004080504500c1b529240c91005011803054041c9940e0049030311540600d141025190300302014006a180e090400900503103a070014541000c681d0b01102c81 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 226623705 1250 226622455 226622467
    0xe06040209090f0f0106140906090406050405120a02151b04140a05040608060a0506010302040f150c1b0317030f01170c040203070c0201080f0603030a110f0a0f03091a040b 75
    0x608000079018503400620900b032a204100c201900075509982c001680d103280e0030095001c10411100c2550b00300d4114034650b0202f00454055046281e01c54040c40481d0040f06441c0740c43c03010fa0344000000c400507041703101c0c0c50081010358400e1a030054241d1180454407110800880002c1c030403445294400500948050300384d442d90000400100300007003040107440c1d9100d20254035034004481d1000040e20707220000f2003660003803007a54151100411280d4481d42424000884102c42469880500484e64881000118490b140c01d01d40b03070001418886071840d502d05514180c000c1c00e010030b01c0100520170001e170302041300c103042d045034056030200017030b6101c41c90143c0c10002c100203100e411030300010400042d1500202a0107a85100b030340c84800c940da03207041e000700030346003a80c1440e0305030004c11107001000e100750382d405031015039681610741c0317075001c46055843d005c64610708941409010000809040d001080c1c0e000809001d00000344c0190302ea030f0745542074800c0303018010a903d0302080b1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 226624955 1250 226623705 226623721
    0x80a03020a0e030d0203120106080712050604140a2708090f0613030506010f0503030a091a25020102060f01120312021b070801060b1e0f0c06010e04050c01030e06040209 74
    0x802c0030040c00c05000e46010902407400252246d0041c014070a284031440000241184544136841c895090303680c0710601d007011502020040e01c2e007d4003883e40640c03650b1140d012481e590381c2c018000c0041c51400594035802200140741400182140f04844500d4162040803070700c10411144040c40c200c4018bc5080c6500001401c0e6015031104e00705008210300d408004c000000522070b0680c2d0703c040d2903102960380c6804159813807041c802c0c42c3d000106100c0c002c01c098000750404e541c00035080c004103401d100072990010400903945495618043d10800303040705558040c00326903000880e1205042d02581010070b8030448021500c0010100a080020107000045543c10303240012045045051100e809030b8003d030f9a03100b94011455654a4120b0000b00f4424940441d6103d80a130011030840b005040d11001c143c3e040080c1501500104110000c03901c0c6091110a01030130031100041e4072810315040c80d5103412030780d403039080c1410702e003021000c441c01c00020010f51103581268665010740d51642 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 226626205 1250 226624955 226624967
    0x1b07080c120706020a0801320f151c020304080412020411030405060906010e100603020702040f110d0609020901120903020115081524010f1103030411030c0409080a03020a 75
    0x1080ca5500300124090b010041d040d002489041c45550343c0000caa40c1700c00c2c9507221503802100c21803010b4902006100c000980f60b0301d05603580c43c001e040040000004021951005194220b030f00e040c800014814080010001c00e03800c0c00d44216000c500714076043e51242604c4c4150300441c001c007204e0b0a955001c46d544c40d040b101c00d03d40700040c595240d080a14003107a460000b40c0b41182a40a09000841c07032044004840b403190700f10800020700c082c0b4110f070542c029030100070241d0704240c80d8502103840c101280101c1d00150b11218180340d48051400758241150104c1d00000030290040012440d582c0e0300c8041c0100d49040300c00001014109031505030b0042820100400940510510001e1402030124000d42d1180361101d85110a50701d101e98100e818521f160500040a44180810019407280007184400300160601d12000844071050b1071454000300c1d400c90b50030350030050708101401c00b4000c04280000030744041c0004007199452035494024199000105980813480201c05480b0744 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 226627455 1250 226626205 226626223
    0xa0b0a0513060b040e0601170606030a091704030809090a14150d05061501020d03020403020d08070201210f1d0c060f1201090e01140727080102180103051b07080c 71
    0x154003503915650383e003110b61742001c02c803003642c0420002c01104040741409050b062040d01c0081880d4510383c1e51182d00002011444000c0c0d9081d0f54210203420003a05480c000d00155000e04800e580702d0724000c3c01c11056a5009104d102c10750b0031b000e41008004c0c0160402900261500c6224960100c040d0105401884581029005108031410310401d1001082200700a44082e42503030782d104405401602688140d100082d044855510140c010172000c8000d00031251051400c048954940d210f4056610480660314070103d54034444d5400c03032036040c4603022501c14410910460492210300c43c0b07442e0050280d0359802004c0001d010894214000219000d00618620710116561106030080082054a00b041c00303540c80c054601d07070b0a1112030061881118113903182c0281c40c420503055141c040085124110000b02600046403120382800500402e80d05249071259502101000409131a0003901c00110020107803c0200444584021503080300d8200c0350065503481e225580602d040414 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 226628705 1250 226627455 226627469
    0x21051009061b2a150605100908120708090901080c091006120506030c04021201090e0a020d03120204030f0305030a140106200c03070e01030516060c0312060b0a020708060a0b0a051306 80
    0x1640450b0f511078217504c8441540c0c0c051301c410010030341c10101554000100e0003030750b0701a40440300b00d01c44d03408801d0042c0304051080100d142084408000302d207021400b80c01440782034020080d042094100001c1040e800130710003560040040c68010060640040410300b180380e0340d11500041d4040e10b081040c400b0310080a8411581e41501ca050850b40b0342c0b0a0149034003840c00c007441e801c0303190000540701980b1500105008020189950140c84844203540c4c0030071456002e10000010607600c68122034420b00a80741e56a682c5080c2c407240007110000380d242c3c001003a200005001c815445a80102c8540c15550a0b06941000c1c0f49c409160a03c0c074460b69605104e940000716913a03066086003030480b03120760b0480304800d00f0041140307031400701030081c040081d00107001c0380702191080311103110348029018000740154844100503101d41c004010070b40503a22148040012000400c80c150344030f254100100003000285d000a61501c03458460342d40318001a502512200c20994083c0009140c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 226629955 1250 226628705 226628723
    0x1021c0e1c02030a020705040207020f0d0c09140f071d0f04060819141b0409241b0c0809010309240b0108010b0306090121051009061b2a 60
    0x100c124000c0d41c13980440400380060190090010700c0742818000c0c1e98038643d009240d81d001e0b000c040d084c45003030b108070701d420380f907450441c6c200058400300ca100e59038040a0309242c0080601d0002e001092441d000703840031003044400454a03242c105841e40c61507642c581100c024070003400c0c950014001d40702e01e420899203809070001c2c44400458642d06060007030700c101410901880540c4800b030b100e0b0303031a0f105007a070030003800c84010252500d68041658140302e8001c4c4211200603500c01041d012000243e2002d15542d40260104c1412031981c1d41c03401d000c0c514080545140e40c0da1416514047c02c42c1c0b842c1070641711b911840030000007030741c013040786031050040381070701c81203406031001800c0c40c4042180426918400811040f00e1042241c0c450f02c00580521400d910f070031080302d84c2d003014108241000342441d09010024100703012802c5401c2466002044004040c1481c5085070300d88129004504004075485000c55003044040d0708a1507003018144100240b08021a24401002c400074004c0c12 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 226631205 1250 226629955 226630003
    0x60f0a0231120b010501080606190306030c05040c120209120d080a140108030307110c1305090106060503090a03081513090c08010c090504020915040f080f01021c0e 72
    0x1002000740e81d04880e180c07072400035550342c641c1414420301c40303005841c1000c2d800040c803095000d1801c0c65080040030f80039601d48030f140391500d4404009032080c000001d4a03800b00304140454042d8480c060007003190100b013145d1109001070200512005500800ca80105807008569100e000386024100c00d001035807034044ca140002403988000301d4044408629040b0003a030340c03800250003070781601d19010086145403034402e402c0e01e4102d8490607405244c0725181031400c0544640401d003221542d0b000020850f400d10b0381c180e0b803c2d1520b0360080c1c01004030500401c01840300c005800c40100c1d400d41400b42c2c13540c91306001d0700c030205503000105e5007040f00500640c295403140c0c0d0203c80300300d02640511050588400d6a00d0a9070301c13403903640700024050b040a000c10701e0158010f120450008141081252041d00403c40302c0d003140e48440010054001c04028040040c0b0541c409041c0d00e000840c070f0241e010242c00000359448196410203962840103881c0c42008105e01d6020481c456010360450b8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 226632455 1250 226631205 226631257
    0x304030b0408040f18050705070f020f120709091509170d1b080a0e060603060106200106060c14060c0f03060102010f14070201200f130f03080702010f0c05060f0a02 72
    0x241e17030002d09419140f4102c000350a00384581d00303480302c481c1d0010201055842c030b5004c00c05281e0f004015250b000c5c04c0c8428402088000300000d1004240000d00460b00009a003440e41a100c0c940b51000400c5007011101c80015101d000c42c04290941180040e45612400d10030000030060b00028400c0700c10141ca01800c3e6a4001044138840d04072880d080c40082c400880050300c0b00815201d1075010b0b4010001404803d00034110003204c000582d4103601090301c4854070500b0b6034629400300c00441c60030643d0341c0a018a45071500301414890009003001c1c10024100c0d8418412884901c010000102c040780581e803007904180f0403580402010304c0341200d10f0345106034180040c0e5040c800f541c03030031414400b00c80c0548050f0075040f00c035092950814101c10520003956010451001610171911404602640802c0700d81c0041d6005a000d151544920310000d000d25680c54159014080c3e01e892140010f02c00181403035001e000c05d0440c8500307031a2518080c002e4000d110f803070301c4c4519070840c103440c00c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 226633705 1250 226632455 226632479
    0xf160f060f02180301022d070215120714070f0206160605060910030312090f020307060207030c050604050f010e01022a04050109110706200c0319050c0304030b0408040f 74
    0x700720382c42880c83e03d00d0104105400c078400c600450b40c846800011a106404c000019030303800e0000c008140d0300e0700280e9400034108216043c1c1190488401003154000102150b20240d0703c0407082c00c056800c41d45c4400f401f81c0300c0c09185401031440f40c00600d079004548a03041520000303100000456072102c0549889000351008880c00fa020308510000500c821001e1085801120340540300c106080030f02c0c54030b06014100c9164180e0749406408642c10040c1ca08105500c0100703103960103815501e05514082c0b0103100306a0240b489414240801c0c0640d030344811501505d00802d090982e1005541c0300180d0034030130314801c1d003598a500d9900030381c041544000400d5070781c4422101003026a8841600d40111004000803022104e002e00c01c100c0010001c0e0f211054a11044007880c61706407002030f4505080d8080010341801e908082104000c100441c021803040c40f00078104141003d102142107581c038000c511029125070103d401040520151504850142050400b01e220080e00c030000b0307c9a03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 226634955 1250 226633705 226633717
    0x20a030c020705061e040e09030a020106120327091518090314030703140406061e0e072a05030a0210090c0501052b0b030f030f160f060f02 61
    0x1003400c0c8880065a41d01c081241015118018241410001e0440c0e5111211102c2480740c2c0e44180100004540c48401103107480c481c0342c0020040d552038020702002820f503070156121700d200200541c00ca00c000380d00700408041172110810f0040c0e00a003400e40741501415560b0240070218501000c55502581000811054442418140b00307004c2e150130825045840e030750b0002c4e0014007483e030000c400b05040001150441c03920b00d4003080c045912400c140000d00140c1e000c803072044d5200d500300070320505c0c0540c2c0c040c85540710901500052906251503031000004020008119443d00414610780c800b1652401c40c02000f00390b034002c10420324029035654402e001c888058030075001070100080301d5001d48400c00740e01294002103149040019180b42d046007448507454042000054840c4101404a095060380b02c14003040f0008040b00703060a1600070584c50050707400800038000c0003613844c800c440f010400a0140013824140b410f12801e86071801800410817400c044210514054640240c15 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 226636205 1250 226634955 226634957
    0xe0f0a080d140f030c070203161206050c0c060711070305070b04060e0910030f110909070303080c090108042303040e0906160c060c09050301060608090607030e0a2a09020a 75
    0x1041101c1d940805402d4000c15141c82c041800c2000060451500b500103421050300c050f04481104c80c600161141000494119400580d140000d480910076940203c0e80c0211038200c40500e03100d81215074513103800c001032100703050011000c00f207500b00c001000440000c64209007070740e5040e901d41c110844581c0c094410040000c0c1124840d20070340c80d001d0610382c021802c121815038071500d140c1c0d926220f0700e0301c0d443c141d40c0c402c0702c0a803100e15516007208140c03080200c0009482c8480c2503290103091410b01420481da80d00c01408800d2951760032040841d0003035040700c00c5001034100502e04050000b1100780e4810940004980026181e200402560092170380c007003179400655401e0710311500f240c480c105890000c1d4284200d507000c0b40003984003408819180c80e022002c1e5403640042403d4890960025001981c2001000210740c014001d25410810b6450144414803100448a0351a48255406445202681d40341906440080111460005011210074070556246480c000942011039094 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 226637455 1250 226636205 226636217
    0x11805060d1e0c2c0d0302030703030c08060604050d0606051002030310080613030f02070305190318080a150b130c0206130c14030a0204050406050105120a080a0e0f0a080d 75
    0x1c0400c89450207036100070780ca242d40341011000846410480c2c44442d103401304000d0480c1d4001460364980d11242159940280c005550703a1110741f500a080b00d803070086001c200b1111800303112403580d4600071181160300494203800240c4103400c00b4001440b0540c40181e214031000102e50000b600407010f03601c140040f000400c02181d591503403540315401110a00d644031a14404000064010f14103044c00914510444443d80d4881c1d582c0c0e490810b07070494100d0718017103004a140406500400b00e8007000c07000800e62403207034038143c6916a075450070940140040c100401c130f6012003c00b540301c80710858000b030210300b440c2c045060090007003000c102d9880040c01031900107258a000c1c43c9147c8500ca13400525400c0051a240000c00060841c040d0540d050144d00b0113034000d03070396601446000318091400010309500d0300b01005003200c015032911503982c010300c0b10800491189819102480414140b030801c4c0803016000980004500c080b1650010300e44801150716900046c0020303407079045444036 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 226638705 1250 226637455 226637501
    0xf0c0801020c0c10170f16030216170f030f070801121203050c1204080307110a030207090b0a05090703091515120212030d021e030402030c011805060d 66
    0x510309030301c0345092002c0700e6801074180c04040d040000b070803d00c0d0b14440c40c0c94100070b12090001c4800020a80e000c060240e142c2050000b0507411482c2d0301218202030030218501503040c21842e030b0260940002a1501d50748150352100078505000301c6049420380050707a0360300d11780988440e091044c1603411200182c500b800114000080118500e05150070000f10f908103042c88004030302520008000300789140b07061122000c0708500000160049109500060b00c9141040c00101414a4008030b2103240e80b115812001003900412000b003900d41c11000801c5800101000c030754640000c0e8400d54002c6442e00c00c0000543c1d02d54006003980c0e100302078406414160a02d028160f0340700e4810b2650400f0210341c2000b042d240c003008843c506101810040c001030072101c02506640081324446e400c0d94001500c0011940e11a80c000911b04a08011600710f080bda000b080e9903000d1200c810b818001060035250744055110b00300320041c030004007066500c4405000c0c0c4005000b12022000c8421881c07448 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 226639955 1250 226638705 226638719
    0x12a020106120f0b0603011b03020c0f03030f0a050a0930051905070203100501030b07020607050a0e04051f06050a0306050f0306062106010b120f0105060301150504120f0c 75
    0x70180c0a54000b0070043c803400d40b540b5a22030204000c1c0c0407660641d42d031003209440c0e695001c0d5505d1101c00540b001610b6002040c0460b04000f0313020070190b142d8004104200e0301180f8007070500c1d00004080e80000c0c60b0f40c0d51300280002000091030142c880e00c1c000c00b9030701c8500f0440c0342481c006900243c244103001100320702a5510701691072500c65a03100c1c0b03442181c5140c0b00300007500030140024102c688031455250020110390003a003054400880b01c904204885804002035038121074145030107854542080f40090840b4240d840c414402d548481c0410340030b0404240d5480140c45165445400a03901e036800303495030f030010460340c001c0303402d01800003218680802250502900503000d04402d0781c03242c0402c003078144100c159020041d20b0350502e481b030b00ba00f0402c00d406081c40000196450060a034046100c0000400301040007003001c00610158498a00b0780c0c1c1141c0404010450705040000181c40c1030149420030080c25407656000400c0c4201ca00c100001c4c0da01400780c400c1c44940352a2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 226641205 1250 226639955 226639979
    0x421050a022e020c0616230f1908030402090402011115010f1a03070507080f070c051f02120307120f1b0507050706120f0e060405010e07050108040212012a020106 71
    0x10301c0d56200c0406d00454840000007000d0104c9148500c0817a11440e2030016440010f01a44802030010f41c0140d0b540d03484c04a0800c5102071142c1c000600c142256a142c0d90210b8510005000901a0310a54046000c690088892440c114204400da404001300410146c6241e4024411000490140c0c0400190b001f41811180b00303040303828506a28683c0d4601092b0f5171580a00000c84801100708029050030801c44003415001e44105600400c603481c2c04100b1603c10700020721001446a90340c103103803003a03400180000000081c94400c5440341c2e901c000659101119540c01c501031810218000c0c507444c0d07903910040108910206d880e40c0118048012540350155141c02400ca500005c41401100e00800703000d82c0200340c1090100d04501d04c0800402a6042051012038941c00802404204002802040700310300c400401001c00b03900e4080024a06080500043d001e909001d095001100003034100c41032503044168180000e00701c15010200b0102e1000d4240015483c180000c80c0d41c403240301c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 226642455 1250 226641205 226641223
    0x11416050705060708070605060105090a090506032e0902061605071815060503061306060c020909010c0c02040b030a0606060c050f06060105030a0209041415090604020421050a022e02 80
    0x3c0c805c54200003860b42d903100102800f40c01c05061020a0050030420780c2d401c640c0c1d6014103607000003c03505041000a2501d8441c508101c110011030f10750500d19266883c1000e43c503950108013000c42c000d030b11800843c0492003141d8501d80307000400c103461014000002409000c5861001c0354498072459a40403104440080144100c1815032403002c000c0184110069a000300005000440060a080904088454981c80f01010400c0340c440801541390902249900c101008001d11100d91136180080000300e000c800288038950720b081310081d90728100b054100895100701e080081c151150b0000e00b1034201070004441d00d2007032516100c200079011508501490043e140c49085032550a02c25005e900044006500302c2e50b511100c0ca0103003100310907035000302c6031103a0886440d030891040c0086a10000c040c00c1c0246d00402003048009401546404000507000c242060440a491b045051110039480a0f50001c1c41100f0244000402d400c5040301c102110101002c05070140001d0740c68028007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 226643705 1250 226642455 226642463
    0x603050c0f010c02100e031e012409200f120718030b130c2405090d0602030606040807031a060f030a06050c0d0501030602070219140d020114160507050607 68
    0x168000f40040c01c281c03c0090707030307034949040c0340c001c0000c400042032521504c5105c2510307000c01a82401d500350b10030710581c150950f060303450340d030700558080c1484110308841c403480b03649a07584d0114001c5042c40c041600b255411040889907510f02002d11041030341c101083d810005517041000c229098007030301d2a0ba02c000704411900898916588400711240750007400c0e05ca100303400c910a5400680031139000320241ca40d603144801c0d000c0383c20003d030300540b000310010f01c01d10500300701d0740d409039031070070110072550f6801203000d666a90f40d040400d005010310303072200403240f1403200301000300014013109280a10005d0480f0519503281001c00c00840c01c8ac0581e07940503000040d02c800401c5042c0c000c03a90002e40c15481500d0004051003107000c50340243d001b50345141d030106010046217003004105031b0740d03c035108105048a040c0308210310b0401318614071504ca03900c0d030a109021a40148002d481e41c1e402240d505031100780c42107264031302d030202c91004c55040c024280c1c00310741440d0450036103c040f604 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 226644955 1250 226643705 226643717
    0x415080a0204050a09050312090f0d0e120a0b0f040219121209050a0605040305070e060604180908030403080f0702010501121e0b1e06061e070c09020c010603050c0f01 73
    0x20640901c8028840a480c043d00f00d40c0310000c034808500100008c20072903290b414600c01610300040502c1c1003100702803240c4481d40248190017400c0d6484a6a20400007080b1030b08050141e4031600c161402641d00c1006010285000401240000f4042c5080c401c03402602d10200c102c103070050304042500c080c000c040140c0368041e0b00c00007003480801c29110010950500c54145030701c41000071901503450b401400007440002b0140100103080c4042c40050000b40240081c60405000281040c060380c011085100040081d608581c00903800c1158001e4102c54510ba40c1d04080c20020102401100d05c01c541000c0300700800c0c485031051040904a4001284510700700845949450309800d405d4840e00714425841d5000004c5000ea150703441c081c80014898500d070304c4584d500f0800b00540106810301c1010184003a62000114881501000e0120f002856481c10b10f071521300880f5800d5000258041c1c40401c000100c3ca105500000990380100126951180c10404020900d0805580e45001070f90b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 226646205 1250 226644955 226644973
    0x9081920030102031810060e070c080403060c030c0e03071404020c030c1209010f0201140a020d0f0504060c0219020a0e0603120c01060509090606010c261305041508 72
    0x2903400000303915001004441100000d480d40040d080e60000d0704d001c60f6603202150f01140d940b404204181310600381c860144a15860540e000301e0101c4000d00c03001c280b1001055080403c072003074048402841c0e00030300800c4100149040100205214045030000c2000c1ca0540d403400d107400501b88080b190101504800703005210240320280d0810403c024403407006000b115029001800100d2860f0940e044d0152030b45171082c0010030841c42402103c1c01d591400301c2071096103841ea0155031f03204900f458056600d008548000008010006140e040c0600d000240800c00105411850040c003c903400c07100c500b03240340071400d50004e840200940c042c96402d0100030650007140c450760b01840003010394003030301004500b84a02e0ba1000b1019070403a50345038014440d515081c134000743c0180c4140c0040c103c62a0043c00600004081c40c00600f0f104001c405485a6240c80203581c6a05a100c0451944460048429410101e4240149032140c0e040803100c96048401c0ca4105080710203031401400d8440c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 226647455 1250 226646205 226646213
    0x30405060a0c0207030602041503060506040e061c06090c06260615190302190905060a08061903030c05010e010c02070303050a05040e0c0c060601030b0f040b0604081606090819 77
    0x40091102c41082d4080c01d0800400f2a1403440a0001081000340c2e00c4044000045c0080850b4425042a807186005000620102a44481c000d0780144240c40410001040100d00d03000490b4486000340040d08144c500010400f02e00c13001012070304291108081e048500004940104000140c0030303400e24080f000610500c3d203410145d0311210218076240c6807000b280003c000c0081c1c0b032254180400d400068060754a2500000c4103214001c618058040c0e42c00c10000961504c601501da40030080301c0d102048541d92100f6070302d0041000081495241950381c60050209041c10302c040d00c0c1c9520b07001107802c400b030041c09003960051455000e0720800d03046070380588981e000810368070100a42880045078010500d6260750144030060800354861030441c00e01703490b10f90300400c01d9042500f00035501402e13480b0b10040700e0800404460110300041814040b407400d008550014409220b4062107542140c4d00130452000e0fa80035944001d415a1a100311954448189020384008885000381d00007207 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 226648705 1250 226647455 226647461
    0x90f030f210403060501080a1115040e15030f39100e031f0506030a020a1203030b030a080c0f030307080f070210110a0e0a080c0904031b0b0103021302030405060a 71
    0x1c40c61a105030400d03880c2e032a054110f640036005070080e0303400000c0c44402d0052000c980d50101a08840c80c20040c594403034925101d00540c0f094030350254007400171442c4080c0c005682450080094100c0710903826604440f40d5601a10643c4101c900040c04250303001c88030840d0b14150705e5440c010b44501100c446003440780d0380803848440da04000301c4104502135640c0c02d115444c0b81da402810754017030114030340340b0030411141e003d81014441d41c451450b880c01a12012144000c0b180511140e000332140e42c1170560161030b01d070314415454060708100e882003000000c007600e814229403046480118406004c2c0b40c0e20320041d118480841c1c12034000515219504503220f84c082058030545d084648007802c1182616403003d1000b1801030080707201744410354800310340444d034002212030039020303480c004180b501d030a0141500c5000300350300000a814035000340e0104404440e945c1d42000c0d203842c541440d002200003800304920031804040386150400d9940207a03405107820a001e410b050311111020001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 226649955 1250 226648705 226648753
    0xa09090e070509071b05060609090c010801051c0506130512040e062b050708010b010c080d090807020a030f060c141b120403030201060807050402070b0703020307050403060f02090f030f 81
    0x1003100300c41d403410240c08005c041c00d402500c540c004009504101c0c040000c402d20041441c03005500040d510f054680e4410000e41c1111790584011080c03200c5046d5035003842104850103441807080304144010122413015407040c06024130162803c0107030311910358046200301c2c0709940c00001c4200100b0113b03d48900f4000c05440c810307071200f4030030809008241110b501800c050314240c02511041106500030300a0701106002480d10082464080e82c0314080d5015004107900c0b5203940e80c3c516003c00010f08202d410041e00200101c40c003d5503868008944c19000038219800c6040c00800b00800d4019a5808000a00034841a0400c212980c00700108c030ac000300c80d06c1e114402c103400340118245003001000550700940c004a01241015007003440e20405900150290f841005420085411860801c1e003040d10781c0703009039032510b540504890b42e0107650805040e107440d2044144078118070b40d00405107403400383d805207000352a0504160703c489820360b0182c006e80248503607010b052130202c50908 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 226651205 1250 226649955 226649957
    0x51c140307020406030b1608131b08010525030b010c0605040f08030c09011803020607080d0b042901080f070c020409050d0c14010e031b0a02030a080a09090e07050907 73
    0x418200c0740e03000030301528541e0b481661610140002e00c107404042c01c0e401c1c1040d00f80c50401c00660304007030021801021220102a00c0701e000c400c145003c541c00029080020540d5000a01c1141040e0810802c2c542090b000c0000c0d034001d15143c80c02030741c0603004600504205855010b0000c420344ca42e1009844002c004075080c041c880c44400005034444040c1d406854191415621400400b0000d080e0304c1756001c1e000c030320514000d410001680d80300c0441d000c03030f50b201001c0e9445480c0c070309080c0060711110780d00c0e6502504040c0e01314507c189800840381c140e18000d2203440419104401520b1503881a291501e5144008000522040c042d4075010001031003d00001501c40302502c869003059481c04880000410b1140d018050000c041480f074280314101c00200012142c00b00c1c820354a20645072401c0804081600d0800381d0b20041c41642e241c0e5402030280c4030520300c586410841a40300c035074803c0100d41c510402145082445c4610080e040410b07000700405820841041421240209104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 226652455 1250 226651205 226651207
    0x100c0c020f0616081b01050105030c040e1903121d2a0d05010f0606080f0103021c0605040605060a060203120f0a060312080601020d050909060904060e0d0206090106051c1403 76
    0x944160000d000c00c4083d2401168100c2d01c503003041c603611060140d45500c8410680c10100140800c1c1e50120344e00c26540011240060061140c810413814500c2c040144d8900c0d054119026080c10b400412007810221000810080c01c0d01c801c11084110440e1035184c1013a81c00b2104201c402d00b111007003140d00c2c0c03074024440016000c40500080e84a001c24004668a9449031034800d052010380c000ca0001e02590b0500f0506d07484d0524a8480d80001444080c0c4a00000409401c46900300c042e100541034115100340800d02c0c03d81450005040223540d06406460040320000b1110310201c190781d00009003c01260840d00e0360010031f81c0c0c0c01005004110110b5546800100180c2c60074910810048240c1b1280b01a1a00c0d1001900340040d0489101c1801410412490795a55281501e0750003581101c1004254441d81494001811400000400e511039100400c0e05103800207101440741807607800034040355864409010007080c0e90030075075603801c4141020314006110304003483c03260903200c0100c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 226653705 1250 226652455 226652467
    0x1d0121120509030709020705100903050d0207021813050f06130605061504060c0303150311040c112e0204080304051017010b030f060301050c0a030906021b07050102100c0c020f06 78
    0x9084c10341c141d1020204541c0004c2600805c44144804a0700c0340c0308240801c2400503035180074000e4401c50102c040d05550005505007107590781146400c44051f41580c0340310900d000c0f00449520300c05014240c6586c4101013400031440c100080c542c0c404e011040c5204000d030501da450300b0240501a00f000d40c480c041048007520510480e0107040104810303075858612080909015044500103560510f001c0101e003414008115203100c00d9007503103015600011340c20310804007140c580d440340202d0310302c40c01a1741444486a01c5284106410300c041e09074202c0c800703030302e08202c0128030541c400c0200c1a042403108021034506514000b00403065030424008a0080c0d00c1d80c0407449800744c00090360800044207200002203200380c00b0750703c000260001c00150500001141950060111000030543c03660350070800c001d9250152070b10f0010324004846a101c1400316151030b1041c0303000302801485880256400c001541c014107851450644a94525a50640034083c1c491094182160403890030050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 226654955 1250 226653705 226653709
    0x7050306070c03090602030f0a0c022202090a080109020d110a09020c07090507031505040b0609040908120f1018060b1605010b04061d04050106050306011d0121120509 73
    0x240d6124504964800341425003030f29014004a1007500a5411980184070b0a0306040e00042196401c48407400e10150b004498400505940356030b030b1410384c101c005d00340090390b054180e40285c0300304101220b04080031500d4110b810b00700d03107511001a61000700c2842ca40041080c92001308200b880180c1a854003d440c0c02020f01603030311032828864580d01000c000c22001c01c0394030070140c002c60ec40c0303030030b001d9884090f00581d11000c0a003e603d10403039541e40641100d588600c1100c3d043c010107003044c00001e0040c100f00340c158020640b01580f0441c040005400c8601d6114031030300c611807000400500c00e0410044128104072681c414803065074500300418000188805070a2101c0d4a6104803980380051400030b00b03503400309810300e0090f0b007404001d000704030340e8100c00c1c0503081340c00c2ea07000c01c0366807a424000d02400250340030756014046c3c0000404c600554894070107940d030600602c00784e41d90365003052080748003071410240b11211444903c400052200e030111232100c0c2d580d2414609040d89040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 226656205 1250 226654955 226654963
    0x9060d0f03080603162411241803040306020702010512040501230907050409020a090e03210f01060f0903050607050705071502060c0d0905070306020d140105030d050c070503 76
    0x10305601040301d10003003003090b140030003d0305000c0c030031500f4204038103244c915030704510302041490304140700504541149161051842e05a2504040d04441d13281030150203118803650f10b020095456029000000c503590704040c001186442200e00452a180c0b039519024000d40011400301d040000400400c072046001020140c0920b00480001902a6640743c2071a56003100058018100c0c4c224000c03c0700e02d100110348103084940a460208000c440e610000c0c400f801d0317642100c40003900e81134021408500c004043e01c0e01c01d45031030080c46006e15401c403003075592004a44104c600501c0c0380060107410304c2a0000e5402c8071160410410341d68507955550f081000c00c640c248001003010403084103202c0200000b80040c180d080d40050071100c8144029100e802c01048045041d900180c034018980d86944008103c603003081c00c1c0c070b0544d6241d240c00c4c0060b6020101c0400032608180f8030484181c45880c2c0d01d8100c55000300180f9440d0170810080e03803140c011010303c02580c003e0560008140d1000c1c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 226657455 1250 226656205 226656233
    0x30f0d061806060f030506061b0a0b010308040e070e1c06140702061b0306031c020f07080a03110c0d110604030c08010b04051305071a04180b0f060f040509060d 70
    0x10000300b002c0741031860052001680003c40070030541401e0a100490b2201400c41e00c52907400e0b482e005100f0910a03140b40781070950100108240c4688000000313001001015000751140a0400d22160300e41c1103040314034842c100e6403070350320403e20100241c1d07940d80c1401b0013406605c20207001c01d101c03070f840c10380c0c500710b5030122400405600400c0030031000400000c26020380c96000bd8801d810b40c107000d03011070740e265100b0a044180246000108002c03d00070407581003a0b2001c541100e0681c0d4580481c191211038007501140822840c1821040c0c010001c11680e80341c50b009042c10080a5a07915070300c075050116180f0360b420210030000031003c2a5040e249401a00080001003004134501060104440006211200041e1b55910001c00148013245440031101d5051010720407070040d910541c01c911440e4041100c41283c5865900c131003460b0b4208001c0808122885100c034030004040c8101d46c482c8446404103010104801e00041c6070400c41030b50040c801400a455800003a82c031a49811319403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 226658705 1250 226657455 226657499
    0x903060903031a150d02070302030c0307210305042013090521040e070e010302040e0f04050d0306141302091809010c050f0d0c030e06010605070302060117030f0d06 72
    0x241c40141d483c010f907000301c1c4041d44082c2d9000040081e410b08028490041095208501d90001201024144200240e407800c691240035640d90310103a107056850001482c0030001c040b0440a402521103000e480741601c078a800c04840d404203030400a500010683c0d1421079039010304018020b00702d00540d8455403001c20321030402015031030065030b418900d24001e004141500881004284000450344460380d1b0022102d0411203912042c1c040143e003c3c1c02a90021000400480d00b0844480c00200030580035a0080702582e20040c80c0010403010f5901a004400d050a1860001c4019042110750031001c40081c420040c1032075502c03800180c00b000c1f400304e0780c0c004400040c14081078400a22030508100b423281000d9141500529080e13096000302000015150354411030324120300c0c0603402441c070b03070601c0c4000e40d01c00790b031a10400ba103182c120400c140d00621030350002042c21510000c1ca0000d011185008606242c04400c07030a0071131340414034011001d52901c90004d2901c21031007003a0b20344000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 226659955 1250 226658705 226658711
    0xf0602010c1b08040b031005090c0d0c020706020c0111120307080105100c03080708041a04051b090919080c0f070501030f0212160c051005090c150d0507090306090303 73
    0x40180108151010b01d469050300d1182d018010019800720103c40880342040f62494599669401c3e88261149940c005500f101c00784041049405000300200350321040410100245150014102d071381700300d940103120160f030100700702003603079801032440600d9840b5000032500e600400c140714560a400c281c13500c4011990500060202d858070a8040d94204200d1802c15070ba465a51030007007405a01401c084180b00401c0c01050602510018660740f800c811b0300800154280f61030315a64420b180c0444d0781e00e41c020822400d440b881c04a154600584440006101e040103465542015105000701100c10b030a0412204170502c034240041941840182c02400303d003841c0100240941d0702544c02140000d1040088405610742403c42941008400c00400101001a00140e0702d8402a20000e020351103034003044000c00e14603812451146800e42c00f50307111025148140321283e44510071241e084001842100c020690a620a5900844600c1c15100340340d529240c00c0101c070780c1c1d12010380c00662 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 226661205 1250 226659955 226659971
    0x5092209060e070f081f0504060b1c0209060301020702090a051f060c0b1005010c0609170d02034302011103090105090c0306010b04031e02310203040305070209100f060201 75
    0x1c10004c0d00402007200f080070308403001000c005400e036480d1042151142c3c0b0b075144081020703c601e1303034080d0b158038030017a10410b155005020920603510000c00f00704e11694072200000c00d01d00f018000d88105503030160001149072107000a820103487c008083c0c82103c86600140c030702c0c1e00565090304004007101c2c0c82c1c01c504c804d6242441207415400174007445410780603003010441641c0c008000300c48aa00020005103000c41d501d400b80101a01030884070341c512011410030131442069000390300400000c40590304480500e1158032440c0d211050038030ce0b024005c45400032502d040c444800044007503100004100034074100211843d0021f80c0e40794090ba545e10100f001a15041001400b080c1c411001408d1035803500c07440b580a8410f900009120750700c00ea980340b940010400200d0720655001380076001015506146a4100c8081d41000002102c0d01c22122480e01c014401c480c0039a0b010b650342454140b00c0e07000c1c01265903000c0c1045400681c6408001145c120305500080038124079800466014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 226662455 1250 226661205 226661219
    0x140904110a120b01020109020d020f0d06020f040f080105010303020601050d05070902040e1501020f060604020a0512040f02011d24070b101d01180e1903120c05092209060e07 76
    0x764644003c0d034150780c0350200c10405a40c0c6d86882120302c07581140c850603140000e01c081a00c441c0040d100410642c004644950f81c520900090020744030311106001c0840d951341300c200d091312021300c0082c015800c1030005016509080c08081c00180c000c204407100b5903034074000c0c001203038800c1c0c1c0080e4104080c20700344015601076020482e4044002d10090158440d0808600d40315000a448035101d43d9000a080720a94000c40036540c890701e844142100d6840d2a050510110341c4000d0100d001558410182c0100303a9203414000d1030231801380200d0700160442d01842541010a102c0c1c404019090140f640050b10800046201c1e014600000d01355901d020500500303603594800d2800505102d400500c10798440e03403200820b403c079954011540d0a41005081e052401509002d032001084001c01000e040e009064801444408441000702075810b100c220352034011000b60b254894050b0310311501d031b17000406c00c8000000e250080040c441015646003401c03181c000d0b0b090b51313194002044c100911 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 226663705 1250 226662455 226662461
    0xb04030b0601030b0414150f03010915110f0304080f04090216140309010e131b05040e060a060c060e07120b0103020f09070c0f110907080603010516140904110a12 71
    0x8103101783c1e000d00017008210107441100307000411070108415440203002d09a0380303000c542c21030128080d0080103000030600f0124080c40c2034018070241c4030300742084480300b045100100d8005802002810341582c44a0303440c2d950b90b43c000c0c00240010001403201180810f00c40c801013100c00c01c030983d041841170742440c00d100140e41d046881ca0b40c6410078028004640d8009000302054242207550160015110f02020001d00e214584020301d5551704000204180d0000d00500c251141000000b40741c1c2d0f501000c011580c01c0034016130000070721450345100001c481d60000303031070ba504030001e41d0307011030300c0f4000c58210b52030500b01901c008111200410a505215056088403038088c5c0d100409403a21601c054000f4405800003401003003a5407039181402040ca981512914005080c04920705100d5030042440905489440c484c2d440c10780801c2c1280300003140c0010490280c1c84183d020890b203a04070840f07412400507250041c2d07da18000b0100e00341c3d00c00400b02c00312903481d40f24800720070401803411 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 226664955 1250 226663705 226663721
    0x30810030b150406090204050d0b09010e06091005011a070f0c1e0f0801021614030f0a110606030607022a0a0806040b0705090a05120f07060818070f050f0a0b04030b060103 75
    0x5917610400007404542c03190040006125000103018442d5100c0070041c40c01840d03040643d02e118000d003c02d0220722903010810000300c144c15503043c080781e40c8413a11103007207070521100b64481000803c24039000800407041e01e10864010315a00c0005a681c000301c0c03060413680900414203100ca0700c024040410001c00c1d80000d8200c5a00031401d24070360f5042d080c0d1144843c0c0e405860582c0e02c01c141007050341c08204882544000104c02070b224203e5030005050030f000381903041018040c0b5000076405060000b0817030310401e0b03254010304003294040d104121103090444298010700c41d58298400d00d48a40e02510000c050010050102d0700d4103041900300740802812160400ca400c0002d0740d9541da0364406a8184c400c1102d500a8001202d0012031800c002c004040e903013401500700000d07031260028541071180e80300c440403c6100c801040c143e44c8401e03403405648000140440d00340800c1c10003080d008810341028092003000c070303141d0600121743d07009503204a84080186080180e5541d150040000d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 226666205 1250 226664955 226664969
    0x50c0312040503030f0c0703050109060f060b070302060c090a171b271e090d080a0e03070f080c16060f03090809010f1e090e070206040b04030810030b150406 69
    0x700301818000080d031248115021400340080102d02941c0c4401c0c24010f080055920100070040042d140c50010094900300c0140c464492400e074001540302080c10445c0d05595155002d0803850792a0200d01100784c01090300b40341c0001c425200481e55007655400d200007005400010a81c40e1000b24605051f012a020203d000d60100666080010036011100a0b240301e0302c82c610010b40c2d03402501c4091a400c240b030b80204030b4400c3c400d1201d01e410100c1d0f1b0350980402179071440407964464132214190f0301140030051140d8010409040400d03a0100c020000510610b806864201e0107400c180c038022140900c0024041d0707240d403c1001e1500002c00020a0507c1c1c10240304001c590703291500701d801000b4010381804401c1f802044994405e100a99803550f4046050210850500c0020042441c83c002c411860410300c000c140d485000103081c43c41140e004c1d5100e5003d81d2260f0301101d810740050300e05c00001055000200010380c40b01d96141c4240080c41c0c0c4007e000d0702c410100016100c0643c0004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 226667455 1250 226666205 226666207
    0x90818040b01080406020f0d11090a0609060507020904020a0306090b01080c010f08070e0d020a0b0a02101103041707050a112d120705040203040b01030c15020c010f0c0f050c0312 78
    0x20a0390341c00c1280319a02c1344c1c0084005032941d1200510421074460100a00d0140e4a00007480070444100380162440340015201c11041c81d44640c425a0010128022840842c070244103d81c01858048415584688003170f0000e4010741e5244d80e101c09541c2d2004007160201c00d494014040070504000d5064103200901c7c00e039108600ca0071015151560280041d010081c04081000b496141c404051a00300d0b405000c0641c865500c3e82d040380036811142c3c0344001801100c03a50016035189000d0200c1c0551804006491900c2e2030b902d11a214101e880340200c3d46600b4002c1c4000b140b810311810820a0180704160000e142c12020815012541740c020800040c07402141424105d01e46c07917685105006440b0680c0244148c4102450401541d02103a0b005000004000400220b188054102c0e4800d4103410710381520b88240c410000e00c20400c00005a11030840c2000d02d601c1154a100054a1400c1a041081e1a031711000306000c0b10031003e0b00c0c19403103826180c40c203003420040300c60f0140344000341c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 226668705 1250 226667455 226667471
    0xa0602031003150b221d01061401080115110a1704050906030f1005061804051b01051204060b0f030312160c02180a1d07091a01020d030e1009081804 65
    0x10310b44421117030881d150704405030720a802e202c646a108400ca4507070010741d500c1c50100103841c1c5010740310902410b00c08e40450400b040c1e01d5400b540c61039058513000c2c0003540303080b00d42d03a01c11981d80910004858692240e00f6101000c0750700a4a44400342401184056895042809110405070301600450190340701c00c094100d00385010a03445d00c4184650004121a1100d04c001015a500300001002e2409144148000c001e000180e40042c0d0f561446600c5940c00d0042c01581c030342c055030355059405c3c48820005000103000b54800040110000c5c140e40b04c800e0041d000ca40386402030300784410208042c805100000c1d24420385428803282c0d516010048000300c2d4007142140440003034001214a03540d0201ea90491190410043d2018005c082c07c9074003000010b403550355180e84500b450680c680399504060102550720603081c031406030000c00b903c040c0d90108600401c0b0b01e8030341d0600d50043d8052441c1c41d042034010f000720240141f45440d10b440c1c0c1d0300c0100c0c018070710383e0139020b1240c1d02e803400d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 226669955 1250 226668705 226668709
    0x60a06080f04020604052e0f3c020f071e0308030c251704030b0f04140607020304050909070501020619020412080403062405060c0a0602031003150b 65
    0x641c0e0300000010341c22040c1d07221880840d1a40c0a80e8000d550301104960014541e00d10ba1070740400020007103140c1c07848003010910103581030803203801e5490000d03140d101c418101d54504400c10000c1801310458805540f00c01d50300e000740c0361000310000d00582040613288643e00b000c000a10140c45803640590241201c02e110701c0400601d444003c00a450110020300341074480d00035102d51030b406208498480304d80044c100a040d0080208a982c17406c03a14003500400c2c4800d080d00d003505d03480f80e403800c01519a40801c001c80e80c070081084034500d5603102d100c840100d090001da030080b54582c000b15211403c140410160940c000c02d88020f5602c806000c00081e0783c00a0400c0c2c1180d640760385010450083c08001c4041d2249400014040d65488000401c000d107a200800489008900401c02c007203041100d0307000c51100180708001402e8040c0d0900031031400c04014440141d03124101d41d080d410561703d40059030000c0760910000c0950724000c00600018030728880c40341c00c06880130403c400381b401c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 226671205 1250 226669955 226669967
    0x30120b0f0121090602071412090d0b060d0203070902041a0f04060c021206090304060314060a03112722030503010e0a0207060203151014090402390105060a06 69
    0x707035084005500002d401e6a0000c0796000003202500444290765910b003074184135250301c10b40c42c1241d145110f00d481c003081c41c071407410680b0001003004020403480c009948452200410180c201603000098101c0100181c0c1d04002d0b2400418081c500941c8461412418810100d18900d25018800003084038410f4668400c0c2200c0030740b1103d00f481c402c4c4815500100310410981e104059040c0b08890501100d04400405082107503440e1346c040c01154114020020312020a55440350441495481071001907046000490081b40103040740442051008a0a40d044a90504042e0981610b4184082404130001010300d00d040d503000b000354840c1668000b0300c1d511051189849140c0050045010001c003501140c0c03003643c1000e030640d181d048c5000035078540c0401000c040d205e000303908100d01e441d0b4011105682c58059074507040c4d00b48454a01444003035400602e0b080c10080c040d0106c1440d030454041d8030416003000e90038040007a001800c00c90308490010348000e00c20110441d0800840754049 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 226672455 1250 226671205 226671227
    0x80c0406021c140c06010f0902072312070f02030c0a080d0806040b0424080d020316050c0901060917010b090109020a03090b0a0b04060b040501050730120b0f01 70
    0x10a82e44191442150111810900c012100b803444200240e5041041000215503058400c500e4007204519a16000b40d002c030301ca0848000e11540804030200710400c92452518150038400c03050f28840c3c1a584883c49465101103070848020f485203c0e8001907050400c8400c05004056444083d41030038002c56503034480c1e0811560b010884c110002075010744a64205c0700001c20050000d0028a02d064080240b50440c03004a2185c0b4241c220300040c40500081d9103081030356590095442c20050414001d44000c031510203071180d100c4c2e103000c0c0c44141c5911882600800d0207568002a95041207440884e900c0000c0d9207100d141e042044510043c1c0da0740003124112521200016501c2984500603409070545440c0034080c82102c170104201000503400c01058140110390030040d458961840c146240158014140010b205208000008100303c82c00000d05ca403160b1101859146049103071040643c20714100002400380ba0350191400e418080e2804e000740c110b403140c40b29046640001e105031001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 226673705 1250 226672455 226672483
    0x1a2709041b0e010e1906052206030503030901020406170702060f0601021c0305070306050d050c150f07210201091203051b0f070302070609061b020105090402120601080c040602 77
    0x3030032400d450748000000c00410420349085143e603910945008508411aa84d252071900144131050642444c8a960b041d19401416000640724002c0112101a01a16400e02c016601c0c64040041141003001e140325a074041c0016903134030b041140050001da00303142483c201c5d655000602a8041d0085405580030303052a05031184d640d03075a00100d01e482d58142c100075406c010080300d43d40444d0725400003880b500e81c0341c406022150761401484120300040340003900a4000a00084031842c28180180e403100001d0f50b00c40c1042c1c1401c0040c0c216610200084541e00c58096090010098180501b030a131000360000b04440c1c0240c1d1904c100090401030f218081541da140000c00e9221160f25909504681e46d00c06d5882d01d880740c004006c00d40c080130b0164094442e03e80c000460310301c2040b2180075601265039250803100a5804019100e0704224124180807003404544010f03100d070b102070718840d0151042030906040840c0090100c440103810024503580400c070600c5103035000911004003142c2c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 226674955 1250 226673705 226673723
    0xc06050703032306030d0c03080f060118060206040201031503023001061206060b0a0906032d05040b070201023c040b03010305060c04030312151a270904 67
    0x500d0110020b06000908000030b040c108010b40c0305160545126104c0c90081c1c4c1104c40092100b481a10030400c49840100015a50720008515081d03600d40703030390400c2c0181000c0103405100030900d1401c1d4001d0300f1450050340003500300010741d0b906004044000d070300500045a100d0554005c1114210a4025040c03007090009001545e005d43d0204100046500c5000f04107160701c401c00c04c05800d8200360103883c0d0300e0030420003142c4410241c044035000380b826201c25000600d4036405502134010a00622100500a0214003003207400205424030312000c92400070722031a0510340300d12140e10250114045a1044c0700d40709100c1003003c3d0701208043c07080c1100013132803540d05100c01d02c0403154528420400010500066000c00100651b0590303104409598496403403001a5000d40520320026001910b0307907242d0740301810b6652141c82c60b1420316410311000da440300646a000380440039441400840002c5094112880e601140710300c20400001a01260000340004e00100002d4000307098026 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 226676205 1250 226674955 226674967
    0x105040b0d05070e12010b04050a1401030311030c010516110d0504120204060302120109120e030606090411031f0b06130b0c0a1202060106080105010f12021308010f1b0c0c0605 77
    0x8041c4207000c0b0340160061488170207040c1c0d510203901070400c81d82e210380910708001c0480e8032400d10740915035050300505c94001d00341e880c50b1002c8481c000480071500e220b000c1007080410b690070a0043c20300c101e40042112896070080b000050104c3c080c403207140c205400000304001c859030b2040c01c49007141c14003428000404410f000040042019030720095025001c4010940d00c218190800c03c0c0d1180503400c03c01d0000001103064410400804006a0580080000812619055008540090244007180220005030b8013192a014501416643e40002c1001005c540d80c0c0500921445400903125141817115200c1400908681c50084152001010401c4111004204044a0701c160005058040c124009201a44990080c0a0030300003c0d0b0903400410f15500800c1c01c05550380069440c0c45034500c004c000a4000d4000e00606100e0540c0c1c1240010900c0d02406400c110080d0b03010000b610200c03601580042d80394503a01c00041c8001c200100000c5800d00c4c1c0030000b2180d040c184990703521 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 226677455 1250 226676205 226676207
    0x501032301030c050a050901060915030f0c0c210c140a020901090501081603080913060503030a0315050102010e030d0c03060b03040501051b0c190c090c1205060105040b0d0507 77
    0x11940100301548500040001062001d1943c4002c1103520075145184400d071640140015501e09000f05004580005020001d404205046550001e0342c0e281c00030320b46038020400ca0540d203c44040c00001400b0403e40002d001c02c1030252a14828003102c02c40500191244c080c001c4030310210b0180004001c0d41a0004214003441004a01540280b99440b40c1da12103020304001d000c20b00441005110781d48910134200302c1c2d49844c2041d02e0700000301c141807813580700400818088800004551588511000801c5d45042021f040810102d40f4081030107044400948840d9080d41d01450440e13041001c1280d04000100031039901119403c80401d0000c3c2515040d4003512150380460b00225001080005100781036000c0e40c05a010300821445400320040000310301e00a0f490360107c150443e00c032407401d0b00d10000135841c03d4cc4c450109101c82d00e644080040031100082e4410010a05140100301f400010b0310070709920040c2400c0c047e0419041090f04501c034014080301408582d83c41021800003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 226678705 1250 226677455 226677491
    0xb030c0d061503140705070f05100c0201020702030f1606120b0312070605090a03051c0f020d140903071505090a12111005060f01050f0d05090a17070309050103 70
    0x21403000000d01005540e400500c032071118284081000901e40309081400d00100c519282c001c100790303074425081c03059580350540443d00034032003140e00c2e00c075400d0b5483c4004c0840c007a843d03601009800058aa040c18014582442d414400c040141e800c0700d070380810013062204100d01600c030780d03190046e84614004042c80003400079241d8540d044c8158030100014244a05c014100940303c0c9600f80b20507100d201d10540e640e50005c50040100300d0900c0944a503889a80051411848494003c5100740007202c0d940c0c226440092140300c020744403400d01c0441200000200d800c8540e80008600d000841d031105030f0922211581009100d031a8000700c2c0034500708100c001c403443e030000204200107201c41c0707000d814608001a402068040c5c0b81c0d0201094000d403040c81d108440107407842c4192544a40119002d5001c060a441c1030013041c01a406040030f00c1c0302c1c4511511600307008040b254000d081052010b8402d103940d42040c0c40400007500003d61104909044520078203010824092081c0c6c80108 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 226679955 1250 226678705 226678717
    0xa020708010e070f150c03030e07050402120a15081c270305060a090812040f080c061b0306060d09020102070b0a020102040e0a0b090c030615120612030c070b030c 71
    0x550b007800c1c1007102e180070118a56003150596006040000d540b0381802810003603070404440454641091304012900075008441c0c00c2c180c1105807420951030f00002403c0760410340d20702a100986c2d000300501105541306644900407000014101d40d0303e4100019510781c03d500b04040075110400081a43ca8041c20134a02d09101c5202845490035a002071905044220720054500b441800007194080713040c0d01c501e4400c0c0b508806000d1900281c1051982188405002119140070000754a00410440380203085480c1205001c0c1030f041c1402e414500c1850301c01c40c00c80518000400620106907100c0b0b003180c00825454001103012100ca000503418448590300541c46440c0004e5602041c96042d1b00820984140c14003001644d00c0c1c240e06031040f03444003004550000b0010010680560080002c0c5a0101f0010320000480c000b2501001841c1c00034005007600140030011f103d03280c60a002c081301c0c13110001c001503003004074a808603583d48a10b44240c0700e12020001c00305028043c2e1702d0443d41 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 226681205 1250 226679955 226679969
    0x71713090e100c03020304060f0e0a080f130b131a031503070512010603022103030c16020a06080a180c050d031205130210020105101401030e1b040b04050105150a0207 73
    0x3c400e00100c80a000380d40219000c032030b901d14200d014841c0d40c0051003440c911a004900030201105150750305c0c10ba5a004000752041c0303510038007114a0301083c0c00c5010010f050409019500c550000242c21150321407600f01000b40c001000c2c08103c0c204010b010f4a6200ca01c0500c080e0410503ca004a410480c0c103412881c0c200702508000741c0c02c04015000725041307a2003507400d4222404601c20040c10035107074041007010394004001286a500714140036207a04548000c01720842e607969400506010074962054000c02d2001040051094240c0f1418120558010000c51a00402c0e51030344404440c40c0981803046002e03c003074500f450f1246a07031340c00c0d47c410040c0800039828010101ca241c5449020200d1150485003424103e41d807060142c3c034019196106000c848504100c001510680c035016030314101070b0745c1c2c01e10182c141e01c200441b4400c2c1d4429560782d64664002c405100596400d58000c43c0900c0c01c250040041e03482d8102001c804d0103000001548500341c0c4034003241004200d0b44071207 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 226682455 1250 226681205 226681211
    0xc09011b081c0e0f01110a08180a03030507031a01020a03050310050904050604050c1017070e0d03030b01020708011a060a090308042d1415040f0b071713090e10 70
    0x8001104540c40000e10603c1d032021502a821880070980c2070761802e25402c9a003010501104e030340107010b156040c1c0c000040000d00ca90070701500342c82c149802c2c023040003500080c0e1110705000b40c0070380621400c1c65205500451170100894400040d542d8095405c0c0107040003070000004078203801c90014940540300007031520f0f01d982403078200181d89110586054030140130b03040140c10103103004c03410480071400c181c480c442c0208100280204030040202588103014423501001c0c6150b64082c44840e03060302c252400540c1c48400b03000207242c1b62580c0c02c0f904440e807400300c5003440740c06a142c5c5c054807008100ca8043c8d541e01d00c00c00485030f0180302d9200409101010078003040d60135042d51040202260145000c2c00d03004c00e188004160a0244a000e41040302c2c01402c881c1030401980c2901000a4141460f142c2a42d072500040c403a4803d620184404070701140000030850043c411100d0421b0020001d400d0010706072066112000310b11400701143d0b0780d503054a501e10424401010740307040703140c020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 226683705 1250 226682455 226682497
    0x1d2503030e150d0f0f0c05090901150215090d02010501060e180c0f120103031202030c0d0b04090503130609050a031a090c06070803010513050405030301060e060403020a030c05090c09011b08 83
    0xa403015014040407402006d0400306158042840368081d68000c52004001d80d400381d103084401f44950040704104400c501501c40304080000bc48260240542070300f4004114140b1407450003401c451044c1c02c2401040044400041641c1d2104046441c92101b0300d05c1c16090344503c0c0004a00d071107440c0c16510510004140305000320f034601c8080341200d00030386565180c48128481807040380710445038000d0341101400046130400f156400003007816400352000039110040d869061540d004031001014485d031441d01401810b5000000340300030101a03c6400981c1d0466961b0b0403e0403c400c1448040421700002031f0940100300007a8111701c2002c0c10450355040c00742000c0006520901803203001c1e04000d40000d030901407900c00c403489250841c0c051400d507400d1103021100e240c0c2d0500100d41c4100140000b2026039121403603031004510410b82e0a41943c40c01081c003a004c0300c001c0054196420901c41840180d03040b081e08030f80044009100004080c1d40d2030080914000d040c08500905001079034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 226684955 1250 226683705 226683731
    0x1803020d050d020d05070203031204020f090a0b0109050f030c120307080403031805010f0f0e0d05060906010e0c190e0402040e0f01170304060203070212011d2503030e150d 75
    0x1100c2c070400aa40c01d580007062501015034981c0700b80d900c001e402d139104002030b103d07928500300d209401601c01803400e441c0b90780e01000108070040994100c40560b40d144145001076030003600c80d01c0188000c0e0b074454000d0300d90200180c0c0307a0f52100611409000305440d09802f0940500072106415031042145031150340341d0400038001c0480b001a095000d102980200780740d0f010314031040040b03081d5071702e0300840c18035118112107041081a4483d00148018400400118148051f138071a9140200a040641c50035846d04c03840c81024089908803103041100205010015290b81892012800c103510161580004500280704551006c0c589007007810511050300c0161404904882c802d0000342c07490f2040d945025104d2090348039190242c0d108101410060a141d40421b1000005000014a03199060409859050201d154951a17040440544a903504044044804034003d03401445583c0c20b581c0c024003601d00042042e807113140a4005180700c143d110f0100d03020012410003d00c444440214 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 226686205 1250 226684955 226684963
    0x50106030501060e061f020123060a06050c0601090b1306150210022d0405151e0a1b060b19050102060c03071b0f0206120118110306011803020d05 64
    0x8407225401c0040006400704803407080c50144000900741080381800815801c0e4041813106400159525020b010342d4130303c1b0f030100024180f00d9500c0c2d0a01c4925114003006006c0762035030004014401c0a0040104414000070000e05455801200046404000c0c0001b480341c0031402c81d6070b05450074030001141c8511000d080c48198881a02150700305a40c124041d4140c0c040c240c1040c2401440d61620444540c070750b06110422418410b06a00e01500c0d040850500d041081040c0307040a0002441c0d4007801100c1d070680034a86010116a0130010f04401c0140b072488806081e90b100c12007084100144141c96000f0240200c0091860143d00c0c50b40e0078000061440d8802d003170241c0540300004410502c010101c1b03110749640d90300c40c0140281c10307001d4a566840c90a0540d10014143c00d000700584034031004118020800c54202c00a40c0741400d0140c0c1c0035403c40c50f030002c2c0c03801e21ba84a4040088002070701c1d0008400d0800e52140307144400e0185021400750b001030b40c04402d0001c10b40c18017601207 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 226687455 1250 226686205 226686209
    0x10060b0702090702150a1b0e1c02010c0605090c030f0304050a0902030406020c010c0809010b030c0f01140f1303140a0302070303031808040b0a0219081e04080616020c0114030103080f0412050106 85
    0x403e20f0038074240300e02c054441101244015070056171100d20b89c01c0302d5401e4001e000000e841410044842d051a80310a003c450003102c010041c1d5000070f0f101c000314a030070001003c440d01e540004503d030034108000f244105689200d00000b40e038000c4041410802c254050700c0210030820001c001740960010018262101910b000c00355501c0e0860140982c00c001c111079480320001352801400081d0200116803501d04d000540703590b500103200820ba6000302c0d400902e00c200b00c1070141c6010314154188a88000510b0303541c4a581c0d80035526440000340c0200c0c10900b1240c050500090103100b50003178801400c40041e0081c202107000402042c003180420103080c42000e19401c4984215904800c40d00d4074030648009403a0050500c01180d01c0020340c0c3c40c2070300c0c0441c0c100b81d450915982e40d02d26482c0400036982e40540c0c080500300490120b5042102112174142468106001815504800e40342d202c1808080d02040000074013140034860300080710000e2006092100c640c0c0640e09016000344414 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 226688705 1250 226687455 226687481
    0x90209010f081e0a020904140c0d0b0f100504090b0109150f140102011b020a03021b0f011101060f0308030412090302061603020f0706050c10060b0702090702150a 71
    0x10500204412440320908415540c800c402070001080400000702c1101c061500f100e881d2050003420b0005803180303500a4020f510884860b001d040514881d14180402400c1d03090080d00100c07009004980622895030f000000004402c0c403075256060b403440122200d40081d50800e00b4a44804104290300c40c10349d040700d038a00420400b20030011008160b00e6880c0c89480c10701001601c09000700c4040040408820034140000211a402a041c400380644103c1c8200c0140c1c00c50300b89803092640600c001900400e800288204040101c0c000030500c00011440c0d50403c05240100c8041a900f548510040c0c82c01c1041c554009950b850214401d81c8116012a11110504402c00da1a0300034281321090303c2d8010a02418034020325214400d021421130244d0840c443c18040c10041c030000d0085102408056a50b16965120700800c540b604001641c2d1040c220301c0c1a00400400c2ca09505403450143d04460648240e19841c1003245031004200700c0f4003194544105002c44401076074001042c80841d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 226689955 1250 226688705 226688719
    0x10050306010f030c0e13020904060f050702010605150a090f0e04021008060609010c110a0303200f03070303090302030c0d09061106040f02270903031e04080712031e0902 74
    0x36100b04901c8007181d0321000b0718810440c2828402c054103441302a138040c250800841c180d050320340002d20303081402d81d41a10f2184c2e1b540c002940d484928041c441c2e004007180001c1c05050b103881c010039030010501d04180420f00020600018442c481c01c101c030001c1c2680d902189882c0d07204c800300109500240c804030b2045419600980c00940501d681510900000340040c0c1000c00860040d29035403002041200e03103103411107594802da41c9a40b140000345002c0d94844100f066000545c90305580103111300c800716404140d003a00e5031701c00003044030400f550524011890742040c1c40c05a00d94000c1140381d07003072070142240e180341042e40500070b2400c903000c559032500b80e48100c2d4811078445400fa903024200c44071100084000d4105252002c8680700761864040189144040900d40403900f90740d03a03000b641000041c403001885041e142d00e04041c0c4050124503a040540d40c807105403140d090f0041ca0b0018070388010044a0080e1300c00c1c288825641303494068540f81000714030003058079031022403003500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 226691205 1250 226689955 226689959
    0x6010e0102100203041202150f010b03070309060f050615160204090317040b0912030f1311031203010503060a0b130906060f0b0720010203040b0f130f0821030601180b031005030601 79
    0x4855480b0358049c2c2c08040444659034200f00d4610681c0d40300078110014907495250340c1c00080c02078454440515002203001816080000c1008400010020303494209402030001d0040c2c0216464600692503040328000f881485034601607505002c901c50a1648851a038200702c14420306032503061190440100355040860443e400700c0d0240410b0725000c0d00c62810300000380ca0002403981110340c550050101c03040c000039010001c1c1c80d05680000e02444403d001c0010404e0b030404001107134010303051a005100c098220380110f2070a101445030700d01056101e801c002c0500000c0c2d0302c0b000150064030640442261641e0454a02d680701c05006c070f52540354560364500b466028484600c42e420140e020310b26080c540301c04503400ba000311080302c8044204012a46107003a18070940e200405075181044841c62034900c0311030401d828619251a441118141079520761540b8040780d50048090030051400590704a9140203d18190040140d101d000402e00074080400b00903001103410803000c40384a40c0e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 226692455 1250 226691205 226691233
    0x106020c03010c0912060618020c07291b01052e0303200c1003060e0108030f07020616050d020105061e03060c09150d0203060a060503060906010e0102100203041202 72
    0x24003c11000c0001544801091000c0401071083c445268080c800114032a070b1603c44400007020110704002285030300003244071031100148401303002002510048095030070384001070703201d0507444d50b005607820100080c1200e072541580442c07150100303194000c008501c0d140c1c00c0c103a46482d05a915080420311141c644841c0b400992042055079810394810b05d00a01020403584c11134101c0c1d049070b445004080c1d1400c1c50782c075050f0f001c80d03003107505035408500d8901d00034080c4007029060308050032030b40003005607008074074034501224411a8156292070f030b21400071000500840340c803035006003640155032a2651195054010602804080380c41846000d0307070358410000544030325911a00b58020a000030030502081c0040c0c6503840c00a000158494200c0d50380d1a6150300407031740800c03929404010301c003090900f00000c0024100c0c904081c0d00c2d60505400107200c100c001020103040103141410030146034401d0020103540d103583d40041d0340380d003010b00d800000101c3c03070380b9190010703c0b4910310300c00c004c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 226693705 1250 226692455 226692461
    0x30605010608250c060c120e0a1b0b0f070206070b04031707030c12050702010905030a0306091802180a020906070812060105130e09030405060c030a0e1e0409110d0b0106020c0301 78
    0x480401d480343c2c40b13402c150b81c2c0c4030700103404c408105000348043c40c01d8040c80100b031401750f8554015400050106150989491a40400104081003040040e00b03814056401001c0c00c0f1501e44200b044210f449186500c00100e252207840c6000b0000b01000d07044c4070401d0b4208103521015149001c00443d1540c40d8078084044501d16002180014031490f0603204420190748180d400c030509100104094200e6140d040c5942d1140444100080e81c0343c0c0e04010803c0c0d14800c00380e000702c40541c0f00c001d180031074000560580001054074446a0a030010440c10380e59581100d900550141c082501c07003249003084542ca0308100b054402d03906102c80021040c0d81314500f01d400c04043c0d402403d240508000c05088400c000402c210101d00c001c000c0440c155958001400d01c00100600a664500c40301d00f004120080d180c00941c00360310888404078030140d107040003000140081d200081d484405040016803440003011b8550400000340c5480180004800814180c2d25681c007164020100d0300189400c0f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 226694955 1250 226693705 226693771
    0x501030c0e0103050a0635060f0c21180c040204051f03020408030f09010e01020a020109180204030c0e0609071b020405041505011514190c0507030605010608 69
    0x901d051002100340d0700030750103181c1001c221140000c6c82c944410f010001c03890b0811101150700e070720306440d060b5042000c0c8030036001d449001c00b0780a2410018015000000050702c0f01080790b07404180b0b59400e40b925841c203500b0001088410140d400d140f0140c40d4000e2120a082c0310500a07100899031a00300b074004c5030200d030006000d0b1050000c5c0903400002c3d0080503140d030420180c08010001e40b000d81040a0260684405803007642c4058070303000034140d0381486041c241550040b01048001d41e8101180d042150500d0704070400301244102000000e104641000389107009a480124040d002032400d14801c0e0019904060f242d2558542544c043c85141c1c6040582440b508510b0700504042c5c00458020b4411000340c01b118210800d00c4060f18401d820200002e40240c044490305603106203d00c500600701c64481e0b1804010f0382c100112501d00c1c94880c020301004811207400c00104100e44001150050b40807c40303940c4805c002410001c00b51940d001c0c0d041043c0004012290000c0020300d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 226696205 1250 226694955 226694957
    0xe07060e04111801050c0f03031905060d02010e1201091506031406011401050901170f070e0f0604380c01050a06050108041209260d080717040c03120503100501030c 72
    0xc043c11010300110380c1944841c26541084c000ca080307826491201300051030040c00c0307400140c2c0d510303c03010031400d084910003081540705206901ea46405070345c016001c0b0380409001c2d2014004804400c0f82c09016000440006218511a6400c13045400103544024162485006003c00c02510410f004e665041e0a00942d81020303010301c2190202d6010380b00400c404481030401d81061104104d4403003403040300312101c4180b8542e1000f000b52181d8008201041c00d04225807211444045001044c51400385005402400b4141000102e1041c20b1555181c1038000001c540034940c81d41840401150b00300680d2829958240030118034038102501600c4159441070b941d13032403140d03035070f884013074046001300c810354240308e1803020204008084480011003850040d509000307294000c500c15141413280c40018040166501c240082e00798001c109801c4040d101d0b200000544540c140320b104510140e0006000e01c030301c1c80b040c115284d000000340d403080784c01c94104850290394000541c207031604119948 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 226697455 1250 226696205 226696237
    0x503060c030109090c1a1804110d0b2103070b0106020601030b0f0a0b03101a0a05150703140d0b010210090302100f090204020a090e090a030c0b07030e07060e0411 71
    0x101802545611403012203004180c0c590400c1e6482c1d00c05142c2501d80e070100110140001f4940b2506159901d130000e2844040d9020005440c201c07400458070701600c0001011542c4465030005540d030f414840c1c484050b4040703096003080c005420815501e600888045034401030000001901c0c50001c50020f040700c0d0040d2100000359100703804d500c8070610042408001d01d07a151401c601c1a01d0030462440a9030f01c5020002c0d00c01c4428008206103800b41102074454031016005014075111509419100c6400c419401c0c4c440c10786250a40d140c0300c40c101e1071800c07951301181ca0501c42c04a40c0008a805000fa02640d50b001e00102c0b1003415240740640140c090313441030008542203100c5a0003805040c2c0300060008040c0e409500107000da80c050f1105800160300d010090080450481d4a81d810105207001850110340f1b556024106250026001d00900300381c0d80000c00d4140690060021501c51340c082d1051180c031074101030301a580380c00000b80641e01d000444001d16425104076543d080001d1015 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 226698705 1250 226697455 226697459
    0x10305030a0f1116090b040209060702040c02030f1210060c0507051903060204030b06011407110d0c0315050103031b050705091806090a02031203040b041502040b0d050609010503060c0301 82
    0x1915880a08000d0008102400c1c08044403100207100700c9200310168070304e8030982172404004c10300703850005400ba0300c114410800d041083d504c550880d0010356040c0c4001c034921400d150144e08500078081d51800b14040000c1c3c040160ba81801039510440d8854540001d41d84c4602c001c441c10001e03800005d284d54007280040c072152a101a241c02c5003164600000c0c103103601c81d0b54038030581e0466402161140d503100107004d032641c2c10019206288810090860419140e52140001c0c0d0310741600c1540502d64582d00704041c800c0109200b0084c503001441d0324155a5a61614002044244070503000552250910424113000b2090f800b407103a000700003030240c00c1c2031104201c10054007812005541034809841480064140192441101c03c80043c00302c902c59401814101100b04100490311002001084002080000785640080d08030082101150007402001c000741b003190407485044802148080d61110150040d500c80d9005407440f1031142d0303907582070554420f8295180380030f0706024401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 226699955 1250 226698705 226698707
    0x140a0e0f0307050303070602030108060114010909022d0a020111030105061b011805072409090905280201031407140f090a030b0106110d0e0415030605010f030b070206010305030a 78
    0x440d504918000e080d501940d50b9800000d14503440781000311811070700071004110315101440300c1801408091920307030a41d4005400242118524040c20005d0355020032041c0c41e181d003081c070440c81c07222540c1030104600c0d5980e016501981003400c09400540c24800c111840d6841c0b00b05581c12100050242c41c05d08140155039062000180f0001059668924542680c07003204140000c1e181c0c0288040c040d0142040003459100160a07800d850944204c03240c101000d40c0b060842085035200301c000031f00048186031240c108508900100344086281c10798108030011592900f00700d5100742c0342000a190340d550b820848103011600300000ca81d0443c46a00000482ca00502d80a181b050003180b4081009002881240d2150800c2e60f100390100b00503c0750300c1c7c204110403500c4460400074070790038413540e4008060200e4407900a000e00e072621a550365020507440b9083c00b940e440a424800c6684503440306c41720303034038910003982c86000c0031020851090020403260305a03074100c0055881c162840030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 226701205 1250 226699955 226699969
    0x9080d0e01030b06030c0a09080a020604030201030e0a120306080c191203120c0806040b030c1f030f020408210a1b020d1406060901081204030b1b0a03060303140a0e 72
    0xe101814941c440204080039500c0c20001c62084003001c2045454450b5030070000c22041a0f9084840b465028581c0c010242e521203090350100c960900e00403c00c0080c5284103070904a150500a1009169802040109800d07401803c03e87d06c00d8411500196101130800c03032150300c0e021010040c0480507130184000540a55404071150207030910100701d02c040c00005003215000a600c100241111040c84000d1500f03001e0383c4001c041c201c0040000610a00029604c030030039619030001d04107086042540ca0b03010390412120740d070000c80b08645441e075680e0140c0d1a607400c4000e100ba9030042050340e0040c503030500d0036503c035000c0e40d950f20501c41c041815410b007039802e004020303a4050400c14081d0005035a206000043c10800c5028210500703100c4280300d40c548042e0050f0885802060842440c0540f44090310b0460f50011801c0401e91a4404900d084d0395840e0000d40188000240710f00d0794580603045581202d1090303a42d0800c010600c14540810300403001d0201c002031102c00790601a140040f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 226702455 1250 226701205 226701227
    0x15030a02130810050105033d0e03280906080c030705120108010c140c0c010503150d050a03080f19020702040b030d031e02070812040507050a0605040e0709080d 70
    0x7454500340305440d021810b00d04582e4031408001180c891006000a0030148415000c4030700c44480b6503443c000810390460003c03117680340201c0c0916024034080b400d01454200e5440d0b4481a415281c0d10741e500821100e00c1d804468050b07004070740701c1c0080303084140300d03030b4450003126a25030301c00020f0345034a00d080c80f11b9071010303244408020041c085d44807074a0250018a00030851000000790a440c2c50030090003903402010642804102031256000442c4040f0b583c0058080c240790071550f0b0740c3c0d07c140d0301c2c0d00d21000010094101e0f07080034180c010017a00060300a400340c065160030040340d5030142d40c0103258100300d64801c8160a0540c6012100e001d079000750050303e01c0100003040b070783d008102080c80c060081040790006030300c0c0c2c1c1c10409041120458810160801d803c15441c0813010b807220b03412440b620750b800c06403c10320130029081c440300b8000e100c050000203058421043c0d030342c10010103640050080d0105034000f600400c01c51400340500d0002c40720614003600f0141d15822007614411052 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 226703705 1250 226702455 226702477
    0x60610080403050c0303190b0102010b01020705012f03030405060f0103030c0305070201020f0f0610080303011211130609020904060905040c030209070e0301060308040e090706081f0302091303080615030a02 90
    0xc0c00b084d81e0201041c4050340c03154020443c8542e9143c0708030101c01c141c8c0c0c000e03040c26065900d0906201400d903404191002525001e0a0032805c903c2c0c1d104541c501e046642403252a00a42c011300c1d2010954084021801340c5c1c00741301254202e403103e500704c179028002071100030b0105120707658801c00680201d01078143d503401401035442c2c0b100c1040708582030482411058903550411803c2111340301a4440c0c070006812130705c0c000d50540d07040000c031010490100300302408501ca507100c8a0441c0e541c0d450401c1000c13400788028490310727944045003030194014051452103603080c600702003214440d900c6a5480360f42c0022101c85140c0c0b4540a109220b80098590000c00019502d580260b4800340204801144a0b0b03842940d128030341642011110b070041c0070000284c02c000410070840b503000829a4018a010b0058181a80300f808080003d924a6000940240b410381c200941c00201c01c1d004407415000b6240d00100d5a03c00c0200b20105518500b83c00c2d422400b40040f03524502142d0207040c4201c40307 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 226704955 1250 226703705 226703707
    0x5061c050a110c0a0201080106051e0708070219050a0512030304022206060809010507020627151e0106030b060f0d06030b090f100c0f08060d080c07140306061008040305 74
    0x20b0003500215400150110305950101400c04211b507417142d0040c1c01019640341460401c1000120002140c4484801c1c0d0b1441c1d2020403600d007444802c400b15000780ba402082d810803020390446c00101d09155105981c400e20f180440000d0500345000c0c15628600c400000e5440d542e225402c10105621511070228516004004c0750b8400d49030b03124000c043d00c6151591000362a01300551420b5904c02082c847c04c40d0031100030300c00c0d800f48e030000c860518200388140000304580d04c0c0d02c540ca40003040300c034400008140414803ca910311640310724042d042061010045a8035a0340603802e8039005c07903405030465410005401250b0075000601200248280b02080c81d42e500c1d1a5403d62000588801460380c01c281e010603500d40c0c08000200c40f20700b10a1050005110b11b900160001c402240e500d0140306c02a8001200c0d6500c101644442070780c001e0080752908102070910307540f00000e000c3d441814007054443c030541e140001e80c8030f11680c0020082e0700e550356854130440b1000b1014104600b0712030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 226706205 1250 226704955 226704971
    0x50915040609060321020c1005070b011211040605010504090f0603050d020c0315070503070f0e040507020705030f0102031519150c02040614030601142404050a05061c050a 75
    0x9118041c85004100304800403950b5800e50802d501030071945080b1081000340d69000000ba1500850080440d60007101c601c81121480c0e035082e46c2a00c0785120042c0714208440021075a000e803002011040d5015129802801418405000450303115019141c00708400740010020700e94290840404000c0c84240030070f200b0783d69500c2e00d01d0b040c5690001d602580159000c4800703401c08000c446503450500d0102e128500706a01c0c068113520000d003201c0308109110109021060080000000c1d00a02820400c402d02d480308000751130f006c50b8091701d0711a00070860301c9108100140250390080c007100007201080e10040c000c11001180d844103c0c80f5820500c800058840c81c44010821140025110850044c0d118810401110140d400045943c214001d08107000c0e100002c209054825840d40c24080f0091040041c00f11408540c269040c2c80401036980c0446c0e5451014104841c81599410005501c84040000501a82d00c4c402c0d541401c0c44181721360300c40690001c9400041810b40021195 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 226707455 1250 226706205 226706209
    0x212010b09010e0603190b090c0a0503060109030b0f1603020408100f23060405060a031e0204110412050705030303041214071e030905370e090f010c18050915 69
    0x2401c21180c1b544503400c1080070f85881301180c003d150110008850104071442c0006524544d401003031310140c1003110100028160364050740082003c1d41d0000c180b40c1c95860b25081010b80c605003201d11160300841c0b507000d8200e5900070b0081c0d034290344088014081c8919a038590304000c003400c0008050064540125140f5210010100b0300c0552290317134450010300e03101d01800299140589000d004400300c140410200341e220100400004084100c07503102003090000402410318103810302c2c2108000903000801d44840003002e00d415120758292130009641e0300c00c0644a0100b1240501503529161800c50a00c0c4103112030741144071685405414841140c403000c0308442c00c0b5040c0148101c165500c1014180c0082020004000031218200c404402d100c40588140350740903120305403413000600c00c15000c0342e406164081e04408440610601d030840b682a0b5810801c00c1f0880c86510300001401060b10035502c030300d00e00c507000c1c030082401841c120600280c880c00414108034900349561510a030303 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 226708705 1250 226707455 226707457
    0x80a02300607091a0a03020d06050406080a050106050307030b040f06022209050604050103110f031c020a030f02070806220210051305060408120a050d05131103010212010b09010e06 79
    0x1030103044000c20451500c00c0d0040e00d0207945400c090100c1c50800d114100e02c1c03003540115422041e0034540941c80704403007a100c0004d402190000b9a1140c2485004102c0e81000210a10010701901c001e0050564400905031120080c1c00050040c000040000c0d0100c0c1600d921030b91643e1103010b0051509480c0c4100c001490700558418000138601641084401c1c150301405401c41c0702182d0800013540b441c2c2e030b034940041140460314098900d0b803400d070005540600114042040109901400000700324000303444031802e4a00f100410a230100d9030004a1001507108107495040c4010040c80d100c0414501d072521100b948507003103000460b80640144c1f240394217038a202a07240c4456803070350454070307200d58040640e070042800386d8800e000410200c1c2002554114a200318031002d035032034601d148121002c0c030591a0102c8028200070a2210088040800c19640c03800345e00107406d00380c000c20400d030a034414286600a115140070040c031008440d48014440c01c80e05040440c00c49c1c04e000085041 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 226709955 1250 226708705 226708789
    0x6070b040b010e0702011e0b0d0c090506030d050403150b0a080d03060e0702160e040f0f0c0302040606030b06030f150406090b04050702030c07031515030501020304030f09080a02 78
    0xc04a5071000422541510700512600440180000d102c040801442d00c3c13203800311100e0070307081551602000d4086440d041d419030100c64200440a0140343c0313900a107400b6003030a0314042d0003031190507581c0c18581d01c1a010307a401d4a07400100880c14984d0005194060b010400107a83d1040320202c001030b4130842005000c5070b051035600c001c121140f801c810035070909402024041550001000354081e00207600f0141c0035101d1700c140100790384e119410800702d00140680005d101d09400c54444003800003804818085a108540521146460350000c8041c0c0d121010300176000300c0700707201003100e0800d00000345a12036100c030382c200210800c2200240507194a0340c072040c03a0695560320340d0030350300742806003e03032040305030008501d01100c0640341641c60441d03102c0904081c201c982c40c41d450f900b05800960b00000414024010036880f41441c900035401a80c08a0100d0b80e0044d040520b540200c074490308407040480035001414a5400384501144810039000101031032800c4044101030020090070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 226711205 1250 226709955 226709963
    0xd0e03040b04031101120509210f130801180b01051c0b070507031403090d1107050301090b010e0f16030b1306060c0b0a02031006050f0c0106030503032703041406070b04 74
    0x21101d41103400140051b4600d40882c0f2040b4248010400701140004a45001c1c9400058603402c4d02e2160081c107260307024007800e0a807a81000030340004005000b40c82e640c280c58181e802048040b100c4480c480003186c2c2c1960041254040304010402d91401e41201a80c003110800070318445411590748244c00b400444011002c164040790030801e05900c900800c1042c002940314501d1403c0401540e5a03d84180b4220420089240213000e240b020070712400f40102405402444503007207a280022298800340544941505480002005041c08a180790b0040e041c5507200034007050a210114080c100d00c0c41010740110450040aa203c2c1c01c51190318020441541d4010384640c0398030b0700e034500c0d590191680351940e0051003800548142c407249034045030b0890824555413581c060503c0001d0250342c0d52030000c1c3d4a0600004203000c00840254406d9481091045c95645a00000340d80107281004100c2594028441409000d41c0200301240090f0001d0280d410030030f40d42e0760b02481c84404c40b8104c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 226712455 1250 226711205 226711223
    0x5040303020d0b030318091015090314010c12150509010e07020c01080c25150c0905060a020601140a0503060a0218060a0e300c0a090608030d0e03040b0403 68
    0xe4000d000520802d140c1000c04c40c09107280c41009032104000403180005640b003420488003281a0701d1105a0f0032005102402c041c81c145c40c90396001511790b2041388070587e512003050110110088042c4208078617114243c0b0380e140030392810580c58000704a4113122041c0c1d003230490303000b2600d541c0e0b000d070302c034002c14103501c4403146440c00280090420038410542414000783c8003d1050043c0703d00b064074032113946481d0145243d070007011f1002c034107804c041001d000000500c4e9810003165058010303440401960b02c8110b5941d580e6403e000b1940f10f1200f810700180c100070010705c98124032707071a00c5580d904020504003406455030b000904010003925212041c0360b00080411039044c2c910b0796420044001c1340c10f071341041ca00440192800d14a055010711800051072040304003c80d00304103110525080101c03880700c2c03a0442c040d6588502c4008034a20868002500080c810540d006590550704008044c500b4000070524140290070a0709031142d007400244404176203a107107100a400114040d503040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 226713705 1250 226712455 226712467
    0x180f10171b0901030c0306020705100906050f09031903020309070312050a09050402090904141218010e2b03051c050f06121f060302040e03090a0e091207060f0504030302 74
    0x1440040481da00e4550080c02c0b03060042001ca4030031840c440c104c030f811140141e51241540b6205082811400c107120003545071214a0090149541c0554824100d060480030103031616604070780d83e400382000984c0310700c9020083c7c4105034427035000356030020021402c171094581c6039541c441500094440c200c0020358045121210789510858290003048241c804600c1d0103002008210005401003001e48496441c07264415031410800c811056000359442c040c0d101c4105210103420300e2204c0c0707006030024290541600c1036103440e4591403e02e0301e41890100040c00a004480101107a00c2400d03814032030184404c42500da850310312003881c40c0c0d5120b000074a606e01046408446840507204030301031086010400100400014442c180c3da2510010b1200c900c091000300001d0902d80e003009401908100740b0039907a00c0700001400c40d001048513a03203181a00c410101d88201022541001a40c0c0851540007409040b4002841c09601400000c034910b0440064801521002d50b02280005e41c00030746 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 226714955 1250 226713705 226713733
    0x90c030a021c0302070b220906050d0f02010c1506050a0803160f0302240109060b0a020601030204150b160203010c0807140a0314072c130209180c1305180f1017 70
    0x900251188c0c020400c8000d0800022464903102c1c03010007481c4030b40f007031650820741e8062410071003416805950440f01444840d00807015280c0e038410780b40074031081840410003520100c01d030386000c502c9011114120b11645c84210100e100d001094096015034004041c2c0b40d501c040f050501c07441d004c03100c920a03500d802602000c64406a21608405400707020720038045c0d034085100c504603a011140070070a00710f048140000b022050748060300e5802c0001d040803c1c3c0c0c8400d048808418000c0b0002c00c480482003c01741c07090131040780c2c0b480001c0c501160302e85003100c800f400361020340210300d40040d002c4040548580d80d41f1003030b110a804105039081070311070212400350301e030807800440c0074404050701c0c00380101c0e82300c3d00c0451170524007903004268044540c58010342040583c00212011029003001440ca036441d90000d608580c0c054640000401d0710300704801180c00400482c40d1000040d600c050180705044409018203110340c6903910001550607145181a4801c0400f40c090000340802c0c00c5c0d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 226716205 1250 226714955 226715017
    0x408031b0405060a0f02160303030f1107020306040f080f0a1e09080d2a030807110303010e04060207050705041b030518061306150e090c030a021c0302070b 68
    0x10150040d141000184480d0b181c12083c2d402407402130400300600500250180d003051110f12076201141c1c3c080e2800018507600d500701161403503100c44108001076442103044802d11601d407000e50143e100801041c006424052003160543c0a1070202d801c00c4180c02400303400744e000c5004030703001401d6048202d6800c0c510700900f012154050401c4a007140c5444003150b02c4019942080f0107000040807480100b022110750300a203201c810580150b03400740c0380b90190000b003003520500001030101c1440b8800c8a000000c5030706807130858000c8540d42c1d60725500c0c031000c0d606c51401140c1c035000e224000281900c413405030240d83c0d502c40d0b050155103020020000c040302d0f40140315811a68040380c00100d100e0000c5802c2d82c100080f074140301c0140c09242400030190030075041e014101c0030201000640000a840e54600606451040d00c2c0003a40c10002c05a940d801c1240c0a503005071000b41145100403c0c0c000382c1000303031113401990282c540c0c035001100503420011217491044801c142615031003050354 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 226717455 1250 226716205 226716241
    0xd110a0f051305060a060c0f0c03060c1e0c060902060d09061a010c020a0605070c0e09031801050c0615240a02060f150103150e040c08060a02180603070c0506040803 72
    0x254080000e0324004d0005a8940c1142c4110b100b8010f40440c200300744807004003200c07252034011585615842da40e02e440b038024001e003044000005d415025000d103408000910007078001c7c465661010001082d21401c008120401c8101d0380b08104000300c040310046e0303000b980000e0b0301031000021410f01666607003000288900c10f00d410422103580010041c0e82e280810800c4e15424a070a80c2c40300d80604d000907410105421141c1e1a44003401000301c00d600000003440c1c56860070122900364894200199014040c405420700790741c11030380011b40502c05200303084890b004002d203900b4100151072030280403600d4881c2201030902001078040741b0b90b5010400303950015810300d40c503061441e09030007488111043c80c500c541010307140c43c480c00c51b100299240300c0207000e41602c6100141003d1514244000c25446840c0443c02030030300140790350b0b0491082d54001300302506480495903006003008a03507440107003040140070310001140c000c80c03002c200c0d03540304901c60004542c0d81d04040815504040c1c0070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 226718705 1250 226717455 226717489
    0x10110601091103010e04030507080c060402011b2a0504060807140f01050a05070201090e0f0a050a020c07171002030c0301140307060f0c020a080d03020d050f04110d110a0f05 76
    0x260401c40d081102c2040300d044944504070000c00f41c07070790f10341101c49214401c00a080e0303480102c0e591074030542c081034943c0590720036214240c008207104010058180c034180c01400855980035500c03148000d9400034001c00b00d1080501c42800d880700c0c0081c040300c025810001c05940014420b10400000c8101221000c404403498072242101e440001d286e885070034407a804014010072050116401528103502400301002441c00600c5c0504148140e00e81c1220103000c06420078012428000540c07003102d40c0c1c1d25189015200301ca04140742900131a074003840400242c030400441c0e1480451302d101460240030000070705503803545400c2c3c80c030703000c0e0b90b5052030079109070403141040000503081080d81c03502d010310781003032400d5000da80002101c0d80500e5006215a0242c03809841c401c941c95402008080520041002035460302d00c4540014041182c1c0244408a401541d000310b10341800c0d807806991041010000e803545038000320341d942c0c1650f8000c0c240300d9000b00c1c06100038a4000d01d02032000c900 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 226719955 1250 226718705 226718711
    0x4051003080301060f03140a02030f0f06090106260901051801060501050403020f0f03060f0613060315050c1303110406050d0f02060306010302040902070c050a06020f0a080d09021011060109 83
    0x31901c0d800494401813192500f4401006403021071940250000300350210305d080195481e00c1c1c6920b11401a620841c1d071074007000c4001c07000419001c002c0f41c509015440150001c0f02d207a08054090310160f0183c4040c4003881400b21076a0300480b400c5520a128500240004c1014100165400464600c2c0440c1c074003d64107262042c0402c0e44e01a050350103c03074040b1901c04484900c1000b00c0c5008810329000c41c1c05000369400c11000b4070f00c079400140a900241e83e1040ea60a125890000302e500303500005100c00030807144009628015000342e50020544195546012907661b01081d5211455008880c0914841c2d000ca03142d01e001e12a4400030207058680144081d141c0d59030072100501960300904c60071012020507184d904c40e074141c41c090303e50100215650115400c3c080c255001c5407180078850708030544045940d510120720b80ca56000c1c008014940c40000d550b48988640000c401e4400ca15a01c0359080c0140c0d442c4c0f0f919070b07200003550701d60180b600c0d1154901401c02d18143c2198a1441c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 226721205 1250 226719955 226719959
    0x30606180610030e0d03240b0d0c200c010212030f13150c030603060b0a080312040f08031608010b0c15190e1b0301090c05040c020f0601090b040510 65
    0xc80306816980c40401264400100c0d004800140c3c02428010310b070569130b106a00c0013410340354060307102d000b001c0e40010200440f60b01080319007071301c1e42480c0946852a0f0f0700b480036800400c000c1d00145070a80e09410004014040162180c00c020800ba80c0500d41d9846029050070fa56018046100b0618044028528601e06000040d4178118040d01c010a0381c8014855401030100c0c003150500c943e02203800c203001046413a4001400ba01c2e10340010345040b0301d00341c10020546800280d0004848403e005541401741d01e40040c0e401d00801002a100395004e441c003e00096100d4008621500040000b0300248031f45030001051210140c102c001001d00411104412600001c1d154404804486219038a03640d41103401429651016110600c241460541e810600c004a520444209503507543c02c100240c00d8201801c0e00c004201c041c0c42081d081e00180403500380358214441c5000e003030040303400c00c0205406031443c081c0d0036800644040d9071590000000d20301401542d07080301d500c46e1300c030003294 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 226722455 1250 226721205 226721239
    0x603040b222301060e101a211305011803021b130903022b1202091f0219050f0d020a080307112a0108071e030e010b0604080c030606 58
    0x200126100314240c003040d100c90b07100110940060014044400d40060b050a1800800c00d04500901501040740804000083c1428107801914500c140340b150441030526034545a4444010141c00321140c03c3c11402e072600819000d028294010100e151166a28101c60400034205038505c0c40c84a410402000c0d070b079030035a80e000c02d0480c0c40b59007880009220380070341c40e041e450302c1c40c000301c041030b42000c3c624998840300744250703003800000d0b003a188c5140408408105100303e11901c01e0250f402805010040000c41c180040119035403128012218001d40b404040c199108181508880742d90205008000154007404030b210300668900050030810f5641d07990400602004001c3c0042086c000340e240c0d0740341010450300300c41210b0b545140d8050b01c00c03800d503000c50038462481140840c07414404200410300c100440c415030300ca550810f94a4228022046000d401c000113050b0b003e40d2500c24403401a906c100c024030040070750300010501c41c80300400345420241c0081c507144c40752201018100e00f41d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 226723705 1250 226722455 226722473
    0x907032f060a020307020d0506041b080307110a08030328180b060d0f050d0e0603060112050712020f130909030f0f0c0f03050306010207051f0302030606090603040b22 73
    0x144421910703a601c41d540c4420803851402001000f1354015003a541c82018044d006c10703c82d000da402a850782d82e804c03840c2e450000c0200014850082581d04c104044000b052554020420f80c4900600f10440135a442d0030341855500240c8141441e4102880141e01d0310400e6112182d203040746000c1840701040129151100076401240940517464200000307241e550741c144e81c29266076100d000140302e1007460a00c01c0d5180080c5c5e2001010459503090f142d80e500e40403050b2481400140c4d111006000e03111040c4000d850050620801d00507100d21031191050240003400d4044c0c18220071589644101802c4031049213a94000d9003043d25246c1e40c800440e030320800c4071810105038104101200c2d011030781100c0c9003007454009010046e211000000b00341d404001540207050980c215400c09850f041000065132010110304110652280001c40440c040c5e00a10f9005400624041c1003d41c0c3c00301040c0c580d03108980440c0c06060400c10000138800348080904a280c0006802e4940100c594810640b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 226724955 1250 226723705 226723793
    0x109050f0a0b03090111030c07140a0c03081810020a0606121a100909030503070216060906110a0501060902070b0c07021503190c030c0f05131a04090203090703 70
    0x560000100290131402c007500560090100d140c0c500f41d4a140c40085201c00d50454401244c20014024182440700000103044440c00e070049050b41c40c076031840d510101641d01554224080110002404003a561030012400c041c80280d0040c06181c1c006140280403103007103401c03040e003a00c10781109001107100140300c810f21a8403640182d041e030b21800308095a101a913481520642e05241d5950704059205001c0c500508554003160700c080700d480c002520252442c010315001a40d0a081000011310501a0600b1440b0361402c3e15003480403521400c0c01c1d115150030148040340c00041030420884800203035075100c401954010704000b501d0740041c080c1030031090900c95440004c00411400d105420b0b0242c1e600244500c04c003c82071040a014018007400541d0201050024410000d21406102111209051414410f40190400446004600401d501c52040c1e01050001041e01200341c401503019844d00b40c010008103245260000f84060b604188291109001c400e031080b0960120012032 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 226726205 1250 226724955 226724969
    0x20c03070f0c120804050a09050f041e02030303090604031b030203120c0417100c0c0b180a050a051f0b0d2307090f0b0603130b0c0d05010b090109050f0a 67
    0x3541d81400d002420010540003204031030102c1c0010020031811100070030850b50151005008582e031a40c1c1d05007207520031210405045660300020380020800c45040d0380400001500f1505526241c01203499034000b00c0c2c510f446a4082000d1005040d0040c1404920503c0d00340a0042540c86960080d201c5c0500311021012003041c80200328912041c005a4000e098042611151110241c0c84695150600c007005010149069400300b26a032258400001d90b64001c0d5000c04280c60703402000c400c0c1e83d2070903d081d0b003e010340010400058000d114038104140264000d006003006006900c000b103c003141803855881c507001c82c00000313071516010045031640120f030104c064902a103c0c0041d00c000040c4925180c0105039021034001d42640c803034200c0302d05944080103021000d4062007841d120580705410261068204000024405410305500004000071981425a9003603500243c40080c2c1180c8100724003c95a00302c00c1d40e1025080004100486080c00710340c0c003820102d1072410281c02002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 226727455 1250 226726205 226726223
    0xa27020c071a09010807180e040f0f05030403051504170309010f0204062304030203070506071109010303031b020a1709010c020a090203250f0c03031b020c0109060201020c0307 77
    0x44035805051150800501000c01c00040d1482401410021a070000c0c40003404100e804000c16101407150403070038210324100d50168256818202c000d040312500500c00c44038401580640800582000031071030129100344021340d00e95040d032a01c142010751400d43c001e04c00c0342c0b88041002194a50824007819071002070304960700c1d1641e184042c05488984003c4a480780009000075100f81d003e03050110035018040c0c2c03e0103000d0180020348152160b4840030754180d011100070701c0545000801000300d244180010048020103d02064020600364400d401281e0b40f0203c42161360030110012501e003a8503c054a0b40c402d0940d40c10056000d40c61203044408004194684180d00400d03080d40721a400a24405600b5540c1d002e6070302a50040710000f07000d0842c20315603c0301020503410300c00b003c610380d222007000d400c0010b0115841304d180641a0105070301c41d904007200000340b03411049105110340c0900304a134501340005d01040680c0c1c2c000411607204000300d8004144c044152040309038000016 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 226728705 1250 226727455 226727467
    0x317031308090117010f140405010803091018030503040608070507050618100603081e040308070201050a030f021206030c10170618010602010203041208060906040e0316060b0a2702 79
    0x4940e2404c44080c006400744507000042107080760410f50340300722481207590358102c450800074032058030700a12440340350754002d1025041c00d10703008080341012640c901c1d09042c104001c004009850300c0c00e91003902c003500000f80501800d5400101c041d80718155003881c0380741071155078a550765a00001c200d0300b4001c1c071000ca2040380c1e40c2d051100081d8558008814442240c8900b04034040c2d0b40002d02041405041050400b407200070139050700d04407500302e11950306040030b6800649055015211820416546110041300e40ca91403018110683e8565a048d040345003400515103015042100c940c89207030903080c00d40d0495840407004007100b035084401911030301d942c0301141c1c6070068201c48610380540c0000210790b0650540c040c8d4801e5000e1400c040d407207034500e8016a200d44042c1c42d410b030040580c40000303015081030742141d10704c0c3c40c110f002c0701d14100b520007100d0100016000300320390080e11901103801c94500881103d01030038848000e411010b40305c00450300d2079400d00d40ca0480d03081e008126 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 226729955 1250 226728705 226728707
    0x111c09140105030a05071b11040b030705060a0f0c020a08100606080c091203130617010f150c020f090c0d05090615120c041803030f0507080c070501060f03060603170313080901 77
    0x540c0200c800300040d071491042282c501551044400c88c00c0e0382c0621300e00f0b5a099403a160000b0002c00700c940c090708691401940b220111064016540a2024460310241d40b00050301c8901d0700c00000e020310340140c1a0b0007101d0150784141c801c0c076440102001810001d0000c034440b81c23801c423002208102c0c3c1d070700c0340c00c041c3d009102d0550244c2c00078001c1c2d040c52000001480c80d0460482c0346010692412018140e0301c1d01d5850194075074034003034070b8140d000c4d20207903924103802101c0d52202240014a10850100303c5c000098910400f00d031074900300040859004a040780b58060b0369004135050020b0060380c0b41a44000354090020309032280b081c40c1d10704900312040c40a2040c090700030300141c02800610752050030045002803284007280000c0c41c0418803142c02e4028403071a4010101562101c2c0d0588481c0000c511a801521003580c281d582d44400142c000064409400154855200450141d00d141860b40301c0328881b410071000d0603410002c100941070040380d030b540706a134070410080d1107043d9900 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 226731205 1250 226729955 226729967
    0xa05010e0a030f0b0402030f030c0a02090c0c01060b0405101115060a180203060f060702010206040b06010203040807090b0a0e0403080112110915040b0d02030303010306020a111c09140105030a0507 86
    0x4805400c8058000c5260f00340702d2121116403040340281c00b00d541c400b00140d00f0658911441c0d082111720340051403c20014903000b000b46421241d203103033039410180c051081030308540b15a40440721036400081c0402c418240700306d21204c0d407022801d008a1452482c641103486a1103081d40c07030411141e040010381e06640d040341c8400644010089061070348500009503000b0741c019642184105031399903e801d024600001120082541070b4007616181d1140d5440520420024154905502041c000070030003c108100300030060140e0040032404000d1300040c04500c00c019045400003485507420007020a400580c031504507100b070188010031041504219041c07000c0b140489500801d600c2c14808546802c0007400360145003100e00300640c5100d64104405c11141c420001c1d01600148010004590f076640500710a0030141442c2100c86018010182041001c0c10304a0240180d070a080210341d510410b8074002c1d11041c148014440c41e040006030142c00300030b201c0c0602c50348420020708140c0c0701d01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 226732455 1250 226731205 226731209
    0x3161404080705090a0e03070312020d14040c0506040b0a0e04020f0d2405010f1b020405040302071a040b0f0c120a030b030c041a09040c050d030305150109050a05010e0a 74
    0x180545594440c810152650228416288188840e074040360714505944545450480c03600004d51404140307640a8a00300c20114900000340d07400d201040f40340800d40951a4202c21700300d80d0543c1842c0600c0c107509201e50640015002d18001d0005000440b82c1d0411211030030182c1c200b0003610b406590000e00070b0b11640e0300745058070401042c031080d1202c10790840f040da01d102c01c0712440a96100da05091020b8418407680b40010a004580c501081c0500341c101203110301d42080c0c040c070601d075030041001e4480694007140142d115071000c01420000304884640c0f0100c202c411460a45880301144440c005c046107070780030460002c2c0c811100345003081800c2d842400011210340710011280c0c00380003003403c400d02d103001c0c0c0941c080300b0099141c588194180e4481c0d010094107404203500600020f00c0b8014400c44180780392102c041440d5403441070100100d4400e980c0402c0b1880c044003c3e00f60024410381c82818403034181828000c5580d0744580030251102864211039250550001880b504080c0d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 226733705 1250 226732455 226732487
    0x11030901170c070c17011a0f060d02090402030717160c031b150f0b01110303071b050f100c0e0d020907030204050603150f0603041511070501020307030b040515060316 73
    0x11341d0000380605a03803407420b100d04240c4000700402d503540400500791000d010001644a024a04880c81c54581500580515121001d0040c1030084203008078040360301c15039104003c110085203110b03462a4501c070465112584603441c00d07001c064000080c2c4800c0f01c1c0c1d40d004007400a04203c54208000168034041c000d80c00c0a2252800c104803442c01c0024035218045107003841c04d109805400c1c0d40100d0f419007220900100440c42e43e501d889084a0b90a00c1c485082c3d0b84402c1000a0000301e101044081e503c15601000340c10141c0c1950620302c01c42c2e1442080c10b09200815409101d19540d1020100381c06130140c0d100c2c41030340d5605c1c404030002e00c00e40e00483e501500100c1803014894121941000f208402e603451000c03001d001081080d140000c8900518a0440c0c403210500800030360000407050480910250074855540c3d0b6090981e0002c841c0c003c0084d540700003401944c40d060042541149458200340d041001400108000f0302c80209a00811101c500ca002640c0e84501c107940100900 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 226734955 1250 226733705 226733723
    0x3010906060501020c0a061b06020919090f060501020d0f23040f090608060103060b06041a03060306010605090f04090c0b0a02070611031611010201060b0c0d11030901170c07 76
    0x18980000244a18002c160040c030a0f041c5ca0f10050802c5004034081d00c040380c071103207108181c41514203180072010404983c1d4540074030039800c0710384480c14201c001e140c4c02d1166645460030500709900300da00301d104191140741495020040342c0d8011032100c6102d0524a011508184001002c0c0c80340f6400c20340c6102c0c40d009003040030381000b413020090000e40e240c1c006040c40780c84c2d43c0d040c3e09050b18030b5030150386d81d2500300400420024056030b20001c1c5000002c2c0415003007554481c860500080488d0300c16004030000020005249814004107003d0245802d145082c45540804541035030220a1540d014581d905040700a203c014104d810007032036000d030360039a105070090000391296024442c407000701d0803002d032100744800c01005844a000052060f60348805454a55080d120120445581555a10f10000c5140d8198800600d0301000050060064428a820047c02410450907200d001d800078001c2464036a03000b43c0c481903d102c9016040096200c0d5072906c803541c49803010050066075 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 226736205 1250 226734955 226734971
    0x90f0b0a2a0204050a020a021e01060b0d0c0e0d080d0e030d0603140d0207081c0318050d1403060901050904170309010504110d02130c141204052103061e0301 69
    0x1551410039225100351424041505c41c08001c80a80c01500040c0c0301503004881046582809059000d890900755000428025900da1450740b07680c1c89000040d420343d84507801c405060340c00c91045c00307030641c00303880704032900d140b5850306082e50081c1005420140d4030f80320b00c21008582042900c00b02091004104651692860150702c0c41c240c6070700c08170071401035120b4014540e001003007600c00c4400f0f400107000c07020304a0325010341d0305038007004510034076580d00c0604c510a1018480082264412002007658100c03010700900381c4400e60940d11a40306081041140d1a1524113800d411903009613601169603c99160912200409180c40c816400d404800c218000d801508114042e074003d4210790090510303074040c043c2005c10084040d402c505041d000d00d1302c070070fa81d0744184104041840c0080c0790b280900010f1940b40d10483c8040301c4400d8420034442800400d10240e20104408905104021f45032107400500c0d0100802c25441900880d0120311070f0640e0703a050700c6020600070020840b040c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 226737455 1250 226736205 226736267
    0xb0a030b090a050618011a09040f091101120b030319030207080a1706010903030f0c06060807030510050606070c060309020a17060f060102010b0105070609051525090f0b0a 75
    0x21045800354400ca030340c0b5a0f003d40c1e1a62484145069403580c8001101e41c12081c902d80340560b11230100c0c03a42103030799440d8480c40c01840f44600010346c4d11030142d0099010303031200014000303c0d0300b010722110189012403c005558000080b105182c140f950780c5043d010000701c09600070b0064210190003814001a040c8140d50301c0b0510000120140d841007505464070801103c0300859400010080b40346000300c4281f040c09100804652445050081181c1740c07076078030346410820994000c4800703030b012600c1e003000707013940d0f0150a910480c207030341d002d06103444c9448002c3c1800d01340c03056006244d900c1d10f841096440c0e201400001c0c0440b01c8425542001c48450740d0768994080b50449003040c419808500300d9031040c0941100003205070760f05414002c06032500c100030001d444040704c2c2807160030740002800c601d80042c50b10600110b1040c1c1c2819070b004000500c802114085030f000c01c1803e41c41407000c1100c100740c0f1000c0e0b452920f074050312980c00003019642907e18000314842045140010820a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 226738705 1250 226737455 226737461
    0x1706030f030a27030b0c0c0c030118050c040c0f36030302010b15090411160503090315010501050f0913090501050604110403110d0f0b040308100605070b010b0a030b090a 74
    0x20706801100d98010b8000704403d201c9000540402031900b01c548010511801c8090301905a210428090f59104c822100000e821a061142000108004c00300e480d000e0100502000303091000c2654203000c40c40386650010300070440f82c0d80c4031083c001010300c5440411400d80d020f80e001d442e4006504a80700039212401c00300c00f110310007180150f00705060305e04241000211018181c0550202500300403400c2d0800001e841c0b160104c01c6554000c0c44003040600c503001403109001c0c041c001865442403004140b50401540703140501c513900c0c4e900b00402469a0060494141da2007454855484650300e10001c0c1e12a84003520600289003400203410a220301907101e580603903003c4904001d403580380050035942d030046e440040d10b82c400418684030142400a0a0040070344900500794080107143d907400384207001030b5010340002d440707081004220840322070140e01500290820701c1c1040e0559454507002c00c0d05001e18040d0b0080421202d0185000350040107140f1801012409280b520314104401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 226739955 1250 226738705 226738727
    0x30c120c090e0c13030602090d0b04080403210f0c020f030f060a0c0f0e0909010603081201030b0105010e100c050f01110909060105091507021f030e0f07061706030f030a 74
    0x218024090101d51041c50300000c40300500c0441c4245000313030b855629074400035000204042d0b0801c04001e5080d00140c10801101d100e42d102c1c0d60600d444c1c6041d07041855511440b4502d100070100d81c0c1c90070162458020401d00340c90342c2585424407441139140b012a0b000c0e8130000c44a900b6100d800740c041c5003400b004ca24148100c6806a0130002c090011004542d50301d5420100d00c045003400521114034248290702c0381d4081f03603520020803030990304c2e602c000e0203a20464a07940a1100e0300014801c0104110348140100710034a00800d42c1c04030b080c001072002d050848400d00384203200095100300002400a400c184111000030004144150300c10403044d40701d01c40040c41109008000b42196005c0c90644441e4034014104483c00c44500008220940c0104426030340143c070b000344211080309070700030555013072078568001c00c0f0248c01031b084501d400095946400380f900301c1003041c0a419803004451241c5041c00c3c01980b42c503101c01000c2401c00c0c05220740c0c0e4225020000301800440e40020150348 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 226741205 1250 226739955 226739969
    0x201020d050a0515130e030c0a0b010902090a1503140705130506030108120c0705040219031d03030a0b0409062d020721030b03010507180504050412030c120c09 70
    0x200c10354a1604040443e0022034603000361001001102e0b00c01c2c200b860035140000032202001036a0030600882c6451038000c800003082c80e45c4011000c1c002c00003c0451a401030040c160b040d403d00e030154000486091450007540c05c07104407000c60400e00d03031194000e5030304140825060b841030b06080d1001012076106620035240c159024400242604001d01203d040740c2c40b142c003030038410a001300e18503075941c00032420900038412000003203415500e82c4010190701540440752320302d4030722a20000c0c0070303501030740d1090400360b07c800e0b0311030f444100200440e41d02c00070101c0c001031040c1c480b00c0058000c2c4030b0040301400070351801c1c0341100c0c0b6100c0b035100201300d05007111010601c642c045a0380c0050303110302800140418840c11038108844884139820000c0b41e1f140c10042400d60074000401d00311142100e04400140408200500b2600a0315010028040a440900045c500f944580d4038080000c0128030800d81e0303132400320b411248034407452151f502c6408018880b01a004034014051132442c00746503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 226742455 1250 226741205 226741211
    0x9040f030c17030907080303130809012003040f0504020a090b210108100e0331030b090105070f0e0a0e07030e07080d08070915080a06080712050c04150e0919030201020d 74
    0x8501e0046c00000e032442000440d000000c00750740d55903080c05e01e820140c07a483c14806550000c0407644d840000d414100d0383c02c6401141c54514214803481e6910f00b40d8452809144100600075a5503400803e00d0180c0d10403071319083d9074440034081034242c55444941414402440c3c0c0c000700709041c01140f4010031000410b805d00ca5407034000d0800c0d849101780c2f450130151000c0d200c0420701d02c07510b08020708945144908901700702580c9450740e00d002a81220303285081d0359074008018549800503515104d0081c58030385855840715820105042280d5402030b540540790103000900060301c217400682400310108151182c0a43d80d0f1034840d0388070211900c04000c1800c0c01c3c0000c103094442c0f02c03200103d0740100c01043c8082c41001c0180e0300c1410140690110f503844110100b00000304002c1c5400400c589420b030703501440181800c074108400040124412400c018121404040101c80131003501c10401c4001c3c4243c807041e80c0c492031300042e0b40381541c12002030100001815019800f07001070b042100741c14 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 226743705 1250 226742455 226742459
    0x1710060501050301230a05120109050f0c06040e060d06020703180905060901030b040303090b1807090c14030901090507061d0a050a0b07080c1207050f0c09040f030c17030907 76
    0x66645000034001c49904010710007210042624032000c48500800c050814400d164684011625501072a23403480348580d10341e5040e10401608001c44000e010341c07600a040d00800610000d43c440c03040e841485171040c0024040f480c00e99400740790281c0c095004504554410707481c1f4019000500800d0140d61039204c01000203050780c0d95001c0c0c1d03841404001d01d004035036804c640d241c2c01c15113409081501003643c0c880c0051700003108540c1c2d1134011880071010007a03040601706541c0c0780290780d8015403421400c2c075031603189803600030b0005028040044101a240d5441d160300c85d00400a09901901c0d034494410000380a6420400243c0000c0c4540300e118621805501800b4104081d8840c0e20740261070310400b0481c540c1440c02038a1760900c00d04059107003456108010703280103450550a101c00c0800584041044130812040c030140c120701c405400c810031070301c2c00a007441030300800103007500c003902011404140c401c01001c07078140d070702180fa80c0ca0400800801c0303103617420447d040d40f8184620800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 226744955 1250 226743705 226743707
    0x603090c0f0602030703050d090b010b04090e0a08070b19020a051c090201020c040203060409021e0429011202070501051302032e02090a08030408011a100203070311071710060501 78
    0x81c010070b81c0c400783c00442c6082040c1ea012501070380822408c2076032981e00e80c0104001071040020394020f103c1004400e0316a400c200c001b008a070100c40091025611001341701d00010002419030305504c0e0449030201d15566001c004000e03144000c0e000d00c2043e4400180d46188503085409884155081800751184202c0182250700b2200c2c040006400340c0e002c903041d40111328007a001154004800350011034450800c0e4003040c040700284070940c00c0a04510405015401d00e4440c179490f001c2031000411841d161602ca50300c20314444a440d50400240100091220640c0e4048a50403035024001b0403d600d4a00c400071901030000030200c0c440e000c0d011810303d403140001c4801c3c2c0d91410f5088006207180015403031000035030081c60901c0c0c104d0b248040024900e01d040c4081d0000740507250000c901b0303410b410b0344114803040d01c412680c407625010042010b0755500000391180c42d541800d000010031848803001e45800381560000c16000d6508012190070200417400c40184805068207002903903d07a00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 226746205 1250 226744955 226744979
    0x14131d070206071b151d030903100207020d0b04060914150c0a0f0315080109050d08062407051c02160801110a051b06180f0d0203030a091109010603090c 67
    0x708840c0e880c1300c0c0c82445001c5000c0c18145607111440440000d00308050090001c200341d40e442c0141c1040e0408a480c00032400e0501001d00d010500010451034580742da4001a00d0340c4070598080d15105080c0002800c06c01164823020640741c22100d40a403d014203a05a566030b6410148004089002c0c0046201c404151041e0341402516072155012a105a0001c0f001010b03081d540075030403014002c0000d2040703403e2280040040c0141c01414155001c0c0c14060484c01001c0c081500400c2905440d4552400e50810140105040c01409176541c2c1207003445890b110081c5078503800030040c06146008981c000500c208041400e5004074034540c1d8640d0f0340340c201d03007580740582c415110401560f02d110344650f004024050f41d6600d460f44407250505a9480c0000860300c41c168081002d28000f8170030810000088000c5104005000e000c2501c04000e48900025001c0c100c503c1e2a90001400c20008121114002c60007815240d000d41e900c41d40140502a050340c01d56190710785030340c0800c044620344 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 226747455 1250 226746205 226746227
    0x9020702040f110405010309020109030803090105010f170c1c050f0303190b0306040215041505040531050a0b03150708060102120304032307110306090304030314131d07020607 77
    0x800f460705007407400005402070101e008080741005003503040880060602c1c0c000e58041c0540200000d80e83d0305140f00300c5e880c001e840d08803030103d26200201170710341200001e0342207403144140e0b07407180e081001810a005584004a000340a401000f441800542c40000074501c642100981744540000d09403031801118207140000e60103070050030002e4058140b0040601381041d1031032055140680e02c10b04000301035610800c940c00a200080c0c200114078020701c0148803088030115400750100d0310100088492810000300500940316000652004043d0384002c011b10740150584d2149a504201969103801c11038010f800302e6070180201c0c085500c000740c102980669201d206155458135101540d03055080c203213000d00702c40502e01c22580e0068801c09003904900c40c0c084d1050a0340324804150418900400d001e01d554424003080001c2680855602124040108416956020f05034924884d0000303800c2000042c1d128045040a0110400a0b07842a61123509440d41515200402c8035092103036 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 226748705 1250 226747455 226747481
    0xe010e0a050f011e03060e01060306060516052a090108030307090e150a0e0402040e010b061e04030501090320150705032e21020102030a110c040609020702040f 70
    0x2a80d02840141844801680036a00506018048614000d8010801c03100101380340002912108104404007a2280d014050266424240070702814090000c01a0081a072980c8c00d000c90f0791801001d1041c00d100700d8201c0030f04520540d40e51079240e001c083c1ca1a80700c0c408680503425030000000e040c0d00c00300c280c134054546076503481550391400350740c0b60864801914000180c0b8029201101c00d680b40d25200303000782104058004e0728030382801004112039442702e00028030b90400700b40c00345683d100421240c1f04480ca410403840c41503101400c0030796014a80004080b586405602e00a264000b0016850882d15503400120380e00001020b50300d61460b40303d0000710701d0910000c01c0a05020304055980f1018000f000e844c5415030194800c0d0114001a245404413444002441000e400703c500c00104aa402c810f0046506141c1c0000c1d038078400c0080c40030800c4020342d500c1400d01000d21080e1084100104144802c50700c505501000b58400c0b0400c0340300700c1c41d01402d0032101c921030044503110064 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 226749955 1250 226748705 226748719
    0x30601091409030a021c051c09060c1d0d050a140604050f0a080f030a1b0e03070e01140d141b09090a0b040605090109080d0504060b01021207170c030a030504030e010e 73
    0x29046c64002c0064034540c040c04405e201c00c059005000706c2849080101c2c64020401c002e01c1e04000341200e074003000c02401c00c59507500210601084400c0c0ca000c03140140c615815050150030668140398001308010712a24030600401c10310ba800040e014002c41c0a0016140f0180c286010183d46429030240101429028002141d000000c00069a0310410720345c80400ca071800320f400244041121107140b0045032602c035450000342020021000030b00103035500c003901541000c00c4100405101505944509041c24402c0e0130082c21540d0081000b01c0c040c129105580450041a1914545c104480c012080b0030001040140b00142c0302c048607402c508400000d03161511000040c28000303041c1690766490b00b54000000b8213000003804100020900080c050a292401c0816640d215004e5411580a90025001c141110341143e4039581d1009840684407400d11a20782a4041d010510f00d590101154035810700343c15030000c2e80308910996a01e0440c40b02c5c40015107040c0903c00305282c000c45 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 226751205 1250 226749955 226749973
    0x5060121150b06070b100e090d050715060314030a02010f0501062f030d060302130504080d0902030712080d0e0d0504090b0402130f08100506011d0f030601091409030a02 74
    0x4596001e800b600c003000d0102840e180c003c0e00c0e11038284000703660340750320240031420030807549480001c040e41102490000e0b08001510300401041c0340900d00024202c2c40314282141450451079200c50011039010540200c103c1c0c0c07030300b002070f01e980003280c0780070255007040c005000d0740f0000c1c81030340d0580d6001c0c0c4441032000342c100c01c0124200107442260085a4201040594420381003014242c400c03801c0c800488e125043d4418095584030301340d05440792a00302b406100008020009584d4032a0f61312070001030401c003a0000901c0d05490b03500042c8542e49181b01e203414060310000030903100503101428003c000d00c4240d115981c1c044002e460001600c00c0c001480450055080b00d00d40304030080001d400c5c405002000c0600c030315543c2c48948940c1c0708042c00c1004880500c05014101e8500f44108098949480040c010404580d0f14003814020741148a4003a034441d148c2003210100034044812560b1580c4a220042144500c002c00c08014400000c103140d40c004121201074010354040d0034904 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 226752455 1250 226751205 226751243
    0xf0a02090c0a12060906031a0f01060c06020412030305040506060907090614090405270c01092c04082203050a0b07051b0c010e01031b050307030e030705060121 70
    0xb8001001480402c94611804880c0700344901a00c0050304a00000040f00f518600c0c200c085415480ca4140c0f10040c0031040214162240d824641181e0042c140f1040003942450034030000c1c400c03a002400102c40305c0283e40b061680c960300c4207102d10b1041088900c280c1380c25081005c070300c60171a0f0361000078504100130300a0a00c07901d8280c56441000c03080c7c0d4206845000041c2c15508211800520708003038000c05000e00000300300e0822600c8a030030241080a02a100007071548525003d2219903944c07212240c802c04840d07250741206071130032500c4806141030500d042d1705580c1c40711004000785e41d106104886880c030484c0000741200e6215006000c4409540c0c0d800c0d5a0b900c004005c0800c1c0002030101c07100d004907820021b000741c4420340181c0113800c0f1076800501080901c038441410145013130080142c2c03a1303e5944407034080903641070460710707540c0340350b42100548040b0078940e0044c00040342207802c2040c006000b90507681c14010f00c030f010111807888842c0c102d403000780182091108200746020b0f8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 226753705 1250 226752455 226752457
    0xe0412030f1a1201181101030501270b01050f2205060a0e0409050c0613081006120b22080d050c03070c060e0c12030318010e03040302041a0a080307050f0a02090c 71
    0x3c4110000400c4500305032030403e00c980c006032001d46220a1248015560307680c50f20507503005d061201071114030232241c854544c071850b5140c0480a40e90382c0e10031310041c06a01500075142012520b03c01540d9034007003440100c210300640c0341c41c0324a81e2012880811180b5140c025a00c44c00743c66a01c5203e01c556610801c0701811a04200f1b90303c0d4041c0320016090b540b64078004213404459030360290b206601d05070400740b07001d04030b003003c0c0d480601c3c3c02d00900c142146e00954226440d0081c460300d4003600d6104800c1c01d041c210f18150700a203180881501c0400c4425005050b040d02e0481041090ba0340b140d015602d184421915000044c61b003002500000d400c9522100f070003e481d80131501c80f91000004900391100741d24050102d540040100503404840300031100b00f00400900038000c1d40303040300d182545c0f40942d00000b4400c5071140007080c0004040b004c4202d8484004290014060360341850b0707612980300310000c0d2614081c4c03404280c4100800108103809070b9018240a1069a03003407020012 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 226754955 1250 226753705 226753729
    0xf0304060204080708060f13030c02010f12060909020a0911040b0f040305030d240806011403012306030d0309050d05030408090a08070503070602070b0409090c0e0412030f1a 76
    0x3010381c2408080f4242c9010070182000c0c290400c000d003803605200740140340130301e002089a90395100c2c18a00500180c0d110031202c404550a0a180c40b015100351019038455203201c4840301098076002000071016420341014514074002d99401c1c41c1c03079071122404420380700c103140c1548030231100300710400501503448010240410000040e82c10075880340c1e501821603200040c0c0c1c441250300c5130a18041c082c032107403c01d11240d540400b05030180d031030b1200d17560701c0344014400e10002600700440104562003e4120030f0f01208201c19403a21100000f4a040c440f03441962203600a114a55207008028028855004500d0704180140003403284441d0032901070340b004000300d502520601500d0581d4030307004138120150607900042c001d030701d06100a05140c44040c0e4444411580808010810900300307404540584186550104003001141064002558142c1c401d00c9103100100c10007007030029070500301107409a84e0760107010940003a00007400703031140c0c0328a2951000b00540032001c1d0307180031080703c48 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 226756205 1250 226754955 226754963
    0x60903030c07051609060e160c0b07030e030d1b02120f0304030e04090507090b0d08070b1302060a08011a04150f03180f0b0f04030207150c12020f0714060f0304 70
    0x708048030304c18200500034140d001400903a01e0300c106121a01e841203d82e0b50011582102c0001802500c400505106900d000600f0240e0301d500400c0e007003407082e0000d44020780c2e0201203940e260300c2d480307001e4000c0144099032035100040c145245130f02031010030750f01c03012203101b40000e04000303003418505030550000d84202c040c003040004902da1921980107400e100c40c0101c0c0078044140c0381000307502c18ac800c2e48a40612440070300780c5080000311700f02d098881880d08002c00f20311960761040480700d001850340c000795200b00f02160400b40160706c041910b05844200c24010b8001c0b0a407403450049000700d02401c12582814450046010b00c41c0b0359030810790000e840d010030307100e840181d12040e6960656054945449407549a001d00603c0203000d82c0100c01010502c91034601524001d448a4030360041c8100300341007200c989000c910a6848200c81d17604000800588a00d90030069078500d00304000d45a1070050385400181c4640600b1100d40381e05c0041c0c071641c544440702e40c200107103610052040fa = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 226757455 1250 226756205 226756213
    0x801060f0314070c2d060905030403080f0d0605010206010b040608151c020120060c18060307090e061807050702010c0c060201021210030510110d0507050d0e060903030c0705 76
    0x1e500340d5840300146000d0081074075109032a08840c107082c940400050030a001841c0c5201d050781c0c44e40d0705c43c407082c400c150f04981c2c000743d01702c3d640c60800d05500c0303240d002904480c0c010401029043c00900101040118001c04000a540e10b00041e62500130900c144e004085092000300640d501800700181d02448000b442600d492201e00018000b481c40c4040d844040002e81408085581240600385078a0600c400d20400c00200c02c2c4040d40d5003001400f10707140c82000300704c01d030580d02807869454191400821503502ea00d040040140000800e10590608120800100c1c0341c1d0305100c41059201194448141000c2c0d960200c2580c40e94800e00e001c80c10032011030303281c4000c13649800100c40a880b9950000da56078072402010a41c40d035014160140c00f60341d00e0030402c00544000340101044208040c04980c0c0490310250310511b000710800303810454141000c00184641c0403000300720700d02108408124210b80322801a0761360310f00b103801280070390080000c1101134036960f01404010388034800712 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 226758705 1250 226757455 226757471
    0x2090c160c0b0c010e0c100302130b0708070605011410030c020f0303010f2907030f030e01050906040501050c04050117091e070302030c04090209241c0b0609070801060f03 75
    0x1045900d01e56009841800011861400140c02030003104101042030b0000d0205086160008240354490f03084d80c4189640010b07460840d0110745110301c020300b81d085a4688422041c10900b0040c2c0c803901c1c04803205440c00c8004614036000003000340040101508000381501f20300c1c002d0300140012000e4001390b01c200c148034503249108100541c0a400f4801c2c1c401c2003189403210700007020100c17481c20b0100040003c040740072008000142d681c21a054680081c409001d008240c0081c041d002e020704040d400e085c204402d01f000018201d000d0791190f00204140e940d82030086203113015a0207054006403071403400f0500b446690007a5034100e070004040c0c0300010082004c030030701d402c00600c8004003031700001010425450140300098407890705607001d0081081950000c0c1003104020b000044a10031000c0190501d003a1002c0c1000c00803002e800c52540c80d40205080c1c40844000b0411104140001c0014241c0d0800303c2c1c24034026083d0b500c0384003c6900f014416925200c2e03884051003050340d0781c822 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 226759955 1250 226758705 226758713
    0x9040e07050d060b09090705091b0712020109110105040f090b03010e0114010807080d0504052101050703090c17060601050a050c071820041205010908120f0106090302090c16 76
    0x20020b103103881060002070781a140400e0055890009008032480d42051070208466194104000d5200b0b0210031603100d00010940fa0480c54040c4e40030142c682c000310f1360a1822280c0544c13001020394080d0308001040070818004540602c40e0740212403ca000104041200c0091504614202d8000400116440c200701c00c0c40c50844403890244c1d00e03818400c0700100006070080c019040601801c1004d080601001c1d107000d03203140b180d80304040c080c041443d002c0c1080171614030060424040b900c000c0c002424030007402000340c1050981910301500c10391000640c1c40c10101d402080d03812840140903155151001958240c1000800c0e00900c1400c11009100503420301008000e00f0310302c1500f041e95200011a0300442d08908219001c04204006440d03905101c1c200b81c90454a042c603c6c050145414501103000d84100400100b2a800100304004ca20400b102030b94403e20130300d0310300d003a00d0ba42d401040710039070070300c0c80041c3d0881c0d141c8000c07030041e6200c0c00c01800c020045207030742905d8000b04c2c1e903 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 226761205 1250 226759955 226759969
    0x60f050406090b070e0306240a0806070e0402070209010603090c1a03070e0f0a0b03091002270102150c0f070213090b1f151b050109060b040c0509040e0705 68
    0x90219a4641d582c1140d40030400510a4140c02c000786150140c0054403141c0840e664640140c0581844444119100c030301e13898034141300c00c140382d0141286e50210307034422200355240002daa91201040e030140c2500350704d040600c00d03111060340080143d51564a484016802407045078000d451110314480b0115030300c2a00112515116410510130341c2da45440f4000602c000b902c0318043e072250140303180a032810b85e03442c08084251680b407002c1c0c1c3c2e80d03074440e144464504140e91314500a0140080348550180a80506414003214610740e010181121b030b100480e10b940008861004403032540001c951101000400740480420051130350b0310f440303c5c2d600050115000c40318403000860703e030292035040242c29018107400035002c1d08103e100140b8006c0d007041002040c010f00e00441812605030741030f2407103010400d140100f2110b19048520560901c94042c01c10804166641e5081922066540c1018428900000340c00da075400c0c141011882000040d04000441050a124011000c1840c0d40e03986 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 226762455 1250 226761205 226761211
    0xf060a15050c0106050604080a150e0717070501080f01060f05070b04080901120c0c082a0703030908030a0e01050a090e0720010504210903080a0c0b0f01080c0d060f05 73
    0x91245078441c180102c100742521256001603000c0d51060101f0800d96400140b045501c42c1c0c01010607400b8503000d41e944c00140540d0305148441d119084000a280402c1400340105404002c2039680a0780c4a00040da0340705c005560802c00540d01d00010008907101d02000000b0101c1464003914014080d1030740c04480c0002c2d02c05407245c03940000c00390220740c1c02c00501104030710b29407010300070b1030019000504088240d0300c000d85004000190b1084800080c44140c4100101000c40c0d145c0101044083d6941c035031070700044001c0f8070341e10404a08940b000040d82c0783c0310502da6607103059040710401101c05410070454081801a4440007240300340b0201d808903c1210f4541e02c141c01034207410341010110030a11071118180c3d140205010208a50360707581901040c020f18000d211000700c4508403402400c541c00508000004512504003580c03218070150914010002c0d2a01c9845450710883c4410081c03044504550100a29040d00d080028074502854003401c00020650544140501a07800031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 226763705 1250 226762455 226762457
    0x30c02062a150a020702010908010606030b10080114580803040b063c0102010c080610020102091201020915030f0f060609100305090105130201080f060a15 68
    0x2003410440c0480d140341501551a0341d2100400094089000c6040c0c0e40301c0c060303c0058070075000501c0000b56401111450010305503031000b08091961303181e0040040c070341040f0035841400b04181a45800e0f02c100b80f03003410b032250610600883c4002101300a110715068107101c40f5280f0a0340032800c03144c2c054801c0d86400e501030034801450309800502107908ca50440d035103105003000081010110b02c0300c070261f070307480b80d8007503101c0a55881c1c1c2d00004408a050342d080c2c030180c00c03801e818500e04614100192084818080040c200c0c80c80010059003a216510581c900280e00e07840081d039603142c60801d902101396a800014034226a913004076101c0e000c4e03410392070503c0c0c3d00040c03030011074142250383c0e1408450013004181507007000007401c80d2003103029140f000b5000340b02d40801c403555500011203000b00801410084517556895000d009020101c4441c1c009529150000d2000440528603076a40795051756100102c0e40c1d8401d00c203204aa0250660f42c11060640c2c000c641c40402c844212001440303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 226764955 1250 226763705 226763737
    0x501050d0803060121180b060d0b01090f02070b0405010903090906080a06090305091810060f08070e0102150109090506060306130f06060f0e0108060702031c020307170a0905060f040f020d030c0206 86
    0x42c1c7c0c144081550000780115010f805038103480e201281302040264151000341c04007003440100c0d05c40c1c03800a8011140c000c0c2c50a00c00d4010300c0708100056111210283c869143c504196a4418175001180c600d4820179800760440031603500003c10030790020020900c03030705202c1e003002c03107410103e18080c03001202d4a9199030341e00d060001c03a107001349085004043d286011000c0e149480341c0100b1400c0098a0721060100342c0700d8031156680207001c540c0c200115644840b1480d84e5070303141d00e40a010100000d5400c0d0113003001090b080d042c08503880384034003c110700f50455a60b0075030318481c00c990320300030030341700c09981c0c00c0045035210302e510f4800000d026a00c41c1c081c843d41004651420640b020340f040055510400408811403100801400a9806280016165550340354241e07403250401c950214801c441100300800e800c1603912000d00540a082100c2c8aa80c0b0101000000c140030340c1d010b171113001604210001440c2400c240d10341c5c01e200b0325140c80325010540c00b180c12900061116043c0b040c0f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 226766205 1250 226764955 226765001
    0xf08010c08090a021c1a0a0209100905060f070816061506030b10030905011b050a03060506070206070609030507051009030f0203120114040213080703060501050d0803060121 76
    0x5071100d0940c0c1c00180c0c15010f0b100c03c040f03540c00540810305851841005070708801c41c182c02d02c00012000074004c00510f00c0c907400c601c0d10702100c00095104100d000e110320801485841945c2c0300702020010f880d40500080c1c41d14403a841c1000090b003101c18100c0e84464104004c1e2000303142180d0026040d449100302040380000982207004400172034016904241c6030840e0040155180b9818810512150078001204001400c007503002d02008034880e81c50303908280c0a6084aa07018004080028031950100b0641d03884204005241c4a0b424020b0b40c80754041c000300010651560203441c24a200703040c52484d084070340e41c1c1c090528604000e41b4000d982c4e2008072600749a08203050401240c2c040c40510b180a0810345d49900360001801888515024941d4011954645904454030b9a0782c0e0305103142c001c2d656160056850039240011075406051000000305410403100140c00d86510503091411603030703607000440300d55003e580d0100d41d120040d40d0200441c002c1d4454100c1342d680304d074402d001c090 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 226767455 1250 226766205 226766207
    0x207060e0607140a0801050906040e0114070906170103121107030c091104050303160516090204080f07030203070b0c07180506030706020c0604060e12030a02060108010b040902010918060f08010c 85
    0x40300d640001c140c00d20070000d0300d1311140c0c090780c428155801110401d030075444060224008000d0fa0840054075031a041d0300510b20b190200c0300c0c5100d030707034150307515903000b42c44140c00c646081c0d2014100900030800701c010700005003500f61010405855240541c0d05002c1001072518004440d881a203c181002006004074403845c01200503144045c2d000518061420b00401d0f980d100d11001018002580110081042000d01c94401030814403041d8203510f0303449449010081d800351148040d103105c0c0201c1001c0c0722a02007500300c1201d4004010344509071800303200c2c4941c0c0d48580103014150181440118041010400d80c091010041d84c00007294986002850324080302134200009550111401070300b03d80d28041202c007560703800e240c442c10050421300418104020410b64024034040450080c04440d030000f41141281e10b0130000303200d8001d1b01300602c81250f9485201a001850112050050400c0508011204521381300b000800303507518000c103001c0540a402c81810707039441c1c4811021003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 226768705 1250 226767455 226767467
    0x5030a0e070308040302090a0605040219030b04051e0405030d020a0e0310290d080a02011b05070302100c050706060303030c18050d020904080f031e0106180605030a0207060e0607 78
    0x500d5203580141071450560310b0700c1c040d40c0a14072000b40728034072410004041400b00d81200d0700403c4041c1041d91940c2442c044006500c80c1150034600191400f1079050b408d00e1f103030140d0f0b401002c0110b840300d07030244031801e598130b02c2200820546d075610040144840c0f00e0355030b00c014504006150b54100954000500301410075044950742600c01e810325002c1d41c0b03141120608500101c2d20349100c83e00942da803c0200c1d12a464030707400039000c0c0c4004070388003100e5501034204605c4910180721501a800381100300740e40034001e81c0e40280060f44000c2004080155651002403056490305007241448110380c0ea1606655132074208400090300d80b06074480560300300d545a07405908661550716030b10700b4000800c485465900303000e03100760f000201203801c2c000c0104c00c5030a82d02c541440b02e42d607031030103c1d480a81c0ca415040b1300200c0c184c075403000240e600c0c460500c0ca0a820b000c401a9034219103001d1003140c8a40018000500642c1c0c01c0250b1400224540b03e004d0035401d0231000350646290910001e050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 226769955 1250 226768705 226768721
    0x804080a0c031a070e01051305060f09040501060f020d050a09080a05011b1409040c18170c150307140c010e1507030608030d0c03090f05010209090a0606020705011214010605030a 78
    0x3c1e61443c030502c02c3c031a401c5285060704000a1918545070706803407088601181259216030303080071001645a02404d6094018810070f802981c00b44601c1e6a05c08044550411080300b040040e00100348900700c803403042d0020080e0384a6403170544070300b03900c80c2c0055050149040084816a5441c022112465184c901c030311074803c0c0f5400d01c500003102020f40546103128101e4070500c965580c0003c451080d0003150801306e46c1011010903803805490b0030020032503c0328041c08048501c01c0480d0360440e0f2030300ca04140e00d2110303500c001c1c0d41141c407410810384040618800e418002c020511446101d003a0034450701e00b80e41121802000368000c141080300074a200600030340c0c101401d00c001480350440020440345105561040054910303a1940102c00524003103100800b1002120224014480150050b05242c07108803642580c0303031100b50144bc1210010f205050160700042000c016642c052081c40650780c0c245080402c08010b100c43e00140c82000342c000c4404a80048188040d907412407140da10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 226771205 1250 226769955 226769993
    0x4020309030d14091203190c0f1106012301090305011a0108060603010e0c030c070c1409060a050a14130507030501030c12383903010302010302070804080a0c03 70
    0x206814034095058694608000f5a100317210000041410019990020100888080c0d001c004850180380700500c030341c007920341d44c900160201d4040e0100040120302c1d58100e43c1000c0e0000440b4200c1c00662280301c00b940952390610a260400101062080c0200006022840e03a00300600355010700140c0351003400b074205c40c0658410300040c04005480182150406c0d440032003d034480ea2044040701541c45030780130051803507e4030f00000804003a000d101e0742591703408503040c202c0c55482e0814050304030703124031583e1f47c0032502100c20018040e103941a524010b1002e000ea0440e08050f200c0c0c0703000d5034019102c1c180043d40c1e5000400c00d02c001d890000003d020100e80c82c061210241d1a410201031081824448080e901d0300b15a8a101c08074202018030085043c40b0410f40c503010701405160452035a8038900200903a006890b02d004003003210f0400358820000d9810b507401d5400440007034001c50b1003104d941600b00301c08501c0000030000b1522a9104018200c045819031508185d00010101841 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 226772455 1250 226771205 226771241
    0x1180c0c02030c0105161a04140604050c0f01030212040b0a1410091a03060a0b010e0105090306130804050d0507240804110a0f090209031b10050d060504020309030d 72
    0x10042e07401107440a119002480e12945070080d40c4465182c5d0341503250010320158050401800029040019030321480c081c80585488044101046482d00c0c1c00700c50080c030070b42101c15006078628082d06070305031030354040c5001400c103209140140f50f0244180c50540c0d402c6018420010034407001d014800d1102829102d03002d4a05000d8070f5460140082c0c065880c690352940410b10801510b8502010040c500404403031143c1890f5641e071000f800c5a40301d05001898580b8044401d50185080f1400400041d0003003c41c0d5450244001030260280c500721030040c810400000c059641303c414418080c040e01c050103a00d8506214490740c0c02100820060240e090b031261030341950001001c5620a03008481009465003102c00280201007942001c292440300d007030045408192035000e0050024158120795400c9032030380f0034a00c044000504950711402414074100c0a07071052020b0070121500715400708500c1d0b203540c009003d9030000c994030110381c0c0c000700d040c10308518640107042c0c495410b19085 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 226773705 1250 226772455 226772477
    0x21e0c0a12021c03020a060906093008130c06050c060703060f0b1602040f0b010806041515050702030105240901060e0616120504030506010605120406111201180c 71
    0x4036045050b00c3d80000303100c04211490742d0905000384a4850000d500500411004a00d49010001010040f5056801500d4042203444a010b440c1560400b00400c403c0258144418402203805842c028807a2079284407084005001030001e8140d1400341ca1f5940300d80d1303180c0b81a48881480d250700200030702d0815050810420a1610b0380305054142c8601050440e41c40e031800d070001508094810000350400c1c50b02d4000c101d001b8031b5510800996000340e0303400351592918030402041d96a0700a540c0c40d8241480001c1210008665250034105480e0500a003010f40640002e801c480c412500c0c40b21040d84003031490070741c0b401682d24685035070f408c9807015000d5041000040801e103180d02042d018200026500d04d6581661f00003420345640714549076111140c00100a0940e0040c0c030003116544100c4001240f468003a034240c2d0103081c1600f1030f58013540c0c1c85481c0c81b0040e20403401c2528405504001030101c0d056000d082d14085c2c584403019140c404141c0c00280b0454241a05c48020000c8400d02c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 226774955 1250 226773705 226773709
    0x51603150902010302090d0b010f05010206040b072001140109230a0203190e030a1e0c02010c020109080118050f0a050a08030c090a14040f090f02010807021e0c0a1202 73
    0x41103198690350400100390701607100581c000c4c4103a00c6d06a074081c2110000d0800c0044d04440b081c140d5480d6000c0350b444a544a006a99800c07003900c0084c0039503a06000103524038030030000b078040441c4600a24007640403031620642114050036003031096210150060200c00168001e403003140c1507001c21402d120407520020300d5903402c0545510115a0000041158800082010345940c16295002c000281c5120300440c2d0301e41c0040e42600c00318200c80840303a00c0e042001c48003000b0f2076540d29481003568060b40112110803c1c08002c80c14480c8005012135002030034480c4225214003070050000459460414510b4035024441094039580300c0c680d40d10000e180412000ca005030700c000303040d8a83c4c0f10b000058850303004d243c4401c2e03008140740200040d400e6440c41c960980e0b2038280d9040003000902c0750000d060350580700f03010b4000d9a2002404c2c0065100358442e5510180e14410703036880c00c2d4052003e04200c994014070403807079031101041000b20700c0e001d07034204020480c03000c0c100401c419a41c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 226776205 1250 226774955 226774973
    0x70206070f08190204050301020c03040e0c03091c020313060309141b0904020a0b0f040e01050604050609120a06062714070507030e091e16081501020118030c051603 72
    0x1021480100e003c614403020a494050b01c01610380103000307646a1a0940019544c1e42241c885d28042e1000c3d9408a4004130f0801c0071240210382120161042c00500942d118000f605c1386d100404521040200c8545604134010707140150000d0f680c00309001080c0d003000305c1c49800c0d06044a1158104400c6140640c070170201961f0b50130416640c0a043d9504c600002d00071038a9940300b00c103840c0000440070000010800184151140441180f0086e40c8590500070640640e006258202008102e040400d01c0e011003050f020f120408210781800a0300d64903503065503d5584110171041c60b0200b14961128051881c1201d02c2c0e05410821002000c1c0d0b060101c484409800c0d1400e0040010300300b8203052080748013a0080308054141c1d00302d030404410101025680d0b500342c464000c030700700114107034070550110340780c0c4c0b4140c690300d1400c99120344210800804035101d032141550360300d4840c1c240e0304ac48001c2e606c130038900035218103241e81410b082c030f46d04140038100070180f85041c0c190705000040041e0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 226777455 1250 226776205 226776211
    0xc0e010f0311040e0c031f05010f12090212030414040e0604020f120d0806010906030c0806120106030b0c07050c01140d090303020408030c160503070605160c0518070206070f08 77
    0x3140115941c0b6104400c4030076846281c001050b41d110210400060180751002180210b0218000c1440d141d00d16504003070b0707040680501c0c0d00080c40798880344844c1d40b2401056410060340340b0000b84040f141d41c001a500c103030038280c500290b003010604010160300c035140407542d904141c03814000c054000d0003507515460002c00003403003507031602d680300450b8071100c100300d41c0e4136440c104482081c00200d40240243c4011502140000d124040c089500c43c824040d90304400e03501c1d21424440d07242c000401c41124681c0c0458a4030350b60700c0e4000030104600c0e02c036080c0549010418503507161319600b020380c100003241c032401c0e050001185451170700407001d00481d03220f0815031800081c4161613250441c0030b4070480e4810766141c8800b044040350355101048040b41204d0110750b10301c0403a45d6a0030300d600c03402c1c45d100305000304800380303c41540d2040d482d01a52940b882207030148202034039280000d03e001180d0f003001080b0116081009a07442d010040c660f0460300700c0c00c003c0032545181000510241c3c1c01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 226778705 1250 226777455 226777457
    0xb0418060c030e0d03140a020703050a1d0301021317060615070302160303050d060e0c0d15080706080117070b0d09020d02120f010f0903020d1b0b18010c0e010f 70
    0x2401004000a1007680800c0304500540c0541e1806003040d94020041c05010a03403503014146c0c080416060481da100704e86250350303d911524180042403906552500d500001700c0e0404001c5070040360303d95020b20091404504d040401e0402505208498524107080c0d903107125142c1c04201803002c6550b030502e1244401902ca500d540e07483d501f918080381425418200c1440c04c40000d14040201600040580024207030f0400400c0110780d00d82d11443e50020a0711030162002040043d640c8840185e0419400041c207095260300d251f50b1541124a404a950300100000b402d050040c4a200f0805244c2d00c080038445004254076030502e0301aa50a210300280c00c00d040e641e0790081400c640b943ea8070115030351f80080117820f6201d0308c04078240d1517100c0f4490420440d441c01c2404010815144100c80010b070b056401050302c1c3e400040305031404d450105800b010001d03070f81c800000150840a01c0c0f88500c0d2008400c03803000f020060b0160950b06050a03020a10809400c01100c699102012241c0b18880d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 226779955 1250 226778705 226778711
    0x206040b030709030b070f0f02210f070515100803070209071d0301050a0507090515040521010504080703030f0b0d02060901050c06150a0503061009151502100b041806 73
    0xb180c2e0240c03070030041d950008208504040070852140d40110b0210781d8a00306850b2000c0d0703100b000c881203880380740e03402e27200c0c44c40c503050144903d40d035410340c000e010900b02c0440f0030351400200f0f445103032821490810814914075043c0421010b40d001100c0301005001280096042107000e134009540c40e02d0040504040140100c00821103c1d600041e11520702c1006e0020041402c0a0b4403040151a08946c55030100301150000166402c0c00080310380141c1c081c814103030034241000c040003004160b880344510b0b103902d03000d65514030781000e110b401d00403480ba83d40e0540c0c83e4103600d00a13066032101040220b61501e051040c1d10651035022144180e154120b43d665075448020300145e0f0a4002c21180c000144103840030080d03407200198100b540e5140032038400d240c895550b010950b681004a5a401c481c0140000030000903409030010090b03a001c0000c3c454005da25800c45000840c2d0300b034900b10040c1c1c0030710325070b4030303181060b00c203407a210070080c1c82c00d2040d00da030800000300100385400d004010580d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 226781205 1250 226779955 226779961
    0x304110103050c190c020406080304050603011404090b070507020108070f021c050f0d090c0504180b040203011b08070f0207060203070b0a0906050c130801051005100903152004030206040b03 83
    0x5031100719001c884d08035200c840d060380021001064501402422401603140c6100414941000020395003281d90081c820b514603070a080000300200d1800714200d400030703200d002e40c070001040010780c90305c074011968038592983d5090000400311b40b00a000c4100348000e075000101881d9002c0748400002180b2000101c44011031001100c0901c07560480700e802920100306002007081640040340c602e8000c9060300100c546070001c02c0f084174404418041c1c5c5048218010780020610248140d1050008000007414401c024203001c1649080800d1000141254200500e054101c034040c04071080505c024134289051203800fa560b441a43d80141c82c2d46600c0c000180c00c101290007036003800d41c2c0000c1c00c0c05603090450114041d50045a00407142d042055404a0a00c205202ea04e20030303407480040c0b030f800354075050900682c100240002c20401030300c81e40c04400708030143c401c140d00d240e2004d4000340203035242c0100100c0e0303894a80100b4115200700000c10142c1d481c4000e1b60151139060803d0f81d582d407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 226782455 1250 226781205 226781221
    0xa1514220213090605160f052703120d0e07090b01021f02130b0306040515240d0c0903050706022b26150f0a0603050903040f08030304060b041503080a02031b0601060e0303030411010305 81
    0x50416583e00c03cbd02500055484102d031115080290714040301000c943c034054440c00d4000c00c3d15a651803907030050b8008800c0310100c0080d00a04545045280c02c0103160a0b00303260004441d10035500144500d050010601c0f80c103091074031816601ca0314100789101120304010002c2d00904d10400d0500d914503040242103400f02c40b075030403245e4981410303904001906201602907e000080e10041d82d5600074500000b40d01400800c0c4c401301c0c0000560000d08200c01c500050941c0f203034401e9120100a1303c00e18640c0e110303c017244100b0083d0217070f40000f211460400342044030701c40c40d400028000e041090b54007442da2907911440003954024280890907030350303240c4041d01c0c600840c1c1c0003080044a8000000f5581c002000075401580501402d1003070240500c14030060356a095141070000e001c105042020804441c00b4140c1084c1d184152403802c24050303100540c074221291402c81c1030f0010001000001d40207801c030500304800703902460641c40c09031144940c0c3e80314401a14103043d12840001d4060b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 226783705 1250 226782455 226782463
    0x6181504050d120f0906020606040207060902060a08011802040b03060d021206040c03030801050904050c010e0102100212011404111b0a1514220213090605160f052703 73
    0x7070701026004603500041402c00c001a800b080a04002050382c0f0748512808500c511001030035180a03800515030b503118081400300a43c031032141912410b9460310b0b00001690384200908015502e59201006541050010100c9030100150340c0d084900c1044104030040d8402e042d0303540000112800c100880c058004690341320400082201c540c00f801c0200801c010201ca0000309481c0260380d03480c500d030f0b20780c02070240321882954050031036032010001c80e40b6507114041e1180100c006105451110050340c20540598000d01e044502d0560608014031428803c0c115407180000c08550900500f600c1d186030103c00c0c45440c4541c0c5e01f642c02c262052081401c01c1020002c150382c0944030f109040310441118006021242d001c50b12041c0c89030100710340300040846561a4007410082c0b9020424075420001c0b02c0f4480010703894425214804039012400a2081a2280e82403d003001461401c040c80280300c113119280d054107005040c0320007030b03803207452000000034256640c01c0040401c18041c0003a00d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 226784955 1250 226783705 226783709
    0x503071d0d050d0807120b0901031b23010210060302060712020330100602101a060408031c020c030a05090f03060108010b0312270a030803010e1506181504 68
    0x90f441401e012904950388510114860740c0c007035071012140c0992007148001d0314006c160303481c1e014001c0d00c014404504d040d075182200c446000422002a540c1d0f04900b1061050b080401030303462000b101c0c03c005960140800c0c0e040c00448030040040c581143e0020b00c440c040e180000c0c0c04452902d000900e4640200206c6509180300390300c41e0307403001301091016034610301440c10030010104100820602e903265500717078095580c01c1d0007411140b1005102c1000038030084a000c6075070012510a41d6581e15508010f00c060020720300515036420041c1d00c07605000c0c0388000182140e92040008800501003c001d403005040c49290a507a600c4030744001803030184241c46020ba050045100018403001c0551004103502c40503810385401c4014841e01e20501d01590740d001300080706078040b2207414482c0c60300c1c0f0590810010000e90000e52607803500c82c0250026003044820081c81009d0002400d40b082c010100c000c01124140c2c40d295810b001c80c240081680c0120340140d80f542c1044800c12440d200b5140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 226786205 1250 226784955 226784963
    0x50c030c060a0b1017040803060d08040f030302060106080c1219021303030f0507020a120203151519060c030804021c030806120705010c0b1b0d0e010c0503071d0d 71
    0x3420b800c0401400004264030324205108036589032402c6200e6002d10590f128003a02a0038134481d41d40c854441d0b0000b0360000b4080c2c1ea1080d00d00c04c1c420005034520014201a00030740c33400540c01419450060b00c4c5c1507045c3c004800b401088020011524000002c903611513001d4015442981c417890341e00080c0c0070400140714581400407070329880c1c0d41a40140340040301d000380c2d1503840e40c00e40d2200c1905c2a20501c240a50040d651010030b00180c6403441c403426945d88058126004080050759801402101b07841c2d40703100543c2e00c2041c2d03d0900e0141041c48807024000d0906200c1c901c1d245020304184544035000781071152110000307055541e026422034486103101030b0042c0070410f500e402020301c90b0890b0036901c2036a80340071688011000050000c240c902c1030712004030104650325003410405005100743e40c10307030103121a02c071000c107001301070850080030040220320042c0c09030801d070a440c0ca4503804c404111051003004101a440010740350100f0010f500e021101d015a808034995040c0750b40003034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 226787455 1250 226786205 226786213
    0x80c0f1317031c06120803060f09070c11011403180a0c0f0501140c03090d110307090605090a1b11010f140f0a0501050a140d0b10052806050c030c 64
    0x54194000400100800c0e1084007000780b0000c0c480f5441400c50b03540b40950501001002103100004d28920001c1d600070343d0060003c86a0003940d0009010901c0c00c03500480001c81a038028420410049140404074000342440542c0f000301c0c124001c4140401018034400c00015601041807034014462961240d4100c420051195202ca91301080c10085110342c6002134800f00d00c4820000d07612003520003020300380d00514075100380c040c1081800c0c1e102100a68030641307081d461117400c0d607003000598001c11001c0b20101d00c040c5801c00300009084002e24682c10f01d820980c404a4805c10700486c0001c1d8409414511149100b05c01180e00511212000d261401d1800200040c49040003110522419034a800c0a006076a03140c00241662020310501750401e22090b4284081c200c2c458090141c558081d0040c09e00c42e06a840da40c0c5051000c1c0ca10110001c0d1148040c0241d0600311a114400c02c180030302d403460955019203061505055204d14020082c0101e04a12401030500441c1c61013044c42d401c43d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 226788705 1250 226787455 226787489
    0xb070b0403080a150608010f12080d23011202090711060406110f0c031201120305090f01031806050405060a150e060301090803010602071508040302031c1b03050f07080c0f13 76
    0x1906d411000e00450202c0c9811007000100401150a13205845a00648181c01c1ca185010a90068140202071007405221905800006d100e2250809e00a04500b510380800c1c44490050008412000d481441081007407051a0388a800000340309030810307800b4000003840e00f40c07a83c3c2c113070301c9000d102818138500300001100200b402c000001f0f01608021040c0340c1c801c1c0d99803454460384407621741c50010b005c10360511903485145000981d00e4940041814041500301d8a807181c0d01c05950302000c110b541c1c03903482051106010b030401405a00041d43c10080182480d85544140d9100c118440c15016100e5500045c0380d40d2000c0d080b02440e170fa40a04010348958480d90043e48071140c0e07026490360100d070407064030744640c883c502c80307400342c0d4141c0c01461400c044a1180503041310301c802000f10795038403041c003100c0d050349265140120700d0265074006101e04000400c2c080100000d0044410003107400140010041440211808503ca405c80302c1c1d80d81741881d00d04805601d0550004503c0d589400350 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 226789955 1250 226788705 226788707
    0x6190e040c0207050301060e040c03080f0702060f0d0b19180b0d031106061005030a0911060a0c03080a051005010521010f0302030f06220501020903010204120b010b070b0403080a1506 80
    0x3c4802c2d501c04030020f00001d030722084884000c0008480103403c1d246440000c00110740d03118010084100c040d64068a01580790b00450a03a900561342243c180c040003540d401c0b1a6064800c0c614076050440b40e01c0e42c074005e0541d0308035400c1401e001d2042c5241c40785105900c0c4032500d070311000074070745e0140c6084406138507410041c00b0090340d0807542d001405444000303140c40c500003540c01c1175001661101030540c0c4551152500070529503600300ca00480301c5690f00c02960fa1080a0301c0c04103060398606451400034a802040418040e0204035954103280500c4414003000c1540e2064034402e00c0c05c15107038030114491000445d5000030f0043c011030810008100091070b100b103d03080d04e0003034007101c0c001c026441c50540d8800f070449103080000c040303000300e551074440f290f403c2e901140540005070500045d54006803c992040c0c0c0800d8456800e01692000c21a09003807103801403a880b84403a04140441e1100300803a50003d1000f0200080e140010300c004013a6407060345582c60340000c9500403515800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 226791205 1250 226789955 226789963
    0x90b01050102150403052a01090809041d06040215040f03060f0c0206090c01081801060b040303020f07060c0308060a0837050c13021902032706190e040c02 68
    0x40c2500500440420400d24000c4080c1d075402958140d8507140740100c95240c18603082d01c0e071004a0000d880095041103030290074000c5a68142c06034100715942c0c08540c0c100000c98143e540d2108400329a0320710351044e114086200c2d5801601034074514140302c0240304407203c601c0360f900714520040700171001005200040c1d2202c1650048000100541980d403801030f41e9504048070070b110303254803442c09100c05511030b030002030300101110400d81c6a0007000c1111070039107486400142203400d005c6020001c0c55810000c648000c000040580341845c1426801030481101d4400541444880c502251681d12100b002e400203160107815541a0000418032529514044900c20034008200f02c000e82110711035041d021038640d1210082038002035544c02c0c8101c11040401e410780d01c43c0e084c042d0040103515240d10400603040d5a0145960740040d100c0705c0c9504400d6042000f43e2a40c0f441c01300419100c07401192010814204400c4c500b443c04582210f2409400701031a41141c1044038411700d00d9000a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 226792455 1250 226791205 226791209
    0x6120b0c0f0715050a06052d0102120c150f090d0c080403020406060c020405090303010f03020405100e25020d050301090b030f121321031d1c060b09090706030c090306090b01 76
    0x4809101160750342d400c100c207424003407410401a012821540322100c2151036803000759841070060b1440740360340030382003041a04112043c000580010b081c110f0680c500dc2c02d0954416100684000103040000e400d6030341310341d880300c3c001c01e000c0c0d140c1d08142070045440580b0029580140f00340400358641d00b009141c00d040c14422030050b41000b000c0340d080d03a03000c0180d80c140c801c844050200545584c00700005020302801814030840c0c0c80d280401c011038401c2a05d482458108804807245079154940c050200180e290b800464000b405044000e81d0703c030b82180e0454a607407401080c40303030101002904196401803001171a10440f060711a020210070041c080c1000b00d40f8000d2485543c4035850340700f6031640b00c0000c4402d5005210407001a009007e645c0c011a187c1d5410407403135920502140c01e11080844036241000054460010030120703014001ca03c0300159502c4100342041c3c201aa9544c02501605080c5600d94010703010191090100c80000c5400080c00e00406800b4180030031811028 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 226793705 1250 226792455 226792471
    0x608010507140306041802031c080c12010302130f0c0f020c06160314040e04060b0901120507060807030b190608010b03101505091003050a06120b0c0f071505 69
    0x80006070301540a68205419400421042460340d51180c0c1004000c200c200c42d0b0f40c5420400f48402c1e0003586082200c200303403150f008142c2031003407940f00000e800c0600041407050085010807001012901c0c0850b120304603681a910810120039583c0d001c0b0180040000400020780381c08203102c3d503a40d01400e8080f5800c016002e49919802c04c2c0d040c000184140c8034015044a0024100c00000340305003001d40103d11814001418503807100c0707402d00d4044007507600b641c8058071076100288520b002e05c0c010307004000104c0031030304801c4165901c0b600c50007070344555401c1c801440c0001d00594025004680c240034024008210803404030303d40784441400303008a100044800d400441c046000e8421240598460b18a99444620b80305c980e0095900403050802008000d1005070601e44400f191071a81e1203480d140412a4503114581a0441d040340d80840d44001c0000078080104070503481d104d4002e007090b04080d0390342c94002800c0d6501d21808600400c1c404110300d150207003001c075500c882e000d0000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 226794955 1250 226793705 226793711
    0xd09030b13030503012303071e090911010c03030b030a080c060a1e020a1b200618280303170f06060d02070f0c08100e03070308061203090a09060801 65
    0x181c404096100050706800030041582040180a02c030a50340d240d44240c0c1c89002c42000800ca2040030034248039055014100d5800b03a003031394140600180a010000e040811402c0082c40e2445d00c1303141461001c2d00c2010306001401c400d80051500c29005490f0101002d8100c5003030000c02c0c81c0c4001540e00c000b0307005605010703600100384040f903180a5061181e0740b0340c00c2c42c2040b01155891100035807081d1840402c2c41480a01c8080c00c080f40d8078000040c0d4012003d51801440c42101e081c158030340300701c1d424400c1d40104205201210040c100a21080042c0c0d045404000e80b50074880e00512140c054148801d007400000040540c00704405c0001c21074a50f00c010b203501c81c202045041141074401d1070f84110140002e550511099018010290044464082c100e0081c0c542d0b00d0310301e8071078111074280d0f0031003071424480c0341040c011000015900b000035413414626440007802404003070043d070f101da04000c543d0305074030b030301002641d001c240024101001c4581e80c2600b400281a60302c112082542 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 226796205 1250 226794955 226794961
    0xf10090e090f0705060c03130b03010914070923030f0619060f03020d05030904090305180105070b0112020d080d0c0e01022109010c140106030201200c0409080c0d09030b 74
    0x40c1c00b04802401140440c02019070909080810400760040e40180000780f205100108402c107240012000504e40840060398035418200c2c42000c8d51840c201001001c1104c0341407041c20ba500220000807149008001060900540b26048085c1504410700750b1602c90400c000907132400105081d0b01030720038041c40550000105c4d8210b000c0d14070304d10400001c0c18401c1000c1015007401038050351801d00c180140d03440c00d181440050202c0f40b0303604040d0b00043c0041408071100360115413141c9001000d003070460609030740e40c1d1407041c0050140503408081200c22041800c5464401001510f04d90041c42e43d516190802c4034500200302d810409000525404603500055002080c0c3d44444400d080040c0d100218040c8050015031003048501c0c100300700c403c540c6001c124400310880c00e5084c1c2d040049030b010b14500005020703000303400710b105c800480301110a003603600c006403c1151905c00e0301d011680005a040c03031002402507040c0240c6500907134201d81140351307100c80c1c2001030768800c0c404c2d100103407 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 226797455 1250 226796205 226796221
    0x70903060501180e071203030b0d051608070605270607050a030e0312160b060f0d05011a090106020a150216050c09092406030c060f1305010309020d02040b0f10090e 72
    0x34544514081201c0b005040004284030749c010742a03407040a0102c8040503800d958035450101c9a1070721600c1018220000c0c0410301d001e0100b100201814600581000a0000809a4460b8107804608180c120315628203c43d115041074400c407035009800d03189100c08038107019207000048000c00348640101460343c00d00720107290540d40c8481ca16030802d441000d6030380d1880421100503003665445512580d00c1803165032010204400144920004910315155034024202180300800c19882850a6001440321315800180b071341110707401800c1640c1c01603140d90290001d201d11000c40005042480c45003060200005004030f100505482c1c440080c1d45002403d500c0c0c0030344540d18984050065000c1c10482040705440e42c00010090540306804220000030340290310003200c1c14800e4001159005501d27015441c0200201420308040c00341110aa00145000d038580341c0017841543c0d21400d401d0542c56886104e01d01080c0544050340800e1689005094102c09100b0112281d0083c00080d03460 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 226798561 1106 226797455 226797463
    0x60509030a120c0606050a0803070318080105010303170912040b09030c130504030f110a080a1107082d03044b1d0f070903060501180e 59
    0x83c1143c5070840541307006900c4244110a0032904001c0c2e400e020049800c401e070b041c036280200410103440d11400e0104e07600285682e62030310001101709600a0440c030740411580383c0d01c02c01503444401d0307a030341c8a180d140b00d01540c80081c0070410a680c4864041c05d05540000c05880c040035404010410701c84203580d0701c0c51040d440d94240028035400c800c0d15541420b40781341904d001c8001c0d020b41544e030810a000105080e400081c59008244034050910b4a52105015101815642c194850343c510820701128201d500c221907001c0d260304041c00312141c14a240f006503040902e0415004c4608000802c0c2d90340700003020b40c20041280d0301c045081c030740411081092a4840840a042c003600300b543d007040c00c0194410034015a80b03030380201003d41c000d0b6484131000b21990742d00da049032000d4071640014401418040049848030300120080094011040108503914151031142d5031 = true := by decide +kernel

theorem cover : BRFrame.Cov 226618705 226798561 := by
  have h0 := BRFrame.cov_init 226618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 226618705 ≤ n) (h2 : n < 226798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
