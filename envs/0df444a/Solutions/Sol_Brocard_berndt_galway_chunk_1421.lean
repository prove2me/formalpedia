-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1421
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:54:09.824998+00:00
-- url     : https://prove2.me/submissions/75eba2c5-d816-4960-b3c8-5d89aa324724

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 255395683 ≤ n < 255575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 255396933 1250 255395683 255395687
    0x30e160515040e0f04020105040306051e091b04090501060f180b0307060507030807020f030c0a0506090a0f17090d12030e0c0a1a09060d0c081320011704060219 70
    0x2e81c1c8118003440b111140051150072012045541c0640b0504105007095100c2d121001290f008550340465555144c00d0990445da4628046501188550003000340f200d18880044405504031b407860702845e104c924171b604120080d04000003030406080895000765848001c0c10540c0c01c4e6074055a02c3d00d24050b035a01c040e0401044042c241c95550f1165031400c0200c0d54206c0f0004001000314045000740744400211341002c1c4000c1c054201245c00510140c001d45c02c1007800c1243c080c0c4017854542c00b8180084c00031300e118003103883c129042072500d4002050b0308407038002c074815014100c3c0e00200c0230000c44100003400b00b1804940e5002c2c0d40421040403500341d2a030750340d9558140580c2c450a00d02c001c101c110b4002211302240003a4018030b07410841c000001c200d55800c6202d1200c00c6a4595414440d15030b1b0003154103034044d62080812890b0411a107075002a807005030540300c0c0c3d160382c42040440603401030711048125803c4480c00961890f1908221000b500701190822030715644285001e0114 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 255398183 1250 255396933 255396937
    0x4051003060b070b0a0905010f1a040b03060a0507170c070b07030213140d0212061b070804030816081902100905030301140114070501090c060507080316030e160515 72
    0x5a4900040d41c0f91641c41e48441000c80002855290a03546421059001540038041c4131154061240b022a000c04200c1c481030a00c200381075002c0c081ca1a280300010039030b40c0041c0254100c026800000b41d19100c12400300c03182c10700221651110a204c0c8244142d40600f00010301e0150300070310700300034291034019003101a449940908564540c035201c007800310a80c000601d0044860045c890100050079030301103103504040844044003601306c10100007001e8403000032800404403030003500d8500041c0355248003040c040c900010b0040c032804250110401403112a03252404d810084058844402c480405c0d5540855106c2d040180903480b130169003200c20313029415010fa8440080c40c190384c204902c804010081c40e00d000d0420003000a03408041d51100000d00d5500c2c05080046114a0942003000341c941882c0d003d0020007004000b01c1c000319082d00305903604803441c0050020541d80c80100bc8014101c3c01c00060868000d151307120801c00207c40c0d502c001c5820a40b000703c204041c403d0013741b28 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 255399433 1250 255398183 255398189
    0x10e0604050a120e1e04020d1103011809030c060507031503060c021b1e030102090402130608010e07080a0e07090c030b01020601080d05040510110d0908010e0a0c05010c0807080a0201020405100306 86
    0x10f04940110a18a0418828017502c000540f0040c10f00d0344030480c080940300d0380510603040b504000b006020b0075030f0024910707078208a0020184200d0b0410f540051400b40021805007075541d40b403012600d4103209421403d082d1030642c00d00490140c480c00e00301e008000070949000944a003400e00003084142500362030200c040185409884415114001040681054002d60555081040d000780341d035948080e010004d100b60034415401d0030a080a801041c060b0450700448a015007000200c99012221a034484802d80000c00e840038200146403500080c1e800400c1e0440c14130751915002907140d0300424000400364200c425990b65441d000f5202c01050403a400000c50401060000d41032203005c400c00c42d161072402d001c40c1c81100000070304180010450a0015030303809010005202d09001d082c01003c0140c0181c80721241c1c0303a45d04159602284961410300918054038414061148203544030f881d041000030b42c1e5000c080310000c2c001d5202e0300529115041c80c00c403990740b00c0c0c4644580815 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 255400683 1250 255399433 255399439
    0xd031a01030b210114010807150203040e04082515060b0306030307030e0604080706020a060b09060901050f0303120915010e0c18040209060a210b0904060b0102010e0604050a120e 78
    0x480b407840c58a106100245160f0000307907494507515803841c02c0d0040042d000f040c00c0405031480500303003160300001c1d245040880c8210360051000780104401044600d03001035000362110f588500241480c089000d000c0710031504034810510000c14407000a003820b41d298428a0100001ca0302ca180b0200140030542d440b07905548203011580000780501403000d81410010250b50515680d03070a400d14008098000c5c3e00180c110051100c00c0002078004d03508544d00c2110032000340c0c90310b000882c628200502c81c0c644111300a200c1030600da1000d00c1115104501c00e400e5070750600d0000089a5108802030f103488400300340038000601c86603505061400b404002c20014500b6100381881218020440307090307a4000c0e0b007006900240d9840304018408188203482c1c20444081c0c10055018003850040304020640c1410303081c1400c0e59440c5000c07a0301c654000400228000c200004178010501d1145142c0288074034028030040c400001880c508062144112561590100c10111880c1c0c84080090390 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 255401933 1250 255400683 255400699
    0x190c050a170406150308071b060c020907031d010b100c030f180923061c02131404030534030503091c2303010e0105210d031a01030b 58
    0x107581c01030031a150300640110000305070302c4500300680007004045c1d80b084030207410008440d000c2141d01400b091220040140314081d2a04d44900a841c8250400c0000e208410610001da185c1c0e02982c0448840b5850035015003100180f651514003c00d8a1410513104501c02902d049040707104204140d40594996280e488001025a05a0f698040032803c140c00001c5a2404582c01010b0b01c0340564900910130250008503011a10031001d4901800e0240106030070003060f5160920b9098a002ca95810780e4041d1a02c40e20120801c0100007065104003a034503004140020303d82c1c04000307004e48101181000340388802d402c0c244d1100c1480c2c16215280c115290300f074040800c1c05480070710340c009541d0040d01d10303d032000c4a12900e00b5040b62100c03c08500d000351070105200801038985021a5510402451035060442e280d80e104014490b991180c2001c0d2450404541d03400c03552080c4168000490f00400d2030720001070050100442c811605c840751440a01c00c96109008030104170301c1c00b40c0164 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 255403183 1250 255401933 255401957
    0x30e030c0a12061e05070e090f070e01020307061d15090a0b22051e07180b03030c010e060609060d03090504020d0204120804030302010c0504060e0103021b06190c050a 73
    0x369142e0702403074040d60070f180d5440406810110700c0c1c0200c2040744004000003080d03d4408000307040440d01d203903098012509601040003c101701d00f140d54202c143c5003400c14584101c500101e20398454000010480c0c0c0c100fa10b401a404138000d81c0c2e40f102103803682901c56403401115050004001100c403d074466015440310f0000c20307030480301d171500203204009441c51660205003109e00324043c140115072507032240040c00c40c5000195440315610307000602a010807840e00c014868541d05140318100c4042d5203100d0a40296020802c0301d82d1000000001d00088003e1801d0903140d2404036000c6000b01700e882c000450b0351808013030310010280c2c19250104028200780500001350440c105018510387d0030030001c40e804140082840803984500341c144d64842c1586002429101002c0302c400030f001043c0024000190058854070451000f864016210449030000250b00020242c544540303001309002c0c00b200301600c2c1d507508000f0701c3c403c1d4240b285034903011003240d6901ca4406200000b4851507184 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 255404433 1250 255403183 255403199
    0xb07150e0f0703080304030e09102103120c020a020a06021b2b2603041205070210050f1c0c020f03030c0d0b0d0204020a0f0906080f0606031008010c0903030e030c0a 72
    0x3551b0070900134508000c0406112022402e505416110343c0072102c0440010410962720b0b03504584e5400900740d14401155481e60003800c04c005500271200f80548a8031444001032080005144440d0010003043c0b503140e490001079180d20000e030044482c050f559440e15000d040420b801d110040d0001492080c1c1c883c001380908071210080821544a0320094656080f01c5002080324007903404032700d280e60b41e810249084020032100004100900506000400c05642c0341400c0081e20001400c2981c2d903030b09000d40140c6284500c84628052100310f0f003c001c0c0048550784503400e07600d40c031707001c40d003503248c44450680c0e0b00d003c21921514402d4081003400b5064645401010400001610380d42c0c0000a9034001001c5c1e0308410212400a5100c01da2420040c2d40108100c00500c3e032810103920b01e051403a01c0b0400c0f42c00c01405140641c2c0000041107401d0984000c40000b0316840c002000340244040340100800c20905c010b500140d001d040483c131a1070003240c001a01c0c18001c088400700d83c030380006 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 255405683 1250 255404433 255404437
    0x4211124070e0d1205041e0b25020402041511120a0e010215280507020601061409120c041a0604050d030915030506040c0206090d05130b07150e0f070308 67
    0x18154100c0690701480002a4140d800b40c0c13000002a11a41e865505000c92121280c00713201070081601c0700b00400304074140c8114100c07950340e440d0401100c804400e65200d051816050f000c02504580b001400285d50712404464115179612503441283d1400f0b20800180d03595205c20300d040c83d0010030000042018001c00401040c1c1c4410b0050352010643ca641540c1d40500855200600d000c18003241c1904254040b0034840e07881c071054041017a030030071203c020741d00e500500552041c48100049495880d0044041d83e4a202001700324001a5500c00081c5480707422a41c0414040c9041952145643e500d00342c642d0b00c00e00024010a04152030142005441060000140d0500c01c000d4808612041d5044041c00700d14282d8501140c0307070818005007c00c481060f0102c6086400c04801e220401c46c01284c0c0e2142d0125a14145071039216408076121410744a5000100000c0d000030082c00700300d0700040900f050340520004211800051060a499203a0003041020316082404140002804c07940 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 255406933 1250 255405683 255405707
    0xf1b0313051c0203071e2709030507021f030b0f011e1107230103021903050606090a030302150f010f090e0c040e010e06011a09090421112407 62
    0x10724041d0b054030715000300703040c91800d40055907000784014040540b0080c0c0c81c0104010f080591031003103142c0200c03490900801d080c4241d40d000c80c0e1030350649021704d1320074001da070201030b001000808000c000044069880c5108061000401d051150400c6a0303d000940c960301c03914181c4514a111284038000484a244003082c03000307011b800b00310800b1054007080100c010340008c41034840c0d51740d00c03400103101210581400034100b60042107034100540d0900c080102880d0301c0e04000c60181c44502c00540d0f580120051903802c0300480400006141d400903440780c00040d903c03402440e075158404174164100c02400b03102e1461403206020014641c4031344c4001d80d00500c50007a1a54264940001b40542d10442c070702c1c41d882c0e074591070260880b400c284215401401c0344880740010071446244e440030390096141292144841c5400181440280044405083e1040101d03040c0d600703144030054060610506501d02d03503c40c20700c1d0780041034100c0c07050111540c1e018400802c00d9643c100708943e0303044c800b4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 255408183 1250 255406933 255406969
    0xc0e06150301122a030b09060609010303090e060a0e0709170d051902010902040507120c020601060f0509030c0301050406021c0504050a02042307120b0a0506160807080f1b031305 78
    0xc10340072114404ca03c00c880510300c140c040610302e060851020b498031601529107403098810400400010f0b400004030400c90382c2540683c40203654810005001003550b42c00396020a914078104900b8580c840d034084103554a00c038032003101c4064140c03c41e6460600c9031061000c01c00403c00848015094a01c1080035215072001040c01509540400c05440090381c608000c0b450301c0424988580c802c0c0940e540800d850310045c19250701d040e00040624200e40380003000d0001c005807925158909010103641844050024015818149800c0000f98006052001c110000e14040c61070f480c041c0c0a0380303000ea0341007401414020015002c000c01046018880034406141403480c01881002c2000a4446e80c0d0503210301c0c2c1c1420024040b1000e641070f0410080c411a0809805c0c04903035510070907225040100304800500c0d071070300d140244040c4100007002c0e004078801315801d410f0400580040511409101059180c0b1218440c0700b90b6900415408010810a2100612103810074596040d1840000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 255409433 1250 255408183 255408233
    0xa060507170a0302090f012d0215090a03030e03130b2107020f0d0311040b030709080304090e0c010c0f0620070503030f1b070b060103090c0e0615030112 67
    0x100026001c254402038845020940100d402c3c801703072622507210741601c2c100303081130015240813904035526400602550f1300e00711105103000719628420440541001300300c0310444041d0800c048159910740c901402100000c0c00e02c5140d10f1b00d44804410b40707c0d4081000109420784d402c01e040728200c3e40101400317002d000408410503000300c03040c404281c0200307200c2d0054444038082c41c0041d81080401c035042c4041c98144034541d01c9460012084504450305000c0d000d4a03511400800c450030660b55100c0842840082000f041d0b110003944100c2001c80401c0c02c80b411320203610019100d8542d80300020704501444c00c1101e0119403141c104410b81c852010342c510240e070f02c1a80a445680220380c00746d0710342d480841000700d03000f000412030760001c0c1d000030080440403080c07040c44120300c2a008002c00b62401e450216036140d0003500103816030340e8012082d44400361070303508108110f070b0304446403480346005660031801c2042c0c4008803416035940208003512401292155901c1d1020f16051914201038 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 255410683 1250 255409433 255409463
    0x1603030206011203140d050a1512020105070507050405070f0809011b050d0e0303100801060b03090606010c030c1a090c0a0302010f050a1b06150b03071b03020c1315080c0a060507 78
    0x5d400014108400701e07100004903030410402d610203c0342809856045034000c2801800a54142c11b0b0207040175a0910300141e840c01140fa14604256603940500c2c0c05c107003400284140560045444000018181d9032401c0c0d56a41c100342c43d00781c44480c015140c01c4090a4010790603d8440c4008000320411484c0c04101c03810469280307442c561048600b00128000b2080030700c0a45001c3c0103450041421200c4641181008100f20780c8680c0c0c040c10041c14442603104400030503004034031425015400c9110081507c00d40c008400f191f407001c440741c0d03059002c0d402001d052440c162801c20203a9070107943d0700545641010003a81c4981c41044042c0500038503074000b001c0350500c00248a0a94410130020411001c0411044146086508000001841031041101d441e82c00009400c020034601018200010385080c20b0b800e090180310304d9600325103c051641042c07119600040e4641c03070248074030720350190340300802922203501c90490340c0d0088003100100641c40c841d50251110a01a03080300c006c0170070f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 255411933 1250 255410683 255410717
    0xb0f040f050d090609060206060f010804020a0902070308060a0e0f010510030f11070302160e0a02030c0d0c02070e010602030903120c010b0d05010b040f0515010309050f0304171603030206011203 85
    0x2d0006103400016001c000e0502825038002e03140e0009242d1400100080d0030481d001540c5101c5640e045410001d0050004040d0340e10400304c680204000e0320115900c04140c10000e00104e000c50301140110084000060001503a01425124030004440190264241401c20605100420842c2c08060b1600c04200c102503103440384184404007982401e50729405444c02a003071001c0c881e40e1090603c442d103030420a503000e481d862903010004500c01a500c0d070720f00140c0d05141c01484140307061a407401c07080a50003a00011120309a41070780103050310236071340c07188203d80d01d100301101560075801004402c003002c44101c01503e41324a0940000c240039501002240f0101c11150040d20260b4591451710401e0800740f003801c550100b660814402c0b49030072002142408168010281019910008282071000602451090148040660396aa13598410107080c0e011503600d00605800713100503d4082c07800303242d111411241e1540240040360701e00542c0845840c000030303007030b001e01c4402890464045 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 255413183 1250 255411933 255411943
    0x2060a050c1909030623010b070602041a030603060f090c042309030307030c020106051c0501060302041d060c0c070314030c0d171003050331060e1003090b0f040f05 72
    0x2c8141d98031884100d141d070602c002503c1c0c040d555014001410f8169128001ea0108a035041d1020f640c9507555415144c40c01800920950340311180201c80425401044200d880095025103411000c482017501c40c0403103600855003d88000304258031240d80004c150405070003584102d44101d05404c80e40120b02040c4240b080100c55441040d00000108182644c1610a005000340c0c81e1000704289030600c004100e0082181481961f103230f5882c190300c01040003d4102c103019550107001844440103101c0307203018000520910a2181c080c100000f01c00744204029601b0303080c00b0300e009005152441e2100c40c0c0c0500507e00c41c045d01d0008020348003050204100d40710140200b0fa03107100c1040d4408144419540002e498081e0703090058800f0000f20308000b0507940c1a90301844d0407459006242c0102e0000c108041c20601040140740b400180d80c0e40200e007031100000b040d602984003e80451049049480a600c020460312456000c2018440900c01d690350242c440c41d00d0303d580300c0303c03601c5180c40c1c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 255414433 1250 255413183 255413227
    0x10b1003050726011a16030f0f0e0a0e040507081207060b010f0807081f030b04020108071b0b040f05060a09020a08120d0203040206040b070602090411070302060a050c 73
    0x2094a841c20300100310303400010001c164081c02c018500c44500910301105112041c481c0c40e40405002030079030400c0b0000b1007102c9006035010788601d41c00e041c82c64041c00307207800c81200e0004252101004c1d6502c6009014040603544010a0503010505060103003243c01005002966107104010700487e00c80c20812401d040c44950802140c0c41c0c400a1030504107580144205030f0422243d00d954400c010b81001806810800500b008010341d40c440c001d0070395441c24860f0702e00000c00f14613800000d000080c0f100c180a24000e85c3c82041c82c0c0c1d601c4030705545e0010b14065034440c6c0802c0a0380c041c0801c1c0c40b000c4482d0818030400d8140400792281c4c9400c0e00e0300e8410f0703842c0c034006a0307178005030780841c503018071440010107020300680300fa038107142c07420b03401c0303020390705800300201c0e000000102103540d520100c40c0a449a51030700c503200c0740e090401800a41003424103d008a00e040308203d0241c004101341d8840590550051103540d80d00f00c0844081d000c00b0b040c41e40070090902c140c00741d6000c3c009541b842 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 255415683 1250 255414433 255414437
    0x1060b040308040f09061202010c14030a031e061203080717090f010b03011a0d020d080406020732010507060902040c050a021b180c0708030a05040320030318010b10 72
    0x219814071500004c2c1c3c0d4019800045aa03290600400414401510084c003041d0242002c8224074614102040d21681d00040828a07010019104204135003542c400e0b0310b0407130101d400c0303040040000400d80403691342d07000d002400d4440c880f002002900c180d00c170701d40c030070740c135280a1060101462042c41100340c141d814652a0308003604150031114244140e0782d510b18110024420a0603c44c00c1405228030004054040d45041950200f0b64440261a10b24540d000080341e50751941e80800946400365401a1a0030300001d0400751600f610201c50b00300031855490780c09800c900041d005644a41c040780003214003070344480d40c07000540d0f1684101d0340c8421480e10303144c2e50f0340610358000341000e0b1140c564070340c541918040194175031141f040c0c0700803403062503000306203e440d1840c030741c0712a004901000300408000400c1141c902d0142c0c01c03035802284281c46400c0101c00700300c040500903d081071010625030090001a10803620198000521a04940002068003201012800c041c06503528000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 255416933 1250 255415683 255415687
    0x110d1101020c03070302130e0109080c03030f090715030f0902100e01030b0105071101050a0c060510031202031809060409060501091d0a0503070303020d0e160602061f150201060b040308 81
    0x26940c060200152204084014104043c15580041c1d040c001041c1a00c26031540d0356011121184258008007403250003070201a210541010b042e652a8800c4802c8508a0388000c04222003e00001e600410743d02d030b00b0300b5600d03101038000007100140a0625548a11600d46107101c0150319204a1042002c1455444001200900d40050217940c0000f11881c1041400c000d500003043c2040d55407d43c881092030090341d00e642441044450407100f200190901c0c1c507207024040c4a40d01c0b900000b080740d11074081036001c198806016a100e00415103141d5035030034481295042440d01c0319019912042c01400000c442d00a903c4080440b04243c103c001c605680b03e018910b0003000c00d03528172894104c5402046864103c0e5103690301c1c4d02890b400141031580105542c0d000355400d03081344000d25410f030119000301c500e4680380c2c0907542083c443c1c1d03c0580035020104503548818500880c14140340d80d401c1040346c0c507010765400308003030050a100455584940c04206a407041000b40002c50284c64207075 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 255418183 1250 255416933 255416963
    0x30a0c1b051005070c020d140304030219140d030503070f09121a1f030b070e040f090209070201022a15011e120b0403081315020d050603010b03030403020607110d 71
    0x20b001c03150058110414401c2900c25840141d49800e450160b42d0f131700c418041d003001851410b240c918041c0d03130402503104841c20440ca00000101c1181400c850042c0182201d884004091040300b070300041c1c019002400800006a4841c010061a030102c002d45c681b0710380c1c1541c0c4400c40d030003542c0c2e80001150f003030302440d1349065034501850005400450f440305040408004030b082c22803146561000401c082d1000000540086c0a0103142d100b0701c001800c14407003500005c10f040700502c1c0050f0206c4c407400040011924642c814426201e00c3e0200d405908940e401c0c001481104207070004800c0d1041c4221020083e4144106603101d00a2a040784803050000c805a1a25900d200350f804c819541400d442000700030485840116030420303098100040107480c0c0d0200e22036156006140540386000c03904200072202c440340c1c018840c5001c40710f801c002c66180c3e80101401d80c1d80c1c0849003035141c0d005110920161a00000815949205d2000c6a041d80c1008000ca41c5c080e0a030714007550700d00720449800d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 255419433 1250 255418183 255418213
    0xa05010e0616083007170a020415092c0a090204090206040603061a070507051002010f05041214040e0a0518070e01090f0b09190609020f18010c0305030a0c1b05 70
    0x15a400c2c0c8000050410605d420a002854a04201c45506000c114200071807201d1031154100c0c0d000d0f002e809110012201a01c802401134105442007e20803401000030110108001e0341c26030301c01c1c0350502e002000e43c07034030903000c4003820540005030f80c010303a241d0300708006a9483d0000d200820150700c004c40d4003450f00706c840500100052020039900070270441680041c0300821001d0075180100e43c1504840c0c00d0040490040c0250b1403c0c0c20281d1419040c0824031007400c6682c40f81804940c0d0300b40120208840c0500b1500440c407034103030045e40301d1000c1160045c032034002c940d016403801850301d0703031008a419031307480e0103444c0e440fa414201168005100803003031402141400380404a0510191074a200840d080c1c840041445802d8464040c1e009002446900128001c0001c900305640340d02850300070010320342c4018040c6015811460003101c00f540250800b24040390507440f00d50550f80d5100b00c1001404a040485003042242401180410021101c814445008000401030001082d0407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 255420683 1250 255419433 255419497
    0x5090f041e031b0c090c030e0c010c030c0803040212032b0902010c02090a0f15140108010b0f030c090409080c010507180b0c01020d050702030a0e0a05010e061608 71
    0x1c0d12a125050401030010942103007443d030b100001914000003079601828042c082d00b00c180c01801082d8103002882c40c2d810780c07503005202103400c0700d002e68561000e11001599080c2123148000c2c0400c08100c901d20106007210040e40d131090001d00b9003424911003441d402d0456004038141d03600080c031150a102900c80b904420341c0040701100c0104050b40b45a000a00910b00e400c10080c4140f403030500281a00d8011f4109a0340103800c942c040c881459402105035440c0742c540900c48001b00664100c107215072080011504980c04500880e26080061346094803682c0010b000640c05001000155920384503407050860940c042c0034050780b1001e181c441d603030941c0d0780541f408003001941005040042c2a500001007140c128a16440c0d941151219032400fa0048012b0072021030705e40010010150707004070003444038a050f50740d6450020702610411000f50814002c00e80041c0e640e01030b0291030b00700f0b8001403414014001d80e001c0b58607041d41e00c0325080e41c01107a42e044030012440c4520304454007400c0f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 255421933 1250 255420683 255420713
    0x91e050a0f0303031526100f0c1205160c0f0206131e230a030609110a0803040e042a061808120a03200c0706110624040605090f04 57
    0x200340741781c05141109040c00d010000c05101061040110140c07200f01003000b980c3c0800213070b107406100d240804030754840101321544c4d5107004981100780c6e01c0a00c1480e449240d12845580d8103681d50b0301d02c0e1210450300c08000301c2c81243e520360154001d20240c1d40c1c80c0c0290802004129010080a041c01e04000d04000158401c40d240142c035501032022640401c100009c9880340000d0390b10b540c800100141141840d6800540304500e04800d500900c042d4010140307124000b40d9611809990f90109036541c0d101d0352040141038081040420300040907100300c0c0140b2650a494144040701092114074507028543c86840410040b100b141c503142549010b0100601200000d828640c00700e040c0804948a4945110200342c1d83c0d071003075001d0964036602121005d0710400b2545d00c2c0d00c181c43c081d9695807a02d00649010590107980d6405c803000c0055980c0c820203140d83d07030303240500c65402900180c074003580e9842d40c041d4a070303880411a902e4461640f407003081218243c10b01420942000c811901e0005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 255423183 1250 255421933 255421961
    0xc080d0e030309093d080d021506010c02040219080613020f070b090f060705090112050402030a020d0302010b040f1407030203060a150e12060601030606090501091e050a0f030303 78
    0xc015010781c4d5640e10080c960044929410701840100c0e50102001031640c900c640b809051188111080c09600c45a450240c45848048461481641d50280d80d5a5840c0b01e2200c0e0001064002800f15407141c0404e0503000d1019002500b40746950141d400703550b0702ca038a4840000c0c090300c10001c0d00c0c64008600045802072003c11881d26a00513881e151501c01c6240190000c6030034008595007842c02c204003c144c038000010b894090501160041480e0b0040c40c41c075000840c0d134440b0612103806031003103a024960090041c20756001c182c1c24010081c0c4d046005a0565683d81c40440c400d44460140780e10071a500c042c000740c0c0c00300710070b000781126001a00040803d44103100300031321502e4510100303080e505142c02c1100062042c90040700c0c1a40b44481c0d56030440008030100c3c41069000481500030107090b2818400d154544800b2a8409014800d440c001188540c0c200682d16503000c0c807051004c40c240c00b01c980705032500086000e0501d598070840040448103c20011316502d40702c1c02c511800e076a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 255424433 1250 255423183 255423187
    0x604050d030c17060a0b131a0a0e0118050418031409030a02121c03061715060d0309030c03080c0f030c0d050a0219060509010f090c060c020d0c080d0e0303 68
    0xa0020003880341070b01650074500d407480c08900c0540d5178000600040580800c0c1c0ca9a4000d040740407003c20f4014420481050280c004031742071501d23003400383c4003d1602681c950840e4400030b001190320109000080340034400e6520082030540351405103028030b1118403010f05814556240051001000602a4441e01418012000903560200b030242001e41c04592040302c4880d48100d16041c11050040e01c043c8406420ba2842c00c02c1d0180c0120b800c80303c1d010704c0070343e4070f01001481c2c035202d040a00405000841c418001010f0785030a0107004003190003840c5c070703c1c00c039500d0303549079410040c90b82c01c01e0b12211404114804880300400c00c941c1d140507003138040c0d130502515985095454112140300ca041c01400b0850030b004510070800c42c0802d000d2030b03006c01e036034501c2c6042c524010302c4182d0701100c00e5401d0518450030350f0050300075141280e41c0900840843c0c1e00d031020480e00040d400340d0490380228192920742c0811504da02d114013038032070b2501909a100d54200040d118030000e1089901075001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 255425683 1250 255424433 255424451
    0x2030c130b0a0f0207032a0b0c16051f03020c0c060403050114010501020a03050a030c110d1206080a080706090609050d09090507171501020309210105010e16141306020604050d03 78
    0x200c0d0755900c24461080340d064081c7d45500e1209001250708540c1c3c1511002c500c407101081c0c001441d1410456071000f4000c80390712a410321840628411044542c280090304442a091103640240030070248441681c00440203031000aa40740c1c0282d005a849070745500700c1d41d40450504400c13500405090000704010840f540c5c0c007600c10b00401248005250b40c5020340580680604100c602010200b000c0e81d04030950301001501c0309250054403902145004c4011540300340002c1c240d8021900900e42d22304040c203a9492901800744001c080b40e40544825402c40094001c01800da4615401c2c0c03200000641003514850880c3c100034110420031000405829005981201603600003507141d0500e0ac82103410130060f0310f1032088010791745e00540b100840f48110300041564540d01c0440b03000900c038036681c031111240300038010f84002c85aa00f541c404001054090301c50450f80c0089654078500300421a4540d882c01d1519520a50158028100300800c10005105a03070000089042c10000000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 255426933 1250 255425683 255425693
    0x6030103050619020909010312090f060203040b13080114011d0403120207050c090c070519020604150c060603060507081602061501091211120c01021002030c130b0a0f020703 76
    0x14001120802e107020f54940003280c04d03012070741c040901900015603543c0d00e203442249140307020703880000200c051030017203400755017005a182141d800e94002d50416081505001c03a0fa071042180090803091440c0000d4961000e02a0440300c902c030740c010301e14540c03400324150144103841e45c9944030001c1c50010000066040350307078149807081004006813250041d1500302c0c80c000840b1f0a0076440341981e000c003c0750040d00e600801d801440380c42514001d4004140101305003100c0c020080d03200c0000d0105014680e0b404042c6490041e0500e4003100c0c1c100c0a44900084803010741056481548500030040e03c1c40c0c000305a01e42001d83d610341c007402141882c0c4002d46410000d048010507010003107039406542e203d02d43c003401034103d5012210039010305182c045d16442e082c0b121039000700414204002d04590101d4126600172041e005440d1880c20302403400020741c401002d5401c90a414040907a28103030f1404810040d1220400310b07990391450034009013000425031070201c1151700000e03040c03000603 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 255428183 1250 255426933 255426943
    0x7080c060a03050612101a031f020a1209060617030a0c11060d0f06080c09010608040b06120a030c0b0c090f060a032703140705030910091517060603010305 68
    0x400da42c40e0000d29500d4060008030181c00a2580d5a414443c4a4050031994100c1e4403200b207030111386418984400e900070501d40c950b20302e21801944101d182c0752104120800c1d400170000301c4201c1c13404074000c4828100300c0c0d04031031241d0b00503030307030182d40740014404003040c001c2d000070800c1c005c00110300b401304c5032030300800314810305100511240c4060f545401c981c030703440d040e1044038180d0352081c00f0360782002200c1d100500403841216640e109005800343d460038120800d074180c4080b5962880243d13101d0302c5050400f80c01415041c0c100920300440c1c1e40c1000203101000c501c0e44250b0381c5010080301d60070843d101d500003405425081c00d041250080390354401c46280c0da0300c0c405894242c0c035903c65020503402008501c0e2100900c0d40c840d010041c1e0b0840c68401c55003c1d5100b92115408580f80c0b2411540d64002e00e040141258801c221b03003002c51500442454000d42d8925110b8440c540303552054117400e03a442c5485020401a82801005049032140303640d01030015203130701d82503600d151602c90740c0d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 255429433 1250 255428183 255428197
    0x60403260609240d060207060605010503070516030c0206120f1501020d08090313180e122a010c03020a0207080d2a0204090809030c01020105040507050613032307080c06 74
    0x400e81c1180b8008400b0800c80c5141042800800c80d0011318104d04003d40690302030072085900030701e07002000c03410398018019a4080d10203982d4283c04d141d109614150340001d0b80d04190180b0004e803081200681c3d5580040452044141e401006801c000d81020710346000506a40c1404078151074101803a41d00040d4020082d9213440c04503c00e44600d20418114841d155a0820714040507a0120b000b05200070320120071810030504002c0034018500c00c9450f800502038030481c1d1501040894410441e40f14055400d41145400c2c81207620314051883c2128103940d40507000c242c0225001d00000e0b0140311401c0180400406480d20006a420080070b05204030030301d0b0201d9501c00015000410711040e0032a54541c082e004012103151070802030051303045071034801e11920a031071041c6d6840d48180a1341e8040d030342c03002c024001181058100a030f650003d80d500035161071580000400700e02c51a5281e464030003644124030800380e41c040b42e141420a45e80105c0c079650700c0f0154805c601e07144c10085a840b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 255430683 1250 255429433 255429451
    0x1104050f010e0c1309060906030b0a05060f0f210706090501020309031510080304030303092009041203090609060911010f0e041a03060f2e1214060403260609 69
    0x5600e540a80c101d044c01c186401c031030542d610b4140f01068980781c40c0d0054080e40e001d0181200c0e260303a9a0400c00c2030755000c403801031304041c010a011445007042040c0310128100108046803040c03241d203200031719401400c3c1d101583e82c00380504004403500041100054442880558a007480d903d0100e03940e5607115104030f00500580b070008000301903c0550b080504401d00a50b9911541c9043c01006044151000c1e2280d00e510a400c294081080481c404840c201603c0841181d070781d9114a800c1c09030b0304100d0402d2503202c40000c0c1c00038150f4800c1c44080c80c450035002a402c0b0480c00c0c003818460754030000c0b50602c200b078494400700a4100c0d880043c50b00c8110740201d1880303008200c200e81e80154404243d014403c10050280040d4192000d612800807a40c2c5200f0400f0070160021101c0c582070002940c481c0030070000e2084103440350345c40b131200f402a0020500c00d4032000a0074600b40301110182c1c000b6105040f0403940d491204102d2642d8040445ca03440c41d0300304440060130400b806840d6501c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 255431933 1250 255430683 255430687
    0x21e09090c0f0603090c0306010906030c060906021e0c130615110601090e0c040f02091905010509060d0e0303041202010b0102161502120c010c141e0c070807031104050f010e0c 77
    0x3041381020450f04031b170f002018080d1109541d40e1942c0c0c20181c503441c002191842c0f0300820101d0301911a01955084440c6980107100280c250f120920300d8400007002d0000c24041da03500c01105868003000080f00c0f0b5076400d0006840b0303280032044c4a0b001500c500038010402d82000c0d54480b41000100702d410f407041c0240000b0f0302d0b041023540c1d9240030a66210b2503081030820b1090001c08941e030340a008080d07025078090403c031f080004c9011411a90b80901da0203c4c0c0141301c000800e041c804041c00300a205013500058820380c84aa145c1f81d5002114101c803d17018420200900a074280140c9503110002c0c00103101c1c0b001404500708182600d806103110315100c652032402014402c00c101e44000c01481e0740c10b603896000c01c41aa002c2c0110828000100c0c9400b40c0340203d03064500111140c22401c2209140444c610052005681c0e1082030103044902c5000c0021803542d109002180045105d0fa42c0900c6400e41d00e0240015034100908104d2807079500c200402c513400300034200340d50040d1b95010303040d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 255433183 1250 255431933 255431941
    0x150915040e0117010e010c0507030e090106020601091107020a0b0a02070b0c030901030e0c09090601140a080303180304090f020706140403080402100c0501140117030307050a1803021e09090c0f0603 86
    0x41c1c01854018040c1c500d0b0b47c00e020001344525040380043c850540039559140038220003909015682d81c082c4070300c400584c0250010020000603600480c0520300e034030031003440c1034102d4002885e00b2a540d0403075114100300203100d40002c0e13010441710303009220303044c4010b007001c2042d60510380700d024502860b8145501e4141c3d18114210601c03a84c1a80c1d400206039070b5540c1804603d843d134590003400f6a4214000c0050008210b24020080c9001c0320b4100e40114519a200032500603038030090301c216510b0388000c4c00013283c1c0c01d01901401300c0142072802d00680760041030500c07609076001450540c0d01e00c0041c0061002007a80141420fa0080e01541c24002c001030f02a07041301c1c1c05800c950040c205510b4100700300f43c0a4209000141202c0d84450104880007143c0446910b0384001c0d90300d00082481008840c4c5094050643c1d10f02c1034014004c1c02111030713940d40100e543d8040c5d00c9002001c0c604014825402071400c0f6024580081d1903c000344080982d140119032407850007003000303214180c00310000e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 255434433 1250 255433183 255433229
    0xe10120204180501050f060d080d3222020108240d060e0606011e0f03141501091401140304060e1e0d030903080402061305150915040e01 60
    0xe06041d52200b446103401d245103041050003040107440707049104801201160540c940500c07104485078209000a14120f1100c00031002041d000c43c51110f4490054a12402542d025800c80000a551700402100e468180c0b100c6106184804090009000d00c450303040242c2d900080d20b961000040c004021000c803e58074282c0d1040d217440715180c0c842000d405903030400c81c2a4100351380000c480400c4031010b4941320010356030550055445080f00518103c6801c0ea42c0c0308066030b503065540e1f41800110708400603003140c003150045502042c1085141207441065a010240c200240490425014070341e2210300020304840e004009540103001c044085030601c030287c0e01404c489418402100d003c0000850707c0010b0240c0c001861005000341c03092002007900a02134a1500c1d036050b9501d100c250394030f0382000000d40081304425501c0c00c400001040c40d449000c0d60080044569492a0b1984120810440901422080703e50705c64801d00040112980b0066940c0c107465204243c428002489141 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 255435683 1250 255434433 255434441
    0x12080418200702040b1507030804030c150b011e0906030906060b070b0618060a050603071b151d0c040902011101020301060e120f0a12020c03030d0f060e10120204 71
    0x216501e14940025102426110300c0040c0b0300584244c0707051080010840c2080421302c1d0041c80080e064604110713100020784242c4005030310502c241004510458591542002107090b02600301c502c1e41e0340ca440810b03541e000302000000072903241c0b803489202e800c4100207001d00400c0c4250702c24103858002c4d080810240360820405401c215501d40e07108d080500703141d1040c06042e92890701906420031038110001341107400501c03604000e02040c0724249401c0521096900090501d002c0040c00449651011210358100550900074404082c50050300350510084810b008490490310121601403480b4510110718401001012100000c9420240c00141c6450401d41001c01241d4030000003c18030301d4010244110380300f030a560215004502c1d0003ca5540c2040311000500fa03032007900c00350001480084540e85001080c81941c4246100e18082860f5401008000030390903161074140746010700a100c0c01b4002e1844110050381d44c20040c43d040c03804c851360302039058110300c07803d1a4010340d115900 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 255436933 1250 255435683 255435701
    0x20705150417160b070c23060307020a030e0406050906090a092a0608071b080c0a0803162d033e0a0e06160204050c030a0612080418 58
    0x101c9928002c541100030b91280d01c4203000300c1c500b407841c980101303150346401d00f600d01c13a580c0801c4500056080c0082d4060450282c44010004940084905402c5d12000c0180d4000c2140750000e24000c800c1d49400340c09203002d5507069015034a00a4104150b0740c40c40030641c0c1041040c0ca0700101d41e00c801280300050400310101410514407510358201506c12504000d07900e8403070501c100340c0349032240c41c00c80702d08200b03613648000605003801d43c502e07031000900c014004610580e0310030724201e0898005030a11010741002d81e810f00011041040341c48e010049a10180c1e25071502c2254081001d03104e0391484403c0f83d2000f400506034071400841406036200140c1c2500d0112100c80c0c10290f030b80e9144450104c1840c074040c1500320b8102c14012010341d81656000485030300da8189402007403041c0034041d007001720840341e40d60f019440316016031a644240f45c028088a24080d07a45c0c9040c04a22007074030300035484554088a100344030004541544162030954126902c1042c042044040303c1016080349a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 255438183 1250 255436933 255436949
    0x209041104121502040308040e09010e010e0304030b0a0e060112080c0613020112060605030c0903011104030b06100e060a031d0d030c0909110a1103070b040b0a0b0609010207051504 79
    0x3004641e00251080c20415548900d5401c440100d00000c0b074404d0f40100d200c024294442032109028041d4038084155024000900018046800003c070600b50307400240e24592580000400b88180004520000c0c0d01c427011520500c5859501c64505a07240c80502c11040c49882c00700158040102d2141110064001c0750103c0317045003048912050520000601280410b140c2416101c010116001e0501150704586502c3e045960300641d1000c0f0790311490046a2655880842d8000540388001a01c0550300407140c6c01c1403807034420b0600503c404510f0984040c00b903c1c0c0d11a0000355200c0080301e952820354030300441d40f80c840d040c0b10048020341e0f02c0b02d4021800b41c01006864170ba45a8171444032001c0940d10041500e6079110f0340c0c400c64078601c0c07000c424038808004410105024600c821039200f0072800301c0b03280034000d4403005010348042e03030f00300c2d08520f401042c81440305460240c146019400c607001443e06044d1400030307542d80c120f0b03c40c0c00d0040360401d105507035031608102076500415800c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 255439433 1250 255438183 255438187
    0xf1a192102040e070806031e03070819031503050601090209150c15060109120b0c13170c040209010c0f080408010903170c040303300603031d0609100302090411 70
    0x420500301941050241c01654030848000408042c400c2c10300501a16000d00034003000c403840750070300e402100c0d000342e03480b241e110030805040051503000080010340302c0c1c202c5290300161a1031004094a051411160300840700f004140081103010414504440b8619001031341d8410300004102035641701a0792961107040030a01c2018200b021031100580c1c076116005260030b60701c4000544001e410350142092001d82c200070000000d00203010250444e2140c1a11800c203812154010704440b0590007409140001095024180c00704019800e030b85202290254100400030000906800946a0140110201402620034011200100c80180520304000e000b03c48080c1005006c618442640c0c124107880500003400f10305d51340040c0d41c1940d0341540c2e00503800b280712004201c1d480b85400c0c0000d00440c0000030340304101c001c2c0b042400030751003a2148660540207000c59058820050301450040c4000c002003002c4d0f41c1c03400b514103100c1c02181001a00c2d090000041030003800c01081c202482600 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 255440683 1250 255439433 255439487
    0x1080609060703020904540305090310090c06080a0203010b030411010c020303030c07140106060215070e06040e091c05040603020c010609020c0303091902060a0f050702030114010f1a19 81
    0x42442d41c2c101f030218649a4910318203117000105014106400c0c0141c1060107100c0000002c2c0f003140201518000241162808541c1140b000308a0300420300c21520004c1e010000c000707040c0c0241c481e60748002244821400c1d5031610030341c1c8010748401003006107203a00d0b00d0580300c61a8020100aa52950080c084130b0322482d11202180300c1e58811075040d100015001c082d0244083e0500590080c0c481c0380d03010b0001104207040c01d001c10f4001510340c0f81803000b40703d4441001d0325034001030700017044c0103158500c860034507004044c2032400345003107031710040c040d82c940d402c505070404211011a4081e140c01a654221000c020b401840d0303e1f0170070411035000207000b08102c14000003a6019851600030b960340861a0210681d1840b8000002074110809100c506d040364010b40421500402504003d0b00c1c00c003040c1c2c002030855440d5500d4482203c4414010b0004c8400e01d04075801414151150703440c0c1d4005108400c240d4086ea5038180c1031425520004d00300c45100341d10400020220105440c01c40709 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 255441933 1250 255440683 255440741
    0x20a2715050301060b0702031b03100f0c080604050403080403050c0c03070b04080705100905040b0d021309060b0102070e040605060301020714062d070f020115060806030601080609060703020904 85
    0x9128458584651308001012a140360302078212000c19a000340108020040c0d0b6041ca81500541001258103000710b040702c100c4a02140185071400c0b50800000908a801c0da801511500001d481103004510700420400002d41006001d508950075050039a00d0b409082c414030b16106c1a0341e80c49415002d054000140042c54002500a6800813800d807500799403100c0902c000311a02001003400280c180d1010419418640c0c015004141e026101c0f0000c3c02c40c50300880c000c0c40c410000b190405540340c03501f0045c040f007841010054402417024000092030703d07145a42900020304040c03d421740e500d001c80c0701c1c1da03000d50483d68901d42c0604014050182c0e40f80c8030740c642800700e80f188803d03001814020440440301210070784445a00f00704150035203820303070f0488803200d0300d407454030035590b9aa03050503a2050f01c2001000405c100e650340c900c41e1411505040c00e000041c1d1001300300794403000c148034219801084566202c0040d180050b1100031060001d005022080400001c4540c040f4508203054 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 255443183 1250 255441933 255441971
    0x6041a0301090c0f020709090203030d320601020c0405060307030515040c05090c070b06010e060d0903030e030f19090f030c090e0a0503090f12010c03020a0f080103020a27 75
    0x103400c2000822000c500e0340001c1c3c0d130900e003824000005811003241402807e85031340c04031080c0c07400a0100e0741000141181c0c0c80440c0d2403882c0040745050407000b203100c400c15046c00a1524091088003802c1c40c2400f100107940c50700440344030392107540c64600042d5140c03400c02c40e420095400c4000c5859240f1f009680c2407140c40196801c3d103a901d905800802c55040c03c0040da0b010315106020b06250440035140c1c1d082c035400260140e410040c1d50a2481015901c0102034002d106894100040320652031070083d04540307092201e10101d8000f48603c0549408103000c0d079240b482c101c01040218044550300304c500010740d4121402090986001005000303c42e9086000e540d4006d03000c02400ca40c1c1c4128940d182e40541e0014403580c810418844a1b0070f15402109030715402624800d005071000c0c440c40d0a58102c2d07110003000030340c041000c927000c55226903000c00310301081c04c0122140d41540c01180a0095034020084410310f01c0d070320b038441030661103001d08030104941402c02c81c0c0d0001260190540c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 255444433 1250 255443183 255443189
    0x6060e0708091b010c0302010209040c022503021302030c0f1206100e0d030f09050a08030d050c0c0a02041a0402070b04111002030d150b03041203180b0601030b06041a0301 75
    0x10740390800125858400500d840c03090060000602c048031110004492070003103010b0450465409100d100c0f01501d4501580c1004c85494010b01244a07144050030781220451503554400d2002070400c00150f19803408c22043e0480040001d0f13034a0380ca8020540c4a44280304c403010501c3d20000303040d00b04405034140f040c01100100c1c0c082007031110240d400c95801020124981d13004045144440000f401001c40c00c81403007950400140701903859000445140c3c0da82d110520680000500f00070550740e52084030313884940d40120354140300c64040710642e1070030f410340028084d956030302124450088000c01010b0061005106659506503440c080d1100c0f03a082d00e044444ca0700c411180011031618003018980c12005078000e60a22101a03a00405042c040d500102d0100d82840041400c10050b0020361181d030003407162050584842500900321803d00b0080600741003408a0580050740041c4155004582480d0200b0300c000c440d400104148525801200c4090b10318540d071311440301c070402031412 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 255445683 1250 255444433 255444437
    0xf0e06040c030209061207090b0f0705160f0306051905091b030303070f030902150403080307090b190522260f07030b090a120903050f01061a0d020706060e07 69
    0x1209100c000ba000c0e0300507110401e0340300c141841003a00e40000c80180039882200380c80e001d50641d6607418034108640c402c40961510300c0e4006071030b1003407040170010b4403850b1000d10018011a031a0410710030001c001e50000030320240d05d410201e000c82d10313240504d010740070039068100b14070b04000c154141d890402c001005414010403880c1201417a012061740d200d00c4841d252180d8211b900c0b01d0480c020864000201e03402480f2880a80b0f1440400d0060b1020350b00c2403208594030304041e03101500d020103961143e82d48060400c40c1c00c828882510058000310018103000d0344414181707060242c00440071018410350300900c0400513130015a504d82e40c4050510b65070382c030032a08594240d2a00c034108036107007131800d9000c0c4c4000c1000038010b160090f8050910340598008403d0396942c6c4072080c03500f072101400214081c20034014010103115848000c240c1c00000c020032464050000c403c04000c50321401e8148012030489114503003034044030000c070360141c0c00304090b9898804246008606440200c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 255446933 1250 255445683 255445691
    0xd080c030c1e072303120406030e010b010e24030c040e0f01050604090b01110f16051c030c02060c060703060302093301090302090c0a03060e071b06091b053102070302070f0e0604 78
    0xc001c1e01841140e6840cd41a03441c8004040000207202c040e80300c1c415564140700b00500c0000c2c40c5855031010754050f02d1901c1d0034a541c2d5241c0010303205a482d0140030342c1c038400340d1080100580c0e601c10b021a01100e00f40d640104480c2d02a10040c2c491015507040c002d418000d80120b00600307507022449002035001c20509150564598051000348109030247d4050911449030f80c01c007180c010095246114030003442289419080c140b0756050240655215020036101e03a42881145400c01c0280e0348141215428210781100340c5081d41070300c1078281c1c03803c202e581c8900c1c44046ca1344191a003a010703540141240c401410304000701102a072140c1c40345000039182c04004156000c40d031584a0107640d0380c3d80c0c0d900400500040c1c0c1a11044040c0048460030f030b440c0c25400004942030076190707050400200c020b407143e160078240502c1501038061b19204e503002e8406120b80001528002502454403140161980e01500d01070386440041e4219020581c2500380c0086c24540d6041c440e480380900340c030140 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 255448183 1250 255446933 255446951
    0x31a0906091b0f030a080c010c02061303020a0b0c040503070305060a0b0f0603070305071209050607020d020102090a030b10080102160302120a0503040209060d080c030c1e07230312040603 82
    0x26840302c1e000018184030090300c40d5810741500d01280003840d1400d0050554903c0011070751240001d074408080d02e11982d44840b450500e0701d40502c0003a503c545522000262641242e400a4a03030540030310040120542502040414110000703903805842e0180c110342c482a04c07400c150f41d99010031580c46a00c0d90522240c8046420199100c411894014101c03601f10b84401000340d000e4403000300303590200300307905d40140c590b60100e0040c0158a4011005413103a401d02d414000e0400207034104c0c0000b5680100a00c1d0516252482090112604181d8240858031219000482c1401660203170109600105800318400c5903081d00400b914400d400302c4031407001c0d422030403199000780e07148170001c503206000007005800c0c1480d030706900040040c00c2c0750703072040903554802040d00b01c1100000941e20124880040d00c400f00305144042148042d40d003401501800c03480d40d6002d96025010201581980401003c08003440c0040c00c41c034000c3c00d60b4208161043c843c0c0c6c0541142c403c410009082034501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 255449433 1250 255448183 255448201
    0x2030705060a050307050c0c2e0315050103090501180c1d070e12031603030c1205010e0601030e0709060b030402010f1b0821010b120709080303130c031a0906 69
    0x1141c80d035002c1c0d16018250f40d203581e415038a41d0003050700d115060191451548d19903840b0b01c40c0307840c14050f040800280c1071400b4805d21413800301e0030320035061601e0000320580d4091100d044070100c443c2460040741003107a038034009000d484922050b510b4035000c01c10210412185004071025a403c05010410a0300310a0b10703000b00d000300381c0d1a070010a140380c5d561001c60804140303500304100d11808580c035003148100c0e142c8120f02c0c9040e040d80002e030742e16001450310343d04c10320310700c0c074004007010030f0000e541450f02c140c041e5400074291a060541d2982d481080e000c1c2400000d0084c01402010004542d640402900e15402220120b00040101c071181d64143d01070494142050008680c01c1030500c501da50f42c40b95540043c121084400010581901d0440120401da02804000c1151500c0310030107040300c41c150001400080c24400030a40500c03401c1400800c0e6503100900001c0044000018200032001881c20382000e400b9200c2c201c03540c064000564149801000340200311440ca5a8032011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 255450683 1250 255449433 255449437
    0x1030501141e0705040803070309091d03090607170d0b010e040207050d21020c100c030e0303040609020d0b13020a0603150501050c0f0d1d010311040b070302011b0c0203070506 77
    0xe55121846075600d03141c031440d0ba0214a0358803a540382000ca20b000d0b15840070034503640007544101c0c00150b2080040c050f003e060700400d4036540c0800540c00a0400d074141041d2179000c0c0b00d89140c0510f40102d0880140210681c19031444a0f2480c2034070f07581c8410b240c002d40a01140744455001c554200c03896002800c0c18801c4902c510b4104d00a01044140c1c81000c41d00510300c8260403401686502406420741a6403000700140f10040c00103060054546003004240e4001420ba00181441c000221070380c0180403084a0303015a10000004000c2007500c006441c0010b140c1002d0711650a940400c90b07801c4442c90b0003a015402198a04a050b076507200440589078401e1407000d0000d24a4010400c41d40100701034480310a22006232621ba80030203500307500d40502ca5101e0000102c007007005602c030b00200f001c02524100c3c20302c9c041c0010450410710306202e00ca035101c3c0f20074408001801c2d50a0510030740c04882c4a416034040d1030500003072544000d02c200b401d03032000c0c1d10070300400400003040d02e841b40c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 255451933 1250 255450683 255450691
    0x314061618030f02040b090108071403070e06011b06050114010e0915010c030e04150f09020a08011a070f0312060602010605090610090312020d030501080303040203120f130e0103050114 81
    0x10001101c0341142c1d1038a00c40443c02e80200d802540303c52142456507510b00780603000c0c1180380014641c00389030040d40002c040000b40f40f94008d0700240d90a2114182020316203510603000e003030880c5a803480030488940c100710414040d104c1844d26001240c4451010151303544200c0c00d9841c030515014040410060600c15a9101446455205001c10a50098035484c050500074102481c849503c00082029100c6100d006040b40c210800300380080750000d00a04003400719000f00714200020310304003030310b840010700518407140c06d00607507480f14003501803c60360000d41c011800100c103400d516000d0803000141e0301044660341003640c040b03000da20500c207003c1200c0c001007520003141c81d42c40a00c01443e00c05006002004100607002c0b010501c250501e40e10f244860f03004004003007417041c00808807076040e045030307170140c00400c00e01015a400151080320303142010700907940c80c1e001029803070303a40c810802980301181c51400c0c0003e10340d2518520398100c82c001d42c020310a080382c07818903070140e038800c0f0303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 255453183 1250 255451933 255451967
    0x30406020d2304060507050c030d0b040507112d030a18090209061e1e03070305070804050a02130f110d05010905041713120521041d09030403140616 65
    0x110010f80400d01035048a0b40040035403d08515003011801d04a080d40c1c0b211350032088203500c80c19113042600b003038840c0c6070f40642d440c0b8191039a1390409034615141d0b0a494100700c45242860388403200c4e0f030780040d00341c900e5400100881c2e580e40d01e20080030304a00c0c450142c203041c042e610b010008965583d4000c072429900000c0c4001d2400c96607240520304860343c2d1850002c1d6890601111492840e81c4500e0080800c1c0c1490b160344030b242414005007960001400b08003004100c10600000401c00503099940503412520150b045a540700007000402501c1d40300c1d0041b5040c04448003e6003103d01c010329095400340b41c140003aa0700c0d03581120560f1401e035002000325481860ba07a500d110400003400b00a80b01c81e1070b140ca2560340d503070103c01d5035016030350940703003500f054010500030000d180c0c0e0301c080071054007042810640b40010001c001311014150444040c9200c0014542500c203004480145502a501c689501ba810250701c1e074466041740d1000101d980520126651030083d111407607004511 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 255454433 1250 255453183 255453251
    0x9071110060f050d11040623031b090a0b040501120c08030306030303070c050c0a1d100819030306030c090905101109040b01030906110a02210406030b030a0503030406020d 75
    0x110600c10704c000002c1042c3d884455141c06007503156500d004260040c40001440b020f1049482107080003000c03203008072482503105541d80181224a002d2101500000707d904860b5592403124907070217080e0201402d54810300c0d100c0003151480c0e01c0322100c0b000500929010107860380b0b41c4003513642c92009403051381d4158400e100007541e0318401c0780710342d4031188524150b42d540704104020441c85c00c22a0000f4110030743c01c5605084614541001ca6804003500c5005159180340c49006505c4900031013280510f502e6096002081c14040c0c0c0003100115030200800705000c0c0d071201c80c0f030000c0c07490b114202c540d0700402c0f15440e6216103900803508181d5603501d42c903181020b0b04040100030035001d00c0e034505254640c2d6005021030014030481d01e0b03043d58140707001d5540c084040020306000d8250b0381c00b0000070034000c855061910160a50302a2156420002401c10002d030002e4500031460030020103d1000008020030480950043c20030034014800a01c9541c400890f411f038030600d1156501403031500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 255455683 1250 255454433 255454439
    0x31801081b030907180603171303020105130315020903010501051801091d0118020f1c020d0302010912020f060c0301030b0a0c0909020f130f0b0315030c09071110060f 73
    0x21078401150081035907812500055540c134620f000d09440c1c0c25506140d00c1e5101d508005001c2c1c100609941d9108d0804900e14148000707182d00d2030900e1602010b81004800709000da20701c140c07031030200059500101010290650708004102030740c400031223079009500f01000001d981c01c244090214062080b01c03000d000340e08101c0000000c010b00100e5a00d04246006494800e4000717100c0e8195020f010201ea1203140590700501005100101c01a4042d02c518400c000a003080c83d502081a1a03044420480001190034105d024007036406001d001100300d807081c3c400c0d05070000703449000ca800301819621180e0320140050b420b0300007440003818000101000504092203940201c044416504000100f1615210b289040744c008060101445500103103001c249504126000010700300e202a6001150422180080a00005c1c000c1a991844000303034610302d54051115078207803400600421014548904000c000152007a1401044e010707883c09528400380300d003c1c1d201aa0002c42240c503201d4a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 255456933 1250 255455683 255455731
    0x50c03010e06061c05150c04030b19050117030412062301030b1e06040203040303110307030e0606030706091502070e0a0534110f0307050d080c09130207020d02040e03180108 76
    0x186c01401c0ca09062810800440024108001140600351000c03001401c4c90304d90030350608585040c0c0100c240c916500680c1200140001300301d03425034280320b62907254003140b0700c4c4c0200940542128086268040070340800d204002c1004c00d4120f130300500a20100e51108801900200300c4620404000c0440100180c202e040035001550090311a2800003516101444003004507041a07d261700080e4441d0b26200d0054801c0001e04d40160742140a0b11000b8070f81103014001b282c15110300101c0c0c1100320203240c071440c000c0c01b04000400c1c00c4074040d0303403900e062544034000707184c11901e0002d00c0600250140c1c02032806400c900c00d50108084105c40070000103010340f078000c01800040028412611054001141800504031040c82070000788070680c00d02c44041e201020043c4000c1d90230351309200d56003580c0e4501f0b12404050048032030050f6110894000704480008601e00a50880d0521004060b0002d00000410310f02c01003001e80c20240071400c00440d84034205483c412084c0000543c0448180 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 255458183 1250 255456933 255456973
    0x506010509180a03031d06060609150f040807090e0102131a041d04060c02030f0d020a090b130515040b0711030a0b01080109050607051213050c03010e06061c05 70
    0x400c204028403940d101d503440c0b0b9107003200014040300001c1c0c039502d0482e40000c202c1842c1101500d150061300c0c4a02e4010f0100f040360113406066842208408444801821850102e80c20a0042d10400b81e42e29140e02c00150348020780c1c441c94844925001140d6815070040c401e03143d29455540340d19081c01d11340407141100000d1443c1c0c8803c0c0c51000c00c030001f003800115801035208102c0c0b030503d840515083c10308d10100c0b51500c8810701590801c100b150104904c0d0310884c1c01208a20b0740040e1205003007101100d109280b9000180c80401c0000d959049000031a540300c00c50390b04890301d81c015007079005200c3c194000c40c4240309110b0410300080f40061003142d054052031601404540300365000361210300a20030284d00216899540f00204c40c2804400c2c00416405511801c00702d240503010321320744074001d500038004081c0f03518106a003820040140b21090f08024000d0081c400c3d0f0041108040d110181980c4903841211076840a010040b020000c52402980100241490308942d910100d421 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 255459433 1250 255458183 255458191
    0x3250e041d0a06140601050703020a14070e010602030c0c010f02070902031929010f0e122505010210060308070803040c0e010902041d1b0901090803220603090506010509 74
    0x2141594481950340c1d88100440d0070080d002d00d00104d1501610068403610a501038030f05030410204101e03510200781c0002e2003c8416901c540002a098100028503003090200d400c07855441c00782e2400085d140e0380c0040582258200c400c01e89003503200100c010340760b81540c0c4000e0710244e0071000c0208001e00655000d0b48e4040c0340500c0c140301d405052482d0034111030701001e00700c500e074900048501081c2030103010100c40341c0003800c121503c3c1008940141c0902c3c81e03290003d1007030f81120b070042d10703e54041c4109803c1601c0007240102c82c4a4020343c5003c80c91050103100d005102c1d000c0050b00e1a540e0340102403c80c0d421100c61450300c8041c2c0c0310003102ea80001c0c800c1c4e886c89203d00700003c140421040050080c2200c0d08010b0702c448c10f02c0c070b59050a4050414108600e01101c042c800d0209980c5844042022082e44a566400c808401070b02d41e000258000311290002050700c156052480c02c0119203003a68681d8480240d840b100141c0c01c5070700792000901541d04c100d006202904044100c1703500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 255460683 1250 255459433 255459461
    0x50a0b010c1112070801020c0d0206070201050c033103092904060e1903060b10080603100e0118060501060e15160213180b0105060711060a0e030a050303250e04 70
    0x1c079859115840c07d903801300f00d1618071a401223084241c4264140301103034003c941d40c4024007490610345124400703404040e11012081010090212900c25000c0d080d41058a0500b103446080754541005010018103120380d880f0018504502c800045c4031b090180f2902c034000749183d0402e82001c004030f810407460030419800030300e03181c4000b6000620307003c00e40056102d03850102d46420804148070000c86852902d4003449010420722105039030104004008052310000003605620010030785015160558001e04148245091003050004641100f81660f415490f4964020301c0d000a00800c442e08103440b100701d44060080b00000d46040035408090303400140400c0044c55808034002c01c49104808410701c5501d0321b02ca200400c145200c0040c010003085480a082c5889607c6074011201c540070344034440d03040045c0606106000303e528008002c03026080311107a072030a00d04196a6402a20510207003610b401100042c54102e0680702d0030b0003184d9a816041034011024000070300007403104014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 255461933 1250 255460683 255460693
    0x406091a010305010c02010f020f0a1107090e03071205090d0615030209280204061b080c01060f0305060c0403030e101205101412060403110705090a050a0b010c1112 72
    0x4400ca40480c921400381d0f014400009101038540c002a00312200c1502c8901001d0060115407103600703444094842c10807650900c132024500a40e81141410a40c0d0884080680752103011807684a0000184c0034040c841c030141b22018100703040641d820701500051f40e500041d002804000521140c000d41406003800c0d148041494032503001698001303084415901c002c0d00c4241c0461268180c00131003001340f4100c46c1c03c6107001d080c444001c080c408501a00151441036000700c0c0c04002202c41115071003890b40300200300c03280d1581038112640c166403205a03041d00c40d02011070100c41c2c5c0c1200f10307812a581500e88224198461041c0020201e21010a40500c1101d103194001d09542c3d00a161165001070303001000e41e030802900004420407000414003691009004d18010000040c10719040703a05401d1400c4d07082210140e0318540031241d040150440c0c1081d09002a098054000c0d0b40a160072600900003000400c00456594102120142c980504250340081a060008000480d0030192050754 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 255463183 1250 255461933 255461963
    0x904080706090b0c0d14010506190203130e0601080705040f030b0402030307060c030506120f100902030316050303072c01050d02040906030f03022803050a03090b2e050108040609 78
    0x10515401180c441c0d11000b000544000d140d00039105405170301b00c4129001c1210750411000c00c1c1030740190000b9080f0480300d0100310303052900070002d03220492040d10740c000c5143e45854201405043c20b4844501003a0500e001c00d06043c043c800341c0302683c0444c0030048101d80f9503203440a00341c0001d00188d8241c0410020040840c01500a000c0f444000341c034040b6490600c903090009640e14404505151380142e1aa00787c0941c0104100d00400489080400c84001600010b4118890803000304101c0500c0704414042001c00300145100324110b480e1045507a02d030034012098150740c4c0304d061600e40901ca41c0350503150300500207040d1100b8030140040c00c1a40790010f0031700301d0780e2542069403041c4450600c00b080541c100300440c03a0004034046004203a02c8920241642c0c0380307550300203080c05004a501c2600070321a500510740c15420100080c201c0c20f02d040303816281c0d080010b515024404111025401001d03034200ba00880c2c8040e5a000c5240c2c0c0c4075140c040050116000884460010108071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 255464433 1250 255463183 255463193
    0xa050901051224010f09050f010e09040302010e100b030a150b1306030209060415030f02030a2f0102030903070324090b190507140c0f0d2705090408070609 68
    0x6102c3c80320b0503e0860303040a10000001d1288541066604020108011000720799200141e40c045401c10749441c50303034210394001600c1c2e05442c4030145400c001c0d000d0070013040c180e054200c1e410244802080e41d281034641d900100540c0c89034422690107520440c03090b40002e228070402c0d402003800150010f09200030f0400500b03118804069200d80c26200c0c00f00380103500e0406c071200e4000000b21010410011045110010400c0610004d061501d64104100079501e00f4004801c1040c0d001628002038071500c0c1d48900c40203000d0440c100c070882214810303102035000204079203404500500030001e140c511307968003a1009803014003e06546101ea0b800020390303d113000d030110b01c134465201201c0c20314100300101c4202d0900c2024049680c10f0505004820b500301d000c48014850004002e0383e0390440190b5170f4940701b6a0104c07521a8882d910750503d1441c4e00085280301c0034004403001e80c03464405429011404800d02520fa406940380b8041400078140c00000d1941e544514404207501c481da4440d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 255465683 1250 255464433 255464467
    0x603270d020f1204030b0103021003020c010207140609010e0303060d0c0305030414011d0904020f040905070602250e07030c090e100e0604140a0b040b0a150e09010b0a05090105 77
    0x5030240e0700c00100e04031261001e012401e058101402d0850405145496041c0700d55010b200c068052210001341e168603a20135011034a900c180c00c4000c0d9942c007110303d0700c00c001e0003c8880110980c00f5610104403482010b00032000c0d02c1104d40019421074231100100004421001c000710342a003c90000040001c8082c00900010221035000081400800001401541d0401501c040034031070040f44491584e07404100a030016016188001003400150104009010484024115208064000400c503500181b000011003101d680300c09142200c890000441609008141b02d01e900c010019102074400d40c0140c807003819a2030700107062607035281100d22054056800d0b00781c1e19410304041c2f02c60720b0440c0f8040e40042c41a00d041101d00401000c181c905540a07205801d0f254441c102c1548580e20342e0003d0340c85190081407400700d2a83e500301c0712001c421040107880070a500440f00c000a180c000540741c1210300c018110340c9400d00d6014100c450340d20074030229060180c02d0043d0b040741500411 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 255466933 1250 255465683 255465703
    0x121106060d02040c05041a0904061205100203131a0103050f0102070b160c14061e010b0d0b030705030f300f0708120a090c08121c02071e1b05060327 65
    0x400150f841100d0000c0c84161802e54101e1489038890bc403041000450000d80e42903c0142118010f0304c0b071f103c4007288619290302e00c901918407400001012004a01000301c00d04991043e4221944116100440c1d0700381e018981c400b6004103c8080056440c4100003540079443c1d880d4a01030300641c40da0b42e41e02c4201c203e2441c0400d420703402501040f4488011940b8842d42c0c0d44082c884001c15894000072030b4140c443c079014491080d4660420404d0b0b5102040780030042c1031b000342a02c1031000c0c0c2042481d501c00d20340d401c40c04000809401e401d0542c01814038a1401c01c030b0200010b2402010044103038030303075001c02011100c00c50200442d070090440b24140750700a0505c2e0390040394a400c5400d0410030002544c000c40b1030f60700050400d1000064184c00ca0307104400c1620030021240c02108190001c1c09031207001f80003e070a00700f2104201050b072a000c0c00e4244034154460b401822000318010441d0680140744c2c102004201280300c9003580c90786109800441d4003441c0c4440c8510b512241000d442c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 255468183 1250 255466933 255466979
    0xb12060f062208030f091207080613060b041103070f090302030d0c03030e1204050d0201140d02090a060912081b0a030206090106210b061c121106060d02040c0504 71
    0x107030709400c1c1201c200804002d0a10f500114108892044031034418466400c4482c42603030260484d1400030802e020442c0100b5511081d580359160000751580c0414090034121400e928110380450a8507191140080c1c04595220031400c59468613800d58283e00c1c031140360818041c030f000c00000165010090300750380300c509550f46100055a49400307402d07143c0303403540d03600581c101c289800140c00d403c4054504945044590441c48036070b60005841030140440511194a40040c00251a05051b0018450740c00180c0c1c0813a19180d07200801c40d50002c00b801249868110300842c900450b840101504c107102620066402085006c0005490022854001c5000d60001010000c1c005020b110703c034002c00c04100c000860010b20081c65170f00844298006190320346c0040451080d845905507032404410301c1c0302c8040c803984141031040f410700c1086141c50014200f00a4188880c5011a24501800e00903090304500586a03007040060403481710508104101031100103900300d1901c8164101c40f03801 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 255469433 1250 255468183 255468217
    0x40302010902130c0c0206160606170c010c05061b210a0f0603020114030703060b03010902180a0b0702090c19030504021011120c03040306060311010f08010b12060f06 73
    0x30b1050000c44003d20000610692030525040c2e80f15410180a0078116811500a80d4a19800c0e550700c010602422018105524103980801d072884a5074107002c05a10342001c442d005102d0000455006841400c000c0c2150852004240300c08240c0e01845000302c0d000340d2030790801140490494070402c80800e14a00c1d2100d420134070588030414464540b80b80901d40c421301060381150006403012004071500c0c080c4c210008002803905200340d0000d00a0b0a15920169072560740d03030320242c0650000082c11f80704042990f1310a00da40703809900102294004000d260a00c0c00c140c003040742001e00140360304581c00003040f035840e109080d4288240f4581d56a200000c0c1420140180a9002034550080c0e09100c500d020030364154200140d1007917504a500000e650f00e400c00000182176004039400201a14101003000c01081807286e60b080c9011000e9990355200c00c0401001c6074520070070b1040c3c500c0300d101004400705103501e0000c9207a1258015089200344003010300840c0c002d40c845220700f02c504142c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 255470683 1250 255469433 255469451
    0x1506091a1c050a0b090406150b0a140c160609060305150108010303031a030d0c060e0102090d0f110d061e05101203090f09060501020607020c06120415050103050d030c0203160201080c040e04030201 86
    0xc415400e40681040c0c584140ad10a40150291080c1a409941c2800000200d040811a0300801240c0c0b401103040040c00e01e07407076880704080c1840582e40105404a41480f00040818400580000030200c059403a240e89902c0c0d500d060700140440c8040c1c1141c12045030320704406803001c00540d100490f917907131158407408450804200325007540b41154040e9004100c40341c030035585d400002881c07540050511240603038503c0c2c4424079092580c0706a40120281007600300b844035540c041c04507403a900d0300d086100c01020000c0b40031107004035007030f40c05004614801d006c2c0341e4045080c0003500b0320030308007900840d4aa154108102c00907a105900d60b54403442c0c03c1c065560305215054115400c5d000a2040d0f1900c5000581507000d909485102031001c0000641400700700f59410500103c111420004c0d541c480c10f10395211000c0b410329201003820701c1855800c9500c000115101c1c02000400000120410780c011248604007801c500a841e105000100d4a11100c2407068081c1e8032030340001401d00d40c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 255471933 1250 255470683 255470711
    0x907050d060f170c13020322051c0806010206010303050c011d011d070609030f0204090b09060103031b0b0f0c0f0c0703061505030307151506091a1c050a0b090406 71
    0x104000c800b103440c1c010f80021602c90311101c401c1702031602c9207407001d626540c8001c0b4004811002109460104500300841c2041c06404120740c0c2101c03041d40904180f8a807a0a03040e42c03d04030030344500c0d005a10500040010074403440140c000c010899001040c0c61101000d450100d691819001c0c000b039664940c126a80500b1200f2060014681400707024a0ba1500e000600b41c1a11880060000c4400c049940c046503929070140b1103066100169581702d0408403a0320b0f5a0308806d000403004609200149c0041000b00d05081082c503500a840070740c1c4d0741c1c9400c101c00b144040030348080402e00c400d00441340b1442036a4050680c20040720020003400b4a54207100090701c10000c40b895041700c15810034021600d0210803502035613085405214200c2d4100d040350001c2a81c0e80f483ca9107507202d01000b2480170360100d44142101c1902d2160015218128803c81041c4111403d008010010200300038281c403403a04260303401400a02d00045080300351021542500089808503440c40d034480c40007a00003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 255473183 1250 255471933 255471959
    0xa0f061e110615040f02030a05040c05030105130305071103151605030606070609021809010b030f15130c030218060103051b220b0d0603140a0c050907050d060f 70
    0x1030480c0c54044401c1605460194071040c0103003480e0020ba140e4005905107850b00e40010f03031504407a4204569900d45190000006d05081d07508030395107120800002600e1805004160086070039203803903011080e031030358246c9040d889070400703c07490041040413404c6650103020f210000401d85001301007a28040c0c0e0302c2c1c40c1551200710740ca801c0c03000500c14090315464404c1944d0803207030b200000288960150002625141030807040c001c0550851080040120040d0458030841c0c00c01c0c0c0494041482c403d07000c54a03601d040100003400070a2800003205051004898141240540507100c1e40d01c7c1c6070340110b03001c9401d0850412400b0403050500c01256454070650307038001a035090284250303000396080d810502c141001c41c3c02e40b55480740642d5040c002c924042000744406540550340ea03620700d03442c80281c0598402a0394140c0031002800710554081904803404c0e0388019524022814101000000786014001e801080000e002040c5556414811900a80482a03030144410301c2d090303081d1284 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 255474433 1250 255473183 255473237
    0x150a090311010c05030c0d0209151c0203151908030c03090a06020c03070905090f010f060501030b061c09110d1a0108010218040209030f06040b040b060405060f0405060a0f06 76
    0xb07030314080f241180640d0103810b8907000741c401003040790780c2c49001100380080d001e040f1207150f100c0d00c000c0b000140c0152500007440400c2d220f28802005545c0d4502000c100d0100302e461012909101f0b021100b2817821100422982c140441c041200d140c40c1c544161070340d000b0030ba40c90711079803000903150110324008125000820b040c1c4001e0640c40000e00c04240c8544141c820122800d4854010595006041c410002402c1c680002004140c80b100b10b0306018000754802d90707020910301a49545281805000c4420740d40c0c001321400003101e8480e03481c900410050f241591091a01c0d111401c142c3c3c2c8000454801c54050303c01606410310480c002021054180c0c41030301b50307a00c100f0003120310a80b400406a21000d0032500103880c0d620040c0840c1c141a0614010301e600e010b01001c01003040035060301a03003da40a2501103c496841c142800222081516007503171292110003005e4603494a40c010341c4c0e06c031401605031081641c0d50b041d60118070b0190b03040500451646550105007507603202641e440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 255475683 1250 255474433 255474467
    0x13090c090609060b0c1f06080a0308190e1c03060308031f17070623040b040801050903070f0605040c08121b0303060f010c060204030b010b07050d090501021b03150a0903 74
    0x60001c424a5581c0e0390707541602c6d91040030181c4035041c0444045584200000c2121409035080301c081450020200e203011180e2005a84407141032904108076449055241c0030404000c0403401703840b4814014074482944950101a01c8090110000314101d0145014142c022040301044c1c21210f0710740640a003a03041049601c04d001c075500141d820006d88642150a142000d0003500700a002c41500b40c80d003200865481d440000740000c0c0042a100200b086901c40c81c001c200302c2d1540c11138207840c3d2040942c0600315219102007000411965481290001c0c80fa403215841c2c150341d0b4080d11f04280481000110a18000c50188401c030110b0b001800c200121002030341c0747d80f42c40380c0042d807082440da003442e041040d00088002000781c581d046801440e08841d40708495a03584450150560101000b1250340c000c0c2241803e140d40128100c40c26102c05030050028a25421664400c03116607a810030751510921614419605882c070003580182101640400c0c28919810090841c0300c0528150b80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 255476933 1250 255475683 255475687
    0x12030e060403120207060b09040c030212071503020306010201020705010c0302091c02030d0302030606070f05012a08180313031104050c160803130218061011070513090c090609060b 79
    0xf540059980303031200c00044016100c00745030900030028112807000c3c503000402501070006004042082200b124821117820803034005034002d4030b465115604c5100c078044103100000348844d006c1d4010f554404410302c0010304100e25910b0303017429951b00145240204c0d500040c1054103041001b09503425106206903c0e1240000740d001c06d5440d100b8010390810164048003181082c0c2e030b4041180d254036041401d1a0f864800c5041c12802040f4001c03402e0222054020754144003034486c1c0000040d8866921484000d41c0e8180c2040842528002c5424090004102c00d03094041c1c8104142d01542c081d071030100c081050368041c4030884001802621380c800080c00102218100c04100c00300c0f80381e02102d0941c0769141c81250006850f0400700c0254043c0b0301c1c2e5404074414080ca905a44a44805c4402407907800c07110f181a034105040702c05445064000d20300600550034220090f1040001040000a40e010541c03541c0003100d80f96001042220b032941010421811030b030040e50050088a400b41d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 255478183 1250 255476933 255476941
    0xc010e030a060203040c17101d0604061a0303120105030618030d1104090504050604021f0f05030415060b03011e0f0603051f0605070201080108070e040b04150912030e06 74
    0x80e603070310181c01d00030075041e00040040c040102c4c104100c0000c00c00410000c2c0c0707c8600c4004962690b50990f5a13002c0d15281040c60008403050b504220100c000308000b501e542d071a0b9850b240c0c050000003110001e94529044c0d24072241d2030030801026107070007220050034554140740800d8140103000d072a480303550310082444121140c000c8200c441481e17036080005055025040d0086090140e80d224140c018500ba04000501601150051145100b103c5120844544400d401c00da08240c21051000a481d1640c6400450140d802150018000c0d01403455024072810070340141c3e51a500000c254170b2010004002a4130400c40400d0101c804807050212203041102d20380002c44c041c0b050008068894021400c00d4049a4554801c1001c0411015156449080107040e507840070104030700140050000240141001c20584160342203400541101e80310742d01d03954480b8401400c2a544040300131641c60410030070780700b580c42d41da200300c02c002041070350300304083c048030040c6c4070031403031900414200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 255479433 1250 255478183 255478189
    0x70e0106081f080a0c15090b09010f03020f0c0c03060106020a111507021905010e041a0d0515100e07050a230f030406020405090117030a0302070611030403030e0c010e 73
    0x2481e0b0180003000c0b044414002566180601c1d07180d540408aa40101c0c039109080c801ea2040000c00d40d02d10b00300146120442c1c40c0100e800341c2644c0306076082110180800e885661041c010000009170600c2d003d420400062400007150740308140c2e00169a1103504224002e003014040c0500410080c002b400d11104180c951404541901000e5442501e0f24030765003a80001c408166501b0a40161480c500c01c5401d607810341788040039010b080d000c90701003c407000d002d140c035014020074140010054402d1202400500100b007107180e01c05c4495006459620b941c00801c18070ba41c1c41021001c0407007142614024042454603405802e08040110400440758210b4100c0124001410340900c020135014041c1018a00c1d4000c0d40c2c580600310000000b80001c2c8100e64004d04291070b0103c2c0c00d802d469903540b031010304200308100004c1a50b0018046190054069806007084034001e42c1d01040340c4516203c40266940704603800c8010039030310750740100c1c40001006844440300702820500c228200381800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 255480683 1250 255479433 255479447
    0x50c060f1629010e06040905250b0a0509040b040c020615040609020c0106080f1c08090109020d050109150b0f13060905100e09280204060e0c0a02070e0106 68
    0x100256580070201d40340100801c1100301d1260210003030380c440c146034000da02d0500203142032003060000150240407441a1519208584489a01c00028019030300e4062250003d11024520303180107d006070000910702040b82c0040c0f0700c628460381e0780c07941c809550041004032241d440b070b510700443c5441c5090091580004003d07820004010500050031510340020380a80300c2600314403062400417401e54402001508180d0954041106440a0088000309280c1d100740c0008030703901412400614081141c003890801e900101103a0020604800c030b500401e9140030500b201711800e0f995002c01e2800e1000f4400c07801e0030f150b81174a06200922120000410940142820511075101e1000c4400402c505034018402007184040c10300040c64a8490b144403050700d4802c2101c072000100006000990104d100c0510704c0e50100800d4100443d6030120f0710b03a20407050200e803c1070742d079100030819a10071362009125404d0800c107580d4501240100a0070034000d80d00125040d000c01d40140a400d800103c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 255481933 1250 255480683 255480697
    0x30c05030121050c041b270b030403020a020306150405060f1509010504050301090807020102060f0108030703050f090a1e060c050613050a0c080601090615090612150b0403050c060f 79
    0x428000b181000e4208182025880c0380e10300d51041c0f4260340907407452840070360700c0c101409503103074015035001c08105000500501c0141c51030703400402c8005e1040001c204051500640240b0481e5150403071940842e01d03104090720361000c502484900038280b49450b003e03c41c0d002006460000c401d468181c007050814640c501400407018011030454982e91007041550000d16008000384099046824121082c1d07000b02e0741a40140204000929074a1040440ca8125811000114030300720395601c0888079900181402c1c009810200708004031a901c03001e0120180c10080003032028481c56040401c1600d40c00e500007000e002d601c103190000720f0300c0030820036070200c94245a1880d61140e071030414100243c06000034505c1c400c0701e101045210b00000c51074181c0704043c4017080916150120010b0560901d0180030000d80300700d5042c03046901c00d903e84500c42c195440040f5047c212075202100301203003608001441c04c004141001403140c104516024030100365042c91421030580040d1840c1c5c49030706 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 255483183 1250 255481933 255481979
    0x20705091918060b030607080c09060403050d1d0d0b24030a110306010603180f0302030408030c1f0506131e05070f02010608030906071b030f03020607030c050301 71
    0x24000c8080d10071881c0820320589420400ca03030b840302000302510500e8405840c02440d0400201043c18006400c0b40211050b0311860210b540c0c0e440c190b4807d030310083d1140c0c2c01c000300380400400540100b200751503030001603c03105001d075004014240d41030400354105216610312803169008c1840d401160741c002d5208035101403c4496a5942c2220035400229a5054810707144000300303101b5816004140c000701202651a42c1e641e8940c1101561010301018810b000314044040c00511900c0071100c04a100e801603d003499600c1d8001811074021000502a5030000a440c8100c04003000300d480501c061400c082110313040070301c04141c2d2002070038411140756503201410403103400011803061050400302c82c140203920f00001d0041a05240140c2007015609107031010556500102c16200302050252801c0d04011498a4241080c000000c801182544810020012a503603009941089010b0340003800c15041c0b40000400300c6001c03401d514108070060005001c0c000c0100700e02e0941c40200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 255484433 1250 255483183 255483199
    0xf04140120030a0b060a09030c050315010e070210060602030408100e07170c0402040611010b030d0806060d0e070303180806010b0d02030c12011410080f01030b1b030403020c04051501020705 83
    0x59940e400206480c1c107480340e200c5c0010a000c0400c81c1d0240300001500d00c26000f6407049a03650040c19514818994803003500968a80144886c1e0303001000381d907201002d80b0440d40f44150051840c000c41e001c40e0070005c010b820009061084d58003c01c051141d03100c0040701081020140c1e400c49403210554001d80d031360134851842c4000d24050811140e00340941c02801159520396842014204400c00d149044140d42002e903001d200b8580071529200c0800e00d51142a0aa91414100b1900f0342c03200384d40d045461350314095108480e50400a04024511079210580c03c106100c002c54a01c50f1240c1c4890b41070b61040c40184505100041030300c0030313098000c0015882c3e40f140030400d00700f4010440740c0d40329000280000a28a100c165003207450705e10a9958074100d0134511011203400d03100315585d041d5910704100410000e4400b0a0f150380c401d510102c2c1c0c1454080900c4000c90550040e5020341c01a8080c21240342249424403c041d0071410028940c0689500c4a0001c1d40340c1041e882020310035181c1c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 255485683 1250 255484433 255484441
    0x6141914060c06091006052706152205120a03121404030c02010806010c1a090a05031801090e070f1202040b0403060203040507060c0b0103290f0414012003 68
    0x19140c1a1036188030701500f0b464807032400d0034901d941c4400024107045c0083c01e00000003220b04000d140211810b61284011b2400f2060514a000550b80542450f070003007125000801c00e024050043e000102011008026040d051401441c1884494002c2840b0380ca680149000d1035100151004429a05003080d58031401e522410100400000108501c4000340104100400d6032040200b1801e1740700341c032030403040d03103400004584555020320002d041c01c000800c1941a500e03a01d0a042d44988068110741e0800c00c699582c2c1d056070040303c01c64000003984020300304550381019031f150142c5485c694010041c504040014800094000f0200c1400960228041d01c24200d0b011500034154151a455490b0764a140000c001e500454080c0e505004049001c214248610007075100c0940045003051583d0858a031010206000100b01903c5203070000b821161082101e4164031850b00c200055245140608100c0050594a84110256407410520302628804522100003810404c0c51250b00d03655 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 255486933 1250 255485683 255485689
    0xa15050108160c0c081e07080a03320c070501080618060a0803220504020301030201020d12141302030d03050f070c02130501030c05010f0c050319050d0f06141914 71
    0x445060140c5022484040811495000250702e141c140000d018840b0903c4444251500c909060281c070485800440c02c08020a01c51449207001f007040ca9442f00d07a40c0038507a45080c1510070405e0a061400000c83e40900d03044040c407000b4010308081c02d080c0e07064038010001032000090454004411122480441e41e180c542500400c0034101b10b0301240d50360302846004a840d030100440305010381c0c10f88040402c0b9802c042c0290380c100c0754180c0080c4070224410b07206607007030340d560058440c0e015560340a8400c90014082c20500030441c408000d505906580145410840340d000800d06050400c0c0501800d4900f182c082940311120b46894207400a1620000c0c1c0580322101310342481e5800c02c1c0c008410f00c824dc0079a5000c461098075010201c5101c400c0c15542d0a42160001c0d140e03401c2400880802c8141d42c80b034844282861421902d092254105981100c10b408008208640d89040601050020781c901880d03890080710740c2c01018804403c00040c4065038060701003900040f42c000c0500351 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 255488183 1250 255486933 255486947
    0x1b081609080a02010819050403120e0a08040506030c0c0109030903030e04020a0801030b07020312041218030309180f020d06051005040e01090209120604030c0b06010903080318190b0a1505010816 85
    0x2c6c0000d000500f003c0c1030050003464410360300c10303099140c510340c244040302c00a0100b10460340266090b003810b1134102003103490782004115a440b24800c02003074140400a1058100861280c0c441000c01c0e804d5040080c038040340c0c046002d009030b10401001c41144d80042d540381c11039900c0740003450199951a003ca045d400713110350300d4401060700c0050208101c605030858004500e90360303888130209600e440f443d81110881c80040c01080d03003d4070070320800865040a40000c0385040012807203041310320000c01240d00215001400075a10350017404070307241c5221410a0001030b407030303c14142414100c0e442c101c90b1040c401c400344280d0001d080d02c029200d08081a80280f85c41c01034a0030f6161900300540304e56400e94088450a8000b0b00041b020742c011003c50054a0700422010b045a40d2180c03c201d9400341304030148840c0c4a1100c507960600c542d103004031070091003440041440c7c100700d00e1080c1502c07a001060090303541d07400d0003401030382d9020300311961145c1052000c040611183c002a500382c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 255489433 1250 255488183 255488221
    0x71202010b10030608060f0712090609021201230610120b09100303031407080711120d060509181c05091804030e030a03140a031b081609080a020108 65
    0x2c400b0b9049044009505603015408030744502c0140d030b03020341d41c0a040140e0781c001118410081403564000401d0f0f03041aa22004481d0b02c6050b0024003180c0a40014850b010406032a0642c0d81d12000b00e94040040c4040d0602d43c841100c1031210306040040004078401c80c2d1510390300400814400c038114070500e41c2c204048081001e8a050164141500104d400e508940025804241010001144c2119076000240300e0400d0342e84004054950503400c91303407a4502d0601442034442c850501540c2c201c1c03900101121708449100040481c901700910030141002803900c500046d0025001c0c072192804110310718801e41c02c500308440a032402c0d509130384a0280d004265000050702040d0303003501580d490414000c60203a101e0781d0f0407661040c201659100c1c4950300070b000584904002d2110741140021309620a11400e000c205424651000240c04000c082c1d540b0015100005000241021403580c00341c05480e07280c010300c0ca038104030761160b030b03188941c20090411804070002480203518480584d84 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 255490683 1250 255489433 255489439
    0x12080904050c0705060c0f071709030105510a08030a0201050a060b03091002090114070624060509010c030302070609050a020901091a0d0204020714030307030c050a05071202010b 78
    0x1d01c0c1050560100540c00c80c0c401203846206044c0070035014820391003500c205107405014203241401607034171000e42d00e401c4a041201003605012a10107a81e081c06114861180f844c8100c0000849002d0901d629072500b060300c0784441044100c40d00750f100441c000409100620b880c610502c002e10219886d07a1950780480c1e01400302084402c00b07164190885401010080b00601040d500c9014a005900c82680c1c030510395886040c903000020f0703c0b60064002c1690504200340720810b0300101803803d80c802c171000c03642c0c82d0b561b81d007807603140c8200380f80321090020040a40f10740307170b0403c2c0e00031300544034134504035040c0045001c505003014461b4040342c1402e944124240071035485440c105903540f400f494228801d80002e00003180803103030391003240311025035160071074200d0004d10300317204007004030001c141d801c00e8017008104089a150050a0b0407600c032580195907038902a58000c00b1030310f0904502d800c103c010800d0104266001083d0340680e50000307050080d003842d00000340c5c0144465114160 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 255491933 1250 255490683 255490691
    0x501050429151204051b0d030c020102120c030309120702090711031b0d020c01021c030510030b040f0302010c030501060c03122d060506040e0103230319180e0112080904 74
    0x9100f00d1490940158803c0c8204d80d16001080c0035220001011034589030044807810700d2a0200b1720516041103954010300548002445428055049900004100c40550300000c148000420200030202c0c09168003802c0300d00f80303402a800a0076251000d40400c0401c24122020700c03c22100340101d606c01809000350250081480070802c1c0c6a42d4207041010140c00b0300010b10805500205890142d42d00081c84c203e084100607006070f00408000d05402e02c81c181d2108080002684492003d00450240545000b90081440c009095560b0541c1c0441018104001001200e0b003007112144683d03414202011000c000c4c201002c020303c2c1e81c1c406982565545040d1401c0315007900c0307942c0e070746600651007440903540b901d05009180c40380e40300d001800e4242000400100b14904d03400c034001c10b0b81c20290041007800f43c5082d880c2d034115100c20750890100503080c0900542001e42411701d085106e159a4695141040008000307505114600c5e0070b10205d52410100446581154031056000308100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 255493183 1250 255491933 255491947
    0x403080723160303170702030406030e030d020c0304030b0a02040b071e12091401230c0a0c090204090e0c031f2a08071e0c02060c01020703080901050105042915 70
    0x1602c400184015400302d070540a01c82451040c091000381304000c1034000354603080c900701c0c04500030b00702820600514001404a65181030b040d00080c0b140f542c4040045494605500b0100d0b004040680300124651040008111612420f01501c1801c2d400145002801e6111700003030404207030990004152000040d0550a40398020700ca01050742c04042500c51041410401900c0700d4592800d1421010400003084110110100081c600c40038100141c070188140c683e180b0300440240d400103a14190046001d00a082e0a40314060400c42150300a010901114003c01d4445c800042114180c0000d150032088400704c03038100c1e0b4074800154080c050400c060051101c82140e00c40b00d0540001c1105010801d1107105a502c00103a00150000e01c40c9040300d00700070340c1c105200c800120381021040c040041c40700c07000c0c806068030034041d80714004680781c0803003001d00b1500160441d5110b5071401d0500044484484051491607504090708403001032030300c00240c2091148036800b908100002401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 255494433 1250 255493183 255493213
    0x1b060e010501060e0d0506042015030a0b0607020d020103050a0b191508070f0e01030603060f0b0f0102210906070212250302090f040c09020301060507020111030403080723 75
    0xd18101c460300c0ea00e00c1c0c04043d0f4141000394501d801400500154880000300c0c2c0031904000300c1c04580071540e400c1c9c401001401010450300d0700303064031035000d5100201c104007d03a802d50285020100040320010701d0400c0d20741c00900e0010007090f003e410144c0d40c00004204498a900100d040e0000a094844c1d0502402200034070f941240104c1b103010105803070000c4024014400d040c0110344603110b442c2c0141d80d4034021106d40000c03e0b0901d040645880c03002022070218426404000400c00e0003080802454041c4502c10101c196943c1c115807000d131080e144d61079403400061012603a40d0406a49004140c00200e00340646a4040c0d4891840801000004000074440107202000310350112980c401081180c10350001c0d00c000307034001070071400007803c1c0400402402c1d8024801c1c50030300c0c8042c1c0c840e1071040c101e03002604180f0100d80006211800e640c0c1000c1419444c408400056103020b05583d640c50300e034001c019008080305001c204907401640c00d02c1c003100803800700f0021078040c403040100c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 255495683 1250 255494433 255494441
    0x13020303161b031211160f06020f060f0a0906140f0106081509010506030406020c070602100609050903041e1802030a0c08041106300106020c03030403050a031b060e01 73
    0x104403125110120394008100b00282d00780d080325007040340010300789019001030750f0700700c0d40150b40822409a580d054649141c050809005010300810b02080d0030b0900001914110243e09586803e41c450b00070072032051400ca4000303911903100000440c02d078140313140c41030203086501440b07001f20300c40d903003001640078102038a80d041711116a00c5e44d00d9034907401400c0021000d401690760308a220364005010f181412001143c1180c842c0b4401880d141c400940b00b400d0103c00d410000060b0008251580300d009103016900c09010040c40401080c1000d01206e42da0344194411100d00a0300414041c51101e90700300d4840c02411128201911b0150000940300254012a1240071861415020103d241c1c821800c1078811644160b00411000014081040940188021188000149034600e0100c41c40c08090034204203203038075018055040c04406400d040d4040200c9001c0c0e4010f010030400300b100059100303005909401d02c03044c1d6000c11050f115500000010107010581026000041c003681540 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 255496933 1250 255495683 255495727
    0x100f020c061801090605040308220305030d090b0a140612011e0204090f09050c150f0703080906010515070308040606091107170406120b040204080a26070b0403030513020303 76
    0x1a51396800340d20380304160340a011300c0c000501019018490428030b20315548907148a80ca540c040d61005698a9940030314640c89000c0e07c210b4585c5482a48040288000fa6560001c101074410b10200b424400484c1040c080108241d20401c2e01040040d841c4100798000058121200d810000d00599400b0b00344c069840ba10611803500d00e0445440c040c0850b41c4103a11400e68001c014042c10b0140c081080302c1c99038400d81b040e20008fc00c0154080d1138502c600203010b46842380d21001c116191049816041c80c60590081d0b00943c0c041c42d4a40018034075800302e5401e2075060908517629180d0b07050003802480c3c3d94005107011494421807a0b2a010090003801c1c1c00392061410444074500000c4d6500c0740e0080740324850100d8186004c0604902c0213420032038007090b000c2c0005080c156214800d515203044401c00781c43d26810b0103ca070300442003126241084246c281c0100b40303000308550303820040710070040c0302804056036000824283c0a000030042d601c550005d003120f8507506030314200e48108035192 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 255498183 1250 255496933 255496937
    0x2706230906010501020d09052101020310031e0b0106110109171207030c0207090b010512040311070602060601080402060306040b030d1d0a080a0f020d15060609090902100f020c061801 80
    0x1e000007082e62001948240138100fa83d00c2802251800b401d216812a0700c0c03d060000340000701c544510020244042c620070000c9480600c1c0301891410008900001e00b0f090510603408665004040b80502c00000c0c1198010300e4980c014098a0703650b07600400f00c1c0c0d2001001228040a4003c06400b0540600a0600114480c2c0c085855650b000c0e030440e0b0000c030203400540c119030400c21030406103500c25154110181092450244540c002c1142441c04880c22800300e21800100c10040c1810001d190107402140002d02c01d03070400300c0028103c4180208024031404002000a10b2500e40307800c45880b0030009011900c1e0400004d50203440c0d6000117a0600075000c4a1034030150a00c1c107400160101c441c40000b40400c40c0c00c0e910b418952950300a010703600b20000103000d00016402404c0d44126800310800011280c0c00d000008103640e40b56406800110300304086800541e484031112050210541454216840f01300c0d001e0b820300074034051241e8882c03400b090020a1310f82400c5030b40700c206401d03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 255499433 1250 255498183 255498193
    0x105010e0603150f01020a0b0a0608330402121905010b330910020c01020c0901140f0312121b030702030409020f090a06020a1527062309 60
    0x48248115400103c400014030703100360003c0d010070300b40400b01100511044c030640b007100c2269110a00c692400303071043c004c00c983e106010085004280864005200d01e80318810300d42038114840e50080d21304c202e22008a0341820045021541c03225403c10710640d22340e00b82d80c485120310050004c001c0310f4076420303916075003040705043c683e18140702044040145c48045810703e5034081102640c148a034000c100c4400c0c000c00c030300304060b500c0442c00094040c0d103a0051007100d510000081c2420050107000d4082e0000f007005101e000c248101c21844050103490304a00d41244400080c500821001c8903040c010000a019410a444480b4a481026138242c1070540c1c10010b226080c1c1440105d071050011703002401700740031814081d0000c2c80c1c806c80d442c25135402c150081d00001d0700c01590381d10810240e80b000c4a10000c011000d115003416555038207080207501c038201140001842d10700441c4d100b041c0c0c0302c11503c0c108402035021090266521090710903900313220052030301284007591500d80f45c0c425 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 255500683 1250 255499433 255499457
    0x1509070c02120f030f0d0204050a1806150f0c02030a0602040f03060e07120f030903080a120f0614041518091518030f0219230f07120c0e0f010501 64
    0x800103c8401608503c0c00035890a40c0c02c000960060300030039442aa101c1d000c0100007642d07942c2d500c20201402d00d40400e081c245a02d0700e0054125000c80d07200e10400441943c1398000300b500a03d0103c01408039040c408458110f620021f402c08000d0200140441d00c042008134000b904070190340140d921601c01040382d00003032210641d40e00103500c5040701049110f06018000b50303458003010415031003401c160f101c49481707548144090704140740071000500d415030b000c0d0240c0c03d54044c040c1e1144926404018440c00e00d224a00103c04104099009680701d00071ba269801c0210850002001042e00086076180d81010800190040c00415220400c40b6407094403850700921030050303c420701c2500307411078034902c0d81d059404459006900e00dc1d801006030080c0b0300005c404034100403500c036850780e29180b0140341d405410280c10300503800b400d03800780884d0344458000042d69001c4c1c3d00803c91b420814141490004d03c60075681c2c2248101009880900203410385500d42281654400d888210381002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 255501933 1250 255500683 255500719
    0x90f03030108060a15030b010b13170715051204050f15070503060d0804050d2d051015080d0e0102150f0f071b050c120312010902031509070c02 63
    0x100780180c030910381010001c1640c80c002030f80066680508003d03941d145d10b03030725210104c0ca51800d912181d2081c10001d40c18050b00d108101050181000d166400100003100c0525a1340d000c0a01415402c51041030070398079402c0c01203007a2011034410811041017841d05160590304c8601001e54540544540c0160140700b28142d07800ca4410000c503030741c0908565551040216207003880400f034400020400020425844492844580600a2496003070380350588810340d00c0003c110310704011191080b0440e000280d07003c294860400040400407884412030000c009103180305a100c40c409215416140c03d259810600803081180c09800323441d081200002c070309100000c200c1d607203001c2c081d69000043c03c070001000a40e8201c3c58070b1504c840114440f2804040261940da030a486690007144d01d1005481c10341d5640b00408900d0000d1800c0c4900c2518030100440180603500010b600800042d214040c0d0304100006d00800520032409402c003404083c203030342c41982041e40030741e540e02d00041481c6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 255503183 1250 255501933 255501937
    0xe0a15050a0b032112041b05062106040e1c030e01020412080703121505040b030d0c0f03020a0c09020c21030105040c0e130b10081e04020d0c0806090f03 67
    0x98020f00901881401e10f00c0a001c0540c21040e803e55000c3e040c0510403000c602d11131003c0c8514030912084407645480000b8401c0307003081d0741c0000e114501c20455050b900307124880905081640302000401d6840b0440040e002d800300000201652140040718171804440c490700c4084600140c4081200709021382c4414240e10440c007510540d001c0007004d43d0001100c3c0c6004110f0213000b4a00b11912a007180002d1065030181884c441030403001403014046450140704024410a0480003416054a0000c020303021810f5490054039000210640c0c42c00d050003480101c0003543d1104c441e030300b45511810b0040c02500400c40d103000c944030340d0000326004841c4031030340091800e01c410300c5130071603107403d08020190210451542c00c214112503c042c450701d420001d41964400c0c00d03008521103444101384500c0705600c80c8000e0401c001e590078001110f204c032800c4929200140c100c0c2050f070382c81e400030030005408900001e0040e02480c10000303100c03002107030082c050b0500d2801d8071a1002c2c10481c06a0340c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 255504433 1250 255503183 255503201
    0x140604021f030f0c020c03070806040b06210607091a07050a1b09150608220f02042304140d020c0f03150403030b0118080606010e03010e0a15050a 64
    0x310003124a40307074051010680a114112072440e001c10355110031032000090b82d40c080f520300301603400010b004289180922207440604400002000140760613191001588800b1f41100c0c042c07800810000c1717103c01c0c6400580c4c40c44100808481850509001c01040c0312800e1140341022a0a012114105005403040b900300d550807100500e420141a15281074003103000c40035400c42d0307000301e03000a030300c501c1809034601131800a119582d10514001015145d07a0340241040b045a01c4c090768100c0d10740e000d1f59504c8481d41c201084030209515403010600500000c005000896290080c1c0c40c108081c03400c10f035210303610411382da0001c1c1500d14101179403440d58410300d0340507800845669000d8182109010106040101101c42007501a810321803503250075141580041d88402807070900e56080b51801344034129420016001916200a00c0c5d2104006061a810000451140c126a0794250030079000c81104d8815900f00881c207252020000c061450040151802d00c000070f101100b181c860302040d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 255505683 1250 255504433 255504439
    0x9020d26040602030a2712120309080d090203030706050906060f0105090105040e0613050115081b04030b04062405090f06090c0304062004051903080f0c0f030d0914060402 75
    0x200345112100f1b6421110350011a100301c40715020020307102080d50304420003840010343d4001c0741c000030705041c4015004001a0418541412aa00000340d1f80b08115500c84605e84d00c000340c1c181403440041d0541c840d40d0f00c041e140a00304001c0c4580a00003090490181c0310844400b640704845c83c0041d50b40c1c0c090003408501158042c80100026040d500348076500680042c09002580c59160f40b840440d0400e8100c501650320030007100c05d01e0b64004a020750400c542040398149040702952303080262055001c01440701c0f2020010900700095500104440401c05480e0300d44014564060701090b0b032188607191042c0c5184c4e01060788010360741001d41c02000e028240d190b0740c1d6210707070451300d281e4800307041240c035580d89041102848001c8400d02c00801100042d03950762303d141408200c070b00e2858940383c00366800c602c0d004000240b81881100d01414000003540c0d01e843c03108900f982401428020030503980400220310300b82800644c0b282107118030407000f16030300712502032540d50f03100001c0341c000750 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 255506933 1250 255505683 255505687
    0x50f211f09020a020106030f060605030f06100b0901020307050d0e040606080c0414180703050132041e02070b0106030518060a02031302040e0f010e0c0a140409020d2604060203 77
    0x21120340301c0e40051145405600010411550725642c4c0f580300030300204252961903903104140101d00d42403203140c5030981d4100083c6050300380361062852100b1079103d0501329007400210741038142d00910a5440803900715081d5840b01c0c200174405440368601c3c41210388039a01d030201c04a0300f61b008000280c01130522010007030416041100304c07441302240041255001380450000c0a14803d0043d4032407003034001d07a03000b00d065450b020b81c45045000f49808a0070442d48601121100129450800c98180c0111404104200000d8807111583e1000c00e03150b5400d400010050305014500c180581254000c0e0b40800540d620f20b00403c001c8a1241d00803642c51700291301140c13000704d05802442d004544055809000c1000768006807c41c0c5400d001445983c11100010745002d6082c07003610000108034010344000c140d0b1200107043c0810300d004002400311111a41c80703860300c4070b41c001800e4640c00340014054010904040d101314a04080002c0d250888580291080072500700780c0d0211021a00218 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 255508183 1250 255506933 255506939
    0x80a032403031d030a08030903090a0510021b0a09021b1002040803040e070512130605160c14010e150a0c02031303022403130c090603020105030412050f211f 69
    0x3c2d410446070403803e0350521400c0c284201146480c00150f0013076460500039a940c0352004280b00c09400a58004e42c800d001110a00200d550041042941e800d28440c05460003c0010000b544440c40d50b0007052a0902c007241109041951681d10041901076004417030354400078040c41c1c01640304a001c0c4845c0358206020030030210283c50400364109445007080c1c0e041100040c21f440088000f11800d811314601901400f0900c401d5215403030700800710b00d8403031101280780c1402070001e6080401c02410b844000003584075006080d4002c6860800f08419101c8441c890088140300701c7c0151a10341c3c03132501e4940c00310b0403030b4000021212611004118802050b145030204030b4031488406848112003017aa000059a04200004510610344030b100500510b0050401e00c030b81b100140c00005a0502d85041440940e810009880d0b00a502c03015a001c4044846004c03a028061003074061034102011940d503c1c03010055000030300400350315082000c00d17510700100c0342d00b08000d05440001154005818 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 255509433 1250 255508183 255508217
    0x30209120606061c0902061917010806420909030301060e010c080909010e0a11070c0b0a022b08090c0f1302040305071202030d0f02060703020304030309080a03240303 73
    0x1200101c102c4500010703000e15140c000c1005540003400403001c107800c0d02d0341e2251098104150227201030a0360085501581040e09403079a82001402009140c044804074511800c078001605600309800320244201040c80e98443c1e038103460000180c0d129616200c002800da900010603641295900e81d40d24104c0381e4500010b461031501401c05550b2803004022030b140517290b041003c0c2c001c005201020324180741c841e8949040b5604501030010722001002500040340100032070303106a40d0301c9120030303680c0c03105201c00b40c0ca00049004002d10a080b4004454040108110581050b040503115015985e031440a0340d6221070520036055032003003002c6001181d5041c8041c40306005c1440f800010301d401e4407615034902e8000a644018460450707076000e001141000e000c4400140b41c04d0030301000604c40c102010b91210070042403001010382c040000303400d141c403d07000303072203a40e402c24001641c4001c0c41310b0080183c42062018a80107c1e249408900d0310718840e682c2046035010750702c00302e26400c01180 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 255510683 1250 255509433 255509467
    0x906040c09050402060f1812010608060f0711060408120a02030906070e040e0f0a0212010207020a03081e0a0507030324091d010204150207080c0a170a1203020912060606 74
    0x3c1a03030426818019403180c100341c10010030030112000e011980e05003808003000b4202ca1004660600c82c3d0404000b007003c0340d0300007016500064012109c564a13130b19120126051600c0c110074200c10f100b16400e000510400000901190096841c6600c09980d203201403001e0784000d8980030103aa000c4800121650300c240000c4040d61401400071a900e50480086031508a4486491169811000c1c2000c1140380c00c4030400300c0c4444900003503003800815000514442c585100150065100042008404406030300d10920740c54081d07007407500d5145840d001001500f041c4002c030040380c03030301a011824110111305c90b142080c01500d11900281800e0021000d01107515051101003080242c00d805424280090710140410b175001c040c0e0b24065030002842d080486d8403465403a008004030600035120500017009440602d013150382c03880a80017080d8075203200741e5405004d00c0c1d082c1103404183c5506070002d0075580303400c07103a12008a0301103c42c0d5468032001e8410070780c03085080202006407515400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 255511933 1250 255510683 255510691
    0x210050c0a0501020c0c0112060b0301050108040c18140f0103051b040204150519030c020d050715050411041d1c0c14070603060e040c031b1a0d050906040c0905 70
    0x1680e911030070503540c6a099800030350005001d41c00100c00040c095a104000c03075030300d1046040900070b00740b07080d0940c0c050744018040c4030b04000798000000c042c40380209001e0300400d085130480240f40300101c415070042c858101810400a421008180e00508880d2224142c03600500070f0860f540e2208090070204d022080020f40154080c0400912511001c40b9540600050307101d043ea19000185040c844031103054059080c14034000c81104503e0340042c51514424003421300710382c0c0746001e0230500707021317143d583d034881c0440e040030200020800003006a034000c0d0700070f440901940002c0c541c40894840c5103200c60200da031011320948000011104603009107101e5062415401c4082d4588141c015290b0400e0b5600d03501041080001503894802d900080c51400c464000c1c0e07050039521b0407104092884060101060090740010050f04504260b00608a5020028030000c180402c1c5070350307401203208800c40e2403070403000807981040445c0c0b00c0c0c0310b1070344040e080526a09150300c94005120140c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 255513183 1250 255511933 255511957
    0xb010902210a0b04051608070c0303020c1617030717070807151406091611010f06140f0d020d0b0702120d050f010501020d0c080d0b04110d06060c021005 67
    0x250303401240c1c1290340016000d41103080003c0b50401841c1c0038001070f98000b5043d28544445000600001035000607da60440c080703107040c10601200c1e040071000f03405180100307116405460000c901c01c03c003030002441184c1000543e81a40c10207032003030036100d00030404041d0504091400240526409070003c3c140541301d1400c00d408c020b0306440e4940c0f030904003003c0d813106a81d2861501800095280c0d40c030741c0041e00311485540e910f010500c116086907560701400600c0f00a80410107040303020341250191015004003000100d83e580c11280b80c0c4450820700c280510008940c64202c2c1c00c0c0303040d061503811340103441b504190304580c0ea035204882000300f2400840c0116002000b2020185006001c1d150020001140ba8104540700c0302c020784040c0c1c0302c541550300030418480360507002002a60307800c3d04445042d484e035900fa80340d10301900b9030303001403980585003815862a4900100c040c0c8900c3d014000100002034440005403847c0405d104081d50103400100043e04092041c0c000b040303c3c40400d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 255514433 1250 255513183 255513217
    0x5010b0d020721090608090a0818040615090512030328090507060903150e0607050d1401032102010905070515090a0b090f0301090f060c090806240d0b010902 69
    0x1404000146030070010f40f02d0009648560400100f941302c50001e420003092070140841995035a914104e07803088100154010403489244c4205683d40e90120f0010300c03010750152803000c01241c00500d04002405454070888031421340314040c80c0c001054074881c1c58264410500900d5480202920381d07480501441031903101c142079000140c06004400043c010740d19203100940c1580f034650300710b5844440140e000c52400742001881e44002604c2608400300c0d06001d0350311141c0c0028000503240311001051021080400002000054404c1d004603446035031441e0307141c03600744004a01360f4819400190060b80280d13014001ca00e0405548c0c0c44d0500c1160184c2d1500700c005010522040f182e0784042450080441d5030001800c00142001b41d04030120001c2000000d142c0c2d4405140c2100000030740f000355115004003d050041d401c1d60060a000b608807055460300004842500b48807612142c0403551070200380d04103041445003090640c0e4058820b55080c0e0070020410025004500e814a85e03080d4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 255515683 1250 255514433 255514463
    0x3105030406020102040320090703051512060603010606021b012010090b16050301030b060d0503070b0a11040e16020c1216170a060519061508010905010b0d0207 70
    0x10801080140103a800140e2200d14604040e5820450601380384003942c0d8410703c1030503666400d00c400741d12040500340012075460300500a000c900200e00c9094005000c40300145102d103000400fa842148205c00a100320b985800c000c03603d03501a1401062481c0d007000302009a90701440341c0043d031184030640d16001c0d2143e0415546040c440784031a0404aa5030107074032042c001c2041003581d00050b00080024091070002005050707100511020340890190004140240d940c10541c4817000d8014084a8030346039a414800030b580c005651000d070a5141001e61050b1071407510a8804a543c0c8021070092942e40d10a04a007580c0048200f204500400f048184955514030307204040d2940d0000a0100507a50064481d4800c0309422080650185c49003d50308100d001450300b01c0d070356100101141c15280c0300c400c041001450380c84101c01c6402c0110120b00b440d000755400e10707011010750342c11105d41d0340c908a0900700c039400c1c0250411141704020120603142a6001400100d1044080340c5060714 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 255516933 1250 255515683 255515693
    0x1060503030415051306050706050f010501020712080c0a08030109050609060f061b030a0306090b040e0309100203120f0402100305040b130c030204060803090924040b01051207110d020631 82
    0x11700354110001044011030076201b801014030940382d10030b2980e0100e807060750601d00041e42e1182036100e411030500003842d8800c1041060016611103000c6002242e81c03c91003450001c9041c1c0003401002c1d9120b240c500015510701c1e0800669010300c202600c0d13012486081810721505501001c094503280f4100702200d20594000c0008040d04501c40c0d03000150b0600302003c900c1034441e1610b0240c407842c10304443c0300c120744001c0200c0380ea02c00200d50f050040c1109030007d03400d500900307844c1c054850281781000900c0140e03d038524420340c07084542d20103c0f00c80d400c0c20740848030300b40c07009410440c0c21400600c280101c500700d444854040e040760303504103549034002820b45545822290940d0000701c0e4156007410400c6145403c07164400030840c41c51f4448581001150034a10b00c1c2d44500d072502c0c95841281d02400844092110254105e4500d04d0400800782006600d440c1c1d660240c0305805d00a851036102040d085d00510950100010100580754031402510040c8918503003804090510070001d5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 255518183 1250 255516933 255516967
    0x1302091206100501031e1d070b0403060f0c081b07021309021005070512031003060905010c0e06091302031e0703050f07030504150e07091802040e0106050303041505 72
    0x3204100100301600d0054005100090306074001414942044103c000c40c4102083d1007400c04181540061402d043d8042803001c2643c540d1658180d024418012840c14585401402682e0040c2d1045c800e1000c1e1008880464426586040000d0b4100c8045100000c0d0903070042052303215034112908188241d0005a940703031a64030140e040c0ca40c0c4408407021400c04036012000c84001d07081003818480c032515040d4580045c1b0420300403008001001584020b0f880c41040c0146401001c100103000c41c5141045c028212030000001080c45d500d0310715414a01541203580080002c1d211070f0b9980d41c0d800115010f508054040382c802c2c0d50100e8155030b00455a02e80e40e00c41c41440e50003060710b013040c003091070012030064031690815041804010200e000360300d2620343c04420800019002c1c00c0e1000c424185011038010b804001d003801a141c44045c9040005481580211001c009652071610410b080358100c1c030615406420510041281c400e0f15407500c5107106890070041e00c2c0c00c0d0840043c01c014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 255519433 1250 255518183 255518209
    0x71b020f0a080106140a050a06020a140a080705010f0510050105090f040204090e030d0609050c090904020a0302040606020f0c0a0602070522050403082d2d0708071803020906130209 79
    0x100245005d00c03c0d00c0e24090001900a10b4240c0e204001d0310b04000d40251240501840a44240d4651264500007001000350030500d6800c0700c01291280314a00d040d40c040c10504180710105801c0001241042c40000c804a0803907005850321403800c02110203000a0b80e480c080c0b450b50044d800c0c48002400140c5005243c0c1110203000919510b0414140072011030b021130304086032181c600420800c4044c1e41c6c00c00c480f04d008046800300c08564a510004103029000d800003508541440c0001809940000c1da810f07100c1d4845040d6600c9d0030030300d001e100103000301d8410940180d2284400304003908000e44201d00c10300e4401c1030052083c110300780100a54030282c800b100015094801c00c203144803240c02d450400281d01440790035020000d0701c1150355000280c2281d80b100b519034500c2503149080d104000001c01c0000b03812100b898940c40250400c1030440b000e1010072410040707850468000600e26042d290b00030310411003629114140304000341840034035501c5582c02c01c00c2c5241903a911403072040c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 255520683 1250 255519433 255519449
    0x80706050901111207081c1508070501020f060a051902070f11040513110102010b033004240c1e0201030e0102040311060c0304240206071b020f0a080106 67
    0x580c0322118001810880d200b0091000d41d00410154500044c0c070303004035032049403c1800241c480c0000505c0030100c001c100710051003a07250540700c0140210034403001084500513020750f104207a1700c42c01a1b1b114400c00d0840c202a80088001502d540c24540c0900c0c0c11480060340111603811206015040b0303844010103681d004400303900c003010440400041b5246600945007840700f03092041040000e221880f03401050b16021341c00312640e0364400d6020002e00f80f0000c040b25140841c03404602154640c1140e4140c4400b8040000fa00409017982100d0484e0b218608030a054480886242102626411181c2c10084951300001c00724003468424030550003a441400c6170381125100160480d004210045480d900500007000844c8400607a01003d000c02c0e1130541e41c43c0751301c8034094154802d6810038500001d8014600802c28010400344c40104007a4003256101d0b180c5840550b48081c000110324018004c0c0c030500c1d001800e0480c2480c00303200c8044c000e0714401c0d8483d000709003550140d801a10b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 255521933 1250 255520683 255520687
    0x5031e2a15131211010807020309060708040306060503030705030a03180b07030e0706090609030201080a0605090708011e050907050d0f110903100c200309030d08070809060903031602030408070605 86
    0x2850b1111a240900200a5082c0105041201e0340e243c1d42c000034504a002c0c14800c00d00009100316009008a0381d0f4024028075042c0e8400092030300940075086404240c0e4018030307103035000c0f6080c10008221113485400c50002d41c1050b00410b0104d000d8440da40ea03080f41e211051003000c00140c2c2d05050030b4000c003616100800c940e11189445490450513a000204220040c0402c0003450f07040701d08032090f640c0a181600c0682d80d004100c80242249600c41d503000504003041207151036002079800d040e160711001c1d11110254600b10100b149a040c014194400c4099001c500d034240036900030b00c80484000c40200b542c07800c1e070301340c1802ca440820315500400b000042c10401c2c2d1406010301000c40d00500d8082003034a8012100a010003070740784981005851a0301d8500744c0c1c020402c05d440c4500d40080498000c45581e903002089054151081c4001c1015031011540c0c500b00811494420795500d00103600b1951060304891462620004000544c00300304404282c841d07050001202070b0666444440d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 255523183 1250 255521933 255521947
    0x190602040501031808040b09061303030804020a090e100e0a0606030b10060c1505190515130203070f0e011106130c1d0c0708210105031e2a15 62
    0x16041d104100c150300e44081346001060005a864010b440c1907d40145d585502c5492100c0032420328459088444139072100610700100b050351207031405206038800d0b982c5108103542c0c1d007025019149201c001d0405a00602c0350700402e078015501209111100400316580760b45183c954004440d01030b0003d0300c0c080300340c06c1005100010405030308020011072403d81e840b486a038580e4529560520210b000c42d0792208081880b0403050002c4072418146c00700208500e0408040324151030320401c0120b401201c889200c0b40300c1c00c00500c241c80c03081d03040703480e109407802c00e00360100e0300280788800e42c82c14041c90b4010b1130700201d410400d00340705410010039889031a0b400d091440010000b0fa104d0310789640c08151286d801c083c10810380c0d41146103500315075143e4030f080c900303060380f40900b40300002200f0182c0d2880f0151a40c11070324904980c0c003901680c4039507142403210069400759029008081d0311006e50401d0500b0f4a0300041c0044445480110703903120031038009003401c016030780c1083c40d1817000b0503a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 255524433 1250 255523183 255523187
    0x60b0d050906060114160515011707240e061603050403020909060405070314033906130f06020d06030503030a060815040206070c08010c050403052814190602040501 72
    0x6400c0b400909100c051080703049034600750340c4101b4040c809003d1860341c14404005042111100d61011070b2410320b0b044d0b8560b4003000c1540f2400010010606c1002c00c005008800c11170401d500c0444190b0740301551080c20350660300703090724000840c1c00200410181c1c00071380c0c40700008d0052503c641d0360795540c0d0349507004000003420090054240c0c1e0300804203100c0020b000086036070490354066140065914040702c480c3c1980a1403900c201003030096904240c481034000320315050144410144420361090003040c1b030741c5a004880302c0291000046a40300820959281c0e69155880741f4405032604035958007840540300c89074021542a8404410b0010891940c060400582001002042001030034000050f4100010303002a010314400194802405401100d50025144a0340244201d40c10084000d000758030621055a850050000c0324500500c4940800021a02c2546480917060785032100710200001c000788109500c224550008a0a0881080c190083c011600103864511748000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 255525683 1250 255524433 255524443
    0x8070f030501060f082802030105070c020306100303052b060e060108010902030702030d0207050f010c200304050a05041e09030c121b0b310c05030601120303050406060b0d0509 77
    0x8412070b0b0003004c0c1e5041c004180001000801b02000741c0c00101c0120040c1c5404040c00801040650154240400c0004454115070f000003a40d200754206c038030369a01c0c9051500c0048186c003000f000140304000300c54001444085c4031589500c120800818446a802858202e9200d40d0141e03416510001c1041280e60700304240d80c1c014400319100713520314508485c1c02500c0307204020103058891341c04940d14090220401c10030080b481c094000f0481002c1c2c00790060f02041d9139100b000c103500041641e0200d00c032804000e940490700060720110f0b40d9405d00007040b000d81010313015a042000359020449081005d40108042e01c0d000303031101e000ca000b460420746200c4010412000503c0140c0c4c629030084580140e0900d0201e8007c23003064625291616906003107a41c07140441e0340c28585040804100401028084c0103074405c20a005055a41e2400e0640750282407245031148407500241001180c0241c0140740d1107442101e002408540300e070184039664001403050b40c0d8856440c81086958003003004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 255526933 1250 255525683 255525689
    0xb0a08070807091b02060112060207021305060319240905070906031110020607080411130509010f1119140c0f0d02120f160501020705030a140f071b08070f03050106 72
    0x551007a40b110500086e5881c030301803003095000f82d0002004000d010040d03040d11b5400350700031b100b03d99400c7d520940c2d602500081c1c420501c00e0040c451080d03040c03c0c44511100c92a035000c4407a60046a42c0340c500d01d12810150308201515841d51042c0000903030030b00014000d04400c2000182c0035013503042c5000510014a6500d00410420000031091500003604540c40781841c5440b840b59980e03454182004548011100e801140c1d0424a181c04d06154200c14411020440204044103d269003401070321841d801074070305800c1c03c01410000390700462a0103103080403401e284035200301d6400003445590000003916515001340b544000164803c2c00201c50200e5907100a110041c1e0101c7e1441503449509581c2054040c0080e5121010341c80c216000c2207907410000854442850341050341c5c8a9200b1540c90000580f00b03500f2902c0740b0540425070701002031031070995050001c50b81c0d406070444505188149982d0000300000b50401007000508040d009451895001c00d246240c400d081d155550 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 255528183 1250 255526933 255526961
    0x7061508070e100b0c15090709050a02130302011b0c03030f020d110d030b0a0e0c0309060f0106170a0e060a0c021501050d0b070c08120105090c0703080403030b0a0807080709 76
    0x280a0910720069404058035140c51800d80d50345200f00910707240904800306c440c1d28044480c1000143c02000c1501030032204a24424001ca0399003120340c004921955107498400365441c02e050002d5403107248000c68800e9060b01a4030340c0324094958540d601900d0340101c00040440d0888075605505104000305520a030400c54990146055043c0e100c201d0200301000701551610420550f81c3c3e499620b000030442905001e205040c00442400d080e802141d20080c54030454001c45c0c1001c2c001c92409048a0b40341e42e842500c2d0b003080b1480b40303107600003030051015541c6403c9150801e0006000340d80c0101c1c0030900015a83c0800c140c043d041c62029040c0408501103440100075685806030000d50599110320504c0c0903660b074241c140c40310341214034003802000d00071a03440850482110803505840c01120003d006a4801d4045961441502d0004001860601c04540000d000790001006842d004080710402034880c902e4a282c201c6a9000030065404943c04120001440c465900010514 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 255529433 1250 255528183 255528209
    0x1415061003090f0b1f080a02010906020607090e0c1b160503010b0105030406110c0f15011202130c0e10120c050306060a230a0201020d0b1c0201050f0706150807 70
    0xd48803c1c844980d505400741540340481c000540c560000201e5002c003418036001080b110352a006542e59034040070703600b00d0102d00d000d100407038034900008410b1b01c10b41c02d035541d000707610742840d405050001018080020030355081c04000050a2aa9600f140c0701c02d20b000103000c010388405626844540ea940128081e0345000d0003809070780da01c0000c03642d02c036401ca500401c504070140400c0d0310610420b07a110368180124035041000100100780c01140f0200c00b03200f80f4590340c80c0c0d21000407004c10703808005c0d80303c0f011b0341b0000c900341803e07000020b0701c20b01400c221030260503070b5000c10034508110030408002042031020b03a16102c41c501c1a508030b2100c51810301e066103810b0001c2449407160b00002010300c100402c80000307144c01e40400320b041c8548104203640320003200740060b001c0e41040d401074191a04120b040c0302c10342000218014004100e03010302c40c0c80c480c0c036001950709620a02c91203401d03080030031001c80814000d005000d0001c14010500d2050707850000c40504085043d01704140310403c2c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 255530683 1250 255529433 255529451
    0xa06170706081f0f18020909070c020312040b07020405010801020405010f050d0e03070303020c0c010c0203100c0c0609080306090a05040209060f0105071407090c11070b071415061003 80
    0x200180036400c0d40c250b070804011903101d10a1002032200c070310000c0480301904030800315412002018035012242e9504501940341e85070110303102a0300030744d12216000124403001695041c803403410300040e24006400c0d54400410554000800e074000c0c0c018500700d04e000141102141410720405005246001c000c5042a0400c000244101c41c0e080c0c6034001c00c500400c21680c081a0b40d80140c0100f101d402c106c0c0c0d603995151078090080d40001e0715980c0700b4000d010700009154054070380208415802070162505164103a1000c004140100ba5001000303424411100010f41c9407003509450343c000c81015450303107001e00411800d0030008241041c2a810142413000603192813041c140c00203800c98000f10002040801250f95001d8010040d020711600071480450110206413101600c1c440682400681d03203008042d0b91010dc04411140702c0e620103101045400a8000030304030142c440e4001c40c14000313201c0c140b40d24180700000421003000c1c0c1c01c000c0c030000d4030f4600c098900440140c2014414500 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 255531933 1250 255530683 255530729
    0x10170105010b0703111c030c0809061603020315090a060905011d0c0901030915150b0423220e15040506040b0901020d0c0806030705090408030c16020d03080a06 70
    0x44000040c01c2c008220542005a003046c40b0400240d20307003c1c19400c801c94490f80007005050140d0511012400301c5020580a6402081891140300c443d024820030600041048000b580002c00c00c00703600140e0a1501050b40c0c6144480d40580301d08140860440d041140810071184183e0051001a60060080035031108951025601c01905120580caa600300c000590107000c05000c010308000f0550041c0011110940c000e20b00d1528844059140545655001c0c8540c402c1d806844100b4450003182410390290200d801c0c060740c00640101200c1700300e28601180c1e0505040d08065036a2185034040110074104281001d00400340d60f088e19600b03294552541301c0b00042c102601d6819a000083c0340b107002501290741031041c40c50100704201040c80c0041800e6425940383e8480d020b4000002031515123020030303500890b00a018146540c0b100ea43e00c1e030b0a03174800d0710a082d10000c400000c0025960306d010b001401c5000307888091080c90404a0202155440d40182094074144468010100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 255533183 1250 255531933 255531937
    0xd020604030c1a011d0f07051804090f05030301031707110108100b0f07020123090d050703020a0e0a0e3706060602031c14060d02120610170105010b 65
    0x141e09402c202d11592140c0c10b081082c032018a04800c075040d040c40000528070380d016000c2c0d803d01d43c008110707465520380046198003c2d43c1510301c1c01c0000c101740417401480b0019003055400240082000075480f11981c2e0301e494402030494142d030750341c002000400601841504101450a46c1d130003441c90008541d0b500c4c5c15054003480d41c0c80c10802c003c000143c05020103040e2401030400042403075182e843c1c0782e0b02c20005a2008204034001450401b40e2112015502e0140c003550740110303002c90528405e00240700d0201000c1d0800d60300c83c4507120000001da1108040d000241c680b64580c24098648074042e541a5141195403120070742c0040c0c500700300000030300c4031400c2c507040464900789002c2c41440c7c141203160b58403d02425003882c01c140001c0c019000401429154958051407401c085c0031001c0303408030b13a03590704141e50307a4a4100c00950306142c01d900c0e284095200030325550205180b1190749150050496101007558040001031040c543c00000180040320384800a0119604141840c0401c1c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 255534433 1250 255533183 255533191
    0xd170a171e15040914010f02120109020901050412030c060c020303040203060109110403080d060f0b04150323101e0f12060b090903070c0e01030b0414030408070806060a080d0206 78
    0x44544180800c05600054001d550030b01c00080c0203000910181c201541c5002504c580c10038075621700a400384045c2c48074003e6032213030503461280070541e0f880d2000c584069448101c0040c10480c0800c00840d003242501a00890300c0e020380e07903400443c8000c2c504602141d0f010105072065500a01c01c0000503900003a00b541900c00d42e440c00301d6041c0602ca43e5030701e1030207250400ac000e100b0100300d0860b00d480680c04401145c4d440d45401196176030b1885c12840d2485035006070500d0410300761111891501030342240380a0361880c940e11022120710b40d88001c2d194410f880c0020021800e10003040303400206000c80203041e1420be40b002c0d65030b14141c0300d84078100c2907210b03804000d88040751000c14030030a44e10082d01001c010f4200107903440c00380340041d201d904c0b015044400d002104000f0418054200308203058030f0b407058610b40585c4544e21095a4024680e00034080d5103c200301c0800c4c02030051000300300403c0f1000060120f818100e0801040714400c0d0001a1070354000102c50311600c2d40010720b00e401c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 255535683 1250 255534433 255534481
    0xa0203070803190f1103040f1e08031b030108030a0804031404032312041403071502071802070305070308041b0612110a20070b04140f030a020f010302090d170a17 71
    0x1592223a1078404044440540784060a07503010058000b406035000086101c0c8aa10744841101d1920002106060000b8024161030768000d00c40c10705001c1c025580c640d0420f0090400001000070075030701c03005503071042d0811650101c1880c04044080c03010081c04001c581a00f000c1c20700f44400003214002e41c011442500f164480c0d06540c2035880d1018400310001c0c4c0148050003c1031121400040d644808911894030b054440c54006e61441c2006c3c4280c4031003640c10f03a41d051400c140b80c2c60458080314090000c0d2020070342c07a0940c0b81e00d950401a208020f01040e20b0308000c1c080c505143c0d0048071000c0d0b021540101e002c1100c9d8110303543c4501c41810341c50000a80d04450b103908842d0034034061043d0400904680000f8012821840320300c200c5504010071594204064800c80070305446141c4040002d41250b9503850310080ca6010703401505034140b018110b80ca01a51725110700605480c5115800d407003031400100e03c89940d51202207803554403000c2030380131010709002d441100e00110050110036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 255536933 1250 255535683 255535703
    0x402060313031b030e10020703020901450b0609060403080a110105070c020a0510020d0807022e060f060e01050a0e0904150c0e030a0204020a0203070803190f110304 72
    0x10940034081d503460f6003a01e0100c2085403501c614000c0d080320340054003a4441c2d681d00c0301aa1403070b4800110102520380c00303454000750b40d01e4040b0119000010b0b24900b01601c1707041c4044800f114600c40b0603a140d03a0360005120604010741a075800321520600d016000d40750030401009107031924011201240d921035140d41d5a100c5140c0120340e041c019030000c0f4415400c1c00d050001683c1e1002c80007030840c1c000c8941c0d6a14035541e00030003588544180c000000b5812081c400e515903801623244039030010300750040d00c080913501602462629807442182210175054051140c0c021058071514028104a10310300c001c40c0d051400141583d0f071218910390401c0f01c0003540300e24003481102c0d09584400090102106d500381b0b4603012844500280800011605d0400d98000c06486811000300c204400f074040c00b55030752241c0910001e5440303410b4540c2944010800341000805000003180320b0080402d60040038841108090309075501000700c00421420305204210442286040701d8105620090000e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 255538183 1250 255536933 255536971
    0x81b090a120314070c0515030402100f1101090602130803040305030304080a1809020a030e010c09140612070203030702100606091403011b0e01020705030a030c0209100503030a111504020603 83
    0x980c0e1001c4001c041030707810b00100d00c1c0002c00a03505040d8003610300c01c03070740740c0c01c07d45803040010705902080320041d5000c5d506102c100081800b0f01182600307199280b9000c0c605843d00341d4080e081d24043e005c21950583e00140020121400c01c0301c81c0058032030303103016502e4685151180b681d01d0101034000b8000c0c8400007a55500e041c01005080c0e812400f00784000c641a640e0b140100007500048114004139003446c40310f044160044c8a101541c0c2035a403604848a0300300b8180c1b5190810710060150130a2041007604030000b0035040e55071147d20160700943e81c0c0e00c0d020302d0090601b001050315a10003070412200344041c58003e02c840003a100044006200c12101d140041c2c05804c11115442800050003000c100c555445403040903070072002c0e003c446442d5502c0e018990390342d560190186c0010b084049a1005180507118203405c0030a411440580d10f46510020341580d000c0394030308010800441c09486002c005000319100007030078000d80d42071031074160003150003440014104d401200e5804080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 255539433 1250 255538183 255538187
    0x6040c26070b03041208060603180c180118060803041202061306051b03040503100e0f150105040c11070504020d02070c03111f050f07031e081b090a1203 67
    0x10090010500890704a41c1e650352280a0661050314261240c0000070000c81e5403e0154241070300445002c0e01d4549075640d1a00d100d403950030b83c1007c0b103280d8000c140c0300d004141d86600c0f40c10305103000c0240107003d43d40351840811942d401c100c1c0c000401c504040040144842c00b2040d101100c102c1e401c482158002440000c2030352145036024468540080c6020840070707400005050500c2d80000c3d285000320b03620b0900e80d0381740950720821750b260f80100c4020310f42070044d411009160745041c0c1101da0714085107078200c0c200006070403d075141710a500c00400c62440e050084409007c09810b02c80c03101c1f0742c07211005403519030034000c80b17025540000b1a5000101c2a0b070485000d076030001100c4400d80d459190000d2480e54520f0400d101740c030760f000c91101803041c1d2680e85031821020344a1600d020b180c00101740590700403000c25014050401400b07074580c2508880f401c0c01a65650351f114441c0341900268040c800c00d02405170350f6010030702c42c0c13111070b40301e6885400640e141240e0142c2e0040c480d10301 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 255540683 1250 255539433 255539489
    0x11040803040627031e02030d02071509230420030f0f01081507140417120c03070b0c040302090a020706060807080c0415080f0a0b0601030c17040f020312070308060306040c 75
    0x1700a4140c4501c1e400559060360105000341680c121400b4040041400c000440c1c0490300c1c1d0140712014000f8003007000c081e01060390881d4519201500c00300c1e0411750902a0b512501607035620f0100c080d4008204403021b10000011a44404000440820f55044c203502c5a5101c10119440078082e104c1004145200d00404041c24144c2c41030300010703983d0f80ca50301001c440c0e1080c001d16141c248210f90504820b00c20180940303040c1c01440000b10b0030241e0544a2a05c60000070307140e845075000401c00440961542c42250303108018007a80580c0d80c1c040752414008503452680504015006100c003800164804100703200c0c101c40071500031441f01a2000c01c00c44c1c0d00866840891103202d0a40d580344a0720002c9a00c9031554000c1c03a800e45241e0b110781c0107606441000341c1400005103130340d1808405840d800301c95a001800340e0100054401306501207460000e4a64090040180c003064038020594031942c0d6603801380007038000d84010305140c1c2da43c1051116901441c1814010340711a0340c03241d007070202 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 255541933 1250 255540683 255540743
    0x80411060a120608010b09010b120c0307030b1e1207030201090611010605040c0206061002070e06010f051c020429090d1a010303180803090f0f03011104080304062703 73
    0x1c0c08110761550f440085000349401b4080034000d200d8000001803144505040d10103800c440d600d11540e55507203031450030302c660004040381c0030f0650751750207508a03031075500240c0040c0f0001010603800d60f0088041120016000710b801c2c800b82e001d02c3d010300041c1d91025842c1d00315042c0b401c0c56640000c0d000143c0f4003401045c0c010350341040c03401c0200b1280710360004000b401104207070380341c1d510201010412610744640e8090350881417816030100748103510813090f0722900d20f96460f00c2400c12040c08500070030400850400318000d900441c040c001d1740440d100014041003503448643c807007070b15019500ca040c02020b403000e02c203003003e410000034000c440341c0b003800c01011102c3e0310f017003981c40e0b00e8054003c1031900307108804041251804545d015000040710194a03000344914035024504040004100c01070500d50381554950010700381d4912400081c0c00a461004080d540341c03410300c040101424440e4a4210500700148460118551410292000d5a4100300085601024003d0384032811490303c0e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 255543183 1250 255541933 255541967
    0x30c090305060f0a0c050703020c0f010903080a020703031d0d0b0c0702131a0f131a130e0c01030c120e03070b1e0c0f0f09130903080a0507080411060a 66
    0x30810010034100e6603c00d01c504902d141c10028802d5042040390b440c050406d000700542d01c42d10541c2c2c0c0603e0810b0f0b01a00d01001490003100c007980301d955643c0a034011000c2d40c00980d110b2035041c010950440040d5240628101c03807150100c40c540300180c507207000908003034106e03140200450100c07101d4004030b03070034242c000d05001344c803445010088009200c055401201641031011260003031405015401d190130f00240700c2046006911500001000c3d14010025041085403183c0c18503107030101c544c3e03400100501c00180408210307840318205080d0f810784038105441d103611009019045414488041e02d82c000009801001081d02e510b18881d0350000760403032500c01c1c200070b805240c0b4044480e42c600a003d0720034440c0c5803441c203507040f401494050096034405204a0084061003406040c04100042007900c121069040b9101110300100c420b0700003680d58020004a001d840c018560003c0300d91504404904d0192980341c0710009040100c2d1050200140750f0000921461064056032310300b0f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 255544433 1250 255543183 255543193
    0x40b0301060e09030711031516030b0a0b0d110f1605071805010503011a100e0d0b33130f141006030e031207030507120504030801140301020a0f030c090305 68
    0x41c401c1e540d494105170001c46240c0904100315980c0d080201e0b507a110001c06410440447d00c1c1c41000f040b008505a00700f004140c0e4503920b40040f590345140103002401d40103c0350790344d0303882450704a0a0311404191681e000a04007c0035040081100c1206c0c400405100384004c41ea5082c85c0c40e0b41070541d568821150715040d00e4140003450070980c0400c1c100d880440c0200880c01450607001c200752003040b0040d51010800801662050003855422004000242000b2000520741d440c2d03c2d80c9d80d0300340c4d960300405c529000034244d00e80c2c010350700051039424480a49a00b003038940002d039480b40e4560f503030100141c9851810850341e8881c2c20007542441121040100d070302e807420701c407501000c0f6442150000307030400c220302c05110804012a01c440d03030b015010600a5558201c01d0300504400b500307800030040f1041d0122103100f080d202e00c5004910030340e504a17440d4507041401200004042c0c00300d109074810080c1d45415900440d00c1a4011224140410300c1e049009040e98030b4040d65201411501407 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 255545683 1250 255544433 255544441
    0xe010c0507091d1c050f090904060209010f02150403031a040f140a02040e15030f1b0405010512062e0b030f0708041208090a0c0608040c061d040b0301060e 68
    0x3194010f0b08a1060200b1481520384450f1840b980c1c0d0207609640801c240342c11185075041078480c1d0300070081010350b4010245065045000b1400c0c003401110145c40d8558041900b44540da441385c0c01c80c09400d064801020111161650b070000540041c00007802d16658856100d0400103410b2074001d005401802000440840340041011702500301248900030886000100b40090300d1084c0c030165400d000c0e000255030380d1802032b51508200e4591081c0d040c4180c514080302c0e01c80c10071002a1601c84010702c4c00e0240b51010038802134a5040c6c03c1140310351024180b400b100880041c240c0d900501198480d01401c441c4131034005080b0a00c40e051418121712074004c1880f2100c040110300450361080d44000d503603500d5004440014050b40c008241d446900e441d074043d46c0c41880e10b643c100031143c00383d9443c0103050760303242004000e55010350003140d200c1c41040284401301d00901c008018504240200002c0c01d1440c8a5125a581e032042c0f00b581c2c0e410102100c0e403000d40c80032020304400352500d0b4040c10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 255546933 1250 255545683 255545699
    0xf0f0a090905010e1008190f020a050a0f0927020105090a05030706050a0e0405060102030403033509210910050c01230702010c050304060b01030b0d060506121c0e010c0507 75
    0x1104070761440117219482000030701018009030700031246644581c84e01164005980d17076001c440c00240241d912003640c07500400c4030350b211020765000b4040080080416464807801c44d044d02c3c18032410a17002e00340071020100c6016451501441581d092074480c0c2d4030f0040340c00003003d00b4121b80040e50140b26140b4049003498010300106490030711030b12901e10140042c2d04110aa8500f240c1d4030340181c205101c20030000e4015050621070700d2403942450300e500d089214442040c841480c0100e50a01c6031014428a50b00600038000300c10180f1441088d0340100a025031968410f13801c103d80a80203003051683d40700d1290003a529501e46000084c411944011069a03107242c02c49040b55150587c02c0108007128014032031456202c4d060b440c0c86065179115201d0344010100e01004c9418140c03504a0f50019070345030511743c050303113201e11000a05410b00c4018004112113064003007240b640301c1011040c0c1801070341c12111004203140f2b40085c442d00305a004031407040c140742d13000b8402d101d58070011813a20 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 255548183 1250 255546933 255546959
    0x71509080a031508300a0302090a08010c090510020705060c01050105041b121107080a030608070f0509040b070c050304082b210b0d03080103020f060f0f0a09090501 72
    0x7882070750b0034080050a1010409140380314800c0c0d4509601c4050401007043c076880c0320740c10b80c02c1ca07440900c410042e0901c9545683e48603001120000b540040c03004524540b40c00074002515805008005d07442030080b020b07040e1050360055600c140f80c5180c1c00c00a05108200c1513000d8400604017a0b25440c215000602030107003030140314030030390801c4000111138001c600020031041840d5603040040c021001802e0003440e6042c0c407024413032010020360002c258144002c006800745940d0002d03005190045841c209a09600714510301c0001c032908110694500070010740040d00500c10b084d403900e41c044c0555001c180c1c0e0314010450700010400280007140803c203c5103041d128000281512001c442d4030300d80c910b034000701d800860022840740e45160b42e00c21860300b40f1900200b0024500f43d503a0300148055440d0b46040b40002c2c44c000051046007450f4018851940c07050f03858034181440011003448074091000900c900150100703d0340c0100d80f1070050b4030300503d048002042076585801009203d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 255549433 1250 255548183 255548197
    0x30b091f1d0613050408070b10150f08070801050604051e090103080a09140a27050a020406030e0307030c0209040303090c030303050a0b010c0b1605070b090d1706010e040207150908 79
    0x18111000300d100e0019490003105d12031503009007030314038081d00c503520044000f801501417600d843c00380b4004140b640c4004080704c0220344681324240c10340c80280b00240002d00042030707a001c006445004011540fa01c809450560710f003100c0152aa1000000003500c2060b10101c1507071000003c0000828031203810024003850b503140d503410248684070b04a101110300d05030003141c6c0240c100e6008010500c3d41485150640034920b40e0101d014040036100c1055820036202003807910750001b020021f1641602c2290581105c04001c1d50400c009500d014040007452400030b8040d00301e0500143c105407088d1b12060f1202e510445607072070a0b8590a0060040c0021605441828942821003045602943c841d14030306038440c0c10a00d203942c0c0c09070002e0a00600e0300784035042c028148000b50008030101c012610411020f401800304191a0800402c0303048191803602603040b100d010700c000da0340c0c0080703035403c11076040e1405642c1c1e10a03858421010700034511009481c41c80c1c170000004021444c0010098 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 255550683 1250 255549433 255549439
    0x703051306030203040309170c150a090509090a0305030601051b28020307050f06090307081506090408033d090e0f19020303040807030507080706030b091f1d06 70
    0x1031070348664040c0c0491100382c4c3c028003c20081e800421142c4440c242d4403440f94104801e40e000c02c04020003050203c04020030b41d025045001ca5403c0805510844110080c1307001c540c000d001d4146400c48580754074a5240c040d040140007c00510564000c4d000c03100032050702020341d0480340d54441d60b0394540c9841100d4240c80a201030100b80e8a50400302400e10032500200680541d9141170100300c0c2c010080c50680760820030070300807400aa60306001c1070006000c00380240c91214903042e0000302041000f082d01c0c0c41111044107020100d80030380140c0c0e5010070010380071401259078200802270741080e0382050f0000b0b604040305445011540c2c0300801144e006a100b840301c1c82c0107031407158541c5092050340a90741d00c07114450600c41587c0610001c1140040d0a0b00d241c5504d40510505101d11034009a07082c1d03100b440e040250910400c5800d00401d8a440c00304036180894002454080d0090000c01d1201c6400015171802174030507035401c0c0241180800030341255041c9096201101c0c0465501c1d03c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 255551933 1250 255550683 255550717
    0x4120c0b010602010219080c0a0305220b01171501060f0504030602030109021201080d0e06071b030503180105180603060112020a030e070b0406020309190305030a0c061b050301050d03030b0303070305 87
    0xb8485002e255400d008010303c0d44114200b2422100c1103005110082c42c18080b02421241c4133554441004000041d50141180e000d003581000b40304548201c810000d9074295208031803601b0749041c1c60b400f56056410794a0046041d000b1140229120f009681001e40b0300d5100200000d445025640204a115600c0b001e5085680e138498869454140320703191900401c40320100b060381c13403901000030b10a0910583e02c092a50952220a480016140d0412180e6074000106006580d04035501112110403d103011443c041203001c40c3e14209482e096420300401c8048040340c810ba004078010106030301c100300115252000d1040080191130742c5100d0700c501c0c0c0550240840d0007000c6d001154203031407203600103501c0e00c803049051200214800d4000403401451140220010390140010602c100141da00e90700404500e04250703046803441511070424940c860380f021007181d000760079a41118800c40b5105a14036040c28150058000e1050b445c1c0d250100007015000c258011015008040e04a01c1e111 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 255553183 1250 255551933 255551977
    0x40c0e0a02091e09060307062f0708010b1e0604030609030201090b2e08300a0c020411090d06050613060f0e10060509060a260405010509011404120c0b0106020102 71
    0x903407508070a000d21000910454804900e40c030707034120000c0035151000005850180f00c5c09c0c2203810310016410040d0165142e014180880c544141d24030103000060003214031421024002900501c0f035440014825500da45440c010b140c003c3d07101d895481d400001400316490410100e4217903560404440c16802d1318195200c04000c7c1d680c000d101901d501500070104208200070840401e110312100103240d10300c161000c00302e403500c100602011400340e120700300b0145d4244100310a0300d40b01c91107050800c00c2400481c84954420b40c0340316500340c10100016081d19100d01040384803041c61645029036003003140005911020f4101e81007114000d4400508a443e46030442d006020940300300030014100340700d4600140340800040c1101081400c04420009600114207107210031281840041a0342d03000304424014207015040d440444000200980d4024400060039184d014201601b40100805401c900c6402403074108003440e0441d00c1c025141d070350780744024044d610146100e251194140004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 255554433 1250 255553183 255553189
    0x601030c03151e0f0306060602071208031b1e09030606090f0f0c0706050108010b012304141908030706060f06050423090c070303060806040c0e0a02091e0906 69
    0x740ba03007009100080410b182c18026040c0802420190040039200d00000412180030400c15004505c1900701041c00c03031900c1406410b02c60254000000b0002c030031060700014141c00212940604161154410003c4035500b0390102d008070003982c0d0742d0022071401803541c3c008540c00790400000c114116031607655090144207680340140c40314219003c241c1c01003204c1d0540300c1c2e4415805221400101d08002003602d422060350000c0e8040e540c00d95448a0000b06542d00501c0101594800e0101c1c0b100081c0025031904144124800c491280220313040c0011540e03180749581038800c10302030300c40c4102c1e0b4699060a8403030b4011358049030264070f09927000614078407141007441211043c0d00c406041c685003002d02d442c0c46410562921a003402d01014007015034070400c000780104000b02c0a00d44038006032501400700c400300e4000b6110b0351322902c20000043c003291610b03012303580d01c00d0380b000480d121103000f00c0c0640120700700d5640c0140140400c46001000c2400015444000c43c3c41411544980c0c1c28 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 255555683 1250 255554433 255554441
    0x30c03120b120114060d05030703391e0305031b04030602032811040302060a030f090c05011d10050c0f060f101205060a050714070803070f111f0b06070b0601030c03 72
    0x6c01402a001880f0300000b0174080c50340b400340b0b405921042c44403030703006426003e810769006100c03102010035001c1e2001131012008904a0480c0744404260f110403203514040d240d404002c0540b0008480d0465004840a00d8029900195800201951242407006040b9401c401031410000c102030740c4444a440c40e00c0078040c0d296000c0700c07000351502d042c1c00c6409000341a03120300d10318010b15440301500c201449407441030111503801560200800c609140004100a201500409100038000d8003145a907a039480900c094610718104103554083c2c0780719032810045200c0315070b0788034001c440070440303010110003c4078407549000f0401240151540c0001555258143c0e02a1107030f4809030001e111107100d0340c405a0450b401e03040c15024640d008026107200d6008007800c1322080800300500c00b10366049001140c0280144c14059021103140070860b6594070b042d642d1009204c1c0f0b00c2640c10441030564803c1c0007581e4040e05a9644240904021001c0c0106407121800a0300e4812a42d0029102e442 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 255556933 1250 255555683 255555709
    0x7080111072d0f0c150203040602060c03071403090a0201020111120601080a0f020d0b0901080703020315100e0c130503061b0702130212010e0c07030c03120b12011406 73
    0x40024186030350490301120400c480c141c40320750b0942c4140d20303000300320344664089a42e4460a005504141040e0503007010b00f80d4240400103652007884180040741d000304006a004a210701c10507140e0799620350807140350070080c1031354900e000c001041c0b100060010440c034131124000c0e002800641960034450220344210381c0072600700905400882e84542c852081c00384c00003810300010481030000c081407022640900e030b0440b00241c0d2003024184c1800e08002d4140100405c00203019042d10f990003007070b103e0000c030701071801c0c1715100b100245c0c2110144107402d01402401180b4176070380c6040400200c95134450ba1000301c4014111100042c1c5150000d0300341d01c5681110490080602030030b0a01c426074210180480e880340011140b16503a084910103007440400c40d02e20800c032545040c00f120355070b280103010300c0d040c0c070000c00203034000c6504514081c074a660b0520304015503034000c0d82040001c00740c520006501280078801c541414805401207a00c1a00304140c5000c00c5d15598100514003403510 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 255558183 1250 255556933 255556943
    0x40609150501110307030e030c101121090f01020106090c0e0406080f0a0f0602070f030c0203150c041205010b03030304080405090c04060219030e0325050a12030c05070b0c01060e070201021201050f0a170708011107 93
    0x2c1586400d04014140e03b40c1c003101800003040007611240c01609503400021070078001850580c242d00c5a107000c1c000c00740100051009040121141e031042034441c40f40d100050003501d640d80e4244200680b075811070f06050380101d0451003a0b1010b02c0c004001411f032030b0040c1c0c0b080c440c5a07071200b0076604920f20395000b45000c1002d1464213192502d421412240d100c000d4032107569070000d41d8110345080c4021481288503400841d074031401c0c08200b0004100241100c00c602c103003444203201e41600054000306d40280030b40b01c41c880c40d203980f908a503003182e4018016010700905554040f2104840c2c402c40800d0030301e0009030306103516102442002c0d0558032415a030800c1864204000c42e010f01c05180141d40a03000b40c0c0d4043e511f80d80d07154031960011145064070303075440f4020400b440b00c00c5040751700103030648001e5180c500c02206038141d4400c1030148500c50b0080c50141040da5480a401c0801003018541004034060801c2c81d081d00c2e036209200301d08107542007580d020042c0a980b400c031101c1607801 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 255559433 1250 255558183 255558187
    0x915060f03070918020103140708060108151e0405072a0516030c0806070c11150d1104050306010608011503050703020405040609150501110307030e030c101121 70
    0x104104011000c20310551501405049408a400c40d5107005440c0381101d04008012007000354400103003181d410014100c4480c440c80b06200451783c0c00540a900000246020703031683c3c0314540c036103034119011082c0384d80c00b8000d2030072503101c00070004140303c4006003280c04120710707503c20500b662105003203440500c010951041d1101c078080c0002c800c80d81117024104460311418580714500110a403034000f40c40000c40d031103040004000400555500c0750f03203450101e00c100d02c10396130503890b4603a0490251080454006e05403499521a060b2400b220012a09211101c0901c22540c0b450340b090040a00900401d800810210b0244e809903049810905081e82240c02c0c502d0220300404010305034804141d02044005401e0356a8040c0c480540084e00000991400404000d11090000d50160b410300103142a0b01c51400f00200650300c000c5c0d05814400c00d11101080001c2c20715000c070600c141c0c011400ca0300c41020503440b0103690303c403034070000844940d210030780d220b05100500d28031488003190003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 255560683 1250 255559433 255559441
    0xe1204030204050a0b03060903030f0a201612030b12010b0d14190b09012016080d150e070201020f040302040c02031306030506030c010e0904030509010513080303010303080915 77
    0x81548a150f004d802d21100013400d24604000a08154055a042c10a54404001d021080702c5180d1400d42041031404100200149000b00c560440c020810f6070300894000f04a00c8000e82c0300c1c40c2d800a1041d0300c03000c0c00750b20314a0b00381c001d4000c00d150f0802a000317091190000801c89414030807000310036001001e218844806036264803000802c02104422801100c88540002050708524503100340f1910190307503d840c11a07001421101c880413042211140701203100d0414242d18212147c01c9042c2469402c0e03e003240c20032a509100e44034006032104d1030f08090001000d1800c000d001540c03824001c024240d202d0b09822405e0740a541842e02464508120801c01440e2580c0010740710b0509005887c2884072150403121030411a9101b41c01084d101d17003c000340c0385030500c081d05400d002402d026080c075941c0c2000c1825030070003c000030240280028004400ea009909940013184050b10400e8242e40340d1904507221f030000e02c4124049615003011034094003000c80e007001e200000024000d090345d2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 255561933 1250 255560683 255560689
    0x110d08010821041a0c060903030f070c0b0609090c03100b150703170601030b030a050a02030d0f05041802070c080307020102100509030a1d12070f090207030f030c0201021b060a0e12040302 82
    0x88507085483c4136074041002c003180c0c0c9014004140304e8010790340a0350301c034545440030405204004103e0820001c0c49900f900000311941e01c1e90790016000d4401140580ea0a904c00c1e1074510080600360b0f1504c84d03090001070100454200c3c001c02c801c00d484040c0b010307001710380100080c015a900103012030b082e10710080001ca00346040c00d6001905240116421814501080c24121b10010566158200c00e0000b420f43c10304000140d003204162518600041c41080300801c607008900400c19000034018000d061250183c05a0314280e41000c00c0c0401c01d03079929140303a62a804554128050301803d002c503ca00c2c91140315140c441c0d11801d01640c54078030803480484004150aa4058280c440c001d8114100d07103c2d060302242e4401da07207004041003801e100910b18988075603405401d805004011500010b40e001c00345544070441420041401101202c050f80039009014442c003640012001148180c40006144c9004500310b0000b00004008249496111448007030a011410307403c00007000142 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 255563183 1250 255561933 255561959
    0x1090303030c030f020a0c06270305030604090507080a0605010501021b090403021f1a03030a02210708033d140109030c06020a021924110d0801082104 66
    0x8545483c00003610b00316420204100e03002541d10308009400001001c0801000d4407580d61044190510000d509080f424015803a01c82030310003c00304070300803003c5541600c81d0342020b00f00381e601c41c0c242c0f40f079140c840801a03550f00c10310505031640382c00e0500000b0036500119400503540b0950146400700c40c80c0d2803e018082d0300c00b078404c80851196626580b004003200d070b0b9444900e2204000072400390003070480003014503101100c592007500208488111540c0000700d8030f451424086084800145040714000c181c0034140c40036007070704400801c00c0000540e01c8041d0802e038101080d4a0503890a46140d01915071404101a000e4030b1228401d011500b4600401090140145400356034a9100d03a14640d14813900d031b10590143e84080000c004500e08080c45244050310b0803440d902e0180f0b00300c9003c0542c28410405212550300c40c40b0184818451503801c1c0c1300e08200c4084a066903482d6200814200013407060b40520f004018400c100c3e142e0420300c040030b405200200a0409040c0606941c0302 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 255564433 1250 255563183 255563201
    0x140f04020c0c04050a1b26040309030f05060f01080a051f0b0301021b0606010519080c090925050c0303010b030a06080a0b01030309050d051c030204050307030b0103200109030303 78
    0xd21400b60500690303a00e6005043c0309000100010429852120341032214030f5400c40844180030311000c4042c0c09240c44005140b03080000d0f881c1082d42c1e141c50a0507203240341d03c1d400284c080c0110700b10110501c540090110b0094406a2024070780e07a83c0d50001a0700d4542c68000280301d034200b2402039003000c00074410700d13104140c0b0841c0007850307040c1e8070006802ca80c07003292a10040f0340d10750207907811000d040c401e0b551300c000207003840b030f1038090384011801c1c08024588829040c005141d02040e154291a000c0c0c4011060250101c4840c0c14031a026203440700101711401b40a440c031014594125104800703844e808a503c400950a69007090143c2d070403900010302e170140310796403290002440b44040101c6541e25015040c009283e504609000301890441e0700007d008000d804003880c00031760001440001c0e1041204008032074115110120041e1295600a60f414810804040140400000c404d41220720545036840003444407a88856a43c1401c007046011542010013040801c0c001c0d0452210 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 255565683 1250 255564433 255564457
    0x304021917010501030c0501030e19240b04060902090a0501081801061d070c0b010902070615060905010329150d02030705181203030a20031609140f0402 67
    0x2500d074480c8011800c6051002038610141c0d128001001440910400400541400e1030148501a82d0030000d9903548a80039942d56803070480940c6009112281c44c0d92191038840d04000c0300e2103441c515407039028006181c0224400d500e415000900050f02d4821a003846002410344020117141000640381e42200415281c070b440c50014650360740200a03c00c54015203444031410340c001d15007045200c808a0300801040511280b8144000481c01c5000080c0c1110361b118400740e500e404a2030050b002e092050a01da5002d04071004c04141c041e044075034070041d01c4c02079170704000141c1c00c10141c401d1601007194011800503402c8103154582420114284902d600803901890088580960012070780101c0d07448000450100301c1c2e000d074407070140c10b909001404683c8401604803001c00e01e91244001307000310741e801d90f0b200c0e5000c40104211001c100b007505540c65882e202c1c509615010500920b460800d400141020004564103251181203011060080c00020004100509000081d4481ba0207061 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 255566933 1250 255565683 255565729
    0x3023a090902030403050a081e040b070c020a03030801060e0609090a0902010219060c08010503010e1e0a0f0624150c08160c0305011d030f1303050304030f0210090506030402 76
    0x801e80190700003507008510a603240b594621444c10b0042181d4000381c6503d20304011032892110b18903440c241e443c1c100d5003023003401c409034450311429038440b2480e80c00250040d9801600100f8142c204c0303a01070484410742c035080700007101502040003e01c1102c1103a43e004001e00f02080c00400395a1064101503c1030040310000510316560880c00703611507000b1136400e900c80b01c8110710681c1c400e2480e8010f002c05c4c2c0090000d000341e00f110310348905400707100031011031902001c902e01c00300800070541100d4000ca05581c003603c0310b0a0840c054500c80c03084004041904090031408442c081d018800c588003400903101058520800300d8015004007000d4405a80c10300c47c00c40098000c0b00c124512600c5692031048191943c6409401d45060b4904020180c188400c52845040084200c65201130103841081d41e50003a81c1d8201d04503505e907000a80103120106000c010031000d28000403805001301c4070040591424a0219004000d0380103054201c0d0090000c01c0c01400c1880d64082182c4040c81c40d84 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 255568183 1250 255566933 255566939
    0x7060210020906130806220506040f0201021002040617061203071b03080a020a0203010c05030618040602070606150e06090a0b0d09080d091112030f03071e03060303023a09 75
    0x5034021206411403a046e400c0f010510049440c0c103a62880480100d585505040145403261500c0c1e003401400a0807400740690300008581c400d02000a4100b10380b0f60454450741c031820300a0400c10302d01c000d40140180e6402181c102c0c9414007a03504003104d8100250b01d8001903a403042c85c01807d882514800288203200840082c40394006483d40010650041c40d542106004041c02d4030303002004c2d107090003810403e20100c0d4072608096641a4111107100417503403a507240040092080410180c02c0500c0c4c888007040d80025108040c80c0c00d0320f16a508100c000d00781c0100802880b811824031341c404000c0400704010600d1002502d5501c17000c03440020400742a0b1150101035000302c0343c114000d603030707401481e080043c80f81d441034520301d0545440c0b0000542001c82596441403580c580030088012000a403100e100f4004c4500d4014414007466564090303081c05005800d5a000c01c40141c0a05610340c5064202c060600a0040c03810152602d402c8600c1c0130703031750b000049008000c04c100c0001008 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 255569433 1250 255568183 255568207
    0x2040504570302030702060a09020a0506070525030c0b041d0a020c060103030e13150311030f011406100f0e04110c1905070b181c02090702070e0907060210020906 71
    0x70054006510050fa8900d00134400a00f0100018280124030385401240c50150315055040015500701386c0381d503a41d4180a0408030b1401c10030807030b4040d000140c22405410040032101c4801100d114910135251191150351080c000d0055000314010310300c804030b40755084591500400c0c0c00003000e400051070420109083d6080c41c000760001ea005c01d9850030b0050203070421018400e10301d00071620810001e1074a80449401208130303c40940f010782610440c4400395010f02c0b11003514040007008008107246640c41c030040190841e502ea208800000340c2080e118041c3c50060140f01182c0d07107424406414030200002030141c900c086162301c03414024014110b204001400c0000701c0070507000704045103440c01e5482c140301500044c034038201c14442407904130729417504588901003c0354a0349030f440080b10700008540d080c1d1400796101c0255401d00540ca138010442d40c055407400c05502d400c59940c0186145d030b5560b00d01c10f400042c2d11000c284003e0b03c045601401e0000401400c25180070301000310 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 255570683 1250 255569433 255569591
    0x50415020712020f0304030507090c0504080604120311030402030d0804140f07081c09231003020901080130140f030a080a05010302060405060d061802040504 69
    0x2044074450702c50140920030a40401038450401511070045103000e05642c5c41e1502c034126480f500501c40d032503503070340015240101c0c01e441c040e03c440340c00ca070054030700341c14805085002c80c003a0002103072402400d04449105001160320654003d0000c0ca1b1402c00c0300811105a80020010344400c51002161000303403209110328020560010014011281441d501c541040ca4401700f2400c0d00408084841c1c0c801c0d0080021800c03121030040700e03610422800e40c844080394007480784582c0814802d221103079554155000d0861440c007a44c8076499680c9641c003100c403e52a082c005241d0f01c28031812402503a90701c5061804403403191400004418842c00b016207010910803001d0910f810110780e03081183d50186502d5401030600d031040c800c41d451034012958a1045005041c010900001c02e0b00c1da08100c2d4219900074170616040326600d02045800f64025001401500d00c550706000d2031440d4036100180250b12006070522004007030103046500c9251802c0281c1c0c600550300154040201c0c0811046 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 255571933 1250 255570683 255570697
    0x50a18060e030616171008100504030e0306010e010504021305180106020f0303070f032a05030a06140906040b0a031203060f1e0303030c05070c0f08060105011d0405041502 75
    0x7600808085a94201420000003c03c076425590001d207403080e00c2e6501981034481e92204c6103ca03800358a40c034035500100325150304151032038450700e58000d041c50080d6220710b00c61400780d583d56284510880403d51100e07030a1040e46504091100103204626155006000b28a11305c01c1d00903487e613650740400c04050b080800618142c410200400c140340d018042036218450950203180b940c07a000b00040d00003012030340c19004142e59465121051004800ea0204d000c0d40d04c1641c1513110044500241290f00480d812140d160600c0030002d01f200c030010300084c500c1c07002000c8503225503d1900b88001040c4030812140d0102c07000d000000854205801111002d000741c0e000304155041140380703920000c0750350050440d1903000809025100c5108803076016240c2c10701d0040f40311684804c0031601e90140d140040c0c9103180620000614081060010080f0b44002c001d079951680d903407006540c00300c02448900311200c200030180031070b8a4507511030740d4440e21444500c410115051140001c03604445 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 255573183 1250 255571933 255571937
    0x50c030403020c1f0503180303090a110307080604060902030a08040e061e0f010309050c1e03010c0203091e04290a050a180513061811060304080406050a1806 69
    0x8188018150305002d9220040d400f9540340111403581c824040d4000c0020a8442c10820080701091084002610020500c511081200d4403801d00340d252075100c40480c88212000c0014450144284c240464910105c0e49100007030000c954072605c42d1806002c0f000c0080340e1601622001e140002e8000d806000a08182c038103001a5142103014414103840d81100c2000e002210003042d84155100800c2050704a400c5c60042036450140ca025460040c005071f48907408860446d0002d00d04840c1c04080700c20342c0e402c80c004c0c131134080b903114180c2e00c03449120301c2e05070010100329081c034070035480104000a000c8041c01c00580d5680c05240303407404d0b101c8048200c402c0299200d601c0711503e01303042c005c0040c0004550040d55607180c181410840b4140e180103d500c00c1d160800119500ca0b803c1c45806031075006202030000d6488005460258030410108540c0c42c00015645102c5040190a40340302d9a84420520b282908080003502d4682004209008108003c0300f0b02000c034111500d900001c207416 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 255574433 1250 255573183 255573187
    0x20d0c0e0103110d0f03030b0a091802010201140c041502030d0609020405101706012610081903050406120933022d1207080a05061e061c050c 62
    0x103291084031001c1e400c2d0003501c40d1100c00315135004686a21400392819906040000f80c107060900883c00c10300d410f41c0554542407510082c5c4418800f04c0354100c410b140b00368000c12006001084414040300292400782d00311205000c02d2200001400000203a10702c50f0041307034284030130070f10390100380ca5076078014040b81c980114041116007062051549a5010b605003c443c0c80781561900c41317841e50003000340c0e040020b0110710100030003030224912070004072103199440034602100c6846082c8050f01c56007140344201042d1200d1005403d089984107980340e42c1e018503040c0f61001c100e40ca4107000315044c1107140d0381c1d0900e0000506216128000300c0c20b030303203003400030880701069190700511384044047e9a900400521102aa0b4a280d44030300b00d100444800c080e110321482c03c0890b02408281f804140d081505000c8a80d8200f460700d40316a450400c1406140c0e118030500451100d44020445420007440b5540c40914037240902200e4502040404804008403184030a480081d070b4078110603140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 255575539 1106 255574433 255574439
    0x50607080a0e15040309060206010303050a0815030604050706030608160506070f080a020f06060a12030e12011109090f06060414030a06020a02160503060919020d0c0e01 74
    0x611022101400da040c03081c0c0c1ea41d000f05690a4012400714080041e4603031001410030f0680b6416a501420a050302d0000d50b00030401800c5a80114680f1000e080c160310104500c0d8411030081005211a5107414800380855415030051110b80c1c100256800000759454031043c201d400680c0c480c0e944104505000302040c94001004140c607800013500f80300103900144190300d1503104800e8500eaa00d1302e000b040360070600c0d4414800c1e5400c2003e40c0c2c502203030080226034003075840601404032001000201d40d08450119400c080000340c04940d44101d070518141003035000d101d4025a8419051200009100340620b00c02e142c1858074000c03040c0510b071801d000240c00700c0c1d441a01551200742c4904c021751a0590429040e45440c100d89000501e4500020298001c20407180a13207100782400c072209821382c0010320280d8010390480c040d04001411001d24500600c5051554465941 = true := by decide +kernel

theorem cover : BRFrame.Cov 255395683 255575539 := by
  have h0 := BRFrame.cov_init 255395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 255395683 ≤ n) (h2 : n < 255575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
