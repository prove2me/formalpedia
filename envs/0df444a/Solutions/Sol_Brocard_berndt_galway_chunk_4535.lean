-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4535
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:55:36.272342+00:00
-- url     : https://prove2.me/submissions/a5227239-6a0b-49d1-bd48-85ddc1d2f9d2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 815467625 ≤ n < 815647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 815468875 1250 815467625 815467633
    0x60609031101030515090c0f03090717030c100513050616080901230a02040b0a09150c03050304120e030a0807020a050303030c0435030a031a0a050103020c0a06060305 73
    0x40e508011280c5084101a181050706000402403418500405000c001d00291680c03941940e5520358174075140101c00d010703469028000107000c241480090240151218860038003111080c1c410125500c0c440c000c000c2c3c1c0107800a407050382000c6003a81c8100d500444038450807400c90320540d12a410300001700c4032080c0301105040341554181d4450501c5500c189203100802447c500003403918042d88001582c52040070f901c0d40040c0c18400540c05440040202d40f62854880060b00800750556400707000388622405003040c40041523120343d480007031090701743d2241803854130f40e5110303992156a188804014032600c1d0508902d503480c01c018240000f4010f1280d252200e10314070401c4540c810301d41c8070500c01d5006005001c1e150100b08100d5048410010354081100042003202001081602d85501151040c111071001c1d540048020004c0503015581008103a648900c80820585044461900481d01490074030442d4042e81c001c0416201c8201110007a040558886060780c155030000c03111900 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 815470125 1250 815468875 815468879
    0x702101113053109060603030f1112030411030c13020c1b1c14150114010206040c120512030414060703020f09090402181f0f05030c01050f0409060609 66
    0x410769494400ba00049408988010160100350030080540c144500d055140611142e0b440420fa403241c80626072210303082c40302540c0d80c00d0150541505500b4840810030050a0280742e00020400c0000c280b12103659a0464403aa1980d001c00030006400a03058030944c94411040ea841d80003180c600d440f08040569034201a8003010306000030b0142c42c441e080c16070440341c00c0e25540c1120305007003c4a228840c000c60542820305000e00680031103004000e0060501031014070922610050598041040c3c0e40c0c4c82525183c01280d40d400103d50181200968000c18400300201d2010492000d01600031602d4000da07035420464182d100791800c5401c0c030000910343c1c40050052141e5980700d50242421420b0205009038020940320b40120700384100c0c180c00000d17045507240d520a40101150310314050103403800c0c0c2c10880243c82800e454510308120400009084148180c540096641c00780103020241c003080c0041d103694020000c0d00c002c40d0818080440e80c1c0c09244201c2c070040409a41d0854064 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 815471375 1250 815470125 815470147
    0xc0f01020c010b01020a1205091f0e04060e04030c17090415030215030408180109180b040e0c0a0e151002030715060308030f180f1e071d07021011 64
    0x6a43d03000050540d007100d0301105c081000440e08401c0b1070944e080455030b900c400380014402c25455003565109030051a050074426a00151020320480242e4080041d141c9406030003420400032280100040c0030035007602d0000d401e80506402c1000c4243e400d40c1001030000014003642c0c3c00d46010b50058001190800551070491220307500200200e11051950402c1d0721000380c41d01c9409409031914958001480d100d0344240001d0004201408860705284140701180c00500720058442c1d1040b420108030502035100451000c528040040081c180d0ba031a04e062801d00540081c40e032442d050709480d54050b641c6680c080e42e80c1052040d4040c55680030f083c03405114400529000a20080c506202400040d050004072a0016012410001c15a40d50340340c0141e1711050103d0980d10307000302401d1980c6910002400400d20700500035600c980c005042c00155103d04910414950140580301150441ca078194207039007016031407040e41c00f854040b0806070240c480c0890700c070911032800110421a5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 815472625 1250 815471375 815471381
    0x3060819120f1d0604050603070804110102010c0f0e0307051906031401230a050a090e0c030c10231b0c011d0f010315030b010e0c2a01020c0f01020c01 66
    0x303140079051000c102c0c000c03a40000c06681e051101101a10a03c1010206a076203800503540208001803500f580d03450440802400824107a0741141d1402102f00803500c03c0d0b0060180800e00d00c2596070300c1c41041d154880071525110219149505401242c2002c42c0c0da483d051903007241c2900000c2e4250800345071143c010200c80d2500c245003000c0f10345600501200f20500c152981110076154500d0415803505d00094800c80390f6400f82d9480350017983c2c00101d00c00c9942009501e00140c90998004254071818151101105c41c09e859100c180090303160300c41c9009071142c905030740d89000503020881c80105406543c0c0d0004020701d04030700950000892103070041200344e07911034082c40e100400205020800300c0807404c031180640b046203c1100e454580e4845d5002d0000301c2d28038005001101d5503402d02c950034400a00a40180d10302a5000502c0f1480c802e0807221140111400f100c445911464141e160944020903e5500c1d5001c00c4003000c240b80c20001c920b5610390500c0016a00d0078000e00301030071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 815473875 1250 815472625 815472653
    0x7080d08070c0b0a020706150f050a0603050c03040210120e010630120e061606051810020904090206030702160501030e060609090c090c0d05132103060819 68
    0x1c21038404034010000f0078800c001c80d0460711a02c400351700c44c03c5515100700540b80c055181c1e8000d0044250010b15250341000140480300300740d03810100280c84031400c406849040b90f000c00940010408100142012101418038040c54079002980b0900400d41c070341901d4040c3d107880c6583c2c1d102d850038080100320051940480c0c4181d8020781c1001c90058500c118031400700000382c6000d00b064101c2115034040d03400d041d10080014042c555918a90321403410b04800c1f4001640c52905e010001120307540c01030131407103c2c400c40100a045079481d4050b045e010798000301889800c151603208100042e01c0c1c01c2d010314001c0e40d15070050102e0710050030038507040b90b00940c000c5041600f805008000c044010441c1034001c401a140001640d41350314003146080d0625003031030f400242c02070030004c40ba200e980240155078040304051180d80c4900328140b00e1405810301c01b5080203400070a0100320404005260140f034040d00303002c220a0754441509040058165a8003502c00003940040b0411034106c45c0c03080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 815475125 1250 815473875 815473877
    0x9050601110d180515040906050306040c1526040204240e04080405030f070608161b0c08060c0a030e0a170c010212070c150c082707080d0807 62
    0x40c080e041ca640d4a98030401c000410041c8840815140350303c80000d49540c2c007816001d400c011051901c0340d000c81712984140309a481007803800d040881c15180128106004580040007001348038103111440804118003011003041c84070b003074002c150a0b00c14180714014004166079500e05803034540188000d6515094803011101d07461a04041420001400302c03050f100450310701001d1343e03100c0c9016015407180c2d0b084280d0604ca80340c000d0481e824000380c02402d035840d5030344490791502c80c101c051010518120f0035101241600914006d0f4909104000704050b02801c40106c407940d42c0c03c0c81c01c2c1803503400d0f00c44070141d030030000703020300c2198050140c000000c6042c4010000343d08651505c508134201e8010b050300c040030020708080601000d4055441e911101d4040f008141040000504510303c040c008407000c0c0c4a40e410240c414420307208108442e58180c455068a664481c90f008846601040105041449028004016204100705005800d207500240f080c0000c108014021280091281d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 815476375 1250 815475125 815475137
    0x30d1d16030b1504110d0203042303031603021b010e1b0a14130f140f04050730050c15160f02010509100e01030608010b01091701090203060a0609050601 67
    0x112500c0c4680d81c40300b001c00d000482000c20070b0004001d0705c240358011140e018046001c480c40c2d0450703401140903e1241c0810410130100c080300b4282e200d140c0c03c0c00540c0d90010710002e08001c03451352040c01d076031829103401803800c1394001612088a0f140244003d15a554800840d00040c00300310f09081c007080100c5000000c41d441001664100c0b15000301010b18060708803282494880b4044495100d070343ca08107202e028144082d6100600c100190240c2424041c4049020844c9110042d801150800b0250024078245100e1040c000b810300902001c0d280304499800441d40710841010300750b44500098124800024204452103101f4007556100c00010008612902c1890203e0b8a81681c40b40f11500d10140c82e000603207042c01001800e5410618544441908581c04600808010070980701080000e495032100f501700d43d00304c18024045980c40c2c0d81448505490034000e000c0b000520700200c0c00d200c159000c2801c0c80d03804e6841e40282c50700c800c0d007485459024014a64050020700c0e186c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 815477625 1250 815476375 815476379
    0x606070228060f0c0c1701091406060901051c020405090f03130e1819030513151106090a0b061f0210200304020d11040203010b22081c02030d1d16 64
    0x40b4201700d0300ca140441012581401d1136400290040070000e504140c11480c0954034510f00e07602c41104482c502d12a10140c000480c507884c207500d02064250f1003071700c1071510f812030b40d080c84020036001d03041c2c000d1840740c1003604000500420040c01140400541e910005250103100c0200404c0503102804650580b204907000c1c2c1c1000a04050700806007000c0c03080c0100d0b03410142d0f19803085948505075410340340d102003003050303940c1200d050fa101c461b9501c45441c04951085a00c84605668148007600604404804610b03940320054000303000401d5030342030301008803101759072507a034051040c05a00040d19048400700f451140c141d050300035000c0c960540c4809003c0f031030140320043c4028400d055200884043c4015940031188400e80a08119980d50f110f685014468000070007643c0d0007260306150700031100c83e00803034500315a4800300400d18054807071716461036113004002000c11440280100004c4d0211030090103d04016005140401004092540d080401700a00040b0000c600707601 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 815478875 1250 815477625 815477633
    0x70b1309050115020a150204080a08030f0a0536010e01061d040b01060503135c13090b1e070c020f060915031806010b030606070228060f0c 61
    0x744244407980311b06541c080000a0115100a0040307030001c00d900e2240380c0f4040b0402c41c001c00114020560000280c85517624840c1c014142c1c0c008039050000e00c0e00c8194500040c0401120002c85400c0c280c00d0410790390f10242181c5c0c21101030840c1c1c5001691500b808024107291103030b0054080001c4d500d400d00c18642500c40d0005a00d040c4250300c00c201c0000006401100010145501c4a07403110704c1c09000e8910b908640300c0322005070800d20043c8000c6d0001d004a0707480c0e0002645407240582594039440d0750050104c00d041c07041d0034440d0061109032450b400c0e107250344200030340d01e03100e40383d14181030400c244541c400a8203c0401210f02c507881051004898000015090781681282d43c01401084580494014001e60b0982e070307005040c500c084400c48140030042d500c204010500e0404a5401c0341da5603039251420710600704800300402c04a941030510800500c0c941e030000d0b002030a1044025502d45480c0c5500040715500b00c041d0b1801d0105075401300140c048071101d07241000f418165070321 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 815480125 1250 815478875 815478883
    0x314030c06070c080c06070206010603060510020c040507090305030c0721051b03012003150103090f1401060321020c01180b03181c09060203210702070b130905011502 73
    0x100e0083c855181c14003010803011808466040c841c820565000741081640695500d4081c02058082410040081014205420742d40c800d132956500600114140f02d040c40300500c405460013041004940c80800440c0d803c0004001003648940107010080c9010504115000e000c000000000465007030704011600015400190b0120054540407603916100000c0c014180e0140c240203412190000d0108481e640010b903100b180021045d036070003414030004404954007101b00402c2c0200e01d00014005c54150b0030035907181c0c82070800015145440e41c0300c0e40420800018001d441598400c10000c0b032035414880900c4410007030074010000380c0c0032019144641a1400740f0700010034080b00065000c3d070304401c542c0b40e80c2d00c1c000507078441d416240a20448004c4000401e03022940c01075000800a20010817541d4001d01851140341c0050140d000d5400c15102400e22030441c818030501003010052a00140303010240811071801700307840d0152180580310168803122141c0040030240c800c06801103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 815481375 1250 815480125 815480131
    0x60803030a0b2709160603090203070506070506070810030b160e1008061005121008060106050c0714040b090c040911070f080a0908030301081005161e03020708070501060314030c06 79
    0x41080f15180e40d403103083da14084075503070303400904100b02c180041c04540650141d141d003402074094600198594040c05030b94400d0001c010715030f07400704001070100c610800f82641c20003043e0008c1003040c1c1d40c0b038660000106042e0780045480c0342d803142504015802030b0b007010728010181c03008291070035035400c080c2103010000c14881c014142590110150741c800c8048645c461440003011104c1d0522040b03201c120075940c0140d840e04e124603000400d941340514140d907022901b12004280040c1070010a5080c901c0000c081c5402c41c1d03d42c420b1815903a90242440d12840740d101000b502c0340c0c41c0150312003c0c1d47c118000703001120360800924020078440d402d0380b00032503013006a0599441209000700d810b00c0981e4030840301800007100200b070482c030108041900d04a10017040c8056103c10f0140b0550381c41d04801030380031681c181c1441120300818214440c0955181c10700604084460f1030380c81e210303072000d1404c481995580c10148204040c008a45e04101200e9009500340b01c0c0304c0e404195103910107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 815482625 1250 815481375 815481439
    0x312050610021b1512011d04050c010c061413050c0111120f0c060112110f0d14030d06091e021309050c07061d0105090d05180d06060803030a0b 63
    0x20003682582c0791186894007141e03844032010b056655005050840c002c000078010700281c1f10059a50b940d898a46440e403c0c02140c00801400303001403a01d00540350b084c00c400341207429948404070b40100401c030014040c80b50804848034605007030039180843c140400000010b042c0700130840200401b1b4030004020303802d00851451184d44440340e4108410310f02407500b41034250b22544c0008140140441440f480301c8d481000341c0341081e40d0f03c504001c0c81100c01246107400039110108100030603600b040a4003905e81081c20b6034030300071000c0ca01909980c41c079009101160b884990200108001d0400d91645080b102c80c00c60501d020700d5100c41e498810b512a0b48803103916040860102008041214100342d80035408120094062100307010f0700021030000c812551821001507943c510105413101e4541a41c0d607164503060040910301c114000141d161904017080942e40e0780003c202d803060790042c02403240110780764584400e00c0804d40c1c80003100c081c00380c03d580c442800604041e404886072340d420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 815483875 1250 815482625 815482663
    0xb01090801050130050105040c140d020112022d0702131103041205040503010f06230f0d061b170c0406021b03150c0406020c030105101e0b0403031205061002 69
    0x400c42a000d20402c10701300150081d4607100034002002045084542104d0b2588009194000c1900802c4141716102c90080d0119101111a0b0042030b80c60b401040c2600d801519982c1542400f410803004e44001100c5030002017000071081d00f5481c1c91b00900810100e070200620400281d14081010b500020300700030040c5070b00102100e451070150054501070301c0041c00030880c02d501072031041d0150070b0741e1103900e81003800f00c112901c20350142c1d140f40440a802a000118641c5064140440e4510b82c241c140e03180e5a40d8a110346074101d110034441c402c1c102c01d507101c58402c808400c00101c0448040c00c1084140c004001c1005070640200d18244402101d4200d8901d91282034003082c240184920b640f090345a5481c1004956039002000d48103a60440c0e084450320304414080c142202d00a4807421440c1d59907810030016000c1d540721101004c0d0036a03140c2c210721562003c024179140c005800440105211801c01d07804481c45c0e114042d40b04c030080f9401144645201d41c040d4441821807501615000307 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 815485125 1250 815483875 815483939
    0x30e0604230a06111b0109021e04090c0e06030d1106061003020c0d030e0607020c150a090b0705100c0503010b03041205090a090203010f060905031b0316090b010908010501 75
    0x41800703071403516908002c05000044d02a84120540d9000407a141020b0030b0341031030360075807100501c5024074403a4040e1603a201c3c00284c0e0b1514010f030100d03800c0c41c3d030310607201c41000f0002241d5001020080000c007005e100241804400c1506040485100b4420042260039480c2d070b514000a506400c650107940d01001800507040440180c440d4105500c1c80d8070440c40d141003119030640c0551003102c4004103840c4192110342c130498176036060070f582d1648100700e40010320f22050420002c1c581404181070000020350b940840a44982202606442da60415045580151094020544030555a150007481c66040004840c0ca80c000900003801e540300c0a402100f20301c3c0248101c0e8408140202403480c40c0355100f01d500040d500900802040615205d0005010740c010300072102510b0000300079200310f1044c3c1c00070340c1c124040c12488940c140f04061480d040e003580044250f016002e8681c011400904000014106003407551043d0b01680c50480100141d50b0042d41102900a00000c2411100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 815486375 1250 815485125 815485193
    0x91e020a0b0903010b15070201120209030304090f0603022805010503040201050d050702070302090a02041d0c070f0813030828080112050309090c030601080c0703080118020c070312030e0604 83
    0x316042c0c5c8281c1120080c00c0c1c0501c44600d1001409105100b681d40e481d402c5408a9280140e0048031850740d05540180410b000d0100b5036000011101d0300e54500044441d07880e00015142000a00c2c10b91500c45074a80d03d150f00021000b00001034202800e1003441c1d403e080d0300084c414422114200e1000c1d90342d0010400c2c2d60720a000c184000c540041641429051082c80d848c003e50081c850b142c00119856200104030701d28041071441740c041c0114142c00c1c085a41c5408410070080b5104540c402d40410000750071a8400c91100d0103180560070f16503c418450311480d2141284048410703000e0801d045c500a8181d100c0c0c0190f0550b102e6031520083e10501e843c3c000d1460140c038100c690701c2800c180820401e40c01351005548a07140076039070300b6807584030050114a207100b58000500003d00520051001e244880490b0910540c20000103190803002d207422400c280d841d0304202c506c00241c3c090f0304003941e0316000b910b000207103180241c8140c1c00c1c156945000202403040103e24440c1c40303a5603100e45 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 815487625 1250 815486375 815486381
    0x30f020409050a03020309040b1203031f08010c020d0e0915220203040f03020601050117040602090a1805040201121416140a0f0f1e0c020a0513091e020a0b090301 71
    0x16a406801c0f55044280f51a000e5100c3e00107455050186140821305401c0b440d00c03032000c030005040e09029614544032400c0c00710411000300d10240b82400d0303480001422400910034650000340700d42c0940302c00c03541c07075071b0042620a1548481e1300c9014801705120401c0e0b0170a01c0d40359042c0d402c540e0b0390648000a004080303465135581100c461311b407001c0308110a000c48802c0380b00c41140309030b00303480c6903a88420043d99400ca00c00b07819004130400740006400075126600412102c01c00610000c4030b1561a10305600c0d9a0406200b000740a0b101c8060008558205805030402840b400f4180411480750543e502c40c10b5004001c0c40519400c1c3c0e0360031007854000d40c540d443e500e00c114802036603100c9608001c0c08040054087c440000c4501c03003618209803280785008900e41d015501140c80007128001107030741040042040e60b2006140c1c00004066940202090060010f0280405d2055840c14005450712404e0000190503015800304001681d0344600741041c0c1d5000160f194803504c80001003401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 815488875 1250 815487625 815487641
    0x1051e010e0613030c12050d110c0a080114100b180f0d0b330906120706021506030d02070e0705040f030f05010c0314011205150a0608070605030907030f0204 69
    0x1c02c00040705240710300c203820043d090320701900e00300806039515110307920045020f49000d455a00280c90102610388112828010000355104440703508189100080038905290f0103c0c0140c2e641d081652003411400400036448201d01501c1c41105141c040c01e85214801d0210710b4080811075805040345a0300d0020104d03e12102602014080c080c6240c61601c2001c20380303140503141c5508070a0805840f4a03070503040700c1b9001d0036980c0040c0101c10180f200b00303c0c020f08050b43c172600c10040703802c8c1c4440401c10100240041d90007800c0ca241002100254218064103140c0070b42c106910f0240050380016882003201c2441e290810b2130b649024040f2851301540d04122004a0300100002c1401114080426028000d9008100c041035060080d000c950310315400754008446a00100010780b460220316920700c0c011001d403005210407010f1080d070310b4000c464410703090742d8540041c80b114108204880141440d410308a01c1d50034600d000300c0e90380f1800d20000380300804174004141151995000421 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 815490125 1250 815488875 815488879
    0x906020c120702030f0c0d080a0314160f021903110304031b0504110316030e010f14160809030f030406181211070e04061a09130b0f01051e010e 63
    0x724100090101945601c1004180c0c402e2003046038074642e00001103201080d940006041c0320709000705564900d0a03401400c1880113142d80c51002c0c0c207400070710b08040d51040242c41184681030026190142500784441c00300d00031580325007202c41c2d9048030383d1410002d440e05410202420038814600600e0f46c49140c1000b8803000f0140a030007000206003407868150360040f1001d1089441c400440300180c0811a10100c60b00480002d1000d1a07006c1e034450f00c41100c00200104241d07900f40c503030800b640c0054102988141a071820016403554001c680f440c0a0320b18131b001c1400b414184181e40e5a8000d4203140f0041000000100c1c08000e2a44d1081a1007090041c0413008072089041440081d01c0035220180414402c903290250041d02265144c10368540008007445520346445450007400110440c8031910380c0c02d0745918541d40d8039141e02c0e01c80c440000e044060140c1e03501c0d20100850029243c180102103690050210395214502c81840501d0040145c00f229842401200c100c0c1100740324039 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 815491375 1250 815490125 815490133
    0x109080a03020409050705030402011e181205060105090f16050d050114040f0b0a092c03180301020306011e03090615030314070b0105360405011508030307030906020c 73
    0xc40164068000d80b04a401e2240c0400841d41e8900041c2c95a01c0115402800101c0c02c0184da100c0140100348054095035900c2e2440200c80382c6900b00d800d12041b074100d001354951400f01c4c0d0041010412400c0e0140c070303098038103001c24146200040e000080150010203200d05003000c01c0e07400c034840c6099500315030180800340100e5075a44001485454007080041c026400c001003103400c203806001d140403a1402038541c40d5680c1c9000305040003403084c0070030030301281d0984102c0304580440705003080420f01000c2c05140c1d501014032016041041084100c0e000381d0052040040c1d5a81144803c60481c04002c141000d01841540c1100146101e2030010061460150001c20302d2010f0b05031700064a10030b03111000c00c0e0040b240c1c45003076405000f80c018619000324005200c0c070700344416184042200c0c014101c40da0000488070072204003e9a04507801c0704448001c00c000c0c85400d01030000301c611800084503005080c454169124031004001b00181a1101c100104002c40e0758129500168200305803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 815492625 1250 815491375 815491387
    0x60c0a02030d1d10090b0a0905190e0f04051218030601030605070f0c050d050c10020a030b010e0f030c10020708010504121e0e0112090b070929030402060903010908 72
    0x40c00d1030181c4110f01d10f211010501042c0a410400e1594800980c141c40741d40720320340f030000c24907002d600002c00c40c010040c00680c009841e84541800000800d10080d540602030f06021104244200050202c03100c00c04260500c40450000300d40711300340c0d180743c082540c0e40303c400046007619401c40c202c040b605840b1305000041400580c1d403240303004a4040da502c1c030507040c1c1054111059241d03090094003640282e20071700011800f503001040840b44100649401c4008014000101c0e0001900310000c29140c00e2051444c4d030780718400071804c0c4422582010415140700c08281c0c1c070401600703001c0c0590b401c0c1d1414501180204910030003094010020b000c286040c0c505900c030401200d242602268850180760109212104d0400d0703880141d9a500e5102c0a07440c0c01111301c044408042c8803565aa4559200800c10900c12a031181000e034450200951800c004603500340340b580011200420800c0781c2c01e5843c2016402c41e41c01c143c040307500e00c0c2c550260300d0001e40140f04070384000300410800a14 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 815493875 1250 815492625 815492627
    0x30c0702040c140c0d110109020a12140624040207080901030b040b0a0602011416080c0a05040f09090210081315020d020a080916121b051005040503010e0714060c0a02030d 75
    0x91842d001905c0d81c1d0384945218824a03070341c281c1b941060300940c441202003045c0284003440d040000114050f0708481607070801c0300c4903681016800d0f146080407900f14000c401d0503011051210035018410788003146001920f032600d125074010305403403a04060712076807408403170b41c3c940e0881800514010000020260b0711000a8000c001c101940442c00b800b000000d0034020521051450260b41c0340c80e04101c0e9075510300031903041e6100c6c0c0001c106100091002140c0286080c1c0c048020308070f0301e0b0002403070708502d0040140c1341d44402000400c002c02c11040004481040f00782c50103555000900020b40d002c0c410488029016040d840c0048a10203d02c075032402d940040294081d200c4103041ea1090070300ea0303000040d400e0290254641c58038030213500000041c007620f903d06801d0307906111007541030340720000189803100008514001810101d0700b072000d480c0a1295000c401c4071040144102460041c0300110400309c180c0244c0314400210b07610100d014240304801c60140e008081d1030301d9490f0924 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 815495125 1250 815493875 815493883
    0xb0712060f06030b0901050405090601060503070546020d0c020a0506300606030c03060103091a0a0c1d040c090909150b040c08061318080307030e03030c0702040c140c 73
    0x180184915402c07000003501c3e00303091140502951f500805442f442e802c15405881da54405400c607130821804000c00000e41d24940f1482c0380e2108030107041c9d101c0a020b02400741094200340301e90131000d00d00c0080011100e4001554801c0003030142403c0c00c100103e400042d691503415030295801c090009550850800844200c030040c40030074100b443c0714400f80c1c004450101d42242c00c00d030001405c00203e114400140041d43d44140f0515010030000c055a5500c1440400c04000600740000401170011072600c501602e0907a0b5017618000610100d000315010b0408074400e403103400703140d4512480300d1081c441c0d0005409001c4a1205000141c40c81c80e042c5810f0a05808140060340b41c00c0c464000c034030b40350003200c40305d5040380e0302c410164a580703041152030340c80564640c440070768601d0596000440f80445581040c003403960b158491521040103804c1d508040c403460550b410400030042c1c12544401942d1059070181c0c0c00080c000007510080c1ca0428002c0d0108800301d0001c503420701c1c00c0d10005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 815496375 1250 815495125 815495141
    0x30a0b01110f0a030c020d140d020c03161e03120203040503161401031515020609010f140106050d061a2206050d0e190507170a0b0712060f0603 63
    0xc0d980140003105a40c1880d10780000a8016481e600406401030101c5c0c4500001300410303000525060810310b40399203c030794400030858031195a0700706119000700ca50701404031004000b019006084030144800c6451200d00250089201c0c1e03280d10107056004000c0448000040c55004503600f02c11120044040e640303070400d00c1010f110b482141801413a2040d003c103000121402d0541d200c011409001c01940170b8a500c194400c01501c06030000a2240082c0e009080f6004a0390050f00b080c2c14841c041034290349407138000c0d80415050480014a8a100300b4415046451924140d40c0325600181c1041c040c060700c1d804501013a0f010070000000500540007018900361038221515224400003480d113010107a0f10a900110301d0910401001031090780060711040c2c001800c3d01d0100540881032a4420a0309006440580c0840710078001903c840d00c0c0101201030400040c010a220307507a4090090100400c050200301a0318282240707003406801441c003801d4100c1350582c03115100c0b000200102082 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 815497625 1250 815496375 815496377
    0x904051e0112030f030902040b270c0901051902030403242a050703050702090a020c0d0207050607110118030302012f0403030806030304030f08040302130216060b01090902030a0b01 79
    0x500c00016110b00e100440c001c01607816100c038000700e00500016001008044401d0360000c0d200d0b01c07440309582e0f80c08100000d51850382203803061499104403241d2122001415001405802c1000003650b81c0c205040c0c944019506010704d84180b0b02c2c0108a003140035950009207025000b00452541d0209200d40555139490040d041118030030850030940e01c4007140c4060012408258541d83d1142d21420050041c0e03400782c201a0724000d4580c0c0424615202220015030b02c83c0d0200d41c1901c542d03028819001409074a100030001c0c5410308001845a1041602c010f141c88401d400030030150f40282d00000b004030b031780c030b042c00c0c2041c1d660704000e4040c0907051304008000013403201c44805003034407003000c0082401400c0040c2c10a411075900f514121406008294035103c00d000000c00110581d058150b111700c20400c5645a500e50b1050020000c81040d101c1000790040c088000e0b014a0311143c1d210160300300e03d000c41d0703000d07010700165514812a00801074041c000810400c044000d9040f0017203410003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 815498875 1250 815497625 815497681
    0x605031002160b151f20120c0303010f050108070909020711060a0f081e0f1b04080d08070f080a0b04020c191101052b0204090207030f2c06030c090405 66
    0x380817006505a12003000840d078540600c0f11503034036816201690a45490880d440fa0915001c0300030325030092100d01c44982e1002006100c10040da4030941c00030310080c01d01e102d042c10403210241401c40b6a000d051a5182e010880c0d6040c01080b62031041d0144001d0081270381c801001400800e030080e03060101c0042035002010a80e002c0100e828520919030400382c0003026101e80c0413858018201408890007249494012100c1c107907a80020700050100c40014000104560f50250480038001e161000348059130300401c030306507081005c8950044c81c00d900007500c074079a140004c00a0042240882c0c05114078078056011191a20f0261101406446119407241c00700004403420b02c42d40c2d170812040c3c0c0300c442d240200c41c01c0190720004601c279402000350403d912811302da01280c01c0380304250300041403594819049500200c140c00e509000b4405400c0185e07078480e02424072028010082d0084000000160496800105480c1c896030014020300c0a41040084201c1c0e01d42c24024041034006 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 815500125 1250 815498875 815498899
    0x9090a14010e01050604060305180f0307060e0303010501080c07140613060b06041406280c0308090601140f0102100f0501230306060f060d0507050a11010605031002160b15 75
    0x3042c0c50054101d0b10010714461030682441c0c03044007e4140034148000201c0111030501e000070051165590702c00c4800001c40d2110090704180703050b40c222085451a9400c1000180b1a0b6644180010750000390308507081d950f400d040c070b0540761203d10068a10700500920303007407002c41028152000b1082c1d0191b4001d2042001540401c144c82c8600d1040340e071450315145a410381d07810098003030421641c41640c911440000d0450903074040c02c039224001c0001d80300c500b80310105030700000515000b8a000c00240607640c10410358114008104501c548541c4440e486008075030710070070034103040d8050400180030421a1501d00c90117010b00f0b014550010400141045001301c0d400001015000020018070380c9440750400c0c00443c41030f03580056004413082004226a0030203002e042e000f08040c0d551f05170780f40359201c2c0c01051601001d1205078145d04140040190340d4000031410460042c02a00584d100030110000c4000c44c161312000780000024400c0095218404603400c0c2ca07031109030340c0d5008203c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 815501375 1250 815500125 815500139
    0xc06091a120601110a0b09010209121b2206080f010b090708190f1401050f242a03041d090312060f0612090c060a0203120c09090a1401 59
    0x10140707a500e0412426081c0002d90250304c20102d034410148540c094502d000340d0358a4100410b10102ca010380c4a81d000601e40c22075041c00c5100620b040d606401030910340f40e611402000011510709118407445041d01840c103030410700100350036588140e41007003100a0741c408286403140503501012186500c0c04142075460700340800424404d072016554000c160360341004042d5401c02c4120701e4821540d9543d08060352040901c92a0020f1100318005281589041e08020403485003103100c600650244080d120076044000383c00208442007502980c48681c9034042c400f22034181241e810161065510300320b110700011008009582c95038054110150070900f040580403030030350700d641d2170760710800020782c0f01520050856004440113000120a184090000301e4a81000e983c030000004040c0500c00328600c1008030241d007980544186080c5510490041e4607400703500c80303500912030142c00044140c22003004a54100d44024402c0129080444440005207070700c00500302240c00b8400041001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 815502625 1250 815501375 815501377
    0x160c080106140306011a040b030106050c070f0503100e0f0a0803010810110f0a020106051e01080f13021e0306180d23280320091f020a0c06091a 63
    0x8402c0a0010a0540d01e040311402c16181c8030b80f0b032000818002d02000c80c0c18001080194000c1c01c090b65019103400c110341e44c040c00c04140383c0c00180ea100000400304450780700800c945030b0f06011000c000035091a2006804d082c6082206910141c0c002c0300320807400c0042e41c001130350585200c41c0880d00004030100c11481210407054a402c1c40f25002c0c0560301028561000904400c502d91002042c0d255490010a1300a0038102e04400c0c40e8066000094072560700c0000e00f980112003078800d4605050074828450400611000a4041d21941031903401ca185047c41070340e980c020190443d14180303803050b800c100c85892080804158020205250020344c03046151620503807911241000111321481e1040c0d003540003500b18042051409410b01400341c440103048021001a2400f1644041c3c0b803186045040f982100c8924030401445110244d445006011001140c25030041c015030700000b400380c1c0b8142098200804400a00b04081450350b070007480071b01103071003102000740304441421100710b003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 815503875 1250 815502625 815502659
    0x7121202060709050d050f0607051c0b130b0a0e070807090b07020114030613020706060914040f020105030c27031903080a050c09030f030306090a0216060e03160c080106 74
    0x5101c401e0130311041c0341030064200d4043c483c01c01c40e036400601031155070800e03104455003008100e01007020042c81c09084407852544007400c400308110380d0500c00144100b4240140740c00c3e03030390380c2e14510310003a00c3d82d00301c0c10042d0568060945242c17a2a000c010182c54017210070800050108200159840c1118180c81215134140c40d10408003802c94110b542a8000a00040d8850034810030401610302610040c1070860081c240840d008d0f08001c800341c1515a034018406240880c4c20800001c03600c07014070810800d40c2480c0c250b40da601ca00000d40e05078010024040964428004001100407014512654545040e401d0303c0c012901d52085169003440e058014001c00c042000241c0307112002d51000f07074010201d0714103c0c244010031020034501058124612140c0d0b1000007401140c0c0790406030b0640c0b24030841425860702507640089000c1c4134464000500c0140c0300c02da10340a900040c070a4130281150f0980b46506203601d410300416544907485403468070b518106012620039000703080c0d204 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 815505125 1250 815503875 815503877
    0x30f0c06080f0f0916061106060111150a0207140a030e01031104060e03070305030301080601140a0b0d0b0a03080a032c1c031b030c020d021501090b03030c071212020607 74
    0x1006964805503d00c14240080282100e402582490480540f000c08400301902c03250b620750f000f82400b1030f2520b2900d07002420290500440c040790803001240082c4100c1000c02803004079266885512154010380505000109954140d84240c00c1c0f80d0800250850842c0c002d55820301030307668000055040755903051002c030104401700010321109000d0240300010031000f50072110344681d070303884407419030f0000c1c0c0041c43c0c02e8010200411500c51680c0c012160f0f01030481c4e05030803d902d040350010840c800d0980c8455142d40362000c0d0360b0700d07940b01d041c000d00a50b0464030b03043e03680c040044000c004008080c0c2e040c4540720f8503180440c140c00c1c00c510f0102e41d2550100104210204c010031080084d440b00b0302e4400300b5071030760010565040d44c10f04250119445450200c3c140c150000301030304240400116200310340c05813103101c0e1001000c0580d5070444500110000b980b0064402090035403240e41d280d80068840c075100011061859414000c4050145203045158110030104903220102694144 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 815506375 1250 815505125 815505151
    0x190e1801050f0609030a06020c01020310061107060f020a05100c02190b040303050c0708120402091e060105030c0408010501030c05012307120c020d0b0f01060203120a180c030f0c0608 80
    0x4846083c00c0c1e000308034101004040303400001c0035541e04c2c026640f0031b50312407490303940100511109882c0c111042c00a020030f42411103200382001d25040d0790b24200c1c4100c42c10455401105c1445a009004140c000342c1c00006640d10906508200c034041c1c42084d80d084010b204034100c0c180c03045224200c03000c9160740510010001d40b41e5071411005404090b1100103200c00420042e00040d8014008025103500d846801d403071842c0500400c0f441c040001d2003d48409203090280c001d41840300c204039031004c801d09190351252680c60841009000c1e0f90045032042d8a0b0038004401c1c04594040b0300c0c2101c400740d0303a005280102e50b149121503100114840c40c0d100d02440034000050300401c05001e021641d1034000c2e500e810a40005440f160740210946400615000341704000240e03080c45809031401e07000551609078a02c140c0404807000400040c01e0340d540b0000071420a8600c1c078071004058200035115141901e23030400350040c450b50002200c0c0840070110009203d801020043d2003a0119429030f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 815507625 1250 815506375 815506399
    0xf0b0a09030906030b1c06020f03010807050a0501030e15040804120614010b04180c1b080a03150f1413020a0513080105010f141f03270804031205190e180105 69
    0x102d40c1b50038a5030720031550b1503004d00c95005418079110186000702500401440350b90316040034032810300c9541d00704604243c1040b102e100060302c001503280103640260100540d5507114103010030180240c4c0c000c0307084910b0404081e001d0010b9a001a80e103110390201c1000280da075003101c1d044600c030310310500011940060308841c904034560301c540799501150410700400e01e0850b10f024003c00d11040304840005c004102c0703401c41a4075100c2c42400c290a82d00107103100c0d0800941c00c042c84580c1c4510b480c50400305800072810344030203c0002003607a40400564a0f05049003024282c0e4018400f600d0f0f504500781c0000940140c140915412100c40b1903003410580d00303019190890b010040171054020030b00300c01a1020340c0c2d590014104100032641c0008501113032400038500110380243e050040808001b02501280c00c0b901201d003180da00800700307007407007070340500940c6c840c02aa07002040340c9052825a41d40710f40c11540d12185a0011106000040024032103162060800e028070b64020050900d070b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 815508875 1250 815507625 815507659
    0x1203100e090703021e0d060c0f08090c01141c110a02211e0903010c02060405101a121915140408090f0a0305060106080106091d04030e151602030106051806010c0f0b0a09030906030b 79
    0x340781111600c81d64034900003f101c0c1080a44000e4107910759401400606524034580c1030010b01c282c8003603440207100ca04500314001da040d00456028007000c403100c0a00340c5286800004aa5003514040c0081c026030941000181d105c20089400751603a005003030f50f001c2203803114880d04050700d05907400510104010024000880d03001000c40b40306110f260001c0d8030400c50514846c0c0101e20580d5041501d211015450060780d50390644641e07400078040610000a0021060341ca988600751800040c070300094002460701e014030361000d401801200000b1401a80c0701c07144a040e5a4640c03101208184d50710201c540480d50b01600c080d5480c070b0b000108001070320586003c9041c03d0003c2808000c0d0707000f88078540d190b920001c1c40248441260000d131013181028010308004000444201000709100c9002001e03080001740748030b040002807902d020410921100100c02c0c1c80c2c00c855160302d2860031204140c010305040e1015008a0701c49070000075058480d0142907c1d04001500c0c203083e911501c44 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 815510125 1250 815508875 815508877
    0x50303070818011715040b0a0f0b0906090909070e18210f04080304030510050106020a060e120c0c0406050a14010309051203100e090703021e0d060c0f08090c0114 71
    0xb2800c0c1000007070f10301c1a40000107458114080d2049640110011844504000032102e9440032640520541c0d0010418810313240c0f807a60440700024601d80e9101607803000581180310b030140d030950010b262018891035103c0043d10001b074500d10019070105860307030412001590410840015140e0100c034065200050020076101c0c0c2004400a0a00700f2540020038183c40c0c000c3d4004074a00c0c0c1c00410200180441044130040c06903030749074204400c3d41440e00c02174031420803030b4002d8043c54845c1a81d0420010402c01e240f4442c1d84040240c0e26003c0407002c15440e0428104601d1007241400d10104261510b54201002c0302e0081140e410000d035820019000b410b00c0079002d60303c0740142c8011095140002000b14414001c0c02101c546103418915000740ba00e00c083c4c28014190f00c695400d01c01a114000c0000ca1300d03240b080b44541c043d0307221300021410703420503030010706160034100880440754015106101420858540c500e03d9a02c8a00241e503d6174040080340c00500f45040c12150407000c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 815511375 1250 815510125 815510167
    0x906090f0509180f0d030b0316061e0e0a0f0306050f0c04060c030e09040f0506160903080706021306090510050309060f060d1713080102030412120209041103010905010503030708 78
    0x5481c0740c00040e4140a08000c140da80b417901003904d1305010b81c0c0a00c0c00b030100102c68864410040001030030000e0040c5802c0070f084100403003081d40250b0140a0b80207c50b00150348200401c0c40e80100c0d21412812680d0189200480d1010300b00f10200301c082840c0700c0450b102e1100c1c1c0060504041c50804225148203482000303030b0500c51804060026501c54201281c070507030150a288545a5051404901d0440700801c100040009900c80708400c07603215032904112038000c0c21523501c4d01540d00389807000784a2420842100d16203d0400141c07286c00c5490702d000c43c4c404451400c9100900f00040e2202c0c801207400d417260b908400300044540c3c22803013102d0781003040982081104142941c45006078921901c441c4e04604012aa0284202142c0048000740807404000d40c214100742d80c03041d41e05c0b10740000740024800e88050b503a03110510f03941076071100200100148800220001c034044581d00070b0191895250502d4000319941c18000129110a940100d01614003e508981032952080701 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 815512625 1250 815511375 815511421
    0xc0f1d011206051c021203040602070b0d0219020a1209030b0c130e1807060e06030604050405030c0a0f060c0e0a030615170f0c01082e09020a0906090f0509 68
    0x41d541c040740036194901340c0c0310789000c0741d4514102000c0e6030040041d6200d160301501c88645c4108014410182d010450108803400e840c0c4140d2206000d0010b1006800b403200d120082c1d00710f0750031300300950381e0015400c2d00542c001c1184040e103e60300c51044800d05054040a0035603c8200042003c03814550002c10908142c45409158261910760152030440c013603507528052204d0000070f040440080c0450341c020300460403c052040c0301c400205050b800b00428061241d583c1c0d00000d020702100f071048031200c20104041e550944d1032441c00d1087c4030328180044c1c9841b4030f05040c0116081c06420f00b0f951001004140e00001c42c9903903500b80140c00b94000d051001424010300103507906001101d01d40c0140d1420141000e50b034921441480d040b000f9100c00c0c108000c02050000007101030146001514012800180d441400c001c8410001d080b58041e1507000d02c009003070040c003175006940034140c0728240d950f8240b0690f0341d10b101d40d480100d40142680301000c0c42c0070500310840c850103009440e200f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 815513875 1250 815512625 815512631
    0xf0c0102130816080318011d092802090a05130b09190507030603120f03230f090a02031506041d031321020f0a17010c0f1d0112 56
    0x240c01c03540326100039035000c40125403282d5030042c50524120f04000203010741ca002076041c442c4101c1580303055204040391170b05118401c403c9aa41145c45904904900006442c030421402c00501c1202c0760203882c90081410a60450380e00b0b880ea646000b1140054401003500035081d040c10b04000304c254a1500e10302e5050740d034911410650311200d0049202e18881c206c0c0d62000c450880b810025603200070b01c000704041c5092000d00004203050500c410030341240c500a1419803840350290020f00e40d40100e0b1403101d101c071a020444411102005201e162420940308964807441812691031b01c100750000e5064010074172000099004040c0c8580c0004014008101c0721003600c1ca4850383d0b02801c004464a030000110a854a05180c03003100081100720044542880c0c0484a003408c802060030003840790849404810301d41d6120751000015101401e1a00300a050101e0350b20f00820903102074a01040b4078000c0d4201c3c1c0380c010810000020728a40ea1019070307201081c011a00c0d581b01204032314990f84e0b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 815515125 1250 815513875 815513887
    0xb01032f0c01050a06050a06020105040f0809030c130b0103200a141204060902010806010c020d0b040c05060a0c0203150402130506130204030503041a0c1506030a020d0302010b120105010b0f0c0102 86
    0x200340a11809130b060000300054940c248002d100c2c4500203900f004045d6814007041c80300090450804a80701a080311030292038100150009042c550070f99890307540491080c00b9070088031013584c0828408203090700e0070050210a0b0b0450807a000011003a035aa104003440700b40c50081c05110313180361080ba40c0c51200c0c50f0003142004c194403000c0c00c2e40c00340d6500307640d030210340110358105191a811103002d0a181a04960b20750000c1c02032040c401c80103007240381c0400458108800382c15220b0240c640101004d80b503000b1010000c040c00d2600c502644a803060110060440101000003401650068060b0b206004d4100c02e00c0f020f01005030809030420184040150114054405000078520aa02031550b0728603021710420f034154058012040c4403410001c07031107404c0000031030a1040c012490740c0342c00d83e900c01c40001c5c1404000e20010b504680501b06079001c040c0d065104000828007185d5101b264901e101e0003908941c401d0003400100802007164148414065018001e4859400005440d01e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 815516375 1250 815515125 815515147
    0x1d0901031505090703231b030703080c07080106181404021e01110601060c0611030c042714010e0a05040206030703151d1b0a050d0c27090b01032f 64
    0x41c001280e407050700d42c503c0310080c101d0b440900400003680b901448010940907d100060b03100e80b803d00c401010f0000001d1201e04c0b00c502801001c0007001c1da0002088004c0d0766803c83d2086a6020071821140d07480c00d055019200c907095200d50140d6000b815202d0743d068000141da0344aa1080383c410705100e082c5600d500688020480300e80030b010b1681e15031b40503840324075000c8103036030529030f4600313038032400340704200030030034410180d030b040340c09a20000781851040c000c0c00010341c50555001410b10b0500c00e0b1a4003083c00054824100d624040703a1920302e03510001c1c02400c039202603c0089d4408002c1001c1449203200c3d400010281ca824010065101d50b6074101d500d0450380780d501191200284400c01904041d0020180302d5452460385d81442d2025500c40104684218120032012a42d5010b14510b6030384181c00c40d03240b016589402c03045106001c20750b4840c403641445a441d83c50300340050b40d03940f54420b00900079101c0e662401c5291a01d00d20f1140540308881404a0400364401d200d000154 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 815517625 1250 815516375 815516393
    0x30506121002180915150f0f18061c15080604050c09070207080706051c0f0b030c2706060f030a060e06010906170405030d020a1d0901031505090703 65
    0xc1c401070300700141e8500d00c01c20f40b0100b401c0f0604042d8818030700d040c00c01840b0303030907451450510a0100c41c0200b000d0041c82610049015280c2d00100d00d080c040f0b1036a0070142004c0040c003400c4c0e00d0810000c0710b80c808a082141742c2c45100078451900070851000c14003140c036600022104d9842540b4018090b031245941031070890300700e0b0181c0e00c56200496000c118100404030603004001803015241c51030511f50741544d074040c0c622500082010000d075918450486101c5803288203c10141444514940030b040000b521001c01c04078444d000c0c6000e10ba8042c44e210003e02c3c500d40390910300c8001c0307590402000e0210a0020049604540200292001c3c8580f01d00258032881c40ea2400103440d0b07062040d801c2405a0043c655418840b848900b17010700c68003da12035030a010080840d40c0103503100d281c46411030040041075040b860010403034508460700002c05d05020f1403200701c480541d5241d4000c00a40301c000b0b00c00035081e5144001142107a0700750360000c95006000304200c03030b20541da135a520111 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 815518875 1250 815517625 815517643
    0x80616121b18082e060509070e01031d060a0f1506080408040f121203141f18060608060d020a060518030604061406010c120e010323090d0807090603050612 68
    0x4c1a000000381e594035030040b01505088180700e1600700718460509001c00d403c10030241168052041c5142c900b07035103a210790001001841c2c43ca10075900c0340e85010115581c0c01d42504e504650b2030038812101c4c044e08491042000910160700c00403112803a200050711a00000b61040c0c8401000f0480031807261070081c000d100412881e0590300200a40f81000b0100e40c0c02030481c4000c00d410f159038420000300504402d034102031400d6056000c0c445410b001c3c0300880066102d048000513030408255101110b5205604880803501d4540c1b06a560701c0400c6044258481c0c000d511003c940b070180032780c40c811030103400c08a841c84035101c00b00c6410030000386800d404481c1100c000d40c0f40c5001d103001481d1454025002607080c28184259800ca944403640d100c3c003400b00d01c0811034441107420f5540e20941144840c040c8618005c2d40034003034000070b41045001181e40101501c5944045512a80304407a014450600c40c0c0d5640d1555080c84021030140002900280e4820030414403556840740a100d6000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 815520125 1250 815518875 815518903
    0xc1005120705040806101d0a02070b07030204051e1f02100e031903020702030c04050705071e03090f0b041203030905030a12181515080616121b1808 65
    0x622140f0f080d10755171504400070024400030b00304500402015007142c000c2000000301a110800641d40d160161000380a036910140884d0320600611103c1505a401441070750740030344800203658440a0390300c8211034440150360b00143d00700903003400c50104080758580700040384165074480240c0384080c02502c0510003c26000e80001800004c034400b5038541050034100c9080039401c02d0025000a612420120f14480c021600c810028940c58031400c1140c083d682d00030240036911900e0140c03c44101801c040803004500034240100f026800001a181103030300068009180c241008101540f60007140011400e040d00c80028500080041c0058101d000f6079640703802840d14100282d00988150034803603100761030008082c90104003000d04c0e6150000610001142a050441b602a5814031980c0621024050780c82072181d908042034040101940b0b507541d1650f19843e28860f1011030b1203005009480501c0c20a6240005008131070540d0503992010880800e01e607919041414042c0d0110520 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 815521375 1250 815520125 815520127
    0x1030b060310150815130b06040e010305060a020f0403111504140301050714070803100e070903121e080a0f020a0306080f1c110a0f0b090606030a02030c1005120705 72
    0x804810000e10818105210b11301c0c0850349800d00091070100c0c80c1403007034207500805d000c410420f4070b0507850700000c0c5501c1000c1d280c6550f0350b0340c904540d0300402003800308032200c0c0651008116a011180241c0b01d030000c001e200640342c54078541e5040009401004030f00c0d0030001c4190741080a442c0707200504001c20072800c0c4000c07058403010070075003186c0c030081080083c01174521501f90110000010f031001f095001c103030166130391980c0b45000301840703c550004121a10203000c00c644590300c1190030085a02c076038a5030760705072508042500d07200d654101400510760701410204500e1700c202c21194000c4504e00000825545032480502a039201c0d201c2c0c02e021a0b00e51004005644c2c04110359481c00351001c010344501c00e03140d0700c000c07002004541008104100307901c2c0404d6040081c84150101580548103628107295490700e00f6540c01d04846080c2d680c01014002252400c01040b444034955004010744411622607017004010420b4200f188200710081c80620100c2c0349000205000c1d840c561912 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 815522625 1250 815521375 815521379
    0x18030a0b04030e01210c09030203010e032a060604090f020405090c01020c0d11040504031803030e0901051c08030709120c080616050a1d040c170112110d0201030b060310 74
    0x742c00c0200e0514418100703d40e0200c1c0d0f00081d4030b9980306120001820344d02143c2c0d0310700010222151f21090b0406541235290800046d4a010004020701032800141e540c40c002d070040030860000c0c3c400380094030085801c00300002c0d580d0b190543c4920302d0389216a05c06003001303d03690042802c482e02102c00e00c42aa00030b0070080410340c0c041241061100341210340000422580d0360ba181d041098141c404e0145844101003410540500a01c030f00f45525080251049596800d00070420300344140d80c1800b0b204140c00108150406401c156260000442182d41c6035003550350f102860ba00040411080000580380894095481006411858002c01c992144c1314100303491075003090300c05800c80b0076628002500c0c2e1316003500002500c10b040345a00301298048160146500b9003458111680e901518004100805a8000c200d5800d0501a110501183e07a00d9a0381542003102c6e02c000907240745c0c0b50106800803403400e11089001d051040c03402040300d601c4072001c121240c000f943c050150803245481 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 815523875 1250 815522625 815522627
    0x6060f1303021f120e19030909060f0503031204062319050708040b09160e16032007020406031a0411040606080a1505090c071b051518030a0b0403 64
    0x9180a00300d820781101c0b40e14407160000c1e01004c003140034000040e440d0f0406804011040c00b8514044610a0b04040301c00b84074600100849071501940382d45920300b000201d580740c80140c100c41950005002103261060003d03e41b00c1450f0010801c4550700e459000401031a0b007002d101e442041c0041929982c42d040081c1103950744500381e0748031840c0d28640010400c42d20f9000c4203050700180c0013010b400442d00c6010401c1d04105e103940c80310180120032100050348a45007100c4910912040c2100c0c0f5601070b5001707048081d02d16000910000c804903a070160840d908070380042041501c001d2000860950303e030b0703600e17095140102d4480c0c0c210388840704100c140300e4201c102c51041d42c011101000a0b500300100541140e50107402141e206942d0710b0540b5040344da01001002902c001080d060310352a000c080703506603a0000c03204440e40b00300740c581800c0034105040c1c0c42c4103544004241081100a51151340500d03040036660618407003000001103a60b48050000d1542e00d4020400b040ea076240c01e0074 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 815525125 1250 815523875 815523889
    0x130e01090e03040b0304031427030f0606010e01020a0c0305061008070608240a03051e030f19091203080109050c0705060a020d090c09091704030f060506060f130302 72
    0x403280303084038200a11120354400c0841250161103078100210703207940baa401c00f11140d482240d88080410000608451f44100f10b121040390700400e442c0090310a6050f10a05032244800e070940d20881d40141e01248541d8080c10501d0484201031048442d6500d064490f04090a80d03070344260742ca85c0264042c0508603d00c5400305d809480640028002c061030040c000700440d0004103020964116003034500c42d20491030045414644c0c0083c0510b090b680c07a0b04066444a4141e100e43c0f1400f04030011031884200c0200990f00c5403d0483c1115090900d503066103603485000045500801c44030400110300000d103808007071035140c065038600d600c45d0304103440c1c0c1c011588040d10090050000b800110009003002504071751150803540d000d42c440c881d2141d01000f034010500c000b00174065003000810302142603801006030301c1c01034072035141003c0d0000c0000340c90710440c000940a0704011610390301058141e006031b034110744040c3c002841d2045800c0c100c003a9030072803500c20204520386c07001003055182c075032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 815526375 1250 815525125 815525129
    0x61b051b0306090f0a080f0906030405070509070207300c06050a02280204200c031305040605060f0f16120807020303130b0a18030f17070801090e0c0303130e01 70
    0x3c0040c6000316203015580d60310b2000d504000e2100700d00040b540200d18050043d6446650090b0072103480b800d1502d415a10340d1817a0003440d014607402400110414030020301382048a100340340101902c0011b035404134030461100c204a41030350580041c81e0020704030005550040c40e081d5070f56a15030f200702d02d000341085002080c040131401400d1404081c0b10050303c4400c0e119604450000e0b9020710004082800c9002c0c4002c1d01100c200030403c420060008002480e00010641c21241c0c0b0315110020041200c8090099a402c02414032194080007925401010300c00e2b2820007080c200480160f0031031043c00800c0080722014424481c0210007034014100075001a4507001170750170361034032032808031152081c040c01508541818010400280305940203000a840f009c50f0407642064904002d049142c12000410000740d41d0302c04000c00e2170717001c550355000305800d507541010380c0d20701440a0f000e0510782c8540b40540c0a07001c2d03080041c0c3e03001c0004201c00749012450070300312403808074038043c604016 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 815527625 1250 815526375 815526391
    0xc0c050607030807050a020a0b01060504031505090c0d0501020903070f1d0f060418050601030b0f09030703020303070e030f060906100b040f0524040b070204060b0a0207061b051b0306 80
    0x140040700c0060380000d0055401289031410b252695083c25040341340903040c1c9400780048003610004261a03501030f00410669008075110b44595110024120481f00202c0d0358044030b4100c0d481c10012441d081c00c900c0d0515005d80005800c080740040040d04000c0750f40c2c0020040012004c1c104660710003050143d800501b20302001304249070015034144025001000345102c1c0d90b641c441d41440c1e90511005a80b000c1c2c110048803d00e603101d242140d0200415a105890403040e040024030000000085900c82c40d03156002e1800d544801301c0c19205000c110311020350500951104401e0107004021642c4650300740701c001c00d4142800280d200c40c140d241c1d002013098007420041405032442c400198402c82d28240c5001050f00c4409101a4180d000c121502000c208001400035000e425040a0001e4a00884081014507030b1880e2400f25841440d2182000d038016010400905014003800c090b2800302d501c0a000790940c0765103207420a000303640f14840303940c803610b6405114201040748503482445c1c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 815528875 1250 815527625 815527627
    0xe222906090f07230f0c01110309071211120604210c080c1204060207030b10140d032708060705040602030d1e0e0a03140f0a050d09020603070c0c0506 66
    0x10544242d01e00d80100b030b94007409115201e03401040811140440f400e12182e60980d11409541440e01c000d0740070405507501c940c02d01c08019410100c000450b401003100c1d000400755035282203000102034005000a9658100303c1c520075610752603d0041400c044130f94030180c120b614080c982094005003020601882140145100b4031070b582111480320125004002c00341c54003442c51b0307124a003c442c4102968030740008200021466000503203a81524030441c07a9030703001c0d643c035000045004824400ea0301c00f100b904d0b4000301c9070305049681c0c460480c02031400b00040035074861300c94010801d441f0a1101c4031004501005542418040b281c0c204105181003450b1600d41a0000c0d43d81c042c078982c090740169215420760b00e019200b41d20703001e5406000300c1030050809180a1544800001505801140c4e8400320380c03401c001c80748102d0798208828003490381000b8250354111020b81242c0110010036650b520068050307640c04014500c0340b000d660740d603103407601645440b20051412364030a07802418 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 815530125 1250 815528875 815528881
    0xa050c0d1b090b0906041214070b0304150203071d1201150e06060c2805060a0207120806060a0f021e03031e152707020c03070501090e22290609 63
    0x945c100840d03040b0b0b803003002480643c002a080207624454030340d11010051191500025142488002441c420741c009e00d501010b031803400d15120309a100849012002448450340c110400103400310200c401540034001072450680e90410600312903003421681c00480310040d04025031180c2ca02117550100003941da241c14034000400341d680d106e5020081d1203441d8485600c01040005c03e820046000ba0054220b600600380221100021340c000b100a0303d1969524207407000e581e01809441d4001c02d40603021301e1800b808818100d400e613060883e03400c118050b0761a918018860044400d1500d5403080c00b865890600003409121a40681d25611200c02240c0400c11a0820204200394010042e1012581078424045000b41c110712400000f0300c021201007072084041e80010b00c81501c5034168121484c0780d464000540d0784070b0440c420542d01e00e508400142c1200c40c1002c1c2003500101040e9590589402c0d076480d45100254a164042c8510180e80045488050190300542048050f1010384d105e007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 815531375 1250 815530125 815530129
    0x10050f1203070f0813031518050d110f16060e10080c07030905041508011a060f1e04171e0303070c140d110f0708060a050c0d1b090b09 59
    0x1001c0c200b000381c881d000400d03098081c800c2c07000c21a0030840c000d140d0044515106e01e02540ca225510038490b080c50324104151181c0744004000c0031900d40c10000416000c810315808681800c080e001010503809440a2060f4000b030800c054030fa904034005e2508035107820020700a001d40380d55443c8a1040e002c100c8601801500200c4950700a1082c04503070b84c0e6440c413400c00f5602c14055a0095400034607041b00c07494000241501d110070b407101c0400902411410440035000704020540c3c85511240c100141c510408200c0c0041170181d001d00c0c0e50000c803841e201c80125054101d944907903c1c40f04400c509174880d40f005d0221810854407102090707001d241c05500c2640c2ca00006259006004045000109102044403080d01050050044500c136500505001f80507914a02030396400b0311801050003c0c40303001040003001c1c1c6030440020302c01c699400324018050600a0828001c0d50300402c8802e114440e14003030960b035186e24090140c1d07c2e08010038001c001c0c0c0c046a03c0303048921400c1c880d2500304e03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 815532625 1250 815531375 815531377
    0x4050a050c0414010201060e040312050c0901120b0415030308150103090305120415020d0c0311160201081305100e1b0916121a100c120f0c050610050f1203 68
    0x5124219100d0300c41c00103e5005030700511607608400808200f03d01044201035001880490a10214405000c2502e80b071202c419140101440d83d4003040740341d1109140c1495170742c07200340c640d400103001040b8041c0350501c54101040303035007080d000150800108052041c15840035440d040e004e2030100a20212510014002d01411030380910446014001c18248141c101004401404e0070f04e08665620003003010f00000c1070b407035154001180c24401002e0b000d24071081600d0001000d6025a0301451483c2d004441040d4018921fa029402c81441c09021940030061048500c1056070001145203c14041c1407521041c040c1056880500035442400c64072444040f03034015808000c8600050b8403080e05949800044102e64286480c1049520410700c40d0310b040f0036009810f642d42c04100c0c2c4030724401c6692030703000030780900700310340034085e00700054840d087c11800e01c00039103084801000956601428a9026210b00064117600c0409000b139107440301e083c141060046404210000003403048a850b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 815533875 1250 815532625 815532629
    0xc030408030a020d06090e07050102010207021309050f0f030403230d0305090f0f0a1109010b03010302131d0a0308132402094f05040602130602030904050a050c04 71
    0x210000071000c102c803035560f901035442d85420350600384496030701c9000c000014198034001004521070b0803000152940180b003100c1d500794028142003e100e00041a440203812582d00031191480740401d80c251030381082c0a244400c14080c809180d0f030301c0c59401c03c80f241c1703070150003200e0948031019082c004e61080060508500ba04a040115159035446407203400c2010303c555681043c0207445010308002000308014201ca84545203d140081c503036010f01400c030001340207501038510b04000603c0503141c081e0301c804d0903004200002c41c48840c10308411021a4540a010301d25902c00500c080416800c00019030b8070542d4404a2101c040341a1520f0701c0e81508030051140744d0800b104032445451280d0119002500c003c1c000c145d07542409001640e4500c803e00108095085400c00220a18214000c981031a03e4007c00c40074901400d40411b00240000717041110029800c00c00b0920454a90b11004000c11b0b494003c0c6490704c0040e02484142d8400500c2050894508410016455003840075101 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 815535125 1250 815533875 815533883
    0x7031b091e0504020f0d0c0e0708040c060516020a0e0601030501090b030709150e07090602210702011d0301150306050a14010e09030408031201150903050c0d06090f0b04050f060c0304 80
    0xd0980c543c0e00101d09500b5a03c003489401c1030400c0d036800300b0700001840c18000c07a1301da000f070800c841c3c0e1592400c990302c4500360744c018a00d074000340040020b1480340001d44040010115440c80609260707001074135004241d4011489881c048007013116960b0144200d90040c1140c04c01484440e0082c000240c85251074056009010381c1c40034401300c0300d602401d8030409007a03403240e12031090070b15100140c12040e2038420440180702c2c010000c0c022400e850746080400800d004100d0600303086a00548036081c9110200c17400120b02c0900305010b9400b40558418001c0e60040320b084c281c02c504189055400091001c24060309207a40c04545994940d840350454107000215081629024003075420762240c0da214000350711020810031240903060012030b040b10029a003070a0344030440e1106540c12041031001918580120161503282d040003c042d50140b881408001064551992541d0240c80c0403901901c0700a9503204010070402c0c100880e0040d01c8411008091514100700c0c141414031008000038 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 815536375 1250 815535125 815535131
    0x24070806060d110408010c020a12020705090727091506080c0301090c021624111c0212030a0c03060e0f16030906090b072a080a0c0507031b091e 63
    0x600c00f6003007401520301400c041c400034001d801c01c80c24001c0d51112039160940f0340c100998207011080c2d000140c018120b40d00074190b10042d90325280e0030344a480c04441455041c2440c5200c000350080c0e240b0344031015056a801c0082c4c52850450341200003041c640001041c800720303c00b4000c01001c14000e07241120b801c1e51002c00c0b1041e1480c001c0741000781a0124590035a007141020070051103846812003240301d05545600030b514030070380407250b01c0400c425040030f80e0018500301801c170709908800750b01c801c240d004961006048803a540c07541e82c002c1b40e0010880c2d9079001220315440d0b05000302c000070614504807011178185241500808040a488940c0c00943d01003020340c480e000340c0000b810190401070812040003d0306144400c0c0b0300884003c0005100e59002403454030325103042d060200703035580d000c050750f084903a245103469001c0f0740d16000780b01d040603032200011002c10495028502c0794030140070003042010304100c0c8140c01d4100d00c00c600e0911900d1085802c1450401ca03242680c02404 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 815537625 1250 815536375 815536391
    0x150603090f0f1a0112050c0402360303040306020d0e01201810080412020102161b0905340c082811060109060308040303080a0b0324070806060d 63
    0x8140a8001080060f8415445400015404810080d83c10701c035000d0741c2520505800385080008034812605512812000540b00038049481100706280e240c488400000108e801c280021b0310b1034101d07500448807540c0000d20801490414001c20701c0801d6590000d0210a10758540800410648002c00c0d5040e480810800e0301200d207101d48850f0480041d01e01030526841078002000c001e8100c5040e5a01007100036000c4d007540c4140701b00d4007085070243c8461030203040c6907105428404000030581d21540c0c1d181000c218000188203141c010445441d907000387c0e44002d80081c4a13100020202c2d042c00c100c04503040d00c45600302d04a010b1041e0b11104082d9181c0c14080150804801d840500c8100004c40025100c80c94115440765600c4036070b0422079041d030303980b03c00780402d940c0c2c00e0000030b080f10001e000400009016240701a00801e0400c80410030220560211786030144070b4403404a6051003c0220151814101c00b903a04641540b50001041c54107402280705440b0f03140062444039660404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 815538875 1250 815537625 815537633
    0x403050726070b01031a090c0607020f1903050d110303012d0806180a0c0303110a0501050c03060109090c0e01050a0c050613060c0804030c03030203060a1701150603090f0f 75
    0x80c1d040e104140a41610780e030b80c0c0d0503d40064042404110360050040c640c410582ca180b0014600c2541020024170042d411101402995000b140040b40c00c041190185001c42c1d5070040c20303018141074601c20410381459420428903020700801c0c41d0081c441c0a01e035900ca1503a000c0100e0b81900d141c0842e034450f00f0000499084aa107c3c00d41c1030348214420000407030312803004160180166041180201c0c5ca0803c4000385485e4122514014402122440c08000090052481108590007003064800c41900c0e40c4a081c04e58400319034001d1541c100204101480d0380001f00400a00b03529001040b1070800b03641b024180c00391003891181030020200301d442039640f00c4c41c01d4000040d488010307110725003410485c100004000b0031084900c0c41c201030356280b215220700000c0340702c0c580540d1040000d0466840c1540250301c080e01d19030b0055a002c0020540c90040d16070403518503501c400008515048403164010014141c004004140c00c05040300013164002442e00c1510b0340100040e007640041d850 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 815540125 1250 815538875 815538923
    0x402011b05060a0c020f0309030a0605100e2d0618101e030203070504020a09060809031306050703090602010b240c070f09050906102c1303021504030507 67
    0x4010107070701c01c00040150465468000750684602c6400311134810740e04001e00b5440780981c0f40b44e103406a02c10b854480200729503030041500030001450100c01d05480d5103071120020030848841d8540400c180c4442401d5000341c0000f4422081e801200070681403560018980012032039480e2080695140401c0400c48401c5000b4010b080c80440e900d4002c0c03054850003180c4c21648001d0380300e40144d41000510341024022180c000c5400c2d911000c1c0e00e82000000d4a030150041c140c40090321051100100d81d101080c22030001c7d1460b600d40d10307143ea103180b60082c84d04040d41c00180031a410b02c0c92034195a2283d00403501c00782a0b400440d03020314201008203205004a81c00c52015100380c07040020403400825600040d100368090a1010350b4801020039030b604825545050402e50700c50040040d450081482040c0b4016500484101e150101c00030400d86000e60300307590a10320344000101015010424044c480e04602c0200f0f51618050310083c0170390003094406059400244400785d002d0007000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 815541375 1250 815540125 815540177
    0x30b0601091404051f0602011508010525110a0303050a0506040e03031b090916091a0307030908071704090f050c091212070501021308010203040f030e0a03020603180c0612040201 78
    0x2089111450f031b648900a0180070700701d03100d01c0d0202a05c0b001050004040c05550310500c045220610f07503c1d801d0301401d44048a90703d000d001c00803c4620402e07034550500106000e80d01980e00803500f4104030307007050100d44000c0c2030303a4492441c040070841440000300940c0c0d03000d400010740e8a6144540782c6408494810034804680c0316080313074200001e49845c00009403541c4401d0b42c1341c14101c0d0703c459204842010203440242d450703105100083c0c142d442500505c81d158459030042d41030031501e0740d400300c41c0c21503003107807008500002c58144900c100510520821000030701080c0454204403003ca0790900c0340c0c020060241c1c15010301311003602d408116000e14038048074800783d5906900e040c018005d400600e802000103004480000d10144140240d9000e0303074212590480e07a810301c0e40c0583c2d064140141d82030304240b5560000002d40c0c0c0303c03409180304400d580b00e908015185070500070700b003100c1401d555110364024085032080540a01440e54000d5080c2130060782c0c00100b030714141d0210785031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 815542625 1250 815541375 815541421
    0x30f05130b0309060f040c0b070321050925030206090307080f030712030603020102060601031a0a0306021206060a0504030803090102040b0309010e0f07080d050d2004030b060109140405 81
    0x2411000540c41c245900031486624160203590300ea8075094001d80089600380c402904251003004180b044810b500700501006200b420301c1c6e001607650b00880d00d00c800340f000b0058070307440d030f108100407981c501030110721100b0066000390f04081c5d59003070300c00441d2501070101902480c1e02042002007503d0401c550380c0500010001c0350a20300c030524149a89601800c030444200301c1524090940d02e00a00402c030599038160050400d6a481d040114010031f050051606c8841c1c10010000b00303602d0b10036400018501519000d40d40341003401c40ca0910180c0074002034000c0340108080d81c04150300209803002d40780d11038942e60b980e0300e68062060181c000c82c4c1018a0002c00001406841c440540c041400c03107407450280c3c0c0d508450024042c0d2604924407500d81c2c0c0c1e800590f16100081d00c1403006100c1900c11355400550b409003e8a101140c0503005031010008070002400e00c21700c0511720b18503600031001d10f09456860704149c04450302080c1d5031200e034019078136500070920021110340d0030302440d104 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 815543875 1250 815542625 815542657
    0x706050705150f0106180e060103181202030426060403050c1606050408011505011209061e060609080d0e0405060102030909150f03030f071103100203071701051804030f05 75
    0x700d040d540003500400e11400020610101b0003840e02100e4070758010850b00c40041880e007a65480e0b0064010b41005030b400c104a030504152440040c0b0039145801c66060701303900035030312581010305616001d079444081c099828076201511044202c0002c015078480d41c14078100d910f40e426070908614041c5201010001c02401c4ac402007a0795603ca005803023128136503402800300c00c00d480161280500c9034095103000601480e500040c0b80703503903040000745034130801c40040c2d204d2280c0c19800b04580e90300c41c44600302c0e031112402c110075940074420801a02030b18000d0000101c801d807000e003c4040c0c0b04695802a83c441d00000d100e6802130059a13409100903145c00c10301e2621189455001d402e8070061446046000c80c40002420004142e4a40c1000c602c201440d00c01c05171941d1300307115445880360350b05100b90740d0555002d00c00390010b54055410f98680c080d00b020094400300d940c2d20b05820040c01103007186a0300c10340610f0403888c40e81160b05820302c0c01111030056000c480f03500c1038084041c01c03040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 815545125 1250 815543875 815543881
    0x71209020f0114190e0418050703030503100b18030d080106080718051f03061208072315010305010b061c1d15060f0402030f04080a0201180501140c0a02070605070515 73
    0x14001d6000702205d602190204040300c900d2140e0031480224083c05016503114010a100190049006580180f001e07614403000564941d8013100c564490130f00300a0300e00f807104111100303040400840b04581d60394100079041d036040c400020041080100b40108128910000d08030126824a4240103850b024040740c0f81070721001008100003030350340351010010b4500b60b00081c15035000d21a8070b10b1190f0001c042c5150441c1070711a042030001035201107801d101071048800c00e09a0400041c0c1c1c040440d10700da03100641c1b446c2021821100c80245ea203024140c204280342d03401c16601d060a48010f1568000180c030514080c18130130340403461454040780d2041040041808072404100d52042108a074030800040085c070501c420785c0405d490484040100320081400110644081c1a210078544000100d5102c3d09000b90586101c0c001d00307841e00d03555043c40000709101a40701591245220f0079040c9020a8031600942d00c2d60305102d11010004040382d9401001b401740149000034183c4800008541 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 815546375 1250 815545125 815545127
    0xc060f0c0804050d2a1a18010e0a11010315170f06090715050a0e090f040b090105070207090e10020c0d0f03090f022701030b071209020f011419 63
    0x15000c0d20265001e214080d031401d0f519104a010700d10014121014501ca041c0001c480780450a0144040340d48040c9001c550000c2c06c01940c04910402030004801c520075211b001503030071601034407140391040d040fa4070500c01042c907403401100944c40c2071070001243e058100c1d00c113603042c0c0681c0041e003103031610820384d102c0c8000001e200f9500312410029502e42e5180d8141035a964502e0340f1230401c0c1c502d012442c04000f0350041019000b5120070741800600d1096a000084041000b2501c4030500c20028045c4000d200c03c0102031940501e500f4020481801c0c181e0b03000c1e50f6941a40b02c1d100e4520780f210203005500d40180202d419031034010704c0540d121542100d001c3d480380c003c00400000203240f44c00b8101194481c0c024403950300e8201c040103a00391500c0d02400340c42c80650072550504800310340329840450382c8850a034000c0d40941070503000d40c1000030f0300501c4542c00701c2c2c1e0642201c0c00c11040102583c0c6401e40814031803001d00309040c1d1280c8030380e000580b500890402c1283c82e400d2080c000f10003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 815547625 1250 815546375 815546387
    0x7082a0102033102040c050d1e060e070c0204050604060812040614032802040b0a03060e060604050604090218061305090a0519270609020a080303090a030c060f0c 71
    0x10f41e8140002c2c5804082d0500d40c210502586000c040b09030f500341d040740c0241c2450750001d0300c032400f070f031400519040f200106d01e0203440b04001c50109401c909810025030054134403a54028008105c2203441d6800c00000003804640703041030103849141e9400100e85995142d501000041c4043e2064a0740c41c0e402200c401d000d60803910800f4007042c0043d1910766540244800c40e0311a1203500a00d8055400000c3c880036014042c08c01c0002565003000086100c5d00320801500010429940110301181030001d03440c03c50101400160241c02d09000a000e5540c40e80159000c0e2505082d0058480d4208078031703c140c0d1074000c030055030071001c00036510044121041a500507100d040d038006084c0c0d15291010022598201c50621055a0915036044016510741010031103282d40c50b07003a0509604458500711034017840c001240c00759503482400c2c007103041052801d8000c1071860041c50841c81c242000c0d684a01103044020204607075401c10800b0800280e000c05194044c5010400040c1841e49001e014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 815548875 1250 815547625 815547631
    0x151419050301080c0102060415020d060512011517031608090d0812150a030209090a0204020315031009080702090417030109021b060103030905060a030905010e0604120203040b07082a010203 83
    0x25010b80c1396600c143d07500009000340516882400c005142c011900c05034000d400c03461512400b1a15084001210741c1c0780910108c00307c02c070400000f0b8075010352801e203810303004a61222a1001040c84c41444201006c000e480201004e100e41c0c10301c51010b85042c80c2d1030300c120103605600201c0b5030010414040098007030301c0b14011180d69820140c442e810960003180c00c440c42d19a000e120110284014205245c05680003001d10080b04d490003299400135060741c2048030740b240001000d180c0028540707401c00200241c0b08030707040100b000407059103a20031580324413000603008610b100003090820000320803803410902004102034583d61240c400d600039501404018070340311071103846880111004100d0504890b07040e1a0301000e28584401e020107a001030b40c2980c1890b81e510700c0500810800e010b403032201020a006480c0c1498a482e0014040380090343c003c0866005000c00d02c29044060111540690040612601c5001140b50900361001000445c1c0340904905210442c0340c50540113140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 815550125 1250 815548875 815548889
    0xc0f030d0c081506040b0702010509150a02070501050403020d1713030f0308150a142d150f030106031d19060e0f06010b07061508060907060504151419050301 69
    0x85503100ea00d0a5050f07043e200b15090f9102c0000c1104102c1e070140c50004111162060420908040a200000d03450350000751210844046c0024180611036050090f04058542420038508140c01e43e000318048000031200103111800120445290010380d40907240040b0300000d0ba894a2a02e0b880c0c10182580800d4007100400d150314049641c9102280125060b800003400e42210945003c1c482c511100301c0700c42c00c3e41c0200700400703034444182031104000d0013903080300f950010092091302032003408180e0305017065034048180110038014544c4000c44e8111400c034540810440880442203545841308840d4840500c503240c1403a000046194450b16103d0003401d04100050700100116101c038402e2103820659003003240140840030703054025042a034014000001c850000400c0300f41c9903511f9402400c0c45900c5a0108003800381c0400c000006401c0515100d4240361815140602180c0c0040c41c0390284104585801071820a40d07040d0351fa060000500422850001e1601506551003801220 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 815551375 1250 815550125 815550137
    0x3090a170c1207020d02041104052e0f0219080d14090601050402090315040c0509070c0605060d0b0118110d02070501200319090203030a2a020105030c0c0f030d0c 71
    0x841071000300c400d94490f2500680aa0202451036003000000c00b6a60346801810b40107000100d20781d140c000012580c2c0c50351034903070411401501c251401c0c4e07d07800001c46040001440058030429808a000c1c00100d202c044801d84490b03c0b403038600001e003d004540007000c0e1030083c581981d9140404074a0280011200ba1261662035000340002e0384031306451320350168800b8400601000c0440031803503000d8002c04410028031b84550002d00c070a1000d54400300040c6080c0180710500406129180c7c000300c088175441035122007076848444003001403040302c0355605403204484000c061600425680c1078501b0526a580812440ca41c00035041b000060354903600c0d040d801c4500302100602c1c001c40590361401d20b81145c1d12403402480403c10031110b034ac0c1082d152561100140c80070005031810748225201d500c0c101c07291564800411550b80c489520380400c218480c0050307604202100e0b0010a601042c9644136503000d61a403602c601842c41d01e20703d100c0000d940c14a80515404100d940d891940e0342 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 815552625 1250 815551375 815551393
    0x10c080d09083f01060e010207081b090703050108100c020f010c02061f0308030a0b01090803030103050d03050906280b0d0f17030c0313021c030914010306140603090a170c 75
    0x42c444a00d504000d01154090f00801400340a02840c61070402060510403180070076211001507080c03545800004041440f825900b50035403620203945da0f4005c5840c9000c01896261500c420342e9848040c40318141580ea035194102d00314400c0c0441c2c008040c0681c002e1001401e900c4c8000e540b130000b225640c3c401d1001c03400600c203410f07a1945940032680c00c13550241c00c41c0c441043c01d01c0140100071120707043c82140302c400110503100780080c60017940240050304d80840031101c0a001d40b40010100c400b00c0c0c11140800242003106a02000a011984d156400740008207044074000c140403440d0030b41c0803500041c07260811403107450500720b5502c80c030b644848642e0071203000b5246010540f14642d004000707200140e000701c1c20781c000c40c048074001010000031240781110540005610482540012003046c003d00c034100740324405604680302842c0800c1028580042c5021600e155200313544142000404035030524003c001102580e07030400c4a0400e0300d00c84e414400c6050b40300d5090311215000e04458 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 815553875 1250 815552625 815552707
    0x200a060615050405040e0a050a0b01080d0f0f0e120a290402100e0612070309030311090a050d081306050a0806041505091e070507110d02010c080d0908 66
    0x1001e240390007903198a0f0600b4200340800015000b98001030515108440312480461020042d070075026000f0486034456506008000c0c6c00d00c29142d0b81d1109000da49803030031204560000000030400c0d00741c5414a400452100007440e010140348000001e84101030041050001f402c401c00c018041450210b111710701d0185480420480845000e5400103481064001d064000e00103c40e440700011701551602c45049089500c0c044142c40c0c0b5070000303035502071500416806202d51400014020b074428280039100e0300080c5031103028060280920918441c59081150300000e0b82c0c110b000900407e07008a441c1d0100610580140380407000003150032002c6040c80c1032910491740301180980c811a000c50400e001d0003044d103005040b421504400700c2428544101c46a4010300031000303965038039030325061820104090700d101e0701c606200741201d8040c500185c1c4c100c42c02410b07440d4040c1c0c4c0c0603200c02c5410344000082a003000094240c00e800501c01003003035182c00b0896114400130060754030070003418003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 815555125 1250 815553875 815553899
    0x90f0603060527070c030c0210093f05070506040801230f07030e032812020913090c0e13230a11030c030a060903030c050f0f0307200a0606 61
    0x4078030683c01510404240a10b1294050981c1103000781045242c19907168042130590f690f45500c0800600381c8601484070451040030307a0010359800d0b00244d000000e4498003070030355048003084034289070644072131b404010051181d4402001c00810191f100e668a81d25140078050072814015642c01c043d083c101241075201000307011307a41c2090342020365130704c0140c260004e010b004000e00052106200001802e02003070148085001010400e801080204401902811100003c542c41130b005000e114100d88400b82e84440306a09810003148180060800681710b4540d60860458200c10341d041042c481440c02c0b219000500c16004412440428003e115800048802d00741c0190003a4044001150781001c11401c00d41c8003c041e02d4080b03041c0000240f0307081781d901d401c80d425901c64211506243e05403051081c40030860501500d13245415aa10a261194040500e0610004400f0449061107061a0000c031a0280c0400c22072421041c4011364649920004883d0740b820080081802c8c40301207 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 815556375 1250 815555125 815555179
    0xb0109030c0302130b0909010608060c090114031f080313301407062c01080c031b07030315060e0f09041a070c060b012102030601090f06030605 63
    0x441181e0400e0441e420480030014200030100355540311411120103544401e0517900585510300005201883e0040705820203c0041200325004401d025141440e40c00181c404007e220200b4056520b54810600c56600c0040c0300b800300351300e240c1c0301020880000000082c85050301444d4038410480d551302c86155280d10341001c3c4142041009101c03241d12580150303214130340d0701c104034020100c0140a007a0303240c80b6080d444400060300c050008042403c03d115036002e012a940707400218065100d002914429000d03150101000300000080c6500d1000b03119409800d51420095560f140c45040c000c01600300d007090444506490312000942c40e000d400c40c1c07644540050200240081c102c3d04201340c50b40028010b44115010307810594031890560380861107071080342c95002140d0381c6070a0100031281c541000310705000ca10040d0b04018103041c404010a82001c050159980da5180c00480720621107922020307044102c000b0100e0325a400d60010000c1d1801039910b01403000c1d98048a404d03149104d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 815557625 1250 815556375 815556383
    0x403170c0a140c010902060c1e030c0a031202160c030303051006021c0306181b1b0b090f06010602010e16300c0801051608090c09100801140a0b010903 66
    0x2c800000000d0400c9005000615043c40c000140c400940c3c001c590154040140000c003a080520b0201100485220070803d44096070000c3d07043c044a401240d1313568041c0030002c1c0510522009400540c0000c0e01160300d0f940142d8100742c80d02d0100d2410900d4401140812000f0904040000300714440740c41100b002c90396283e004018003e04002040d9141c0e603c4038405040544480300422a424518a04511f00c40d80c00030000d00c0d4482c2c2d040001e9205800c01d155000c00607a5580e07010500c1c0b111004150183d0010358145503078070380213015441c10340d42051000090203650000280c50390103610085203105020146c907400e010884c22507540d02194014a490b54808030050701e0222241c00440e00c46030604c03440182004503076140d148481c00107a00001650b912001000348641600061003211480c0341400c01c00350500b003c0071500c840742020072a0154030580c000502418490000340b000744031490003000b07d214402c074212445a800c60b004038085090003000c410300d520642d80c0c80126508 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 815558875 1250 815557625 815557637
    0x507030e0d05071a071b08010b030307112b1a07030b090a02070602090a241719020d0e01150f06050d0f0204090e030712050f1803010e03030403170c0a 66
    0x1440c002c550441950004c250000c00c0500c0600b00068540d204a000c92154001a4007180d29004096094801c1080d440f170180d0428007800c00020050b032208510703040c1c01c451000e003081c0346130001c6003082e1040a110500040f0710400c0c006000100c4071700e5090540c1c0c07031aa09129698148140c051720301e1052250f4001c01c80100040ca2103000380d01801c1030b2403042601600c4c2c03501c0c01c0001000ca9015401511003405102c00002d000c900c80c01c01e00301b0140d008d080940340080d040104030f2900750018041407040021500300c6012140c55070441c0da0316505c1040412407400c102071514000d18044020306102d46145101145040101c985a01215001d40c2e4507803070a03002c1001003000e02031100c00084e206800f4000864121114010b41252041902c01161a0b0101c0e09290294415002512080c06810410707128103034010b05c111180e03071040e00740b41c40f074015090000c40d0040a990b07080c2c4d203450002100f03010800d030f4003d000c074038a1599000c00341442e07103880c40e110b001c0b03203c2c20b00c074840450300c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 815560125 1250 815558875 815558879
    0x11040938152d0408010606020607020105070801050d1e020603070c060b03010e0325050a06091b0b0906090a170a020901171b1f020c040c02010204230d0804060507030e0d0507 76
    0x46810142c0209010845610f410241e90f580310300e0030344d241608000c0161f0003500030024281d03424410550b00030583d142102e41035241002203401c014403075001829444500e004c3d00c410301c502e48003001364141d0152000359285810710f002042c00038048401c43d6510700b080144040342c5414000c18a407207510b1070107540340541c0340500e4058004010b85d0301308884100c03820000450070500c204c128550103800c01103a442031714074114179403040024907400c00b25203808042c401d4144440640c1c001a100fa11020790302c141920000b50303000310b1540b0440f07030320480700440040401c020404105030341c07003038841e14290703601c44000e071140e05241d18200c18998007140c554115005c44c1d245600c000503000c2c11032000c8581405011342640700c0545050701581c8140d0300c800103404c00d8070030b100610203944021820641050780d2400b40010f0343c0070703079100003151840284140c1e0350402c40030030041d80003410542da01d0f0b4800e4054807541011009030007248070b90100d00307070714141507800c605000d50000190103072074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 815561375 1250 815560125 815560177
    0x905010b030f180a0609113c09010807030c06140f0703030b060a0306050306060d2103061d0f0c16030c03050f070605040212011104093815 61
    0x1c0ca00400d0900040c80d0f006034508050001d02064000d1801070502044600803401c0c400c0301604a40583c6010f040d24820814500c0103625018401030030202e81c00744078005600b00d48503241ea4003440b01380d10640703500000840c28000205038003100e10540c0c503d0401540c0361070944030450719201c4110500001c1215010080b41a401400801c0c442d08002a482d00d0a4020441d642c105d000090080382e41c030041442541303030030030805503c40e00440c1d440c0000c0ca810f544031014081010154889100c0b0003070003802c2c2a0207a00254080e004000c00100b04410321800c2c40864031042d280405418010070104104510502c202d4070408400705210103c106550b9048551200301c02c0c06a08115061041d4210610103600510300e82c2d00410700030440e030405004100e07080320139074842d00113a894100007140341c019160030754080391101240040c40d801c240401c000c48409401c0c801c1c07811203814590508031321407102000b42c2440151014507002c2000380601409106050303e040c18100c08a41ca20801 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 815562625 1250 815561375 815561401
    0x30e1203122203182601051513050a0b060310090606030506100f03140112200907260109021b070f0902070c050901090204061206030b040b09011d10060905010b03 71
    0x215200c0d080c90b01056038174a510440d81120b120110481041c84018000c0c00c0800d00420780c206004500070160704084c44005482001c1d26840c180d00c0302d0300c4200243c440e8546601040724400003900f001d41c1c914000b04450081200bd0051441c924070b4540d011407418441c0c07141c1d41c840c100143c04025124108241500c200d81c84180304030030035403154480014000502611360080414041042ea000003d142480708083c100b0001510300c01d0000b80d00380700c0da881482c041e40054103820400d0501c1105515140002da508400304411a4001c0001817070004560042090540c0072014018411035000800d071a00c881344503034079a24528510520040c06658014103106126460008089a0f11808545100b01c2648901015035021800f00301440c0c00900722101c6010381c1b10204401419541c54814410024001600c107103031040014080036025445032000c46410601421441c0321064a190356112202e5002c542a0801800242401c5c040c01150305a03129143c3ca64110756406640d9440 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 815563875 1250 815562625 815562647
    0x201080916031b0b130306090213140115051c0b0310090809010e1914060d1b020d0315120c0506040603200f0d09030e1203122203 57
    0x10300840410700c41141074080918011803107450001070000d141c103504401d00c40180d1241c00000710400c625420032107070100b400b094a41c42040041d8030641c900103d41901142c00c48119018a45050382017003045080782a8125002c00d95040b188a50b0b11000711154080c003283c18001180030864401c18658981040c200048044c04840152807131030081401d5030240017044d14050350024800d005545d00000c0d2409a8100f540e001501080407262060407035014490b4801074402e08004e080705640c0e500441c2d16003009002c092100f900100540101100c904055070050f208800f100f22116010f4040d11091540316881e2000c09440d10440c0410341d02e0f42c040c21071780c08012050204507590b4800180000d01490340d000600d04d01c101ca08281c0b50200354a800040c00c0051000c40d40c60b1400c402190300008140d100411a07041a16058031284030081d0300e15445099141ca20a030140c0000107062000311000d080400e070345442101e620200d90a1003402a144401026070740402d0040c80f004030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 815565125 1250 815563875 815563891
    0xc04080c09150612040b070c0c030f020406090501090c0905040b03300a0206090c2407020103090c090f11070317091f0c0e01080f0604090f0b0c0c060112030804020108 73
    0x3507000c51902c0015031030340c0007840300040080c20314107001c2032005020780f15500803182e041140301850305442d601041c130a2480010404025031076000c1c01c640b02c5400038401441e2281d0305010b9940c44d10401303805003600354000c00004094030000101c51416024036a501e1b00060080d0010b00180c01c00b1364192044000040e0242c4151400c1000c4401407000500b02d281c100d034064921400e04908a40c2002e00d100889071240d20b588171003540b1030320100300080301c1c2d0051121141c3c1e100c2c21480180d0103000e00000c042c2174504001c034000344503040d9402030300020f070880b03034100001103040c030f00550507000b41d02d8080e0005520401c45da40c2610b0007460740d038000c4081011960410450300a8404800005541c070700422380f1045943c02c600d030804c0b0107000365882404c00708100e1030030903c1141005402008640b00d10345440704e1b0700900031503041c1c3c421400d81109003c4902c1c40c20a04601103680203d03402e114904c6101d000040400c0c140300900340c9a130b815a14460b8a4035035400441d44000d000d03280740 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 815566375 1250 815565125 815565151
    0x90b1509060708091302040e010b0331060905011e061d060616061b0507110105030c161a0112030804110f03060915100f05120a0c0b0d050c04080c09 65
    0x1a92041d008817103c194400e000350343c490402d2019118024180d004078001c050030b10500001e85040c00064060700c0c2148041c4400d000100c20800c11101044805030000d803030180402d00344441034105035551048038040301060740104042c0d900f06c8085100c1d4144100d403c0d001250410000c4032100c4e00a00018000c078246010320f08881c20b0030341e240d5800c461441d03a504641c1c2c401c500b10707803141e81c0b03502142c00c0080c01c1030126180c41e09403214417203910b4100300c0000006011145510700342e8030040e120072802803102000d40f8000c007941c190001d441e0010a194000011241c007081404403249a040d81d03000840e071140c0d43c07850286140c0495065200c602c1c03d40200705a06c0c10003a45208210140c0242555140c002d803141c02090060090010310184807024010310b04607020300e000712102904d144008103220a011401d120008200508100400c0c0d4001031010406000d800d1001076110100419101d154650102d03100d0392182c1d5a041e000455400200d14000780c4095205504503401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 815567625 1250 815566375 815566387
    0xf0302030a060b1c060b21060f120102070302070b0702012f0102070b0f060a0f0b090a090c0509011103040f05090c12130507060201092a150f091d01050d050c0301020310090b1509060708 81
    0x303401c1d45180ac001e20000d81d030110300e0509040e410469400202806c0384981d2514503d600000c01d8580b00280c0f0284010340003071a4102e0030202045c01c0d41540082000315100e60030741c640990002c40c2a40c891003901f884101040c0b01d481e00b42d2410080b85e5403040e0a20f2000e1803c50340c034443ea040300141c03d5005541d080700003885455800741e459040c0325684c40c10380d90900f14002426600d41c68a924005610900c400d000300c010b00a00b4030140e40084407000050f607181110242248907401901040125640c24401c03918401117a107402c02d485002620540d60701c03240c0c100c0c200e8074518006400d040102c0704003980c048440b03400510b503541442c000c44d50552944000001c80e07940c014040001a50000901c486940c005a40360107040c210380d8100440121905460301d90307806000380340c82401d10007003040402c0000c0100041040d4050000e43d124a8104803244450302e1611a001c000750600d200000d4030710300420325203054a1840341041c03d0541c0d250920080c1c0d008180102d545180811607 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 815568875 1250 815567625 815567629
    0x702040f090b07030615030b03010f0c200a17070317010605130807080703080f070507080a021e1e0406050406090204090605030d0f0302030a060b1c060b21060f 70
    0x5004000014180c08a020341141c5016007800e480109901c0400d071420000340304551340000c2403040e0003103600d0041001005d41000034010a5040043c5c0c0f0014500030320300303200d590040c10140110160704004a603283d0407040f100d071503401d003150003800106900900e541108444019043d034038068901750207c40010102012907641c00e80084000c07650101c3c202081d01c18482c1803d001c2c00b072000c0130303018091501208035915906400002c19051001c180c41011b00070303103016520304980180891300380b650368143e0a030701d070600c0307610030380c000c0d101d034180305108031113200c0040300a00d07000e4000f42d1000a120300c80c000840c9540d840f103a0242d00e4020000c0d041d920b60080c1c0c400384c06481130042c0c0d0742c2d1410782c40c80216110341e88014020b400005485244c1d68001100b01200c1c070701c0382405aa6940c51701d030341400800c0c1c2c64206906100001c03078210390080c1034100b018000c0f11264404c00c48240c9500c0c4440300303805069071070302c03ea92189030700f4402030703c000303032520341000c406400c50b4080300c11000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 815570125 1250 815568875 815568881
    0x2120f061f03081315050c0c090703020c07140112140f0703061d1f0305060411040f18050f0601050f041119120c0f0c020415030215130b0306060301061103070204 71
    0x803030b0004c0f040b0745041804205142840c0a08401c050700300986000f00c503840a9031241c0c0318980b52031044c10380d80f0000d203144d4001e40403140c50300aa82c0c2500c400310744551710003009601100315240096000d08101043c80035a11030b02040d07038410380013481d03141d03034559841ca0080c5004100d402019140d04000491685401100804c1107418440045ca451f15480c00205900e40320615411a00b8002040000c15008161a17800c030760010720121607110040007090147c0710341d800361071145151090505d40050082980aa402d1244060790481d90069164654a280030300940b5448180b540c440007071413401c3c1d03000003041e0714446156420f080c0411301800c0c510280d4195200807031660140c44035002c41502c60302c480d4a00509084001c1c2605442c010142d00c102c1000a0180790707140d90100c51400b000303001d03900841d40204054140140107a03480025004214500000c0c95030b01004034400305e850003500d05ca500064007031403c582c40d160742100c0d04c00300a100504240810000000540c171940 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 815571375 1250 815570125 815570137
    0x4050a1202191d060a0323030c03040929130c09030c0b030601120501060207090e0307230115080a08070c121208010605090f04150e0f0402120f061f0308 67
    0x3d12600c00c01c042082c00140c896401401e0600c039217070065003800040c0074500c0c8024881010420b890440440c00c02e403510b103214000c66000e05100c0490300184411080d00141305610946800a1006040d0007203000c8080b00ca00101e0340c0410786c500305140302e11066001040084640c42d100a01c140c1c0d90316103404484458002d00320003000002080340d42d58002a6041004106032801c22442d0b15001c3d009465001d82e020349000541c65415642c451881001541d5540d41c11000001080c40507140360b4900079281000780a043d42814821400700b0101b004103000c49181c03401070900c0700c0036a521450b01c1d5000c842e00322003c0703610b51004503100c410a11001c0d80e00340b0a060614030054a15805013000700140d000b041009410000c85080751903884d003c880380001a00c02040c07200c12000400007100c0c96401581142003c44100f10007007100e2414980124001d40c0e034468914003d000c0c03d0388542c90b9049110b1640d0000000c00c1410426500c1682ca1404a5800003e4251030ba03030381040700d5200c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 815572625 1250 815571375 815571389
    0x4021c060608030702041b080408070201050f0d060305010f0b0105071e2f0f0d06050c04090c03140c090618010314040f060605030c0112180f12030c0504050a120219 72
    0x404c1000450900d480369168820000c0c0c45055558140781000345032180040c801041004082145404c5901907020380c2c02142a0f200c1d96600e03214060741d18401082188425030f004e40c20003125185070181481502401c582c10303541c0303a1a0081c0b5407110402600c103840305c0701d600036844c81d2a01c040351b88015420810460b407000111295040340702c40c0c10b104985c80705103100d11100d481510315941e40b2951042c0c0c4907409000810145d0381d02c3d000701d0460146078030080e07100c0e0500845041d20395256000506c1a1007070b0381244801c2d19090b5084206016400542d50440010001c034503000703000034115400e0f50b070145004a52206240041d0005010a4604a4580390ba420011080243e0b900842e400340c64264001c026180902d00001c00c1c46007001c0c0c0d41540255141c5541d003503600d920402e128256044014180c1105c80d9180590060b031464800d500060f24180c0050500c5201d6400c035800c0f118000c06810115040403070b005142c1c000c003035040b64003020110a04202c071326803180d6100104a1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 815573875 1250 815572625 815572627
    0x1c05030709080c0604120201090305010e070f0902030c0a110705030709060806091b0d17070308040c17121809010902030a0c0302070b070c08130b1b0a0b04021c06060803 74
    0x502001d0080040c0d50000c00c0650401c120f500800d440c0c00e030654003180d1601c0d40c4840031003020300050b544001c6a81010700b4a50030207811000c00c1000054000c101d624130711441d0942c3d43e49a007810100d0000307507880c0c0c07420101004801c400303500c5402c00c08242c4040c4802e507004140d4510002e490520194040c022294a85034108841d60050082d66401005030000d0514000000440701b8043c80c0404a03e01c1003041d40d000c00d081c8a09220007910400c051106103039506894107001d03240c8041254111f50f01100c2985c0815114a0b61960074813101d0124024458000c42ea03689107010b4004441c0b410340d0b0001c0820042c126035406034040d000b0445440c0059a90810300d004405844055400c0c1c1d0030f05004002c9000020414a1600d03444206490040140102446c00545502c01c800d504005070080d0f10010803000d2030000280b001d681107444d0711120132400c003141754a03030904030f034003424200580c4005005414a400410760744561030340f5030000015981d5a480c00c41760303d900003441c1640 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 815575125 1250 815573875 815573881
    0x80901021f06140105090d03080c21060f010207060912240b1201020406050304060b0f030a1103010c1b030e0a090609020c12070b07050d09151e0e030f03091c0503 71
    0x50351039030f103440c260fa00b8600303586040c024001203840c2101140b0020f0803c616080050b01240080099680050302c030601c062703028101d00714250304603509852040c0300300610301003544550b000260b0344d0105ea00503280c038042d152038400d108445030039002058a21031500c4c0c00c0210514000b12448038103601814002400f040d13008103000d81d8560102d0001410380c41080248022908502a07a50150344658086002882017021030900038901c0a215050f2007424408000c00809a079803409144064000304070f481c0c00c80a0444142d0700d01d0320f801441110b07405031900400d01c90442151408009850b92507020750392044542195410b81c8003000b400e5000c40e0800c800e11081c032200400108a00c55181071501c2ca40720852403a0018110300207018000a10008050703d80d0000302e076182d00130442900c502c05071405880500703c000c507040c80140a4516403c0701d11080e1144c0c1010b200311f2030085050414071701c3d1002060b400904a00100e20801800c08030600903170802d5024021981c0e41c05840f1b003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 815576375 1250 815575125 815575139
    0x1b0d050712050711032209090f14060103150f0b13020705070b210415050a0504060c110303060121020304120207150c120315080c030c06070b04080901021f06 69
    0x410150848040291400b11a0010300f130010654444181d004413011036801c0032150b201600001e0b030b12071000541004400420303c401032560940c41c070b004c0d1705000391800c201d40d00365468400c240030007007240c100ca000502c8103101a51002c01d400404160018010305020005269201c440e01d001002a030001109803c2140a022400003400001145401d100e4401d03002140c8100c42d80b03040c01c43c0e500c5200094184035103400645200031300b0f0402002a8101921030710042c0c6421036007610700074108002c6c1a8280d2103099003230100b4443c800910300355184c00004480c1d074456035442c0210600030012403546125980300031400f40d4865165040c4042800d42c001e81401c01c0e43d0302c4a0000070105407003801c21a04180c1d1514a56406072000d110f100e0442c42c02c4d00103200170aa5030000316080c12010600c05070000d501d50214400b20201e440070a44001004014460110000c000d10318000c007080000e40b4042c003906070100140140d0340403441d04a0941c1d1400016000542c569880d070000304891 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 815577625 1250 815576375 815576381
    0x303121404240614010809120c0d170f010905060303070b0f250503041203090525141f2a1109040317040206130609140a06081b0d050712 60
    0x8000c899003d0144134500910f841d0140111142d403418003004900003041c044052091417210400700019544440e17001c8072141c0d540783c141081c5004500ca60320a02030585140f0b01c1a4801c40b150081c4181a80c00c05048402800025000b80c0d01031005011100c00610f0b040740381441501d106c40205130502c1c20540b0300c00b0700507450b840083e02d00c500c0740e000b40f0284d50081c02c41ea8860740207640001c85a01201d411001428003a1001d0910f004541610626429409908925003161883c45120311b41301d02d240004203070320300700895000130807220303240920501c0190403069400da810402e928004100d048000840d50024114005038104841010041121607100861509641356007851515a401401d40108040b6030150704414200040031596607030219080b29001242e8401e459076551400381c5461140c1c00b070844100c80094511880f810b02141100071120035944800b480e4950304584085030b02c82000c040c204420402070b44000c40854080c00e8000d0403143da8824808524507096022 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 815578875 1250 815577625 815577683
    0x315030f1211030d0504020d021f02100c05090d05071a07050f060613180804060e01120b0a05060a05071e06050a2009060d05010b091801030201090303121404 69
    0x14003510030310002c1e10100000a07141c184100200c0050386849074000182c0c12600900001c2d03002d084405203840c0d882c0b560100701108103042d0210303070070680b0000000c0180c44900040000042c000e08c8003403141c6c940070380003001c19030060054410881d29005030074980b14038103d076808000400a040d0080110400144004038016070241560382050000906c40c00321100d140e821260f16100c050202030140740b017040050344c2c0003201550b9a955400080c1c50812050480ba0100343c2d0411659030742c0f000e80c050110f004074020b001c004030354101810061240c2083c0c81002c1013050a0042030000352951004030400082c2042914200180340307040810340c0c02c000d00c80c159a42c10700006980845500803511043c106246400d0348600c4040b000c10224050400d404e10311600340070002910090050081c8000e04007941c89034880d004844851010359403e100090004034940704c10008070744600b842400d160b13840703000450f41d40e200e00c00300c01d90a1002d60b016124215180701c010b1a606110150010f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 815580125 1250 815578875 815578877
    0xf0605030a24090201140d0209030f1c050c03030f131b14120c01110a060212010e0601080408041509030605160e030a0c09090c1a090102012d0c0315030f12 68
    0x1c43c0400c0b6500003440c03101e0b000c036000e001810200e00303000e8000711034054410100c0d0103412181d88028142c50560384501c0da050241407510002840140380b440b0390b044400074448000151314546402d60b608003000ca006002c00744031a8031806600000d110440016914081102c80c1c2d0030322801c040116941c42c440c010302501c80c018580c1d180f1080702c000f01d00036480308400d0900034103131348040c030406040002c4000e008100074800520469011544181581a01c02c02d171001c80c080c0c3e940303000540300c80d401924040c000e000305010400c110312044080d400e0242e418600b503119141e8a80d2510300381c4009840701d840c40602811400c01040e405500f49008100480052001c01c50a4480315400e161601481e200c940c2c40e00050b400f0700004480e148001c0503010000580d1151010450046070040b47c01d45006500304510303c1140060802007141c039003040030600d913400514104103801898150210f10516071250b61100300c410440400200845c001c0c0c4080c542003c084ca090002d0b0020541400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 815581375 1250 815580125 815580131
    0x3070506060108041a06030c060403080d06060e030a1214030901023103030e0609060307020604151a0904020301090b010f0819080313050f060c07050c040614040f0605030a24 76
    0x40428407000440d5a9105c94000d088100e0b2904000b180c20600498102600203000003400401c0003103001c0204102d1013848003c00a81c0d440d00c1007141c08088035402143d16a02032090384020428029200c242040c450505402034050300f4040c96013604219003941c1c182c1d42c04641c10f80c804125030200050054212007800050700b03d603c09442c07198039808094100310b40b00c040d1100d952110411601c2095000b000765469140c2a6030082d0345110131a000c0b1401000c014607040e0700070103805007036a045103140803001070304100c00a12031300690041c0182e91540d220003040001c100031110a5003c0c24803800c1c01581103043c00c407881d15194080c0103040314148841003510115860070184d07500052841c10300002c0380da160900314030700f02040f544900301d80117403c01e11514000782c0e0010400c0314490b90598a840c41c50341c040004650161003010042018440301081500d044d90100c8451140343c0c50004107291a41c01180c603080c966a401c8481c841071a0000321440d00d00e180c1840e164036050350074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 815582625 1250 815581375 815581381
    0xc0f0303030714090a030f02100813020411190807020f0f0d0e180c03152e031413060e061909030e10180603021206061b0a0503070506060108 62
    0x220359640720040640c0100b01050050610202542d000c460461200910b03c1d00c1064a0f803c2800140303517203100407031141140a020342e607620300800c0128407441c0318040e144000290364003400301a0241207084101500204021903084030311400c0c0c58001d05480d51210840d18022070f002e0310300a001248c00b00294083d140301c00e018500010503003c00c0c0001d00d03000407802000c00211f20040309041c88101c85401007000c0003000d0705280d001d18403504035034903112710480d5260180400c0354000801d40415480c6c031038000380d41d400f9614201c80300e207682d0300e0005100450155815902241500d00150754402e884015050002c00d0141583c000c0340c040107041d02c0d0801d00d580078000c60401d000e051007d62560941400d0500400030881000c4000c0c101240c050480d00005061010349441600500d065000100b901032003442901d54103010400901381c251a240c080000395041210050380c0341c11481020413510b0001d20003c804144544000d40c0c80d40e003940781440c00c0c83d000814050401c00b40c0410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 815583875 1250 815582625 815582629
    0x9060504120c0507090b0d050f0d120c1718010e060f06010f021504020102031b0d031a1e060f0f0c010501140919060e150a0b0f0301170a06110406020c0f 67
    0x82d000c84205c410001111494080819070b210700140c800340880c0568080342e00d0301c07180412403145041c0507a0750030340b00d0b81d10800c18034201c03503c000c000380020f013007501c2c0d17185501c0010450640200720714940c1d441c410340c2c411141e0300755401c02028100c650041c100b03010003018100b8407107800040c2400c12492141464070000d45d01c1190348482d00e410420040440c0c1507900a0040303840644000c8210341c0c03105032184015540750b422a8201c00040d1509032224100b144a00d420441108010099206035408440d080680c2d4425010540e0210040107108481c40c040307802401e503405a50b0718591652510840d003400c40350140d000c03070034001760141c8000c0550b40d00e54501da400307400600e0030307560b600c6d100480700000c1460390072802800301c400081c403c41c01ea085000120198040300c40f5103109803640e060080c24095411690300b8070300140018402c8a4900c01041c80050400044445460071502d03003606860300f0304041514a1000901030000b00d505002003c100e8400343c540c2480d0040681c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 815585125 1250 815583875 815583883
    0xa031404030f0209070e1020010603170f0f0307030926030a0e031204030908070f0819021302030103060b180610030209030111030901060e1006020a0f02040f09060504120c05 76
    0x303100304d401c000000c104601600c80f040c18050043c04809040402110240500b0001d0405c1c1803824007100c10943c10080501801d001d030390b40401e051509031400c1d0702e621255006200b41041d036107424082c40718003a026501a500c40d040340ea030b010605a442e42825070042ca03200103501100304120300c500d01c5400341d2504482c0c0001c010381000a18409040e0007504600400710441060207048084c002410744c0300582c07009555000d403d698900303036603e02911203079581344907074600c58208485e101440281c4d003143c440c0460000d441e041c001401040c1007070403070740241c10480716540c1d80d40b0341090078104480c140c01b260521010000090504034000303540503115280450805400084440f865203003904955215142c0d103048580701c1c1080b042080c06446180034804020078640002201064000413850803985690060918411151251503546480581c1680c01a03100c01c008504181c2e68460f16004038003d5800282d60304052500101d0601c00c44030b001c0412403400142d00103d0030106d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 815586375 1250 815585125 815585153
    0x2101b08180a0b0c04050d11040510060914120601080d121a09040c09091103010f050705070602031e04030e030d2303090a0f0302030711150d1a120a03140403 69
    0x2040c00c034a01d0f502d18440341c406200f1038201d01e4102c00c220301ca1204000300313809031720007230b9004403024041540c4480340c0d907078941c0c8244650800a4000740c1c007044030301c0105c2c24041c0c00c00d10251842c1056085144510f00d031660030b910292240d808603d002c5502c1d948241c401000c25030b03c60307051200c030a0648101c1c007640411040140324080b0300c0040740c10001400c00d0880244101c0c0c0050145000900b8450f8402e41101001030080d400e04610040002c00380c8540c2e442801c06803102c07401c0581c00e48414000b500002d01301004410705560349480c9070801981e0a1040c3d01c03035035404818038810310606050080d80c0d40c80d1007e114901c100800308401d4881004141c408061116859a842c0740300d081c0b070203070056005840c0e00c01c241a030006040d40840109095401080d1004103441c800c4184001c0020b0903504010108050041d250301d00116080031481d1844141c04040019480002a2808200d0044c0a0303586d40050900710425411002180140e8040c071100e80c1010301e1925030381c8c4541009 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 815587625 1250 815586375 815586383
    0x4140f16090b0901051c1109040518070308130801110a031505031e0307120512100602060c031305070b031503010204080d030b2103040314010911040c02101b08180a 72
    0x4110a01c900c12146c0070300c0440da40c01c00d424804409000d02989059000304e07034280c083c5041000060301e0002c58407a09010008120042003010b10b9a00c1d1014160890b110000f41810340e4500010800000d0144059800c921700c0c4a66468409007006011120400a03846103544010010842e6540c0490502c1c07e0310280c0c01d20031600740c20b4940712402c600c1000401030581c4894040c00180351390150140030f0785880c19a490919481e540d00002c4108424410f600042c0d00190001d41642c0c00400a0364000c2e039100c08031120005281c0e65282803c01d030360401502040b01204200b0800c075401940310280600f98001c43c50036052a0781d442d120620b03100300605068136010025582e0300c507101c0100351040c00071052040c03d142100c034a5200e5202d44821b890001c079101c40c235840da000610414140580c043c81540320448180c05101c0940030b00991102540603103881204c5004c540c2c041c14115411001800340b402500705000b5008550180a010b03a1685403040419180d00c00500c0c20b0000e600 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 815588875 1250 815587625 815587627
    0x706082409071209060608100605010c0b0411130f0b01021c02061b0405060309030d050c2a0f0102070b06180f040b1b040e041a060d02010e04140f16090b090105 70
    0x30104003c03000d4a500d08000341840e01d42800042c00708404600036a220810401c18040680e0381c038011640c0d4001820f002d0b0200401d07102040c00214a0b403c0310b0000e0b034020744544800c651001030401100c00030100c5518954444100210f01c0d81d052103052440400500444554081e05200960b918001400183d20001c1a5007800241800c0010380c0e00600d0010032603656450304420749034a03500139083d1904040d0400f408202e0044481b4251800c0d001e0101c1d40e5812086085024040c4040d000b046800d04d01030b24811617200402800201501401a0450b440701d0a111040c45005402c1c41d03500300a181058080c825041c00c1d80c4065a0810380001c00001d442c0c0707039844030125080d0b81c0003c2403000c2c140051300195081d101c0b00a1481a8003e61030104081e100b91480400b4000c203d5405a0114401c030070700e401907025141c4010502400b0b480024055a084200c0c0001402500c0303e040060b06202005000c1c0c902ca104001c250f4071900d0010080c41c036140d0010014041c066426043c880 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 815590125 1250 815588875 815588897
    0x1d0304090905030c1e071a0d1503050d0c21080403080406060506030a0e0d02120a031104030b0a021903021801140c010c05031b04030507060818070608240907 69
    0x2003c00c1583c40c1090f05005540c1c00900310320090400741441041c4400324042e9102c000780051502110300d24100c000b80109261084602c18600181072416854040b01c01e025404070128400f000b0042040c01c0940f10404078035141e0034031000110407642e40c43c082651805c2da5850300c0303a200d40226006580350a00d150703540c1300c42c980300e00504100d40089400c00804004c01070300301c80c1c40d000f001c00c1382c0b810400e50f203400001c0074080781c07680407035401403004d000100300040d51544240d104040e610700d1460214140741d100d64074448040d40a036441410f250300440c646042100140d080382c400340d49424118a015000040140616407940d10030741804402c51260941c036204c4402c075100d200a00c0020400b01411490140040d001174501c0b80c185a401000c00700d0051142044806403038100d00100440e600d464412222504018074030711480c2e800800300b10840c08200b00d0b501c044d100640341c0302d103103203001148200242c48041058591910107955041103403110f50b40241c1229884c503044030000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 815591375 1250 815590125 815590133
    0x90e0304170f030c0d0f020c090105330d060f0e0f0408040302040c0c110d03021e030408030418050f060d021513030b01030210031401090c090504110a031d03040909 72
    0x6950390b03551081d5400005054041c042002c81c151400010a446500001104100807655013205000c1da58004e000c500045c0040e250100c1d450526405a83c00c0c1ca03540400013140d100c0050344640588900d0350003040d10b4004410314001c0d41c1c05070600101e404c1002d4603000c18035200c20030103412140c0c40d50b80d16000c1b5091015400440e001707550054028440030304042801032494061507019100d00b43c00c00d81d07041c02803a040400049043e0503600503d095443c164030740145e5000c519590400e440200000108200c0a201802c0103041c0690070b0031008a0491407402034070f9008104c1038844105a003005100d45e80c400e0700482058040e51446a902d50710000c207819031240c00e1f03000c49a5060040300000304901001142e040c0da10955a450414210885c00e5041e00c01060342846101c46810040c8529080343d48505a41060303460034810803544c920105040760408032844840c208009000205c054250185449005c4420f14000810740d00e241840d440340594062800703000d441d0ba9400307040c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 815592625 1250 815591375 815591383
    0x101e0813111801031103150c0901080612190507080307080a0302090d0b10180908030103140a08070308160c260c0f0604030f030b010206070f260a06090e030417 70
    0x80b501001000310103585034103040c0d41420071031030b905101c3d100c0c20300301c1201c4682c8212280d004001070102641080720100054403190b20041c0141e03000001c41d004002000010055240c00c25400b2201d0b50010b000c0d81029810068650094000c0354000c0060000140401c8201c501c45481440e00684030303003102c400a00b481100d44406821070709860144281d08480030301207811100c2460b04c031000700c6211074103241556404500540044018801080130400412000481030a07a000723603800301441f59a149130717071307003110006500064034030040092044409201d07a1410f401d82c00e00c00c06842442d55002452410003200322140e0600389541c84098802c1400e480e4100042410707941c02c20100d88072540d41b042e046130300380c00140c4103107603103410640244140000c0d041c06134043d103800e5413440400d603252001d00d1560010000e400903010060b481038104440d42c40604001c1141d141015120401501c100c2c4d045800094540480910041c100000310740031504450340791a03491040880c401e0070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 815593875 1250 815592625 815592649
    0x9030203090a09020d181505130f1a010602060609010303051b240c0f160305090616151a04050a0b060418060f08031b0309101e081311 59
    0x10403002e00c0441e80003d650042c1812031140360b030810500c1c0c40f01c85007440c03081c001c080183c82d00034a0341c1c6181d0258010b4000340e81c0905200002080441035030756800c0919420302c02178418480c01e0b41d41c5d008407960050000d006000c544018449828000f00046000206100043c11300400090419141210462070101c442003101a190a400410455030400b550b04241c02211507249002074900500c402c00d403a80450000304050801400c0020002e014445000c00e9040c89402d00c0400e1441d80c03800000c0004101010b14414012114900822115007450300e03044007030309103141c52084036080081c42da11003108840100d000c1d298200c800380146007440781683c00442c001004500a140c40b02c0c0551140044071040240e9981d4114900103135909025591023031f00200320004076414120200c2c00042c1280003a249018000c40005003552072400c1c001010907010f510940e855014117a103409035017020308004050b0715140c003903000e003150455002010f11129000d1041c00380c50b001c1060070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 815595125 1250 815593875 815593879
    0x18090b031c0216170705010810030312140c0a1d0607030e0a090e0f06060a0605160c09020406020d021b011e0c0c0f05030f0706050307110307080f0a200d030903020309 73
    0x161858540d480c0d450b20f4540030381104094485c03a0310000d4a54441c5402d54800d141c1c07000c02100460031903504071800c2d43d40d203100000f259101c0e80f50240c400d901c072002900424100045d00c2c1c0d0342407000f002a0240942003a510941104d0108194041c0ca5501c00c07030b50010b034945010018122020b0004003138588c41e03001454490f2521060490103100000c0340c96500940b13a0440d0100c4d40c0d01020000c1c1c40c0d10901a000c0051800c1c055102603c58400e500d00b4020312400041032401e0b00c40c3e181c4403c9130455440640141c0c0400c00c9010002e8060109129451802d40c0082c4281041e50000e4542e80000c240d06440c0401e451250312054418418500e642d980b10020220700c41e510a10a0004245401450700c6130240b0a040c000c2408000f82400c1100c0050711158290703512010140c40520101a61000d6800204070403000a20300d07030014503401844240c080d8444031a5400100350310919031810901c00040c400c9540c590900107034044080325180b03030100c0c030b00c140e91408900358000d00325040d03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 815596375 1250 815595125 815595163
    0xb1b03030702031210121103030c01090507091808070f170a0201060317130608061315030611040e01050402030a06120b4203071518090b031c02 63
    0x20045940c040b0082000f0074100d00d80004c1c6480318260310326140418400c401a51b200715041400145c0030305082c06002c039008040d03e0429034550151800d45840c248207c805402c00b01e001d0007940410310444101d425442c0520601001d2a42c5806c2c0c80c1c0314000313000d001004201d004c5e80800406003004010540c030350712010307111102c00314040e003c0d118500040320344480490f40703000100705c162f003a1140010100c800e0070750f0301d15048055a1510f4040e000135088158100021601000c5004086c500b07044802c80082c41461424154200d85000035030f09140d55041000700050000d0074107041c191001118016920b45a0075091401080e1a0340481c0c0c6010310192000c09000c402c1031034a10075848503203030b9001c0340305000f000700801e151800790100c42040000c695003c804d181d2002d0109100c0a002c60752860b88418510b4079004003040881c0005042d50120310083e04500da170303c0e00410260f0344c01d1203d00304041c00030361182c1c102e05180755200c22222420703c130544204005849040711038000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 815597625 1250 815596375 815596381
    0xa030c09020403030807080606221e0f0f0302060d050c190c1101020715050309210a0e150301140f0a1d0105270702031c0e060703150b1b0303 62
    0x30040d4009102c19404104690009480d450082c000c4510804005140c00e103400105c1c40d502c02140c43e260000201203081c51004540301c0c202c40340244640c01080c2e84024024604100300103000e0711900480c0c1c140154010420041c0c85010654014800c03c14010a41e81c0d5103c07814840750080014490107000000c14034080c041e00002c05070405130180540d403094200e0180160790b2802c0034401e810502450050724155680700c3d8010350340141d03004043d04c81c5d10300540b2001003600c080c00580c1e04040400904a0311040d0070032007105480400fa228118002469035a001585c00148200b1500440d83c10032107001d590307905002107125800510390321440d911003102034690b050320100000322041d40c60021840e440e10310002c648800b03080304a49a8100d0044115007000300207455a020743c4818031500c0c2c0d01c0b03042c00001c40009401860009511030a2880c1070780740c14405800350080c1031900d20400010510200540207030340d0740d04a01c03992000004151486840c90208084240c0004814 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 815598875 1250 815597625 815597639
    0x30a0f060605041514030c070305090406030303151205030a03020d0e010606050306180f070e01090f060f090e0709030618050a080309010b030d12090303140403080718030218060a030c 80
    0x10740180e0340c1e548030703d0b005481d4030b41c800d40ba4608509000c000b80d175028400030b00030703102d0ba10003405401d101c3e1605500301506d44010506594683d08210003180d100e00c500480c3d0402c2400c00d100500000c60640700d9907440351156a240d2042c08545c00826170001101d070904c640a4004c0c000a440540080022581c4e5a00c020b2040d0400d6403003d00c20200620740c602c100900d10b442d2800b0313440c5001c00401c0b94850300401d42e2480102c417031030340c10700c0021400090048003004443c0d00410a6480d5548a540302a0006200c00096006a00246041c4080c07040030f0707610000d1941a07075400b940005200307843c03990f03150031001e20804c001c2c0180b20741038001c000c0042040156000e413686100074090398984408260300e50014121000024a0401c18644d9282182d0001c000b40d5010f03081c0011102d40400700d8661040049500342c0104480c041408001a40911000020a10360101003101d40c01d6900007000192400301c07518011810501040580d0740d104091002140d00c43c400c40c444940d1224 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 815600125 1250 815598875 815598877
    0x1170a0b03120408070b0a23040608101202120f100b040621030810090e0a050c091308030408040e190b0603010e01030b0405010902061b01050115080705030a0f060605 73
    0x24501d00a001c0d0b01482030800207035600f600c003925116000340c010181004402220f1b50001446071081001010030b55000388103c108100400700302100565545003019805454848050072440311184490810000d80c0c00000d5000c001950485003048044c0a03051b60501d00540c0404040c43c0b03001e03d48159252038683c2d840068880b03c03e940c1842040c0d550001000a1080289492621480b409800c00002d01c200707503543e440b514140c42800501e460b540110215030408101100c5a48110a0b44060007010010020490021070b80e403151450405c103003c0398038000400007850000040046001c100f02281950003074610a100c510552070210712910003107142c1011515218a000ca64a8075410100700f00c9040e1240b001f034000b01070b403860741c40010f06030b401001582e41e5540c801c1c07800d00580c0c512004080c003d410000391000c0c030103070040003421164107a001c1c405082405808100c89174005844c81e9016050781070091f100d59a0031001009016028451114503250180109e42c0b260850 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 815601375 1250 815600125 815600141
    0xc010b1903020102070b032a0c0115090f0605010504171510030c141e030307021003240e0412140a020d0f052701170f01031e0f03030b01170a 62
    0x184c21160302560741d50454070148400d6415001c1000110849002c442c1550209070000c8001202c09252142c1002441d007100c0c45050718445408840104000009440c001c903444015901c0c0b040001c18a44000a030180c8558400c45002036003140c0c000e02c906e8001d01c0a0400003049030442945403803c110305454014050100703e401c51130460f8082454030400b5458148242d001d003c0b84c0100c5400b0300c511410110b18044150300d440704009400060b150007942e0345501c034843d140402d001d8007841c4603907450103001641320112a81000200f10480300c0008140d00150030001500303002c5441c0c10111100d1083d03100c2c605418000142d104a9103900240e4000800304503503402c0100c4c2540e03e42152203100d00f205803c4040b00100900c5240f87d50602d0034229807a050405403501d041840c2c0310142d5110458255034200d1030342d00100f050100c01c810703c0c1602d10300106003020402480d580c01014252403100501090b075940365256059000d000910384104091080036890b00e4030850305c1020344295 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 815602625 1250 815601375 815601377
    0x528051902040b030603060907060801030201050912030c01050105030f0a02030c0d0611042c0910050a1e1407020a020612090109020d050a020301110307140906090a030f032d050c010b19030201 84
    0x47c2000401c0c00c0b82c042010000d40d43c6503500c8542591a40c5c00442c3d0a4001e6039906a00030b004240b4005a1a410001405e20242c0240040b03804d616003004c02d400c10700440701c03d90054115010700d400603640030904610340e060488002c03280d09070307600346a03000700000440801d0700c9500040100764880300224031403da40c0400301540c644080014100c02c4200107130303030090080e408100c841c1f0683d2001d0300001c0d8003500c8000c002581c002001406c0f05201000a214000c45a90b2a250030b03800d60030201c02540000140020480032142c0c0e808207440340b20303420040c0000340c0d0420108080400c2134003e003000d00d800603c1c000f41c9100a01b0400c0e250040c2c51000c0f8070070761810382460201c00411058134030902444d141e01e014030804401c21412075002842c000d9008504200d0755880e40c0c0c0b2000c540010b075000d51a02e40b0a04030341c1c034011300304c440752040510400c3c6403000003400030300c00d5000e00440d071045442c03c03d0320b4081000280c0c0c0542000b26449903c151000740100d00441380300e004c00c0c220390007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 815603875 1250 815602625 815602633
    0xa0606050319020d030c1211010e010203060a0501051b24060901060e100318051e03070f12030f09060e010f05040b0105010c0807150c030528051902040b030603 70
    0x180d0410142e64591060074003a14424895401015280010a10310312034000d0420100c0761020b03a0700e0307041544c06803080070701003821040303001d109136024894000d12640b4031008503c2d40c10502c0018554183d81d2081d281008000500040790759841516a5841743c142d104507410300c00340381c80203035080000c1c0020449855242c000500c4d14500794803a01d040b40c0447d1120350b00c404040c4140040c00c1c0d45032141030240360301c641c80820f41c50040c2d25100842c42c0504045c04c05000c03d01402504801040e05000140d8400e001103c045901e2038064503031154841c4803214608024076060740600300c3c5aa00b00e4480e85000c00c90024460590000200300a0341c0d002003240078201c01e409000c9940581c0c02900d90850500180807650048502d078001310b020382c141509201880d0341d50324640d91200e604007403c030b440c0c08524410540500481703800038461000c4504141410b04000c0360a0841040c202e60140c6171004510011f00340e002c220180c40c00001d0a540c0d964039240d09a50507441070307640302d000b0308c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 815605125 1250 815603875 815603879
    0x140c100507020907110102300105011d010f0e030105090703020a0f0e0604092604030c05122d0a030e03150c1207051c0b10030204080316060b0306090a0606 68
    0x403050044412050340100301603059150303d54200c0c1c00400e442d922500c00c0d0b608201c08090034a900c2d0070380285500e000c8500142d200c00c00503551030384106902041c10f01c58002c80b01a000802c504803003101c0c08007803902190a05944c40c04849410701148402c0d015441d2100380804107101141410589000b519144c05c0903a13070b01441c07095403445204890001085038080b4400385000c0d00719064490003840a8603840703100f10201c0001c2c03180e0044a05101c0c0c1c00043c100200808443c3c5100100300031249c5080300c41646120030303100c43c09000703100c0290998604081c01820a0307020044000f403020f0403100310240624001d8042400961014864828080303030344040e812410310a4802d1250490082c18480b14083c5414009000381100c82440001d0145c110401000c1704560400704141201081c40750701c00050281e14100f401c1c507001014010001446580000000c64031092810200c4458007891414544000c140c91112103a142c0680d006000b001d500016080c1070240c094001000f500da = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 815606375 1250 815605125 815605127
    0x10e04120503060109090b040923070f050f06030912030a090b0603010908091e0d0b0f060103051015020a08030a020a020f0d0f05090d0f080c010c05120f13140c10 71
    0x70204841c83c1340060f0142c8820700242c0703403a0b00243c0d1500d40c09080800c01444607564400507400400c0760300c850218145040840c40c008004000040c01e540c003640c1c1c145400c00000c07840c113052000151f401080b0000c0800ca0808003002450048030b03410144603141c1c140301c0703014405060328080503a07400039a80040b80d507524061041d01c02d45030f84000001d140030304000504c0510a24200c0012031700d03442e6007400400b5143c0e01d1155401d14030910000c0b07898603100310070b64101803003e41000d042500d01000c01c40c070340c24032402c46d405554401040001c0502c1404c0201e280c418190801403200c2c40100a03c10b80703400c03d40151a1080340b0b5000d842060b490240c019036103008035550080043c0c03001c0d0b000008a4006d0703008014480010b801d1000c88005d6880d49060320520200480f116400003031083d02d440f4081c490301a01d403810b4540545000d030b2115201030415070281468074020920004201c584e5a10000b0106465001b020341c4012198442c4140e10b91075400d03201c034007444003840403a001c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 815607625 1250 815606375 815606377
    0x7031a0102010510260609010906050106030b0a090506030106080a0c0302010e010c0312050a02040b0c070608010506130302120a02130c0909022d0906040806100506040f09150e010e041205 82
    0x416580408410140c6402c0c1441c0c03109060700e0f940441d40903400301100b103000c07046c030101d48290414000495030746100d2910030104d03081640300b182090702e010303581015940d4a40d5264210780c5c02001c041020b89441000900400480c0c3c0320f108903124a8198104005110100c002100d00036200c41c41e83c80040c00042d01d0490314814003c0c001a04030384541c0c4000c030301e070740804d81142d1104001802e090302c9003c1e00c5060390001a41d14007642c40803c040003520b03031184856000d42002c0e65114103041c0c0000c00c00014240b5800001e1085501c1030074900741c0e007410080100e400f0340003802e0000900003400c090006044c0c0700a001c0018010340c0c8042410300c018021640c0c5c81c004c640000920400940900d5003801407008503946d01c62003008191229540c150150000d4560320001d04001e0910f500703084000100e1b60b20140c0250743c1031108100000c000c001000c1110012038010660002e03c3c01c86101c002095040072801e0a1048000b00744000e0386512180b2892250b109a80203400380b5605440da = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 815608875 1250 815607625 815607631
    0x51305040212010e150403090f0605070c090b030c120102130b0c010e1b0f010c050f012403050a03050a0509220506030f0601210510022a0d03020304020f030607031a01020105 76
    0x1a0f41c44120700c07a01000401711a91303442402450610340380c5413200c1c81614030301c10a602c0100041c10102c1e0003000c4c0000451410010308448900300082c1110720040b0b922601c50307079941846a100c144c19020001d0303081d01201c0e0207506030401ca038606a11028420302a81008080b000c0e25071902405810b10302001400da0344120351117114081c1d101c2040c00300018603800c2000c1da41000750349801c100014104020111411500b02c00115100347e4880680018505030701814002d10034005040021800c041058211541c241c07801c19590302c00c200303042d1410302c1441c2e0140d03004941e00c2d142c040703d600e810307000c00c0c13000c46041c1040c01161101010185d8940d88100084120380054004100303050038200c40609010a620001c80c0b00e80e115198941403084004079a03a2440d00040d0000e240c060000449800e08283c011886260001c00f04856070b50100800f45011f055000021a083d03644030301141690001c01030451b5948c2c64010300040142150710035559402c1340860880d0081d40c01030048900c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 815610125 1250 815608875 815608901
    0x60a0315120305070f0f050a050c120a08180303160b06040b0f0f0909280302070e07020318120604030e0a05040603031b0f050a0c150306050d0f0c05130504021201 71
    0x104110325505c5002120b443d03c00200d40c84a204c44070003000810a000d804110780c041c1001c3c1044444000a12802c2c000080d420b0869030082c06001000031410310580d0407a0100c4d95642080500700e201003071841c0300d1104024140384520382c441003044019420769100300401d031414080358160b001400000c0d0105171a45a02540440c010f421070b00744420300c287c0c001140c1d42200c0b5008901048180d604204018040c00004010300c07541c14560100020001000280c2028515284c000c81c02500c0b40100320602203a15070402c4147c5503640e51f115010000203001040d2610b60425142c0606034000048081d800b403104010001180d203400d01ca070340c00316600340c1c035000c1510301040640700c0d25034501001115a01079004240700030400800c0043d84051244030103281352420420080c25070f0021102001c20541061001c0c0038540322a103142000a9002c0b007003180c81103403031900c0440c4070469001b044d0800240760a00c0f0300800540c1020f4040d900076201c40171102403400d0003a013030300c0506481c88 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 815611375 1250 815610125 815610127
    0x605060412030f05130b070b07020d020601171c1e02030a020a06090206071209180b011409130f0b01031107020d0f050309030d0509011706130c030b060a0315120305 72
    0x4400b0902612204108803080c2c80c01900d4032200016101c0b8a10719608010008000807601504100c560042c998200d1a0760005000042c80b42100950f100c005024400540d810746401048038942049018010204003403480c09111662100401000007e2502e528440650a004008a002100311242c3c5911540503100d1140d0301d032254400f8041c04a000c0ba08030004202e00c8002c03504c0f00c002c2a00141a40c1da855489501d4007500114600485819400c8585400c4c80070020b6078200441100504504861a40782c0b510700c0009550200e41ca00030a54007030920300d000421108661111031100001d80301040070043d007107188134050103a60002500042c1c0801200c1c08540c50340c010340d510030300c91411203140200580101e400c0c00313041065800840e0001c6011840e540c2c02843c030500741a00700024011915044000035200464034225a040d00d80d0f820008080c203200340c0101c080d515005e0b001d159564400ca90007801810540322500c5900d590620101e69954201030190f02140c00d03980d0340d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 815612625 1250 815611375 815611409
    0x70e0102250b07030c0b0106080f220c0305011506050304081e040f030c1404051513060f03230d0207050f04090b390d05060d080d0501030606050604 65
    0x40721012002501d404000000c0000d14503544802802014425a1000705928040c5400910101c2c113070013a4060080d020100602914160710240d808064a50740b101100b090000606401d940108041e1142900c200080188030b41500800009090410208900c55451074112064001980c00400c204002c008403490111504034503071070070101c84910762a0a0740d03081031510031085c1d503000716144200984100b0480c1402c0070a900d13000400d4505001d145007540016166100703c600c0c01c0d1160103c101208802c5146a00c204043c1014442402407607441c0e052400c00d00109405400101d2617040c0c045c4028a00419240200031081e001814020708010402000002e001c45041e001981d405240700401e00c00302c1918015800808820040d5500c1c000d00e02c5040c6145004045112003885e61700780e4801486c00b1602c1c1070303d1880c0c0008039074a5000005410000c0080003404800c0e0203d0485080006503020300c0c1201c3c0f080f07008011403552a000d01c69680907030312a01c04c10344504840 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 815613875 1250 815612625 815612653
    0x1a040b0604090c110d0315091407031508010e060105030606030115120503070803010612110c03040303030b1504031b060206040206090108070e090a0915110306100c020301020d02030f070e0102 84
    0x44080c0050b40c50030200380894581c0030300762400d200480d05c60b00180c1c03214407188000c5088450603000d415410010301002d1115048584054030181c286410190303183c400e089003031000700312400504501d000074400c5090311044203a85210038010b0a02c00c0c00b03601c0204100f4641442555414240c00c0c07100041185816080200c007008a001030b2514041042203800003200307100118040c0c5007035181c10203950b150105c2e1700304640003500c00010454041060902240380001590201da81c0751502160080142021809118035021064030342000410044100306094041c207107000d00cc0d00c1d40c0d10142e45e499108980d60315060f03501a4224008005044045d48a039100e264170044030f06041100c45c52100120300c1d410000c80304c84402175903580742c036020895600e4a03504511001c401c1803244041021441800d440086e1601c0c0c4100402c40d0f9581d0301c03d0140b00e50040301d6400400131925944412034181c042d620841e205000b1004400006182e14021042d18440d200182e00603d280c500d0250 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 815615125 1250 815613875 815613881
    0x303090e06210a02130e150f0114360f01050603011401110f0d022a040902031501060e040e011b030b0a0b0c0123070f0c0f020409061a040b060409 64
    0xd0b40c000340a101d10f60340150301e5210480744413100c8100002840c01c80e880000e0b080c02c6081c011140080c6441003444500a250080981504d03a0000000d01c03098003040003030900e000c41200041c04d9050759150f030045801c46e0840c5401c401e09402614950744e241c0d80b80d901c00d81000d00681d644002e040c801031000c070445e40400080000e06040c00b09440c0813440728030b031422000302d0640d02a0f91081200d640382030703810300c1200400d0340040890720100a400420068440340c82d030300d5030300460340c44a0500c00e6517070410440c4840da100c55a5071406503103e000c004d0400d803810154501880c1031010091200805101d103d6040a1901c44900201d00b049003c601814030030030029032011a840020420a400c44010011042a1800014049540c00d60070340071022011403104498540720401c02150380010b008654101c8503d42480104900d18001c5810703881202c0c0650803919180e410030030401e041d4040700e42da040903076000081c0f440c46410801036030040100c4a0300260103010030484004160 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 815616375 1250 815615125 815615179
    0xc150f0215070507050a05060603010c0e030c13110412120c0203031c02090604180b0916080a15080c0307151403040203120708070605010605040b0315120102130303090e06 75
    0x49803c51400040f500c5480c5050741c101020307102034119406101903440d00f4414009049840c1c00c0c1142c440300c1280000e5100c00c80d86030294040e8040c11411100750015134058485580030320089038880c0c0e242c03841c003c00f04911010407140d6a00340d182d0100314901034038000c0d00c00ba81c014019031512000709941002191262071070b02c080c94090019035481d13a100350151010309204008020100c108005080694900c07c1c0c8440c01851908244800b10b03c941584584840d2203003400030705600c840c00c03800014125469144c1000016180100302d00b0000b10b41e58886d403404904840e210398441404800d08469580254086848254145c0c2d100989402071a403142c001020b481e00c6c0d410000c0248025444248110303100100040c90104002c0c00344585405043c05150050a01d81441c0c5040407600c03002d006940c0041044003003010301d80d22140f03002c208480307c1001303648990101c09602c01c4155140811000b0543d5072002107040700c01c100d026071180c00020940c0c0c0c10003060020000c2074078020f13 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 815617625 1250 815616375 815616377
    0x1b06050721031d01091b14010c0516120203060a05070816050c060106051903020301060507150914010c0e0f030d050901090306051608060301090f1205040306090c150f021507 76
    0x600004000304095018098140341c00c2c80000c0b81d041000c0c5092042910811480d1406d03183d903400512040c408100b032640c501c034080c00d068001c410141001340c0750115040c600c05040600b018086070380c0f0382a01400791954425411144d068845455500586108903001800210040001000700d4019124451282c8207418690b1a004c407041c165418803a090300100d0210300000f074031704101c8105000c8410303030035450b15045056504110000740140b1441c0c5011f001c120030700d40704158a810a900000c03140740e00105d01418101e0442002e406060300d0001715003c20b03d000c81840c6142003101ca500b441c0c400040161615140d040c81c00e0300c5980107405824100580030101000150052040714003851654920602c0c21103a180000d228080040c071050282e41840007503400141d101500c031440c2544044140f0070803400d500101e80d42d015551014000741c0c28030154500340503c030754008040d1000c401c6000000c03221100c0603100418580580401644a034807030752001d40e80e400e01b0350342000107 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 815618875 1250 815617625 815617631
    0x8060f0612010e0702070f0308180a0504020307031a030a111905061c061d0a0f1113171203010902030703061d06210706030b0f04091b0605072103 64
    0x81c9030350014010303000d82000750701030b0580c410301c54125010822100240310f00c0100d524100e044d56110f00882c0249491440e01c4074a08224014640d00c460040c00540341c040e008548916150300020301034004651440007810b00101d000c105d0f8100481d4043c01180c00c14000681340b920309c03040c0f003071401558801641103c0e6410740450700380e40b001c0042c22007841c0e04600c500c110120788100e03c101c62044d4400440b840c0360403005580006003442465014028580000d2440082c159a5000e045001c0c1032180100b80014072036000641180c805041e1045030141c105852131365000036580c2d8003d09010f00e21201e051004000e060000c2c0c0045074040d45e20301e8003190043c1d882100142c0c041c100e203035100c004000c40c01000842e0030704202a0b1003404054400c0010142c01c401500e850301c059014650404d91610811034968440540c004c04116004d00b040141014905000c402040c03031100010400c4401c09000509500c9a42540c1003541c120181c024408140a2843c1c046001c0450038024561 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 815620125 1250 815618875 815618887
    0xb0a200a2105250f150c03021810020c03030a031413050325020907050c0c011d04020706200913020705190f0605040b10081902090c0d0e01020d11070308060f06 70
    0xc6044426903005208240c516001101303001d0241c01c1d6041d08060038101232050142800419845030b20100c1208191440f60148203048000c80c02d03e0b5401c040c46030548030004449542590540c0400340d81e4840b00801000d54441c50414090180b4016010381968014404c4081c400789030b0300311001409800780380700503510b07480d400b1403400141140c280010410201d1910f41090060154503c800c08c2481c001e036291001d4021003030207082d402d907828021136000c14141d0404c0707069800003c0130304400c1c03821007603032840b04c01d00340b010761025101902841d1880e00c0b4072a01032017402512540d592141c0030f82240140c4900e600069164248113590405105c06080045011880f9160140c1d00442c03030f03000c5030300d402c10000000030704030341c4040000c0d03100d01619400e00c2042c43c0b10b04142a8100c0d0000e0341515480b06042c1e0b40e00413401052001458540311300020310055005141c11307400f003002880b11104900075180e09016502014000c42c030340310001165490b00e200c404090700001445a0b003011 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 815621375 1250 815620125 815620133
    0x30209061804050a0606120309031410110a090f0b121015030506010206012c060609120703020118050f010309080f04170f010c05040b0a200a210525 65
    0x90700030707a010f0700c0a8100d0228001405580d0041901030310100381050b01404042d54014814171503840054108400c90740e0410150034140001c84a90090716014030001c044010700d074255a10a0b1034640110f560310f00002140840700016200309d0340010001414041c050610740c902010080c90041030700c00444000c2100c8141c603d058502003c00e50300003c69182c84400685442c0040c0c000b11031005028030b1191a1f20454000f501ca0128501d0803140551200c402094140c09500314855111060b40001e0044160000d05101100c0c000d0380c0304107000e041c210071500f000032640201500000c0607000c0428550294101c07010040c400d1303620518000643e680d84425800c00d8214a4030007070903401c3d503c800b030820014213144003810030080000210a802c0075019118070b00c00c101c007000001c034a25200380c3c0034441004d0074009414841c0d0480c0907224a41c2d40781c000000088078148800e40e42c0c820940c10b6480c0009010100f03446c0c00d4508a01018540f03c500501e01044d00f4019210300550005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 815622625 1250 815621375 815621419
    0x1170d02190312141009060506090d0c1d040c0b09010903030c1104020c0a0212030c0601052202030a0e010c02011b051803101d01020304170f0d05010b1801090503030403020906 77
    0x10780d034604004c0445081920203042c0c1040f245c3c0c81511220b040034401d004c2560b0b60070407540142c2c0221140c1186002e103141590682c946a03000e85035a81501c284501079107481c80e103442c400d80c8101261000581c0300d60315003100380259846030f80042c0712a0001d000203030141c00b04084080c060040906090b6080000406aa00440810420f40c10012002c1c0071802c0000c1101d68001544001d1400d00c0100644a5585d150500c00c042c81900741040d0061028003c0c003240c800c3c0310000806555900d415500840503089515184200d58685004108c05510620401081001c40d0780612640501180f0032a02600440d03c81480800b08014030b44041d41d0070007400806541e002400314012040d440301d189071054170b40311495940d00400411001aa6003803500c1140c1200301c00d21610f615001440784481d000319101c04040c20710b00400403403240444805000a100e40580080800b40018011a01040244170f1290590300074130040c0300600d8600300c4607601a00c060000706110841c1c08101d100b07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 815623875 1250 815622625 815622641
    0x260607020f0f0a080d1d0a03020627070e07020c031c14030c07230303070c020a05010c0b22050d09140d03170c04080d0801170d02190312 60
    0x25a0006080c499011428840c411519031860302800100a03152201d00803481103007a01703820b0b20358600156803405034010300b056480b2125812070b50500150f00c0d01035502c030003d84260202c020700ca00700c2c0240c4031500510301c080070501009000c0d410700c1c143c0b6444d08400e01134690b0007540641c00b8001c205440030480380c00c0160154031400950240c6510107003d48107040030190103281e00300104801c05607484101c1c0c0445074042150300d425a80701700d078404107440214444140d804000b00f0301003026840031028140f41e0007190040840e1b0381c0c5800655141c1018100103011140d20400a2803c0300c510800c1034590740c1403c07101e201d1009943e0754a00b0f100d41c0f99400808203903490b009100100e8140c2000040d01d1060781c0121086030b864030f02410600b070f00e1140c00108140400021703420328a20f81518014500c8004603003c400a564000d80315140c02d004014811001d1283c501c9046070005026050b44001d0300501244142c51030100c01200d07a044094bc1801000349883e050000f0900c22101 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 815625125 1250 815623875 815623877
    0x21212070309090f05040203030a05031f03140c030303100303030e0a02061908010f0501080f1003080d0605090a061d041a0c090f010f0f030b0d3009030c260607 70
    0x150b1410255210201c896144050400c3c81c03500d410040143c070000200ca03908170140c1003550300e80d554000344111034507a00803140300114484100004120701c40d5110140300034042c06407080401c80505040d564001241c00007100072440311704001003806030b0310100b4230400c010309458091000e500465807070350000d484841c001d204009002c070081d520000a901506c1d81d08088a80c1c2403074440020306c00e44020f400c000c0c3c0717000c034031000c10409060418000f0040d90703c2940c030703903c2e101100103010052895201d1180118240000594440d40c584100420b84400c2c074004801c144c02501c0741540c155004004407640201c5a00c4612006c18403407400d0b20070720751101c802d40c4e1002c03a80d080c40707108a8050051810300c1070014200d01d0803904035900780c0c8403054a00d00010070014210000b5046894020040c050100111030002410845201c50800502c0b440d4102d011624100080302d407081c45100103001d403416001c081c2321584902491100d0303903000303c0e4918014012605000c1c10944142d407a00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 815626375 1250 815625125 815625137
    0x1a040302030703110303040f0303110904110a0f03020f0f220e070f030c02061f051e0906061c050604060521060703020f160203070b032d130212120703 66
    0xb05940711300000c90404540d8040c60071400e0980d1a410700305130000e401414140c4078101000ca4084a005840540c00011300500170303140c2c2c0c80030405095000e0b0b85c00a00180d940300c0b218182c9030080c0219804045031050492400100744460710194000b5514ad5541d512009422118078408070b03101c001905410741c50404500340309030050f0001000303c002c80c0a043c05d0a030302c2d007910740c1c001c9015680400305240040246540c01d040502c442a00e4200b164046014251501500495071701c44940880549060829841d03890800c2414001d056410f9191030324610500b00c0105144c0055800c280050302c0443d0082d220400a0703000800d00c410034844047c00181e960041004010680d00310b0b05a003011032a0050902512845200c0c0100303083c408015200b8040031504d003000120000c01d1847c0c3c4003500c90074100c128010494ac055900c5120b13508003102d0f07001020242500c0d501604240c1c1d86403102d041e241e2f081c07101c20940100442418083c0c0c81114180b40c00110003000340b00d100390354032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 815627625 1250 815626375 815626387
    0x1003080403061b11100e1c020303010f050f0616020607080304110907050301290d0e0d0201150608010608060a051e130501050622120804241202071a04030203 69
    0xc03d501880c80742c50101000014030300c2003540800480c00710100c084020300481d007030840583d0390b80342c81603a0300100e0102d003000c08070310301499001c00075605940c0c81c402d00313201295442c01042025000403030000c0e40729104002519041c03403a00221001c5078030203030503a402c0555940710325100d030300209c0b0300703441a040c280f6201e00304d4982707119016809529402c006046504000300030003074445580302d0035861074078008000710780100003043d580202500007040c4000c02c4070428403901d48a040700a1005503017000046200d0020420b00c04c0c003038540c41e03540c0d0002d5078644203080f25104800340269070030004401012135076480340c24280640050881200c58070080407404d101c0464606070071010818940030043c8403603510b110460310007a03c011241c80380e00600708441c0c11424015400b95400c50f0400700c10504011513240a00222400d116950301060b000c09035469580758516030b0ac1000440021406132207440903400341c000180100c0810301c0130303a030141c180d4a2480c401c1d10260050b03070000ca85 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 815628875 1250 815627625 815627651
    0x3011d070c120905031e060a0b040e01021b10091502070812070201230103051903180f0905011e0b0f04031b031101021b060a11060712050c0405010e0603100308040306 73
    0x91040c402002c01b00901c80c1000760102c3c90b4680300d028100c03001094841c04600d403a07a0300c50b00403c0944007440001c6503600d1001c0300c0c1905a180300e801a05403409200949a041da0462141800342c4e03800c100a0259007902041c1c0350029805414221403132802402030090b108000c1504030301c030b18110340000600001d003080307003a00100226001c11440d03a034040184001100484c011952201f2403a504503031006903c0c0c255841b09580f0601340c4640c2041e0000210343c2880c0d07005000b1190703a080200504c0c0d80b180c1d080d061074070039065100e4503002c10171410000315040400070586804503d1480d82840e469035a04040340d070365182a1283c1e5421900300b40144008542000035a0500340018860113802c25444003240d2100740b2030501c20710b0041101d2032510300818480c0a80c00458060310400c2c6004803000d018030b01e44148110b40903103080b0008006074812000c4800341c50058448034051800b2b80208180d641c0f00500a100215400720008000f55610700900007a42c1305500c0402d0603c20104 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 815630125 1250 815628875 815628883
    0x1050c011e060b04050a1203030e1903080c0408060708070504330207180207020d0213050f0703050601121e02031e0903090a030b04050a0203100b01031103011d070c12090503 76
    0x1207243d020408010802c10390b03070f501600404035421310341072031840c134000c1c2001c2d001802803010600702401b403078282c440b07500342403251401e00d1031081d102e80d8100e03200c0d41d0301090b81d4061401804119808100030030500c501981440794070040602d041854240ca1f03000c0041007041d6a401002c41c0000c1030000c0780c1c00c4000c1304c03500042c44032910081c009540740c0001543c0302c18804c440c60304d02c1c540c00184101592138902c00808101d80240034065130882c428100780003010200c84520300c4c0c800d011701089105200340603407070080c1c0d0f0582d54007400c030181076001d100610491301008200c2c82914040c0300f2081e5a40055441900b0304250640a041c0a00c101e0b5500d0340000c0200c8584d0700704200b2003005c2c0e9205809402566006000c04002d0f51b941e2078080c2c41c0690300c0801a50510410340d0796612802503407c8008440700aa80c03c2c40b080c403c403c0da0a44900082c09088610302c600300780c91950641c4941140d91003680d03440d2140d034410060b250002400c0c13a035104140000c41c000e00a00050400700 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 815631375 1250 815630125 815630129
    0x60902030f010c09061e050301050603100b030103110415031104020a02030403060c020c030f1f0b0103090c03080c1006150e010903080403050d1b051c030b04050903090312030c0405090601050c011e06 87
    0x200105001c100791b05001001440140a0b0030f02c50003011011840c0d5111502107030020301680007005a481d41c481c286451910003a4441c4c070f11441c14290310440220f4000c02003000c4a5026080201d007807440820040603400888032401180320521001000c030303000d400342c1140350400d6000b03000101802d005050034a051391704070a000c0d601c504c41c0311090362041c041c60003881d1709401d1b0004240b440d21004170040d140c400070242590f100c0b0f410110900ca079520051491940600488140011507241e84084c1c540d1032195807401c81c082d0b4842e081c454021980b40724150014900b403030045880f544c2d46070076608580c1087e2420360041515196151b0030000c0884c01c54000e00384d04e02c071007000750303078a86e0b5959132001041c103041000544110a01c0c0203400103409254000d00501981c505149031507640d4012514a82c428030611a04d0301042c054001202d010f10a0868540e00d081c0c100420f014010030040d003614100402084201060082846424480b504c0310304650101d05100b02c104082e00d440da = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 815632625 1250 815631375 815631407
    0x10b0714070e040f0204110a180515040314030c060a0906150510031d010905010b0f010f300f09031713230703140d05030c0403060902030f010c0906 65
    0x100140035030601c2c807101c00e03031203980200d107185008401c1c40802d0160900100e018000c50010880c1740740142c100c818214502c202581d2088007a40d18020008119400c003484824513008100034004245101503616000520f441264a009420046145000402c54601c10181c0e0740d00711700007c00409004850900c2c000900c4140390300c0c1000000360031000c0c003040349800d1554901c00e00062410f00ca00303104080340140020081c240720b500b01203005c0d140c08501e80c4c0c412199400c02e040598010a0802d41c55246555580300c00c0743d1f00a043d62059940e001340c0030b12400200c00c0c40141740110b008062402d8051000031079203807054078015024000f00701d05021310300c904800300b02c80e01007040c0305406d0054104020343d0803010307a010b814500701168a91103005024241e80401070003240403148111150510441d40d081c50b4100c001c0f0303050b000c00d03240254180010030040001c18110781180e4590b600040907142c204800b109003c0c03c6440042503840072480103c000c206454001c020240d18140d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 815633875 1250 815632625 815632633
    0x11030108060a150e0c03070908010e0c0a0b040f0b160c030305040e0a05060306060f0d020a030c060908010501081b03012301091109030c122518020702030a060f090b010b0714 76
    0x4000003040011030003440105000c402200047c41c4e284141050f400074200d0400810103000800d42c0c040e00c0b10440c0038646d000c2c01d680c0500161040403c0104e508491603a0440316110382010a0040745a1150b4101410780c080c052040021801740314011005603ca0b480d07a6964900d4145511815000100080b01082c034200c1080031a03200452030b0355114508544007a1300c1c0c1d141000084d08141d080401a41020002801104000c14041100309031350494841c4200d840e0b5513500303d030a8400074000c500558101004c05000100c00244032580c40343c00030000b040b0301d0302c4901d103030081e0980b0b00f14132240441080700410003c4c816118040b00701800c031100f00e280c806004040fa6458802c040e180c0d0042d0100d400d844d214a4042c00026001240000b03401208034400040e0b50f410303115405030302172500070181010780607011882111085980035000e0501c011560305c07850000c0065620188640b61690881400030b010780411501a0080d0f041c079545450340c900340700c983e80e44100107180b20b6600c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 815635125 1250 815633875 815633879
    0x30210050a080a05060d050a151401030c060302031506030709150e15031e04030c05150601120f0b030a032f07030b13120201140c040f1811030108060a15 67
    0x81e00a0480750f1105580e40f000c900340c0c4a03140031500f00129600064000c0c0555505801003024424225a00e00c0b2910f105024001d0240398141103201e00b07210080c903c035504081000041d0098024561105200f05021846902400410202c1e401240c0460000d00710300d9062000c80c511803080d0805010701d10700204c0040642011411030855102c1600e4000b90220005000340011440c9280c140350b80608229541054034000e042171454040c203d5149c0140d02c0030ba6801c0d440d500c1403510805c0140d5075110810b0f01c86403148000c0900c40050903072980c8501c0f80b40c0c8951800c11010300c0d034500c0f0f540c64441d6a5481c515407040a00c04442c0c18001002e00d021036241d0172000261042a242c001d142210b00fa100d083d102808030f4030906004217100c1034000b460b0500c1b5019440200c0c0c45183c0d00707180c0c0703540e40d0ba056454000d2285000e030008858a010044c8801c610b20b28414620b40340700e80d00010810014643c140d03458009038000f000e160b1103207080144910007800f600002c050f101d00c2d00e00b000c0b8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 815636375 1250 815635125 815635127
    0x71106160507060605060703200105061807030902060a09030b0906040222020d05040605010905070c080d0905030903070b04060f0e0d0f020120030c2503030c0201180609030210050a 79
    0x380c8090400ca040000c003203204000d0106a90100c4000c000080c08030342d8440e0140780c043c10b42c8401116080303214400300100300d9221018040d0900c15400104054148110b01103098803070300b0007401020405a840b105000141c46e18001000841c1c61071b22035403101890f516105407501c0c0001d052510603006402840016100d0350300c00750032140c041d4081d10f080c080d05928400207000300100d029015085c10113102c207001407603201e030f0305a8038114028000c2c4d41d200d00302035582001d00301005000c00300030007207200101f00756400110440d205500f903a08d0501c014001915000960f00000407107034000a040003034030380025200c0781e80d0009051695031441700e0780006003000400c80024050300001ca001c10116172003044201c0e040540a492103c0031070040401a43e01c1d009540441c0d031a210f07104003002c2442c1d8a8924000014404062070b07001c5c1d003150b41c1110301c0c00c00c0000403814407060b4040e028060418041001c054245c030399840f81a2899801080740d00811203209205208080100c4001e032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 815637625 1250 815636375 815636401
    0x190606090b120711030409150501030903210609050411040608060103032a0515040201080105060708070f05010209030708060411011403061918050f010e01060c14150f071106 76
    0x110030480c2c00c2000643d40d01c5015641c01090303c0b1860240e0200003000329062280758454400c0c0c038100b44100c02e1240c0c50304019000c4500d40c7c0c2c8040d020a2202003140b1003440e0301984d800031410345190114403d950b0315032400c00e45100740e80c1290394804080544429041a100703440050260340010020740d450368074050b044042006c8011410a401ca151241d00c500008515918581c0041190135586402c4044054010300ba80d049001031a404000250b52500409032140c4682012940303180c14001d036200708049103004d40440721550240810207207503900307112031030050244100ed468940b901d4a004c0609030360703c1c6c21541c140021b060181d9100c10100c41502c2d8080403da0b8181da11038041660301c0d00b02c03d85c40d031114a01400031415804040070580000e802508419411030701b030390f206c07620340c240c80c0d509005050000303402d2034a1801181c0441200110800840300717135000000d20443d15250954211441c420000d89102800b9480c5e038000001e0105410400141c0002e041003058030500d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 815638875 1250 815637625 815637637
    0xa0e04151a090f100c03030b030d1202071b080304170307030903020409110618040f09021012021611030f0f0c0112020c0f0f07120c09020c030909190606090b 69
    0x41d00c00c0100c0e400206490f4101c0411580000810048400c1c40b030b0074008122410002e01140024100310801078182800581084040c409417110500840010107604c002e40000307078241d8075118255209242002c5c80c05415000d803030400c0c007943d40d0310706180517490085040e090104a81e0710400828000ca548040e40d5402e590303041341c001c031300d50352075090144102d007000350110307449100080c2001e1550020f104008110360143e070240308510104181c01c013101c00440c4065088503181080e8184a80325040511000903c03010044c2460034156a2000e00781f464841199440f0405004a078581b80801c8120310b821280c50083c0030020041e0b04442d140c040214406051007079040100b44a520103805464412405070304461203a40b0201c03005e5070358070f800740080d850383c05410404541005140d540c038400c0c036003005090503803910f82234448000354042e140300d85140c007051069000ca80c0d280c0420030b020708030041c0c61484001c4500c484c4070843d8103c1c0c0c08901800103000c4200820f00400c0b0545e50 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 815640125 1250 815638875 815638919
    0x20303010b040e130209070305070f02060609040809030304080d03020d0b061c0f090506040501090c08211308060703050402150c0a06091a010b070308010f140f0102120a0e0415 77
    0xa0b21340303507845030842c01c041940d0000e50001c042410054810340c19800316200d070034140d5410400c0e1044420690b1038800c00d50710903400c03446280000700411510001004240b1004d02102c3c076199940140b18101130101084100181e000190103020046038020800c0010080711110b203401d440c29800c050103296291003145064035410130003003900c0c030759018482c3e00360443c09a401c14039040c5011030003010110070844035400c0c280d50200305120f0015a051560418080700300148000500403001a001800b51007840100028041021702051048a003c0c14854402040c1406d0903c10401103250f911117100d00c00d101804084032014000402000e90307600050300103680c6209040000d241402046011111104107000040d02860b43c07009241407402a0358120340e0341d880f02c0e4601c0300031010b440341010400e80a899000341e4a0041c8030080301c0a0140111610b000078444941c81c07a0700006190742c0070030b0b03680c9010b400c107050a006100300c510106650040c3c690034041e400424184210180e1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 815641375 1250 815640125 815640149
    0xb0d0902030106050d050f07060503090304210609030e01080c1617120c040617040c170715020a140f0d111212040201030b04050f011e0906170d020303010b04 69
    0x1506548083d030011000d014040c020401c100781d1030500b942e403090142e0b194821440b52031000035146102c1c0094034020322206c2c0195242901e80500880c000c041c508200b0309010510b607107400020b02070f21032a91040d1003178503445442000c0c9000075040890040805945183c10006030503101000e1154a403045d50020b681c429810076510049107500844650320101c0d50f0000a01c003254020a01030801c80f5020303039401100200205405d1a010300648009004181c041c02c103000d8406c982d0201c00e05410b900c81212016603031207440440781c0e035090300d005d405170304070b039100909105580d450f00d90b07908210401071010201102d02c2d2544d43c00c030070001e00100481c0c00710710b00c0500c10504c843c00c20031440c04001c0c1e032030354000c0d6012201070310180c4d022030200703141007100e8046003488c0c02141d1041c94010422a04c0e84e00e001d032942c0d030402802c951a0580c40c8500e0000c03500040c00c0c8650704c050180d102441d0b103c180d0505d50710f407410400e800c80009560040c40100803500480c400caa0035600358013612 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 815642625 1250 815641375 815641391
    0x1909150c2325030203030417070b01090b01021c03050105010e0d050c0918070807061d0a030303050603011d0c151201140604180920090a020c0c0d050114010501090b0d 73
    0x60980746802c1c054101020b42ea01c90b05410f156000001e54020f9010300110544080c00c2e1020684903c40c048000f080d516103040108116407040d8085c504000060040d245500c1c88880d240345507a41448000b800b180d07540300103001a59000c0b04a4407009021b5800300015002a205d950342d0340c441c6d092952160f098100000c5803505618040b020340f25028007121001d580716510582c0380d540c3c5024520000c0c444168034801081c41840c815544400a800f40760700b2030035610b00b00e01618009000070380540d200c0c40020b203014130300c5000c4c030a868000000b82c80020061810400c05040f155020b035045c1c44203003e110302000660000e6811504080a00c910075034505000c54210b0260390721040d481c001141c130181c3d100070550041c07590584210b44000c10300c0e5040c55801e100850b544400741d000310040001442c5108903500914805111808031612100c207000051540c0000307071000c035002d9444043c001c07003510230064994050402400d000301c1031414211307a032000c1d008082207103070003135151041 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 815643875 1250 815642625 815642647
    0x60e0606120112020a0e0c04140d0b13020616080c0d0504050307060e010c060f0e0c01110d050d390804020d0b070e040f0213091505091909150c23 64
    0x508011310070503695080d1b9240c04002e000c51a001841005015500d0f000d044000707140c001c0c01407407a00d900007031818040e202d01ca0b00300c13040760b02080101d8002404200f41e0041036998110000076511920b2080d40e01c0301c816582d10704140042c20590300f80142031105004c6590045040e00641d00649417014404414400407681061038403400703481c40c1d28041c20f800c1a45e81d00c0d0410301001c41c841c421507060b624808011a8045440c1014080c0364000d0540410000d00c00c47c0117103500100700c000031809024208461481844e032003ca198a109081d03954901e10348402810f030301080c403a007481034241c5407640202e0f143d0b80c2400001005c440070300340000c40c0035000d05a69410400c000e0010080e01c10f00784100c0c0700942c049104166428207001c4006104900d50040f02c50584514580e1641d0501d00020300131700b180301034519010105c4034442c080d004402d07403280000a074060f90018040a00d03c044640480301b4000300981000310340e0340000210b403445c0700c1c0800c0062030b00000c5139444e070403240 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 815645125 1250 815643875 815643889
    0xc0c0a0506090d080f12151014070f0803013203150601180e0601170c0d150b0a030f0e0d1e020c03150405010c0206090c062b060e060612011202 63
    0x9a80e011680c0221b13540ca45907444990390b0b1310542030800c070307071149a200c02c04014860b001018148000f910403084290402d501b2406400c10030300c903a03003501004800e81c1d035504958009810039031741017031944a1480102c940c441c00b0f2080f001c40d10b008040510714000400d44409424481590b0904039001050031a4415a2400554588541c402518035114a201d54480905031b40e082c2c0019001c03500940d19103500c622090003000d00b0f07118249890101305540002d4549180d210100d42c2043c1d1001171a07801c004000d14142440341d400151001c290002142140c91a40d40f0580680c0102d4220002c190010110103815031407040203104144508022460300705071800464041c0502c40c00c400c80042d102c51000e002380d2042d402486060b01a040880e6500d10495006540780c0c4410184c0c1051308004008102c03080c000960007640e480400c803060083d000820410032800d42e514000c20400316840d6507250080c1c022034a00d407415068141012404106015200b10010944000720071517462036 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 815646375 1250 815645125 815645137
    0x501050f1605061503191e05060f100905071d03010209030109140601090903020d2f0312060603130803091018030e0a0501142a030c0c0a0506090d08 65
    0x4107194849446030702e07006840d1042a51014810251891007441034900410286e41826080309403100c80400303070301d440400355a50003140f07070302d480e840440c40003045042c0603041c40380e50140b48c2d078501421b0481421205c080d0560015400711311700b40900081c254417641000140c102040400c1307940b11141d00190092242700529030703256107050003520820002d003100e990551010760a07207905070307038030000d9100762943e160009005030000c003104680309004900240311b0b042004144548809018409806da00594100300c1240d030000c01c444c00d104191a24540d03000030b0640f032803410343c20038080106141c403103580d0040c0303a80c1000c000200030071410080d02c0000700341d5260500540450b0180b07140341146402043d80018001a81d000c02410071402038401c90b4410703546d1402c4048625103c44150b0048031460305201d0b6460241041c142480035a0013811003154003440d9035544144100f440c0910b41d000290080c89210010421070f5034030402e07101c010310162510f2940441d54500348600c0d114070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 815647482 1107 815646375 815646397
    0x11817090607080a030912080405160f18020708070b040c080604080304082b0e0d0819020a05120f100909020a140609060403060b0108130c0501050f 65
    0x601c004213042a0300d8a000a44540640e90f4034460850840c09000091a03610922007404410b01a00c6810f480981c00d41c00c090b0f180201c81246100580300c1c140100103069105914180c00d50100d80d02c1d036038031001041e5188154605403401c400300769030644590050780400300d0349800014096000e00e400c0011103085a803250b488401941c09011350f4141c0041d811410f150320728152624841c2c40d0001d85012451784104158035252054038014041000400d005010084c1040c1c5400c0ea80300da00c11101507a41e0341e054506440c24403a80e540c0c1c042e2101000c08007d8107807504824039004040860002c060240e8504030b61054901da550042d41c058810308040150400203000010561406859941409410310000340d09070050380c0b042e50016102c1000d800d0f01d40c0d00800f015880360700c4c804c50140c229103d03119a40309c1d510500540741880400912503482d00e180c001561485468 = true := by decide +kernel

theorem cover : BRFrame.Cov 815467625 815647482 := by
  have h0 := BRFrame.cov_init 815467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 815467625 ≤ n) (h2 : n < 815647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
