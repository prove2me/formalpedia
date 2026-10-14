-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3737
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:32:09.337987+00:00
-- url     : https://prove2.me/submissions/f08b8218-cc70-434c-9454-a70f9b86e67b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 671942446 ≤ n < 672122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 671943696 1250 671942446 671942461
    0x606051807020d032016022701090f020c150412030c051b011806020904060f05010c08091933050a05070f05070b040e0108030a050d02090a0e070314 65
    0x31901100e60100503040121041c0c001c2c2c1c0a90700111180e49803030003030080d00481482100c0142e105000d10743e10751410101283c00c600e0051607228113849a0400c8440e00e5255080c864141701e03042c003810750b21903110440906c051440c1d074169080d00900b1402c964006000902100e0419402d4070140e505644020f6030025040c02802038442e03031540c580c1d0301d900d00060f540703074000c0460350301c1c1d0040d580c2e540303918600c0f84680040b0b1504020174012100140c2d100301400402040f15419401002c0d80d902c020b07804c1006070703005181c50f203000d6040080c0396a110f6001000454552180303803442400e464144c80450030344186001d54918082903907600f55801210015a0822642144201c000032000c0102c0414140300b14040d110181c0f040351103901c00740341c07580d8150400d642130708002c000d203202003020400c000a40d00607500600000001e10302c1c2014075503004007644240b0300000300c801d80010b1840025194041000010402d20b546003000d41050400240545140c0315a082201c0c401000304514 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 671944946 1250 671943696 671943739
    0xb04060b0f090609062e1b0308130c0b030106080105030c1206061203070b0c1e031b0c2409010b0a0806070c080417010207030f1809050a090f060605 65
    0x600308020595141951031204210801d0002082c468200000c00b0448040703124000012440002414002517406c1c0f21070750050070b0801c010700b07540020f82003d0b16134000c41d0f080b1031400d420541c481081c1681718054107107200e84c00d030741c0d6108101c8503400000000f0160352000740705044c0c0d501101554204034805d0100030a04080c00040c185030340020b00882d029203426003142d81041304180c141c0e418040c0d81d848034490030344103e5248c00010000680c050121707404030054084101c0e00801182542000d1202c4001c0050000207841000c0c0b000840d4000310740200841825143e090341c00c4040c649251004500c101401e64050034258240b24590350107140c00418601070320f02c0c8400806450740c60f04411100304d180c202054940394420803020900b2107100e81c02401c8900c0850015a544005245c001c04641c1c450b10f4603000c018003c0449180c01c10380442d0081100c86d421000709260f00e0705e1158900070302e41f40c00001e0103049107541c03000070080550000da048a030120b44844c002070498520031103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 671946196 1250 671944946 671944969
    0x323070b09091806010b09130504051b0114220302300a0213050601051303030e1e0d02040e0f0109030309050c01030501050d1509080307031b030b060f030a090f0b04060b 74
    0x2000d0304411300500000c030b00903015201e10031000700b000680200d0a001302d003c4401c140d40036103890300032020704605100d5042b001861164203203080d81000d200e0034941c110b240501a1402c00e4500c840c19120940d00541c41d500000d0f41e001013189400844030115548580e41d044942c188400a0403c510b0b4200c001140d2281d816070090120201d2a031020380744030007420000c150303a040c04002d2060030125195010644080d51182d191280703910b4500080003400ca401082c0c07080e08095842c00f03840b0319100c1d407100816140d81950302040f00188020818100701d62004501c07a5586800010420b00da81900840c0c00d09003e0401e0307840d01e01402c0011001d0303440034084c090304050715400d40c0e00011015640c42c07111b4200c51000289000c0c190760b40e084c450348103407a4080001d480b4201a0a594950400b1401003071050074200064500303a0080342c23440c01b0309824565805008800038200c2c400f2604502d0101d03074894150700f641b0540c1e02c2d15900516003902d003078807214681143c85a85040c01001d005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 671947446 1250 671946196 671946241
    0x81506040e0613021903050a06050a0b07020d12020c0109120314071109040b0708060108040c0611150109020c0f0604020901030f080d110301090b190323070b0909 71
    0x52520741400d5040180040c090003042d080711903d83d000c05400601e02c0501021490306900400001100c60010705840c4090300c407a01c814540001045190b071081c0d100000c43d840e0341e00c050345410403400000d0440d056905c0281142d00048019440f0640c0031510f5a015003003600e801103225120303000c814680031000300040c041900950701e524440d02060280000b1449001d00181800c600d00100717040502c1502c2c11181d801e004403d100e80c0c241c002c43da00d03a10003030a2030101d003545002c0c0c8516903103e000b845400103100300543c6a49411000f88a00e0319814590f08001404d56502c0e06035000940c04001c040d43d1902919842085130360002c0b6a180c01503800500c5614180d0850310381e10a44100a40b003282c04220411a91088070900d0040c046100449015141c9a40c503104003c0d003035a055805081c4100c01c4050f0319010f1000b942180010344e034000c107180700c2d44201200421711000c42103217000038030700c20aa00001c5144030003009000413501039840041c10f07221b80c488201c04509100014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 671948696 1250 671947446 671947459
    0x1508041119030c06050901110624040902120f010e03030c092115040212030708070b0a14090304090c050a050712020c040f0f060b09030601090b130c0f0815 68
    0x8495440c0c59074841506401071440904095560303030b5074800e01c445035030210010078004a030b584400d607003216a0804482c90300d0040d010916100c40e81446126280030600611a5181a1040720361141c0d84034400d49903002e0021500d000e120085241d447d4810303501d010171503007811481c4080c8070010042e81d008040f15210300d424003114a041010200485601c1095880a100b042030a0901000843c1c0c0c21401010700903294240bc2c014010740c2c041052015000b07600820040c03001910000c22288103940141c04254203454401d6408040e1840b10051521480c4c0101031015901011008004664119a0401100a6642090700d2501541503c040802c00c280103420101700c000c0e14a5240c1382142c410f940a0040103400034084488907000c10201644d201212080034030b0794812540076002c5c80a15604001500700020756500e0140600500107890301c05c0c0e8212038441c0382420403032916144052107100400700f0010448400010342d40d000842c40d81c00300394910300444040260a1024122 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 671949946 1250 671948696 671948723
    0x70825030f0534030e01140d0203041103060117060a0506010801120c0515040e150a27090f0b0f0403021011040b0706020c1203091509010e0d09150804 66
    0x259226001102c840b030120b0030f10710800c5902030403580441d080398102d000c1c070b5010714001d040c0103200301d02007003655061000c061024002d4080b038005650f5498510200943c0e00c1d0781d1440c09940c4510a01600354040c0720b00c2c00007040c000d8000c14861074a801840c03c648440d0350340100101a69001ea41e00e501280600c0018060301d1410300e070341c60406014000d1209040ea4810105011b401c00c0c003a103407840000800d0030301003c000c4020850f00020320507000c00c81001d4030360000b40c215000e44192180141d03a0f075403206030600040425080c0c480000340800c0341051a050003202407000190484a8600341d45c0040c0312116040c0c816030145806a009214030f05c04044420700910840140102140b420b1000150501c10800101896441000050b03261441140b845240c031220141540d45036806004001001800142c008480d008041d2100183c0d103030080b42500400c038520048105020350036a00904903088001d40086907240c40d0146020300000200300c0d107a0100352030040c502c4140460 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 671951196 1250 671949946 671949977
    0x30308010909111e18090c04021b120d0606051c0e070b27090c0a05070303110d05040c0504020c0c041a0d030f02190308040f150207082503 61
    0x401059481410b40c1c42c500402c24000078079081400c40d1110161240c6403694103142017420203000c00205515012800d41408401941c503000408550b6001e44d030f000c262042e480e0349a02481e034140c081101079813071810707130010086401d90002c860003044a00306400000d200e0301c40d5003211416286d903006400003446000b1983d0240410b1189404903104000300450b40f052100700900c0080083e40103600b4090b02c40344009407014000310203078426007513801040081001c400841c3c412041600c1c101e5981c1c2c5a603e400c0c0c004044402044030341c0980801e62402c2030403260b1000c1d000d00d00851101d495a9911400c2009a20402e51007410380c1e00450503041c094105600720590745000141b981c00c098604101080c2c07140160201900060b50901e20034402c5601400000c0010000902013102800316460141402101070402001e2490101c404800c4c400046a0010303a00c1180e4000e541d602c8103400c0c20740d85a08004405070000e45c8035202c404000101390000e9241a62503121910200000311 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 671952446 1250 671951196 671951201
    0xe040503071104110a112503141e010e10180204150b030c030a06050102070303141b010e030903010f0b0d031d0316060807030c141b0105090a0b0f010303080109 70
    0x10000fa0455200c980304203004400c18090000c8840c542c1d42c0c040c6c0c0725050700400385409000100045040400e45c0c48842d80a00c1305842c40540b40c201801111500f0000d019528102200300786144880d002d81c8911043c1c2410740001300300c04005411100c0b5078280d942d5640031524411114101002055407000c0182010f403c04090f10540d25090382c0402d41d60080c500711540200c1304c203240d40800004005d5602503912444005c2c050070301c01000064110742e1301074480c032801005039414050104c0c0c1055400403840409826a40e000024815810380f42e2800780d59420a016081c42035003020110303807415805108032403912900a040c1c49000c006601c0035a41d48100da1903110428401040c4003007a40c40401103927000752a021000c0b4501850081c000300014806400d400070942804104084247d02c8542800e0008c8480e1129594008007841d64500d40c0c010584a5403650806003009075889021428014080c09180802210760741c0049040308803500b404000c0220785120014004081c00f40e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 671953696 1250 671952446 671952473
    0x50d020f060a09080601080a0308040602070f0f06020a090806160c030507170403030f1d19030209010f050906030a1a0601051b06010302010f0c0b19060b130801060e04050307 76
    0x40c015041a40042010410a0b882000c8072800310b60a00c0f003c12100008000260041000f40050b001c5d40780c19a500410140e0042c102420f550380104000080c801a41a40d0310b140e6800300720300c1000445854410041d4110222010200f8508880040c8884010600368406c070400c014401075a01c1d660b90a840c00d00c600c0b04190100a4240071800000d01d01e1400c0c01d131a002c58540984c0c80d07030b01d1807900400ca114030020341c0c02001008809007145148554031441600011101e010748030b840a000c01800c0b42680e070002c0d40c480044c00000450107a14003029055400946940c0720b2583d405080c140c2d17a180c0450010030040e2104050b62006080c000d0003600b00c901450442d00d080c03445040400110b84010a07a661500440010811903800100e5500f4641090500300c00a0b40162a19032500308001d00b030301c2d00715210004050307039818554401000f41544042140d10b8460310214145003564034003400100358a1b02c800490001e41304100e845c031640c3d008005515264855944010340c5054 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 671954946 1250 671953696 671953699
    0x20c04090c081204030c060e13051503120903070e040f03050c0c040c020f0d080c1218030408060709080102180f0f03071401031a06040b070318060f0201140709050d02 73
    0x1c035400400c4020080c0300104001445100c2c25403214194206404610303001c1e4030040500c07419003c09002a100c50460321039010211100003010b0391140030361007031080300700c0c41d065146c02242020725400050801a0807100700c184c1c22204030a45642030710640c80020b6501a051030240404000020f100e040207150002c0194241e402080700900407a00303032240c034400d000160300420711040d01d407001000381c0038600440c2d00d04200c0030b0520039210f004500c65842d844044680010015110b5000c9110140b901c00580007101d03915641c3d500840e07190315082d00c2041c005901101d00092144050007540c05000612007007101c1100308008009501340c41d11001504070800140304c0f0301556050200c50300418080900b0451900e070940014100d401895015400c0385240714450495144c060590b02611043e40416030307240c04d242000d985607994001d080c2a0810415404205240c0c4844906030101c7c2c50b800900c0001c80251404518ac801103d9a500080511104101d6840d001038540d882600 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 671956196 1250 671954946 671954963
    0x80309060d090203070609090b010c120f0903020603160815210c12010b13020c032506020703020106060e27130534030f170405121b01020706020c0409 66
    0x7250f010034100b0805500c0000480c1001004000c11a254010814020824a402c0d100c0300281c0d034509221004440c03040003041b540055010f059400f03140500c0c0910f80007002c45072030b850120004a820300c0c411000400083ea42404140f80720407020f0204204e007030080145c0c890546804e03400c0e1088603540003000da248581042c560f01901c5100725180d41400711380010170803000a44c1030101384141ca5100c524010700c10001218050b102000352204274a9400d5002024150341a0742030001440004c00307802c0520005090080680544c0054101c54407a240d40384a00042e108020500301e042588145110340c3c606040001c41e84c1e41c3c0c490741d011004450303003c100c158a0f1200d910703208204401d0b4907800790110201300c010380901c0d40c1403001c0ba004150744451a085a46040940d0350145004080284010b600000c80036a4010740e409010050610b00c1c044800481103582c0b503000d038041410600320801230341059440850000c2c2aa122900107003c0101c142081c0002022008003c0d100c450 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 671957446 1250 671956196 671956211
    0xc0b0a110c010b030c0a05010c11120d120b0a0b030415021c140901051b031e0903090f09090307020f03030909180706031b1107090612110406080309060d 67
    0x40d9114040c01994004600018140d40c0340c2082c5031828649183d03151041070480300811181c3e078890b1f00010841da2220304001c004951901107481c101310500719407600d014900110144550251944411211450050040c4bca54409100b40c00040b400380c802200740c10800200444c48082c290f41d161407403044018641441100005448441041c16200d161707182c0500034402c508121540350032006a20013004103061682a90baa0070311034903641c07030002c00c01000290b010700481c03145c80000111a410981146458503d681d1030f50301c02d000d44e42c8140080d02c844243c0341032100d034462040710000300861800b0615001c2228580035000703c1c9606200420040095454090340b06006004202c0442a83e0010480383d504201a54006804141c0b0b00030f0003c140100380e401d40c0840040c141014036038134642000450426200e900400724060404000045640c180d42101c1c08103401440c07040280040c4001b0002610414030a450307007580107111403000340c5052001032400a031070050000c1c010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 671958696 1250 671957446 671957471
    0x16030f200901120c08060f011707090519180203070501030b0d061b0f030912141e0912032a160303120f15030303020a09080a141c0c0b0a 60
    0xc01c240c00c0350b5180c407150303181201000b41070741410020f03100000c040e20740f03803800d00e011010071001407043c0301808410380c01c900304401043c0000b00160500c01014011440c0240c3c0c50800c006400c002a1600344c80c00d103464144502044520f459503a0040140c000c0c00d140100440c042d0a001241c3c0c0c0c1d004140b000602c00146a0f80300c0c2d007540391341d00848003c5012231040d020744012965582002030500745149400018860b044859007043d075810106041e190a4200703071014054002c9090546e050381c440c1c0903010f117144000c1c100d10402100d9110000c188004082d480740a00e28001a01208141e524071132045c103c20b9400030300341d6510403142c41c4103011001c0058070040e61f00c00e80118609113001158030019008030391000c05aa00140309054400d01c41450410381d40c4806400c1680c04281c8100320740c410304000d801403885008580b100c1c1094245416911401001da1b00940700700a031040c503804c1540401d01c3c0342001a00d600442100a440301d04002030014001050344c1e90700c84030400b20 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 671959946 1250 671958696 671958709
    0x7210e010f0f0c08010e1b070609080c0c030c040204061e0201140a0506090c04060816031808090a06030b030709022b1508010b030d05221716030f20 65
    0x702c0b844601080c0b4001020010340000d074184c102000c0f4110890801000646605900841c05905140d1540c1d42080c1d06190004050b100c00c0103000b8a0002841501090b0018007a100604100c081d500000d007210204012803040d4490341c00850895000109035440c1003510010310480f900011411810004000d20301040884c0c03404500c03540c0e142030050f90700740180069803000b507228205241604055001e44880001400c1084403a0340843c0c215100d44250011b036107010440064203031800c29860320038480c0d042a8242801200030300000586944680036a0200b000083e02404480e420b000030356010350300c00885050790985011081d03040d081d404405004503a54184000b6031034070751110355040c001d59940705038407681c10801040780c2aa0041140c0b00d68040740d00307000c0d0780d64116520007041054400da20200d45c80513014005000c5000c8008141910040c200fa00e122aa000400b03181a030098007000d004400c0c81c08444002400803550f00ca614181251108200c64844001968 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 671961196 1250 671959946 671959961
    0xf3c0306380915040e0702030711041a060406020f120403020904020603040303110310240f030b0307050604140a06030e03040308070809191802160204022104110907210e010f 76
    0xa00c80000602040003401c085e154a802030300328400746240034801d4031529040c0d0049003850384200d54920140b10142c0311f0400714540c460000e011075450701c1d035411020703490700003030005060103005060380e500c0d480c00f407070081310292a4010818901354540d502842550b410060003102490703550301c040340c3c0c602c4865014612403402409140c07010350520805079410501907501000403200c0d00341d41c00059800c0b003040118910946400285042c2d030900080c90250590320050b001040003502040300c81405c1d0607034161080650321450816602e940132400c464001c8144000354209101c01d00009181d10001c00c1081d0103041c0c92424000d41e107001070322118904406410412220a040001c49640c0d4000c8440e0400e015085003001d011480104030030b100410024450b1f40d0010f200944140102c00c1c0101404000c00710650b47d1801e80741250340d00346915010381c4605550300014102a00ca0032a12101d00340f1040300781028070034980d08501601c80481210303255500c988003c4440700e41c0348101c40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 671962446 1250 671961196 671961229
    0xe0a050306072015040317040b06040209011b081e030c030103020f040e01140103050607020d050d0906020c061905010902190818030a0c1209060f3c03063809 69
    0x8145017840c1c54007900e4201000c3c2a03030f103e017101208100205a640c200c02c0d602803416580540c1c0e40d1280300040f502603240075411210400080904000d06c100030b0702511580c00d03001151807440c880c284101605020031500500320040800c0144010309003140340710014030b4050408505c407040d84002d282074800350499490b5940e03000004000340300c01000305c90741181903070010f02001c0031481c030000c02521880b407141c04c4464a4980c01c1c0100034041d4101c070414003540301a40c2c0c1605200000c003041807140b004204a180c1004004a411446c0c3d1084402c0144007060078459408410f005540c03080000341005102c03d02c1e10425140088c05100900c0d21981c01e0362015410503031850f00104580e602d01d114001c224003006d00b80107403a0030190707151003c1d0243c03c000e44140f5003500f410b6039515001d624005c032085442c031154036072420b4088404030000180c40910041e40c1b249007817042200c50081c2c1810740d144c000ba5403034140702c071414030240b1034040000e0a8503000300e05000c940c012040c00b4485 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 671963696 1250 671962446 671962483
    0x306020304020312040f06052827060903020d0507080f0a1b05011b060b13060603050f04030923100c05210d1d0706020d0e0a0503060720 60
    0x40214078007401342c02040b00c905010103081c6402d20014a910000c20300445050007000076001d0f0001c2401c4c0c906480c44000c020840e650004014001003480f43c94110084280e1100300703083c3c02d4080b02c0d81a1000f80c90f010303601c01a582c0d02d1a0200000e40014031000d41da28001d030b020100d10b080041c008145254040c5004180c9000a403814030030403d1a50359114503000744210901c51030703a04c00701030340301010b0003608246620050b0a22400502c1c0c10710541d40c3c421039034940139400c0480c4d904010300715040e80d2000c00041d03940d00c00707000282800710b4006000644004003400042902c40072484103401103080c02284060510109000318008084070f804103440340c0822041103030800469a02d5003030301900307550a2115490500c040e000d50580800c80507200c21801d489440c01c031400e060354281e003404442c207a0380e868101a4554403040074040004030801082e44c2d41d401c04180c42400c50f84064010304d450760780d0796404c40f0b015801000400c01599400b0201140070b0701040540000030310400310 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 671964946 1250 671963696 671963701
    0x20d021203070c141b0402180402130f06080109050a0c020a080c03090612090d05040e04110d020616150605010507021509130b03280209100f080709150b161b03060203 73
    0xc500c03d05130401780544104c0c0100800501411826451545140301f0789001d07840c0c8501e84440c1c49000340701d0700300c03442c00d0180140005940fa4403070701540c101c88180c481005030f40ca40004031000e61700004158400740e840a00e0600004088030014000c03031401d0307401c0d02e09005101c00000c18962000d81c80307410200028040c46807400c814440110803000500b001c0d868507240100036a0001c10050010700300703042420450301c103501c50444001e20300340d00400241c0d444085641ca01035080600000f520041d80c107203440c20355010301c1d104207016214140c40340341c1000c4070356003081496000600f0040701c2c01000d1000325815101d2842c0d980d0150a00d00020610310001d60030701d49070030403100841c4d1002c1e0702c1c46d810880c4080041d42c2841e1858040d01c98800c9940c442d502c40110308015404081c1c01c06800310001030110340822040291041e12806101300d0703120f4003003041400b81c5070084407000d400170011680740c2c94003500b603006c01900c2500b409441c10740d9800b5030020044164029192142c00004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 671966196 1250 671964946 671964973
    0x30d060806010302011202070f02040e0d0e010f1202030c16080703030f05060108130302011b020304140a0506030711100f020408160806060d0303020712020a0c06020d021203070c14 79
    0x19050261104000416480d071442e0002040e110720700d0b040c03024003a80041c105051080504050f0039040d00908103010140307055500311382d141800013899001441c00f028030109984250700b0903064031013903a80c900c151074803088420000c4d0700190000318614010020a1019256154a0952140a401d0854a0307010509029040ea8511500b482c081403525080101d940e80090045410902c1030700c42c0c9050398000d1805a00501c82c001d106046001c000402103a0b03a58000010010368071990700d607440b060000c00512410310001d00955a00c07440900010321038902c40c02d80ca4402060042c00ca504410141152108960443c0d06036901c003a000601445074100410950211211040716030000c50320f03008500c3e45400002d4a00f84c440e00b0081404410703d84660141c659454001c5244001180ca00380c001e95920403400701225000300410740015210300200300e4100c40c2d11103070080c1c4a000500440e081903a8801860b44080c440f400d0048000b00b001d1580000800c0342c008003c01c0e210384480c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 671967446 1250 671966196 671966201
    0x1902011202030f01140415030b060a0501030b030a06020306011e180e13060b01020c060d090501180323071b050306010819260c0c040f020c0606090a1d030d 68
    0xd05a04180100300788030811002610301811221840103100e0a40840c0c00003502620824030040e55804403010044140420280030034064601103440030400781c0c2d10030054040c2c8a80e400d41d41d9150300000800700c0400c0c581d400569201c841490101f00eaa60f51b210140c03e03114a401c032a00000c1c1c01110f004100c0c800265006004d0651051200c03940c0c50000113071405204000c0c00180752544079000090f80d030b4020000c514410307500500b01a11180807840141c020984444291003640c01c2110442c620b9103040307000319070182c00d41e440700d8505e60305c104100ca41108185a09001001c20060600400c0d0182501d58400d00b90200145900385042c0425141c20710603000019290000c1c10701140b0180d800390101c0742198050010352249091446511101260108030b009994000482c0364100324080b4144804000841d400c028a00b9035103041401c0340100752851030513501100105141d4070741204003960207010820003140341c812107020116100c20746140b0242700c1d4408980324548107a00e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 671968696 1250 671967446 671967467
    0x301060c0b011d0a110412140705010302070b0c071e0609060608060702031e16050703290a0b0d02040f152408090307020301091101120507050d0209010908190201 71
    0x42c0783d2070342646882e0b40c0400c40450250003952541e9481c0c1d25105a080403030700b075a008000a4000722090282c500b003650300c41800c0768080e4100e0240351808034803980a031007580c0003150001380804403075443d4441c0d15404c0e0b012600582c0e1070050100288482d40d50100429080c5129560110302400a032400d9002d5400301d802c0182990401010449999400020380c0e03d05600207912a030f000e14100c1110780c0d184260b042c2c08002c4883c4500e024240180083c2c20402c6034460071540d500d82c04801e104010745c514001204d042042010041842c880050b00580076000c0010f0641d800f400041d40011300311481060910080d40d01c0744070103402100400c0c81e40c0014180c2081800c43c0312a6000110100004c40c16a24144070001000c41c22228040059685456010b0000c001030005410405001c1d1150101c0301c0c0010180d00c00185080003d004140c003401e81c2da1142c82c2810200506070700650000c00307610741041034140002540e40f60800c2980a174400801c14010803a200c8d00004000c1001c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 671969946 1250 671968696 671968709
    0x5040809031e0303061c0c06020d1b0c090f0b0904050d0905040504050d180b0408010614010f080114180a06090b0108042409080c010b0a080c030a060b0d080301060c0b01 74
    0x302e2014540e03140032080741d44c010401c075a02d0080311103c030f1070001050041030b8007030200c601210011401e1500040e016820b0862a292050160046100d2580003a840c3c4c4009165480f01d040c1005010300f2900004580340703041d40301055010058002c2100400e003121b0a0355260310100c81c0a056680000152016100c261803e005a190503150140d5500b10074003010104000c070b81c00c03410400070901806002d08481155141c0d280e03601c201e00c81c0603250900035065000c01d044404407496002d12119610aa101d4846a0340c42e071804402c44040e1880103403581d0414003806000780498021900584036a0100d04006895030500d1242802c0310513420605040c441c0280038000401d10304500c01c000d903146140442c040001160414000c4d00200340004c04240010540604070101908813042503403081d20803400040e0784a0b0000c0d500d03144907070199010382000c80e81c103010800c10b400070580c107000585443c000349001c3d909c800503540268003620010b0b0601c000a01081690310405004012 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 671971196 1250 671969946 671969983
    0x1b0d09060906051204030c2001020c09370603030305090106091104090b0607080c06191b120b06030c0706050109020f12180d0512010803030c030402220504080903 71
    0x30000c003e0094411050080c014a00c41d40000f403c15104030061040c0b20b503c04618081d259886400d445072201c0e03008003c1c003500071129145403509098110a1049050b10b80c10b90006180c120b1880792010368044400100d00704429511a824143c002c1d90011841303998000717040c3c54000d1205003110502e40241c52150308006801c4d0b080684036042d02c003a1641300380300051429010002a44511901b6401070050b02e0125114500c80008540300388a290003143e4019502044030820003102c1c08001d81c02907814038840b88514031032151040038048241101d0005522409400140036500700f01c602c54454940042d4003403c000003030144a0041000030300c01d608183c00300500b50118051610320348441c0d072440c0006455800d042d100402c0100307148084d0362103c40004402010b0f40c0c0000340c0d0303655906890b000007840e503200104072407140400003002c908645903a800c12840c400030343d9600e03026110440d01d201101447d413060320300981c0300300c504076030700c1d00008245801c154070708000c20500c11 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 671972446 1250 671971196 671971199
    0x10e061614071a0c0109150207050f0c01120b0102030c060a06150507050a02010309020d0614091902030d0e0307090c020304090b030f0a0605090a050604060906060e0705040b0f1b0d090609 82
    0x4040b518034061040d001030310940f96240740c0504c03030041c005000050295034071000c00c40c0045030164000e0921600440694500940301c60f40160384030450003501c4e0010361443c0c1e06406600c00c541c0084100c03d8144192031410000490582c6041010343d12030000e1036039101c04010400e40303000003218032001d900307040e420500e0b59250755031902c1c02c812000e4140354171800c07003004544c1d807118200c40c030b07940c03042c41008202d000c05205150008211040d241c184107440310301442d42c61080170505c80a82c010300034441c502010008490509003005026010701c1544408103494450703004682c80c414440c2e000b140c0f030b03070b1402c10079600b6503003810802400398110700201e44000c240401e03902081c54029101044544032592200d1170000303104030141075401f03280103000c10800141c000c0304449000b00d00c01e0091a4070b4140304540d031001914480d002c207401300010041c010001d00030705400c038800c4081c40e00706404815800f142c0d001100b14100503420642c1d101c0811900452400c01504207031402c0100705 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 671973696 1250 671972446 671972459
    0x4050c0927010308250501050403120608121b0316050c0a06021009030e04020f03150f01020d03090c0509150406140303090f0a080d051908040f02090402010e06161407 73
    0x18006000203010b4004c00070350005e42c2005440c00403507000420882c05034a001c4c80c10a64001c01342aa01100007800720304080c0000070840c06072900303031066034000d80844045204240c40c0c3e98481802031119496000e55100846020320280030002825604401034031502d01c0d00c40c0c20700c07002c4101e0a11031091001d09100d00345c1d00003042c10140b00c003800009604005802c098656407551000141d003d400029101d14500b440c0c80903500500740707003030422004000d14007000b8250a007180b625006a11584c0700169480c420b4012240d814000c0107108042e90300d84012486846c800c450a00301ca1641082c110464181407240a004142e04c1804000c0c0b0900480001d4607441003282c0184121480e82a08030b030380e03850400c40f000901d09201101d2405c81901000341030307a00081c00503440c0444c0484452199405003803501d100e940e1020361a01e811003ea130070007604a5000d00184c1c10804103264400c0192101c20050145480d86814440b000342c80340351000100081d0014032125412615042201c0b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 671974946 1250 671973696 671973769
    0x60901150303030b03121c060f08062202040c090503060604050f011202150d06080f0109020a030b0c0c0d0e0a06020705030a12120204030c090612030806041a04050c09 73
    0x1074030b5040c41c000c80c0d008950000280b41c01c003440e4503c1c45000c00082c4004c5041c1090743c01041020709040f003482103603036a1655035a0700d00580300d1180c0b0743d00300c0e00001c0c5908907550008050500b43d50549003410540e07801140481e0004201c02e0301044074568288181c1c07408001c001c0d44410215801d01c050b25055a03210300551040c451380b1400340720f00058204664440c120034050300c0580c8501903c0c2d400b4403589201400300342c07217007440724020300915070103102c01030048040b40d580207403c0021aa1031655960000800101345e00502c800500052002080038049d2152015540c2d0320f0340540d040c0c0340104017060049da44071006642c000907040185840c0030920242c00c036080214a035450f1a0080103452035240154800d4000e88005000700400100c0540c80c0e050310b400d00010010b660329110b005840d100c01c28000740c04180c010300040c4940c54990020201c0d90310800b030600100e10303d4000700d42035650030703102140c2c44138000c250401c09042003c444941d21a28081100000700d2503150801d8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 671976196 1250 671974946 671974949
    0x6060b07020a05042721020312060108041106030405010c14041802030901091208070201061401020c120f0a0b0109050703111b161806080303070e2b0503040806090115 73
    0x20b2905d550044900321240c0754040340d8501402d09061024850f440c25001d071560b8070502a801206a2640403010340c80041500e002131090040d84203507850301e400654001c60001c01c00c652050f01d20081e01d0240d00d4400c090360065101784e00108a1024009019019801040d588035041100340020041030983e00521000404c06000060b62130325012800c6000d4455640094603242105003850000c581c4250418400c00044d070081005075240c04151049510101070140141e0084418803003501e4880c55010b5034803020011102c510b040307407100900313140074180142e030559101c0d0010006203240f40105a40300c201850100000203105034103a00c0da01960082c042d03036450480b04248506420403642c00702c0141541035007202503440900e0f00c414402004c0312902c0500382032001852590000949000c2e078503d8442d20644604c620510200304880c0000703c172002d50115072203405030390000d01e030090980180c000c2c503a12810009403919000000d44071007203d030b00d0300000c0042c40e060441140b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 671977446 1250 671976196 671976199
    0x16030b01051e0904150e100518071206180b0604050612150306010e0a0c08060f04020703090e07020c030f070e0f0a021e13060c0f03050a020a170706060b07020a05 71
    0x946201e8030b00b0380c6030301c0c60140151203500700b4980002401d80d032201c00c070034800b254002440e6100710703503908a46100500c650302c01e070780d08112034000c05030342d24260748151135121a00b880e100131621041c1c007000085e80c026511940c9040e000426440100c211402462020901510b0340307842d2910b400f0204509114101d5008042650070020980702d0182040a03020040020119020f658696404914a02050707c00411080ca806e1424001d036020340015440303403d000b8003901207400c01d10b062002030f500c500300450402075140b9000c00c0101c91112014018002940106007541c001d1302854a0452001c407491072952201c401004030000303081320f0303691100c5070314081000f5484940c55240a4080c000354080c47e00d0100300a100c8150a250103000c03a880100706c00b02116503101407e8441802045001d4940c0a010540101090082008002e15100f40c8103c40384e07000240c0300c07a4400c04214503000c0712140d0004405050008034001d4034042c0401000a91402411380e0000b20700754424802d89 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 671978696 1250 671977446 671977477
    0x40311060708061512161106070f030608061501110129010f080f040f0c150c0203010f02180d0c1d040606050f031f021c0b130b090424110316030b0105 66
    0x2040441d104200541c80e0070747d40c204544032818880c00282015070310340903560020380b4107407001841d010300284160051241b220190b51001c810b1004440e202c0043d00010740641d2a088150702201201d40b641001540d81000340c0174000c01c0c2c50004200d410710715110740c2040400002d1058490101210940242d030208419005c10040e25116450503c1d40c0e104440e001803c0122200f800c0c1c004c1c4207468950f2084008001302c50100d9241d80490040954001e01c03e43c00c8000c0020138200314560380035990041171001b108a80e0b03410340003203000214588490440125041c0b008000041c05014041c0c84125040d40002c1424401700369204900d00c500302c00f540d40c0480d007441601495040b241c070388010840ca16142c208140b2142c024000010009001e03c1c24414085038402c618480c0c41c5442c070005044041d6500d0300d40716545c446042021107030300400303000355100e001c071010720071320742010091000e031500e03460000268900361010740c5900c4181820140c07402e509a0340b000455070310100c200840e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 671979946 1250 671978696 671978731
    0x3091c020109060608012a17041a04150608010b1305100503060a0204050102100203071e050c0a0b01060f080708010918020411030906131a040311060708061512 70
    0x101e01500002c070340603115030f18140000c42d4040064200010303803000c0c0020344200121304102e00c050911400310f0800014400c1120b250145401d00c04030340c00c40d002d503220618804000c1b45084407844140d034100e507012036610904030b0320900c0b07016100040c2010002000081c0c05080490300404030181c0c4550314680d9140000c0764a5042d01159024003005412607245151140302c140095206005041c007601c82c650081c03107294001c1c0200d07803198165541c0c3d2140c0ca07a4045404070515800c25212062010601130381c1d0410a00b0080c0340441030042d45440810b5240820144c1005080100b0204110610041000e1781c1d4019a2140c1103a901410005000040d2005800030240b5603078000e5015040c240d021364803803600d0f07008c4c0d4007039032401041e113080791904100f011601000d190010312021038034a804010311030803524968480d000c0c2c10100b03441c40340c02340c0c02410303c107088502e000894401004d20041c2d0802c0c14020600c3d0b20b0f0f10303008900d824102554510002c030002c0c000789180c14400308 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 671981196 1250 671979946 671980003
    0x2705070e04060e07060e2103041502150403080f070804170313020603190501050a0602100b040914010507020706030c0503010e0c120c0909060a050d060b06130801051b0309 75
    0x100340d41d10209142030b07130a6a034540c280100181c986d04603052048140290820055854a25403c82c204110004600e0303d454412050314071000d1781d00100c15400b403007226404901c0155240e51003580b080e41d5000543c07030180503022141002500ca00204419a001c2000003082540740c40e5081c0d6520741e605850760b039a080e4580c00e035030010f00025088407000c01407240d540300782400ba01a03911000402c0c04181c3e00c800038001410b045210703510050b0b05c01d8542144c0c002182d0f100d464883c03400f41c0041500c0450b501c03031181885181081d2983d580d9541c042000050b0f06011740d10240038145010b000ca060280d500500501040c010301c80740b440e65901282070030b1030b5002101c01d009000312602602e458100f4400035143c0001c02000d00076180c50b00010b500d403800403c3c000030364a008001c039545800c5d5231943c1005018028185811410800c501522a98518022802013000e00000307c0d082c504801d10103010440884042e62180b0103009110b907801c404142003401403444103228050800004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 671982446 1250 671981196 671981201
    0x150409150207030c05060f040c0306021c0207080703121517070306110a35070207030c15030b1f0c051203150118180f0207080c012705070e0406 63
    0xc64006152000610000f05a004811856828003c07030903039004d41e032004043d101c55081200d000307101c0064014107000280c0c0d103601034441c0700d0303ca40c070041298007080f106108130707881310900759074400e4007181c1401007561142c4044409450b00740c0c244100030658140c002414454041c50744042003446142c89440e07410080c0d50700540c1c220009102600301541c0083c80c40e4000003440d8002540c0b8481c40c1001690340301040c214808020b44d0f040401030140a4110400d0060205411805811000000300d90b000380c0b0f00d005404403011803071400303110000140032502c0c11300c0b84d2402041441890340494100705908034020740542010703035034924903240c0182001040512204041808801c2c07040200400b10307a540d070544207807a680000c2d04007a040300ea026003148101481c10400b41d01074101c100e107940000001091108000d414040e0541c5c0e54211900101e01181c1346a40d80c0b40b02020791b41c50544410485140111940402030300760310b600d03484043c01d00402042d110000040342c2040011ba = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 671983696 1250 671982446 671982473
    0xf15090b1b210304120f020c0f03150709060201060f0b090d0f0b1905130b180a0c0308090306070f020d0e0a05060a0e0310020c0717151603060e150409 66
    0x44101c1c0070007245440b0300307141e2a0410744043d5409038914148118643c007540d175807032280c4103175001441f441142204202c0701403000d1541940500402c11409030307000040d03a01c0c42c041e903610f80b110740100742071001c02400c4410981c81000c024450361010081842c111045440c0740b00103803001c8000d02c4150171300300a80007032003000400512928080103901ca6186182e6a03040740c1d00d0703c05001d60b407549102c0204214502d10003030612822000803500920a040645010240174030075030b1044041078860036803080c01d5034000e581c14030000441d0001442e050085035408042424085541480f0150082d0740740c4003400d59106000581c080400103a0302d094001004140042c9866078400b030703c0000404440003e1003150080c401c0c004d10001000581c000c2d00e0594447d0b4004103042440d141c4070f0740320f295114101c844240110102c10485140320003100c2d00c6943c00d103446030040c440b24007001701140c01c5a40102c441c1a410310601c0340484500c1d02d0122003070000c40c0c010072452030038104a1400d2884 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 671984946 1250 671983696 671983723
    0x204020307110304090207021008040b06040c090503150a18030503040303050603010209040f0c0f03050112020d11030106121406040305120703061e050f030a121b06060f15090b1b 78
    0x404c0016400f4910340080c00320318030a403030071004030030780410030342d007044041d180140209000c1c030004041e402c05622016800c0000e242150550ba914008241007940491644445040341003c1140d124030324040c0c112140500c0c0300980c10804262030080c120300002e0801810117446a000c20004da400350113031103450100400c2013200240c245406001030419411b40d80100e20300100a0780d0382400780c8101030490781203060000c03e140f072960810902d0380b0302d07081c00c4035610074442298801d500c0900c641d00181990105036841a6a142803145a21f40c5d0b04903100c895901000c00c00c00042c3d403080507100301c200000b5041d000780d15508030507000307456260021040400130703605050341c0d0356045911000b210420740e0407070704040078581410b031101c01d5000701402900e29070940c0d25649224503108601280704401e1305441c40119911f880176511694400e61101c0300c111418420343c0b0400031041000310990515600142c80d1041019450040350040d03244032a007840d000c028004c082c00b004a004a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 671986196 1250 671984946 671984953
    0x1d030a0f03231c050a0e0706180b034605070e15091512041101050c010903030203061003090f020130020705010e1203220209130605060307050d020402030711 69
    0x1048180780b50901c14620300c1689040c113010101c5e052040c6031280d160a141d03c003010301041030520380180d61140d01d25a00d94290710f040000080c0c68100d40c000340d80951912074403000309036108900f6030005e120369032500e0039045410446c0703544c41c46944460020070707040040215899480500aa6080401001080d00040700408205000d0100001060100304c21038032002c1e61154181d44412034040e441e424045080000c02090100d10300d207000c0c00140384145451407600c1d0030b4500351070a468001204801082c0c01005118040c5000b1490060f4490365160801906020f034a031138001c4064144064140062011100f10038a0005407036a1184410b40c0b118440130030041c0d4200081d400032030f065425518141000c8401d85020800d2100c00c044c8105540c210346490001d501c038500812038007011a0140214100143c480c007440610500420b03550040540c803c2c2031174030580704020070140c401d0b04040c40520055840000b8800b5144e01641c0041c1c8035550b07500c0c01d9550641a8841d1a440e10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 671987446 1250 671986196 671986207
    0x12c0d060b0d0f050d091a03220503030412211e0e07081002041d1e0f0403090f0b041703040f081e012013151d030a0f0323 54
    0x745910040354914403a00c05c440452a1180d02180d444507180030303440c898011014014599182d400107590808140240d060080b480a500c8061101828800f181c0d00d40000c4200428801c28003400f041d50915801d0154800704200c840d03504040010840315113140d928658885442c400070102d0401580b440740c100721010318007049558411803441441d0320b51140d101d03c04514141802520111180c204210725030034407034841c0c594800c070020181c54071642000c01e00c0c08265102c0c00c80e58010b1b01c440b0a00b802905103030034002d0880c00550020304d80d8400c107000401c50101490304a5045812904111025102d1000e006045100d25400407030454003645d80450f01a9010400e0005407000403041c0b03c6405110030b03424207032508000340704114002d00c0000c910482c0a503009001007542d514840f822161284c0f03560a0407003401440d40000741c44442e4102c1100c1d000d00340301e440200100c000700041242e5030741d10000000c50320801010000341ca01c99010040c50104416000c01001c54010340301d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 671988696 1250 671987446 671987453
    0xf040623040b1c1802100c0c060906020c0a0b040b0702040207050303040503091e0d03052b290f0d0f05011107110d0209040602031b0414012c0d060b0d 66
    0x1c1c0c0040190044580c8800780c10f180e051464400c43c440d403402c10b8518201400d042c1c007000208a40f400014050282e46446100020919400b520180c1030030f884001659040190003490040e49010b23881c00390110a0003801001d081c081503070100c48100c6c0c0c806913038680900c00b0401070302a2000041181c4000b1092104000c0084081d1910443c20f0303d10b5150035815003c481851405401499000141c036141032000c40e01c02d0000389004140504d141403101095107403500c1054050b8954003450340d440390503a0340c08000200e800250b0302c48007980b02214510000049102c00c900910600c5049640c0305103082010000809002c2ea800c80002c200301e15808007003181c59408010225900d03201c40e118501c5500d4001c40fa08402a0013905103001980e450b5541d0009607c094440c1c2001151414100c2032003c5140040003c3d014240f90640882d801c14009007481210035940359000c00c0801c80c011030b1402c1d40444980c00c01c0100d90912910002e8203101d00142003203c0c0e02c82c0c00940b20b1071004d0a1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 671989946 1250 671988696 671988719
    0x804060e030c240c1201180b13050405160f0b220e011406162a0b1c14041203020904090f02130606050a0810051f0210020f04062304 58
    0x400302034102c5802c0307541d030f000041044d510a181004540e10300c5600140124140768130350940c11a0b0708000060076000c3c000000d50f000c2d84420854030300c0d40d1107000308010481c051265007400500208103040075410840503803500c4240703014010300c1000101e9403086400c118080300c441d8106085c03407082a140c940000100300c0c1005d001d643c0c0d40c004415000d42c0c00381480f0084490103d0714040300c0c0d0161441c0d80d2180e035010b42d03003d41c1d140c410b20510600c900b4912002c140e000200940b5401a90320440c1c2d528140100781003403150b2845a141003219400c10034001c640580c415405002000e4041da21a8182d0084c0100303102150420329201a1000b0803000c3c061201c0001c1c021100e0140001c0c0d100201c1c01070b28a035002c1c40001400a0058611490160032496000002c1d0280e00d2103181d1500c011454012901c210016646440c0c1c00c6800d003142c0502121013900d9191034217500c1d148401c1c06223869849184a480f04101d86d8480032501c0107440d643d040000390384d0700d525581d12907580a04001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 671991196 1250 671989946 671989993
    0xb040c080d14030f1003060e0c03010b0307060c02120a05060a02031801050601090b180909011e0c39081b06040c030b04020105040806040507091b0804060e030c 70
    0x80340e1241d8440c03200c0c200e0003075101100480e16854903d18591303461501c0e201c0400f001d09403a51000d0454004400984603000301e5400500c103c005060000000040509440c0c1c0c18003428002c0d040786105103d03540e80700000c8103130f03681c05603031080350000442e82d04c03440c1c904501d41c068240e00680c4180070200301240c00031070241200b42e00c100b0a00e580e107428a030032101c042e100c450104400d250208645004e040c0a0708c203800c680c00360b00300a9400302001c1584100101c0c0c3d14046a5074410058a80c1c03400300c0000415404005420007103100314850240540c9a00b8a08441a48035441d0280700343c20f004a50b8140380d540003c01045440342854203650030340001088503881d0804041141e142d01e0005050340c40745400101d8041002e140d40c07144040140c000d4000d078104802040301041810301048240c0c003580c444c1c4000e01d8010701e03000c1808103e4805059840443c035443d11000c40540c4d01c50701854005070020b00000b85000844040c615502c075000c0000c07444d0007100780c150000b030303441c1c0340ca10b8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 671992446 1250 671991196 671991209
    0x3020f07150507170f15040b06070c031e05070501030f0207140d0f030b06030402040e0703020303040e0f070c12030509011b0207080d030b03030406080405070b070807020312030606250b040c 83
    0x4c00c00c0300c0c80b15490100b40d03011258040760140341c00c001000300201d400c010019074006440054280c401388040344a50740000303000d440e01e084031142041000803482003801007245828a03180c0c800e01540e00c4a443c0c014070300c80c10b4101510ba0b00e14480410b481e0341295880303036101d120380b62000050a1480c1e194080c45114030041036040ad014107150b80070b40240d0a00f40c00050505243d566079508100041040407003944040c0b144801c00320050b00c00b040248050100d0b10450b288034540422744c4070f040040102204108880240c0c0e030800030380a000c04000d1800c585c1000310741c0b41d0700c40140c1170050004008043c2d109a400c08584030050700411700c2c401b500c02203829543e00350002c84065040e0b60420b0b501d55019413041000700f2000d84100012500103100750240c4038025502c0e400d880d150341103100180d6007910000390045c21031034100542c981d12821811424214513050002540a02030380c0000b00c1300301c0c0e07010644c4401501c403034441d4040700c0d808000150103040c6828404481c400710b000d00e1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 671993696 1250 671992446 671992457
    0x1b120807030219050d11041e12110f0f030304180b040903020a120302120a060e06030d1b03110d020c0102060c090a060e010210140a0b01081603020f07150507 69
    0x6888a1082c02158411025002c0442816500c9031044605601c8040b14410302642c07540e206921019400040005010350626100600800c200c8000c00f070341c103940020000343c00e000e00c480020b0440c0c9840f0405420031940c112411001a0109200003042c0120075854000000c01080c13814185040407442c001d00d04c0108a042611010b0008032801c048010b070242c0e000f8144840041d0590306a1001d801d00c1c3c2c9005400d00441002e508245c0c1000e540800c042519034000303020300c4580a071040d511100440041840d10102d80c0b001e0a0303020380312489205514a14121000e16000d0004101c4922010084a4101c001468025114211414034078014014503000c40c00303045500c0180c43c1c0b402c00003040701851038070705401691080d001401060542c080c484180e0342c1d1410a0ac030b0078a400362003154110343c034a03101101d1411903221482071344c1480380e0301d0144095454010129070742d101040c10016501e070300c0c244650b002c40c050340100501100179410348a4245809801440c080d0b03030561504d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 671994946 1250 671993696 671993701
    0xf350d050a1b05060a020304020a030b10051002010b01080106030c050c0304030803060f12030f070311030d0906050603030a090317040b1603140702010c170c100b10030605130c1b1208 80
    0xe0420225400042c142c0d43c0100c0105c2c551211039030055410610040284070125600d54810a205108440d641c4044100751020412030504402c9807400f1080e61008010a8001100181840728107001700340406648003842d03c00f003401041100c0c0e101042d031040702e4403582e407468105200e5004480b860300034003880d00285520b0511306444603801d030f056401b542c208265201111340340d0300030b544240d040011461602100c1d020900040c40840700100010030448818109201078810144c1111300036441003000e40c02c0203922501344820303aa07105031000c0101e4500031804900d4000c0340c010f07001c500300002c1e00240326465017034076000e004d201c0e44401d240c0030414944000345009401c00039000c141c1c01154407000401541c1c1c020300740000c42007080d080c00607102c810740c600f1002e00c9a605540340d0301c0e02c20241a2801c01000c440304070440c641030200a00f85004984454154240c0503091074446405125182c028000e501c0709040740c03280d54076041120300f000d01001078014001c40100720000301 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 671996196 1250 671994946 671994977
    0xf07050a080304140f130b090907050d0204020c10020a0207060e060703082221020c150f0310120609060c0804170c030c010e06010503070f350d050a 65
    0x114000300c5400c1c1e00503500b000d00d04000f852108070b00c80b11241c1e02401d641d50102507503071a034201080c8094004400200e2110640c1408075444016080e80d100794000322040009544549146410329410369000d86c441c41e24100c40c82c5011400a0400764250000c1890002d4643c006a400b04a800956820042c540c40d03100340080c074868208003400045510300040c3c05202400200c5100007164861011801110f071241d0440345d5910490803509070b850a602800e059040081070b8100740110741c503203582141c480844605105001003202003440100003d085180c5d81a000e50003052412150701c8480906d14101000300400c40080703501600d0980003440301841000340600c07507940100d0f04000154495040c010503040b030511145544000c000c8070410381e9003805200c0b50041250014134031035041604040c1040555000007020f540c02e01e00400c20b00016041098188082c440b4919240503a00c00c0c0b04414054008440e1181c801c4280031980030354407200906240b15203546040f400240b910303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 671997446 1250 671996196 671996209
    0x60317120a060f12020310050a0e01111c051308070302061801051003080310030c0b040608091b0108060f030d0906030605030c012c18090c09130b0a1d0f0705 69
    0xc0c1e440d40c440000013031049006100f03c800c01c1a000408845026400c50810000d0300c200701c0301034100070b84910a00c0c0f0700c00000d02404c51844840c2c61120f003480c0303122815441c40001c403a13004e822951104081a03131003a0000805200a1b0080807aa940303100c2810080c0d0341e404142e407180c4c1a801403502415900c0e0041c400c1c5070107108500241c01c61285180c4401c512504081d209480310300d4070349400000200e00100f44002401409001611f40c5d20b8114043c0c041200103180442d1030b0000c0740066030240c0f2115080c90101c400742805020b40d00c800002c03e4072200d01202c0150140320f280e0303810001e03940040d505022100103590a00c00d4545035028543c541e2306203110305000c50820822403404100da4100448042e08003100003004071036600c00600c0c0d1605422035102c2d0351424078148070100f0010700413403118600c1a01d5043d81402c02841018a5103004c141c0030700740d050840c010a1002d261a04a11f03800b800b0f5021084903120031110054541043c21001030040c031800c40d0000702d504100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 671998696 1250 671997446 671997449
    0xb0a18080d05100909052a030714040509190821090604060605030c03031c1812020d0503010311010c0204090b0a141b03190b040513030809010516030f060317120a06 72
    0xc4094580b6800d445030702c2401f4045a101e42c100624034102c43c40260302c003005043c0040ca001d291000282c00790506210803910090000c201c107810136502c2c0344d0707184141d0712244000341d805480c1c0c035650b0384114480b440642200354460080c20101041c0b202c136900c00518540200e004981c100038142d642c9042655034089075400e2a010307003040c4502d01c140c40c486051194000754000000c590b04907880d0602ca0000e0500400301c1c3c510315002510707040c00d541001604c0f00b034045410036500d07650464407088100070380c0c000903604110003600c10f4400c5480301c1d005800f9242d40700c4a41e81e500e042040c003480c00341a4180403c0b086845401c00101e03447d00c008400e18504030580c22891a68541c1c9100f0749940c0c807241241c590464441d00d442d000341c1c40310700c1414842d41d680b80710414030450038500280b10343c2000e850701d10103a050109010100381030400b5001d412000e070900251010130030104002030310b03191744003901140900b0221540f6103918001412250550800880c0550f508902c1c3d00c00c40d0001e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 671999946 1250 671998696 671998703
    0x9060412050114190207030c02030d090e070503010b2b05010306060501030b1503010509060a0b36011e11060c04060f08010303090e070c05031b10090b0a18080d05100909 74
    0x1042400c28440080307078011b04060b4043d00d040b6104906c0380c0c0119160041200c500d1000440ca50382c1008510203440320b85030810500c1c9822469940b400869100c00c5c001d040380e4a142c0346d1481710b02c804c4441d43c22031410900080035814046580d5906021005108920407140828207080b40344140d840c102c0c09a100004288040030b045034201800c1c000c91080082905e90030401c00e510200720341800001902d00301745601d507560b250103500c0c1d58480304011031590f01841103a59841c0780d22160780041448d80c1810912100b01682d081c0c0d040212034021020380100360a000f84005c0c010500c42440042040d00d869450740302d508103020100f20340c049400d00c005000201e0003001031004032401949250031116030b24040f0300c482c5880c1c450504640c400e40750a000c5080740c040c120300400c014002662038401c800400c2000d0802d9444084440d100104000035041d078a280d020300d43d0704110214135580380c0216807541c4461801000100812064075011404142c05030002285507880c020324145551 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 672001196 1250 671999946 671999971
    0x100c08070203090913030e03122a0a0b0c040b040305070503010b0a050a090203040f1e0b0702280203070f1d1605070f0201031b050702041103060d140309060412050114 73
    0x1a8100f400107405e5002404034200040b24450300c14a03039040068011411a0390300c1e1640d100680c030348182e84140c25040e080d41c2d911941c15102081c00b400f06100c0800b98002d22001d810341e8820f590141c03280f00726084030004a03008075020051041c0000c003042550002d400800082c50000100449507000e0b01c5407a80c05549401e00b131145240c690003954000d071040c80c422802c50048da4400360880c0124070344420442c5030044810a0112100c04680c106074240042e203221031411b1400f40d20740c444614103000000b41c1000103011500e040000c0790040000e40c040c001f6103a2a240701c01204000c40440000901d01d99000c84d00c1312041c00040c0d030001c6a180c40d4189441060703a00d58008034603010080c0c2c145a610340381d28102821010904041c064103a0380c00d9a500c0403441080b080f02c0c0e0340d0580205000040c810080151541c2ca28481119045516145103400719103119146120340740d800d5400100202e00010702500a0b0303140610b8030322a10091100710110704180081900494a0309180340303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 672002446 1250 672001196 672001201
    0x40c06050a140304060f14070516030903080c03270306011203051b0d02010f0603111c05010615030606030209010c020105090d060212180a05030a050d060503100c080702030909 77
    0x5009100508211919040c16111803580c06502c1d0100c3d00100c8081d501c10b5140c013007807005490700b48108041c9410030900e60034a401d1507a0f004069004904620341c41e0801151030405050142d0320300002503501800d0b9a07942c1c1c0101c400c807912508401150a031048001e41040d0f80e24486004036402c0140150007400560320303248410341340362901d0100750240a0100441c1c50318001004d05800c020300383c5d03c01040ca09a400200030708407140305008002c554600102070000a96078524018100c4007250710300060070300709200501001960b040101250300c0c1403000a80500d0181b90b10b8144100f5481c00c201807556040d082d41641b241081c0c0f00e0015100044c45d00056014074064450600301805155804045a550341d0403603215260f203e034107803101d50810640e03100c2408144400d0b800759024002428041c2d903113a55a0040c0f0b040e4109010000c40c84030b0303031142c02c0e40c45240203140090231180c2c0c4941c5046203000518032929003100080c4075800080000b0700010440d4142d02c0003504180156 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 672003696 1250 672002446 672002459
    0x215010303020d1d0303070c1e050607020f030f0a0501050405070501080f160224040219061409030123071206050d080f072f180a090f0c0617060603040c 67
    0xe480000c030911328881c03190300300d070480d480800261100511603480715040504006503074986100030306800c820a6001c10007071083d0703151401940c1015605541c22030078a9460000a0704001443e071800880d8416000402d083c8001508094021401441580c0e10180c4480045403000f00881e094121903207804007041d001184d40c0210300c1c00000078810340d01c612034134080d002c0c4201c0100c3d005254665444080c00300390305e40700200481e400c151943d80c04d00c01d0324150340900b8072072148100300e40392040802c0002454900b900801d030410388415040402e402d0429a0042c0c052081d01d40000007000442e000f44107041c50b02c00c00c01511002000006407007855070340c550301a031045410f203504800a00003a00018040c07085403e40b204c0140445603540002017029075071100f1403005074403511040100c1c4070307224203c0c021203030070800701030000c510590142070a589010b0700c0f484c02000381c12451b000086c06648410502208400f260046501d51903240401401d800144c0c3c000c2d0007801004410001c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 672004946 1250 672003696 672003707
    0x90108040f031e021b0d020315071e030212070e0f10050409060b28090608040503070f06052a0415120501090c03050901021305040b03070e09010c0215010303020d 71
    0x41807082c40d21200c10a0a583c0d0440c0d9020941042d0002d640180144031804122800b02803400700103035001d0488030300c0c0c0d800003a90380640c42c41d64030b2214800d10105198611410340402e01188102a14403000b9000b08000c0c0254416480c40360328486040202d403070144650782102820780000c100f031010f20585400c11034a000029a40c6090240410000600c030100340280c200401004000c00d8030b48001c840350000e41036684400002c03001c9020001002d0303d400c00396030030584410785002c00e415600c03403030a41c2c550300c150302019000380c03500b1101c60100519a000144940b850740885c000351b80b04400c1100c01c1d0701c211035841d52402001e2005201c465006081c1e5561200240781c00703d01101d040040008035082a000080010b031102e00007020380350540207058104003e10300842c40c00d6919801d9168800c42402402d01c9035485510f0302d400f1355800c00040026090041c0074020f5402c00074091402000c0c01240c800142c05003d200007142c98040035424102d03074058001d8561468111003c494 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 672006196 1250 672004946 672004973
    0x2040506040b090414060106180b09010c080c070512010902090c03130b070206090d0e011b0303150e011403061920071a1501020a03120f09050714010509010804 70
    0x700256250300e100071940d0340e02c0c0001e0103103019050341c0b100c2c91160300c4410b0078008160414000d11400101c00009014404400011039801c010b1391910707400c241c1c0040f5481440c0e21030160a02d000403541244102e8080349003012034400b10341d8004516802c11905003a40c1708140080d40c032018036800151000318040c015039004080820b840d8000840d03944010f880a001d07101000103a01c6402003084590302080303480383c002a03a081518000d0031010000340400e401c2081c03907503115500688402054080d070846030b8103410203202c1c512a00e07110856004010340074490100c0b03540d000d0040c0302082c01d0115403d4082d110ba400010082a411307403900d00a00486d0300c102c81a10f030052200045d80b001702c07004c4c1c50309901c908840301481500c42c4405c0b900030005008401345200201d0040304aa03000640d00c080f19074036040a020111038045000300030901c00c645407551a0800488c01d0402c140480c1e440b0907110300d05e058101845201d00110340d1030059106c42404600158080390220b0070009080b01f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 672007446 1250 672006196 672006199
    0xf031808031801050f0a0b0603060a060e13060b070302010b0d020a030f0c0302040f05060f10020c22060b0a02060c09010c060b03030d110306040e19120912050c0907030506030a02040506 81
    0x2400c080d96600600c2c03c403402260180381410445c4140400d00e2014081e681e0030340c82c1154400c0c15401c0600004800401c0f5104900610001011106041d1a070940b10b0707090055104080080950f11052103030543d0004d0021001075103801c0682e80107190600c0040c54441e0003a140d01c2200d4210307a074030450600c0220b400c2d00c02c010740000000040e5640e020b008204204070102140700e080040c18425100e00601140b803090ac10005602e074603580c00940c04406090803945041d03400c0301e60300704800240d2607100306a01241021300c0490b1405c0840000d000b0a422942100d84540e510900e002160142040302800101c0344801003000c41c4240d0071280101c140107040c2c0b4507115103084800101c072070740b1114240c40c6001000700101450a40300d0461032201c0320014128032044c2144a2014650004c0018605408494030200140c411804100038114070b054602c200101070500a0781d50145015544c413803043c0e00001840c0c54400d0141a00441d005802050404040d030300700009810028910b5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 672008696 1250 672007446 672007471
    0x90d0302070320040501090b092d09062a041a0c1501140a0b090603101e24021c140706090507140a06080603030906030403050a0f03180803 61
    0x10000c55154410001c500325083c0c0d010041e842c800051105440050740103031182ca203003550520954a4001601c0d501545c5491078800440c0d0f1881c001c1d04040d861680108020700d01c40c2040700c030401c006641c4e405094643e040241241400507100f1507101c401011141d4104c085c4401c1010301c070401d0840b0345c1c11200907000c5003018a07407230a941ca0540740407104a0100e601200412a1045a2140e01510761040e14039042050410048004521994103001c3c0100c40c0000000c0d0070500d808c130300e407000d00500c0405010441e01c140185542e20000c1c043d1400303c05401c0032030300300c2d41b070801d00ea41411050741d00903022408011002c1088585001840b00a0007002480840104615401492400e01ca184000b8150150382041440d1501c281c00074260000c0c0c510300522159180b0401c0c04c01c55080e0b180c0001d4550341d00300801d0941c01042e05881e04144003100b80403c05070800c000e40900080740e540e0208500d61020110300b998000c5240c40c2100301261318000200d0020401960300140c6140c85 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 672009946 1250 672008696 672008699
    0x40911090a030b2701020a0e0f0a1205011d0604060c03090320010f11272b0b070e121501090c051b0105040c0906050a050103022a1c080c090d030207 65
    0x2181c640c0c52502001e16517a5800248161015000003000b0030071103003510002e1103140a04080b070b1584041b4003405140c0c00209c0450b00800900f5041007032844441c07455074181c1103c4400c010368074802650100c40300303410300c0e11840c00c2501c03d2181003a1548c1642c0c409105800e0b950522a03849941c05604016540310005840704081500a03884805c0c100e500e12a55200801c5290042c00c3c8034022400c1d502c040c06504a00790350740c80d150001d18050940200d44404d001c424018504106c940c0b008001081c40401c0201642e0007200c2203a41003000d030303101020301016601282c1c51703134211144c115a50703603044018071900113254400d581810140c00d14925164100240b070406c20600100e0072400c2e9105c0042100304007070412804010420b52800788051828240058205640e82c090b85040560110744d407000002da1a00e03c041d4403022181c056007404290640c00d80340c0001414800c04a038480c40400705681c89040090b21600c0d6442440c0e0900303407206c0402c60030300d258031400d60851141100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 672011196 1250 672009946 672009991
    0x60a0509010e01090b010f0605043f0303060e13120e010c05150114091b030705041212020c03030c060a0902030304080615090a180609020411040902040911090a030b 72
    0x245144543c000c03405d1600070361424407100c106100c190025002c001c42444100000345100c611010103018140c1d0f41122507100145500f04580d00d01c083e404070748801041201810340580c040002d44800e03640c1c0307a80c01e542e08403071a034070000d81c148010041c0703080201501c00c452103512402032200c2c0c149000e04a941d403a8a600d481e00308800103004214003040300402c5404058200d01401034015206000a450254040324081c0c00301440000e59640c00000504014820403c85c0c01400002410000204580c1410001c26039950a01e2016109844c518a45840d002040d2108100100000e003841d60f0f4002001d805440200742c22a054403050001082d0072106010b050320030329171902810f00e0b00c0f0300d00042104d8160047c0c140706840c1e01d481404280d5841c148861a8455081030000c03406060700d1011500401e14610110b8101e1004075010814200701d80080046408011040c040b0088000e01c2d401f05105110038164030200e0400304100150550000980c040c40c4100502c226101482 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 672012446 1250 672011196 672011201
    0x6020d020703020f010542060c1b0406050a0b0d0b030f0a0b06090412031505060d0c020606090906012102030106030f12031103010603090f0f062a02060a0509010e01 72
    0x1d0100d000d42c000801889100f8001d210b0240d1185281c1c1c4405480c8048451180b544a60390141c003038420340c9420010f8800311250b403028003580340507000c0e030340e00c0410803d500e850703007080c3c0c0f405e002c50f40a0001c00c11551525001d001e0903100b0080103040c0071441e094030050560b010140d0001c1c3c81da00d0388410700c1155400c5c0502d8021210080140c04484c2030362426801c043c0c0d0080400f849880614248800308104800380c0d2224005424000307030180641d015428103001a80c00182d00036000034218124002c41c0d00403401c01c5556400312121a1151001c00152140c2196041ea80758080d400402190700604c454000905a144018205001e160003090954416800c10b8503103134103844041c001c05c841707410301c6c04805505281c10024480c4000340c0c010584810b114000030503840c1d80d400e40038007503000c50440d0000d42c0600f010b07009400701e01e0890b02401d12411442c111405100c510740c4070440700054040c2c1100c003603024103116a140c00651004000c060000c1c2441c2d0750b95855600113000c2407 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 672013696 1250 672012446 672012457
    0x912090105071115130b040e04140a0b0709080706022808121f05010c0c0303030e030f040e01091805070b0315031f0e0c030a02060703050f040603091203061d0406020d02 74
    0x5180e401c0c1c1d117030700403010100000d4269001c20821001080101b10303900b078004110742c001c3d60145a14000c0e500c000d0041c0e14042a0b01c601400b1100f2003414406516080795142c0100c813441020707180b250340c0c0d07441d041c1d03111032500450310070700c403d00b40c07000d207410b0451030700448158400c1080034182425002c141100100485e003142481c54000440206603101c1503280000702404d180640200c601c954400d41c90080d2071000400303064480030002180542401a1200c03442c855204944980d51400d20078400c0c2c00078407031020110300e00a80540042c0c8200814000d0640040044c03100600c0c2c038010001d5179200070410240071188da01d800c07100703076002e02c0507540d8546111200c0c4112440618000e0444810300320320303280d0b64008002e43c9115200405c1440003560112125600c2d1800d038182502ca521036065039034400d00c070000c0c0205000390541d2201c0c40b03407401001c6001d4090383c40300041e811100c03540244104000e1750010b0781c0e641d98401c0000c591041c81403a026003080d8407614040140e8102 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 672014946 1250 672013696 672013729
    0x10e0a05100612110d140a03030510060807021203070905060406270f03030e04020c0727020307120207030903060e030d1107030e0d0305130f03020909120901050711 72
    0x810440781c420190b4001e03080903107803404282d00c460400740da54659000e0700081c2207010301100704e4450705000b8041103186c10158044141d82042e80d00d854018003c2c002115160150341000c0b001050301c0344036003259845401503400a0085000f070714000b1000b500014030500820005000c040707243c1c0c5a8201410040c00f5a1f01c0705102003103130560020034003200744179101c140400c480b810000c00412464840c103c0c0d425040400e8614822404900070384500b034000480341c880c1c0c100000b09290b088101002489a404003c8592210500302005178842526403900060010581001080c040d900424a0301c0c800d04202c0f18441d501c1e5214016500444034044140e08007048907094400303107014100600c403400c3d811034a8404580c1d409040d07441e0260030750303002c4c0c800881400e08160142e8100d44a24a401a07507202c110399501a1006642030750004034001d001d08008202c007003e000901c1d00149840c004011f080c510300c0001155140c004503400e80d096030b1821803000c0503031940c2c0061440c0c07031035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 672016196 1250 672014946 672014953
    0x52809020a0e1801050402031e101b020f03120402011116031506080f030301090b0d08030a09030e010203090d12020106030b0903031b0408061b0f180f03071805040302010e0a05 77
    0x1c1070f00d800704a92000c40c1c110701142e41400104001a5400f080c0c40d903201c0307039005d82c028003c441440303a50300c0c040c41c00086000681c075080b0010291220901221229500d80d400c585081c0b8100d03200c69124051307540c0c050074056179034000c240103600410f4407200700e40e030050843c0c0d014207440b61845030340e003e01e038030664507808403a20462400a2a00544000e410040c004141e00c24038410010380e42c0c0310500ca0380ca84c0e9a50350180485030754400744400030440c0c1084000392030341002001c0707100034000804101d0104030303643e05803400f550011058a980480040c203080d481070701e50b01c80d84855a1002044400c6540c2c0713640200006002c201817502695160f002141c413450700742c14035200d40d10f402c00140c1550100780020881c108000400325403240c0b80900b10b1040d20300201022071140a001410304038000041070f00194540565810303078240b2011140200034184030424551540c1c042d004515a407903511100c51342c00030064104036001442480000313078404000e0001400d10400e807500715660381 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 672017446 1250 672016196 672016201
    0x30507050607030b0915011d310b0f0d030e030313030b040c050109030503040b2107020307020906041b0503060d300201060e040210120609021309052809020a0e 70
    0x24245c03203556000402194090b0b088208400280181c800140100ca14441540c448405510303502c1400701e0107015940c41c040480744058020404090203d40148180d242c01a6591180340905c054032806501420f1400340750300c030762002c4550310096455150140700030480110407030031640c1004015405140e9a0b4590300f442d260006103105d1a0380f01c1d6040121061062007c118080300301c80884d600010510303901c00d130040d141c980078103540c0c0c84555164088002c001069402100a00d03003503200b2030310b0002942d1100100021036800c0465100d003c00304410700d604a07800f8500440c1c10080c0102402800a0036607110440400c41043c0882c1c031980400701701d91101d21032030801c012078a03140001e11a40d030070808041501c0e400200064401c902c15248a500a406200d1000c2003c1e24003005009583c2c035800060069400403d41e000610645070002491074410302c9464028245102848100d40c8146040b0f00d10100c903072007030000b813590ac0c4000b5005035180b83c1c560001b81850fa0502380c417403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 672018696 1250 672017446 672017449
    0xc180609050f061011070f0e0601081b0a0302090a0f0b09030609010b030d0e180f10061806110f0a110432071206090e0601121509030507050607030b 65
    0x441c4040d02c101d220003844414000256103a6654011119070383c5050400072050050252500030a40d00c0a4075041c26000d0108469074010700d0603209500a0704d030030715940c5a10403845180c4008440344400140240400b600c91441303078000b0030340d42c0d500501d40c41c0c0580e150072081029542a501540c2c2100c1c1c00541244541802c1c00490b5200103904001c00070301c110100441c0d100c003850340d01c000c01c100c2109501c001580c0c481d030301418034034400401c41032a460f125234031350941d90040c0c886a80e900c03501100054413a00c02c03100725000c00d0b200108003e41d1403030703d082984c02c940364080d100240e00450f0301e5103040703400c104020321015004044100116140c132050204403240c482841c1c600105214144a8525490071001744212600c40c1c1007450b036462500032a5910b0f034907180d54000700c0c10b104000a000c401600089240c0490405840099a07034140d00780348005000c0c4010968005d01c62454074203043c550040110354000e040185c9003035540e9aa450038083c04807848c20220f55203515141d5039 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 672019946 1250 672018696 672018701
    0xa050703110d06061d10081c0516030908070503030c120c03071202101407050304110102012909071107030305070302122106100516141203070e0a1a070c180609 70
    0x164081044c012010704041c0c51130313100c101000c01070f810300c0d100c0c1421681052144044811174ad500c000d4500c1a04100d2a00603c0741d122071061071140d200340305001c101454080101d4140c05189801818801d560300f0f0250003603001a410541640000c0c807503000892043d45058a4296041d40a400300d205848048411100100b0032071944031100c404018042e90040b044030303041038100c88100c01c07404000700103c0c0074121040c2020400c40066015540e1701d0080484c03107050950854607002546c2e205e040072203103c840d02d0380b540c03075542c4003600030070200b4081c00003015014041c2c810f80706100044030101506030b000b42101002e0046844408100c40c0b204da07221a001401140d00c100e50190044008020b4050b1010b042d0040000203020820010181d640607030b55007007001601c041c4901d001e681d20036600100c9006022800c0c88003842c14915100c040d010036590400c038100748a1200d6800103910303800603001243c0c0c2c1c484110000c03036100c5080d00c441222450560000c20314034102901e4a06 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 672021196 1250 672019946 672019951
    0xc020709050a09030903112b0605060303030f070c0615150e15031915090b01020609060403020d0302030717150f040504080301140604030807080405120a050703110d06061d 75
    0x802c10318190000000a078031107900070443e074001000119142050000482d190744040d11284800003001c0403861164840900d484014010503041109a50300800e040d20b82c8022522810506c0c200e50024040500504d0040b0712035014110000f1004201c4500984886150f044030340d80d070145001061040e0740c040c144003000c04d425a50805042003440c0c09042501003d05221540402131004605101e0713a54080840c0e640050210701000f0750350b1003008010b2038000180e90044c050031000038070f00c00380001d1150180d5032560082c0071103420008118025000507200030208648061841d101103285032159000b00040c2c4050103c9440c2c4030704000c00c10501e140c0c45400703581410101b1000c101c0d003000340ca045508001169000c400c01d2000941c480c850b40e04000c1c0000004610a414040440068000d0701c00a5440312044180d140c44180c5c0c6410000f0000e205a104000c00d1001440603420640b100c00094000251199a030707075400300303a0700e154009040d891542101165514107103030a80b038 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 672022446 1250 672021196 672021211
    0x903251e0c1e05011d090c07020a150507062a020616140301090e070b040e010306050c04031101030f0608191208040f0f0503121f1e0501030509030403060c02070905 72
    0x80d4110011801c40110071014400e00d0306200c1d441c03412424044419000c45d81d8950010000182403900131000d07060790300b11b058261b010708001c110208009141d0f40142d4441c02c10b40d2996400c01c19280c3d50040a40618030800241303040000d4406602c3d020607004500910180e006480513252229800040d03d00007207c031000c00000c060400d1028150004070fa05480c0304400111384403204a04240c50082981c0c01060140400900000c080c1110b10040d03060364490b00341400745880780070310850113009a00002c0c001c4210415100744540c002c0e07000008483c070007840030442c1c5039949481e6080c500c50b160148007250460110b0700804c00403004c00f0234541c890341481d0942d070406881311035907140350aa0080240110148020501a0030001d41c1d6401a10f01d154056619021b039528034420b41700046043d4030320030810007082000c0076034512080700b00340e44044040c113441c04004401405018100e429280020030010011420a006010300e42c2e4881e0014003400f072a00245008a40c0001d2000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 672023696 1250 672022446 672022469
    0x3050901110c030d050a060e0c1b06070905060706110a05300f0414010507050c070504060b160c080d050409141b0a091208250302100e01020c0d031e02030903251e0c 72
    0x30849800100c080305540b010384fd2161144017a14103d4020140025291401c650104036102500d51000c014100744030000b0911011050090303102d003100459080d200103d000300000958003031600302156601901500507a6500c03542c1d250741c142100c4050760100b00242c13001840070b8615104001d01401013800b41d034104005880d01442c0040381c018800c8101c841c0c10792031000000d1004858021700604200300c20380e8001d0a003108080d1040c2d100d449000d000d14181103400380b04c46044072580344205200c050540e40c0503210003440d0f60366400186043d0070301000d81004500000144c94903d5694400c001080e0340b20742c0d01503607107188082640c4450b041e01c09105a400020382c082180385600301d040070007150180303040301014060300a00b04021141e20503d0710001880341d140e08610801b020341c13080c1164402c034261841d02640301c00c031000c4840344d20130010764a00b0074100c0f6034000b140100707102840d80404150380c2d11040f82840070913203d0300c0c000769544606002100179400c00600700c06145 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 672024946 1250 672023696 672023701
    0x5010f060e0616021002030c19020a081614060705060a05060906150a030b18040b010312090f0b0a050708030f040c12020f010e0303160303050901110c030d050a060e0c1b06 75
    0x1000c0400c40780c043c000d00908541c0c1c244600a8001c10590714004081d0f420350740a0201e041c0c0701d0502080c083c1060780300f0542400000ba180c2004103c1500b80d1801c000211501d60602c4080d0006002240b50150410410080c00300425010b00806008050b40300d07011503523007001d901700302c15000064001c0d84640030a140c40c55002104004480485940307080202d2101106000511155203d5280c0d000c1581c07100200400c04c200141d1081c1602d00c0740c04100286d065126003129070341c800b030050320100210304006100802c0410042c2c1401c101601d00b0f00e01c0c1c0412652084400d81081e40d0403080385500300300b030200304000349800b600030b030807684110080b01036641c000918041c952807070350b8184200d5016513030ba40d490074411500858005205440981003502d0000c00905040318009500e501e0a030380402900c0d0124200c5461001d4040190304040400780303040010980500781f600c28543d10000010340711041440c2d0340c402d5084906c2151a181d11880052265055046080031504070f5000c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 672026196 1250 672024946 672024967
    0x30c011a0a0911040302040c0c0b0703050c04050d150603050d0306080c06040905042f04050c070c0b0f0702040906090318032006160c1d100608150405010f060e06 71
    0x760100701c580b207a20115101e140c801c0200042d100d00c1d00080d40181c14075000c204502c0d0440d2002070014450800c240c4a40da8429046085074010390300340d002a417003000100503500c3c140d0a07020806e400b40702c180d9000901200741c0822101180d00441e40d60300144000608a030f007602c1510300500c10390000d00300c2c038814040091503500c81e03805224620307540d91012034140408085180045180841d140740081c0e0356800038000038440d800301912543c10000040c4824512805444040350311030b056410480c248401c14115411804180380e05207420310a80001d0380d00c40c090032221501405c00003810a070079050051000c40c043c0c0e011555401070b0407003000007802814004207000500c0106904103600100062203900c1041c4074a01c0c8100a51441c1040c84030342e500b1441194050075040a409905604079025054200c80000221308242c03000c12a09000c0c1b11503550000040c600015844d43c005c00003802c480080e0410050145150400d108442d0000c990035403440c422201c243c2401ca4184 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 672027446 1250 672026196 672026209
    0x506040c060807050d02071109070e03070b0c06061c080304120f0203090102070b0d1d010f060501020a2a05030105070801060e0411071211060a051f03030e010f02031b030c011a 77
    0x5c02010015a00158040600c0b0310041403001c4244010b102000500740b0980050951442c14512486801291000120322100c1c80c115aa201000ca0117004180e0302c2008001e04040d0a400c0c0440501c000c6004100055052000350b100702c0c4100121411041d220f0300060112041d05268415980208001c00650382c0016605086400e09400b565031401c0403000400a011488001091021008a10030a1a0040d0003560706e00e000400104820740d62000126138403002004041c29074004031800680c2c4c1c03082080c14501c600001d405110303096503540e001ca4211082183c02c000091030300401480b030b0355400b46039000a03182c11101448100f12081090010b0302c01c80700e00510b64807002c0301c5070390b07524002d41b04260b001c0701c60803d4a50500c0c0032050308019190485d0f80301200d010402003042400303050b00c4480183d80c5c050740c03440315859202c801520724066500c1000154030080c001407010301c09900700203101e0003481d0003840d200c2407807100036400d4030702100e150013042c4c605480719002600c690 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 672028696 1250 672027446 672027457
    0x60304050a1b14090c1e09030c030a15020706090f080c0633031c090e10030f0b061906030905120c06061908190b1008190c0801090506040c06080705 65
    0x112001145a10750000c0310309075200b11195991b00c05441c20300441401200c0001d084504401d406446e109144241095101d08041c10018880360702c45401601285069010302a00c0c0c3c840e0b2000140c500703081c0c0754201d007100c880b01e00700d4890a0004200e044080e052107041c1e040400390952200041e80075a8040a00028407407602c480c4030388174503031f08007a82c04015001c00e9030701034504e401ca002d0700c0c01e8000303200749047d0088121301c08421000c03070510a07000401e94110b1390810081d01e81e4144031fa8901001800c05000e0b103501440740002d00c02815910070781c1c00000e003a00e8a00003405401450700c6070400003a4510000e41c11800d00c0f44800901000c151107600c60001c40e10520402e50804020f071004100350010304051003107115603500c04656108030f04160340510a03501d0b040ea18003103604ca6255141c0982714072038000c44103070034001103862000c0490b40c1c13080c18101d9400b61101819400c490604009483c1684980709010600060450b00000340c006c1c2e113001c2529140034080a0144d1185 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 672029946 1250 672028696 672028699
    0x30a2d0b0613140c03010f06050f04140102030702120d0201060503030721170c04060e040c020a060f02070f0507140904050c010f2d090b04060c0f060209060304050a1b14 74
    0x726080190200742c01c0d4080c065503056000d5040c101c0c10070807400540c9800c00d0140303c00841c0816408242540100c1c1a508802200d2581030b1805040c072072034102e100d030000c14840c194071041c055140140d5440c1c00361100c03609048001e0400d096a000001d080d07030011780c40117000e0342080000401080725040a6080d420020b00c0040301c034a90008100d030802e6920ba20406414084814031114526141c024802c90380180d4502d546c1d0700002040000301c0700404070440c096070002501100182c900c0c1c0244030841034940f030040c01c204181d00c804075031403c0118129031540040c0c0c800e11003808c40d4a00140a01004d44d001016490945c0c1d82917130300c81000c803010b070602480070400400c1c1842120207611821120054008074510403a0000c1015200d07110721020030a24880032415640d03a8041c0c0e42161459a1480a1143c15803201001700340076000a9450580030403a00d41162904c00081d4000c9120708010031076074016040c442800d140060340d0340711702056400304016840c0388a8001c800600c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 672031196 1250 672029946 672029959
    0x201080c0304022803060b0109081b06130305010e0d030b0306071d040f0905060604150e04020609030105010f0f0806040b0711011b02030703031d2109030a2d0b06 71
    0x126400042c1015404041031104c000c12510040d07400c001840c0d200003124030450341031241d20b110400540d06001e89010342c408560016000820040c00003802c2c0444141c00f40003640350a10703c01010a0031217080c0c01c15078407691101c1c020400424204000309220345203240c1000702d5655940000e0716090080d00140400800380381d6507001e403641c499801014800284100990300840142d24090008580141c80b0350240c1c00000703009080034054000d04e0403021368030303641a41c24546292140900075100741c0c1c0203481801b10b2401070702e091107103038040c3c080d001079404564a041e00c4102c040e0343c150420200d0fa00250140400110b24070306440d0045c9560408400b60000420703254014141000403121905510030080c82c516004002000c40500980c2c060029089000d1304004031105040401002e0b42304c07114482c42c00d4003101c10b1452a2201440180c13074580c0140010340b9003044400141d5044c008a0b5400503103041e960300b0002c5500310140a41200d03841d43e254000b240381d004044034014030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 672032446 1250 672031196 672031201
    0x270d1407060609021206040c020f0d20010905010b330a0c151e0911060a0c0c0609091406130203090111030a020703090602070b04091508100b01020c010c0201080c03 72
    0x450b41049018208454085407502c124690101802d0000d0ba6424000ca1030704600c041524404035206002c2e500040041105007204041104c84903451004a040c0000340c17044800d28407001c1c020144907500500021508210340d80402c00d540604d200100182a0b81201030f100c00c0c2c001d009410400f140000019840d031800c000c00740d0f180d01030254001c6c0201da5603038070080d1021040d070182d0300c1501e582d02200011907051b0b40307040459400503005410070010003124092860004010400c40040b07192542e42c43c06a5510702094100b10b42082000c04c030012410700c182001072041c6200c1810700316030b000c41d90070410042407000500e0900c040b143d940001c0007400003a401d40004850303210100e1001c1d943e00c0d02050030740c000c0d0130003841100020107000300010304600c0001c0300e01c02da840e0b800410745803501e4038088000504122128100800040380d0000780b00b08107001017a504c4030124000704821351040002400d103481e040340389051050207400f200160f6800303144180e000ca0010750a56807138 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 672033696 1250 672032446 672032453
    0x30a080108031c0b0f040f150b0412020f030a05060708040b0a0c2316030c0204050a09051f0b040c0c0c0602030c030a120b061b120304020904030509040b0306270d1407 73
    0x1040285001c40c0c01c03904040307c2020171421a8000003100410303d007860300c0d007130311030703040000601c9940710f043c40d424160042c440241c42c000782130305240b090042c01c0755010300b16a81d1340d03801e080003181c1901c04038040320100000d01601c0b81c072141d4844c06581003040b000b40c1d004005005030701e020442c038a42000140f60103948042c0355007100c882008040c02541c2c000b850f403a0081c40702e190610200d000e20704201c00300e0642041ca000b50300410354020301411841c1c03008829480085a49086240a44d842c0c4c600908240c0300c40c420304100a403580c0c1e43c688820100d00b032802c8600c51130782c403003000c40d0300c200000e0806680110030303a140354100d494081000d141c0c40309042c016100b289640303903110340009211000c107008016a50b0745030b045442a120703d118045d1300882503020403a0040d40000c1440c0c00200040e00c500c00401c001c110040c0000382d1506d10f40c02180c90900211110320400c0344400207039000072816807c408044200c580100680c00d1070120040014440780c034074140c0c3c0343d80402c00c031081 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 672034946 1250 672033696 672033709
    0x90105190c060e33010614160809100e010807140c060a0203190e03042d511101020a12060603092a09020c030a080108031c0b 55
    0x500b80c020a0038400300044074811a19850009031039902e4255102242c881c0d000444d00000c3c4c070242c000680710f002e81ca440e00603500802d4010b040400b08400b04541d00f03540c4658034001078454020043d460701e415150040c410441c00d40020403040c403da00c18034007426a4400c005580c040d0461900b18030904081102c42d00a00402007400d080c1d0007141700f00304545441c3d40c059441265000b0381a03008a031026002c00445180d2904404250002c01c824480c51207200c6131014121280d09410490040d102030019203015540c01110030001132211400090045000c0110ac03a0b03181c2040440700d05084080b111008031071000d54040740030098101d44143d00850f42911040d01410084d507554150724030051082c3c40010410f480380d8a01403012412030b00c0303407041d0990960321445c80b0400e51004045001d12035452100300c1f042a10a1074045090380d0b00d8000346c80111118801551181c40550010b003000f034050300940c10b103900074814204d501ca04420800c0e0b0060b40004002820107140012550 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 672036196 1250 672034946 672034967
    0x90c1701060522091a010503010317030c04090c020a030806030c0901050f010e0a1203021b330412020301140f07030203130b0405030d0b09060d020103051f030c08100209010519 77
    0x2803141150700012580c10395041802c9a2001862400405e5401401598240428040644030340214809580802d00c40702c01560000c80c03000302e0600306507442a00c00c09031101003c1d43d0006800c154008001c050304600c00c10381142c0100c001c0e082440c003503804100b0140c030521902d84280c2c078140020b0001d03409030303814031112000038040e07991036070f12006031100407144100105d005105000680211000b0300c2c411146400000304010400041400204501c80d1403980ba064000040682c09190b054075070010801000b0581d03080c1c03445ca0060040508550440d44038110300e50800c1c0401c6103482804e801c443c0c3c400404d0130f00588031f032a901451501130620140042c07040314280e050006019002002c0c00a621010405105040d199020f00608080a88425810149000d5100d005600035040b2a9100000581d424000035041311180341c150301d65441071307540f41d20052091119680511201200508070340c404c0d1f182400c2400020300a00c41e05c03501c200c0581806000503103043c4219200c44 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 672037446 1250 672036196 672036247
    0x910030c170c0904090c06020f24040c240e0411090d08120112060506010e0108061002010b13230408040506160b0c21131416060801090c17010605 64
    0x1040b032040c42d001e2003102150150788007501c56513004010000000402c8180782b103c5654012200c45520a82e00c2e075600042c03c00c540103409140702040000c61500c8420b4140418820b610809144280c0908032516000c0201d006c0c42c00c0512030291b01150f80111048007806079410b24001c5002d045c017800c42c3c0030700c00310304a001e9004c0d80006040c00256810b00406405000200070700d0301c41d040152020400034040d42d01180e40322002840701d142c400c05021403806a0700005ca00c42c001007000030f5146810604911210b541c0f60744896030702156150b0003e4a0003c507441e0150340c1815180c105441c012403203000d104050010345004410320b00758800f00c42070340c0084410fa8600b403544006c010b60700300f1010030310040313424403070b40c07402401900c03529002e0850000180b25095554a4200c01d10101100d1502d262080038031b414590180e000c1000700a01c0941e5400340305504001e00b0b0410b680c072040d010b508000c90b44201200514601c00524119511803c065a0710f404400300c40e0312607503445034900b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 672038696 1250 672037446 672037451
    0x71509030306090605031603110607140d110610090b01050d091a06270417070602031614120901060f0e0a0501080d170c04030b04080910030c170c0904 66
    0xa0109601500b00506448041206201d04c94880081c150f69940c141040c01c0f50400d80c1c41b0070004100090140498000003810842c644440c3d0f46541503100450b190444441e4841113400d030143ea8400d013800c071011554401740a450a02040d84c00ea12500d0b8050402e4140d5206c1303054060303a014400300c486241050809204101fa82d00b4546c813031511034580740c50a40c21002c00240a481e01403180810000c0b0001900400556200038070b400c0701000b4400c40b19000ca0820500c08800404080c08019204103000340c1d882c82e10b203203801643c1300080004c1d07040c8440c800c061400f00c98141c0030758030880300078040310b0034580d0346040441c0940100d80c4580103580b8034050209014492408081c801c4408400900240e40c0e204a0f8540e144140b913a08800540c10304121181074550101c9950080390607002c460a00361661120b03442d000003030b6002c40c1c490f0000201e181d960b0400d201c050a544103141003c00c04410000c40c043c01c011000d40121400e0428640010340010751107094590708071340034008 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 672039946 1250 672038696 672038711
    0xb0703091509060b030c01051804150e0a181a04150515030c0906010917010b04050c09030115030c180e0d081b0310090216060c020c010e0303040e0c0715 67
    0x2044010040c032202918180d0500503135503018100010f2100ca414010307581c0c5868065186c980075010480081c800368007a841c0e02c14440740082400011000e405a00140303203003401c01c0003030581100e0b1a00036004a9410705001d8002107140c240840f203052a0481c241c100d20740d92480c2c0f184681100c0015044080c1c5044240011861b02c40aa03030364080d01641110100c89006003000481802200e500f0b00040b00c02c1800c3c0036505851520038942035180002044000340c0200040c19a8804c503812003814902041c1c880702ca24090090403800000300e80c0c2000311070308589803020200a0360054442001c01d00c0403d00c580921a4401c282d440c5026054558030369000f1401414048240c810301c0307113420310441c46002c0001d000b04890140805c1d905200086181035402d0b000b07500320160540d8840b0803000c0306130104459002d42e420002e815400340404030002c83c000340a01050340b0460303000790701c00d02c8248907020b5a40f40c0190070076050502c060f160021440c0c00c180340816000c8908165080110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 672041196 1250 672039946 672039983
    0x90c051c02101806051c200703050702041d060403180302031504121d1c0b090706020607110a0f0206091012050c070b070e0a081902040c020601050d0b070309 69
    0xc803c0c200360660b00401c3c100c9039070362008803282c2c02010700801c900320813184282d8100b80b15034003008410240c050042a07036011011014240e401c0254240c4c0414800034192086203090311030481600c00c4840b1051581e104860b03115a15000242b009091003060041407030b5003116040014001c660003011130320b50142d0480d42044802044c5c1d012603816425440141805000b4025003507804e4100c8202000a443e140401001c51610070404004900031260600131507a48500d4a1144c0c91242c000c00c1898548100240b602400400e40000c1000440d810444503e004c2054050706400001c181800b100701d0000840c00d00c1040e02e20350340314104c806010301440c1c0000d4240e88810000c4020022681c9060401c400c40c0301d4214003c121a01da5030000386268003503012076602c0d80d030140c1541c08040d02c0c1e40c03504d45024030160250f600700d0300c0108560114601030242c0c6600304c01502c0508a40d501d020040303840242182d1000b4a0030302e1000008502c1c5110341e210407416078100340807503403210031904c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 672042446 1250 672041196 672041207
    0xa03030201021c09030f0507060b040203070201091101030c050d0b040e15071116061209080d140a0e0c1003152c04081801020c03010c0201021c090c051c0210 69
    0x42c000d141695a55034825040400e071007122503194146d2074030360428010b0041220143e010380401c450159640b0130404c00703a210751014603c591500c3d0000901c00007241031422031800c103030b0307810f904040c1021489983c095012096031088689000701048800f06840001c0180642102031071040c403482e000e1000d5070341c8181300c2d0350013020740740c07030308101c0f0b0fa0f03192460390b103840030400700000060701c5600802000344180f140c041150a0f000780010060629074400b0101c1c0d00c800d0081508940340c0507000f506c050f5030800b2980059040703100b007040403005001e1544034180d000d60980310340a844810300581d8081d400c04042c00d9402000c2e0454261151012400200c8540100c0c044c2120309002c0c0600896010205000fa60040d03411410002c2d111044030180d40703a210000c1c118040c0a0708030142d46c909001c0ca0303119120680000d620741076102d02001c202041249480600760030306045402180c000c42c1c540040d640706840d000450244402504841604200700940105009181500341c55211 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 672043696 1250 672042446 672042457
    0x1a0310090c14061602012105090d1d0105030603070306090602181e040b0102030c071503050c04062a120f03050c0a0915020109080d020715091a040503090a0303020102 73
    0x10303100019407607291801022012458401103070008070800041d25850411580421001e205140403058842c002200da50b4030400d0010b5400869207a000348a8140d50a00106070b0001042ca482c001b4030780920500800350310001e02c8581840000404101c69450600210010f590410710521095542e0b2030540020350100203040317940303042c168000e070181c07501d82e0002070b10090810a01c20700c00e540004100082034003107070786810340c030040000b2559001c0900c0754030020300c1c0303d07100041c14990781c01d00a0142d68004221000c0e400040001744400c58001e600318400d5040c40031340001c4041520460014000e60325400742908810072000300b0001e80c44842c05080301116034080c07182e516400c0103042a0301a120a00011607030003401482101e0b02c440b00e00202050b02c1c070000c500005161a200413a0b030010030004941600000c1003001d0058010141000f90543e01c000c024190450310b40d034107150700515001c52401c9030305010030140704c020070a1354400318008240b40c072580e651b890040d00130b600c00c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 672044946 1250 672043696 672043703
    0x20d1707051f0c050d1512080301080111040e0a0c0c140a0302010605040e0d112b080708220303060f06020106031b03050c12070914010504050907080d031a031009 71
    0x2e04121142c900d041c000c0012140c2c1c244c0301c40342401c200390600030107050300500d06140c0c030200c4800061a112141003080c400d50040f0348803542ea5041c07440d030a00f524070825102920300c004001c100480c0130124461644000c581000061f80b1400c440c04179808a0200c0300a40211254124015a01c0011414510b4140700790001c03c14a83c1d10012303c410b607900c5210490a80d0041040312440d58040d101d0000400c41c3c25095600c100b99110050b0f801d0030404892051240c1d0440c3c51502d4141c100404c3e9401c4034a0741000c01c4140741c03013248030040c0425150b01c208101720225429013054001d41100c0c1c050018000310b656603e45524000b4002c11940c84180c543c0c554601540030300040000e0b10b001039941100c0540180c1c2840d03024400300010300c1075504500d2140b000d0015202c1882d125000400c0c41900c03807007140d54903080412007510b6002e069802c25800045080010b288006591546070b4540d003404101458001c0102490311002904503030140640301d804940600940c0c02109110322 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 672046196 1250 672044946 672044983
    0x201181d07021510140a090e15132f1201020d29101106160f030b1e0402120903070219080c010c110d060e0f011404020d170705 56
    0x4507118143e019141554a29803000c407009040c0100880d0000c0300c43d45040140c8a1030519548040306c5040315400840384d07450780c11104100d0360011070030102607080780744a003d514102840c0c0d220380360034500550490b0101c00c081e00c000a161008420782080301140241590f000c10952404503006c1c0d800340c4040f0f10f085180c004001103200c1d2040c442d065003040c101c81105200e5140061148071201d0398580c0c4144200747c0254504488100080f0340b00d0b50109241c04a006800000908003103070a540400c207240c2003002260064a8501c2c03004050b02d20051280e80041e001d01c00300b0000d1141d0601c14069414003800c00c41810000001040702c0c078805d5421065054880710100140300d0540607000d580e801c9410078807407c0d84101006109203001e000c3c0b0b003042811840000d4410a03000000300d4800b500d9142e02e0000b0101882000c8076507031200000d000909500e0400c0c41c400c10010402441402c0e200070320000d00c05030040c04d00403001081406547e0b00070f5030404581e00c2c00e0700000d200c81e000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 672047446 1250 672046196 672046213
    0x20310030c1712031302030a08040501020607030203090303070e0120060f010e040b15150703170603010513060509010609090f12090f03030c031101020d0207060e12070201181d0702 79
    0xd0744598014080d1011101402c440c02118224410f00e40c000341c038405a44c3c0c80d500c05200581d600348100484144900d045541e9189807800282c01c3c030340010041d409140c410320130410007200202c22264028075515044000d500d0090060340d07014101c010440c00406020b030030a0700c2002c001003841c01f82e601c1e021911078030707a1390f142440c100c400c04482c01041f088108020030107c800e595030405203c4002009000903024800c03c0208540241ca000d8000407608680b00503032400911903180c20407402e038001d1090345844030646501c001d00c08030050410341d5507000940c890700300b940a5000b810b148141845503004138100841380d100c43c0b2605844140b40880c0451070507004c1c4c0b0050040325001340f4078044440c91903d0a40391603481d0002034044c020300205240304840288014903100390081c40050311802d0b1410080c040700c0d40003179540f019502c403411102604502c01e042d20609542441d001a520644840c0e181000c02541c0c003190700c1c803009c1d400d04000f901e40f00020382e01c1020198210b64008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 672048696 1250 672047446 672047459
    0xa09180b18040f0f0302070b030a0f1a01051c0209060d0b011701030c06080403180609080c150919030507090b040b030a0b040312020c19050601150503060906040f020310030c 76
    0x405550080409803020040000110001130f0100f4260103401600c51161f503e017110380e141e510469122030301342e581e048101d00115807881895803035110702ca580180f00c001d00e40042c3c030740d205e108401c0c0c1c1c80c80a0400d000b080c1c8a115012210740a6002e0542601c0784402200350000c1c003150807031540410b620000403c112410340084c18122508804840b948510305181901d040f071010f441501040088134014071010340710320703210004040a03650302a8581c500f6000c0b5041c000c00b5410a8802c2403d07070100340cac802aa460036100c99442c12a0500ca4480c180703081a034070600950b00c02000760040c1c900000c1c0c0c00320715030f02c200b201c000191020301103a21a842099240c640146005018005000100d80441e00c6210b9800c601e5409410040c6406e40c5124901e160a012040f10341c82e0200c04100c0800b0400140300c00c0303005200315100590115070020007e410740c0030080645000e6080c80d4001052a234550f0400d40a014103040119683d0a0074500440d00d4445800140c402c030042c0c10002652 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 672049946 1250 672048696 672048739
    0xc0d09020414010f0b0f07020919180203060c071502031302093103080a0b030309190f060306050307031b030611220b0a0e030a0503030108150f0402150a09180b 70
    0x14020f4010b00949880381523402c11818041c0a4480d0001d10004881ca40c411101031103112808806a0101c40840fa8648100362030820000e00300c0c098640240b10840c00140900b4070700441d941c05c1503003d6200c1d40c43c01da4200c11444141c5000e94000021014480e0705c59818401c8580c3d0148210f031356543c27200050b0404854100c4250040008807420700060088915610480708018024141c1e40f034081c1070400200d010000c28090400300204610411542100b5510240103191b141024000d00e0f103402e0019858580500c40588070900000c59031000c1c089441001c400303550f10440401226014141100c090b8004403402004030f0304160025010964004d160400c0b12540e110141c60300090707220455074840d043d400d05030544112250305000450a2000d140070308640b200410700a80d0801c00072480b4000505250b010f1204103041c440541c031400c08100000c01c0c0088503645d00e01c00598200c90410301940443e03040c14404000c0006814180c00c02c5400c1c0408980f4030402190074001d00f5038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 672051196 1250 672049946 672049957
    0xc0c0206030406051803191b0f0f0311070b0c010b01090e130204060312080709210303110d060611070b030c0405220906061a09090c0d09020414010f0b 66
    0x501140c1400060001825a000781d070b03010b14840300b0b001c10904503101003440c5411200e0100200c0200300520f400d62940320100716030030007900740084400780590b1a80c0c200315a4021300a804204280008400e060140e60280800a51802228801956081c0852443e0485d2040140950804030b08484070342c429850710301030710902100346030315880749071007400a0110302c041240c0240e182e820010220b00d82108440c0b161840e901c0d4642140790008004007074124642008000c1404009080c081d0349820f5000d46106038141000118003a40c00360600c4a800384d050b8041c0054100b10009c0381c076603403140e01406800441001c5034081c6458001001444c04100d4400402030400c1c0030030040d6160042e4100254050b0f0030701040f0b00030078031524006580d25403005940b41515000100030280410741d4140c0f040d412404c0702d03030900c0607020000d605100003030541d00d14802c0106460a0080413035116030081c1d60300070000c00054034040500029503400342b00b110084252120006401c86411013143c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 672052446 1250 672051196 672051199
    0x60409120e010309080d0203060118060f0516050105130512310b070303091208010303080604051005180115020d0219050c120c15090303091e1009090c0c02 68
    0x408400c000000311420585500410304140e20307040a0304c049642d07100104203100325040701503603038a411400508440d419003801d804c0064942c00030010160f0160790b00c0f0480c9001c3c6402656888115440780152114042c05082546400140006c40d280740052070380c8244078400742c1d2900300d9411080c4960b4014001c001110440d505540e041888003001035159901050f002c5424043d240e148280d05500001011004030f0b0307840620f6018444030074802c0f0b800c0042480c0186056045a50050652002411407800385484001103444403090240d203d01816003c2c0c54071f038010911903601d0403032020a101e060520b01c0c1c038140c9015803510119080ca20724031150010002201d100c460511b1a8144000986443c000d091100c441641c0d81103240c02c01c5c5003040001c00050b41c44d00c0800c0690740030301d003446e14190000c0218480702d84000c01642c456013421500c43c0d00120050314414542100300c0046540000a0414102125040326525040d52440c060404c007141030000141e80342d03004810042e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 672053696 1250 672052446 672052463
    0x60e160e011e05090d120f02150c09060c070503101401300503040f031a06010f08011403010f020a0201050121030845280b06030f190209060409 63
    0x81103154018001052290f070003410460305e03400b081d1580e00010060984801c00141e2611203001c1d0300f43d041100f068500c4040401e0385031405c000c000845144900054030b40a05401b0491400f410000d10001000301806829140900961010000240480d0700000e00c1800158004100c0f85506080402c208104020a40c42c41d0b03040a5155031620b1030040c2160681300420010810180c1e50b10000d009600c501400304090102c403084420302140200303210304010a00440240c0d5640c41541c0c9411541ca01d900440c03103064800209000d0f104c00d0304607040d610b0000804091b010b9055001034100d03016aa07100080c6140541e035a500d12000c91000340001d5041c1e008a0300244c0e0b8810020403480200e003601400740c0c2e1910f6079544080d641890564080d007016595210b00c1c0d000c0c490260a40e0801391440051070302e68402c1501608480406007001c00d54400007440703a2070400c440c1743c80c1000d040c2103d0303d85180000f4401d40c0480600124021202c440221b1121b003003d002e20b441e09035019088 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 672054946 1250 672053696 672053747
    0x14040f050607050f010c0503010e1f2c04110906060c1005180616030509030405060f09030312040f03020c040b010519090b0403030905040501081618060e160e01 70
    0x4000d01500402c80950b410300030380100c020321100c24462404c00c0719540c1c94160b1a985008034608281e070303006101c0341c1480701060036415042030340c0140130305992100f004440c40c000d10284680c072580c10300600359441a5180e050200303000700e100703200c034000c80229030110344e543c0c80100b4070a05000b8100f4421b81540314240b030740c10108190300101d5100342e5400d4064409010805013a242c40c2054404000b1100c0076101003c0e5260301d40115a40040c40c100218602807410022031700904c02c07400d0701c0055110208003480142d6003070003180c13441c90070361840c0745003418203092110300c40c00c002c03030304070054480c140641c1c00d079042c24041e48940030016158a400c01e000340c4a0328140b401d03400560004c201d199a4080740c1907a00c28040d0019500943d28840e4403411b250501c011508180c00900703059020f035040081c84440c0b03019003020768000060794402d4980b15810840030700643e4000c0031503810342c1000c0081c2d0141180740e45401c0e442c195140340c55101c0d140d0040d10b0031400000c00d48000300c0419003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 672056196 1250 672054946 672054949
    0x1e061404030b04150c08060306070f0c060e0309040507020d030f090c03151409100501080601050a03170c010204180b011103030105240a090503070b03070e01030b0d0f08040614040f05 80
    0x1c0180d0084c0509613001c1d140d500c00d001c140458001c0325801d00032941d040d084c02032604041020365804156400d0510302000e01c4080075000e00d00746207005022a46494035100c41620910a40365205006007041c041801e050320040d44450407501d0010002c6e18151650380c8100140c05001030050b040903003528140d0842e2130706514019103118226546440d501f085481d54690341c12244501300304030140c030340c0e1069641008107940c0183c3c09481168084001406030303a0b104d901318800c8903480041540c041c036250300d041c100341c003a03600420011751012800045003015014020462a103100c01080441017100040d501d400c64410028410346c814001403059080c0320b40f007021400140c0d4003682d1440c3c1c000000c0401a03000515001c00207211020810050404226203006841405221802d501d40000018501c800c1c1405031030406850311000d030f45a0700c40a003240750031134000c1a00802443c4608003008158041d100b0380707001890b21419078121103100420748041d151601381d40640c3c01c0c0b5140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 672057446 1250 672056196 672056213
    0x60406030b120703080903070611101d120403113c220501060c03050909040f14060106110f0c0f060f0a0c0201081303361e06140403 58
    0x1010390b0484004904200c11041c10001c02d00154441c8000668643c020014542003c0141c1e120f001801102c03e20b00c0340950000c5580341034120100740008052000d043c0141c03a001c0d040050898602a000010391411b11000050064a02400440200c2114041170201c0c40900c03049034000c0c82500b01d115405940c080045500d05070896070030103035a910303502c00540301d0320441c0410090251010042520310010b030003401c0c01040603060a10100c821074902500a1003080b0403103110300c14000001c1d040002940d0000c0d02540c11440031124081c900048175a955800e00440e00402c00541e40d9058090f03000400480307540042014100d2803031a00d00f03010120344008a4aa48108140503101e0101042005800c200c0c00550350200d40024500014040074001381005139100d0001806c200032130b4100c0003681e0011901108800f5140c0c80e48000f180c01d515103005c1c40001a0564800612000a1100d546e035400a91002c00d02c0745941c3d14060754460440381c0051110801030008001189901 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 672058696 1250 672057446 672057461
    0x1180b18010e1006030c0f2301093506070504180f020c0a0303050705070b0402060a0c29160215070e0a0e07030b0f060f0c0a0204180b0c040506040603 66
    0x1040007107903424142e0030302070a00e83d540001d0690f1035079605081040c0681302d64004005c000403401000180d00700329040000710741d92848040705842410840e4050b901c2810389600603e24500200060010340740051031119100d81c110511601c45904085080c0c8040741c4180518040d071070351490a4501000c59144922200b8004881d030340e11000d07244400c07800d0001700b81c06407000c4c004e0700e4000b81d45e01e40a4110b58028000c102041014050140040c880d460820340068049922039103d0206103011114401004d5004002c81c0404a401c0d105503191a415400ca2040036000b00040c0e4423a9800c0001406180c1400d005038402c1e401c01c2e03080c0466100e900d400a03000c0c5006400061842d001c0360b10f0090301e504c0321141078502030400002d150301d482a0132480d2011502320309003029030400035080303000310300940584080c001032450304214208101203d05502600500c1860741c1141c5c3c020050320b072450180e035800c01c02000604901200c00807941555002042a4209820104120002d01d2071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 672059946 1250 672058696 672058741
    0x13170c01200a08030412170403020304230a030b151507030e0a0e0405030904060b1608090a03140d0e1008041e0b100315061404020708090a150201180b 66
    0x4410010020039080b000540c40355000b006d038241600c0780c0300b50003403c043d08141d502c80c0404060303003031100003a0302200b143d00300c40faa08040004c0c43e48143c1300e0b14940e44600c0700c00398888041140002040045040350344100542484194066601020b100c14521001d0954203118003c009100000c0d005050550b021003010348011146030b26603183c203228803402d4409a0f40c90307001080d01c62051505000c0c140150070700040300343c2003155001d00c2c00380004811000030488080480c2d2100c031500c500d40540000d40d00426500307000070f400f05807540c071425500240d9000500208409180f800c2c100340c5c441e900350301981c4d2000f807955292280108905a5120480d400301011101004640001015409040c081c491454003e18601d4890700120003460101703415414a1010080044501014411071005a03409aa0b45046103403107002da10969416680c00001c1d1100807819010010380603a1030307441500200f01007140207041c5401d184502c2001403007210a1070000b50011141249003008210 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 672061196 1250 672059946 672059953
    0x1209060902060d0902090601050f1b24010302180115050d0b0d050c0a08071d15041509050a110a0c0c03140a051e0a02120304030813170c0120 62
    0x820798001180c81c0d001600185441d42c90720710520035071501d5490541c118100b401c09900c0d0201c200509060741c0110b00a01301d8404150080c030b2264142030140c4421804422031811014041114941c0e044500b0702081c0d02174820070340101e948080080503503069500181540c82980f00292007115142d003d088560105500c0d940d643d01240c8907600001103540c815000303000c0c05081c0b08180301c2107100b15031205059500808003003000b00d0b10000d2154110b00c00c0c800e00c0380d4640c2c0f00b9900d061141c0c0b86c03100182d00725203418070701d4801c2001c040520040d10300010341401303240c84400040007520310400d00b00000d25820022001d104d40146d00300f40312140314280510340b20781c3d03e03107410101e081403440c0344000c1d4102c42c0708901002014010400c01145c2c502d0301d13400c00b0719050811643c0701c0c064003000f03000e4940c480c007020030340808206480080d03511624255549002039060481c01e1754a115024112043d405856000d1001081000d00c100b0b040c3d440494006505260b007000c1003844214501500 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 672062446 1250 672061196 672061211
    0xb070503090a12260a0c050309030604080a08010801021e0a11010c02011d0f0c1504030501021804060902091003180b150a08060c1e0f0a090305060c0901120906 70
    0x3121039061500902c10454821a03e4100382040400340480c006090b00419010a1042030449148142c441a0f00e203840c1c020501d010314600b01d481d5200790b24190368544036000c10003003003014540003494040700340d56500c0c4a49e641c3e00300741c500f80c2c05224820104101c14041d403030b039081c58a10140076a4002440e14481d107088840d00c960840d0003000120300103035119000f00d01c140e0082901003e07400019130082c6000d035030035801283c0700c6035000b904522030b440c1c03c0c3c455450501ca032002c0e80c02442c0c20070000c55071020724a140385000c0b00e00110081c0110305098000828806502c03d680c03100101510145060f1841c110850003004013042458200d8003805010000c2a07c1c05075180c80342c03d8021024502011120400c204078045511400039a442502080815828203007501c442e03032000501c100032a10111407050650080300c0c00520152000300d07501142030f41c0620454212401030007920f50580364200c2c290020302c512903115003c05c2c06030030000d50059955101281e01c6008500c000740320b2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 672063696 1250 672062446 672062449
    0x305060f060c07060e01050c030304060b041b0305060a061e031d0d03020706181707020103020706090b180606061606060312120c020105011a03060f10180e010b040b07050309 76
    0x941242d074000712150300c403420903c04140c1144585911a809003816400c0c440c012030300300da0340d110081004100c6921145001c446888070741110b00c0c03440000e00d0b10b80007c224044014000e02c02101d000d4460b001d501e03c0051840e0040c660751b00d07009801481080408925030054010b005018148480b0512034520181d69940074011503200085647c1c01581d1106581880d50654030900c0c003400000c00e410310544c4c00a41c00c100e8461030351283d8800503031940c01c0f078001a0001c1c0035042010341080d0602104804120701820b48a105544c4078110b1081f41d281c3c0e0a24075500c800c2100c41359080038007000741400d8030810819401450344183e80124890f51203948030024104590b64407000b01e00b4021140c07a0001050040100882c031900c000c00141d0314180341c0ea82401900c07040103e98520020104205441d800040c1c05c900a01030300c2c1141c0c51842120040070710380d02e9520380034030646900b4045480c2c4030820000c0c0c1211101c00c0402e08060030070300010007551005100300d076580310410255419 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 672064946 1250 672063696 672063709
    0x80a0c1205090a0c0f0f0b120115050f031510020606220f0216051506030d050306040f06150e091e090f190b06010c0c03060507021e010506030c01050c0d0305060f 71
    0xe0441603c5c0303a0500362401e4080c40c40180190440c4513040030500c64003581c80a0300c1542030444002948518000c0c690900513119841412141800c00c240003040090440070380c0c03003044042c0015104850300c4441200100d817255030a032905030380102d000c1c003403419103c1791644644603004601c0001035903143c1218490104d0b031204020f60351030103e01c000c7c3c000703101c418031246030002e43e2488002035500d4801d00180d15a402002d00c401403000200100300140c40700e61150001407400b140400056450340c01c030b403038403074094120f0b900080d18030b40c050409800c1080a86026590758902220400c1d4048604800450000c0003803240c0d00c01c502135080e0304081040b8520b46103100c540a820a5a81c81c140b4404401d002420181840000f8500700c0c0000c0000700341d04102d03a005803001800d0b4035800012414981c140c1d8280c20409140202551300c0d003170642c0150300a4004608503400e035065200190385500815800b00400d400411440010b81d0181c3c1007541d119000400b9030800c04c48890001d0803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 672066196 1250 672064946 672064949
    0x209150301030f0201021203100603151d010f090e03030604092604030312020909070e241b060408070b0406090f1202060108010b03030a0e04090c080d080a0c1205090a0c 74
    0x1a020304110f000d806558042c07010f81c0c01c0040b2103490b10316514000e444410700404c0c622614040540d01e5800e0211024400200d80c054034070f050600002000c19490400b0b880c0089c001c010080c3c1c0e90100c00602c07010b07544904440d1940440c040c43c15543c4030410480245001001607480c80720703030840c00340000d05045001c11030203501e100c0680c40381d081d401d00414041020896005283c0304000c00010360743c69614490748024203140c030121584042c400308060703001c074004102071300c0302982d4000b0b280c4500c2d00251421181e40225407242c1503003040c04a6407000162070207064a00100110404941480d9441381c2c420701601d400708840c0000da56140c00c04031514400e0740c218040e40e814213125170703050224070300500070500240320381100c0c00300183e20380c491003084109201150380425001d456541012a103031750804485030219039aa4003082d242e26a40380c0c03c1e000a00302c5400681c028009205028a0b0300240d541c0020540608042100034500540110705511034200d010300041c400310324010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 672067446 1250 672066196 672066203
    0x90d270e040803071106010f03141510061209020d0206030c12010e040b090f060109020d15030606180203040f080706090f0809012d050a09080102071109010522020915030103 76
    0xe0383c0745400d4400400b8000b030342e844100c3ca038004074010060b491740c2040c281c05607500a070000f0f1544051417082d0340342c04207120110003400070860030010750f00e00c116158411520f4989900c80c0108580000300100c0d410104000d5106040c4000c6130094207001f4042c42d4041010b501c0383c2d20740480e040c00002d945c1d000768000240542c520081104001c4450489030b000400100181101082082c1d255229041405482071541d40841c0c0c05103644c83e140c01c264103c00075507401d804415201d082410142484d8090013070421024003880c070180010b842103910480c0c00c1301d964074a043c2c1665519005620440050f26450780b9500e0103c0841d1041c0400381103588120311896440d88e07050005421aa2004100c40308480b054240c08000801c0b4003080314141254a455940e80c2c405010a0f90309003e0b64014801070761002c55000d0401800c10224140c509040740d40c03030516030740c0300c04104c100c4400001b03070304001588245203041d501c4150058800418001c00310101001d15440c50700240c1c00c00d91065 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 672068696 1250 672067446 672067463
    0xe121e0412061410141801080703120809190c0b03071e091d0406180609060506060414010305061c0f06050c030609150102160e070206090d270e04 64
    0x500400c0064400c10079000c3c400d840c1648589052190b0b02a081914400c2c01040c04c1c003c940310340655200c800c28800302001d02c4000c021540c462500d1a0f0b15606400102d5034486000b0307454114502809945108400140080c004000c0100d002d0240d00b00b016401c0f25914961940450001c0c1001c01444c030400460303036032201548076440150800c40e01c0c040008240010f0b035000b404500300d038000d035011400c200406608035032528a451001444110030544100013000c0c039100410500d904010300301d80c0201c001b84101e44600c01080303102c0c0301e00c2c441d425030f0450410f00030244c3d500075003100c0e81c003403002050442056010030491110b040441d504855000010000301c0401503a0311509400c200d01e50035440c11443d1440c00302d101c0100c080c1112a46140122810702182c0c8204900d0341c04030861202980300d9075580f00001088907082c0c1c0d41802501071076000809484000072001e0380e02c2040d94803071041e118600103801440c01d6515101500c0070000401080d2040501403003801036200702440e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 672069946 1250 672068696 672068729
    0x11401140a0e04111e0f1605100c0207050a0e0702010b0306072007060806130204050312040302090f27030c030c0d0206070503040f0b06030a051c120e121e04 69
    0xc1108880500e11160900c10041c0525014480d404170900c0c1e2218041404c6660742e22200560500ca000e0300740d01c2c2000310114100c003c20031501189030015101e01a03410b2203124011401a40c0b1a40c00b07014541c0c100c02d40d100100031140703140c0f110340d41080c80c1d0300001a8852114007c00d06000013140c018020952500c081c044506641c03503a0f000310040140508451403c5ca28000c1c20880083d0180c0d105080121030500d10b243e061b4101d500070f110003011500c1340c1038154000031321a0000d00c01684962800c0c00003405554145280340d00c1000c00d44140004075441c0c0b50f1114040e0601d802582d0240700502100e45885000c00c01011300140020041140462940c8024a4404003c0520f410004140305110003d0100c035484903450740d01c4265603000d0780d40c03040030900c0e00828200c003900610440503a0407644410469140c01000250f40d030510010311103590070281d0310702100c80c811070303801a1a0b80104284101c0508012501100e191961031003486c0e03a0001600981c1041c240e40541511 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 672071196 1250 672069946 672069949
    0x10c0210230f03071110140f130308040204020c330c160b0c1c05011401020a0c03060e07050307032d03020a02010c151401081212011401140a0e 63
    0x3105051039545807076191800d4901c0201481e240805080281407213030700340144031070050502031907040c070864400800068010719960001c400c03056850b00000c100900c00700c2c6800207030791a01501c0b03c1d0192a003510503200c0b91f003407200039801480701c440e02d4000d880003662144080e06501050101d100e5003240058070703d059039100904050009041310404101444904c81c0b6098103c5819802024143c0c46036180d01d002c5649100305001c800382030758140485143e1020a511542c1a20b0b18401008068080c000059994250255025241102d012420000607025400488103c6410030549002c141d0321000300349043c907981c004030b0b21426000300c56003260b0b036443d061280d03480310f1110341502e1176040e803000382d2290095030029040051049507241480340f002c0840000303044800040102450560402007811401e0107510031a00409142050040c0124103803400d9144101c06200da40e440d104000c0820010000c00a0600001d900049401d0110202400c0c2500054a80c1d410b1021000c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 672072446 1250 672071196 672071237
    0x80c0f0c0a0c060e220f0e0a050114012706080a0b010e0c0702061801020115090603030e091018140a090516061211090a03050d090e010506030402040b010c0210 70
    0xc00007020803100038000d120f00e5071400031101c041245d0a000c1940840d00c103e4040103001440e4505c448981042d504502c014030004100c900c140c0248000c000d103a03031181110920700b02c01c2c403401c0c0005881f00c401c1d0840d040b00c50a0741c0c6007035421400c0041d5455070345c0041418042c3c940d00c203480f4841c0c0c0900420851a500c5255940700c1280800d051030700302242e0016400b03025064603448445903030314001c18164000d40c8040d000c00c00c14003801ca101540c90000e40050245404200c000a00003001c2c00068100625824040c0c0800c10011154500f8100c9181040401d14005056145c8811002920b0b030b484d800788a02a095048000c00c010405040c01d5103007110b40700030b0b42003410708001c08201c807943c80220100040388840d8085102c84d484100701040d4020080956400030702403000108000c0005840c400c1c2890640b102d1940d06d6884400040e845001d102e10368014000300001401882c00341d202c0100c1c0752050420399500001c4d500420001502401c80038003013400126008004400c55 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 672073696 1250 672072446 672072449
    0x5030f0f032a0604060219090b090415030c030605011d2e0b030c040e1014090601351311240a080106140903060601080c0f0c0a0c 57
    0x800c0c000c154141480e68910400003031000c40400381c011002e41c111502c404500c0640320208480f4942014101200203504c038140b0303180ca041e612250969054010106042104c0c4040d00d03050a10401c80140800b4112141c280601d0540000001c40040c4284440c50061401810000b69a44c1406400c040c500c414406000c00003000340b0400c44104103256500310182d041c2b002030b6505001e403950900c4401021b80240407100340210401060407801406041124401420b4001d16145c20304d07580d000290328028400803000d02c9a459801c0d0402104950b0800c4062620801600c050300084800224010f501042c04c00c400e800348032080038100071580c2000340c000503150740b20b25680d2031012803410044d0942c024a601004802d42d107100d005600031245c4481803982e910703110f07142e0003003034131000740164004030358508890345400b6001c400f5550000b001030000c2256072540ca0041d504a6002040d188540200300002d1307a18010103405044544404002000d00c0c0d841441d00d007449600d42e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 672074946 1250 672073696 672073723
    0x4090609052214030a0206090c090f0705090a050409150c0504290d02041203021009150e011e090c080f0601031e0203060f1e07020607030b01020a0b0a060503 69
    0x805050007100340e542e18820201d2860444880c1e6610001e1600c100c000c14041c4054090f80804074a03504940c0e008696130780b0805950095680b001c02120030003604200c15500000c801940400144003207000d50020300c0000030043c0380648840d6100002401d5414451040310380c2c00e90511641c0c504481400f40c01d1480c07419007082801e140c1020845058006080d910381c080c0342d0000080c00b0310004240803644e81415100e010766441c1d4840c12111220107d9090860040c4a050003c503402c00403031051040180d8000310004942d19412000000360049255402655694480c1849800c0c0400240d50740c1a042650100d103007807541c24420760004d4640c2c000044c5800401c0b080d101d16001050b10341c1581d81c1b14101140800f0301c0300c0c6282c00812800d4001b9014032956082c0000034050030710083c440d12403954050034500086820380701e5018207840c1580980e1003107020505040c0240c0094940c28010b01c1294800080d5894002c03100710203494170f40309030381e07106814421428180b110b407284495 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 672076196 1250 672074946 672074951
    0x18050601031a010f0e04050a060f0e0c1806120a0e24130812040f061d060106051b1207031404080d05070c0503060703050f07090f0306051b03040804090609 68
    0xc1140d80b0a00b160745854010341003043e032000d1808014083c003070f41d100607800030b0410801c44c074050030f25000406a42c011500180d00403540004c000700c031046400d201d0b4420010300d6080c090071946460410203120525680403501f4440410401400c1e0303082445200a1600864610743c1b00622504110030682580901c008010905000030680c04045801003070036420030b813a40c201820030041601510021411181c040300c01d000520034009954030076079000b1003003005a00310707540c2d1081c10700f00a84001c0c0842d4224400400c1001e010f600a00124585003040b5a03002000320401c6060001414140d0441328000c035a034024541c2c081d690f50f04100400820500d8142094007865071064402100d008100c3c0008929003040702c5903000c100204030140031664681016600900a410200c541c0d04604c10300c480001c0713016100c2d01c144d0084401145010f842942981c4410340500340061115a02d00740c0c945801102d44040340007540b0480c0510284c584990034124840e007501d80c00da00c01c185250 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 672077446 1250 672076196 672076211
    0x1091d0f060f010818010e0a1a0a060e060d060f020c1501090507080f061804050a03031103070f050c0304080706020a05100614010c1a011e050307080d05071b1805060103 74
    0x244c001d200241c005d04c408a4050165040140860250000c01c0c01c8140d43c1c010005060100703c0c5c6140980030800c454074000c4150303900c4c6114402116003074444c941c13604690301c010800742d061402c61240e4a41c0030314070108035000e0790882c503004c0c2d0f030001520050603801880891800e003500000e103030240c81455018842030429240041c0344060141001c800301c0700030008280183d48000f80100d03004e904041c11351181c030b003900b0301985407404040241e000c84e040407918803c081c1e1200071a0310030300340c6440352611455900303011241600504a81515444200f0007c20820010091710006240c15030003882c01e13040b81d191040c2012060040c44030b41608201d010720400c0c0d0543c0c00740e269603a003031a0000360045a420494581d030000c00503108800d11200010501c8007416a40284a01c1c50040b1007011a55035000d25607a4040d07840361420503000161051401840f1754003c0405900a01e11111a49010303115a222007075180e0200310b8007000d9501d41102d245050181d2030b407148007402c3c01c12805 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 672078696 1250 672077446 672077449
    0x180f03030304051c020a0f0303020903010e0d14092106090f0109050d052206260606030a11120f0a0f1803120e0102070c05010206060d110f01091d0f060f 67
    0x2c40b04c581404c42c0d030700101556140707264401c121000d41d450300611440000304050074040c001b94024541035000b5405c09144442c2001e0004030240d00c182d41d640c0303010710320005498003401c07074000201c8607a018a0050044504100014040304240b038100051300190400c2c0c4250303403602010000c0030841d80d0600d80e42401241010030402e10f51569402d04a541e00301650009004071020046005480000d0314003240c0f15521450044030f90b0702c44905000c00c60f8529120111400c0122207507944041c00b01f0002e44d6415050308189000b040c03100b040e50502000c1c641e082034505c001c0300e8425400c042e010801c03d00160744d01458500c100320610410440c00007400b80c480c80d400b900b0002c0c080c040c2c07001591020204030390222a07500320080c000c648880745880c01d00540f4089204090041c8114000300d1250b2528400000b00d507a03010454442448550782442800240d180c805418000c032603c2c00664020070080075405016103005003442898800380f00400c054006d00500d02500c1c08002d0300426 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 672079946 1250 672078696 672078703
    0xf0c0c0c0b1c020324060705071202031e031e0c0a0b150415030212010c0903110f10110d080603030708090d05030a21020315040f060902180f0303030405 67
    0x1a0384600094039074646900c0540007440d41d44802c0002c0e9244000200301c4070a0540d040074001c1410141c105041041041c03c021050055100c081c000d0341095a003000951600d000012100b8030282c00d40303002c404506e010f04100d440071800b90440da000010f418180aa40315100700f0018029802d00741004805e1610a9a5031780d99680140701003001c0700403454004040d181e42008c0800140140a041c540300d2440c0b49410461108a00800e01204118040070040c0100081440e07960340301d00c010703482c54560f841134440c0f00b00c003603400410110091055885928145400a1003510b90808035120008114904200c061040007008800400d100ca00e0786c1c080121001c01c2d801c800916200c4100b100081d00418900c1c0c4d00401c01d210015000c40596001a080c4d141c00b0044200001440c00e840149010380c0b00c101d440100309800e00014121620b001da005942040b690400024900c1e01c80e500c0740101c0e4807002500c040c64044a5041c841840c0004c1c010b401e44000307a02450840c00c2942c1c407140d0303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 672081196 1250 672079946 672079949
    0x19061e02010903050901120b0303031305010b0f0904150e010f05061206060a0506072405070219020904060c030b030d05091c02060906160807120305010503210318010e010f0c0c0c 78
    0x10011541c5c0c0100503081c07d50400d482c1490000c007680e50303900380b07040c0c04080a01d204600729207035400c000c2c440c3e4540c60f003294034031001d1201800d1a145540e45540e284039011a10203d0303005140e8a0f040c4c40b004503000d1081111504405000203642e061140400c41e94100c1521a01406e0380310300d04203d00e64a4078140201214070070b403a0280c481c0c0c807900d071010920700317010b1244960300503030581045202215080741e40141d16a4080d82c1e0f007480846d04100c5110021030003c0d40004584000c80c002803502c0d4010b1303131100f0491400242b024000000242050f060f400c4a5000440100d081206841d2102e40701110400941d5100b9800c1ea00782e0200303000f0700581020741d21600e00494034010758985c2000480506602a003866550451480c142c0c0d0300d01c110b4138101d07000902c1c2a00200315401c000444940210813000311a9a9941c0b401581c606130784020400c884c0400c03c0d203004400300f902400341c15001016540045241c44040035000211020b82281000f0002c809484c00045a5090325640 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 672082446 1250 672081196 672081199
    0x20a031d0f121305120105060405130c18020c010e0f01050a150b0904090203030a12060b0313061a0a080114060402130603020304020a0f0305030a02010509120a0e19061e020109030509 80
    0x40d00c03016450340a0300709000d03644c803254014110f545541503d10040d030150b4130821086030100141c5c0c80d13a540710040c40361003d20080040c05191800d0028014111070b10054402d4944003600d00f000d514000b070300b55801e6284021003507000f041c400148410a0056592200a40d002045240d400d61312a0406604d14402d5208080c00003900300c01e00d4540b82c0241c03149503006000c50341e50b480340001c000c0440080c0050310486c6840c100000c01d503114010104c03030007548180ca4034031132481c0d1603d4a00041c50014500007072500544c02400881c0c40f0500c10390f00410164000199100030180d143c8002e04000308001c0c401d910401c480b0100c20302440360303502514041d180050b1207a45500c08a080000503421240c80400e00010000c10450004010074500c0c0c5107600a02061722000d201c640d0311095000808940c64092060040c9140b003044c080a28a0b0001c28030b5141d000225003042c40b03104103030009400581042c0f081c006803020f4021503209220684001c0001c0301250301c0c0104107008913070740389 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 672083696 1250 672082446 672082483
    0x80f07020a1401020408031c0b061305040e070806090d09050f01091203030b150702031b130e0106090203040c1d01050306150102160f080d050c0a0204050712020a031d0f 74
    0x1e0a0b0b07079425030543c0e02601039982200d0350303843c803a1b0b010345004150501001c44541001c500d4010360170040140c49582881c16a0b2505240c00e000400c4040c01d006407080c40c4511540500091203401044158022404817001d040070001400c801407403014180c010501400e070b5447c05841c035981c03000d441c030115550000349418145113850101d02038243c100c0b0103688000c400c1040105c00b400031000300500c40c0700302d00b100c10304003807440c1440d1040e16900312980c0c0001d2070403000030b02041a030011005200c844000152242e2502c42c1d0608907001500d054424401d5158140003e0300c5940c0c4502c4031a01c403009021840d80343c040081d82d91308004141c02c41000c101656040d40d64020000e04078215401c20324415000c0d19640c1d9461607a8040c421101c21b4800c0c40d041d46041401001120140c0c1c030179901030301c8228440d03000c1c40060034010708000100100d86108519a0003540302a00418405a4000ca501c140800500e0070703016001241210f02d400c210681d10406000051040c0259601d0101c0e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 672084946 1250 672083696 672083723
    0xb04050f09250f0f1805060f090316050307171b0d0203030d150f030f1e08071104051b0316090909080d0e0a02010909050a0219020d080f07020a 63
    0x10070038040300305002e205100d10750101da00032290050400207049000342c1e2018401c0c0c143c0242143c803050ba00c2c0c0f1031540115080c1090209041500080416141d2042101d10380342c601008245051000000c15034210800384c01404035107410700c1504028010036601e0501d13400e082c00141e4a400c1c414495000d906580c14101d89203403100c1001030981c4d5001400d03203482e4990350101c0409085003021308050051080c10101c2e1201d0341e00300f13038000da0760020440b09290701e550f5215250040940a080070000c400c207000000203070004000c14030702c0c4c443c4482c4028400310328207000c25210302a128803060342110600c403290038200ca080e6640907035006055900c81110305e0086c3d822040c960440d0000c81d003043c1c04041404001401050b1009400f40100f244102442405840b0860801c0c02800104440c208100c1c0711010340110790400103c00d001880d0100500558802c03083c2e00d0000000f507000358050140b5190000030a6500c09412401d605503450302c00c0c4c1c025240c000c0c0282c01401004240340 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 672086196 1250 672084946 672084961
    0x303011e090c050901030b190e0c0c03040b070b0c0909040b041410060509150a0b0c030c011e20040b0f0c07080604050d0f1d0d0b0a020a090b04050f09 66
    0x202401044070490400c00441c00000c0204140c0c0480d4030280402c0c1450b09008032401e10041810000214015101d46541003043e010003000340900902442401442650a030000900040c4020680750f00c5040d9100514079000c1051000203203040d08000d0103201e0341e9150f07110010001c0e80594491501d80e22961145000410500ba5a1007043d80c1d100c1d80d80c0f140820b60191f4004000d48a003190380e400301d661004541c0301c031080c22881080d000601d0708810451005040090300f001d50f01d4100742c906100ea400569030840b41840000500c1041c501c06c0841410510f20405900060034211301900140b14100240144102c0c4118881c100001410b81041000001519240e88400c4203403089150f80c0c2100c2962814155004c6e25a8080c03248038070501030003100742080c4603041c4e07201c01d5a014000d030340020315200c843c0f4000e608440005108000034801440391407007580c1648005886413810000100384104ea40c111f0518170034100310900180d520805c040c020341900306c460482035500c152 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 672087446 1250 672086196 672086249
    0x12120712150b0c010e010b06390706170601020a020112111606050609070c0f0c0302060d0c030609020c06010513061203050903010506010f0c11190e06040f0e030301 72
    0x1e4045000400c0c0340081101040302c0000e0030308040d110b000f403100c8905006800d080f58140000c0c2c550003081000701e480194030403140c1094911401c8885034050301c580700c409164182050859200d504008028013901c3d4000303442100401540390b41e15800e150560010355510300001002e414040180754416141c00c0d590044400322a03100070450300c07070880c01e400d4400203041500031102c160400300094403138141402e40b03e1207038219a840d1540c0400a07218200503090342d040c29500e000745640b0120158541070000e0004a1a0486c00100207100000060807240716800600310a03004000e20500f02900003902c50540d102140c0e464808500c4e2200200141000d40c801298481280781031028160001d02030078030410140e0081c003090703850705e004442d605e5807450108049201c1c800740001085441c2c2c2032040004000e00756540492181d10074401468160b0311800c3c001d20b2507410802503007407900481e051250325030307000d01c180c45000d040079480e800140580900000c0d0762000248801006 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 672088696 1250 672087446 672087461
    0x18010e04022808161e03080a02070b0f09102f0c04060602071e030b0408030402030c03010527071422090b0402040e0a020112020901030b180912120712 66
    0xd0030304029441c3c0d50508541c41300540c0d48500c158540116001840b803110360120740c0d08040d1040400074060441e03486c81600d4000c1078200d01144640320020411041007001042c2100612410540303902c0d494040051a1011181074420842e00b20902841c80704030580741040b541514007603070000901d01c88c00520340745080d000d0680c4281042000542c460b008981c0509545281240d00021501046501800754407031000a0403a0758840c00078000c10440c4c0083c1d508180300600b03480d446181c00d4006404d4410540c0c010a042c0e101e0302c42a013091400a202c1082580b901d40600101464540307203014019005440318010115a03445000340240c0311342d0100b180d944035004000030190f0381414424000100c0c0c0490041c0d01d00b00c2c03001144000010351000e6560305940c1c1900c002c2c40d030b23000d00c0003a4010040d0039040c141c507030143c1e001e40d40d035810b050030040d01000c0c3d07844a00d00d010003001c0d142031000055811151420400300205a00450a10b40c0c0641e143c20180388051400000000610f2007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 672089946 1250 672088696 672088759
    0x50d0b06040e01170a030c1101030f09121b021f050c100510060519050901120e01051e100b07080c1c030b0604060806040506060c07090b18010e0402 65
    0x40100b4140c1c442c820351030603284500c80800c06041c109961690303e605140d0f015003c00c00e07001c031800c002002001c1c2c514500c48103250214025200081d1902554290307a02203c49a00303004000740c016501070545820211540001d101c1c80201c0e07000b10b6181e0b104016400481c07680c3d03074030000095014408603035021042c081280c07095105648894010501520079948868101038000ba10034400c04c15200c0c0701051000b840321010900c00e054645521107100507050007044007401240102a1044010014142001240070301d00031010500040c00d00d010044020584014000605c0712500044240c826010b10f003552520a03090240c007501038001c0556540c032411307103072462104040c00810302e401702c581c0b824002100480100070b95030240f401080000780041d00010350310710b0f082d0480c41d044540075050f00d10b00b9001d102d50506022039a0080e01c034940c0c0701c5c0540410303424822030710389028400790002041ca504040020b62a4000580003a00c2600d0340c030344604901401c040d044124044 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 672091196 1250 672089946 672089959
    0xe0a0b0708030a11030403030b0a1203021f060b0c0703021c1e0f061a0a0902030702120714120307080f061807090504051501122c030d0203010b0d0507140307050d0b 72
    0xc06c1d180060207009510ba0082c0618102040015a12000b0380425403090703050300070700020803041100b0100c000c4010b03d03107a1510744445001521440c000c00900c1440074038000303072480354114010310095100820300c544a01d41448060300c082841b10740c09c000e01001c100e03000005080b00b814041441c90700d58001074071a526088041000070054a1060f001c810142e440c1c8080d03d641d440b07004100c0c041151040d0243e002100607503403c006080040400520400304c0403825080a00c2c070910749801c4010790041040000140000a03410903000e6510103640c101c08213003485c0840116040c00d1500c040709800d058000041030302640508900030180102410420181c0750901003a001580407808403804605020390f80701d207200c0c40d4014407080e2000d203050503190301e13482000c580000811103410000f9000c2401030780503003201c6000960003800c1002c2c0f0951103000c0d0000b400e040b100040d04241c18440c00202642088080d00700352544042a41000ca880d0040b011401004e00710007040b0907403200 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 672092446 1250 672091196 672091201
    0xc0411090301050601030c120b0d080d0203070210090c060e0d06050c03011e03050a021005070516031a06010903030e03030c030403050f0105130302030910030b0d03030c0e0a0b0708030a1103 83
    0x200001510050404500070f01c282e480f04801941103c0b0200440c0d40080d09001c0c28035200b1080da040000e601d44060840354001109458541441d04030319035503c00745030004144030b0350350b0b070410945000307041e541020000c03104c50381d4070070304150014803d0f0b0091010b004841d5000c2d42d00c0c481c084411030303002102032102d85410701c440003659009003d201c00f00c03500c042a083d45600010720078001e4944c13190041c4000204c580800100b100d40504c41000c01004004940020b5002d100ca0310b0341540d00703525403000c2d90840ca0030020301d00d08914042805a64801044900da030303c1000c440071290142844182650040c1c0030904512810641d40315500c00040d0000400c800000c8a20074200000c0c020482511417806420300c9030709500002d401680309001c0d4400342c0c501080142e0248080b41000510340e14102e0110340c100d295034400344e000c42d43d01c0c0554800c0c0e0750007080034016130004a0344440050f0030a0401c8500c0d005084000d800c404010002820554103503001005180d54070050688030f1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 672093696 1250 672092446 672092471
    0x101404021c0c081807090203130203070e0f0a14160201110a0c02120a1203150510120510150c050c0d0b04170301030b13061b020307111203070f03020c04 67
    0x812804140c440000c4554000500d48004d4184900311280f0140203000744602d80401c8501a400180407405401c1329010000c005079030800c2114000d0190391a10007252802d4002000c502000511810800b0300b44210740145040f07490340710341e008942070a00740e40d07404151822401030014103100c2560000000d180b0100542180c010520b06108071800342e1410030744c0a00640760b40c0d403401c00402061242d0315040030320703003e03410080c4984e583c0c480380942542da800002b400c582c0d4020390307440410786a51840c011401c49005283c1d100240c03901c40142145481090840326098034520340402103001c4001041101c14001401190710090041c010100c16040000202005440c21508210392170001220000f0b14400d0364103c07504000b80051030399403c0c1e5401640a01d40e03200b150a141d0b0341c0d0302c085400701c480b00c4d400c103241001c0c0d0007035449200d02c1c64076005400103030506900c54085900c0c0500c07182000021100900d910215107055000e603868240d142c0040700458a90160801d486001d25 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 672094946 1250 672093696 672093701
    0xe180102210903071e030e0406060e010e03070509060d1b141206070c06050603031b0c040e0106030209070f05120109090b070f0801050f06070b040f0203060f101404021c 74
    0x240301d1802109801c0b40c5541090654900c16410000c20058a080e4001c00307a2600d9512044a01e01038203144c0d00030214280050111216600440041500e003143c01e4429648180c54422080003a4001c003441e40c18040060881c48008210510620780d501034003040044010070b070803a4040e581d80c1c04038615120008d0000c1040d0f40040e003405802e081d5000c5106c8030300050003d004d1030882d254114000b04e961100c40240c6402441e86030181300400030000c0c2c080620840c20052403c0070301402084820600b00000d45404608183c4940e042c9078051015a8035070308041d4110701c944c105240848405141544c040c00344059401d154160203000040408968101c22802d43c8516080481940d56000641d202e01c4419502070020306100c0051002d404c000018610043c4014221810040d03142d441c4201c1d9081281c0840d030030080a0281811401c0410400d0742208080341107120910700401900e840349c2c3c16100d4900220310100d00b10b00c2c0d5031542d03412941c100c000303002d94082a200381840c1402 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 672096196 1250 672094946 672094987
    0xa050a020708131526070c0b09060f0603010c140310050a0608010801050a1a0111030c0307061d0606100c020a050a0909170c0a030305040501060914070215040c0e180102 74
    0x4e01c480320341803001c0e070620070003a2a2143d00a000030780c0d41425034006400e26090010031000501510903004004140310398881480b03400441c0003000e1520345241c0c10b255a0788084d0070240241e044c0000c1c10081070300034940744031091580c070038151240d6402c84003100f04c51080e8000c50700f12140010100d410341c4d01c071035118180d841d08002400307143c4915122004031883d1210344070401e42210a80c100947c03080c6401c114281c6082c003141e0902d107031043d5036070840d071000d58211441581d0b1903c0c54440303900c0329440f4840a00c10405042e00345060380c0400d141c00e0007400c1d1802085110f42034482155200908180540702c0a050084042e03101c2c0c001400501c403c000c16180041410281c0710300380c2c0c1000484017840544005000100c50300da4040e0043d000142c402c5a00307548900c0d002c10400510f21400c2c0102e40c08000d030b850309080800c0007074140040c000100004100040030400411601409e0404070b0341d411300c00460a5650800000c21000550a018419400090102401c00c0030644180 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 672097446 1250 672096196 672096209
    0x4030c030809071a0d1407020c190b040303200712031706030705120c04020a05120705180d031106040c0906050105070c0308031815010f0e06090a050a02070813 70
    0x407081c0c4403000000d94481d42481001c4c1004040303803018801d0311034032001c1d00c4400c8100102007000c040c40f98020074a000119500303c010b0b0310008445000b07240148151141d151169600a419400c3c141468080c5c031980c0030140070b025204007594281c8440ca1034000392480500241c4036416112051084490344008003136000070000e050341d0100040b00010103015a100400030b0080c02e2914080c40706050300c40300020100c0c00b410300100003d80361400107103491010340d5203081d83e405941c1c42080003204064003101c00c00c281400400d4020050501104140800b1038269180700345c2403800319400a96416460441c0c041d800600080000402c482000d4802c0300c0c00c24005140c540c0e0044405000d030386c101070900c0280113810000704081c540115040050408401900740e9103560091600f10488444411031404500402600000c0d00007900503000001080c100390034164002011200043c01c18a42c859070b0302d000c21001e1242c0d030f040701c1c030303a590040100380c45a0350781c4000f02d01450302e4480c04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 672098696 1250 672097446 672097457
    0x4030602071a090c10120609051503120c0307060213120b100b07030e040e0f12030f0c091f1b0506060907030509030301140303210916050f040911040504030c03 70
    0x11440107000c554903c0981c0d01500c5000800790185d42180d80e0200408105c14580d607507000440d030041e59000f628880e0110300c260705880c581200500d03240c040309042a80c2c01c140d0a00950000700170100803169500c1d004400907072102041d00113400d906802e0340c806403004020030851010401a18180c13031207206040005000b241c0d48045410241c400c51070000c000a10000307121070309241940c071401030f01d031400040b214143c00011542e45058014061000201c0c400300c2004031b5854642070b00c5612404d004021810103d0b540003055407440103c0001c1c401d5500103034a109c1140c801c401010486648030310648003490181403080e114030090b18810300514021000680517400b034018103018407440c0005600d03581c6002580014038100840045c0e15000402c41c0c0186410303140000c0324481010f400040d400c0c1410b0303085614111508161030420544140704201503031310850301e00c604040940d000305880342e8905c1c2001354188000000c0d54854603100502c4141030f80320544540301442078a40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 672099946 1250 672098696 672098701
    0x40f05070809010f18060f09121106090706080f090c03060133080414030d0504030801080c011107140406080f0c0102070e0103080304020d0303140726040c05060a0504030602071a 78
    0x100816600c1c3d00c00c201440d070b01c00c50100000201d0340d074040840008020320008e60b1080301da458064008080b0111000154110312061a40c0828001c6036000b42804008106243c941840500071400081a03641503c401c8000509045424440400040001002e440e803540e151100d0881042c10340120824580c0e003005001c08504401c00985080b00b0b45444503400355803683c0d100c4a5800000c0a4804140001e002050f4400040d01075640200e11035255a2200e42c106802c45207420004c0b250981009022002808102804502070b001d40f000c0025020224440300041005400a83e10500103440b03035030f00e1a4040a000314a4444501d0260709440700f40d03a03128103d03105514207000180820f601040490010300e01030007034000756407180c24013062140820310110321030344007121900003141c0c01c0901c61484440c65080440240c040e210b0b08000b50400c3e4840c0ca20307030003080c02028058500010203488040c0190140c4008550107031040d944c9410501d0440d00c5000100002008181c02c02e01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 672101196 1250 672099946 672099971
    0x106110105060901030204111623011406091e01230a06050a0c110d050a060501090e0601120f17090306130201020c0108040206160f0506130c060c02040f0507080901 72
    0x41c1400b411004207002000d0b4216002c2000802c406803504a40d403a00b04000d29010300381c02c1c0c00c5c0314124020494441503e01490082403005003118011180f641740603510350000420390080c035003110068800800036511401c003141400030801e40190410b03075403000082d83c6d10800b9075840c55181e030844025081c0c3c800c10140800c40c40680500c5022402c10b00103c600c03144074100b0088200d0107000c0350420b6092000c003281c008411010107684c583c2060345d0342e006103c1d00c1d000d40350040c822914100154121002d9107a02c414040c040c4801c5080d5084a130001c0c010b840c0c0c0da40710042d4000f20300270350300e110729108005150710480c8114001e01820700090356004000380e000d50101c1e0181c001d80f0390381484000440b010440107008a03403000d014801079a4912400c180300507694801c40c007401402a8a061051820300c0040841c1310380c4040c0901000041c02c85c040c81004c880c0c0300d040c100c40d020f10601c0000c1c00380000c042c64a00251806041210310b5038401c4402d80107010420003040012007000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 672102446 1250 672101196 672101201
    0xe190e160e100c08090a0b1323120c180a0c0e01050f090a1701090201170103021008040602091c110406060e0d020604090e030310271a100801061101 65
    0x10164084101410440c07428083c1d0210720b0701602c035180143c60300308038200203207042240b5000403c01000215203a20945c040350340d0240a030061100781c10281c01e5000340b0040e00307540c0c484c00c0390043c2500040c0550030301307003000485400e010083c400c901500c1410045d803080081150902511410701682c464941d020b101c49048803941a580c4500d04007229020b0300203584042004c0d500306094400015060500191800702c1800400000c01c5640e0301d0300005021940340130100d0100c042d410010001692400341a00007805079003815961070b525801c00b800207000e140d41700380d0061100c5481c1c0d141d0099651416030b0307261042054400e05140801403000301c90035405040c02042c10601458001c0c03501200c40d8619510040c0365a1802d41c448912a056034401447d590b502e40c0003000740080c0c3d0184950240160034094640d8081045c12840180c0204010f00580020781d5165040490035000c0c0c2800042c1c0c1d0400b40c80b489801404800040142c00300b446240c00044c10441803409a40c010b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 672103696 1250 672102446 672102467
    0x1050106081e161b020a030c080c030c0a030f0503070c08012003160318050a0b01051c0b13082808071106160504081501081902010f0e190e16 62
    0x2a04003e01d8244000054482814281190405280350b02d4800c0c010303580c00025001651003640c0c080c0409140080440c9001c1c204030465100740c000d070300b1084254481114035811a600032070380e5100100c00b410058110b105600b8083c00844170410040760380401500142c0701c03042e907040e103402c4a0031880b40d00d205600060b85d9a820580c25904a58a4140300703410010b5a00d0440c5180b003480c141d01e90340c0351314004901d417003210f00045003c0100002d14001c500f0404070480011010712000e00c6544440325010005d001300f032200c0e0505940405e00821100740c030f003000c1ca06c454101d13100b02c2581c50055040c0742845c031800000c1440340024808c91040c2c2006203102c0300107009204580701d600510742c84076081c031880010800706200008540004100c0085400351840e04403601d035041c000b50f28104401c8030817001c804c0c01110318242c0140d074081c0404c54120207528103000b40340c855500142031401148150860500489804034905003a40e41d40d500070100e000c0c0340400790304901016250b030f0600 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 672104946 1250 672103696 672103711
    0x4031a06061602301c0206040b01060f020c100201020d06170c150702041b4a100306050a08010504081606090506040f0b0f06030c1203040801050106081e 67
    0xd1541c1000141001004000710754041da050944c0090b200d0111344072526035443c1244550711042040c00200b0340c1404680045d0141d20140c40b40b071a1603210070390610b070188140010003440f4100080744510a01c10f81c90040401030050a1003681d03110024042d40016181450903403500100140c0641c1054084420f490300c00050f0000086031000c00c4030b1401400c030056442d01c0308020280041e0344a1040c41c0301d1a09914406084015848005001c0e6043d052001903021903500c041525102c1c4a405040c0314410341250510a2901c604c40e00407075070f40100990300515400441200560945c100ca400c1d1b032000e80c0d107002c00c0c075550000d03a4240c62054402401c10f41007040241c10741a4240c804249030780c000d1202065000480d507806d4a060000c540950342c2c400c540c030107034003000f09280701c09030048400c040e84c103018146440000e854080700e288141c880c026001c0d0a080151051050350000e0140390001c01007903039030700005030200c4012192060f200082007103001e9110b02940c03005008180 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 672106196 1250 672104946 672104977
    0x20c04091106091c0b0f0106050f090f060d05041136060a030b011401030c18050f01111207020420040618050303180306090111030609041704031a0606 66
    0x2045001c0c04499840584119009100e0182410180c09a405002d401324443e08041209242407201040c800d903041c1c000f0b0081080400030190540c038550184e402846046070f614061040100010340c15100761b240f808400350808040006104e2880e18000ca020400e41d000400e00401070841c0035234240c0b500d54041d1160001d0b64000c002145100d41c44c2e44500c0103132500b440940c03a52100781c5c511109034041181e0340600d01002c00c103940d05002e0700d8011001402d1101200c0312511012240051602481d4026409503c4601c0b040c2c1c072070710400b0001c1214030142c40c41d141419225880940c01410143c0c042c5040145806003c0f100344040c9801903410800e45041904200f02200d0624103174451265103003254902140341d075010710080c80110013107629000b006000000745424440000c1025000c1d9251403042003e200b8810110780c0d0040d0300700e1300b8201994691400d01c642c2c0c0d9071b581c1c46840c18900030802208010180c0008100c5003400f80101c240c5980c1c000c1007000c81d100e04024010301c1c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 672107446 1250 672106196 672106223
    0xc091c0c080d0504140a0b0f0a090b120f0402010201180f170406050301060302090a17030721021b24041d010609170106031704030209130f260712020c0409 68
    0x100e40380580303400c130500510350351806daa6810f000d88240c00c0400f81c1e80c401000000c0300100b454110240900904c1c0d00c405807410041501c0e111071003100c00911156401c0f00328000038046a201394098004201c60607501c5580d00010308289040300c07031821003214800306083d42c0e88170310301d04da0058800300e80f503d0780e031945560300303140084019411000707403940c10401c007820121302c04030107039503884d011643d040c021600d881450030280401d0b586a00341c3c0c01e003540c696440d00000381d40810007510807550402c00d5100c5550300382c041501c42c940701c00c1d0300400000304881359502034035a1006004441c00380d120010030301c907407103c1c0c516148400c1c0314660115407002010012401003030054244003540800029a4960381e848442a1403a038154240b43d080d0005014400c51821a51050300170f404c0e040011000155a9114180124030086c0a440d01e8000750304c25660711103040340700d4040c1d10103034015a01e40c0030340c0c503003e0328501d010f4047c100903015407070301c031805820716220f4400e03101d4120720b00b88180c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 672108696 1250 672107446 672107459
    0xb010803181002072705062e050c060702071e26011b030f060605041202010e120f0307020f100c120306080604050f06090307030504030206030c091c0c080d0504 70
    0x96a030b241070a0030340c021203074002100103410080b031103d5109928284600506a05041d085a1005160310700c940341001c0107480200361000060715102c0c6030070f10610750400802080e9902c0c080d04c400d803103841c0308100421000f607034003103171034400c455a203451050410b5150302c11240c62450307401907404000090b00c80050102c6602d6900c00807a0700711000190030403280f11203003400310494a541000c84d445a941003c61050752103540e005001034581079040c40e042860781240700d80010310103410441c1d90361446809070b445800b840f25031000042141d503100b40303411410303450307410074001a442152a40c107804041d061002c02d0038025005a50f60700069001c95480120100c40c128a02d02016036481020074906001c015190040c2d015000801c408a100101541740083c000c001c0c0b0382c650018801c0a001a8211040d64166581101d5881c0c599440198041c0f460081c0702e13040303500a14444a8560344940c0400f805280c5025171100303c41141c036955000e9031070021196000000e00304010030400e2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 672109946 1250 672108696 672108709
    0xc2b0308180d080f07032c0118050c040b040e03030601080405010204120b1006030c1b02041e050609060609010e06090f061c06080606060a030f14010f030b01080318 72
    0x8900041808003560800d1414980341000a94811010881c64411301070300c0c6108020a91340082c0501e0103100b1034041800301089420400817201c02500000d204118107002074111605840819414020300c00b040d00f01303141d503940e016032240d0003145490b40d201220b04140c05811803100043c0c000318075607201c000c011203400c9402041aa01c5560a0001041011140c08024006406000c6c0d0b4032281c00c0c2100f00352051121580300405040c9030043d24601c0b01e8101040b640101584603602c5c0a4a52500124016010808010414002d4500c0c0040641403550055020720b1090b24101d031255a0003090100610520684c580400c19800940b6a14501034000f007036403040140105408901c26008203c0c95000018030101d1100840011040c980d5140310b01c80c02070001500030b00d15402c20b074020030f5803480b80070a00c00030035031101ca14409054080d0044042503442c0042000b4660b074440682403940d81600003110000c14036400020700300c0000040d103c3c09840741019407031030340014003040310 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 672111196 1250 672109946 672109951
    0x120105010813060524040603020a03120315230108012709050703080901080901063507060e100206010e0126010510030b06030307050a15060f080c2b0308 67
    0x242d811294404070001080c50181d01c0c0074501442d580e100d002010200c81a100e5600a190341c02607191000401c09a44e415040c001201d4001850102004100b44103c002c0e0140d246031080e030300301c220000540c1c00f04101072104c044c118800348080c986a40070045440304801e04c80c1c0700c0400072140b09002406020014070004140d02180003404542990310142002096070060320062804118000c055030000d0710746501080701002000100d0400744140d040c0002c03081c5000d0303070b081c0702004250b40c034452030b9841416041c01021100030941e2841c00801c0600c05403070950054522840c5001864000a07000d03059420580c044010b0b6821b00c0528a14811400b4511011101000760260041005e00c94076014800300301c0261240c44c11810184100c14001e0947d5009910401c0004041038000c80e44412141d4007910b1821410350292000c00900b00d282c00c13658003c128603200040d51080001e8402d0706031000d441e00b00701c40c40c042c206440c50321030804c9884d4960303002c082008002441180c1e00ea9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 672112446 1250 672111196 672111211
    0x1b0309062202120a0309050a210f0209130204110a0516020118090f050f0903180a08030d051905060d12030212040501020d0608190609020604120c0f05061201050108 72
    0xda0038942c0c0010364802c42d058180040c03500041c0040741810f0744490a0070103480d0a888211100d03140c02006e40080d801180081400440713003403500100058030640b48021038008141d10103d0501000c500a00320281008030f200da031403c4200d65162224401365010a0501d4494505082445128111070a07180800b24108200752044502c1c160052414002401a41c0d00000351307962840182000c4485c09020714000c1544482040280c4a0000c2101c4512000d01018a076025074840424445901500310720504d01001c5001510700070b00e5840144143e43e038000301004030300a40c1240003141e00c01d64a143d080422030182c0408607082c10300e07131686c030026494010310344407410080c82c0c80400151000c440e582d400107000648405d01e4015080036201380c03000741c540b072214083c5036485066401001898542c58154010035513403058242c500400071421010592031441c036141038000014042c0010400d10100c0128540c01d09030103981c19214a544440c03041d900300801543c03141002421035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 672113696 1250 672112446 672112501
    0x503060621010303140909070509041401080a030206250f0e0a030c05031b22091202010209010f0c030c030e040902041a0f040515060a1106010e1b030906 67
    0x103081141000781007000c1041462034440c020750462900034449031001d8615003607018248202d4407140c0c0c40e2048a40c01201d103051080d5030700341c88000300f40940241c883d83e0321101d40907000004c1c140d80200700c0300849842682901c02070780d00d001100b0000042c64903820fa821071a000c100300c40601031034048101c0d0b440c504003081c13401c0d001000664401d071b00f42c000b00c401c0340410a081240c0e05042028103c809682400101c1207015580862004601041d52403900035250340701090107070480c1d00415016400c119652060405400041c0c080d40c4180805800909804401c1120310710402130740d0702155044d07903072860314085d41e1406c4468000c2d0600c0994482e541d0f13284540143c4e80c80c030800755000101540180280201c20400c8046401e80b00309600503070a200030030030040042c02c1d2040084101303c1e60300761198485c060032201007000a165a2291041d1400840c030a410b192403284030740c044501603290ba840c2c112030742041d8003080d20b0480d0181d00c03840124103031081c1418000c8080c41d504a08 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 672114946 1250 672113696 672113707
    0x9050117090616110f0a0b0f090a020609010c05071e0b0313060f141306050c0406020717030708030c04050a09020703080403031a0402040609050a090e070608040201170106020309030f0105130305030606 88
    0x3800c3c140140c0303201103000d071ba01c5510400704115450b08140d600c44a415030301101032a001014540b1510b0f40da600a2060000203840080307680240941f00c8240c0e00300c01124001920740c0056066072032450800b139149406004000f51800115088900c50300b100c00d526031883d241e41e40c4020280921b000c0c0c041881da00c4000c8010b0030142a0b50301442585032140103000c00c203131800d0041c1251000303000f6086c4050100418803c00d9000240f04045821400d180d030b81464030300c0380060640c09030710300041407244000180034613040030401078001e81e4803c4550b49550b0b0750307806000040f80b1456a004010881c2c460000380401d000354401d50f98888800224030309442c03000300040032030780070381c01603400b10b00c0c0c8403004d000c14182a0102c00c003820170b05d48100500aa04484d903980c60b00380e4440e820030017582d03800141c02c591054081d00c2d8000e045251070041c070b58440034081c1d105c0c0c0000501900038451541050358561050050900410601c0340801d0303108001e40f4101c4081d40700905542e0054410801c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 672116196 1250 672114946 672114977
    0x14010212070f150902010e12070501080c040e0403051b03090d02090a060503030c07061b0c031b0b04090203040615050906010309020303070506040b100608010b0910020a1209050117090616 82
    0x300f143c2543c0d07000c00241c51056100142150014401a5015201c40c4441550302d4200044d1101914070900f041440f55440d040a0380f40c034891a0414580d04c02050180010150000068809040231420691070500e4022400740d03a800707410130300c0703912080c0d0101460150520341c41e000e0704000d0b40230740400c2d120388603030200f0300e15440604c101400f9408400c0400c00c142c1d100c20021001c2102c441000b64415245d102e240d041c0060340005071003003102c0c507200a582204208040010498071441903200c5507107216010007904212000d50320f41d030800120f410041921800c002c182c0d07800506043c0306403181e03001100200300c807240c03c90705480200100c1000c80d2003045618410380c0f0600f6200d030356190a5010f14010031041d8400380c140100440144142000c0130166400c44200351913841c00508180130891a0428001c8041e02d4088a00e442c10f151550040c0c41800341c0720280c9415403845800c400d1250095021585c00026420035400300790320010b2008224954069450000c204016401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 672117446 1250 672116196 672116213
    0xa032a1a0a050702192304090b04020621010e01150201230a1503050c010f0c150c0509090703050a060b0708030112060b0a08100507080f07080403110d081014010212070f 74
    0x2c006c98101c204006400c007540b60001c1000311421420355062021101c40d55a150b003050703002e03000038411032340811440d8007484240c4001800109500c001c1805595500c2c540022600070301400f1003024001c050a00045d00500032070039400c00341d122041e100f009400c5410340d0351001034903086e002a00c5030120406015444200001b03140950041d04003412082c0000d0400407942201d07105101003031340c410011440710215100010380001c4081440c5c1c0c55180d04603142e100d0801703d19804803a039410300144540c1341d48441d20640f80341000700040303a01c80d000180240950800109081d20410052000402c250312030040680710320000304242010f400001e400100f140c01002d4541d2283c840c03c98843c01d24015607402103028101404181803021390b50f502da42c4010241428001e880000c07508241c0b2420002c44610407040595640382031028004000020580d41d412810740d10040210304648c80c07c00b2100c802c0c0050700100011860850380c021f031500a01c0c02500c074490301c00c2401000c640200d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 672118696 1250 672117446 672117449
    0x30b0a060e0301050601030b09130201030908180405010e1006140c0d080f0f010f15111e070b210711030f03061306050604050d020a032a1a0a05070219 66
    0x6407205440c071000402418211400288614105401e1054615058851842440c1c00c401e95501c580f55041e002c1c00103030064140e23414000c04050b4000f43c400d10ba100310702ca0f002c4540404407414445a60303a81e21090240740140c510403000701140d0800c208850050103400c980180075204242801055003515040103200a45c5d5008185218100040020801c05076a0300c004c04401c586507e505182080000b80c880e4010790250071482c62108451901982d106170980d05014201c0302071074900e80c0480c050f0480c00107500d849100307450006c030f50044000d0a48001e50000404000c0b880c43e07204031608a00b8000e01028180a03a900d240000703814180020310315003c54484207907a130700b800024800f90402d4501340141e258902041400540e07101c20840c2c0896130216503d00840483d800082d03110112948000d103a40b14204142401118180100ca0b42c221002c203143e00035070b50f4039440000c4005101c0d0000903201c1c00c000b4402514014005000c1e464009011008448210320701450f040340306 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 672119946 1250 672118696 672118709
    0x161b03031d01090804030605130f06200c0c0d1505040b0f06010c11060a0516060c0e010219260c0f010b0d152f030402090a05090c0d03030b0a 62
    0xc80e8040800016a018080c0280704400000c100c0c200307503512400d52601403804002d0410f0b444d04003161004040c0d0a000751402c3d00725180750403000251501703100411402005152905545842c0b20507448041d007034031442c2e038100380a0a0f80d580380d481044140720304068201c2d42011688560010102c15105d072605c80c9124011800071350410041c00c2c101b40304020110350400103070100300e03c000780b24076019036040e03d01130707805685940f41480300340c80c240111085904550254440b54050200c1d5400040400c42140c544004984049004a84449100f00e031110100340b481194000030309074050440103650f84880d01c21044454640d03004150388050039403d1075500001080030020307003c0c81920408003041302e4046000ca031a560328691881c1c001050040540d683e404031828290202c4032201042c00b2030728169072031000c9450041a5002914240d004039821000181c80000521405000300d0201004210036490003033040105c8200c000308400701602c84441c242c1a456051403074000c3c064 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 672121196 1250 672119946 672119951
    0xe0f04020415020325080d0e0c040c0903150b0a030b0c0f0c0a02100f090501111c02070e090c0d080313020312040815010501051c0b060a030f0c03060b03161b0303 71
    0x11605929500ba41802d5160324a000e80400d1700c00c001a042d1080340d440110b45940400c1032070404a2150404400150040d0058240a01d803080b8542c8aa41d00043c0c0303104040244004114800c4c810845124500c415042000e003041030010a07800c0c40c071990300000a40800d031070b0001002c149071054000382548050703a40165540d0046190417041e890340c1c20403a01e040145c0300c040c150001d20329582e82c481d03981130111203000080800da0034400c004007203058402d40c0080c01c0050074001d5072000f051041c80c51540400d4040796842401181031581e04c10001c1000030410b445458a060542c40540701040040500b1803080058806020101d4890000c0c0745040d16246411003050504070102c00301106c1c4101d100051081c1e07a003003c10388240024503070307140c498424419460030080000e903044903400b070808102034a809515801103481410451802d10861a400d0030940660326180281d441402c024800100074103004218a4180101131902010038005402500100b00e030b0618142c00094 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 672122302 1106 672121196 672121207
    0xc171b0d080f16140714060a060503030703030c0302090307090b120c030d0c14011104210203122511040b0a0f0e0a0212070c0b01150e0f040204150203 66
    0x95a810040e41d0f203810504081006c0c3d40c0d000c251000340c0c4520701c0050038131304050040400300d990140003907090260558064010386a025040e4082503802e01640031030741d408022450040c000f55034005240000a41030140002c0d00b601d00500a074000805070086031400103403908000c0461030044007030032035891308803030428102c0c52003021036091034142085801610000c20440314107900d52901c800505080e88403640300c5020107589600b20100780400782d2001c01c0104946801000c05140401004c40800a902d0451070140d41400c5000102038443c1040d1190414501c0111110328030b83c0d190082c0f1200e05510713802084803505a42010070000d140d43c1c1c064444174900107030503100620b0b11034002441b11803903010660309840600300016201c454055000700c010565912090308a00b510180151114000c1d4601d411035403c000c00161494441c5c00f2080000300c036805190b070380 = true := by decide +kernel

theorem cover : BRFrame.Cov 671942446 672122302 := by
  have h0 := BRFrame.cov_init 671942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 671942446 ≤ n) (h2 : n < 672122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
