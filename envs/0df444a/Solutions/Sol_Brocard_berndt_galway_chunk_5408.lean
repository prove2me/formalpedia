-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5408
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:46:14.514627+00:00
-- url     : https://prove2.me/submissions/13c882b6-6419-446f-af67-defa51d2c861

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 972482014 ≤ n < 972661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 972483264 1250 972482014 972482041
    0x323070309061b0c080c03010507050a0f030b0607051f0e0604030f030b0f0604290f0a080c2712060907050d030c05010914120f0307051c0c0908010c0305 67
    0x221281d107001c3c0c0001c0c070805545064006203c41c040e09100040c1c1d004181040003103001003694000790f0084c00076444e94401201c0f644181d51303408002070281c24112414601c01e801c0745081c418003c124504041c0940c41c0e65050406401e800900c000d07804100ca46809030034018621100076000203040e640c40c1c19140504425a4107201104141da25414910a81c0d40d89441e00c8000501410700350320b441c1c807540c056480210030f40c41100801c48140c401408910101d040b56603211115501c01d00f00040c2040a4580210144c6400c001000c1408800d240052049141207141c0111110494408040050221520035051200d40726000300c0c0800142010005101044903800d5034002c10280b03c1e41811554002d8110009005500f04122201808103880055050031440b0082c1c030f280390040c441b203804034400c80050148214007400003400c041c0c040c030003400744801100298000782a02041e4101102d101c42c221a0108605201c20b000c40030003441151060340740c904040004d420701d41c170780c0000c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 972484514 1250 972483264 972483269
    0x40c0806040b0a0b031f020a0e0301051512120a0201060303030e0625110a0b1e1b300f0606160210020309100306030201081e0f0702011104030323070309 67
    0x100d0341350b0350364190a032403c000c00748095099030340c080081030aa101034806940110f00e2540041c1c06440c40c01d90700c0c541031140030b000305800d040e590320b001d084e941880303c05444410440000d00516140000101d0280c000b0304c2240c84c651b00000380f0608502e00a412900d81c100070706d6299110320308008101c4c969140c3c0b401007004007082c08034070200c1c201c0e04551150038201a0f00d41801550b003031a00704591124050f00810a400cdc0d004413541d40030b008009000803c07181c1d43c107034240c0303800d00078000e84508000300300824200c100e0000c480c421141b07200c80c480700a501d6040145e421402c220040303040a281a410900c1200c10501d0b1150b84004c0c0c0318402c0c041d0a000e4891001207000844a50080048902e50403010f001c0c032000a06201c8045d004200d81c0c801030f0b002c1880c113070026003880302208040c400301d01091140003490f160b40c035544054200c01081c0005665807041c00e0002d0032103410281000314882d5440304840300b043c5030031456510000c02a00c84140062021400007030300448803805 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 972485764 1250 972484514 972484531
    0x4090f0b1e03010e0a080c070909020108070c02010215040b04031205011a09061308070305010c02010902011b0c030209101802040b1905070f080711030a0b060d050a0c0b03040c0806040b 81
    0x402048070740003e00401d603540070442d043c850b40d0303d074000304940b0700c02405103406014140d40304c81d603480b01d15134165004840c0003400681c400c0c000031401401030f04290521030040c41140c242c28865003030b0032903410742603400307480c224040e81c2040304069001607602c04005a0010501c40343d450f00010300518691045070211030f4401040d545401d85136a0180c0d0301501122072007000300c5584002c6076441e08010701041d04e40307508141007907041e10b00500800d10a194181e44010411074074481c02503440883c00001c440b00c0103510400005a5281401e480c0200c4051150f182c09902d0034806c048620b90321a5a01007160050108001040310384055401c1426600c80c00009028120000c4480d842540310007004002c2c0055100148040c41f0040c1003000e03c24040c054010824800305a41c4040014001b00365001050005026050501607807000303074070132802c980b400301d12607803501d40d554003a800c03000f400c0d007020041105000c03103070366264018041303040580701307600703240d00c42c03002e003840c001c00650 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 972487014 1250 972485764 972485809
    0xc121d0c01050a050906070f0b10270b2805090405250305070603020a0f1b14150f040b0c0408070902030705040909030c021201110403020d050102190504090f0b 70
    0x22a054042c000301d5008170002000c17079944050524100c21040d141d080141c0390521410002519514940c2ea48402d03641d141e40c541a5444c011003210b5000005400200e09198840741100449e407070320f020b000c0d111071000a807032074400700b40300e0f000038010f010742e202c1817251200c0320900003c42d10201e08148100400e401c58105100001d110300080d030a1907100800078810358400189003641030780a04940001541e4080d010311425108850111900030380002e00c07110300c0c0100700020003a800c82115681714100b03a4103007800c002d0f54451180011190b52038005078200c20001009004000250700840c4907003000d06083c00e04846994503010740c01242a2280d0000c007081505001da025a4002c0819480a02ca140d60074600207000b40304003c000c03401420312a1591818045c1070184400104170800b000d8181480c5400f00b001c21107040900740c1300c0703560800040034031040c00c41c0702c51071501c5c203512455541c1d07250062007021107600001943d0843d281054007010341c0e0729400b07000700e40c1c0d0240e40f803403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 972488264 1250 972487014 972487027
    0x606150302040e041b0b030a0f0f0b030c090a1107230123040816050d0305010504020c2a0616051911010e0a1503060306060e090a02090c0d0c121d0c0105 67
    0x54841e409580084030302c151b000c000c2125004294203c480580c10746c0c40240702840307a04510034241c4e0300381540c43e6899007000303c10300481e05040d140075900c5a900c0d100881e400322007000030440d83e4040c4070207480400e4241020724042d10305010707402880030304100070015070b458031003109e501c91060b0000c1824010311401003000d1100303910075502008000360508a07683c40a24045070745410130b4140101180c00e1000025031407409100b0b80700340c10101c1c00502824070680e0300400040041c1070380316128424241c0141a81e845080140c4855a42100c41c64054182c07824600d140c455409074030b680c424500c1100e200016441c51011101e950207082100f608801d00700003460b0349203140c1085100d003801a0102030300b50390540180003200c0c0034900410200303407210000e01074400708603040721107a8481c84c0341c50014204404856070000000d80020309044c60755104005032100168440b0001300c80c4c0b82c007101255107500c00c09141003c002d8100d801d40f80441005500e4106042c5100e0600c100410305 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 972489514 1250 972488264 972488303
    0xc030b0408120a0b1e0a060f18060207080615030703150e0607180801050c041412010504050102030109060b0a230405090c0a0314070503041209050303070606150302040e04 75
    0xd4828242141c0c40700b19a503c0e041c000c5800504d0320b00f10380f5120300c19400fa80c02a1030660304110038002806080246030600388131b0f007540c041e055000a8020480c5001071420074440b500300d8080500010f40c0a424960324003030304103207441c80140054012185001400050703a60006607102181ea0084d451214200a00312510042c81d244a400e2a64026072081062080d03000c0020700c00e18910741c1c5048645615100d0003400c94404860305002840108818400e845a182e50341008040c020000345c45136550124140c25903105560031550760303402000600030304505000321005040f060308014100b111640d03004141e070225051000850340341007100ca01004d544c01c120390180c40040d00100031820001e10000385030303108850820003c1e1800313000000c0403031a100c10074050981540c8107821a129512080c4800700d030403c41c0d81c14413603a8040003607592410300140000d03e0081600154851910400c141034030401e4a884041510402c8148404441d250b04142c01a8000c4440d50091201e400b2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 972490764 1250 972489514 972489517
    0x70507060b060904180606080c010903200a0608090c15070f060b100503150d03090e1f080a030f0f02030d05090a020a08100605030d12200d0b011106040c030b0408 71
    0x1404e4110b800c09036640e482c013405403c02e144d42445030204101d05541c4003000d940b1240340c3c3c0340c0a40054240c2c5e10800c0482c80d50705c0d00c0003006620040f0f6042000d0742000040700c0c000980e0000010842c01d0041104103407080c82400601c907410b5841c40d00c00e0714030620180f50307072044410040c15aa8120400814081e10b80d004c03100d14a0b0140000081b08804000901250400c817400382c098002c24504245030b0400f100c48004841e1715480340744141e4141180b099003060010640d00015007428441400701745600820001010b0260161090382050b06004045500c01882103003400003030001d40000315800000c94021403014bc500082a4a54118050130000d40100280d4030485101001c1aa0800413845d030482201501d0304101076a42c44007071580308d80e19403d4040119001d00b0b0030b0085110103800058a00c3c041c00c40c5021020500c90032104103800c400624110103540d000e003501d007542c000079202d0600c9440001026a483c1503500d080c2412400d020060010884034040b5040059500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 972492014 1250 972490764 972490777
    0x10507120e1201060311040603050a0f11030304060f0216031509061b0206010611070506120606090a0323010203160e030a15090b07030515040e07080303010e01080c09070507060b06 79
    0x42c41d103084070303000c1080b09001e4490b5000c01d95916080281c651610b01d0288510b0713044a0b400300140c1a240700301d446407000041b8010040e07600382030050f0381d450140da061000b0700103040c0988480301c04a1501d44003d243ca070415210b46d4208240d444184003050300915070207042c101014021510000602d0950080c018405c0c3c0140801100301040c003640d600400d0440c161031890390f61001652500042d665518024880c40d50081070401c588071b60122080d0900d0340c0423101030a80340c0342ca1030034004034030301007400d51042d91070800039640300e03034808480c0c9031420030201c140c8025421410a00500c045503180300c04d03902d0a120304c0208020140d1018000401d0780d0340c1082510700b18105405070b02005c1e000019044580a5810f40080c890901a11901d80036414100e5042c0c0f24111742401d2100414548500301c004c1e00c940307500010700d100c04100460180c040021000025490444014980800d078103c039807244650000300503403546d0000030b41d0003081d0841008600d410150012481510522 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 972493264 1250 972492014 972492019
    0x6041d060405060f0601021b010807050708070b0103021005041a090d05060a060504150b120a0e07080c040605270a1401090b03070618090e0102090907020703031d010507120e 76
    0xe40c00c100612202040a51045030410110313002940c03001d004a840740585806844007030303c04442100c80e548243d0800f40d1211542c100300d80742c40c00b151035803d40360b0004070b01111300803103420040c011400c06400c4449035600d0740c201941007904242c03045104010f15207901c05d107200c01080c040351039602c12070703c00350300c9e60000191040d9040864116026281030b019244c015401d188000f03e048440c8149002110401000d142c1000d80c0840304900c07146c000382242001d191034030140d18450800f031160500070000704004000e9652150306002c1a200c2e1b42d48202d10458140c051003111103081d0444000084913840c04c0340c81e40c1d0f13802404500130149041768051100b043c0c0000700e540000b6500c25044c1c41c008504891515a4800702120f03001140b0504844426410300c041112107460f4100619000b1864005030a0641d580049942460704035007500041e44820707020414540c001103d4203511029130744028500d800c800000e0700703a100e0b07004021b0266482001a010303c500c101e080d0288513000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 972494514 1250 972493264 972493273
    0x4050402070609120f020d090f050603060a270506121f0906060b090108101404020d02190818030406020c010804020d021009140406291c020406030b030d020606041d 72
    0xb6100007005c0c030020039200809480742c5480b03844d0250003070302d200c1d044502e041c0098240e142400240001c0f5040946001c0e0003441c4c4850108040203907101e64403801403203030200000000c03203403207900540e040905881c0c010703041650f2601450901056410109040034002401102036075a103030002e10003e1070182209190050108064020740000c0058010990b10700701c00d82c1341c20544075100c03c40c510a82c81e00c2c5000c2068900141819005010410f401c0b03036005051284411613011200c41c04002d0700b000541040800804003080d0f040030000c500c54000541c100350070420065524443d2001c514140082103001408542d02d28600114060740601800f80100701020702074a1040b050080d9802c04052068020860030b00d4800c80781112005608846514038285140081700b52561200f80810401c021001800f4030303810201c480c01440c8031006a907240f80080c01400c591400b45241d12980085500322100c51303001a00d140c00483c11034001600400c000d0880000d007020300c0488455028 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 972495764 1250 972494514 972494543
    0x108130c080703020f03011b0f12020313030f0c150218040c020604060609090c0e0a0e0307050c18010b0d0b030705100306050f060415030b0109180906060501080c04050402070609 78
    0x40032038220101c82c130903a00b90103074001c150200340c03c0c0d0301e40040312440610604000d403130081c401d04006200d0751150a254044417100c00c0d443c4141c1c0c0c8212210890708540351100810590300c070b0b644c560049141e20300220078000a55484182a5411040c1054a900480c40c100d0103a0407448000c6401c200038020410401d14200194990008072010b803010f51506800203411380c03842c018900c031a0781c402d601304620f41c02e00005030101d190282102510039503031040805401410070082450710b014000a150001594003042841c080025040d82e00ca6181c00040101c401200c080c0c6003214044803012800140ca200480e284c100c240d0b00c2154003021060040c00310f240c0607440a0b0680340c064584101544544080c840300b48103130720a03402031000c52310620400601c2540300001c044c50501d40010304540d5003d07802c3d055072040d5044501c0c96641d40e1080d0030030a01d481010000c1c0702c282044035403850700a000126500561298070b0041c0d8000820104020340c940c03004030b4041e40401c95020601 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 972497014 1250 972495764 972495779
    0x1306080f010c05042c090a0b1f0501051605190b010614031518010b12011d0c070501090203070b04060f02010e07050f0312031305060c03090703060b1207030605060f041103060108130c 80
    0x5101f200a45000304840e0200300c407066840d4000b10052050b025100546141c040115500d5200090596407408000c460800007002440641801d0008007407050000d051030428400150f010792011040c07001041f8041401030f072000c240c0780c1c4160703030052440e4a4000c0d5000300c2d050031640414840c8110030140041000070b408c101078010b020714101c0d004c0150703803180d81c0000950040d002044014a0a00c0014214a0003100600481d0b00c190004164180d00c0d50101e1f251100c40e070006221a98042424822503030b01213180740b01960203200038800407881044250715100f00c2c4c010b10b40540003004000390242c5007001895009084007900e035a03245003075801d403050f18030022022074090082d6008a440040003d080d00d01440250f000b0300303032052440d91035000400e00290a10f80048100c414201204014020840114045c00d00401c180c40d008040000c1c0510328004644a01c0c51300100742003030f050400a6175444003082c24050303106e0f19001c4000c00d00392801d000091842421080118215 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 972498264 1250 972497014 972497023
    0x30309210311030c0d020705030f0406080f09011e110f0711011b0312050727060806030d05031f03050f15060a03050604020d111306080f010c05042c09 66
    0x2803a540411001020301d2210b4500c1c0b01c1543c10140b4050240504207000d0903a900600030035104008582c9002c00d0029a25203a4200350301c400c0100e413440701008070782010141707426032002c0d604008021b10300c04010f02d0f90307125084042c090b040c15512885145c402d80030004803032701c04403100001500c61a6505c3e1050070300014044d01d900043c8010704482d18200050080310005034551252950070f8680301c0e03c03500a100c010410390802c5645440d0a04141d80a4a411201001030011107800c07800d128014048a1000c0c001c2402903008640d8601403507070000c19a41c01ca046240e0030a60070000d40050308824019410250540c0103069041d20003c00014005d8181e50301e240001d032003969840c0400013214aa0b20029040d500014001001450000e002c1c101da40d00c6901c0c01a030000681000c103000c8a440402007521640d01c3e0014040c10504006440d10304454400134050356003101ca00520350700603480741010410b44c0420311840708841c252a030001c0400507000412500c4c201a0303031650f9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 972499514 1250 972498264 972498323
    0xb041b1d0604061a0d0f1b0503100602060c16060e0327061c020903151305010b0909070e07050f1c0c0e0603060f06070c0311030f06070206010e04030309 67
    0x19503d00b403000555103508208400043c608440b805081804843c26880501081e0002160704d1365910001c0401100d0300c000c4140349002e40da42c07640c5a20301202d10003869111038101c070307007554040410001141e044608a51064480c0c20850000300d2040c91f10902030945001c0c51a0540004100c00008141c0006495158031041020b684410041018454a8450a040c03140c0041c15100303800d40b04e0421782c00804100801600b103a204820b00041c895401030192207610100107240804410700c40f00340515140d503c0103c0320381d0058102070007515592080c0b4441c0c007800003001000980110f00480c02d403000c0c6118102c055a40341c540d00520750780c0d28401d4a100290760b00d010741c0c00c000c1600c40c104d410426480509000c2c50754940000304501302c43d15000460740081c04021071400607483c02184001103200d40c03207046048000800301400d240410860060641c8017008011000354000703070150448100340c01c280a0398030b6600703040b40500f000120103019120300c080494a9007290500720b820 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 972500764 1250 972499514 972499519
    0xf010e0f19080a050c1614100e061905040b0703020d0f0c02220204030c0b0c0118120305070e041b080a090809060a0c02030706080403080a05040b041b1d06 68
    0x44074100c5440c4103885245004050030700441440f03058400307800b540c014013003c07800200722000514a20805c00001d083c6400c698520080d01140328080d040142d080b005010389814004000902c84c0003190075805407401518113424450042c0d91098014030845014128151405590305407a0402070b54842c0c1d882d44010008850080603a09180300b1607820403501e9008150200308102040d220040501c1c510030341409603420440000003c0101d2004401080030803400c54582181e81306c0c2d682115030301e005039810140031a03256400070790f001c0c00390b4070014181c1c10002019141c0c01e000301c1d1645c003a140c01a400528100012100150035003400e0301d039a9855a800d0420b41c0c0c1d140700740b41999801c481c01001d25405010901c910300e403c4001e800c2c1c00700c6501d010404050940c0011b80351001d03651144010411440920040c140d0002126034001103841c018401410b2a58640c040050001e00c05860304c451102c0701100c0a8070007075004014248010303010880103074814880452942603c000f403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 972502014 1250 972500764 972500773
    0x30e0a0501050f120912040e0f070c030909051302060409021e0901170411030d08011a0702010e0103200a030b0102011b08130312020d052d0a020c0f010e0f 68
    0x91998414000c55030f0a0076000a480d04010700b46400d4840b085000c2c101082d0790080c1140d041040c00d841003d00024040082c00c600c1500784100400059540a4900030030040c10290340ca0100350041807510483c0d49650001032507a542510f20b00d2251a5a0402544000009000207075800b080d0083d010700f1110043c1240301c1c40c540d01444003a44030701005540807030303200e0b007219840c1440701002c580d1183c00346804071016482d41d400207040a000315804404150018014894030903042590303160035075411403142c5007900540001e0400c0800540213410551101d003500c00d60900408400925256240c0c46a1510790101e0301078003601d00c08102600562a0103003800c001c2030fa50529019454a6403540c00440d00d0300c010621010312044010b606114915403c80181d0030144000c090340040c07901b000510b800d0035900600155901d0041c4209001168841100099907640c241c0d085010203400507556510480f8040c204481001b0100407540b80494014040c90082030040100c2d0120055a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 972503264 1250 972502014 972502019
    0x50c060a0323040b16050408030c01050919080f032e08120316111e0601030b071805040f06030501020c0102031f0608010905041401051503060106110606270103030e0a 73
    0x40c880702c4421540901100b00d038201040e40c400071108403610b22815442d15030b28103a11000c00710301d9a80999610f00c9030703039501d004005809200340950b03145411015441c0c2c20340902504c4d07004240c0903030b40c40500f14484c004040b41c403819001745c4401c0b401c14210380181046005840070541c0c4c034518840d401040c01601403c002d0420264202c0e0300c51160000741c5003203501040400c44d03059401ca95108074601c07d000781c0301800311240b0070301100344170400f0042100d5030440c5016208060003800303070303001c0c44055440319203107807900e0001c08140c803802d071400140c19509000501c058150f940c00641035520000e02c02c03e00f1003040d0001c600c42d21201100640620440074030581c0c9a0b071610030100026003c0f00140b00c0e1103040d13003000d41c00c6030040c50380c80c00d145459942d1508484098130310441810502050a5071401d007804a94010000c03814807583b045401012140c60780802045544101c0d904411b4510045030b0f403952203882d500d0b6200d0b00643d583c41e40340240c1b1480702080107911171030070304800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 972504514 1250 972503264 972503321
    0x50906010510170702150a0603031e020c040b06090d051b0d1a0604090602030f070e0405090a02152a10201c05091f09120c050c060a03 59
    0x910030341c00d8595486410382c000314040000507440c050113040860240c59203580b007044007449568000c80c03481200023403151851401070051101d503a031483c11200e1030101d081b84213801050302c02d100c08080d50046144005180008c1c0640f20300b9001560104a5140203818440300141c1088140211007040c1c07030b0196581c04008400d2880c42009203000c54043d01503000704c0145100d1500b00320003030030229464240f69241e0013039801c00c492251506208800700100c3c00e1b070060103003000b1103040c2c604010504200110645827082840081c1c0200d40007184040d9900221040b030310150185900c0480070901d804588002c40d100c2d03140b00510380302d2015080700031400b038030880100388945c18039028546140101a0f29940050810540c40081c44120303002c10b0300b4500030244980920070290044400b00d00c2c00315101c0c41c1c9968000c04a603c0d001441000984048160541c41c01504240f28915030300e252051902e40d107048040c0e0040c8000ca800345504d501740d000359100200e030402c51000000450003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 972505764 1250 972504514 972504529
    0xf0f01020c0c0a03230304090906230603031e121008060a0e030a210504062702100507140a080403030f0e0d0311010908180a050a031728030509060105 66
    0x400351131007178080024000c0c05902820b82001d00f0307010045e00d080540c0d0780d60030400c4a0100b141500c405441e0150740440c4144070308520845015810f0f440114142140440d90300e000f07d10701d0070110300320022040c001d00c1e04103081c2c03880c0e520b4071600440d05240494407040980740c41e00c42e211a6200744001b19111280d207009100c50036000e0001541000005442100d80101c203042c1c065583c0407022262051059900640344107074041c031000b090f170200100c0c8181442c042151080500300d01c007500c0c07000580c3c03100c984601e40381c06842d03d01d1311911303142400000354499000403400c0c0d1045044803020421040042c0084a000f5220310580c40c00c0d8030400d55000003802c0410341d015a01034507000009010341c48010441c0161780002030000010741d50100c07281e10254000e081d101d4200040c0c880f600d40a0700050284c4815075006143c40d2442c0d440d000407121a402081c0514004a4020720350f2640e0b18419000c0707441808619404103d049001d0018001070720300041c11f006280000c507140c1000d10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 972507014 1250 972505764 972505769
    0x20d0603061d030f0702010e150703110f0723040b060a030509010c0905011b080d02040b04030516051819021908070828020d021b071203090312020f0f01020c0c0a 71
    0x800d4180785c4078055004681191410341d025038040e407007020110501e001e000240c08500d00c2074550002c441c84070003403545030001c001c030680410b50000c0b00601140125103100c030440c6e403146422074600014800000c0141c0603940c44550081c401160441089905400090180403014000c00c4080c0e8580401c03030310640c10b40a460702150f242000e020740c03200046041d03d501c5000710220741c202500c400441c021390340180c3c41600b4161000c982401444414082d03030078a400180e540400103443c2c200443e0566425080c2d4584201c060400200619000840101c0701942280d0866580110100380304a01c0e007004e994400040b44200060703c15401f0303540f00343c0212a04004800c140300d000d80400c809458044c00340025540a005503428006a4005080c52922030b24105008000081b01c5a00c1c00d8003a9201700e0b500a100500040825000304102d401d50350040200743c480c2486a1081e032030841c034003004c80c1403480303091145907101d041980600304008030001619010007114013080681549070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 972508264 1250 972507014 972507037
    0x905150f0c1804240f1d01170a170703030509120904020c01090f050f0d0201140406321501020c090c071b0816050607030c080c01020d0603061d03 64
    0x1000701c01842c1000031148416010300403c0030400422608802107440845484600000340141007400350a80a400c1840500f911100c04103940c0003e02c0903115800c2d040c4150941e502d20b800240a8201d8148039403c0d0b425080b0798030040c2c0f550000020600c9511800099000924180100d50100c1c1c1c0400d80130f210800d1895624100440d0100700701c0254010000d02080e90b603540c0d40000001c00b5403a41d4481c00d4080c03070240c88018021241d030703814000c00d94900002c5916020805d6841d00f662001d4070f80141d001100000e071600707031181d05201040003401c1c4904460040e5401c07100d0f5110078030b00c2441400562260004a07030b50030016a51000782586143d40b003a00e81c000903546820000290442c01e025034004000640c517441d0220789105107401154640d041050f11481d2a003950346402c0007000c095940519101c106e0b1001459200c0b91500180901c000207583c1140e11800d4044c2d6001c0361060a040019a5aa140c0407005007440b03801135803a403a4049141e103007210088250703864140c22 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 972509514 1250 972508264 972508267
    0x110c0102060a15320303030906150109080f0a05210f0304020612040f0b0106110c091026070504060b04092a0527010c061a040905150f0c 60
    0x3860460009400c5507498078030f107821444070000f1104007101c0030b0401a410040c05003849083c004510000c0003241c944140264130810510450302d00024029a000e48000c0341034041500d1040101e80303c419952142c8414420744c0404801c00d0340103c1e650b2841441001100e00182e03241d4607140403000388070030801c0c5841c402d02600d503000078081e005583c40751004040c41d15002a6441c0d8600c03002c02542d00741c4070040e0300495402084075805655015103090305090700b13001c400b03030f1419a541500c005554040c001102c0410754641e0340d988070a0260001d1114032540620702d680140312060420801e0010f8882c610700004e003400c02c1c1c0300341070985070705a1003540782c1402c0960704800f4050407081000e4070b0000900c2002445a4100c2050a00809a0722240d494140b841d09204030042c140010120090352400e41e441c0c0d0382c010303446190403a03108501051000b0090070f43c006100031200ca89411071b0501c01c03004200329000c2900700001001d880d05a44070707221641c046021010403138182d03690300750 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 972510764 1250 972509514 972509521
    0x140a110a030e0c060f041a0f040b0c0106090e24060108040206130b03100810062d0806070903031823031006080303070f03021201060e0102030d1b110c010206 69
    0x209070410000800070a04a4480f04440070104007240d00c4002e8190303101300003050510241c0078184404510075a00108203050174031000102680c7e1243d03100300c42c2a8880002c880401c01001e4104000812044904210030140706109640f1020645072034104401c03210000c0a800b901c81c500030b40201d4040e503e00640e0380d240e50a105559108500f102c0250b5401c81c400600c4140d443c1c000c5124010844500006070700d000011881c110000054400c01414100f0500843d2a8156600c03e2035121083c0301110021842e84003100c8142c0340c00c0881c49004103420481480d4000951808491080d07540d88003104040346051100001c50042c4030031070000c80740b4a4004c21400009410100380101a60304c906030507013482080718200d170f01c04007858002008004034203820030817403c580c1e000c2e42020352034011803101c016400081402901c061050241000503264400c000341c80752014050401c000320030250480018010141d020314000a0720003030241c400003004140651b5560b01a0028002503d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 972512014 1250 972510764 972510767
    0x120071203121a01110a2d150203061008100308070c08100902030c0f0913060b090f011a0a020d0e062203050601092009031609140a110a 60
    0x40c032a50095040007a070400c9400c44031a10320074045030702ea000702c030684100c8640b00007501c4101518048140d80c0c0009070040e01060200d110030349510001d01d900000c400310100b0300c003454460050b001c1c0100c44c1c40000303181320350f540740e0045000d450308440380d542401c0b813210f003116012001c403828191304050610400008114101074142e4600c01c016648805840d03003502403505071600d501d41d1410ba2211b042100f54202808217030040b040582e40c03244070308048008101c00c80b90203410003c951550b483c4113010b10002d030740203040c1000002c1a5a165060000044402880c03c1c0600300e16082c041042003180d800c55000c84a4200b21074014003281c800d03010007560314003c9000d02c180c1098041105100000c039542c000080306031140c071018556401c0d418803501c3c10030143c218003481d92400030160403105000d03003141e88500d002c440c125a550354a00210f410140443e590010003582103101140f41d5005800200e070320030842c1060300290362815030701001c0e50802401c0d916429002c00c408907425 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 972513264 1250 972512014 972512039
    0x7030809030705150a030e0c030304060c1403070308160c1703091f060e011406190c0f060b180f06040c020a050a0c0e130201051204110a030809012007 66
    0x3038001400d440c0c01550b18008030b05001c100907100c0d5141e120000740c113070a5503018407500f41107048544c0180717100c00c0e604021986d64822409001c0038044507185440c10054803c1500d00d1407002c24050720740340c10446c03030080d050b000161402041000d0007014081202c1c41408689038050f0002d12007041c006c000540c2c4201c552001c1d04180340b40c054001e0083c50071411044000442410150008000749003480081c00c0701c2068000d800d810840c0c0448000c584d4440c6c0941d030158168041c0d0032000ca404081c10b44941c0c44204008049086003243d460a000f2280c4c410681440c040d03420f0b030002010310300150702d18101100c1030700500c25950007050150030541e0101d9183d01650040301c2c0309045039115545040b010400848800e40383c2c110510400850340780381a08030000c50301402009010b40d002805901490142c030740000c82c00c00c0003c05001c00c0c22045035598201030300c600c48072a101e041001440e400a2010741c08036030040c19072842d90a10381003200c841c600b100c0140211038100026201103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 972514514 1250 972513264 972513277
    0x1090b09030109120e040c080f3418090c090311121203060118030f0b060f0607032f06180a020901120b0f04050d0309020105130e060a0b040305070308 66
    0x3541d030b1200f50800092002e5440605840c042d228907040380e40c620208001e56401d1901718040280076018031000c8220030a00c0c641102000201003130304110502d464400140e244940030008007004054440780c0d8028080c0d981d07162000740d49803122500e41004901380c8280d00c1c046000a9182001000803542107041c54004060003051b000f204c10b1015011490f00f504203224003104240003081c8441d940e001203848004041848201305c245d451500c52000000d56094050504001600044c0640d0364085c0d842240c03100007003089440b40c00c0381c2002040900c4c810510142181d5054480d00046580c0301074090010301c844c000c0c1a19510220205070540d1400c0030201e481c420005140016580c00320070300c1c040d00e00c80b03010301c80b404800c0c108100141405090b550040e1101c0c4240000b007400400e010b640c04e0100d01380404e006200f840100c8452180d1030f00704500300c4c2007113801305038110321030b02c041e018040c00c4442090203919012003105a1185100c000c046038080a41000003c141c07102800d03c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 972515764 1250 972514514 972514519
    0x91c0c0b0f2a0307030509030d092709120c0c1a070201031503080714150c03040b0403020c0a0b0d11090607200a090905060702160b0d0204090c05032401090b09 70
    0x807200960b4160700c0c54000901c214042240810f210001e0304040112059005091509052092501080150109125041c0c2c92042207118007104160070b20780200d403207590701c035603451a040d0071840700400e07500c4650030072603851150f00c400080d001c043d007031401052641070240300c1c544510360380150010308512840c0700001e82c0180703000002c9040718000e0700085016503890280d40f8a01900c090604884c00310b121203c01c160000c0c41300c595a0344c8185c0b64004da0202c00349945407524241a0300e042036441e003095101100e000041500248500035020132084041d003480784040c10500c1c10700c54001c200c2d807150401428400c81000c55012114881580703000140e010001a81e400820a1580d154215905040d100c070444d9003001020040b003a0b000c6920f1000d0300b80381c011601d03041e40f900d84034402d2403100403000c113000900c400c083d4101c400404001100b00821040f81d41c4c060f103141c004079071040310020500341101c41d2942482a95140d454169101804203041000c5ca80458215000301034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 972517014 1250 972515764 972515827
    0x6031f020a11070b071506060903080d09060e0d0e010207030503030a1518050f07031514040209031006080601060f2f16050411070201020606040b010302091c0c0b0f 72
    0xd05810305010040c06804504d08113680d030555814049102089014125807440c5441c40800a440d480810030068961000c005036943c0f10080c0700c0b0028094503040584140d1500c024204100f500003030010300d00d141910360480c40d028400046e81c883c0780504c005003e640003000081c03443c9500c0d81c4070442d0307a011001984130040d11509500f150b801f56680c4100401d40d18000d00000f13020003427566901c01074500d41400801d044401c44118072505108100113003d01b1940c0c1030050756240c06882490302d0103400c030345483c4c4241c0201c4001e068070780b0481007240070303010000caa00e500c516002e00325042c03540c403144401e000d400076100342102c0c0380030b0075030700c60140e0590802806030500401080c6502422038060160a10080001700d1781c405403400c003246000c000c0840141d8010031055030140d4102c0f0001140500740c80143d01900c540d4504a0740f204100c0c902000b407480300030100c210036001d04100c0410710303201c41c001c501d24404d01444080e042c00500180509100041d403e4451900180d40d04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 972518264 1250 972517014 972517037
    0x10090311060a1e0c0b04050d0905040615232808090a0b10090f02030a0f060614030a15171209091f0312020d0e100f050d060506030c1206031f020a 64
    0x10b2000c05e040d2801c0b5001c0e0030194129106a502c8181c0d8009440101ca04010051600d506020350110b2180c0500c180200f202e0941ca200003001c2c21060074950900700c0e6961030031805c01c41d001100c1d813031400c0321180401040551a0501ca00c0c0e1007031082600c1002407481040301d89501070100c000400341c50324040a6440841e48001600030705c60701c10303060100582c480c1803072000c42041d2940d0a01007018640f80c070004000c80c0d98446044031143d801c1000d400d075641c880f100024040c0c140d0074110000c01844120024282c090007003071b0440d044034001030360104094640c0a0a107803082018444c0d00c8035072003010940183e486520401c00b82c2c0407641c0400c1c01641ca59403208503104004400d005170b00680641c082240d0032140c0010440e0088802d05d07440d4000d240c002e88050800c96210042100111b1001c08000c00d540c0000050080140469201d04d005000c144040d070040840c0c0800720f8020000c5952410300090716030443c06540c07081c000d081c3d074100814000350803030510f0760704101240d03001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 972519514 1250 972518264 972518273
    0x180b0118111209011a03030a120b04090c060906090e0103031101020c06040309360b03070306090c260d08220b0426040504020f040510090311060a1e0c 66
    0x4140b0403004004109041c03622050326421a070a04144400808680c400a64503660210440e13a400c0c2c003d0070064500d14810355a440201000816a034100d443c245640e81403080c03402d24402140c0e8a41c0c0ca8640c1030351284d0701140c1c140322600c107050704641d9900060002901440d207101c400c68900c80014105090100b81c1860308409990603008562a05420301104048030071022046501480ba103100204501d450034064004056040079942d4411305004955418841a0021608a036040c042080c0304d0404448180d210300c900080c000c00c0e2600c01013204540c10800c180381e010310010b4080000f007201c090f103400c100102180307141841d40b0841c17060031400542c21088a030040301001340d503241916080303440714624001f11a12001c0e0001c0c02808030a043c04550941c6c00985000d0303145d8800ca12010124000d81e000389034009036000103442010360100b040e0003101d0190245c6c4111610240c1448907a20a800480380095040120135000e01e074255560312900c003841c0303400c0f050403440e80c46 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 972520764 1250 972519514 972519517
    0xc050712030203070c021e2416030e0d0b06010305060d02060a0c080d020a050c0c010c0b22170a021002030112021507080406020d0909050601080f09010605100909180b011811 76
    0x94241d03007e1403419843c1c00c0c0a0382c0a40d140e600880d00100018103000c544109010700564030400b000c03550f1410041511500000c211030f0005071074214110080d10b060f009080c42125900d001a01d00070000e0394038235100d9819280c0c0317900503100501d0482003000c11242d0350302c000001e0b00c014030200000344640302c5070310051100f070a10744e0740c3e20b49406107070030f102d0b08003014603036681e0400c04000303d80e402107000300c0c0343c00ea0041d07010140c410012900e04d001c000c01c1c104144018007185262030790f0708415502d800041c103114850b03600750b440410b044000d1030b049000c00c0c011240d58401c42001c0b00300501780082099070024000309041d0501031507541c1d00724564419042403005030401c1c4a004201c40d00103010801400742c9007000d000c80d2a1480000f860410010000701105841101003012041c017984103c014200c05081040070701800040500015480e114507510b2a15181ca8480768805410381d00030001d5001c07001d0f000503441d00410448501601030315020b4a652440703201c406085110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 972522014 1250 972520764 972520789
    0x1050711040912180f0803030f07110d1e1e0f05070611071e051011090a03030503100b0414101b0b060a06020f060a2705060a0c050712030203070c02 65
    0x340d13940520080f142642d807003107641354440410307282090014044a6404401d4a81c001d100c441c414155030350b410000c6803440401f43c1080c6d000c2c00b42c18400c0700120340c80303110304002100c294819581d19807035103801c80340c5001030301006030700c00881003c000031103200d0040080c01d032001b440c01ea414403400d6290b01c002c82d0003200722840b110034005045000c005210070f00d0700503400c840703480c81e008140075116161148904000c0c11403c0340e807090303101c44480e0300700c00399800301c8000b0700b2030b000c4280c49180191640c1d20a0b43c0844299100038000100c1c05151421a420340b968a401038000301100390130701810340a406407074014400b544042c0381e0138560b01118071026a00030801d0214506000301844081802d640020b42150812000581102030028060b908407404080000d40390040904140507032400094021046d45100542c4050241c00600385005854000c1d080020000d140070546080c410700c1c0c0018103000089000926840c046d0b8040d40c2e100c1d1041c103001d0028001607000408400101 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 972523264 1250 972522014 972522017
    0x1b0a05130b090112030c02060d0216110909010603050a02060f0f0307020d0f080114240c06151c0602070309090c03020c070b1611180906070e09040201050711040912 72
    0x220780c9841c03546041c0050500500b4800204011440141c90041c641c1680b90000ba02600c000180014851086d030b040700d1091082000d202000c45c1140303010000c05c1070501301c280c894907511000c41c42c80345040c13181c442129801802086454007039402d2109030741003515903000c04c039001d02c900c0c802c1944c108001d40c071a070441e0f0301070940e6010815024000e80c80e04101581000a141d005101105610703d00d0754040004a41d00554201d64030403400011a01c40300001038844045030050440c000040e000b4090f8401b0694440352520360014001710307054000d20080041b00002c0b403940030074031950003019120701038548014581c1d1180041c800356640c1402420010390300203442c0f48040424040d10740030380b100d02e102c986404c1034110f9648010f60b9143c0302400d64503511918002c0e590b9088180e0004035031500c0001c0141c5000f43c15903803030751b400b16014000300741840301040b140d240001301c5501c96541611800d081801e2a10303401c0c107012088800680003a034900c060b5010418194400340040880d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 972524514 1250 972523264 972523271
    0xf0d110a0608041406040b0606071b120c081209120a020306100501110c0102030315010e04050a02070b10030305030f07021516020c010203030108030d0e0a0611090103050f091b0a0513 80
    0x62130070304482809240c0d030b461560041002d220008040d01d8500740c2100086a14076111103050501c40d044085030201341741740f0030740040c00090003004811085030041c000da42e0300908640d11b001c22620342d4100710b0003505e0500c00b0006d8188614090710035404c808905c100f2907028883c030b84c3c040307880c0400a540f00c03284001c1650041105607842080d10742101060000f410a40800500203560390101510100c103035513041d5400700459101c1e000c074056688000700240103604092031a107000390301000c030655404411100154030216210812800c0304d9040d52000e00e580d641e03840c640302552000c1e2101c0e007103004001006444241103c80180503000700448d902e00c0003150a40a8a03225109854906541050004001010010042e540800d60039440400c61540d0b40303011034207110141c40c000300234070f152983c41d842d50b0500b60060805040c080e01e00704459120b003d00e50614200072280c0c0c440c180d214000315881c50140c44806000000080c0c000c81110380c441d80010903141c150401659902d0b903 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 972525764 1250 972524514 972524521
    0xf03150c03090f0b0a0f02030a091e120e0a030506180709090308061201020f0f0c0709020315130605040c23190509010210020f270f0d110a0608 63
    0x5403148403400081070404102c0380100d40e440010101d40181d010740b0080321310000800354101600b0014004e103401e03074119541c1c50901844e00041500038020740c4c21070b81c2441b039859640300d00c000004515170070215800c295114107101310b0703002035100b10380740c1c03c0030340c815001000440c00c00205001d580c86101d1400c101407034000071031511809902c00d40d82c16003400700074030100c0d401c107003556041041038900d903c084421002c241d019100369988a648101d0001d4680603040c02c0a000d044440c605400351144903503148850b105a000503944103d201c00320305501d00c000e1070061b200e800b8551841502040c460b64031303000141107070f2810348142e011450754090f404e0b0121010701c0100d06810003011460a050f2103c8480800d68192038140040c4203000504006030780c000c2044800c05c585e200415542c1c1d1006042051a40d01710b030440c84600c41c20172420030144510403150480c1c0040281110b100c1e40c02641c2049400c0d1402041501c0d015281080c984094844030310754009405e0f86c0c0c4560001b401c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 972527014 1250 972525764 972525803
    0x1602011118040b030102040b0d0e010923010c080c040b0d0f05180c0607050d0c0501060b07080403064d120106020715170403050d0c110c010320130f03 66
    0x50f1195034880c4640d10410050011018801c00d403910140b83e0070002441c1c81701040c0315401031010230b401070306142c400384229510810524055458606a00003844004d001075020f0701c3c030f43c50503100c51310008014041800014012005448104500007011804032040c54252048a0040c1c540022401290606071b072400c10800c110582404107441c1c49217809030585550780c0b54040038407544100074420a5070300a0043c01d420010141041102603681d5125601d017070506540103100031240f04c1d041200390140883c0a4001d06c4003440d080000c000500803a16000e08800a0424000d08034501c4c4440d1f00405010603000e0150105c000d00c0c040300550504002074a4049103502c6107010301050000b90080603840b41900484d0b00f0b0881b0b640d983d5455a25060f41c142c0281207200305001d107041a0008074550000031409512600230580e021100715500440583d000216081502845055803c000c10601c070300805010548100c40c031140f640f039190400354a102a4002c1e60000307079050002480703c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 972528264 1250 972527014 972527021
    0xf060e0d202119020d06290102010506031e010f0603050a0b0609041703070e06070f02010801060207051f18060201061404050f06010809190b010e070512160201111804 73
    0x460152800c0094242c94204907540c00b120742d221119880071912078801c5485503e251a0300302da02075410300030500340c020b0400540c907400b0081740c04079a02c03480c11041940181f107828000c0b68007038098003030312036590705036803401c03c442602e080d80e50341c3c61150b00600d00031441071001961040000e03050b07404d024244034611483c091f00d0f0600c907580c82c400344800200100c01d2180540b00e84076030307941c40740d03907a88040d101301d04081619901b000000820004002071900d920700d469100b600c40c2900c0d41d0700d80e182241c4c1c820540c040d03190008000503a00310403825064100c1105010341c40d24409400740d207038440ca00000e03160300c07100150307440b1031041c0140707920100d8112803244103035410803951400c1540d164007060b010700740074140404031340855400002440324001182c000b4014000201c01c41c0b50600d0b1100c4240b042182d100e12480c08a03002a00c901d0440d0a000382c3c0f0311042d0056112030949a107080e8200c8828000c0d99a200070522880580e0304c0a4524000381c4407000341030481e8681070200785c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 972529514 1250 972528264 972528289
    0x5040e0a0c1211070f150f05011215060f030c0e0702030708121009020c031b0d090510050d09060227010f030b0402070c032a0f060e0d20 60
    0x1001d041000c58a1996481620355800351003540d4003245604030154400c955214440700505030050302e840f41400e200c0900d03d40070207202416410840500b01800c0340f82190028000c3d03c0203882d204400728041200704000740b55205440000003a803e0781c6500c40c00200116501c02c82e90b420f01e015007000581110210968000894005907140600aa8600c6068811000301120103400350700481c1c000f04151003503030064143c01804540d21100034480340e540e900321000948031442c5000005481400c00b007056031107d074180d01d680f01460b043c2810001c141500710341640401009101c008426401c40c040d082e002401010010303030300d0f82810b4000107105107160442e1101182564000840e99000c40300203500300640c90f000400020140015020b441100c2c030140c0460785c0c0000110520003180d11200c00c40107182c816050340c42f10003086020703110b901e01c100d403510178901e1003c00556016071424044480010002030f20400a5514240070b103c81d102c00c5508000000003803445818200b401095 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 972530764 1250 972529514 972529531
    0x504050718021b0f190809120c03070906080c0f0d11011b0605060f06090d080a090b070b1e04051507110d0903110316050d0206071709010e0f010804021207050d0305040e 74
    0x40017415494446140c45001c50050140c1da8010820088450500c00480103010007401e44203610746c0c0708100800b400890040c1d449501038403424841c1c41c40c1c50040f40380021030141a0349179800d829180c0380300303031a00002802c1c1480604450f5009140840c6145201c4034400d001c0000c8c0c03418540705004542a0764100c46000302c104102104040c1d90f408080901c590344084c1e441c0e46c4a01059040310085490340c17108602102c04944941008124105180b04010516101c9141c0045110301501000d00b542c0203000da420161604000072504030905a0003003042c103007268100020880030b0324020418034154001408a00b043c0704000741c078902e54070b03e908110000d00421022203008202c1002a10441c1c0c400c4050381e04000031900c641e0199001c941d0080b88043c018052085032061950100307003414009084100b00b10503503c0d201940454002c41a036a84c0c070035a48940c00e200d400c0c00c0050080a851048201c006860307503c50303d82c0d4480342d00c60350314140c44614044429110900141a915 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 972532014 1250 972530764 972530803
    0xb0301060507150b030a0f06050f0103020a0308130e1f0801020f0d05041115031006020106030b0a020d110d020a03151202100c080409091103010504050718021b0f 71
    0x451507601c082911032154200c010b03502481007042c3e81000070052010002d405000303070307548442405075000d0704000c0b01d0b02850092256a803900c554290b0180b09000c029480000c0c404103001065030100a410740a15040200c13100b82d445080d1001e1549013254400c4091032096071000d5107009101545006200140c000c0d0300300400f490030f081d10760080f0761000d02c409982d24000341c10300c0040c0a140180880c054144031803a030049090307100301d40c400c80740745a080d20b05d40c1c00002d0a03441481800100c9030001240040e030741303641445101a5000052215035607454080060714205420002c0070740545081d0011780d5501c660601500780e40a0010400b0004e1440d0320410003052012603a203081e07a8102c0e0000041400040c05507084a881c0101815064000c42d0109011002e58030081c05d441c01040c54a00c9414203500b01400d0300d038200e900034a95000786000300104c0007080c01100c3c400400346c0002d030138000b2885107004c181554150f413044030f48c004095810300d85800c0c070024280e4001d918205 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 972533264 1250 972532014 972532019
    0x1611121c091104151208030105031207030507200a08030306010f030509061317030406050f130c06140409180b130b06010c080712081b04050a090905010230010b0301 72
    0x240d800c82c81c20451409142c0381c42c6130207981c40003601030030054094422446100b05007418800d0158100f4001c141c028401c80407005012602c60058807821545695001c0c0b03011055640c10b080242110301448000843c0709084503035030b80c0d102d100c2001c2c24000f0029a182e140402c001440142060411814141f0300414040003800100e00c0942c0104010300303001e4030518501e048080c140780300c01c41e205890408800e00040200b1034204c0c502400003048800c486441d4000c0c048820118004010018205004100086402100200c1005500d40e0315181031a0392107048406841e406011341d42c000e9075030034011080186d551219a00702c178003c81920300720300035561000700000700642103506102080503400c1c03c019032030084a1003240d100644002d824502c1c0c001800564040e2004080d0164100900f4100b210681c01d81d0200c54008003040d0542d440c04100c0f034028050910240c1d00e954003000b00e15901c640c4610310400c00c26075408103c0c540d48a4805d80d071031140060b000003075014001c0004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 972534514 1250 972533264 972533273
    0x1c030b01111c05090603240402030f0604051b07030302041e0509010902090d080a02100b0405090a0809033906070c060e041e022106091611121c09 64
    0x40b01181807600c1c40310480d40e0032068240c80c0b5014403224554070031030000800a2042541003083c05202040e20b20507103e65004080005a020440d100e81034150610006100d40ca0250070164000000b0f100c2400b5224169551800c1e90340100d1082c0c021070f030001400c120040910000c8084080e5254100f548a030400780025185032061140c4000d56070041580c0c031059031820140c4c260300750320116855541c60708820107510b03219500524854546410b50150250901d03001703c500c540304001c00b4200a2145a8804040e6040141030301c1d018407441c290380c03001108142440c4042015a1038000a1186007142d810350342240b150400d004c0c4000348100d43c00904e2104c0541c5c2903c459041070b5861b108400041802031080400c040303507030f40e42a00e20030078101c92a0b004040140b40c0501184051801c00205000f0403015909203400101110002e82a01e00494001101409134540902c41401c000302c42c5142200385010340001001c0011130703c040000175400314900200c015024404445141c94 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 972535764 1250 972534514 972534523
    0x12190c0b0405101d0a17010c111915050a0e0d140d05040602070210031d0111121008010504050c090106112a04020310030605130803060f0409051c030b0111 68
    0x103d842440712030a5050000c0704c0c9400321003002c03103000d040003210326510140780c1c580764103522400455510305400072040794407032101081c14100410042c0b0b50303169501c160b120702812400050303812942e860120300e0101040c0c06920b0003074081c10800320b0380e0303407070520304c03d040030345054010003403001720305103403420000306820340c2c880410600703000072580d03681c0c140321010784501c4c140203600400c00c2d51015100d50f003642c04001c1d5881d03a0000340f80400c500042d1103088030113610418048860601c55041030010560f11164441d5201041d58141561000c002d4250340c0241c0c0c1c00c03252504603028006c000d013000c0440c0350043c1110b140c201460080850500d071a000484c540907141c41c010350401d103941491410000221102420444d642c0c40c08103240355841e80715001c2120454188004141d00c80c8007400c000701d1041c2c1102183e032860f1a09030410070b0028403c00c2c0260040c0d01e410309000407880c244814501001c04445807010703900d000c040201119003600d04036050000110441106001c0081d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 972537014 1250 972535764 972535789
    0x150a0b12011202150a03141506040902070f1e0b060a140907180806090c06040501050a0302070c05101107050a0f17030409060f2c040b0612190c0b0405 66
    0x1020140c0c22202800850691010340c1481c4250b0503000511030a410b42c10707402143d06038049042d030030300c03519221040c2c40001003a58400d0789c069014041070000c40007a50091015034420308850841302115940c420390080e21141410340182c2c5e182d150303800e0003ca9011307141c0c003a10848581700301a0400001d00e0300007040c500d040d4001c008840c0000d01c00c502401c00580907080784a50103000f0796a4002542d81c1d90011120000075000d18440a16a030605000b51015250140c40f943d081040c4100118000e4100c1c240a850f1014580d50000d40c5460744945101d04035001da840c0c040c5151021f502d240360a040350321803401014000c0c410030480d03410044034419640fa1460f06030410400c1810ba5181d80216044002001c1c40c1060000f40b5010300304281088441c0c1b08494000079a40040304074002d411009a041180070210000b0700080744c2d542d41940c0490700400710000c00e920a04083d240c10007104201c25000b4114840350188605d440006004248440000f845c0504181c081400d1a0500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 972538264 1250 972537014 972537029
    0x406090201020a020330040609150903202106011203111b0909151b070b07122d05061c08030103150506030a080f09040203150a0b1201 59
    0x144421411a0300c203200040035642c00400b192582d524411304804055003a0341c00700e4038034100c44000141c00ea03682d0b055504990350b0b500c40c464409d151400b050380d8112002104001c0080c2c0b440c000c400921a401034001c0d805142071443d106022920902007402e0748205101714841e031365040658000000112181501c0d4402d00200020b442032609035210300748180b030400280285540000141d4005000d0a038051040310300401da5221819980e448441c148035903d00801c102e4001907000d0b0707501e00c0c0d050802c6043d4102d145840d900752584808050180c9004000907034001c00c0883c02110f80c000d1503c41c0c2d1b5020101c0e9054540e03040c1e41140302004190781c0c805592240001000c0742d031076006c4d80b400240058480118038004e49041e5000390b00901003110f441c1081104903070101661311445102e840003900521f00074070203449044c140d40003044200b148130340401c0440301ca922540042c41c00b901040c0c202d05294040d980402c81c405250b034220343c540309000c0c071425010600318440e650454441 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 972539514 1250 972538264 972538271
    0x10b0901092426010905060427082b06050a0815010302120a080a02030706051803091908030706091406040c0b0c07030803070815060a120b060d15030c06030605090406 73
    0x380c0c0c100c0e5400d81e90825984910f218450000260896160044c610654085a041200009034110000c0721581c40101d244e260003068002c0d000204484000c10800300044e450100090f83d8040d074210751483c820b4480423079521160200450b00300100490090140f81c9c01410800900b140040d884250502c0081c0c0314145080481001d45014800000e00c0ba4109410503a40e02c5a090044e59940c420b500440f50545800000b405e840c030241010800042004051071818070b180742003010070009111a001c5003402d01c0000540c101e410401051074030b102c0c0d9404915684079003403905080e40c14840414880c1c03c4131080100180901c840700c4141c9503210070a50300c800c40a24160702e01900c542000f40990800000d002d5943d400251080c4500da1031440e011080310b1700c1d404d00c07090b401012020300c089158103000d003500d81610713000104250303000f9004a00300404d08190005450103290503414208140400f8805e008046010070003814503420140310640c40c000200340900c41c010b101a159a94 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 972540764 1250 972539514 972539537
    0x807021f11041d04171c05040303320c040e06060a02030c0a0308180106030b0601032d060312080c070b0606090d0605101d06090903070b010b09010924 66
    0x3074006031009480380800402c10300424010b005070f800c1c000da400b17590203210241010440c0365407030105d40001600818074656414610f10400103001701070800c5091544554580c200203070020120800d000f03105086002c0840502c1009220312006004080d0784203040100f800410350054503950062002c3c0c5009903a0b1b191110128114050740245418500070755181e04241580300c1d005500900e246c4040c28058070725500070f1402c8a4407071000401d483c0c0304030b000441c90b40c000d90100d20100b42010003c3c907281d40708140640c0c1141110711081a540e84d40c80d0034818058024018420034540b030905440c81d0030040540c42080c00f0b0300d040204000050b4000407216140c41040c3d0303d51841c042c1648a010039140f60078006003030100d801024008c1a502c0016003080c204117405116422142c1c80d80c80350b104d40d401d104071846d00601d4110144010403071a0000781102c0e1190740244050314050b51198178480c00100440b1003035000c002c03002c81c01d0600d124402141102940c3c1c01000b42026503c166 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 972542014 1250 972540764 972540791
    0x80307020f030309031812100209040b0a0815061c020d06060902030a0e0d0306050d0609020609120d080c030c2706040914060619080406140106030c0807021f 69
    0x6052854210780b8003011040c012455400070207400b0000ea1002c404046161440900603009105c6481e02003d522401207400080e51a41c01000c183c18090008180c0010603c049122100207520807495607006942030111a0021035102d504000c08495050f910021f8010183d034580414034060b1140d00c100d0400e40400595920844c01014042d209640303e00d0000840f20080480d80340e043c043d07004820f2070700a1365202c2d01c100703010b03034030003c04807408a1495142c4030700500c441c0703004a8201500700500c00c503954910701c611803e01c14900040001090248004200386d0780038064038180a424024040e52170084001e43e0388420440c01c2c080070140c0c040b005664988802110150003820000e0b006c03c0664568101c260001c0202000b0001610303030707100380441441444c03c0d06c0886102178908012540c461290789030018064200810a4000c07031b40c8600e0580402e03881100420740c2d8003d201d0846400800443e40402c042c0090306d60f5607070340c0c8050340405103100c0605000c25030b00c200c0c030362405 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 972543264 1250 972542014 972542023
    0x10080a0317060613030b0943090501030c090c0905100f0e1017100305030a0c0c0e19202209061403210901050703110a200405090a08030702 61
    0x100301312030700c054240d89040c86800070800781c4490205014400c4841003a0200592010003c44840000711004001200382d28240b03131818030b96118034226042c0010303400914043d01c0d002c1c6005841402c1c07118a07140c0904129140d041c00c48043c0100c0c10001c0106603901640c52902c0e0f66541020a011034401008460300305a84e1066607204a0713a2146944003540214a21824070340314000030a030b503c0b407030303000030100009110080c0035600030000024032500c50005442c40610400d250003035245c0b42c1003d584c6c035640840b007035070b000500f0300e8032030084803000d00030355007094090701c00342110241d80c0305100c40c58450700090140030f60281500344a042808034800740180703a10701040181d241c0348c1c1102d07c4643d20032003072a032103481061000562a02000100c44110a581030464a041c0308940199600d8128400640c00c3c00040c00180040450a02c2421071003407003000815020819140050303203c00015450340c1c0034518220810280020004491030099080400175440399140e2034100c7c0791 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 972544514 1250 972543264 972543277
    0xe0d17070e130c0f180338070f0f1805040b0f030609030706051f06200a0b22050307060504231f05090d0e040b041410080a03170606 58
    0x4070352034201c3e080d95003503000391000c2d240130140d554450700380d40c2c40d40c80442c0550b00740000f801d8101e48a010b1507448104d00903c03844175a22109401560360740300c5150380301420460380e80d00444c044240580500d98403248403252000d8505041100c00d8003987c01d9000c40780903020b01405140d403a903400680303983c0c9804c544070007140101260030900d01148199103075000041e084031441c0c2000046842441040030414040c490f80284421551401100321061074000300a291040384203921228070810511203601181d004100c80f00a9007007588002c01801142d1609030550785081701361070f0008801008480c840c580001010232562264106000c0d140700605900996a00d070300725083c0c50880100707400d0725020400000c5000503003a049400241c4c3c104032000302140d0030203103400d000c40e8041e480d01114220050000181034031100d010034119250180c002c1c0a0203120820844042101d076100c2001c0c2a40001500100710213a401070001c1a0503030100c7d401000e11000907641c0c1d141c40050329a17 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 972545764 1250 972544514 972544549
    0x1005091020040b130503010c1b0201090e0f100602010c02100e07050406080a050f0307020d03211d1207050607081509040f03030c0e090114010c14010e0d17070e 70
    0x2e8681d07582d00b404040c0c0d8000305820038088180440001d8a00e4184a01400030304a600c800d078103641c0d603034102c000c80303c002901241440250400070441c058080500c91140882d00802c01890030034440000d0001c42a500090444e07040140303582001e60b002c143c5181c1814400c1000c07500c001d0038400f4904101c0281c01880e0014540f4000194002c030001c1d011520b00e0054046c0c40c2c0703514250a04030b4403846480000780d0801c0040280100081c884c155403480e051394800d01d10f514030707402c0c0414800e949038514510302080d500c03044048225428031030240c0c1c0c03070750314446a442d21000750740303181c0c85490090403101801961000600702003120703414021440fa008141c20580c0c501403814a120044401c1c2c2a000240360a050240e0f0398000c1d1380c131a400707410043c01061305030300c0c0003041e8000608240c542030401404511010006525581c0d40e1810f01c064800410f14000c103109207450b040c0140400030030003080d1000081013098440145401040c2440c08105107d03031640030995030600c00f0045075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 972547014 1250 972545764 972545767
    0x6031e06021b0102190e060414130e0124030c090b0d050a03080a0b0f09060609190807150503010b0901051b03030a27020609040506010c17040302031005091020 70
    0x11000700b070660040c00c010a244944031007814034030008542c403500040300c090b0802e2003048140002055428071800e0400001c00040003a03541a2224094442c528202c104580d10742c00c06039140340c541c1c03103402d900300000321785620fa40d0f1660710b4122954000e84581c0040560301d1000030080c0e15800300d170340c001d117030824211001c80341c0d2450000c0007220304565140c00d03581b40848071825403614840616a20800801e440c0d11511a081008815400042940d51146083c8103030380d08804814442c1004008440103060014035190581015014036040a01081010001030103c06402c806403000d812003860b0281e2640401d105848000d41c200028482c588408002c000120031942c00180090300c4c02002040d0401d611a010507041000c000000c1d0302c500180328101107410142e000b6580403005141010a00d82103442d83c04441003a4080f1000f20b000c001001e1040d030030100100521a180d07058200f000745000c9854540300d0105000a80d080e40d2103440301030038404180d090036040b58603600e819 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 972548264 1250 972547014 972547057
    0xe0f0411160c030b24010302031512070f12060b030309010518060906030408090f0102030c2a0a15030b09061c02150f09011106011202011115010e04021306031e0602 72
    0x602d0b84142005c0c02a10b0303124004841d128030352090081d00e0055010304280c52150180c6800c10000c0d21850715012850701c1201000a1380445450000000302820312109100f100c0904081040da01c00e803034440d000341d104101268142c0d91041c220b40c0c462511500c0c82c400c500103d00064010721a620085610070808000d100c01e0200160050010f0724040321a42e845a00d0b1000691b228010100105425002070b003030300c0000b201040d2121140c150101207400c2640d00c2c240021801c00c10f94101410008e101c42e00740c100250548641120800e00b01c0d8840c550785803280020304031524800704c0d4190010510820070454594501c1400014001860030b0385a401d00d1300c0d94401a040101a240000c00b60700c0040307025603000c01c8045c10703a1f8084050410701e28aa800658004032200650465449410080340990025010403070282c403d4035441d0f881c90805004020b001c00600301c24a00e1545440c80801c0010481c541c40c1140510084005401c41c60f42d0810304000c3c0511300801200d0020042c11 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 972549514 1250 972548264 972548281
    0x6060d23150601030e0c0a060f0509060a02161410050f091305100915050402070f0501050901150b0a0c0209060a080a0b0a060609082109100e0f0411160c030b 69
    0x91180c2c00a9030208414180f0010031591100080540781d00140142d82c10300450f80b098510034181d0199041840c940415103001c141d940d48854403040c01030700078010310100c0c00b40c0d0402110041c000e008071085010b00d141c002070107512801c12444107202000039070789002820001541c1802800821500e0100c10504045001d4602103407a101181d40c41c0e400420355000300c1c0301e24160070074441100c1c0c440a00b05010f00000f5400340105036000c001051020000035824068188105640d000108241c0310b2a16001c1013181541c0166203001c80602054410076030110a14807140d4040740c41b03254603201e03030300404c108070010b40012050703000d82c3d9004002e21948a4000e07001d581100410010300f60742d070030201c4052100340221901e03900100c0c14602c118880c22401c2c141080c0c052a40340c603150b00c0f240010a000011100300c0081001500003034040c3c0360000d44813000400a44043c800d14404084182a41c824042c000580441103140030007441040e84c200005540d0248000000d403d200a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 972550764 1250 972549514 972549553
    0xf04050a05010e060409030903020d170408010c081e060907140c030405031006050d08030618090a050d1d0103090609050a05060a06090b0d081e0a170906060d23 70
    0x30f0080c10280802c0800c1181c241072080682807030301036540328103450441c1d0800011081505090790070207080303000b03c076540125100800080803040c00014141c800300d030014002400c000c0210f4009880c2c5440110755500f03604031150b205200300e07a402c0c1c5580d07524030300fa2605140343c0c02c02103c1400118520791880704c000003c02c265141107040b1444c0102884802003622414016560040340d841d928000140c0503002940d0080c4000784601115004903200c070510000c122120100c1c2c3c2d01041595060160520401034150401c0c40c0618070004c040942000010b50054107604165480da0101c040c0486c540c03040c1142507022054503184041b031300b4140c2e80c50000b512002c202c00d25021300092001f08911a4012405020304059101070194a828403140c12040c642c2c078039100a80d01280b25001b400c2c00a000542c0c064a905541c00c9400e00c200e140d030800208801c030f0307550180c0144002a5181078900010a40c480c81e072100019141c03440d20750295013286a02d1007072240c2d02201040191010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 972552014 1250 972550764 972550769
    0x1709090a052e0e060402040b120c07050a060c080906161d09010311090c0304050c01030504060e25080f06060f0102121c0e06040f0b07030e1203040501060602070303020304140f04050a0501 82
    0x9100303403c2e075110036042104a109505c660b90b03040c072041080e030380c1146400503c181d0107400c915480d0304000140e00c40c45d0610300c04d014111a4180c0e584100031100da0441d032400d80081108008010910703100f117040741c080c0c0850001c98103001c10a0900b0815040744130704000c66a82c064005411941c0d82d00d8000908231041c2030b86480790803110300042045110105803441250408014995040501d0040d0014038000d041540c1e6180c450801e03445104d4100415050040e203101d0180b05094000107011307040e07280d034200c0f411030340082d0181c6240d0080000e22079048081201c080140d10b04240050340760050785078a500f400800880c00c12050303655400d621b04151b00b1203005010003100e00031855250b49040740d00a10054005d400e01011401c96800d080c0d001e001c41c00c000401c65161a5894a042007200985851140000170401013040030700904008000b00c2c001880f09905540e000303904d0b401170740240824a00c81c1100315001c0d81e202d80751209420809403041001d400d2001121002c1d04090 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 972553264 1250 972552014 972552029
    0x6150712030605060a020304050d030e10120e030901141b1203010603180f0312020412080910030c05030703020c03040f1d0106021617010212070c1709090a052e 70
    0x350002800742441400c9405c400d9035540510b16240c2024100099052040410f40420041d16007424041d1254249002d00d0b07a110781350340c0c21090f44402ca54080d940d104105100c940c10900945038166004400c040a0a550352041d54803001c11a0b000802d20a0286512a49100d5441600c204a0b0342d87c000f181604c01c10780e07040c0003015080b80d410408503241d500003002c0c3d85038181403d0101c0d02c0307501f1411031286491005403502c0d03503d103c3c0354141e0320552011b40d9038440000300300c0e03e24a410314815000500d10b060038060302c11100c2c0e0141c03903400014a11801c0c117400013131600002c0d1080c0304a0b070141c1400e040d803062042e100c0d28080800e000001c10880c906169500204400b40000b9122404140500d2500ba40c9420820351114220040c41a02d0180d90240003044c1c9460b40003000d02d22485565a070426111801c1c10b1001410341210721035a180d800802c1491080e440f40001250b110300102c0c0003140d142c642200b0620a00004c01c0c801442407054540c0030500502034103240c0c1142d044 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 972554514 1250 972553264 972553271
    0x30801080d0906090e0402010e040c0905011701050108191410030302210a050c030f0307171b0f180a06020303100621090503071704060813020306010e0615071203 71
    0x34820540b07400c0700c0b5002e40b0001c1207a40c44200459982c180b01c00e541320348103143c25400714400801090644540c0308590b00407848401042c0055640304035504c85014034801da2004551411001030020140604484103400c540401540c50001a800c00c3c001ea41c54800d910020f0319100701b41241042207804201e0043c0a03682e880d400003804082c400720180e0a080d00c4a10b030101c50003080c0c803030344e0181544c1d20990005120ba144640c914a000d14414000c0e51110902003d1000308050313107181c024000441e0801d55007094405102070400d41e12035a6100c01d0042c0e84640103880c40c1d1640c4c4060700b0aa5000c4200b000104019901002660061944061016465407140c0e01500d1070110b0191290742c80020442441d4001555000f0003000c5004c2c00550f0302c0e01c501d580301c00e8074400094100e001c3c018000101040001c1c4c1c404412644460440340c0c1413412107055001079218174040c0b1030724a0000d90ba002044541d40c940c08441803031502c000029607100c1d0f242c0740450300c0050400c0d400707000c00e18 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 972555764 1250 972554514 972554533
    0x603070f0c0f12120504050c10110f0a050106050108010b0f030a0209121f0b0d08070303200c0c040204271e0912020c10050309030f1615111803030c070303080108 71
    0x1c1c00d011702401a45d000025001d581c500c00700340038510714415a5401044404030314020910001d01c44001102005009001c505030b550800d04d00b52001c030741c0424108032255004016450616050701c1070300b00f560382029980c1e202e05a03000c01a00a0804003588610a00301c81c00142200055805000b1202c0c103801c0350350080d0351102d40c00c40b030000c80e440d03030880f403c1801040001e5484004100d050710900380000c4040e00b0b060b00d003550a1051505940c084e40000703c201300e040c01005075241841046030294903043c1001042c410410001d41c111076415080c0404c00508038054002070003508904075007071419a26695a48060301da4110181c1c3c0040b282807812181c01d02c0415807440d80354020b401810022580c03c8210341550006001507001d0100380b21841020725038000030040350181c504820aa0002c43c1024510000d803152403241d030310f00d04085070340070f000c2030300940e000c0300301c10300c0450f07411840b10300400e0440c40f071401e107a45030340281000442050340040886060350380364000c5032030500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 972557014 1250 972555764 972555797
    0xa0f031b0f0e040e060405030d0f020301061e03091e021e010e100c0b04030f02061302100c0f020405040503040609141e0d0c0605180a050603070f0c0f12 67
    0xc4110311000041600c104120424002e82d03a82003060340140001400403001c0349514101682520b04803900e410000b020200d089040c000c0180ea00241c940843c1745500d80760002d0000f550f0500441c0c65403070700e0802c030b07a21140240d200b107030410b81050326001c5580010802a240400503801248913582000a5060489448103d00c0c1d1600041c0c5401060300f1601e010440c0a4071401c1140301002095844180060484800c0d6401769100b40ca034030030080c406100c041d061940040c0307850248041c02d503040c800740c0d90704910050f400107036040c6400c818100e81058400d00d030007000c000c0c1d0000d062601f0301c810808004010811603200382e46520076544c44400c2c000390444241c0c1c00603401076800d0000c6400707440b003050032001418000c0004511003030542e210309420500b50300120101d40081000d50a9000e10304900d0701d9940c003150070b1490b140c10800025140c0c0005000601001610050644140e006190801e041381d0040240c001c040c09a00d44450000d002041442c0000e501c00c600011340e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 972558264 1250 972557014 972557051
    0x91805060f0603091908030a1d061b040e010f051906080a0b0a031a060316030309031101090f090204050118030503030f1510030509060c1207030b0310020a0f03 70
    0x48000500340c54040a81c034041205a0b0405440310402d402418040f95060030309440401c255403007a040d5a4903850995242e000312954a1505002054410b00000c1d2014020401d5a0f00ca00303444011300512401513803c002902554018031440ca16040020590280d071801d580c00f00c49080303caa00080c034880e418580d501c100e602c101400f2a08032400304542018541003076003c0103010b811205201d64945401f0140040302e640100460011814040d070b81c05d0501244181100b0441c001c1959450f65170001d2030f000c1d131440045d0428107282605030035680310759110700060480020006610340c481c203014000f50f00c01c0c810a800f1922041c03040000100703016031441202c0d00075024504595414074413010a01d001001d91180c1c3c0e540c0540050326558190313451024070025580059980380046500d8500400507200ca45000c100b400711000310440c0390084c550000452801240c490b40741400703c4e01d00801e52450509150020074800e506a80c0040c885c0395a640302d1381c2c1400322070354070548884003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 972559514 1250 972558264 972558271
    0x181b0c060114041b05120901050910050a06051f0237030207030c091a030f2a10080f07030603030207090b01090b0a03020c1b01020706210507091805 65
    0x25040000100402c011101c0b04040540c0040c1010078000e42042d00d001036000034000000100b140400c294800c4080c505100390302240c01d6000300301a003010300400f82c6d10068004140c1e00561200001840b011a0743c1041000f00000340200c610134010f07080d03545500c00500401300041c0b0901440e6402d0300c840383c01d6004403401010441c11b1094420000c044a4440404194198481d0314400000a402c1a81642c01005a80d400052210402c94201c80d148800c800c001c0c86944126803a005071b040c041400018908848020141141e0421200400e45844543d00e0703800b692000c2070b4190180c00c416081c1c0304948201d010030f00c55841c2401641120061300010340140e001c1e110501803444503031320048030300c076050401c40380b0300d03648106079040c560010350450b00081c2c011418070100b20040040d03009442c0c607401c500c8854142840001e5071510180b00701403c00582c5201c04c0d04548820f0050768000d00305c48424000780c81d024101a20800305071158034001d4143d01400c1034800440e1045900 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 972560764 1250 972559514 972559537
    0xf030f07091203032f1306030621031101090326040b0103061503050106030f12090e06060d090602070c06080c0a021005071b0c050906040c1e0905181b 66
    0x941e40c45480072070040210b040e840d0b0f04e0070046010502d019460702d0b03030b04d41c4c0380c0e8405d191181d45a410000601d030340781c07240d8412818181040c106001420549070254420410304c40c4040403442c1d00e0400301e941d03201c9011141200d51a001d4804d05040d40300036500008050003a00000003142400c6600d1001c2e01140c02411440f0190b00500020346160020706842c04a0055214000d460f03444160845659a100711060001110964100980d190256080b0300c40c0342800400903282c80810491140e0003407180e481414000394210381c170700703140c2c0c00048811380100c01103484200a280c10702072140035005807404106c00d2000078203000d4009048402c1b0090542c054120441c0c00f61400c80602406000c0c0ba05100349200301510b880c16440c0c4442c070503401942100c1c0130301e04c0c00d800e1082c0c41740c01800c0b450243e410100d8044101e50418201c4110500303c04c1a000ca000360002c0440d075402d000d80201c0d034031500742c0203007045410507100a2070099a60f0540704440307a29524426455105810801c107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 972562014 1250 972560764 972560789
    0x3160303080414011d03030a05060d03050f09131b030e061005010309110405190c0e15030415020c07031b12030f03060f0b041701050403020316020d06020f030f0709 72
    0x600081c44580480f16a0711204000300b504101441052540604030b184000310303903c00700030444401658003880750040016503882030700110540f0018014403846c0124001581c002503010113540702c00ea455889841c0309103003040220804a901c1420550015405d00081c0c240f60318544a403d001c80e40a00800043ca100708500c0c0ca0b200054018085215081c5c0d0500b48200d40e54006864900542384078005000e10107604214010700b400c201c4205003501820842400812152911981c0141e00109040a841c1c4d0b102d66552612442c0385805c14010540c2c1c5001003001c0702d50320303400034843e41a60f205038100c4d103040ca030804c40c441407007000d840f441c0b442d02551840c3d4400b182c040c8480ba24005414500420041c0c1c9403141c0440f940c0c1e42c1e60100c0c003d5800014100207a41d0f110036203501e4041100d00034807241c24503480080d540c0c062024816980344440303840f5003c41da540c01008890552020b0250745440d003074620202c00d03030400c486812504c4e8440b800225518402d0030100e00750f468065124 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 972563264 1250 972562014 972562021
    0x105060d0c0909050a05070206010e0106020703170c0109061e0e070509070216080c122a03163b01090c0302040509040b0601140901140d060e150316030308 68
    0x540150090075040c5050141c4202c0101e1050814000d151081102d1500030440b4209a80000d140480580c018019a10000010304c403895003c03469200701e80d001100d0402c0c24509883c2007045225401c0030400c84d41c41c1800d64810044240c02002d91100001d0601e0410309008400c4002c2c0d6604000d16404c980010030244094580440c200c1d800c0742c6140304440b0b51003a801920460b000180c0c000320015880104146128030b4149034402140140a019110f08160341d0244400b2502040c1050341020014a480d21151008c01c01c440e005824242d000c0348036a039070f0031a12003111a003c1c544d280150b42e040141d0070311190400584c5c0c2008103100103080380e0300e040c000d0401480b5003076001c0e0806808100000381c07a40d80b1501a07014034091015024541820340c0098803001409508001c203040600841406030b07008014141e0f0f094144001550716115003a10f000288491b41007c0b901c0c0034220144582c1c5c41a10040d16071001c400c0c2d00715144a218003840800b50b00c4503100050000310783c4c0001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 972564514 1250 972563264 972563287
    0x81e1324050f032205010f1107080a0c0302100c03020309070609080327040c02011d06071b15020c03030103061103060f0d050c2119050a0215040f0f050f0306010506 72
    0xa540c801d08044d1801107038a00900c5502d91496006401e648507074407410324445030031086c42151820103240f4410b5251400c190740310180e50180c0840c4806010040d00782500381030080c03040307a07552034980c0020080851032400c0a4029081039912540300d1140240100d115405554101c007510b100c28001c50500f81c0741d81111139815040641400c0300400f41c90b03a010240c0f19030140c081a808a44c00102e128548030020310102000ca580344049130b88107100780000c481c0c1050043e8134034011340555444c801a1400e101c1041c60400c01004061031000030300c01b0300b0050100196040e00c3c829001809001d454042440490100317031491035200b070044183c20400e20300340d004803810038401c40559030048022000500c081800d051000348114800c0d400c2d030758551007402a1a8a080d8806c07440d06120700503152140da4140e0400028050004002641062401d04090742d00030a0301900007d00783d91200b010440304460f910441e070007200c1e01040540079281c0031400c10305903600501a0742c00c0c0b80a8404 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 972565764 1250 972564514 972564517
    0xf041e050a0b1818012d05010e030102070f111801030c09091407030803100b0f0406050a05130326030613230c07052404081e1324050f 59
    0x500e019080401100b10096200c51824604c0300f41c11665200b800d40c501741000019040320140559010004907040700c10701c030410781c081d082d01c10030b10f85540b00425280100b4028402c400010342906a030302d00792001c00c9100c8490604a210559400625030880940c8100c221400c4c00000c00036440407501348801c02c6182d01c540441c90203070300c052030341044c0c4015090408076560416901c0803030000400030302060500b1100010942094854070b00001250b0300c8000740214003a03241040000580d0645403031007441505c0c083c080e0900080748150340c27071901700011030385881440806407940c80701044040c1004c041c0c84c170035900a4400701c1c5074151a89048002d0070310580800c2d08514901c101c045110003024a0381c41568520a0156600c246092807403078440307440f40300708210036010420480b81a07561300032038026030f000c03003060345640c40c04461001c5581c11151003095818007007801640803003484c4041d411500011072140700640e6590001034422843c003020b101241d0300700190900c500d403840 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 972567014 1250 972565764 972565777
    0x30c06030c0c08071e023304030c05040c110609150c0306030a12140a1224090216060504050c0117060105072003030a0906171e0712020f041e050a0b 65
    0x50b00300111400700c0e1b0001d20f506005801c011112140340820314051000a166090307403107010321019042034034590744d00000d03c02c5401414041c80c1c8510141a90320301465000c28812020401d66015107015400c1c0741e030312482d00c0b003040c08034442d004c04a41c3d43d110300d004503030140c4c902a010700344003406a202c403401400e030201030408110000801121800c040001340081907402d0340d80141e21605101c182007990080c0382102c0101080f000011641a81015400200d8502100168480b442070f408203124030b000407000340580e0f0401c01007204115002c01c0c0003a0641090304c900551b6001c07004425100039044542a0100d842000303503078041410352644200395540c200940b07007011090f0000c030f825074012030894000301c0c04515003072009980140d01480e04044d8006442e15600d0300c0b02d0107000064810356031403080c45091001c41c600e2071040f0594041d00b820315100f95901c0c2c48442120b43c15a006101d0050400b828521190229042c132072454110b0350002c1485580c03c0c07c0c00c2c8003010513800403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 972568264 1250 972567014 972567053
    0x703050919060c0b0a050c030708100306020403111c02010503013503190e01140c0f0d0e0f0d080f031e010e01030c14031e07030c030c06030c0c0807 65
    0x340c00c01c0502414000448003801d1030b42c0c0e640c60110f066280403409040003a040c412042e040100300099007042c002542e52014141c5031044403512809501800e10905400280a46000280c08418480920070802001500b0340302c0089640c02034801c1c2c14042c0405900070300107403041004002440c07080c20780641d002e0039070f40f103a030107220ba00c0c61140c0c44a000c540440c040c0c0c0c01c0854070051400e18200900608142400d0400024100700002090601c1c0c228001c8d130802070200321200c91103801c1140d4a0b000b12910b00711070000c40346410103030000702d41c07542c10391103900414041035160a01514881d802540229800e0621803100d910f11181e81005140a403514001c00d007a54049542c11b0341d003030090043c1c507400003072035055080000550780250000e031034032000d4050610407514001803c02d0007010341810341d058102400b0141d41042402c0d80081c1142110400100520000c00011412a0714584080000d50440c01081d503a500d80410050064082070100c1d50110f003a0704401241041c02 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 972569514 1250 972568264 972568279
    0xc030607030b01270603141605030714161709030c060714100b0310050c07060f0204080d020f06010f0b160221010207060518030a030f0f06030302030705071a07030509 73
    0x880c130a0f48130300b40410302c03044c561118113601000f00c0d0740c040c8201420b182402003070046510b49030110001d10003111609404101c40040020591881900030f40100e5032007240139951803280303940c00210030301d07800c200344d45203c6a0401d540c0c5140603101114100340d070140180024a02c41d07000c0044980201c207040d5012005503c0c480c94803403052100b00d0038995140d130001000c05c5003000f0300d480e1000441586000d035151100b8044010200e0083c0d0701d41c16440080803030300399404040d000181c003d0380e018400c68400c1842d540d800365004118448544003041c2201c170f09a03600d10b0541070004951040300740f00002003090400b50b20166041c0c1d4543c60010781850080052055403640b012110079510003a0796020070301e00200607060150b240c21030f1400c00c0481c00c0b100c00f441d00319100d209441c4601c050560740c601010840c09103030072000e01c410030a45d041080540d02d0030302a4483d0301031b0000b20751328051000003080018078440d000b030000f05440781c194180b0b15a40e03000e607030b20b501840100364403400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 972570764 1250 972569514 972569537
    0x150720030405040207030206181b09061801080a0b0c0f070f0602041d16020105070503060f15030c070c06090308160501091b08010c020c06030a110f070b01170c030607030b01 76
    0x2c1c3c40c0028409a4840d0380103114500d0400107694a46030580820300454010410294a50280d0211b500f040e0400300e8030405292280302c000b801c50700322040d80340c441c02d00c110300005810a0104e0213520f05800b4020080d40c9560740e000c1d80714584205090714496070b009100d0345021070b2080005801040c403801c0010320341525440320a0b0880036091900354000e4508080241d460034000c10300755688040e00007805a810101400f80190100070809400703090741e0310065051740e4840400e40041040303040541e66030b050a440c81211a4002c4000340c9000c041d2840000d0210b1184001c0c50480307401c40211401c0c0000c410800100300354a4405071a41d40d29202c00c3c00108007883d44da100c2d07440c2008201003102c0e1410090900351102400704801b95004003145904940b106400c5a5003c40f94100000d0f440032020305140070790042e2910000216404610313942040005082d1606803880090602908980052199510001030340c000d50103400c070101048215000f03070000181d004050406403113050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 972572014 1250 972570764 972570769
    0x503060d150c0e18040212390109060203040504091119090b0d08041404060b0a0305071b02030d210c030f050106080906011211041d150720030405 64
    0x2055035040204555031800501c400d160880032034501d000c816260300140c0c00f484c5004c1c9490000003003000c2d02038202e4180c00c4203228003d12401c00700010341030880040a81e900c4610318110a83c1e501c0d1940c000c40211a48031390f60003203491314115a019401149041c0c00d040a10014120b80304044545000316035a0324442e55401510b007642c09401040e103c81c0038a001150020341d800445030390b0007400d103141c9010108032080200c0b02511110325036041c47c042540045801800700d948072aa601c1c0b004200f20003869810303000035005055950301c69030f43c4503803081c9090b843d81d110080254140c1c06100540f0b0218000d00444258182a109111580590718002400d580d107a07245040000d5442c2e140c1c0c01c8008a80c4076841c050416460440c1036442c1a580440c2e490780180036921446404084480411061658000c40c00002a00034010700300c00500c49a07808002c400341300307503c1c0208016822070141e8002d00c640304164655800c560304943c0382a548243e44407100003103c2d8003041001103802d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 972573264 1250 972572014 972572033
    0x4031b0209041103101503230706051308281403130e011401200316060f0f09081e1e0309060c041a03070507060501030c080d030207020d030503060d 65
    0x201e000b1500580c440d4004400c040c1804401805e041040e490601403007407414a500000d4243d907400144011047d40e03840c241c101c00c04540700c022103603101c0c8507404141743e83e104d800742c1400d000303031000c049a068503084d4040d2640114451942031400f61585503041c550050104070482d401030b07044105a222528a850940d4403014a0745507080100388100320040c61030400c0e50060401115100500503c04002007010090200084080c8801051100002d41c1801142c010001301039004800015924004020788059204508454039110b41c9000203030207801115038583c3d000c0c0d07138245844103018241107c002c0700f807000e5a0414003480040c3c2c141d21102c0d01814a4580441c0f8180c607490300180440c41e06400429840c001441800100480072540b024a0000103c02034015140c0d511040111030600501c4070180106007848000014008290070741000e0346c40d20407e0344c54400b00d44400303a081e44190720f8002e401161003c0312002081c0316802654100c8070082c040c0301c19109545410002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 972574514 1250 972573264 972573271
    0x51b0d0c0603020a09050108060f0103050c0c01060312140a080c03070c05010908031006050403050a110409120c1509020303090f0d050a050f06060109083708070b0f010b0304031b0209 80
    0x70036400269907a44c0c907007250300030b80106824605941c0a103801000304407a001e000f117106044c9610303400814494500001542d135003d07800c1d4000c120040d681c0c148110f0750803400001e04003203400321542c0c41c40b1460950840c0d075070710a6516080c034551110400301005500c014002001c0222104894001980038001c1d4088e141c0030705080381c1c4a0a0545180304444400c1d44001c062220400c000c100160011a00d00b035400d4000b411120781c41d0618004c030f80a0210b00303c001302000c200401900c001608682ca4408407401440301c038054502c3d83d040ca5046502180303001e54581d0086c009501145032400044140000107400760750341c00b983d50b982500d80600240103c4594000703c1910040507020024598403e409190801d05e00d03280074042078480e100000704c00c0e69041c046440a0305040218500ca240c50500c00c050440c084190800c905990455042196030824803c089661180c08032052410395800031900d519685803584c05803520b00001c604800c48010440000c000b40c0d4840150030321 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 972575764 1250 972574514 972574517
    0xc0305090d08070b0a02042607151d0402090d060e0a06110a0f0e010c030e01020718060521070608040c0905010e160f0e100314070e120703051b0d0c06 66
    0x100c400b81131610b060404001084440e6080c41031004019917004241c8911000c520000c5c03015071807210081c50b0307081845540140f040c3d08003015803500d1040e8041c1d08014203000a81e50350804c40d00000400c0240d100340705026602c40040c0030b0b06400301d40146e00c08510704078202d040716850040d554400c0d043c1d442007011000980000301b03407031080c1c2e500010500840300c0185400201506040c0003e13241d07040159001c4c1c1081035204010360281d00802203c5c024041103043d100040b510203c4080150090780a403501825040c2d0700e4a050f0641d822000001d20b00d200007801c0c216091400484400c0300042060b03404040711b00c800101c0000f5441818080c2c210020344800d14500a011420f85100c14401e040170400d003864076800c0f10b82c0c810400300015804441c0c010300b001180a04a015190301c1e010b04414001000911a05075000303901280c421405a80083c0c02e481c40c0801c1c9501c40049210240a40c0c1003200d0000c2200313007800704000201002054444901025181c035a440c400e41c0c0c001c4030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 972577014 1250 972575764 972575767
    0x100c050405090a0c050d0c11060907150e060406030203070522090605121e010e010609090302070510081302011b0b10080318090a0b030a11010305180c010c0305090d08 73
    0x305908200d84825840907a10b00c00b44149803003048000e09501c9186c041903102a951000103140c41c1c4584285102407001c4d42c1100c0007420b000b040300b41c95090510602c0c15481c3c0b50451a1103003406000c22445c1400014215070034689000c0e01503020f07500081148007007050070020180c028a1229014044503a00b4916182880c2440c40400844805030000d5101d40d8186000c0020300200041240113540c00c14403406440340d04030000d40c0540751091a002c065400e0044c080f80301e085561041000324065401c68003015039030800d1080903601c0c80d40c0c04000803049000920018912660b100f1828410314040494103098010021180074404046941c0000e07079042c0503006602c07080d10005003503401c014601c2c00c200303a02021072119910b6041c80c0600c0000e0300098054150341d015641410019054401803691850b050810100340c0441c0e6000c82c4c03070b21020401c04105401e4403154070300c1c00d0004025400c0c40b6401510055040602181044020004c2003481d80f1180041c01c0c95501c1116030b81e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 972578264 1250 972577014 972577019
    0x60503070e060405030a150f14091e03191b03080a150506161523130309171c11010608010b01051617030c0307170114060a02100c0504 59
    0x40110025008071441100180300502aa580100342440031a502102c1c210003140c14040007009008101d2109003854074220184143c141020b0b01030b44240400e40a0361088490020381c56a6189203260b1034401d0f900500c04455402c074200740c0400300701c0711801c041300d0845d030910300d100d080340b05418200d0010314000c00703200700d9822500a400c400880140822841420440071680c01d014000c4c1d0680e4000ca508642d200342301659442c100c0c404486141804081418241302402003101548280ca011450700010200600400c0b51141a941541c1d42600c8501d45400e842c28008590100d175094081d80b01c00351030f001484910091100e40e240c40e0080700101088059003150400c0d4840c2680e64103014101d007540c1c4c1d1040489420168140c1400f12107403540c00c0c043c15035240b050b02c030012800300009000841c00000d01440c4108400c2d603414101461042405040581c28892070360171203404d444080709803a10b00c000d48040c5c110340c4101d843d60303031600944009031000402400041240050103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 972579514 1250 972578264 972578267
    0x1509020f03060103152d0501080d110607030e16150e27091203040b0f0108010c09030308070e0405010e060415120809060708070b250c0f050705030706050307 69
    0x1031140325081100501520341c55034940c0007070404000944402640d869a01501c01511102d485034020031040c10728001c080440b95207802024280543c1090740b0070f139500a200c95100d070000c405084c0300000546103540b1481019400b61004d54413225085c01080b40050381299044400e8000b814640c0182c1c0c41403004500c0503100001013000c550041c554100c9010108521902060301c0c01d0250100c14002d5581e9107070a4180000140c1100410800005100034410003a0b041806420403480c050b103070780d03600c803209401c0321010f050440114907150810000700b8001d02581d503000700e850905e041c825503020000390407244260040d074040c4c0100d40503c00582070902c070301c08103480d50a6040300b01a0412843d0311380780c83c43e004000d24910000403140420385503001992203007075102c0f00041c0c66001e1450001d43c841002c503011840c01d0b411000c041440e4180414800b524256502c031010749581c10b8032280306070240c0343c1066506101d40403000610391010020300c0002c00960340e43e15182c0c1806c800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 972580764 1250 972579514 972579529
    0x2100e0415090c0203070c0302090721060e07210911031906241205160905191503080c2805071508190b030303072003070809060d09150902 61
    0x240085610500c01d280000d00b00072047d2003900c3d0126032413103241d070351140100c549880e10310118030312104490521744101c1d100d80040d81070b6040381c4064129551130860841d2220080614078191b40784011447c0e0300840740d607101c2c1203540e0007408101d5910911001191910301948004c091444070302200405001d1140b10350000d8010304d5007807803034040003a140300441c90305134011110140605080b8504001003003001c14441c80c690b070104070f003042e519002c2c1d20040400300ca003580500010030030307042a45002d21035104042951418100850f00319111842c0540054608040e90312a00a11000c245074000c154581181c4607201d88800911a150960a00d94194010203419010f141401e141d5a04001031a501003c418030322081001d004031f680d0044d0242440098044c0030000038000300ba613011a00c28004400080c001307802e0300500c65505d54070700c00c030000a00751b17a1041c40440715a2030104000c021803030151001146661040e150340c1c070f0f040c074281c0e541c0d16039a558a0b82c0c0c0f41182840c10 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 972582014 1250 972580764 972580781
    0x9070b190914061c0e0625030e0303241504050a12030f050304050a020d080a020120070f0c230a080a050c06090a0b0408010c03061e0302100e041509 65
    0x20350b0319241e440400c0031400034003c04807680080c010783c06080c21002c21981c04407034041c80704011581903042031a50364961541ea441d0710303001c584010f6940c6c901280640502c4060446030030095145585203100c04440700038410180200301114103805410350b80e11508110a800030140303c507543c0c0d1801d02000b01c0400b06070312811820442e1764020f40404c2e040310100e20343da42d060901ca0395980d11890160b0800c80e1080c4001c3d0702203c506218001c4c450104060064070a4a0300200522488015030403d66012146419031458042080744009030301c0c00b04801080388242c801c0c1c80c120b500c4041015200d1905280d83d142070030342da00c0f0075180d4500301c03200000429195019007141c04c25516829100e8102d204820300840001642c0e00d41921120700c148010315400301810344441c0c0703403c1294060f10011210500007401c0c1400818002040300300450380600806070308034190300c0d680c00c1c024801d500030380c450280181c20700074200d641c542d030191361442000b00b400e01203a94103080c008022102d00382c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 972583264 1250 972582014 972582029
    0x121f0807031e031b0c140a140f0315071d060c0c041109040c080a0507030b03060f0a06090c02030a1805060405040b1c0b04050c0f10030509070b1909 65
    0x5840800204103080703501800140e020041d04092400c504080d5108128440d1450300700c400c42407100140441451744a05076035810729001d00302e034210b100f0410100941c1c0540309140a040440412a10700740400c5070308084054141c1d09981d5202c9941c901305d250845032a0042448564003260580084d25140d83c04401101c1c081c1c00d0400c03e4560f5581d4a10004c00903001c0c075940c507800341003881d0020583d071000314000d01c00e020403d2140d0005225038000c1c0e92583e2014181001700d1242c40c000d008000d4610805001030070981e95440c01c03030607a500003402240d40c80f5036880020400d1216070082503000c0800707400440da01c10401d10020710300f00d181d468902c0340307901c022428850303581c4035002c071000c844d812a00800c1c100c0e01c0c0d00005036414805013a1012041140030031104204850200612660181d0192170324600c09200b8000500c80200a05910058004007040010b020b94412038220000c081215016911a000c82c09280d0261865401071005004130b005590303405040170006c0c1904 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 972584514 1250 972583264 972583273
    0x6010e0a021c05100302100201020a14090609010c030e1521010f0b0d0212070c0b0c0c0c0d061e020319060b040501050703051c0b0405090307150e03121f08 68
    0x280c80d51404980201809201c000d5100e2004c40c020760204410318010319001041411610304d000006030003580f100400b00c01281c01c00d040040e0461000041e03600030070000d0200c0f4035059900e00111116589682c08800303100d10400d0850064031440c81d8110503801c007190650740c80342d0707000c000703551980103450302d00c51002c03068014064074420300c05910403648002c508a40b01c1c00c038400e4010103230241c6112141c0c03c4541c0010486029807000e1041180c0740101c00340d501640301e250305643c152081c485a41119805100304125030b0820300c500300e296a000c0c802c001180d00350b10b44800c3c4804404407180d011280c01000740300702c0754201e03120080c45240203030040281314078040c4201030702e0190780300f12814420049590007d044c0a0011140c203145400c0c14240e0130206d071602d0314000d040c0403009a000754500340c00102040c100008584807a82c10201c039940b40c3e001c16070400007078000e03d00580d00e180014000031085940c2c0e80ca6850255100184202c2000009540f0304007407540c1d54800840d81e440b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 972585764 1250 972584514 972584527
    0x5060708250804150c090b0c01022b0e0f0604021c0204090b0703060501110709020310080703080a0e040218040911030a0305070204050705070b07051608040929130b030f060906010e0a02 81
    0x400150b00007c071100c0d28480c544032019808500e0090040822131490340c06202069110103801c2042c0704207505804108000f031201c400c40305170340d030410b0b0300c401d1213a070340071001041c00b62506c07040702d0a00c808591000e5040200942c080340c16202080f504440c041c44480a1101e03450b058014400540fa00b81303010301441035034400480d5507220900c07800602e5907000000c9082b01850000764809000305004540b002d6940c6d182c0684290f10030090940080d0710b210924410749054021660410405e2002d281040403980c20803004018000c41200e034040e10300e81d4001c86440034805d62000900949881da1100001d00520064904c01030591080240400c5090300042d60300300040d42103015882d1054503074600c100c04c0c04000081c03603c05495614007041c005002016a00100e490310300c80d035410048144601604c6036580c2440103010707405014100c6900600306140d0102485182c01000c4429901451038900d0804c034042e00c5100c16030704100014441a121050050340052150304110702e040c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 972587014 1250 972585764 972585767
    0x20409060803031e160c060b0a080a0c0905190b120d030605030c0619052203140f0706050f090414040c05030d050c0307060c0c060c030b130905060708250804150c 71
    0x5c92403107042d001e211100070113406100c01c66014105c00d41028007040402034441c000c0e140d072032401c3c1d903044468030000304000c120041a8000d183c056511a41c0c07600248170300490380701c00382c5910305855420075011100d80c011081b04000c0c0482102e104c2c0c50010b1202d040170f0505041440d981100d6009070410480180080c8030340405008001c924500f00d52608a040d81101c0301d03c90b02d1541100c0c0b51441ca00100501255032428680303441040104c03071201140f50103a60315203000c0c0c070840707020440034440205503844441c02001001c2d401000000c0c0c00145090103030a103102524195120042000300348110b040030064200b040b03419090560801145400b9581d0b07d100d1000010441500d8081080411340160702c0c030440654484c90a0003a1140c15200400805100b0052403040d140e110710308504165070311480101c00c1e04040039099955400b0004c0d00c03682800b07030500800030707044c45445102c4462030300c034007403840b00c01d40c0c60b00007a0509080ca00344904881c08c40441e02e44c5003010703040744d99 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 972588264 1250 972587014 972587041
    0x9060403020f121002120115020c01120204090f0902040b0105122a1c05060f090c0c070305070303030b011d06090904020112020a03090c09051b030901020409060803031e 74
    0x80340e04480320789000381c1d042c000c00c3c140c01000414541520030900d1281c1c603288540c014014a0f4081c804440c40d0740e0ba45c2e00b801911002d080c00580250f04025158402944109500220300a44810242c0350641e2280031204440d00710036840e0b025a0f984106100f18a8280950740407c031007407805600f4506001c0300410100300150038040318080c0281075516160b0f503641d030407101d022100e00e025190b41051000340c1401940750000d2114904d0280020260f14200b008070700307460000b80500c4056910a86101b1580d4000301015000d48542200080000d20030801c4801451007540d01154000c42400058241c01401290380320b0303c40074800c2d9403015100c22060302c90036202200d0444c0076868900060384c2c0b03407410f000400300040c000600d240542e90144c0003004664469500c020300c1a0707881150404407a401ea956034019010804030580a40e08180038581011030f5170001450f15039038080d6070003250300660016901c0d81011003000720010f18221201c0d641e00c04103100303440c14070f081d0300d03040319a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 972589514 1250 972588264 972588269
    0xf030f0a030203270307230d0b04051204082d03130e1b0f07020a051c050606030607023301090605030d0c050c130e031b06090d0206060d061e0b15090604 67
    0x880c0071018090301f403240101e0205502c0700c0240c80c4401c20041800c0401c01540100d506503994829103800c880c080200500302ca0840c0c40c140d016100380312a00100c094820308100b0140b07020b01d41961555070510782440140f102c10711076030400150300e00d00605441c01c040d0042003040400520340c0c040c1c140240c60303400ca9203400c111600c0c2c943d480c221840024040025504003035044101c1a041c03009170b0b40b00908240030707640200c048981d44d80d1807000305691200c007201c0c1e000042e000b0101ca40d400e8a1040c48c00360b80340c0d1b4440746d4031445070a0340c51003c04910b005d0380103600480c1c86500401c0541020b101d80080c6806510341003000c1051502c400366038010b02031b040da014164140e030305103c01c00c05502c501502c0380c0381019250f0b0b401c02c100315400c009960304c2d0101403e02075440896080b0313600003010604008290094646946c5030ba041040c0120310301d0098596035200c2e0541c0c0c0c00100341101d5020100e49041c2d0000341c4c0201c01003400f1806a40c044521a400c004002103036450f0b03141d0703090350f08 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 972590764 1250 972589514 972589529
    0xe0307021002010e0709061e12080319050403050706181703060f031b101d040209121504030806100909020708071b0e061e0f030f0a030203270307 64
    0x101d66031403001c100e00611105882098501400d00c001c00e0900d1150490407c0721030034480c5800b4100001c1c18268184c1c1c191280c0850a10010386040c0007682d0303e0080d6511102c0403550400d807155510031b074001d490007140d080300041c0c0000341c01c50801c01070340f06080c00100c03003c01e80e265166880d503e0401e8481d0160b04280b17000d0010000568954940300100c06100020b0160b0700203200c12201e00200c1c0b00d01c00d80340c41c421081500010003452080c40d031500e01c012442e452505c110540001d000080d4440c2a1070342c1c0000710340c900010402000c001480504011151441c120714007801e00070100b51000d00394500c1100c815038444502036201000c0c00c19030f00450801079686101b8075080c2c3d00c0b071040500c0142034104007218099428406680d800440d201600304080503500da004104402265608818007117241404603c5207051041d00c05000050241c00c980d0105052240c01d45401c0d411141140182e00014000301e004d01c4401c50705078001c4503000000301c0d050b542070019807075000d140207046 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 972592014 1250 972590764 972590779
    0x2180105030c0405152709030f07120513120303050f060303071b0e0c0c0105100509070302160b190f06121e0b010905040201020c01080c030112021f210e030702 70
    0x1c02141ca02c5c0303c45494901d00504051021441c02c0c111504d0030181c40e4480c1a0300900d200055800401204440c000e0840030750040c5483c810f80e07079401d83d0741055030311071042000a01062903040d03081452791000d0021b241414003c5451450010142e4070000c04440d481c08185040c400e040d05c0020030703600c0295204500d07940a4040458081e140f000035030050103011840e90501c000030020350002c11303031002c00400a0042c1e81d41c03c07480100e200294072a4a403c4192030340092660780c840d501030300c100b09440402d50040e48035034a44400076a02520100009103513036031078a280c0c14143c0b1900ea403100007180c0c14031010389400212580380340c00060162018001a940b07140e95030b2a500105411036111464201ca544c41d01103103401850201d130f0403405446100a048815030040200520030f0039808100c9203143e0070400312140f100c0c0091012030700040c070346800e00e010703444000c001403210165564200d004288200d450081c0c0c000c2c000c0c00c10031a4034060741a41c2d2408048201c4100580640e543e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 972593264 1250 972592014 972592021
    0x131e181107121106101211060c120904240506090d0609030201200325030e030f12100810090213050906100803131a0f0a08010302180105030c0405 64
    0x103115071240020003006000c08000060816070002c00405094443c4001c4480c1543c521801c0410b403d441d014003000e80004614140c0050381128110441000180442d401d01000089642c03800040401a00030010b01103180c1b6805c0c1000d10441d070b100c468800c1140380c40003004103c510110340398003945001e642d0000300740e10191a090390304001036030301110400c4100002d090083c020440543c0c0107810600450400040641e02c101b0759002c6c4445401841c40f00002e0450700048051411412050585401e00300040b00782c14005002c808100150079a82d500301c03015000750540b401010148036104104060010880001d495049145489000114400c01d400000c42c101c0e0f4011040c0c10550400e420400c4401010a49a004000c1c6c1c60f40c0440e055114070301c0d1034407400390180e00c070424003500d98100000d60700c8a00902d5101c520b1764141d4138054110005468681c440b046000216060030010021820481d9400200110f802d0340d4100d40c1d41094006a210341141500c14070554490011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 972594514 1250 972593264 972593291
    0x90402030c1305010e131a10080a0c09060f08060a0c031404060209030622020d0f060c020313080a03080a0b1908101b02060606130b131e18 61
    0x1c4189030004044010500e42404000003410003405044540c0c608000461060030003011400c20260340004c43c1c8100c4071600203c1c1c02c038480020060005154410000522a08d0a100c1c20300e09a0152880b03030000c1c0d0410008106950306179000c240c1c120381088080124000108070310f41c00c001d00420102d44030700703083c10480c09040d55070407403030484049406200030041164001c20780c850041d01968a141d841c2d841840740c041005026244481c1e002d030300c6100615026082d207001901c144c11b00e8942041d43d48034001220015007242c409a440050b4114080b10002107000090022400500d0050305a1b0b400500034400034000a100d9515070300c1d6030070240d07a0303210840580380e104030503000040c0c3d8480b41c4507641c0401c82002c141d854544040f413a2a070b6070009a030b60b803400740d51b001030055480d45c00c10310102d58000888940001c01c83d80010030413a1000d002490010321a4044004079401c1c0720664024100014400d600d8a0040600300b103c020282c01c00c024152115200160500071300c080d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 972595764 1250 972594514 972594523
    0x20c0d21020a1a0105040c030b090703090503070803040606170109120e01020a020405160909050606090f0109091b0906020f0a021002071e080f06190c1e021b04020a05070209040203 79
    0x1490740562403d02c00c21643c680d1000c904031102160140710f007049410007030b01100c10500642e900015900000f51105000383c000d40e00703ca1042048a1604503d9141d180300303500269021105c0c0d44e1900010008101d81c510703a81e008541c0304c40200f2001c02c140d580c0c896001c5c0f440b4000014031a0444c911501307a8000d00c0026180e0742c0140052000e482c048150504010b1039184a1003c1501d212020a1044040c801c141c0300380005015a85450b000404100365240c2100031141041030a05c0d01044c03460040c054000c15082c0140c0103003540480000241200c03016070011003c44d40721081c0e20001d00b400255031403640f90143c903207014024003080100e05191507034009a113100c0c203400040780c100c03007640301034800c441101c401d43c1c40d44204644520384448040e582d02600c039031442c403000010622135101d420010068209200b80d101c1c0400c01c0302d04500901c200708096042101c142c3c401c0c000400b000301146501f110f04510b000000b06c2d010b820342c0100400030f4055025200014111f480400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 972597014 1250 972595764 972595783
    0x813020a0b030664050406080307261e070b16080f0405010213080601263304111810170f06040f030e090c030103060b0f040e0d020c0d2102 61
    0x4a542c44600d1844c0b55041040c2d00b07034070826000d6072400c240044c68810100c1a551040c0d400fa0380341518008403000d214003010341d00c007110703a8840308012a5203c0f041501410200031114040c16441d1055800c0030f1886d01c0b0000c0c0103940c0503d05103200030f00e20354440809503020448000c0e10040307446a0800034028054072407046d00541d0342c0c0b4400301d40c5080004110741266000e40c8241c8090707030b0031400740080842d8500d100003140c2c000d038089440982e80b01429100c2d440d144a0802694508002c000003100301543d055880c2c09a04090103100e04003069403007150611440d100c0c01c581043da12280b89243e062080500b010707010003c8661034181400300ca4801504d0354101d0b060b80c24182406003116000c0391048002c42d510340a6a41c4904002100500c1803021a11050540e1300c4c0d034a17080301802088284c903503c22090b0880d4240f65485205a03040642c980c002403e071185000301c040c2c40c0c032440d1071400307124410110503030002949017000781c00f07001010ba00d60391030048208016458851040c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 972598264 1250 972597014 972597169
    0x30c04050d4b11061303111f050c0a0206030a06090506120c122119090e01170a0515090c03010615050a0c0c03060219030216030813020a0b0306 63
    0x752200705043c5d110340b170f203041d00d001d5410f99010b02c451000308000c031503903c800540594070707034412030f50030b103004078040e01d4403e05620a0358141601603001500760381c4101c4151001c690b03280424041c8200901c10560300c0348094032440410b0003481602980c50009010892003001101411000020706100c40c101030703071903145010300310840e004040400e84c10181184a0350400c03d41e254031414810103051045401c0080000c2007a402c2c4880c2c0c410090081e42c5d627180a2181d4a403281c0094410000e4110419031102c0280c00c0d81403404030582440c4580003802c1c42a81001020f00c80f864214210714060f11007814010b523030381c85411007a42c40f100b0311030f0302600303100750b04100009003d560740040c40e295540d8600f190f0798503030050007130f8100e0184241403005d0704021942a00024000c40c4025040015a100c1216404a940c00916100260f0b0024124204007206002c0f1a060421644c80000200311602000c0003002e04480301c0300f604c41c1a9604c2028500c1400040e24804184041d00510007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 972599514 1250 972598264 972598267
    0x90303040b0301080d0206100e07090305030a02250602062406030405150105181b1b1b01052106040207060e0a1a0c040605030c04050d4b1106 62
    0x1116025081d80c0c00074841c03816640650b0030b4040e00540f0100e040741c822001100c20325001e43c02d00e413082c40011300042120050103032001c004004248100050031101c0c00300d9000f000407030a00d50b4084050840402881c06003160944140a0107401046150b40b04604604151b552108461281140303080b80704100c0d04518004203000601c080030610080034014220300110a9036200140003151411441d03201c0c1c3c01c100600850860032101c0c04240b0713400c0400040340c2c01c0c41400c039451054a1141c01c400040b9074070180045140c0702c20140c4030380454000f405d010303041c12201480c000b400710441003104490303540b59000850740d0351240d064450300f0342c001d01d042142103002101243c1d11401c04905807002a0f0401c084100020540600d511940c000740c900f9040500c0d050080d2403d410151002d04882d6050102040e20307104e428030b41e00310f5401412044800608820785100c0070200e0705c10741d013400c0700f101c40d40b04040e40502850b00d0b10b6a466100701d26003540e0350500303000c103030142540703560701c040e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 972600764 1250 972599514 972599519
    0x30e12090d12091d010e0f090703140f0624150705011d0f060106050a03270605100902130b0304060209151314030c01080402010c06020d0c03061401120c0509030304 72
    0x28071030f000030251041303910100d14008200c14020244402489175607400f815540016481110a40c401500b140e041c0c401c07100c1894aa40e500903010b858540313290107550141030500c00c840c9040007450b40100038954600760b2600d80000c1c100282c00040701e0b9601449004c0050034580920710f085404450b00704000300011a62142c8806045191b1440800c6901c54440e010840501c081003080c1201c1003900c0e8a4609880f0500030303000b901840556000b00280c00c11028507101c912207041c2811403048000080601d0003400f168400785498000e4000c807031042c00700945100c0d5030140502501e041c42e00340c0313440343d07160301e0004040d10503007100c20340002014019041100103400502000405810030301034042e00c0c0e14031600c2c00c0a04000b00e6605600450030202c0950007032500c160417500601d03140300844074030785800301644c2c41841c4102c42c250b6034540300001158184690b0014201c84039080b880303e0304201c00240501c45e552424250035688409121442e4003c404807031501502606032a02c465 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 972602014 1250 972600764 972600767
    0x1605030a09030201090b03063304080604051908090d060b030a110109080d0c14010204080d09050f0d151e0608060a0f06030f060f0f020d09050d030e12090d12 69
    0x1802e100c00c81c04100c0d10200030825602c450190303441000007402c20b6201c010780f080b44254908408a001e1310080f0007a00c2c4030444204100180040c082000042610b8180380c0b0b00146012165040c4591816a85080100054a407000c4134000380c0300b00c91421000c000c50074048024034201442d84d0703061252007010310820150845546100d24240c890203245655914496143c02d051005600003e00388229000007900d1a04d800d8003891150380010b06298543d95a50301d08079204508002042d0016803c020f54940710754590710740c0c00c041d9a400e04115460303880342a002d1580741e100e03801c1130700c03000c0b841000c920356601003c4603a07000300b051003402e030b035280440d88480040d56880340ca03a08052041181007031a00425088035408566044e8a40098640c2c00080020400c080d030754988030045e132116080c4900203000c041804c11340c0010129803a02d4558541640c50840900b81400d003585d0b61200b21022680401c800c03040c0c500d250390f03052417200180866540800060801040024400549 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 972603264 1250 972602014 972602027
    0x7181205010501081b04150308040b030907050a2114120c0f061b0a05090d06050a1d2d03040b032202100c02010309050a0b06010f1106010b1605030a 65
    0x50080008000076601c8a113195100e030001c3d40140b08800311100101c03950704003075012510142c4660400d05403076480759209401ca030b0240d408000305903004418803814130424000302005201c22552101d421f07140041005000980030104400c40c00d14240c0c110a1240c17040740d2041c0d64a2540555003000d00201282c402030b086003040d00d0b924800c200d1400d049140c0001c040740501010400c5a640045000d81300700d1590110741100c082050900c41102c040e190032425040851103440081681e10300303c510300044900310700899102c2a0a65189841036101049001244840034000010717844404008003a03900c1150381144580320011740021594041d8000d5400f0f024680f602c04140c842c00070214000c3c2d103040401960107000d9503d075480c0d0b18045c49428501d0713072060501003580025a1910740c10685032010a8406116440c1000541c1da84a80c18091080403814500004040820741d5951f0b191305004090410000013403103840c003c40c00c0490031103513620100b02d03540da521a04004041 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 972604514 1250 972603264 972603299
    0x20415230a030506130305041212030c020a020d11030114040f0209090f03180d0f05160603090f0605150603070309021005192a080915040f0e0718 64
    0xc24000c929188414602684920300300d0741c01400400240d11849402c42142c89009000c800f4003804100001f4043c000c902845a102c2c01000e00002d0103a041c2405070541d0007100c1d4000454001200500069a440c8c0342140c032190408180c449400f031040c00f1034010500b900c0e001c030081d510481041b00700880602c0071000580b0988203540c00d9140c03117200d2a551a03405024041d00c0c0c01c18403030108000b040100e0403181620003411180703000065142c0101140100c0f40c1680e0701e4020709903100340c80600a0811004020b9850208401c01051711400c0c14203a0843c0000d001c0c40c0c80c0c4000c00d0704810f01160464501d64001c00c031039901c1c02c1042c405002092600001c0b8020301310710586107400ca000e80c0075954412030310010b01c0740502c0c01c41e41c201d80d120210595855080b14200d6000d45007464420b05000740c1d442684070a0352440e0075000c0200b0484e00c5c150545400350100002c0c03110850f1071039800c1c202c0d40141003540d246e40702c0780c405540040b948003400c0c00c60140694000b0751b42006550001d0b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 972605764 1250 972604514 972604559
    0xf0c0a18081e0d02190803130f052407020d0305040602040f1217030f070813050313090e0102280302191d0d1110140c01090212150a0207020415 63
    0x2d01d680111800c4c1d0700c1d4410119244480c100b50313280500810002c00040d42c0c415140f00b1002501c1090790784641ca5808140002d58a582c071840b50f100302c018881e10502c4001c09402092081494150b400a50311169500700e41c0c20507850304c006c5010403105405940c05030084003290fa003504c2e182e410464800910303c100740c500c115001c0515080c1c1c0b14110440c1d004507030300403c0b0900740d83e0310b01c400e8900120240004c0c00c640f511070200008150148080c000c1004c1c03849560481916205002081d91505911140340c0d902c1008690681c2050038202d00e011003504c1c08404a40d0344420b015002802062031000003040c40d0300c0220491580710b40c0749030141c056840018070201001040c051010325420300200b0300d1195401121349440c06400d030ac2022841c51030b140042d1792461404166a80210f00c2c501c4403a916007000b0011403411143e801a0000362000400140003070800c1d08140003405445003c000d0390004003001503490b81e80100321412003108028214503610015007005c88040d10079483c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 972607014 1250 972605764 972605773
    0xf1e1803101a0d0f02030d020309151c24090b101d063004030f14090103150b1206040605060c0721170d050f0c0a18081e 53
    0x42828040d80b0070001c0d40512880c02d034071242c40340b10600004042c120025260001029058001a41d00308000c21454110354043c43e10b4010190501807034803081c14004011030300034080150340c0f10200a035034442c0c094040000c1442c2c001c080c042010101c28589690000903158008290b401c01508150417005040d5040740710b6001104084801d00b043e40c040e002041ca640645400e03515000000d00315401114115900400381448401c01c01c15044070208141c0c1c081000b00410305800c030711b41c0d142000240c20503810b1201d802440400340e02c82c441c07109042c19500c1d0708160f8500c080680070f001800000c00100d41da003802060005541c00c04441c0b05200c0c078242a00801c1a041c4401a9070f026001030004012071f031305040e440c951410319044034105203049014480e001c00e40402c0c41401c114032101020765120226503240c4c0603114000d1000810303001c1c10052180d0b03a10035001300d4078083c0c0c4a240032611421424610603004850740e00c405a64466410386500c114545100446002a8002100e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 972608264 1250 972607014 972607033
    0x180f040b0a090f020f031204090b180c0a14070b07050c0c030c0303071502190c1119210506100f210209040f050d171005060f1e1803 58
    0x1040d00c21042e0024490b0500d4403000c001802e10a8060204200090079101064120842012940c001da8040850326403100740481c01c506160480b241d00c010405076204d0240341403400d01c1c04a02c108135100080025800c002c004800d0074030140c400c0c3c0756005101c0c00490600d00d03801803890f006138a101110340102c8405068510340041c1d030313490003c0c0290141d41010720325103c0d60501a5070b4120400c4498080045090302c80f0303840e03185094001952a0303464400e20f5410404050b1312241030b580c0c01101c8240c99086030a01061550040f03e8010360702c40842803640040010a02c0035140050a40c8521424060820324200c840c02c280ea4000044014040e5212a41c00c01c05c8107410740d002450036024090000741c1081142e0aa105001d001101d4090b8181d0362154640300054580400144040966844d0100001c130358a4010005500b1520005e0800c00011418400c5800900d0802000a401d20f4811420009007405100c0c82d989140c48a50a5107440070322010610b400740b0038000c4083c0c9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 972609514 1250 972608264 972608281
    0xf0a021605090106030b0f03010c080106080708041e0201021501060e12070b032a0d0c091512150503150916060c020609060f031f08210306180f040b 65
    0x3000d0072a50010551600c9920b03048090f07005000c000c2005400c00e420710020052a2001d003e40101403056a503001d0142d850540c00501c0b5000242214040004400a00c8003080d044042d070313814211300ca540c49400701e2042c40180d103055642c481ca4180110020000034040d03800400880113401c040d21160b001c4291801c2d0f0700c0c4c03940d04a005101c803403c024000306035038201c0c0310340d240180c4081d0300140070808070b8240152201d8103c045c90000958540343c10004807030340421814001c001d02c1d2405d183d50003002c1d1000d80100c1d040d011a105041d651b00d080c0150151155906c002000b0190030f403a02d00c0d007038100182130503000300c41a0107107110798080c642e83c54021410800440d040bd90360418491990ba08001c06a40012041640700c80d01b48010007480758640c000310701424070b9a004103103403910748102c1c9070440000c1e440300c0580c0d0411040041c0f001c02d4800040a900c140c0d00c4495502d42d240c00000300d800302d00c41880024418144108425041d02c2c00166000c0c038001d400600702d541d0703160135 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 972610764 1250 972609514 972609553
    0x506070305310306200c0312061f08181504081e0a0c0201031401050109051215070c0302060f06220608191709060702120106050301020f0a02 62
    0x180280040e104000b101d02140c8a0300d21106202248120500c1c6946a2509520100b581d600182c500c155142000440000901128007080c25145002400d1558811516841e030040142807194000340f480043d800c3e613100d0341100100e500500140070961510b1200500590080340c00c00a03040820904010000340003c1e102401344170b203007402d4400d42e210b594280443e089241d0b60b0000c02c0007812018038540541004d00480c0410390303a100c0303518049000040555050141038201d40049100600903030360300400c280d090325016100c1d41d21a0311065462480c0204003001c091a44240405201c0c4142d407001001000b50f000e82e08603500c03910786503c514016001035800303561006213081d0b0401c140e45016071030311544a0344140001d00e6503a410140703050154050081081c44561110709007009006a54120f0395641902c0c51414a4415000b24850307108007070010b4442c0801010000d480103094120030054080035000b5529111210751a81150f00030140c0d00340503000e11003c0e50303030001c8800c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 972612014 1250 972610764 972610777
    0x30403020a0b0405030d0518090a0c02190c051203070c0306050402121207021e1906020115290717040906060c030c0201080a061205070f0e0420010c1b0e010506 70
    0x40140402106481c0700b50b587d82d20910b0305c221502030305001008503a46100d441445a001d1040100d000c5c24030007402030400b111486012485d04a405a16000c5010501141c058810598156000358440c00b682865802200030041200703554030400300c10005079801c000d010720310070b449842d441003d122045866481d407541078494120b051200d407000d0701c3d0807001c0034202495041c144100351205000304000305016540801814120b01c0308014441c0d091180d00a485180d1003400c12481c10822100b501c1c002c0f40603e06520340e54400c120740e114841108491855a00c000545016060200d585c03182c0d401c10b105072814617103042000201e01c0d00074208000865416a204800c1c07100c1075005580c07100000e05481140c81d9952310114940a080100d000000e010b070000340040b618000e030b100d02d880b090760408070240880f14180800111518020900c09505882907540340c4504001210403040d0000e01401106801c1c0c59880e901c41840951419a201c00030300480c661b0300e62040c040c0364030644 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 972613264 1250 972612014 972612019
    0x606090c020307330c02060124080619080316030f03230c04050406120b07030c05041505120115030507031109060310052e02070b12070e0a0602030403020a0b0405 71
    0x61415135034028120307400400499161406400d081100700c5042141d050602c07500c0036074081401403040410307000b0301812506200202c55900d800c0840010103c1c1c0c005012103000b4440c0801402a080c09003a0780c4000d0040300c2c084039101c0c008421030b5000b81c00d4200c03054000c5a40000610542031080c000c241080c0c1e50b003555030303188544090709071005040043c80821034003428003021402e03503594050017000b050600d080c10150308007820200106c5a0180584040c14604145501400d41040035102120131010400380c07103041c0070000751442d11030312085210810700800086801c03030a50740a403003001c0140d40c1c1041a5510806c054046446100749684a51000d01010401c1d241140007035900010b4444104000e6540b000814200b00c4c408030320303091520f81508030341030b04c43d104035440035040c8803440140b00c980d20f072041c1c590540c480e500d1500d462500c40d00c0043c0500d4051140c0200105016110f44046a5030700c500030740300d23045800101c1c4510194500000c4014060082e01c0c1900c500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 972614514 1250 972613264 972613283
    0x32a03090501050c07030503030c040f0510020d11030409060e011514090f040b03011404020315040206070f03180b03010801110315100207030602070804050f0d11010e0303040302030105040606090c020307 89
    0x401c40151103e40240d00814024841d044010000074000c3c4040c0d405813141c9076950381c480b82002c040e03201c100190f0308094066028a101490895800a0345030100c00c61403c10044948400c20b906045100701e4000d082e000d0304150b4001171000300000668120382101900009031854521308680c0c4801580d011404c0360b000740301d084002d291034070315003107650320051001607c50350711800700b403c1d6114080e80110040c111420170080d42002d01c29600c1c070003201041c1801c9880e02c0d90000c1c5241c061400042d21814101c00301600300750040100c242d829210b5204100119070f29407e0480d140e100740601d62155080061513507034400c060041e00d00440c12003156003001b0040c0c0d001c1c4043c1500004808085120f4820000081401c03880200038440c0100c0de81950b0314240b1090002406800c2510fa029141da1520080441c2100075446000360007480c12440f07400c01480003c1ca18000d0fa000654154a06410b000070455141c2c0320f0000c44940c0902400040d01d030340c0e400e0703031030740200100075101046 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 972615764 1250 972614514 972614519
    0x7080a120c200f0f100b0d0c030803130503030f0702010f0603230c1003060801060f12020910091e050f09070e0c0415050306090c0414130e0109032a0309 67
    0x8a0080a18104064003c0340e20582c1ca9410940c5405020b008610b010b40110b1a1010070104034000d401c0801303015106c0700303448170056480c176407071000c0c910018103004000b00c0496400c4641c110000b194540080890340c4905120071710041750303a0290740b04030266180c4046950300d24864099070003240e8020f0501c1e40c00320700e482c0c14180e000d18a40b98640c003034007841c1c518600c40c0d40c031042461030303614907590700062031350621443c00e0031180315422600c66014116020482c40e492182281e40c038541c1520404000c1e111000c40301244546500300c0c406039800e269131132074400881004e0100040b4080800c4c07100ea202c0c2c1400e0040748006640c241080d401c65030741400044441e03c0000e030880c085501030b42c9000d81e9a00340c90100720745c480010000a4000090200616081001541104030b1421303491409180202c0c0d80b00d0100c0301c20b1814000d03140d44120b044100741d164030404117510340200a004c42005ca2800130024001030411100820800304525040f00501001c2038100d5410b07250004500e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 972617014 1250 972615764 972615797
    0x31918080714010309080904050f0709080c13020a0309020301021b01112802150a0507030c300b0a030f02100e0d0b060f0a0f0f05040b1507080f07080a120c 68
    0x103203060584a10200700702086042d01c8d0782c441c01d4800d03502101504c2d80d60400000c0100764107029400301c6010b9200d055070070002d176903040b40004915401c0f20010394442d006001038000c0c11840070081c0d815440400c8560311681001c4140c1129680c80b402009005088007001100e801038a440744051001d01d04171003001c08541c1111f03450340c460750044580c00c802c40c400c0340c881203204654100800c0c0e00d68052229048d018007031141000c1041c20b204c0b81511460145a184d1114403042d9220030040780807602002c502c0341e0000039a010058500e04603a81c40342045420218101e500704d002e00c01c03445a52209501c618814041450020000c0290300226220304481e498090300c4964080711248103201e0568402590000501030039900d00c1020b4a048900807221000b40d002034029070906030b01e191b4a560f46140805202038400321141c8400641c1401c01d118029070803103009506000030312406000d80e401c050f1210b400d880d900c103413000600940140a58122100600110b010411224441d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 972618264 1250 972617014 972617021
    0x120307030e0a12050a02180f0406020319240b0307090504020a090b070c0f0b0403030215090c0612150103140610030e010623040204080d110319180807140103 69
    0x40c0c0d00a05641866480b820b20f122840c9140c0000c9910f540120109000c50406000700c10f100802400c1840152803d421002c502c10001840180050740c00000140042c403802c080c0c89548a1501080150586ca03d440181c104000724070502a00c1841c140001d80000c0304003202d20940310baa03601d4140501d4003041c880a500404520424020382c16400302d000300488024104441c0181c00781d080644c41d040c1c0c001c3c0444040d800541c2c01800030002030000c81e4001840c2d03c1004450001d42245a0743d0703540c0c02d800c04030401d800f0340c2e000324000781c03410f40c010307801c000f96000b40d003102182c00d18845900c006600301d03200091540c84900300c00e00041d0203440c081c541050700d60598180820001c000c1e02283c1d007110a00e8100d559800d480c180606400d03c8015104200c01c0c409640452a250521200742c1e6100c3d03015200004201e0007a4170351013010800c1c001c2e01c42d1800441d0010402c0805030101070442c20000c012108101000c000000b1003a000140510854070552000c0e01c1c0b000c1a600118080c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 972619514 1250 972618264 972618287
    0x614010f030f11070f140111180301061d010609060905010f03020705011104121a070c0b0c0405100306080d180902090d0f050c09070203120630071412030703 69
    0xc0039507a981c4400d494040780000d08034148602055040c01036a85461005400501d44840c1c00ba8501550014602a923004481d03180380d02c410316a45a001e000c00082c09020381d50000160f04501100d07101c051072582c1051070588410307031620151951121000c0754411a580702d11800102e00003044038855000754001c0c41c019025030008649041c00d1480d902141e4003652110803005800b0210800740003c00a103640c40111840d001d07543e03030912041c0107140140214014100c6c107616000703e1952070b42c1d6801c0b50300403d0041d00c02e001c17895191201400412461242180c140521940c0c410440d02c0350903550160304c030035000701914505100442c0f00940000000c190070007108000e44010502d0009513603c0d152240005205035054082848140c00d0050120802d650007030101d5070410800c0c81c4910303440750301511501d900e246813400cc01401040c0e1250241c1b0504600c1040c0340c104808903846007030350f60441d024003c1d10054424040103003030b51b24040a00c0d401c01d02007134000a120340ca040b0319 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 972620764 1250 972619514 972619541
    0x1c0501022713050c090a0803041701060308120c04080a06020d050105120607050c0709240b1801030b1804030903030f020312130c0509010603090c1410030903020f16090614010f03 78
    0x10803800c40041101103050303401647c0c0690010030104040b420302a07c006e41840c10000030b2080c2ca256039100d043e24007400280910104406002a804038000340a96005002410440342410014101a4000e40c00205c0b29810301d030170030300007180500340315a00c401540c10500061040f0303a1048401c807001d4002070148001401805d031300040c03001d554051650712500030182d2280c40d400c40b540302c1040d0300c02548002041c0809209140181c503051060b24040704083c00c01044600450300010301c020b8145c1400049140c0b0003040c0010716500c411800706a0380320b51035140705100001ca0980e92802030030388100045128800280c1140d0313552400701000c0740f095140c3c10500d900c4800040307603940260410f5001917595104030040c04401652440207140381c20254102000790300224044041d1560340001b41070300d81c001542010300c00c200c107208025844080d580e46454148005101c01207903c107150600341000008035041d10300785807000120078142c48503c1a00c071204800e9025000080f010503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 972622014 1250 972620764 972620767
    0xd03060e04020904230f100b0d0803090102042d1707051903020402070b0f01152709230c04050a030b071e0507031e0912021c0501022713050c 62
    0x50b800c0307a004480384a080da03c5c0283c58040000e8101d81e1030030f55402c0d40311070342504140a1000c1921340c21080e801e131540240f2401c0d6280d0b580388540340a0700c82d03a8410203480311203158252015604401c09241c0f0214041c00c41c480752b0f03503101c842074810001c90841c0d103d5004203908110702e25000703600d6181100040300051103107a590300007a0481e042500181c2d143e4004004001006040d00c0c07007107014264007038141309600e1a0890040841c4202c0866440c80750b0039001a0500d101f12800e4180103081c1d0200500507c0c1192a00c1c0c0100e40300f1041c0611504252804501442da40500740c41c2981d42c05010620b4080c6507444296100402414520a0010000340c841c003040700d20681c462030440300d440d025035400c40c42c40c008000720009503c000c40c00401884259071954000c41c140200c3e01ca400020410444d10300001e1000d0540c40c5507602c904d603031031798107004111042d005440344580b00c4640484d00b0303100a03446010b621412174000c0c0c2c0110404a00c46004100740e00090300050300005c0306 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 972623264 1250 972622014 972622043
    0x912090b0337140106080408032815090b040e03070809121b101107060f030209040e010b040e030307140703050c01140a050c18060f13030f02030d03060e04020904 71
    0x10044515114402c03030359484981100c150400460028018030452400d58400c0c503041c1c44641039408050403c8101c51a0242005400071000c0c0d041c01405010080402c64100c410b0941031400b0036520600c3d894a040c00c1940c080c2c0d10700751168104149088000c0e524005032540c805410798408451941d0140300700c040550180b500f00000d032010761210389400d0060349000100100008500c40c20402c000c040c00c00c00180d400e0115072442216140d04100c102c04038003c000fa800b0b030140380344c41034000b490b001d220b19050350705410020101d00292400c02101030340781c41054980c0300480d0300b440819a107100700c6112030010401040014005d107016030800101c5011142074a24141241c40b5140d101d03410700244944602c6903035040000d94440500e005c04124040884903040c1c11028810f45021440054a00740b010484603140c41101014540e40d4030303458020010710790020300764080d1250380c0d11032801a00910800d801d803143d40c100301d00c44da82d071903013000a0000000e00880b12000d041020 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 972624514 1250 972623264 972623341
    0x1009060f1a042c030c070909021011031e09100219030806010917010b01110303160c0206070b010f14010306180506130e030901080f0408040501120b090403030912090b03 74
    0xf02c8040c203020029565840001d041c941c5003030310030f800c09100640751090a000503a90011030710400002c5e420410256041f51000b2801c6002e203000605500a000c080c402c6155060741c01066207a43c00c80b07019501580c034500c100d9441c0c4010300c000c0e0b11002845080300100340a03014517580a90b0514000308065220380323400e04105010301c00144140c3d101e1421406a40e040100f644404c00108019811071401502d0b02c607260004400c0c0c103085c00441311104096458140441d480141c05c5600e50100703503914030524181d200d4a104442c1081010b0032200c500750710030700800f000c4640f40e40d40c1c124006080083e05000300405805140e0003400002c0c8800e189643d07000c0d1661841c50000a50707100c80141c0e001400c94a4010a0f41041c58000010000001c00c402c00b40e505565003132074075082d120101481e0400a02e06015403590013030b8008204802c050f816000130a8a52050100514450101601755103101ca2405903020030b800c28030010f000101200004044260f03e804184080c129045a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 972625764 1250 972624514 972624581
    0xf100f06050c0c0906151c06060206011505070b160c320705090a090807050106181d0606010e030c0406030b011a0f0a080a0b031009060f1a04 62
    0x8104041103020842e03102400040c031034520b40010943d641d090500c0d2400015559450f04062089040000300b001441b624101b002004849a9400108026a15098060360743c502c04d20a1075803081180c41c00200701d51048042e1054907510030140340b09900d5425000c0c460180301020a81007044a46181d40420030314002c04041c104000c240c14040601580c8624030f40c0180b04040ca1280c9c05600100000d40703941e418140d20500752080011002101d240107000c91041d400045c0c03040d8202280442c0070660118992904240404208490300d455503040c02d000320480d00e0f014240c0c2100000602c1d55000c2c03a07074181b00c068001c0583d2a5100c10900027001c0360501c4d04240d40071030740780005001400c841c1c060b074400d000c84581000d05280b240e83c2c00d25240d1003688440c00400c8402c2c0082400c811454001c1100703490f0080c103030740070081880390741c1c0020410004203580441c180400500d50000c14411a0400000003200184045a40c0107000141080032100035036582c03440683d400d20020f060 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 972627014 1250 972625764 972625769
    0x6090d03090501180b250206040305010506040c1b15021306120b0f0618130e01050709060f0909110d0203011e090218040f0f0c020d02150106080f100f 66
    0x712480c1d00795007000c0c00100100c0c8800d60440c00100000707018441d800e6aa030039130b00c800d0441105003540c0b040c1d614005288021501000307401c544045408000c00c003043d08410701c22401500c0070014441c480ca02264540c2503801c2900440c0c14401000f00421401810003d08840351080945808207822880078a11101c0e440600041c4000200b86c5040c40c40d03015040041e6001c4a002c0c075180d50110000d8194030882140318124440c00039030100c5c549520303c2144200e181800c04120004840304042c0c040c0504a48100c0040d040c1400465440d000d0310100000400b03a6a41e440030303038103064a210041000a480040021051042e420b2002e1140029406403030015090f10fa4040c00c0d0f4416030b01c038042904144402d600501c807540740d2040301e03140400d49400c21a030110708561140805d0009100c2101e030b00104078213004101c00045c0e00060020800748107a401c8601424000750418107880080c0102c200051070800441c3e0885055100180c1001e890f0348400c0d5402d9503603da244141410380e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 972628264 1250 972627014 972627017
    0x91c020d02062a0714010c03020403140708060604020c0109060603051c030e0307021e0a0b03010f05010504121b180c0f110a02241b0609191106090d03 66
    0x15403400144550510a40b90441e61444040c500e001e58a0190041c0d076149a2489032111004100301d0705212080b1200560130810324002c01944440e5280207002e50b205020540c2c803c103808035480c8107000c0000301d0104583c542c4014001d680c03190f00402001c5d5101c2110321056640342c07a640c00104605100c4c003401148504001d2000c860750300d01580c60450014606414103181041140d1600e00100444044a41c1100c5424034280c400f464800c010741708900894202111070740220321038040c28000d5060390070384841408001e40d9a801120749102e14000e508034a01101c5040000a20700300c0e060450242a01d442151680c91310326120200c14170000810107143c8510040392210b4002c8480030301c4003c146401c2d104008d1500c4155a94444840300901846260f681c110107025910b410701061142c80c000b03290348080c601c004c190215501e03400c0d0f80c030b13900400c80458580000001e000c802480c1700c12006045200b991542442100381100e860f0300907504000080c0e15079603101c0c42d503004c070744207 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 972629514 1250 972628264 972628273
    0xf1e0405030f06040b0f0402060c101d0a0215130b03240a36020403140d0305060a09051302040207030c1a070909050c0c071503110918091c02 62
    0x108001c05141c40b40000b9140c0d0703142c21807000e10012418822038690b004800541407a0030340c84520205000c2e00c698030700000c860183c3c0f540b2003102842508810024200b02e5600b00c0661390b41d0083d170781c40b5451130a0080d07210b80c1d107264000000b01040068003025551240100c0e4a81d540c0e10219101d5108842c00e02180f03400e000045042c030f2040a03241d60602055856034540b43c01c00403004d01c25403003c41003141f10050703105403050180820107801c0c84800750b4081035440f155a0718101d808204003010742c08442c002d101030034030098400d108682c85100d005101c080e04900e040e0604c00140b85c0500212600d43c494030030a8056110b0340001c11960740f10f65100c5ca890561406c2c01e8070540c44c45d05a0203451034050041c8072780941d004102c8010f0380e961300800515a05d945a440d0094480c900b009030705409058000540c80100c60414203440032142c03020f016406202020200e14401c4c43c2803660b22800380d41e0f0011810020403040c07a4000080c4084824007601c00b080380302200c82e0300b05480010781c071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 972630764 1250 972629514 972629519
    0x2040203090618010b0f0405060a050a0609080f0d020607140c2d0a02060901030c0c1703011d091e0114040503191e03180b0c03010603180308040204020f1e04 69
    0xc061a4103c81c5007040c10080003640e001c2c01c006071a1518294515100d262079901180704c0d40e440700040e81c000c0070020b04005103a551008050700c100d07100d01c60000c55000b0500a09620140850880003520381c5031701418040e902c0410503220710220800c0c41d02484024090b06c02010001c02c403c0108818280c403401010606648d5003d1161010b4030b41421740e00195200e41c016150803058418410090030b0100300c078032141c4001c0b100500c502c1000b4156504c0c44ae90421a0041500214140c0b0305450990b120815052040383e00c0c00c0c400ea07489441c83d4052805100410a16840112505803800c00804c840c2120407a1a680c18019982074480d50000900302d51055a80903103800407001c2c038102904c2202e0806255480c020002240c4418907469400c1040f042d103e80c8010502c003540100a0503007810b0581110400342c00c24004c080100345800c01041a4200c0c0f5080601840d07450350b101c65180d9616030a201c042c0d00182d01c21401503c0500c108000d010703c10080c00300006e84070305101c4c0c42d01c0c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 972632014 1250 972630764 972630781
    0x70608060a0819080c0f0601030812070f0219080d0516030e0106030209010b030c090316030209011a19030e1023010305100c02031218070504270c03020402030906 71
    0x8020350042c09280d1190019244a41c40c548000034000e41164540f5254281240840d050165118181c3e4550044100100400405002405484c3d2086104000c00e80d168401911046800520600986e000110001450f128800101c442501c21504941089643c01c00c50068070001d0310300c0c81404440c0030300b0241c95070381031180307840c035801c404000d0000780e2542e00801c1000d40f041c000c08403900400030000314048500000c03a04074003000f90464a50901d1152000a2042c4500040388110428400054000c3e880d2070312070031403030112000d1854100840508811081c00440c02c7e814142c545404607078015040c00465060400910041205003000400707400284a0700381e0301d09020019001800410740c00284107071305080c03c660010340c1800b1070006038a1030291414949020000034100080d444101d03548c540c04800039403c48000c992a03030104800e44e0041d40c546100050042c1c920020308000301404046180550b00d44240240c9a0700414166442210140c2050748070710180400780c1c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 972633264 1250 972632014 972632029
    0x30b040213180618021908060603011a0402130f08010618110915040b040f0302240307030b06040e0c1b010b03031614060403030b0411070c0302150c07060806 69
    0x2849256010003218070314001040941c0c40c848400340801c0c0e501c2c0c04011324105907080c40310b841c0303400815028011401d4240c09240725214041e00c45140a00b1000c6501e83c20140640c48000c96144030646200740700c03005010003500b00c2c0070a0a1138000201c800540c505184074210090650301001285040c2000e54000d1007110440c0300445030751800324800541c2c4088015104440350032181408000d04003440306207a801a9000908048000100010100344000c40031044038801d80e0203c0224207007460161a14103545100c80c04ca4500b0000580000e100b030340171040c05040102403c0c180794458150002ea910122202d170407003a00010b48a0004a41e0f444a540400b01c0500901600400d4408242c82e80038445100c1003008869601408001005d142d10214124800407207030f44d843c0605004001c0d04034001510f005503d4803041c4100f04808000f100d00294011240c460b1091656007881110804c1034280408140144040300c40f600c01030102800400d01c2e0355030f90046042640411925 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 972634514 1250 972633264 972633289
    0xe040e0a150e1b0a030b04081209011401121502030a1808090f06040602100b01030605060c0105070e0114070b0402180103110f060301080c0f061917130c03080901030213030b0402 78
    0x103c0b400a40d4601c84d59204281c00c280c0c1d90040e07091407a6203642c944114203004005540e010f00510300c080000c62007056105c4141562015400c98003641e0340c100e0f203c030003402c030310010748070a022840d0444505060b4000f1754200b081784c800000c0302c080e1540314003107150205e04211400d200009070b803001031800e804140c848203000c8855070b150900d414406513449482d40060070f0071584902e40480b1503030003588840c00400c4054907075543c07121601c0c415030003000102c800b400401c1d860907401545500c0b5012400c212502c07522011716041d01d944030050003980040003242d000500b0481e488407010302d107d44500030f52098040c140c140e110481001183c281000406020b420280010820041d0000355a82040c600392180e030f819a1041000c40c2e101d12810481c4084e052030500b8032801c6179480302200b20710011074003500c192030b00c5034904440d0b4003000f54400750010b2802003091010400326002441c481005040062428041c41d024400d8915107a005a40400010701000158100707400340608 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 972635764 1250 972634514 972634543
    0x7030911101101230a09050a0c0b1b03130e04230303070305010603021303121806021b040e1f061203110d08091b0303040e0f01030c0608070e040e0a150e 67
    0x420520f001000118010010b185c1601952540e1041092000c180456100c3d40d070030445441d641601c444140388241c0c8280e9144032281c80c1d060481c44040e60100a51f50160300c0190754006042c50408034030072440c0090001e80c0d5019600b018084030301d00400180441858290255441e40760600300030f011518141e100105150040000841100368130070300c40c0a82c2c0e4800d82c1034800410301d5808036001a55080d44000900c210107004c200180c0000f12190700e56595803440202e011700700c00b408103882e0702c0e82480402e58040f12245c5807240520080000201e4800c00025419030f6581a075a8400300041e016008a2903851a07034503040803d0202040c60401e40c18503079024144801016924610022920402c40408095550070303034040c8201c0300181185c0c00e0340c030414240004604143c035030a1008a032a00c465401c0050540d00a04071184501e0160b120500115040b07002d00020b08982007180034036001c0d2806240001d007001000c1803d0002c080c00c00500441100c0da0180380c03d10241c03c80c1e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 972637014 1250 972635764 972635801
    0x209010b13031202030c1b0a1a042d0303050d060b120609060303070203011506111621061415030703080715180302030304150c0807030911101101 64
    0x101c0c454040c0c0c2484045a50100c94068010f034400012030450240222600e424003a00083c000c5120340f0f2010302c45940011504408517503500c6403450102c0b2124507000c04900800c0c041001041e12104103400e201101c0241c2102c00088991120340301a07840e001100030400c003180d20290034a441c41444050300240d480b240c036000b1322403e0140e40900c000d0003a4800c0c10a000015525281030041c2e51099034040d00a00111520007020385039418180107640002c0d0071980b413000a8030001a411003d41500f44415100904021802c0000c6682d18081c08280d601d520b4448001200380c45111750915452505288a0501e5600c0d1840f00340001d44a510a43c08a4800d102040030f03101121102540041210080003507503403400040c0a0301c61302c6604c000c4a2169030014150040000d521861249401200003007411440204691503500c3c00ca0004c0c028100249140340030364003000409000e0174580724118084800120a030100b064103000003132005802044031082409101d800c001446c0114 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 972638264 1250 972637014 972637027
    0xe0607120801061b060b22020d0b0102150a0504020102191401051b040b0d0e010e03070312060e04120309050715031407022e1a0f150a0c2103090209010b 67
    0x100c100b440315440190149544440c2c4000c0c40e56922a603107c2000031001c004001c00f4080c5508009420581d04040d15a05000c0022810b41c80071400302105011090b095416490751070780c1a00426009104906522684d000c09514203500d51661002904c5a50410800303904d6030a41802c0d50320140c001c0340080c0c80c14541c180041c2245041d1020340740407103c0709441d5a0710691020180c002d02d00a83c405510302604903a0201d808001042018000d07140c10312800120600304040301c0040c0326501e05102e1b00000302e000640d0210400c040c40c04c07070b890040b030105d02645841d820b00072507a0040c000c21031011070501c0d2543c1c0600800c00c101c03200c8c140030180361900060281d02d4204a0498001d2100b0100e0030035004211118006005440700d4020003414402c1c00c40c031200c614114035894450001041140c9951600b81c00c0f4040e04c540001540303040c004940340956244201250481d01700c00c03800300e9040000a41e00f41e20100800558001c074050f4000d005100000358181c11101d1358407001c0110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 972639514 1250 972638264 972638297
    0x30702091b043f020f0306060a09182a0605040e0103020105160506010f08150c0a0807090b0309160905102309101d010b2b02120108060603071d070e060712080106 71
    0x22042b23810358000810b503105050015810407464502c010101d07a03243c50382030703003a91001c151030707413404881c82c10609920380321030301500d42d030080d17100b080e0038500100010310065206001a00d0b01c0020400320700c1c03040c1e41c955521805c00d50240c219243e03002e58020204414401004088100811540c0409950600365074407942841140e017240b0074003c0d1000414290780c496031040c0020510428400c0d103a01b000c0b580ea07034031891114405a451501c064020074121024841d180c05a10b9050381c0b80401440c090160b400740e5500180c403003071551003103800b810507100c100001c0c1c410710700080d102c1442070404181da03070445800001c16961100d8600180680185401121921420b1080d0710100188038480702c01c0b00074609010030b20460001c110441c1c113410001e085c506036540002600d920b5640c000505980e16100e100e1a081908181d9024402600c1d000c03616402c9245442c00300400e58450011500991158600f01c610103111150600401e078020320300790240c06903142c1000e448030307031011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 972640764 1250 972639514 972639529
    0x30c010f0903060c0e0d14070b090d0f080f0c030d1109241c0b0102010605030d0c080702060403020306181903080f090717030702091b043f020f030606 66
    0x802061190382d03804203107146000c0d07550045201700040109141c0d8070070740f41640e00804007510700c5443d44102d9001041c030440c02c2094801490000d483c0208010362a11000380c82c1821000541d041c4c3c20806c048658880390000a052006202000315a14003401d2608011140c1c6940c503c002c0c078a0600c804100c0d940d5180315007000450341c840c107402004e0805910b450700d2041c500030007203000303885180e48455005500b1055001100740c00800c642ca50f28014192242ca8000150380081c52031101d80f4005008a000f0340619030019042c0781c1040c0d01e0743d0110f4075140d0140c0b0010107489000f5403031803201c6d4040241c001d51b048207507c81000028143d03009080071002a215950b102e1001e8009000060200036450042054178480004034080b522156282c0d0b104400c01e9004541000c00101940184081c0c0c46039900c036100000c2c9001d00e8901494440c54a440c3d1101940e21004ca1100c07a4050354071204c0c00a001d1040c1082514180344108140c11400790852400790f0009401c00110303964583c0b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 972642014 1250 972640764 972640769
    0x70f0b070b151e0f011e030c200a150c05181c150c0e100c0c09060303050d05011d0711070e0a06080c09131b1211030c010f09 55
    0x40d4110a5484018100350246071410410380c1180410400c5042e0404800d083c0c0d01c42e0708141c0c2e20b4001c54210400444000307882c007074581040b800503600012100d1183c1d00805002c009442c040719107490544810040881354414003680758061511207090162007480400c1d0042003110400841101404c0038126015400882d503440c111a80c0462003611480e0700c40320100070189500d406004140303482c640c001044038050308080e103020708031500c041c0149400e2240020040c0342400680803c98101c500b4401c07144100d800221001e000200b0810600500c00614443d4035120f44070112020504100e40050f803020120320381c00800321003e503500b0140070341c000c161444d04200226020000d03502d824400c1c0c4c0850300d4134072100d003004800b0020303078045000d4410040680e080300304540c0811085038401d131500090f07a03440000710000164101c004122071503843c1082002256214241201014510300540b18101d01c405100c1c520f10701841040d20303810090800300841e11551800030000561030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 972643264 1250 972642014 972642023
    0x12040312060306020c0d0816080c09010201060e0c0d0f051608040816030e0a1203050f0c07051c0201030c1805060d0e06240d02010f0f0e150c070f0b07 66
    0x400d910340381a44150010320103140c1022056680b83c05032240790f951140301c4050480040e22030008140480c83c4049030030952134103961001d01e15192a00303c2205980113108080c10340d91794030800650b101402420301c0c07040b070030740018070303181d445200c031801c250ba50b400d600b000024601020065182204074403c150600c0314544480b0560702c40c5001005032007200c80c080210360078182c1031401c1542c40540e20f401e0a40503105502c03496621100b441d14104080c500a002c50014003140d000040d0060140a400101c50115542e15648801283d10303094003900c40704800000304490415960140149035051304203240140c151112914010740d1890070b0301900d4820000007410550300511508030414001c4080c00b034a5007802c3c00c4107200301800c0303060001c071542d0140c82c0350040549000205c50081c1c540684036440c0741e010315901202c042401c0c89200341070202c035000c07100480e2280101400d0202c1124000c070703511542c0b070350514036085581d400700300c440307101400501c074806286090383c0031107900 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 972644514 1250 972643264 972643277
    0x11a0d0203060a030203010618060803072a050406060c1202060609070c02040902040c081f0b07020111161806173c010506090c0a020d1115010306020d05010605120403 73
    0x1244000703045401d0f5030b40301a501d9800e0050105001ca09080e07409089054814200585550b5194041d160300440c44082d00328008425285103007003030031500f125030503811580c040a213a194400502216500e802040004840703150400400c20031001d03400c02c41c20180001c2c081d920b8288000b46072644000d0a020404c0300b031a81c088219183e90300300090b0594000c0c4144075011484600a020380001c49404102d07105030121010010301d0b803040c020503604008080381c5483e40c990010340d0101e8606211044601c40d0640540314429001000000b03440c0038041c07059a000d0303c00880058520b00d070000b45445441e501c024488400c0004d441900c02c03982c180b4014618924001b41e0443d540018600d0014050711501c0a129401917004511403401296141810740324003003014128041d03417001c0c0d0b0141e4800308040700d041c0c2c01007000300c00a0500f50101c0d07240c02d48240000010f00390a0f4001c032407564010440c120301055a029090144c8094913080d41491b840c0448580681b0002c0e1018090250 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 972645764 1250 972644514 972644521
    0xc0b0412120509070614040f0e060a06081306020f07080c0d030608010b01021f0e10021903020703120504140109050f1b03060a2016120e060d02160f1a011a0d0203 71
    0x6c000e07050b6402081ea21805607581d0f40ea80b041c813009000c007145d06500c1403450840c0410600c2c007035100131b40100721900301c1940c4164107076a110002d40c404000481e8600e800d008080010714a04002c0c00351112030005403550a0b091a00035040d034000750409079403641002c160f11010703640006c244052140b004c040800e014215003410000707050220081e100c5020b1442c899409000e26001080010508104940f00d005007403001c40c22405204001400642c034003492034501c8005400061b0481c0c043c0350b01c610001007144000382121040700080f58540c000d40310700004c6070000d006400d031b81c90040300c06408101d5003200007500c8100081200d112507a50382c40200400d0002660388481d60300c2152060790301c0c0100d0b0074501d145020850100c401106504590250601c108040741c000c0c04082c00c12410b100c060f504010107508400c01d01840f4a1341c4150f400d010440700c886201d111070041c10243c0380010700c1da190070440e2005821a004211600f41d05100003400407046441a00c10900c005850740c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 972647014 1250 972645764 972645797
    0x10606050f0f0d140414010c09260102160209090d0c0308090c221d0c150d050a0606090b0f090d020d0c0305030d1d0309060a0c0b04121205090706 64
    0x5800c8495840da150100c3c1020520136400454012400340315a5190030000d00baa107405e0724245815100000c04480040140c8120100c1d440213000752405c4019201206112882c00c81e0030051080545011044800c02542000f002c101d4002c080c500180417041080300b0083d00c0603c2407076000b004c11a41c5800198030030018003102c1102c1034024203040f002e080c1c510700c0840010803808120405449c0100041e510416101c000e50f91800a10142c000306542001f000665010b10001c0d04016104108103466000207100305480b501c610f0000281640c1001002407030034010740c02140030710504121841309001c00b101602d02c07039241241c0500c0441e01c40d01c003191070b030001211300030101181480080100400800070384503c125103001000500c2d0343d5618049403016000a0240a41007040040c280c1d05040005042d550030905140c0c1e8002910f585108603e0412941503d02d88a02251101a154442d42c1d1142c4030b4480c540501c500d0400d80c081031344070b031a54030807242480040e1540c45d1031035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 972648264 1250 972647014 972647017
    0x20c090c070f12020a1208130201050c030906040b0a090b0711090a02190309050f070501200102090d08030a18080901082809050c09010305030409150e010602030a11010606050f0f 78
    0x1203a00c600f505118074114140603580c3c00c0c56036421164102d0804041c0e0081381f040341c010b072094076804c108040007203444d00190b4055101899014183c042003004000944605000740f00400d10040202e0350784100c0800186000f005400c0300000000401c10f20012079200c4081d0000341d00308450440721038940c598418001d00c904007500c00c1c1d10404540b000902a01580000111030150040d24001460101019103405c480e0040c1808034003c1c5205c0c0502d021107402520f504000400018504500000028001d00c14410304454241000040165802050089c1c921407480e0240d003409030030751541d131400280685030001d410450300000048440c07070034001c0c0c400d800c03030070310003003c048030460041e100a0401c10340c05035107074450150082c0403402e041400e14126a0450051800d1a051041c80c002404000d010401404020000495000b42e01c20009000307018a0300150ba580001c0c0d03401134441c6810709114071659142038801c102060b0000100d60301014041c01407075a0b216502d1003140c55 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 972649514 1250 972648264 972648293
    0xb030f010e0c0d0f060f061d010e3a0f0302151b03060d022808030307080126030a03020307030f090b01060c0204091223161101030f050c0d0c020c090c07 67
    0x407902e40c3c6c50001e4520f40011480d83c6060491480c13600c0c2d40b0b000e10041d11008215496560403044441850200b1121044140d41d100e81c3c546240d0a00c0c1c20b12075003490f031110100025241404c50306010b40405804010022a504040341420510314040d504540124510701c01c035100000000005195a41d42c450120f51080c0d004003210003c021800303810072200101117070024400c01154003c54070480002c103892240050f6964564540c2c2401e2181165941d00c2d500395185c0c0d10700c2e2100580740300081c4003503c60210700737030340051310303072602000090a58119408810415191128580c00b09454240a0b03055913540d0a000240e540c46102040007403000307030302c05007101c015032040603c0ca0b548240803408031100b840c2480120b90070041032040c4c52180c100c54110300d091048150000520b03e09240d10400c005060000b03c40c4108190781055407011110780045200002d00420800c00a00c50b010a080380ca100616080088401286e407407a4058804608018089900410003070390350960f111 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 972650764 1250 972649514 972649529
    0x150403081510021c0c020f0402090307031a25020a03050a05070f0b04230705211b10050a0e0409050f030d0618090f0b0601180b030f010e0c0d0f06 64
    0x111000742600003912051340e1907418030003555000c640401c0710310610710682c007150010400c0a001c010101008000e500c42405680c240c003500400002050090031250002800c809090540b0316107800c6848003600302c200c2c01c000d500002c0c1d950070501980082d603c030b0259410b091031540e40c040040c054420b80a400070003456010001c0f210000c008a24420b00e01842c840d07030b0750010b4503454041c41d00482002203488205984044410406440c061507410a04590f01e000c0501c01000d4203500d40c02d01c4545002c1460007a0f01c190f070300030780e8100108044005451440c040d800c00d0a1520028103900307811080700c2c440c54841040c54240501400034003402441c0d00100d0341c1c0c0321803c5030100c000d8901842b441c000f40c1c1192500c0a855065400391200090303001c00d000e584420141c3d80d004925070040c04980c100710010542d84079071141040528003410155084a85900c1c190020840c0c50005800040d5205a400d05000448001c1d030180c4841111140001c00d03089050040c80c0010725456002c00d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 972652014 1250 972650764 972650779
    0x51c150b07080c121c180f0f020906010302160b18070e100b190305100515040504111303020d06090c0b03040201120603080f07060618050610021504030815 68
    0x50401500500a00c1407a1801080e00c02018030908049011300a040c9440c6040040105c01c82841d06075901c80540b60040d64920f88031a07013980c460100e03401d4552801ca50b00c0c0d22050f07a550540c07402c0b19080b07511030400d20342035181c4520405102401500440e000700046101e1000c00c140348060001c018000e60708030100d80d20640e032560340181305041660701c6050090308680104183c00e0820840b841501e01c445144404061228128028032005045509041c0101070101c1e07a075648900c0c1c40018143c070100103887e181000c0401c000c681d000341030f10003100c0c8200600219000295000c4088a404aa00d0000c0742c1d50f50030544c000d0308118078001e000c4d041c403900119040044401850046000380d803043e01c8031544181c658100c0d110303408017401c142000d229400140241d8002090348502c00e680110306207070761b040410420407150020000107030310f89040200c07a007004100031861508910081c4018800b48800070813510000c2c0c40603007046501d000047c0e10030000110340107400005000032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 972653264 1250 972652014 972652027
    0x5070b0a0e010f17042301090605011d0f18100204080d0e030303040327030c0b040303141201122310061a0904091a0a090b0601051c150b 60
    0x102000c03180103000340400d1200a599101d0b520a580e4203411030031440c0040e403d525107880c1c200004281020103024580006c04a40802ca400c1c0541b81d10548075000119055041603115081548002c8861008240080811604002443c80150404a0801050003904040303240e942402d01c01038598010500028000906007030001d01003032050340c2c44d650141d540701c9400c200341d1244019507001c0d001401d0741000c004104020808400300350000072051803855666542c040390a41503a00c032480d1031201040030410b140d081f032642e01000308115040da00d080d0915104040080040c010102c0f90200b08514008000729200c01c44401da1110086038000c500c482c1425694030b103c51030103802d0f40d007400790001d40c00e41c0d03400492640140e24000c15050004090500c00144660b50065841185000c2100081d41c7c036010051700444000d40e001c01d40f141507041c6190070f6100545280d0400004110790b0499120b003140403450210b01d030201180d140031070005103030000c08176001089203060000d0030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 972654514 1250 972653264 972653267
    0x109020612090c010503040b04060c0207050a030506090609031c05040213050108010b0103110c0a020123030907030c0609050603011202040f0c020c0301180201081906180b033705070b0a 81
    0x825102d82510b00807210004003220044070207000603500140035190801c0418002182508010840b0351284102c50006030b032280007411940d1035500075103658101505102a00c1c00900280e9401040c0d200118a000d0160142da00c2040b0550380394108240c1d03c401040855441d0401910042d007144020b1009586603114103001382295060300c1c4c0401d00e441c506203284180602983c00e080b0400014001c1c1c02c0321600151002c600015a9400041d1004882c0110b907503004041c50040d86082c00070042103003113241107081024503802450a1104e80403040201765542e0007143d06454000400020001c0a0b00c0070501030140040e5401916080040c80c520f055070003d00641c080394110002c2c0041c21b0402e0708200f1304030f01e40f500030340040e03015400a0700d0307440c0a0540900420861400007183c942da810044501002c0d44101e81405842d10f040b10b05515081100c40e1014210f200d0030b0019a480d4034400c000405801c4010024101402000051000c00e10609005110000b4000d0380c9140d182030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 972655764 1250 972654514 972654547
    0xa11030f0f0a1701030803130303090506011d010603020310120317090c13090f06050c0c2407020105091c05120a02090301050f070c03050912030a020106030b22080c01090206 76
    0x100c12001803401d418058043d880c1d0f840242c102c2c0e8201c0c61080c9152562644201c01c466050b20903021f00d0346400c403400000e5020404a40241605000d51034001c50301004d2400694040c1d000e08101801441444401601d440c0004111032481000071402c000a15068498240000600181e420400204109081c021400b01400d80040314400d100d881d0000c401c0c0115002118042c04110300c00c04c0c10800166258081908401481052410680109461441c100c28084000340100c0c80707813656000c04003c040701a4104545000074401450015055a603419140010590b190f81c1d0a80c48004580500220b8614401d80307603c40e10245400c2c10701c10040d511000480380070758071f0000001c13040303140038a415018a40c2aa40d06c1e51f602d486440032100707a00400c10391580422801c0410042260030801040d900352141c002181e41c51446c00c0c41959004014035419441c070703004505805a00380c1c60303040380009074042c1d001c644ad100b03c0c80030342c0d0040c81c404400941141c00003c042d00303c046000b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 972657014 1250 972655764 972655777
    0x1202010f050c0a0c082a100b040c0e09071808070f1e0612020d090f02040c09080c060d02040531140c16060219090b0f0a11030f0f 57
    0x80c800e101036110351040e0740c002c1c070070b40d0110340010307251440307500025050307000501d240e080c01a543c400082c0074040340d4420b007410810f080055404800c0c605d003101e84902415005c280211001c0010b0301034110003610a5260940e241d00c6000c6000004028038000e4600940310020700e03e201481c0e80e01e44013115581d00242c000c50325410281080042d0789140000380355910091541110811842d00509440d0110300031041c81a2980070700c289a000e403060f100f040480c030b01400601040100c28010f00c0106c9200a2542042104411092000c03d900054000b102c80d015140c49079990201c011880c024055a00426032008410b80d0040c0c10440409102c038445080c01c4144400c20f1007041d002c000c13140405403c1090700a071a0003e51420503020251401500010500c200030050303075608022603000001c180340004184562a440035480121074001c2c06560410364500a003c020301c12590160810b84004c0086500c0c80c1c8074061000d0050310145548180610f448080c000100390458000f0f1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 972658264 1250 972657014 972657041
    0x2010c080105030a08090904050a050d0e13060614130302041805060c03070801090f1b0915050909040b060d05070f171903050a0302040b0d020306030c0d0309060f0c120201 75
    0x140c0c00454103140100320303400d0740d03588200000e140c090040103019403c00010000d4800740610380000780410402d01c0900326000b190740d9403104a1042c201001035441c3d20910071303a20300f85000800d1144540028120a00515001079a030b202c0064120801e1500c000f0381000350850b062a0803994030840c500c4c68480c4417171103401900d160b03036222012070030240030403101c0b0340016056100400000c0c440f5400034181180e101000b0038201c0c500d114543c086803802c6090350002d0404142000801807105441e400d25040d032800320b10304000c110000f0007441d40640090840d0700e40c40003142c40f6998040c0e00c0400d065002c4245c400c03040d40c0300d10b1928840d105128400d1102401100c03000101804110100540381074502e0403407010301901c040f40c254108804800c01d040e1b00300700204e00086c129014005160028a015a50f858001c0038982041461741c00280074002495070f1720002a00401c602c000c2e42e2461908018260900204131345001016501034454030246c00e1950800f58103422180200114 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 972659514 1250 972658264 972658277
    0x7030e063706030b0606070506040f030908151f0308030103111f020102090a0501110613061113051201051b03070909050a0506030f06010f180204050a15080c04050d1211070602010c 79
    0xc1c2d03411b00450380b04d010401009600540d00081c002240c41d40e0f49501540246001d642e41601d58031460310704442c00c1ca89000c13000981e0108111070012000c508070a9011a00188200f40fa5598420a901042c04000c06845c00c0d01c404640c9a15000c070301c54004080b0401030030918009000c042e0003580300328105030280c000f0000228480d4001ca1070300d0b0301c58419000411681d6508220040c60042035882280d07403984810030650100c80101c00383c04c07001400d403c9020070b10f151404010b00072091555510b6180d0500e010000e440b411f1031605036584241071561903983d56034440442d00d0310403640216406030f1900c4180082880107600c00381c03190b00d0590884034001044103015680c0d6209102d01c409080b2008024000e5061407100034034205603450026041c651114009001d00c03810f40c12200c409186030382d0304141107600c880810741111040e80d40728542070516004c181204a1400090b02c903515805800d40c26600c952008120701c040c1c00b058980094035620020301804103801d4800000e680d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 972660764 1250 972659514 972659521
    0x12010e01141e0c0f070c150f03050108070803042102040504110f04110f090120010c1409100309030c02040e0f1203090a11130e030406030507030e063706030b 69
    0x9200b803294010f2a00b01c03601030900780501152205a0701030341048441002c80c060000ea041020700e184500300e090358880c1d00080d00c01403402400c40e00305a111842503485a8420801120301000b150180e451001c460300c0003000c40005008464038050009410520b004100010703c00440700040b41c800c0f049500e59030703642c080070810041d16144076411802480802c40c1a880c03030306000003001c0c014018100b038030081d41e0904000300d180c0428000041c00d40d44649074044142d038416080340c1059400d0014500746500751002c03842c0b0a86150f542c906041e540c817052801d05004251540c080c0d40c0c000d005010303140b05e51200b00e858100340c550551769031003899580703040030030b60750140c900c541d0b208001084001c005460b0071441400f11000031380c0040e00880080003000c604d0156a150500e054011643d40e4540074004040320b000400c00d6080501d880c401340056079003c40e00c1a04a000b13000709403c0d2000054411801c01c640c9100c0020f240800ca0310141b03a00c250b504103608480c002c0201c401103a8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 972661870 1106 972660764 972660811
    0x10906150f091403011e0203100e0f0c030a0f150302010206011a0d15080a0302010506010f0c02011d03121605011a1003200d09052a12010e0114 63
    0x350002300f00003010b10007050301c60080458201900c4949030540c05c3d0010b02130041c01c01c080201000010607180140c0750499169205901001c000d40d40004032131103004202440201e0140c001d040c0002950007a007604082c4642e0013100852400e0038441010005050310000042580c04542c400700d0740c3c1d1410058894624840e400000c0c41e4100400054005e43e42c0107031010401141c03910060041c0d1303100ca601410070210030302c0300306641e03080400282810680c0511350500a4003203942209468102108a40d42d8003030002000705050b04802c8110200410f00c000760082e490340b0088113220311907403141010400000e03500c6403030b42c244084403800740d000440c080500303500c1e0182c440c103120090200340c966102903ca409a80d002251303a0b2200b18000704000d034840c0c1000707807203502c10b09803e4000320341108240700200320404405407035010f881c80640c0c2904034620040c1c040a50203 = true := by decide +kernel

theorem cover : BRFrame.Cov 972482014 972661870 := by
  have h0 := BRFrame.cov_init 972482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 972482014 ≤ n) (h2 : n < 972661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
