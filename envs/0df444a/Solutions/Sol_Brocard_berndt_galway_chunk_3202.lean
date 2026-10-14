-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3202
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:57:51.736785+00:00
-- url     : https://prove2.me/submissions/f27a567e-009b-4661-a192-07cf0f564cef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 575719424 ≤ n < 575899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 575720674 1250 575719424 575719447
    0x301060813111c0f150506100c060203060109080d021b04180209060301061809020406050a0501080a0203061c060b0315010602030f0c281707080403121101020f 70
    0x1240d44440160a819245112680c0c0c014401c1030b88040e031485860314000c0d07030b4190000c002c0440c89481e400b030300365565452589000c0d045d0f0194a90300b014002d103001e00103501810080415401003031199180442d484283d69034600940001d8241d0f410080c8800022881034020403a85041c4c080701d400610382441ca02d9101d560b402585111140030b141440b0500c208a401c003402100100e81c100d620300700d55030383e010200c1d0042406500989440010032030109070160254403411b81e031402a1814021551075030b0501c0f03020310b4584191070000b1038100c000359030f00000da40038541000c002800d1054541c4c1007460f41d281c50307040b104151050780d03a45204001ca40381c00c2110b01300e26400e208c5040182c1d071401030083d440303020b044030140340070780c0005202d10480414841321102c40e40d10924641d064140c00301041480411000443d0885442080e480409054130103030b803d529844034170203103001e08503a1031081c5003002029070000d204a100d10300c081d0362300038009800c03402c00660f40700303840701c000314070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 575721924 1250 575720674 575720687
    0xc0f0601050d11040506010e210f060108030306010507110a14040b031c12090c2912010605070206090a1e0e011802070302070e0c030a1b020d0e03010f090503030106 72
    0xe1140030500c9480000401d000c120010703142003140c00003016070ba05001230303c03080600542a84c0c032040345103103041410b5914080c130304044552001c540300c29180440084e60341000780141191a0320900c00104036600c41c0d8010130140d0300c6071810f00d80030300189000c2405480b0796044401c40404000400e525400c283c41020842c2c1c100b20020321485403201c07802d41e2002001c142c84410000c030205079441120f0f00e5082081100e600c042c11200b015900d80700b4a2155050401840c4610002d0240960000380c18058400c0200e003050040c1d6542d20f41300c41910258400c1004903000340c0705110301035185c1e551005090003001145c048510b5034031920a512025105500035200e00161880140300040e14800740a070440ca100d00300581d0b4078280d04050340750031000d5221031009465842000107049500d409140941e0303100205100340e00341c410020000e00d00d818912030050307008040c10618544201f14450070500c015000262460702c070002c610550b0015403003580d5551002004100c00740e800300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 575723174 1250 575721924 575721929
    0x109170105240121150905061203030115121b020606030706020a03080606070f0507030609020f011d010309170c07030b0c09011b0305040506030f0402010f050910050f0c01020c0f0601 80
    0x51510000c0302c08000041d1031128a081950101108030740210007401e40342e4020b03884000f10480d144103443d5103040e680050002200d54901907a01e44400c001d040000200381c9040e82d043c085100100c5501403400c441280c1d480101800c403903242e0801403041c0240c00c0942008800a5000d004180b8144003410715145565108070110b40c00480800c1c0400e0f40704c08000d0300f00d80110307003040c0d45512a06120403d208501000740a90242850000410034594040340300680709032844000c8074407020045d10590387d4103091802c8010750803201c50300c2e0b43c401d5000500562041d0307203240c0b003444001c2c458543e90304540e4603410680e1126000b88180242240c01c6a4445166184203280c160070b0300008285501c03200c0f80300259a003030704821003018040e006480141002419664032490114481c00602000362030507030208076803010132100c9510900c215a84808003801008a201162908440650001d021542200018020205034107420f000800c4074003c030200a0020800405c002da0500006a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 575724424 1250 575723174 575723221
    0x206060a0b03070905091906061205090318010c150c050406020f030f0412050a021c150c051b070b0a020610090c090b09010c171903050408090f0109170105 68
    0xb07008114406611114603001e8420566104d955a2500300000795500d40e0b00b4a88040541003d5010401a41c003521454112486000c107002a80350103101646a00c941c140356102c4d9501c1c400041d4035940a01d0301c0d00c1c074030380c802c07680c410b10034044404002c01c494480031040d0014100050400036a6810006006460044805180340400081c2401c200d4469481a80441c000c03040001d0140201481050745264000e800c01c0304034180321141d11001003407044100d990841513000000d608410784200180240f60f915075600d080040814000680003090024510f03205018011840080c2d40002c0c202085968005081c2c0e0300303080d030700e850a440147c0c110040c040d281c81c0c0e0040f1410b510446007800c43e81d00c00442603448030840c0c012918400c02d001e01803c14512a044414000d8a01004026540c1c1e00403d000790402d5020084082d41c200b95000b80c050182441210300c1031803e0600d212320000141419040203a413842000703061810350325818923030f954820400088031060310030003804885a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 575725674 1250 575724424 575724427
    0x22110313030c021f0302030a0e06042301110d0e0d0809070e0c0c0a0f03180e01180204030b07020c04060501110a0b07140d020d1404080d0903051204030206060a0b 71
    0xca900380810001150040d04021400c0d01550a540b942d810105804103d044100041070702200060080d62050750035807000e07807a041e031800c0c40d030b0310124142c0e001c0e55003d03080c200174140c00d20b140340440f9058107845009540e10700155060007c21b400034801c0c5c0390440004180c200307a40c03912a090654180e1000f0074490011304100440c0c01c0403920009031031078000c00c05456260823500801d1405100d0309940300e40b091802d25001e0244520f01e501015209076100902095003000c5029280da4a109031031548800c00b0060218105c039981c0080038001c00ca50041c100f5aa81d03c0301d040e0b00e0f00a8401c2400360b046008107555604145c024000601001e00b032408035414044c440d10350743c08400c030010381401401070210340307410700c24440e4030f40c0c00502002030b689518446014030000d44c00502c80c0b0708900e1801030320b0800d400c40250340c14400d90708010f007181001e030312403801006003802060031400c0080c100200e50040011502c5580114020f40c020310081c9004014040251200c3e040308401850 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 575726924 1250 575725674 575725681
    0x1d01060506040e0c0d0c23040812071e03270b03222406082e090b0f160c0507121a07020d0207140d020d0809221103 51
    0x1284402c840c100ca440c0031120205964604101c41540103100101015a007403501100c0801e9100f880d480e9884403e000c070101040c107100441010784174900c00c1d41c0494001c00707a0030500c5841c00001e070406c9801811003600389840c0380c40701d26400310169402c601045400d1210410400c0ba9001c404030090781c0b040ca6190f5074100035445019000040001004008004030004921140840908480d5000c5000a51030300690b840c40e2070750b002401080110b501c0e1100000f94148000f8a03035a100b055605001c00100000ca00c0114407106459103541c4552140786001c002054200f0031031107500a0340b500401c1c2d0421000c0c410500c0301c0d030742c5d0210410040c03803040b0000c1400030030104216905040c11415154541c40c28900e0034540c900301c1c24001500d0010030400d940c0103e0308030100d110329400d80c1c20440e00d0f00242d20b031002c00b51480d5034020000c5810140113040c04e0740c4000b60b041c0a20502030030000342c040041d150b4031500d45005454800b030701220f048031030203009180c2c0e410000f400960035843c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 575728174 1250 575726924 575726929
    0xe0402030a1518030f0f02240c1201060c030801082109010e0d0501050f0714030403031d0f0c10051c230a0b01021212060405060109090603061d010605 66
    0x110345601070210803100381d0200d10b209141d0f2040c0194030081e00566501419418082c0c40396080006000c00720f458048040300d198404079001d41e03000c11001902262100e590034000e85042c00070032030840c1c240c04000242c0c0d40080560141e0080081d0f50721141100218500280f0005042e480303002958440b00d80d50b241e0901c0e0f5011119003940016185440e11101d0004894a000e410700d05500502a02540e100748003043d00058401c4090a10b0f81c030391038450380412504400d502c4151408400103101140000707100e60009641c094010341000015104084c10604084c0c0301c1a030920701c0d50041040c0e040702d0511095030000707100c00341029420924800f060000309030b05e07501c550000540d6146000c101c422649078400b040706014110500d94585995241c0040012aa405000d8411480e091825090b59001c03100c0c2c1a44d42403e68000792140c0080c04080e241c0600400c0c14080941c1010076400074a110f84401540110000300e41e8075915035901807410b90b030720040103141c0d0400e4014041078 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 575729424 1250 575728174 575728183
    0xb0d09350f190e060d060509060307051f20010f06050307140906060f031003051510140a05040e0709050105040c050f0d14040b2203140702061306090f0e040203 70
    0x40b802c40e4102980d0081c9420225468141c9407240c0f40d00000c0841c1942c030b0301e41942e2000e000d82d002070303494600603220041019500d01d080d21600307a1117810280c001002950400c3c1c021070031441810b00060303810000300c420092102c9240c02550581d500c118500322100c0c4c0b0700804009000507806080042c1c142488020400241404240074010350740c0415550b40b6984101e851403405d0700313040c544a080911440b60000d426100669152160711102c1043e43e02ea920030a0003002c0ca2000640c101d8504031000400c1c0103203aa4240c0d00840e01c0100007616120b5000d44840b54503080041c1c04858109604a42154410380029000343d1401d1419045c0603000340441c1c80c20a0b42014081d02c03118401d030380b070b00038211029549030441795031030600c4100030340340c04070320700614283c14141901500001c10044100302124040c00080540316004000e40090f401401d4490000e030025140c08580200002054643e0340700100041e4500030804c0840c40101c20031021b0512120060a00d05140e00042d956 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 575730674 1250 575729424 575729437
    0x3060106230c0a050601060206061e040e0607031b0e13180c06030203070305070503091203190218010912110f010c06051612060803040b0d09350f 64
    0x103101c00c0c84500408440d01486001a20316400c590366912110803a0381601c6040c45602112503200f03003400440c1e13190001c03600500c90b038400340035980301c0074001c0d04022142e11210342890708a5030380c80240f200d099040c4002e52041d000398502040400c5521021007040440602450800c00e440e850403074942d440701c0340d50b405408480300c04100c0300070150700002e800401220050945c00c1e0400d0000d080c3da0141c01540c4202180c0e2002c201d0b964564000341c034079101c115105401904115131280040a4440142d0380041c060100d910414200301001000c07a030201400a0101c01c211001d00c01135a0b209005078041d008551545030420420390752201419040e00c80d851141c4c540e0807000744940d00c1001c96210711030b00200e0600607030a00595910903c01454180c100103508180b1101c0058100e0052004032607444c0003d501e010310f00385030700c45190003c0d0070380e10580791550405000f048074402c01c3d07070308a008010307081040e04500301d4601d00109840d0203111400303024800351500882d188140c919 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 575731924 1250 575730674 575730677
    0x30c1203140c0c210c040506010203070312150914010503030a020a060b01140f0d110a0507060203040f02040e0708100c08070806130509010e12070b010501050706020405040501030803150a030203060106 88
    0x215044080480c07030514000350816604444d03401c01c0090510122071011680c001c841013610324a0030000c0c20302c81903d8003140c05a0151f8000c10041d00000d2088a4a9807500264035000030110111402800b038807650394040c85205d07481304c410f6421a0002030b115401854118001c51a0140d0f4840280d111402d465021f0f01d030302d9980312030f0b1105034020140f40d00d500b120800c45581e107000c44150325100340c1280088a10300c074900f0f0340c41e5288072090021210400c466443e0746080520a40e1354034044d500043c02110310301d51101c140001619a03000348401d403200780c4064850705040030803661a0034000c20244845034104003070441601c1d002020f661b00609107251552455880c40c0100c0c4030306140030186d07035400d0700e071804003c1c61003410351001802c1235a4100751402c001060a82c5040340c0101100030701780c206090010013603580204000e04c0300d03911481c800b6051030b5484c40000c048070004d92083c2c2d42c000c000010045100c00c0c01000415085040300c050744044e080d6000701e50781e084140100340 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 575733174 1250 575731924 575731927
    0x140714070303020c01090818101d01020a050102040803042c0a020703021c09260d1110050702070302090619232101110a0f0c081210030c120314 63
    0x10107140c800c0d0100c58011000100910003021a4a0192083c2c0d219076510390740380307080384074040c540e150001180408504035907480342d8030400c0c00394148000440c220024150b20a00408400180782070002c1d00083c46244003640d141c61030290707100390328501000307201181100f040c403001128202e0120349400200c180c00040e100c184600d4240d00d08007482801030405c3d02200da41075201944071030004142d55880f58624050076400c9084c0110b402d02c6402200305401c1280c0c0c0b41c0c821031265110744202114001102c80d80c490b026402c50858109691110043e00072000500c00d40c14400051504114140c0c0d54507220f8041d1440d0208694281c080d0341051004240801404079501c98240c0c0f1142c1c0c000d00721843d0744001e602c141040341241d20720304a55401d00c03000080300040f030800d48800c42c1c180e0b1100c1c000d0100c0100101c0d00b00c010007030100c0e0003020a0103480baaa540c60b84034188a0052103802010490030340c2421007210b851544407111201c0511010030011b640103028040e101c2c408560365 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 575734424 1250 575733174 575733187
    0x10306061d01080a062c0c0f040b010806150426060105150316030b1314070c1a040c03060c03050a060801050c0a0e0f10080f1f1517100504140714 64
    0x20400d4421b840110000d03460403030050705034400401e02e488942c0041b2142212202c03500140020b9401c0055031501052511000a50a061098040da00841d00d2064285002d4a03800c007500002560b0400e5500384d020750701680034040082040d14050001103507401c468401e0107104c85c08a110080c0b103050aa160031400401c0540250003401d10300500410b8a1211111000680c0c010321415170000c0c954150b001c08074060380d01074490200410780000d55000e4002c001030950212101c05801191885c1c42d00c000000840d80c5807194240084480d6404940c60801c3c40030300301580c01d0380d00f05101a0f4540740902c04034000701c000b113805400c82c5007441c0520046000001d101c0304030100801d0b40000c41c2408030300207907900c004050700c240c02d5103c130043c1e42d407505152030301c0c5440780221034611510050070601a1400c2c6030341c64081140741e807910506803020403050307407a8035009940030700f04114000e20600039481c240c0114030241d00a070012002c1032411420041c54519400328440b00d440000508 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 575735674 1250 575734424 575734451
    0x605041e050709060e0c19021f1a0d020a0b030c07050a030905090708070f12021b0102031f050a05060c0c03011a0102070b13090b0a031208011a03092d06010306061d01080a06 76
    0x125504004d500da01c0d45601125003140019060480d10340341280d14000c41010070703151000c52f14202c40e4019100d542c1d180c2c104005a0b005600181100d40401300500c005400107804104201e80b40b44256101c1404515080c00e00c001460f000d002e580500c10604100b1113016403140b280c80c00d40340c4524180c80c01c0c00010314803100a02c103070140b048815135100150100c02005400440c00b9840451501e20344011002805540d14054010141d01501d1240300300402c1c5007102c0a0302c1144000020303281c80004200000c2e084442900f0b402d09040300c00c900ea4440d079a014490b4100a000da50401c42c034142141c4190b040302007142c0519107496580ea40600c4040d200c04001d07201455005414000004210b500a0001d100910800400d9814070301c1041040c02c202c0240c074083c4003400005d0000801c049801c0030406003100c4880c03d2400c80040c4092010010004280250301032000014018149044045d00d8031606a030b070350070701c84520700411040600090440e0304a8010000068100054a9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 575736924 1250 575735674 575735683
    0x6090b07020a033504060b240405010807110307050601090f02041a0a02120c0604060c030908071410020a120507090321050d1d0c0a120605041e050709060e0c1902 71
    0x130700c1c8000420311410042003040b20b43c03102c584c5502c1158072004002c2025005070444a40711136050000c5070510040000c1d5005140301900410320342084005c1d0811389911611315000500c050f03075950f101400400c0050500d1051071580a0045d906628040c00c08110203180090300340034078a084000101d800c41c0c60702c24452610034130040090b00340e942444107041aa04c103001d43d400c1c0c071081c0c64403188404441c002d114008456034400550b5081080d103454000703803402c8010700200c4601a842c0c0c2c1e4403d100052004008043e21900e0320703548610540c0d101d00443d003000340884284000381609101040200c80481070080d0080160302d9a081503010403034040c00b652110a1040b400c00d81c208002c008210303951060f61a00a04584514001e0001c1207801c00151003000b856030f80c04881c14012070340c99001194028098940030007144000070840d1090328002905803243d41100c2000c0c0300300c110038020130004201d40c030030401007800c0807a1040a94403035252480502c8103034043d0024918000e10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 575738174 1250 575736924 575737007
    0x1b03100b1602090103050a11010201050f0105041e051003031b03172d0117010c0f050a020a150e190203100203271f0603050c0108091005010306090b07020a03 69
    0x10144442545d507032a2141d940d031b00082007282d0000c00b0b503103007921075403051052900c01d4101e80080c40e9035910300424400144003440c030f914852521003d081031010030f2406503902544456060303180c0c492440c1402000740e5122100d01e6240441000ca0001103170344002c8201b108800b8000c80701721901e89002a0100c4a00c4046900141a074074885003450840120f0f1203040b1800d81c02c00000d4081402200ca02300c807514840c1c040485c80840c01003403002d2180c000f8095450003401110110851900d405900800e80c003c94041c194803420504410b650600c08551526154044e0002d00c000680c0040d403128880b40b008003000e0360110019865540d40040c201d201d503030841071313428418010034240e6107900b025003406180c44011a410068641c2a1144000b200c0d040006002c0c0421000c0044503216009001c025035032081a81044901d942449034a000307612400c00007602c001c652510030004500240883c0c159048550440007294102c4009900c03c0318070111a0048100c169064040082c41c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 575739424 1250 575738174 575738179
    0x411071b0e0a02070b0c0a170601090b04080a120c0c180605100c020415051513080d0314060603040b1305100e071a07030507141e0102031b03100b1602 66
    0x900645030b074150f00812840c0e0040c5442c9100e50303645402040148150112400042c0321001403000c5400b00610705600014145019491103a403035003950100d070015089181590000c0078001d0030011207d541c00044000ea0a207444520b02a455036405002d0501c45e001d44e51100600304a245040c6030700060281c48000c01c04885d0500480004001d1001e81004078002d0b840c1048180c41c0c6c071180d91000d41156030003400c808040041c2c07415400d40390012009180c060080f05408208607c007400b0f200d81d080004e40c2c0c0010510760000740c1d142c2d13990010f00140d0107480c0400a02020403070100b40310782e0120000f5a451802c0e2518540980f420083c400481c3c0e842c5e02d04243d40d41d01744c0d80803605c00110303100803030195020f1000d1905022113204451004012900c00c022444c00038116042048804140d8070035a900310910140b10100070b5104120002141d50010803c540e244c2c0c0c1e40d4415507032155500c003030b0b40cc614040c01100b025107030034050b118428030046035512892050650f142c0c000782d4007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 575740674 1250 575739424 575739449
    0xb090f0d0302010b130515040b040f0c020d0f08010e0a200a11010f140402091008061306202506021201030302070801020703021c0e100f09050411071b 66
    0x12814024002c08400034001c0c880c8140e42c5c0003501d03e40550051600400307504d90003502c0002ca041c00c01c4010107410381c18a0308103841c8c0840c4a00c40704148034031413000040760003421000108107801003c00d0b04110300141800600e00062083c00c0800c003003030f940030b405c01400080c031400031011140e0262465000024565002814501580e401880b00c42c0100403180240034070318211f004902a20600304091403c3c5d40351600040140c507148a003190400034007070544d0b100685600550782010001c54110741d0082c5c0400e5800c08121042c071907003440c5445a8000602d82101010100c001d1207140702c1c2562003400207030401e0f9115810148003504c1e43d0321540440d500c504201102c4000c4400b440141c025005079a40015405018000c44503550390540c0a40b0b0300c0e541a4000e0341c142d002442c1c4607030070040e51b0740e0707075003055200c02d2a11074002c41180c88805450003207550042103039107103402203070041d4149028010348080507400d603200142c0c442d210074080da4135104900846207180d0b0100310403000c1d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 575741924 1250 575740674 575740699
    0x12020301022205011115070c0206160303090b061e13110c010b030705031b040203070c2f0a0513180507030605041a010b0a0f02011b110d02060f010b090f 67
    0x584403102d108880003a21400d184186800207240c44000241d008001c0e00040000144581c2c0314002401c2c00c00c2c40100880d00b803a40d841c3e100c0080d054864000c8010070340c1d40a000f82031040b11000c1951041c002c8600c0660801410300c0c9207041d22403d8507460060143c0c80400c00014225005203000c0205481140c0d107071000c4045003400b070110507103030070300030f0241c0c450200301d605000c41c14500b000d101d18044800441e03004280402584020700380c1d0108110302501000144503c0d44854407072441c1045400d181e1004100b400c02110300f03141c2d0780d124a0081d40304005030f03150800070080e81e18002100240d141d003e42c03042d0481003200880240f9034091050040100812503020314040c3e806819035500d03d424120030110241000e001d180b10000050180a420904c924200c10300100c50381b00104500080c00c1d405c1a03001004050900414690b0040c665910010403450f4a4001c181c07000f0881c0741410419400510780601805201c0800040d0000094840d5184501c00000180c4502317901807 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 575743174 1250 575741924 575741977
    0xd1704050d1101021b061f08030f0f07060f0212010e01180e0a021c03080a0b0604090506030a02460e0405030f0d0c0e0a05010e010c032a03020f0303101202030102 71
    0x140211919010b14905415047c2848500d0402030140c6140d50021032500e0079141c4030603559040744854035161340c010415807000a90601644034040107401001d61543e07440c248444040105030845080e60000000401240c008104c4030704808200103400204e070804039043c84e052800f8464080d40210f640040901418520140403840324040d681d03030405030303c4520f01181078444800d00030794840400d100c14404001b103a444243c201000a00b2500702565990105100302d036a20081402401c0400307524460070003000d24460100300c50030001c545001c00050704e1140a4690241c44a0001070600142c1003007030420860340944510b04d210741e1034079480d040041c05000350b4000800002c0c49a00c0e02c848505008007070b4019201c05071541600c0380da410004480508003a0020f400304291220010380c069100503941e07080d401c0c40030000030300d08d0540c11301038036041a50400340350319802002000107000201d0000e10583c2c1c2d40003028860980c503800000c1c0039000c0e40391620403000e4140054003030b60 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 575744424 1250 575743174 575743183
    0x4030506070e01080a140c0a1206060201020c240a0513051501050f06030f160e06040b0702150c0a061109030f0c120a03020304050d0f0506090d1704050d1101021b 71
    0x80b900360398540d00359690b00c2c0c201d42540e201d58a00051201000086550319915101a000c10990781c50200d0340d020b9911036180036a06507a116002507507000400c20070440043c003665404080c0c6007180c4c1940c03072440401c43c0302e03000020006002c4594404c04202c2ca6241c0b00c84417406650482c0c1110300e14000e0500c2d0b01000d00d0284186441140e902640c0000c6081c407005a074841c100282070f034405552464003c211a0589001800030450658111540e9580780b80142024200c00b60700c40341c0343c00d0700d44140704104e001802c2d00030711407400b4070445040740c100040011065178008004541207003d4001c0f08500d0042444090381030280040342c2e001c01000181d20b080020040f20030b0314034850355040d400d4481220f0640540140c004103c01d20081c200412a84849840b84280c0b1062460a88550b8142102a290b000f01354001a00c04888598404840c00c400144455084110304140e9106176461006080c546c0034007103038611994a4010070b5041c1c504076450102c5ca038010078060324041c5d40b42c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 575745674 1250 575744424 575744447
    0x90f0803011d160809120f0705060a0519110d0516030f0b030d0305040c051009061103040b090112060b040b0405210d050304050f010f02030103020301180b07140403050607 75
    0x14980300700c101422044030425954040c81c030043c2c542c034061601d40d20854450710010b040441a02c5190449040c10150100401e4819203002c0391548030251458954141600903010b4800d4a090405020440c1c401c400f0380105016407820026803404143e4540d07030140545410f204a4618100402501e5444008003204529955a0400501642640e0b81e41201c41c03240155400d03501100310740b5803190007a4007282d000381c000c0e1075031156141c0d00da0001d0380a5407110800c2000644000c81080301d90f030130001810015920340007950600d803d0404200c054003a640e60141003000f00503100314078801c42c2d40014040c00c0c0c10100c003655551141e0003441a503126204d080c0c0031700645032140d84100f03070100b040b01c1011840d02c090048040544000c648e1500050400e803282c1c0640d40e01040c071600248100100031186d0a8050f8981d855801010708548008500204044201c5001d0000490000005920841d58188071091914030758200c1210b00507a04014400c1c452076040c0490107400242c001403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 575746924 1250 575745674 575745689
    0xe07120509011118030f190201090b040302130534020c0a080307030f050f03070305100602030a121503050601030b040606050618060d0b18040605010807080c0d0204090f080301 77
    0x8640340c241400342250728082c0d0861406001340301000d0b8021452404a00c00380300202119803801000301d2640c18060f104041c05004a102e510000c11544c00004c040000c00d511214681008c0c41c3d900424031400410040720051a618000a04583ca0300302c841e010545010351a024912036942502103103410341d0741d0f1000503128071443c2183c02e10342288220165416000514107012060398203840d034113198055901030003c00c0c4021100b802d4801c019510898660768041214107000384500c290f04150b402100464108206030043c2e5504104900815044004001a00303020714801c600c00e403c0ca6040100300d0700907600000140407a102000340201d015507010003200f56514204842841401c024a10154050000c80418942100070f03103065800210003095a0141c403000860204000003d82818540d80c82072006105061107903501604120300103020107801c2082703483d5109190024144140940d20543c021525540c120b141100c1e80680e401800485038a4150b2460b0400d004411 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 575748174 1250 575746924 575746931
    0x90a03240f0b030715030908121015021e07050a081f06050a03061109040513030201140919080c060108100e0a020d080304050a02060309010b1306030308060d0c0e0712 73
    0x1d84084a9101c0c4040c800740040050502d9441c118041007500b034070380d108000b0715513034100400101381304c14010b000c04003428001080c28900b404205090072260b8200c944110b05694000c04041c1e00066030402208075044c102d0f003003800440712607242000c5030f00216040a403044002544001c001200006140750409900c101911450200d00301c84051040360740c010a1141c3c00c00209d0710380d621541c400320342c080d031442c540f02c41c1101090075140140c031440345071000d2403010b1082c9503080c400c203480d030480340f00c0f05c1407503003481c2c0b50751551030140000e40600300c0f001000ea2000c01801d102147c4480c00080b080ea10f50b50b0f9140581e54035000d41c00c290024003400c2852402c1039070340104000980c2680200750024010f400e85950900c1d4000900442d5039200700310086015a50740da000c2e52080802100100700141e001050000001e807180040c1842800d02005100094004941caa80040c6c00d658000c040403050074090394200155000680d18040e40042c818500e40c02400360351100070309841030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 575749424 1250 575748174 575748191
    0x30606080c0d080c190f0201023009011b0b040b0c120f0405030d05040b06011106010506030619120b04060c050c0703060c02070e0c030124080408090a0324 68
    0x259140d601e41400749a005014a14a00020310700e0300203410400720f14003c503042d54245c00c810700b0001030590025603c600d010040d031021036030b0402c840d2103441400c403000c411040c1020030400c010301081410450001000c102c0300c1d8541d1050724010000c9090170343d840b10602081c1840003541d907007520305840007903075000011040d0000c2c03011288034402c0822050010f41d980180400b6841014208980d41e010410110074051414025079000b640124a541c8190505100240070032070080301c01403a54010340010000380d0703240c1d015268440c00640d12074a04040821001c501c14040343c015201c02800300340c0c0070b42070140f0300703103ca0b03c9148665400c0207003030120203080e100d43c05858581803090703011040610020340c1d030350030140308004580110746038680c13138610540d40040c003221140900c02e4088010000c4040110340e4181088018120510800c1c1c2184e0080022030005c101400e03041000075400310a40380c545007130000359001580303080010324010042e0075010f0078900350b0317140d181408070300f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 575750674 1250 575749424 575749439
    0x6151a070b0703150915080d020c0109091d032808090604151508010b21100b0d02060d0b0102100e150912070c060909020a09031401060b0f04030606 65
    0x1210344840c0c02900100c020764495804901070700c0094881a00e00c00b074150009110603444c080c4019030482c0d00076a0400e80c6c10016050b203800000c002074011907105280342da044e660807015550540303001382400301e06030392050b01400e400300d1150003204442c8400604160425940310508402c085280c0c02200c03801e1500800303d807040f01c2614a445150400004500090b03200c044808000c4143d18000c44c221420000703108200384240c0c00317804241d45440c05c8070554940b00c0382d5541d00c025001d140c0903039103410140480d600c200e1422405c05840c0e490704080da071580c3d080100c0f8041c80d8014203150342c030701e554030103040541003460706c8a000d480b9001c46c2c4004070340f582c040c03501c80b116114014014101110005640c050014003040e01c1401a041810040c01c020402005650b00481e0540e1074980f801500034182c141a07071150310342500c1449900e16055000e40c8110440c4d4010f11a0030301c0c0355071301d104a401400d05d9030042c99402000503024504a000318081e0080f00d020720302c2002100c1da900e43d03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 575751924 1250 575750674 575750677
    0x512041e030b0106110f0d0215010b03071b0305090a03080a080a090302060627040b160518130b03102712030903110a0302031312020f100c06151a 64
    0x70b10303a40c000070040c48035602c140030710801c4204007011640a25540c88046003400000b0035580e0050300001401c0700d05034004503442d4010001154851700c0c619100340700030311045087e0019071003c540d81c1e10700c40506110b001a5000510000d018515840d600c3c6000320240c1d002c2645400810218000103c4480c10340c803519a0f1190035402800803030340c0d10001c000c41c080c4101d10b854100c225851090102030800c0140c00c1c401c0344140b0b440707282400c0580121a92120300d20703c0408120080001034484c282590803207089050662300071144122022641014080400c00035416200d1244c000c0c0c0a40e40c1900180c6030441d0400b040a41950b10b549044502c2d9074803400038207052071101c0303c4c0d0740d50342c483e40c000d082c414000d2070418007400da502c0069080072500b40e07081c0e0059202017201028580c510020350b0082c280348612900d1020f1981c00f041c42d070b0a0701101103215101040200c10242d00410406040c254402c07400c200714901e01700c1e0001a0302c0c05004029145080b44000c0000441810 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 575753174 1250 575751924 575751929
    0x40b01020a0c0603021c0207050a05011812050703030f05190b03010209210c030d0c02030705010f020d11160602030705010b030114180703020d05030a0f0504050d1b030512041e 77
    0x30703402c1e108074105a801c0e4040d60000d0350302c4150241403030b40c1202d501ca441c030142402c90320401c060f01081415003041d5003922103e84104240c81080c495110005504440a45509255080981d20303000a410190000c00c40301c2d1002507900c0c1440100000e100c0d0001081018840803001080046042c03c2418201d00807002c030603400440315440102070004141a20840c0c41910003110b01c1005039074003007402c20402c200c1c11000b14401400d010300310b14052011402901082c030b8019800c000c18030009540d0841d0086690a000446500c84003400c414010304214051000401d51526681c2c80000d5480c0d01081041d521540390042608051606010310507002400030b4024850385c84410084a90040354050400288148980080161180e2031600b1019026102440d25202c5010028080800071b244031810440100400c0c00b484c1e0310381da5441a001c0e0403a10318072454400d80d90000710311142da08050800c2c420f2120780c1d0500240c1c50300500c117481d1b00380c42c141a8808840150890b044450 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 575754424 1250 575753174 575753183
    0xf020303152101020f070b01050d02060403060216380c03070f120c03090210032c010603021f0f030e0a0809010203070212010605180402060d1d030301060905040b01020a 74
    0x540742040c0e00d2520442d210700d030780c81000090007000301c14404203003241d1084d0401986003401040050502c607420558034010907080e52600d0114100380d00060992040307000003803100d940401c8082c803415000c0170038034081d40d00000c0c41c11380c980200316480708802c240301d00008a900380030003282c10480f889021030003404c00c14001406d688400c001610b1070310151070881c0420460300714080d045c1c4402d004000880c043c03a240000c18504500502040c0610700d2058020302d420310a66046544600030007101c04920300743d14441401c80800c5180c007507d002d500181d84850306550341e0041100c4401d1086421429844284902407031940075007c0c2c400c4034622100d19040110007030702003000f010040001e801c0502c141ca20301600c6900003003010600c1c90940035180e540340750a00142c00c0040c99041501030b00d100da02403525088c1e0005030780c0d1282200961800391074031b00e40244a1080c14840301c010412500382c86d00ca41c0c6418000704034002a01c500f0344620308090381d124081d4000304100240a070003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 575755674 1250 575754424 575754451
    0x100204050d170c0d0503070f0206071202030c0d0905010b2b0f0606090203091006120206190903020909030c010b01050307170711030d0b0a0f080304290a020a030f020303 74
    0x142d1101014402e0b600501948a40100803d02c00380000344050082c40100b43c5038203459040201004000d490b440403c6002e65104100b480314085c1c0090300b1941c2580742c020090713580c0e40e5068445101703001e0301c14000c0b1010304103e804410004103420030a00e2040a60700d002034000d9041c940c11039002c4c0490600303244001d484005000c140f0400340301c90440e000c0e510104d815540c3c3d8203c201203074030449139480d0942041c00503080c4001ca900034803008000c013120700c4d4281501e980002d4a540308420741458030030322000c0118039150042c3c0403100250b400800d0a00ca6140413010315440b42d0100505102030352801c860300d41c0f298018015070780100d006650b242100d0320303c04108140060090306010500405d10080f00c1d4600d0200002d1000000202002c100360512030244803403000340b0380040c0841d109600c02400400400410f1302c0464644075021a5042d80328201460080441d00071905459000100340440c5038001601d41040c9209907101d82c540105140d0480e102d0006030f40c0031511521 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 575756924 1250 575755674 575755699
    0x200301030f020109030c0b0705010f06080c010c020307270b0105042102030a0b01060f020c03010c0c021e0d0b0105100c0b0a0b01120507083103050f070c0f0810020405 73
    0x41440512000718418100200502d84071384540204a096510889010400291841c1080820301904001c100e5044051100b1400c0000660300c4a82c1c406d4410304000d4600409025540e04201110040c2002d1105d51549039090394070b181014580035503041c13414140601c00c0c1ca654841c070704541c02c40f140e80203d910701c0a07800a403058101c91450043c0ea140c416412208042040f0ba40c1a50007030900b40c803406203e07075010300040c0c1805006207010b440781e4540011404241e41204442281580c11100c042010000031416035034000d4401c10030380c0211a501200c010030003403007407440c180c0340100c0754480080f0442c1c0c4119002a440140188402440004150000c1203a0403a08042c81c0504190a0b04030b480d14103031045400803110000001c41010134000e04003009034658010072044041d000b103501c150025100034215400c00141000000a0010b00c05803e000545034116803010b0801082951200c0c2e480c01d07600c4500801d100c500a150b40484255128403c40c3c2c1110409000c4041041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 575758174 1250 575756924 575756933
    0x20f090405010b1e0123030604050c120109090201080f131101030f1e1d06040b06010504080f010603020a051905060903010b060a02210309100504031b0309030620030103 74
    0x21409003048945640741c1080381c4043e03503404010300300d4951003041520b04148041c0010201040c10b207503038500e95003a43e60050080000004c90b903100c3c1e000c0d00c2c017080a40720303007000c0c00345407290180039605043c9600022910300b6141e00044da00038000d91b604030558172103040c4c40700743c00d109403081408048650729440000f200e480002c404042c05040005222501804038001d46403a034100c4e034280ca0648034403201404141c461402e100001c03c081200c0403042060107523865001510181c404964400001c1d51684920100d0f40030304400c1c030559051100e2080d40b03034040d01141c0401c174402c080c4a040440e0504000c0034407000c020f00e04400400451a00c010f128640d40204001c035055501c0d81d202c01042e881d001e00401c03027080203500406203140c0000c8010500100c075a403d10b47c0d1501041482503076500020001e0882d48107180000b016100c40c9400d49001061040b0001e00507101c1d05001c0070305410501040c1201e002d00414840742190b4802010781d1038482d40e081c10340c05014170040c000308 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 575759424 1250 575758174 575758189
    0x1407030c1805190f0f060f03060f09051002030a1d01090b011a1c201806070201080412120c050c070b071e0c050d14010b01020c01301103010f060507020f 67
    0x2400c207040001101703800b01d000c0d04152040c0342c01500c84055081001c00030421580300781c0740c000360600020440f00c0e00980c0c45586800e0030b6000d44100399008000700d0780c00000d541c0145030501e2441e4035070030001d81214049028111640080e1612000003000103100c0b5035155442540c05500b214003842e0500003112425103c0e02e549840d6036081c0d81d00048403480648508450400012000042e00c550b41e840c1c0102c00030000090b95802030b40c09003d00030060742c000705070f40e8001d60710004c8010358108049040303604e82d110300140a12642440d00d10403e694200c401050000c44c04030544002e81d0700c4428050340303403151072402040312204962000f4844d004441c40025a803044c80707601c001301c1e41d07000090850040c0c0c040949850b21070a10b0b14150041c24411100c40400a00150040a40c100c5c006040b480c181d010400d40d0800e5050700c0b0000419024403000030000f04202040038441402d502e0300176410900512114016001c80802c410703000700140c41110354001d0010754000c0207201845410f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 575760674 1250 575759424 575759441
    0x30304170f0303130c06180b0a02101125021f1101020a0503070e1206040308060105120f04020f0d0825060c0c02040b0d080d02071407030c180519 64
    0x25010312000c0079500907090005601862a00c44c0b040090360300d5040c58612980940c2c8210144820104e51910008840c011502102d20252966444145012050f03081c110149100d800940c0342c600c9100704000d101d4050000d07509410006c8401c1d5102041507030a42210040107075210000c24040481e000c2c240f01c50360240c08051401c041031030340710f0700818207a03001004880041007003c02044540341c1d0003080c5803000c410441d00302c0c401c0152181c00300d46800c400707807010b020842d00000042952b4024401ca5124406d502c3c0d185404d071400185001d25200305640882c030401c08001200342525103203600040c0c91748c2100c02c940c50508042070b8484454602490319181130007181210001c0390807841800c00817951601d0360307200807440e0700c1040202c07052081b9580c8501200c0d0040000f003042c141c2503e0f0320071803410b00181d441da06410b108194081160a5180c1e52040c924080b00300041d6882c402e04070b0b04074004091088400e2000c54054840c115400400208070320030100d5500401d4202c07014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 575761924 1250 575760674 575760719
    0x302060f0a0e03070b0d2909040501180b04050d020102071a10051e0901080712031d0a0f1502030403021f032a090503030316050711033405030304 64
    0x2441008440468284035160f0311203040000082204e42e11882c6d10b002c2d0702004400c000b1078404440c40e0404000d0245800d003001809030754081c000504105095204070b60700c40c02d140b444e0300d80e0049850300300c0c9516411101181d080c003502140e640d43c00c0c01402600c0030b041c0e01001d168402e230009941503000d40c4d8000c1c69000d100742002070014036912035000c01e00000020541c01c581d0941184c1c00c0c401004010b0780150601d6024075002c102c01841c222004c42d5050b8149010b03014183d100108090011388804003583c405044080056212440c00707081d000c1f2192506140155901150280e881e40510310020b0340100311001c141d04e90b54280c1c0c0448110388054100007410311143c00780600c0d1082e6036200c801c40c0d414003440005800b9003110040d4010720342180154654500008a03140440d9100245000e00c80c0100d01c07001080b11000d41c0d15101c00014080f510803003030040006070b031580c1c01d0003c0b010f04442c1440d030340c0600418a082101b40e40c0c0242c02940b40a24002e050001c4042400c5000c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 575763174 1250 575761924 575761937
    0x30a090512250503010e0a02010f0e0d0c1e061b03030b0303130f0f080a050c091306022b0b01020d110a020307080606190f0308070311030a080f060a0302060f0a 70
    0x2000141038400e0000c0b1207038490314a1000c0e402e00c800d050840d440d0414a00d420f50221740346038010303a03200648092140e101c1c81c001600c0c0c034100340403640040009500804d44e40f481b40740410b42403c510b1084160b512172822485505968a605903107000d012000c0124516102300d46401090203600b02061000024088034600800307151200c05001c640d030041092004000d904000070030310f400a45001e0700091015000321141551056502d0600e00d22207070140700c0000001d2110303020520458069a00844d05550f2080104440068910310001525091f411581090010416031288410030230043e0002c03c03800305d49200c00d888180010f04010601d114030600180161000e210708801050510001c080b142090790070000b8810402070768403100030481c60104000c0e480c0510342e03012a500604029500d58290500300c0700412220b100c01d0307081c40700090445030359a21401d0680724111200c41d83e20f80c6d807241030030441038040e0340c80060341c422028842c0c0001c0259030401020060098207001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 575764424 1250 575763174 575763193
    0x5031009110f0c103602060f040609090c0302090306040f240917070201091a0d11090a170a020411130605030a06080a031e12020c07080f030a090512 65
    0x3400b40d50062220f0911900026649002203d0078002c54071030840030204100c00030781e2100140c4004000c40b02c600c1c540300a42c400e42c001d64440004444034284400c0320b4660700c41d16000080d001e00800c0c03250518852070082d0f2130807014801d200340c3d44944801005000383e40c44070307100c2d0302ca06206000241c48262144e40c207203101030801a07800003084450300c2c3c0032a0b111894201070180103911000c101c5034050411000e40181c2e4804446820744007000308802c112104020407511134020341445440e054507080c409c0028003100d001800b00000100c0d9942001502d4032400502440d43e07580186407a40248046001494241c2100040030030441c5542c0c02c1c26144000450740c00d48543c0b00303002003100001030000c0180e40707005040c0031300708000c000c0c000d201c02560010b03c440318480c0109018400740d0a0991402c1c403c01c081d12481a1300b400a41d1a03140c02510203413900340300e20034040d140c4154101c10000c11408020713146841c940380c880314000d902e0b0505108400c1d1400758900102d0050b040c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 575765674 1250 575764424 575764447
    0x105090c0d060b0423040212040b0c0f0301030609051c09050103020c010213030c0302011d03030a030e010e120a03060e0f070e0303041e030c050f030c010f0e06070506160503100911 79
    0x90002410000d15290800700ca4038802c504440d01712113024002c1c0d00400c480e901c219000c03241030340c04c41d80c00032100d14075a032039503506038050052400c4c205181e500080000240310194020f648154081e00649241c62110404e181012907540711316004510085800c1190b0341c002e9000d0501c0c0c0000704000b61415003001843c0301869003540003112000300c1c03210701b441507580c00040009042404548091005444400681d59000344102d1104068441184002d803200a42007400c450702030804980311849900d240009603041440c581001a24100e8009010245c3c0c03114240502c00103051181c841c2c0340c0303001c200c445001d0800510b8042c4030070840010f070b024000480743c51007240786c04e0b410441811417800302d44200e456884640329485000307041d021075402040103400c121003403d0103400021031840994020306031000b099406040418014148031020454600c6425501005403007031304070203410703210b5000903140300505440740300080c084191194059400324100310f26603414030410100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 575766924 1250 575765674 575765677
    0x71d0a08010213060c08040302042a08090d05250503040e0c0901020c0a05090a20070b0411040c080106030e03040f060e0306060f0d060506120d11150105090c0d060b 72
    0x4203200e0b9070005040e803051401c4200c0c80c001e090145805e284c500a00c0c0c40f1099240141c2c00003900c110ba503894482c01401c01400700011120b881c42d00d004548005480107840c5007400c035641c0010303001d0034031198503041c4034000700c40b03040c2d1200900782d90403201c50310189021018400e00f2100d6100070000410060b5013070028074847d0604503e1159036480c0000024140216914042c4c002d0000303000901480e0b840300641a4858580040000c5e900052600c04824000e81003151300b0a080001d8140144047d00b181d552003a40100482085200303a00305010403128861400400a400130b4014040d080c802d40040c80c04031100000c80741429103645690000d00d01e01d070f00c080e001c11510f00780d4100c1410f050080e9136224408880312280c981d10712010400f0180180c2004002d6651000010455520f00035400d140b03407040f00c01c450b940741c405040039000c54420140404103201c0c46148030840300795079040c941a2000903083d0951929558100c4000b03404c500c50754050300e80c4544010450860110 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 575768174 1250 575766924 575766929
    0xb1302120619020327150c040f08060106080f040f470c0c070f03060914010c020d080a140709061419082d0a06080a0b071d0a 55
    0x24041c1405040c00071240c0300c9040c40070500000d490044c0204003040364002034400c0c4001d9000103251150540d003003085c1c1070000a071041880507200c60240080704c1038035800f8000f500c03079070640304054170380b9029402da858009104403c0000c081000007540c05075007815498000d441401c00c840868500d030b5410b000c80c551409510070391034804003003d1000c1d1600b001c6009822508036030603000d8030305060000c01200000c00c1c0201640001078402c0d5030340030030070404005005c100c00224240d510391521a01601c166201a680304600da1042c01404106209107407602c440c7d0b03002000207541e1043c0075242c0000c000c10b16180030366240d03800d5140d00078804030b2074803d520750780d170b0382c2d1242c1c0c00c28201604000740080d100d90260001c0c0a01c4003c40d01c0c2c05001083d16600d4113000c026991501400941d605c2000d40500a4000681c122034035074400b0608640901c12850052203c19111201c003076070340840d141c01404032820a400700301000c0c0920150030801e00590400c0403201011408599600120fa = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 575769424 1250 575768174 575768209
    0x40b030a14040302120912011b110706051c020408011e0c020a0c0b0d0e0d0e010f030c080406050a18200f0a06050f070c180b0f030a0b1302 61
    0x300204054584601608a0a520014407032400c15440007985c81000c2443d0381d0801390000740101d0715a0351000e842c20400345040c020f000c900c060200140c07403102e0500708078002c100c40b6510b00703a400e078011910328156102a507030309040400c00030300814000a602e500d40c8450758204000f1468200a001d4001007021000120001078514100c06089501c1c00c2e11040031900101840b0300040d080180c0d1a00b141c40094101f91182c8505a9080c0100014281038000380b0404420360b010f59040740101c1d60040c02600c851440003819034050341942e04c03a0784c031039001034440e0000800150140d4011074111001d8400080d03444022152541d00502d036900644025009014080d40d180700504210700002003038940c03042e01030300035011550507001802104240704d804074001075070740e45100649800c19080040300368101c0d40c542c24004202500030442400c44c1c240054041d541c100701008a5400c000034004081300c0100d82c444680c58500500141c02d04d500301181d5901580d280b84c00740b0341b0040318 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 575770674 1250 575769424 575769427
    0x2010213050f0a03080904020c01060602100c0519030c021609021b0a050d2607050301170106030c06030b150c1501060f050a0c0203031905030109111e071403040b 71
    0x518040e1a24121568810351052007034500610164440710318580c2203981c0305040035160103050001030081c0c01200e400c082c180d80b0384000010440e83c0010406a03110a145e02003101c0030140804035080d10440c1c08404040d031030b040035202110b11075030094111004a00c1514590761101001e50103040d02944541480d0f0303004130346042c8640050141c01035115181006004a03950350303031601d465581d545285403e101a0113010269001c402d0305004c514076451030818900e1a00e040003424640083c0100103c4120078145029250310501c120020350340c221500c84922494400d00328003400d0441d00c0550403822094540c480910608064901d000d12030014203140200c81c407290004510591110041101d0348420060241d008401c031000205c191401041d07044d120b001192440c400c485240d200c0940106a07c88000da001000d107050f50f50004041c080e40d44014a005681d0160481403407000c2e00c1205944404640c4800502c50300348280040c00044043c040300ca0b0540e0003c0d0b1113007050420 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 575771924 1250 575770674 575770687
    0x614010e01061106060d0f080412050d09081609021b0303040606080d02121804090503030708180a020105181210060302042d05040219170c0d120815090106020102 71
    0x400504001d0301050050003041c0a280150000300726404200001c0c000000b0221f41c0d209020065040310b0181410160300b00e4a0b04007850510341e21101080003a00080c1d000c5404941400003240d6200c0c1d800016011608840c2030261010007980041c144d4042411104541024035000340065440b03940140300000d2801d14002c9401e0510550501c14400c64020310001d0079080d11150236606112256404030300e4074203d14020a00401401c1c030080c1591101200700320850b544004030b14442c803d403170781d50701180c0102c480c0d0a070b030b404c04d821000b408200e090180703010798607422021a8003124000c000c42c140054060189040c03008200c20503c800b500c910041c030a605281c054903021484980045598840e001d10340744030004111306011009803101c010078155507601c0f02c0e95440142c08808064a43d40c0e0b007482070381c00d02020510b503449015400340170200345003507a5841505038000ea40004642090783e411910b0100c0106003015045040c90910200e443d840c040030f000c1c001d6600010f070f82d82c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 575773174 1250 575771924 575771927
    0x70f060e03010c080f0103110102010b060409020d0e19260301060f0e06040f03023c010905040506011e05220602010b0f06091003020706020d060519060e0105070614010e0106 76
    0xf0f0400c1000f4051080660130305c8841080100d25604482c2c10a960f1050700240200403809441060500c552008010501150810890740100324003400c0d00c004100c64001d032202541c48081d15817484400c00852010740c0040740d000c0b0b4640c640840d81d801001040c910550001c142a0420307000103000926400c449181584c11404203a01a081100c20301c1c00d003450702c00e052a9149540c000240a0308c001940407600c658860451030155901000c2548511b090711491f03207010000035945070000d10a071800145c1400c10303109480c0110010703550341100b8400700c00008603000c404043d80040000820564499590401860800d0a006004c0600880c5020802404d441d03000711128813910541c184046183c2e14102101c8040c40291f0341c8400c25454100c1c168000d0244400140801c0e00004022249080660020090f103030120380410b020411080c81440220160281801062550b035404056600410241503102d1103440302041c440400364003d02d01800c2a4032240081c0440c0d070041c007800c1e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 575774424 1250 575773174 575773181
    0x806150108091506150d0e0c0f1503040807050a080c070f08030c070e090304050432090309060d2c060117060105090703090b011d010e0105030c040e070f060e0301 71
    0x20180d0b0740101458044500400021440074262500c9002d9039100035000072002001c0d00c00e100e10320f00c010000c05004008560310b4040200003035124800c42c0450303640030310307100078142e000c1780703075041c0c00c0d802d590300ca640b00250740d408000295040d10071529804001101c2d1001001659078000103810405d2030056141e01070301c0c00e900010007a0300305104480c809500020844c0480c1d008000240320b58890031000c50031071045401198000d424960030003523460300241d201c0b42c40c0a04c20f5640c1c1c90704d418501003880300b0409441c006002c4e041000404001e151003c0640400030002c98002011044402c008441c03034101ca9030f0b248508030310b044100d001c1c04240f00f950700500f107c80c03584a0800f407560f01c0a442d003d05000e5544550301e802e002c1407115120b50701045216901c41c07001034155850303802c04202c0807000100888041040030001c00c1d8500d26002860403180c021b0010419503003d48100400307040a103d05001d035116004000074132081d030001c0c00e40249800d444208500e1202401d060030b4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 575775674 1250 575774424 575774431
    0xc0a08070b160e130b1009030b01060527010905090a09050618030a0305040c03064b0b0d0b07031a0906010c0b0403140409020c1b10030b04060806150108 67
    0x11194000e80c00203a900700c801c0343d042503412074440320301140c489200e4004112025250380c10400143c4d4040c103440e0000003200a80e0f0007061005400d030703038526040300c00e4801c5003216803131602501d5000c258840b2080480704408014100702040f5a255004076006150031903509003c0764455503810103014040c801d60341c120320380b6600008100313550112680c2d240302e083c50800800d5030b0f0744006014405500800005076621160600220310a88da00440442c101c1010844580011118aa0340400840c40c1c1261410259171800490b40b1401600d00920110240c985c125041c1c0b0910000110702c0c080d4103100c0e10498400103000c80c01005104036003c1918a0107014241c02401d00640f603800c078164200250f031102011050395528982210080102c00c262102e055000c1303404640e02ca01c2c0d802824031604400103d03202d502c46400c403005805031008803190012440c5004c1180e031031084e044444c0480c03000d02b020655541c1c1e01583c0f86080c2040b111614582d1400859100030769210340150381 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 575776924 1250 575775674 575775691
    0x6171008191109070e100309020303160c0e010f03030327260c0c0f011b0f15140a0f060b2710090b070609020405041a01060203040b19050c0a08070b 65
    0x10f041c075001c02c020701005261012113105030100740c1054900340c442c2d040070076400c2d0701400340c82d01d500940d44407602407084018203e5504108003000704d14058000300b014106c070104000b90000078656101030303000304084140c8545440d00c8001d0341c2c7d00b0703207150b103400d038000381c40b4540321942d42c150703031400c0c200700f0140c100230060790401080f000c5486d083c0004c00c3c100f42d080840fa000d1500e2081c1005883c0c000e405049010031050045004043c040d41906000b1080d00a80345d100c4814021008141162405140c80075440d0020010031013003032950780860130310102c210700040d402da101d0004269641108000c00d00800440603118101c4d054402c104c82000b07020780f1040c1c1036000f00d04020342558102d014100607a500403501c442840030350340100f41c0143e00074004025030309103401c1c0134034403030920b0106488101c07180000140841c400022030342115481c800340ba00308649098142405100816071000f00b00b010302c00304002c40d0b420300030f6101c400d100d15805503852600e460300c1313104403000404469 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 575778174 1250 575776924 575776939
    0x230411010c150c23090f0906090a090822140301110f0304020f0d06020711030601061413030507060207080118020609120106032102010e0106061710081911 68
    0x180050318055108600110a20002c83c0c0b00c03400500864100d5103a00d8450000008414408080da109400a207401d1130107841c2c1008040e4680306014451405651440c1c10400c0300700000d2041c0d0103540404030701032156413440e00c1c00140c140714502c0c2d80819541402000b075843d0342080590945c444503141081d05800900c10203101c1000d02046001c4c0c90030481d00540700200017002c540da85000300402c2200201208002c1ca11400c0c0303071340250061482100e85200c01d080c94449481c0015034103040303501e240e85180801c07182802684254000c0d500c4181140400e010101c0020341c1801034001034002940200b2010b440c1041d040e0079a0132035000c181c25a00c00d02c0c180805a03c42000b01d44100c00c0550b955548e42d9103010605004000a50002d480254544074409a4003280d5111038901d60340c580c001d00c003024201c0885400c8a821b44075520102d40e100d8607071091207605100e19607001c100c0e030f00b00003000da58414003941040d681c40e9131520417220001074907041007040c1d01000385a4006a4094 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 575779424 1250 575778174 575778197
    0x110c090115091a091c02180709050d060506040507080105090c1605031b0d0f0905010309030c14251508090a0605040317090105060102072607030f050f0607050304110423041101 77
    0x7860000441f0a681a440c400500240150f40141c000c00000d01015040030507400d49400c00000900007501c2ca944100d0900f00030a0040e4072402e000c81c180e0b1402401c400e1691603d12411165601008289102e002c0b070300e981030f01007003007030000d440b1211058541c851b042d000c0b40c03c020304050019010005003c40c412a03100569400300c8104151502802c0000c0ca0148505040e220103031740450042c0065810b9403c21456400816000345a210808242107109502011190131001a000d2455010644d03110b2071103041c41100410307001031308070096410341c810350344404081c1d034812901a00403800400030071210281b45844160b000c808030000700140d00345040000d403902c0e0710b40300b114034496440240490705a40140c440c41f00800020864950558a1030079555500d011a82952207000e080005582c0110208520788200101d0703907034514541d12507440240c08080b0700041a0000e9a40c80849800032000c09030840100a440c5a04090324003440d00070244603c03c01040c2c100140f0780d044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 575780674 1250 575779424 575779429
    0x409080f040503013911010504060c0216030302030f0a030204170f06060f1e01090b0a0305060a0b0c120715050703021306091a03180601060f110c090115091a091c02 72
    0x40e00d41c2c2070700e55406100317400ca241080314409842140003015510303000c24401048403a50082e04406c0031034082d203900d03464008950351010518480071340960010403140e4802d04640000380068007407402e0040c14951221070b0824601c000c1101740600d540101100d0705908810030056900910454183ca82d044a540220308111048840c400c3c4840d40100c540205038010646039002d1300da00c254035615003003618001030241c2400e481ea07034001c3c1c507400b2000c104400520110784106980e01d0040c50f504030a1246280968400c69040d0341c103403902c80c0045401c0c0700d135000c0d150088031941c6d030140c1c90783c1c610202c101807003010f9440701d01030019100d003c216036a00143c0e4607900310a001040d0341c5990b03e0210580300002e00850050300c0d03000d02000070a00540048026145a0480c3c2e141c050040259441607907800c99070b04182da004001d040100614042045880b1060301c583c078040071403583d1850704001c1405510750710020024003050741016410540444441513103015500821006d45801 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 575781924 1250 575780674 575780741
    0xb0d02010c0203011103100608060a1a0a140a08010302041b020601060e03150108070e09030f0904020c190b18010614100c170a0e090702100b0409080f04050301 70
    0x140281480103058a40c01955001c1d44040036102040e001035549203048001a41846828002c00c4e000c1241580820720f9401e000d001e10040e40d01a101c100c9041502e15031041142d0080400181008800d80341204070282c03540280010901c13a0b140d000540d41588100f0090708c0301c98030451175001d84c0c1e0600e06000d80d40000c1a504443c01d84c01c3c46846044904086030404080b10380a00c084020200000b0300f80c28000782c00003c68031400780c0d1841940f160890310341c681c0f107100800e4021510038000d0301c81382e02e00391f4000c2038203c044004562070340000c1140300c591300380c8048042e151142e0b040200981449403484d440403000c10200200310850400110101100c8a40c103030038052200d441d0a52030f058000c070012001c0c10740000d82a007078003006901d2040380ba401100800002180741307400404a040c04049540144c0d160b0700036090385034241c0310344001040901001c40d803080c0c6400089003c2040000282540c4040d00e1141d0394482c20030050609441c904000384d10700760220209a60f0505110700c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 575783174 1250 575781924 575781949
    0x140601050d020c01060b070501151409060d0506090607030c210e0f03030a05160c0f06110910020102040e060604030b01091802060d090309060e010c080d110705070306050a0b 76
    0xd0803501e404003603000074001c1c019080340944641c60200d0101d00c5a0400300a80703120b500c0f442c000c0c411a10705d142d92100c5100c1c28400c20030726655100825003a803824251440e0300850180107812000d481e51501031822809032103007003d5030030940a008a00c0e6260103040c1020210381005602d00c115210040c2517451044c0f84403019030781c2c80c0c07440c40080c0b000b0301c804151000c0c2c0c14100e9449040000315040109015101400080810b040003100030340998042000c40340c0200004078005096114040079105c8a1004141064204504e840ba540c8400c0c40c4401c011141d03000584841c03c114030b844d943c00b405040607104100502040000840d84d20496065950040007c607075034524400c80740250b407910383e000354450004030340310700800d48546c00129258000d83d101010f10381d41e494292144404c0079006170000310324200880203d04200000e01441100c1040000d0640090404c40402c5d04203c9003150a03401141c1c003002848440c0c000e00750000c50890040022081450000341070030060b1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 575784424 1250 575783174 575783177
    0x1c02091305361e01020d0c0914040b0a05060c10060f2d0303050c0f0a06090b07030b03061f050d0b09100624021603050f1905061b07080a0201050a0f140601 68
    0x140f2803120340388001e40650300741102004040c061242130000141140e119400361800b05140a1004100317490f180c054510f12200141c030b45080103041105220132a4040c1d1001180c40c031505401008980d81886810018001e00303950111190a01401c142241209141d1709594072004141440070120f148215048032342c941046680c8510380c00b112400d111542c0c1e03252480f03008a0352004140420b0f50414000d07075203e02400420303a9103035241035084a840b0310761140c266000100044e0841408448004d8200750060002141e654400000e400e02c2e804000407180d0700c40b010305200d2501001c00801ea5030640b164400d202e018140020181203048104003904019201410700c04502e0092100b1210f01d03c1d94420164840d071603041c695a20702401c1000d01061040c6008070000a02c26581d10602c0c0c2d602001602c5207448400b40621000d02c00f2000340c4c00107904010710000155604000c2900003038680000c100d5103000722003e000c45401c105d001c3c00c028108203546003c510703403810150b84041d09 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 575785674 1250 575784424 575784463
    0x1906020d3b19080a06060509090c0114070204090f0c050915060a0908011a102604050f030703090f0f03030c031103190c15021c0209130536 61
    0x660005000d0000312150251030b190561004507250a01051350014507000d5041401807540e24030074400c0e40390040360201d082e5088988151640c1d0b10902010044140c3e0400040c2840d01e00e4001034120352003c0802c64010740718901a000f0042034452100083c01c00729681d50252030121000c0a80e84038203904544144000a80542810b0161070450007421803c0700800401d140314800040c06d0f02e80708021031140420314241e000b9944544480b5400d41200000020005844628002442805082140d990081500003040c0c82000c00103040c44600039541c00551918003c041c00c04110f07190420345030040d0380d800520210b60003c02d2482c0c400d6041c038209241004032a00d8900b14004c0000b5494200c5044500350a01303940035051024a1b4007500c5051a149840fa9008049200351094405803941511141c501101541e018044e86003028085212804000b400b00040310403c803034407103004160078034901d580c04a65180400c00030707104040352140c5a0700e82401c2d43d2580c0b0340d403038650420038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 575786924 1250 575785674 575785787
    0xd020901050d060305031314060d0e15131202030712120e0631020a12060b15030a0c1701090c0509060a0905010216030f030c021906020d 60
    0x20500c215508034a01070b1040100d55101e2400d19201c1d440005440050004080c0220f03d002c1d010740d801c203149000401c407030b141c641080201c4020340010f41030102540114512100d4600116003024030a800742043e1003030255042c50041443c0b00403041400441d4401c1c0140c6000500075801801e402c2d0700d0303007459440d40760340080c482c2c050540500d111910740114800c0c01024420108038544a840102d0f1500d800c4490509141d19040440000703036000b40b010804000503000ca02ca04844240107000c0071034441c0d040c0300802c441100c00d41d08031030148000810461034000034860f25007030352294504060079250100310512081d03418060242d116030344a40300302b902402181150840c03200a080c2e151039951401c409442d001c854440c1e5405401005014a480110070b0760703510940307a00100503921070401e52800c4a482030756031402ca0300070700180c0011424420201070400100301075801080c070444a810700505040070a444801c883c5400c500171030340f102da00c0f0304510002c004d090600003444c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 575788174 1250 575786924 575786927
    0x9050a06031a0607050a0212101a0307030b09100c0509040501050d1a090f010f0510082e06180f23040602030604110703090503070b0c030307080702070801140604050a0e030d020901 79
    0x3540580c000e600c1031100c5000c1c0580394000c949c0321f0340004a1441001101050f140c4100044020800c8a034983c02021080c000106480c00c072641040e0594129000d1080c5503124108507141080510701107600890f9000542c40c007801035034050002030b0380030000340d0080d6943d0a122002440e0b060740c031500107000100038007000c009081e84a030019009101c286644100030b00201001e96540340fa06401742000709081d00c0005091070031303200000c0d072030300c00d501304209055000c0710780c001c0d44c0003180d11440d000400b002000040703503440c25900000501e00b60004690400c8942c5201002c840b524801e40420b50220903882c600c0d80301c2d40000d0050790f03d589070000100103082205c00d51584941c0820340405155200441109580040d002c03181c80d562141e15407003190142e50748403090341c1e004000061115208080654000001b0700442e1000d54460000c41c2c25030740c10102d440d284d00c801008019182c505801015040700c20407500308407543c031032001543caa1064003030000c0d03031640000d411400743c1d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 575789424 1250 575788174 575788183
    0x11030a1d0604060504171c08070c1a0a05160c14010f02130608010501080c0d0c021f020c2a091801020a03050a050a0b0f1002030c030a09050a06031a060705 68
    0x140c01024603994586802001e48150401d00070280d1307924240e2204680600c1c00281e009100d4800c820003030318107264600131070b400000108036504100c40b0304440c40000c3c8442c0340c401d800078824098624146413080d50f210803550006c1001c4561848010303002c0c41d1541100580405130f4020b1115210007889810060241c101c8800f00944070f4400602e825114a80b8010442a2002a41e4145045e60b80f90300440302c80704240c480e0032807450104038481911300c00d980400e07040c0c8941c3c0103036241c010191b42000c46c00003000c0d00c60941d5035000a001000543c051100010240c0044560b1545580009c54600c035019141d00e214090340b400c030041400d03500d42010340300301c0d988000c2c0203646c0c42d42034090050103000d003501c1044030241850f0204055100501507840720a01c013030226660340c018007007000300e84455040b9420560208200c0554007610a00080c10007110355101c040f1024608400c3c40441c07007407507101e4010103162028412426210100c8240002c200302e0b40961507003880d0a003c1e00f00b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 575790674 1250 575789424 575789477
    0x40e01330b0705010e0708030a080a0218090403050d11190809120c07030201080f0402030a02011407080705010b010806090c0901030b0a0e090a03030506040b031011120f040b010611030a 81
    0x85001c00b007074030002c0040c15000401c1c0004c044080d60480e80d519401561b4070301a0705d030741801144c200000134141003200d17400703806400b01c1070000504010403100030419003042980c0540c0007600002c1e800c1c02d07101039401100000d03000c0c045203910f015650400c1402014640010100f009541070118001c16070401071034904c10003401e1426610f06640700d03000e9641c41144022400704110300c000400722140c144843c2c1c4582e80103405460080c80590044030408040010000059810300102e0b0104480c0006080218403490001400c100380300e001420b000c900425142c820b1a5190401c61000450f030207990f059082030802007080502040050f00c0c0c0c0b107660b000703484100001020440300c00707800160755030003c0c06520304000b10386030310302032009441840e28510b425622440502c0c4100340b05078001040706940b1002c113400c10a903420b10080200050f21500f0038007003824284014800c003602e11074010043da007003402d4240003034612282c036030145c02420302c18071a20100e4103482003800740d4040075 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 575791924 1250 575790674 575790689
    0xc1412040603091704080d08061309050f1011070611040b0a03050f16090e060a0b0a020a031b020d020904150501171b1c0c0302040903050306040e0133 66
    0x44503911000000c000300510607013501c00d460140c5407024115072000445040d01c020202912448049910036a942c8101601098100b40100b102c014020603034400c0b81101845034000c2c180005102c0380343d6140004807a81221214504141c15100c200c0c0c1c001142c0c090740e032004c80490456006810082280604c0c3d00804050742c1c009258034032158140d00051081d82003820346003a640300c0050b203c040c00000c80780c1d40042a00d0400038080416080b0360507600400c003c01d195001c0d1b860740416002600403141c0400035902c29280001090f40180705d01c1403440c1c407402403041c40c950b541c00052105e1017008003c4e0150207c00c01040900c01824005141061160030611007540e488504042546040880c40b9071801080800700042590085400c40c4c00340090140f41c0c4065401e50660303c65298803070465220000240000040e140d40c000c03542000d0090701c56686030303d0200d0501041d500c248004044c070340d240c007a075488281d05c0b500d00d108400320070909102c3c101088112078544425075810500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 575793174 1250 575791924 575791927
    0x51009030206160201021623040b030d03060f0611060106030e0102070b04110109090e0303271603020405150a030303050604140f0603071d060409030e040212061f0c1412 74
    0x9043e00c6048920560080c400e03130842d641881000c504c0c154916060142c030500f81c1c1400c5150300d030b502c074004200d45141001400000c0f405101d1000918107201070415002094540c0c20802c800001d00d101c0301c00500c698100920420700b8007210701c0d01c0b02014000c0c0c405166441020b00c102c101e00b54140e9041c240d01000303007040c0c0e05040c2410010040501d003141d000a901c180082000c0c1054080c1c0f200455058000b0b6055440d9254488441091390049074480c41c1908280040e90350300304040141c1c1444000414029411130043c00165075000701070390720140301c800700d60860342c49030ba06900840b41c00d494000751940780d070030014014084041005c0405984881444800007a600949020b000c00f20100e5503a40d43e6900c00c100404403c0ea90341076000c50190018040c0d0515400c11a0f2480c4203143c074004003a10b81c000a02240c000c070b00d0420806e051a401c118490414407400c41811031080d400840c1c1c8100380e00014500845440b00400c0b5030060003031003000741820031024202809251f40107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 575794424 1250 575793174 575793187
    0x506160503130b0c0405130b10050901090e070c05030d02120114011704060204120507051002070302090f09070902040b09030f01060b0901120917070b161e121805010e0102030c04051009030206 84
    0x20b00c00f23001c1505280e4850000307c0c40394140a4050021950703c1003068460103502403604c0720b1000e00407001042081440035040721503001410900003001003031001000142c8682d01e001c0e4000d00d00d04160045140382415442107495680c00200300d4003045911400c02500380e039640b6240e0060b0003190310401a0460000702c1a003040b1001c146c070380c2522015a9451056041740508903640c146034880690000d084402180301d600c04048035580c004042000c4485003aa03d0002204030380c0503910012807118007084002080c41c040c4404803d03c440340009200860504883c0303600f5200f0040d9590500c44001046a0054559005810119041038807903130000c4515403820041e13480860102c40401003480091009500e490003403a02c00d41c69a50f600d81001100780f03024145803580103003800c0c8110b041c4580402c40795806581c0307a80d8801d100720107030b8502e50f142c1a42075548100c0c0b1128541d00500411008425207400d54084a404858039032002e4081202542c201080d0b4001a40203407001411 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 575795674 1250 575794424 575794459
    0xc03011d1320090f061f021612030e09090c01051b0f030901180f051507171c0e06070e13090614070c0f2d0506160503130b0c0405 57
    0x12054100c4090f030f80a61565541554100304980440b0042e81c82070f4694032900c502c0d036510a42c01c2c0e40104c98011038556030407800307908515105680c040304580c6601c81c01d85080640c0028800302240f01174642036400c0c1000042c1507200e40b84400d01d5810020701280450240300e2031013102a03c40c4150042d6400303041c0013104182c5030341c40082043e000c24044119480007003180d094541c07c0743c0c21000b88174401402c040c00c004100c1640a00605a04400d00000c1c000c01c00080070a090f032038018121a41d0b500408040501ea14002c1580e90f00581c60202c00400400e0f0110302c056004100c0d1070000c513903082c0c500007d032301c10545000203140c46150003007a07010048564001c130040740c8658200d84c130340d5441100c00c030703100044100300500d181c0044c03408100040401d01d0034580045000024020250800f1400201080449040d0360a42c02078080c803000030400280040b00c0003880c03509615500e0182d100c1800c00480c1c8034003c040400a0000942e4050322909440103040010040095052080c2c0e6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 575796924 1250 575795674 575795723
    0x6230603040b2208120a05010b07030804021c05030a020601033e0102070b0a030902150316082203171308121f031104050c03070c06051902070f0303050c03011d13 71
    0x7941183c5600e4000049515400202600c4600c1d50bd640ca451659407994244000511501d0030b100703142407404c1c91600010070138000341c040c0000c1507005040355031441c2000511079079040c2040c0c40c400e1210040000310100d105e0412520300d540d0000c0140140d101004174a0207500364032200c1c01440103d59201d03502da042c1c0040080078001c4984100b828140100c40c8003510007030b213600100701043c5450700d0007580101401544841b01110b07108102c0e03030b0710140c3c1000380c4880e81d00710005008218142c00017550301c000a03412640c402c896560009065072004141c0c401d10200c02c59094081e4000b0744141611143c0700c840c58001482209010b0703592402005400c11060001d100f94200b00014002c100004103681c4500029520b00315502c0503601d4003002018050b01c000941a00403c0e08105141c95000400341c00e0301c140100416456203080060441d01c01502e000b41890080004108881c425010f0302c3c035001c0c15010501803500c8485008400e00588074001b404c2c80c52034004100c4441e4103e1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 575798174 1250 575796924 575796931
    0x91202040e0c1206100609060905010c0c0b030109060609090203010b0a0503042d150b1f0e0411040512010204030308160309050f100c02031606020c03040906230603040b220812 77
    0x144005d68003178035040f054540d18140d000e184005480d91004000b82d607c24070707411809500030000650340645880012480354800d810901149450711b008028959010750382d1030040003541030440c2194103080c1156418843c80038840104000031004c81e0034080c0d0b00b003040030507240200c84040b098818039030208150b14400400c1c6d4559440080412030076400c0d001d082c48040c401007450300f100c882d860030b05010203441c0c1851803c0204d4160003500649462240030340c12140783c0c0045858500c0c200801c1100315614040c41e542c0d034014031040000a4005841541141201d80300035005601c848080300103044407040035000344554440c0c031254150201700391040d02d400c0207040c001c40300c00302010f90b41ca00c504440b031003100c030a50308480e0200d8400d50140c140d00000c00107032840d140c0c0e94aa084181e0f20640c002e403040701c0c003680100045e05050701c1c880c0c0411b40e00356441415880d06d5242c1d4031305008001c1042c484031070040954940140216040c000e420f0b030185100b40c80703220101c1d160a9803032045 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 575799424 1250 575798174 575798191
    0x9012604230604080a030f02040e0402030f0703030815040b1f020105060d0b0f04140a1109070e0f0915040c020303011707030206070305091518010e01091202040e0c1206 74
    0x301e2201c0440c6003036a5010041c45480240b01035151990350020f564402103103401010b9450020051603020343c00200300801d640711010000b4200360042505109000d4041190b581c03000000b000040d030407a400c164054074010300ea0718413a0803400494060b00d41c0b482865440300812448005007080c002c00301010407071940c000c0020355030307220a11074080d83c2c00740701500f844600d80024a15448044090345d00c03c5c800d150180841c4811142c5528140c09684112460384403580c4081c141d0070081c100a500400c03915043d184000c1ea070000c58100810100110b015441c5000018803966581d41000e05d4040003410400120400400007501d030f0b00f0030702441e00004002503c080c0304040c001140c000ba250001c000610300f00e51a501905d03264002c3c000c2c0350704407450001e00071000035420061f01c1044074503120202c10780d054000040110700c00342d00c8507050047c036034800e1000020400d820315460341d041d200000d003002c0e00110180b4102e44410415070084600d142d54060100c003090302d90040c0c850 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 575800674 1250 575799424 575799443
    0x20a03081b01020a1b020d050f030301031a150d063218030909100b070c090b1f0e06040b0409140f0c030a091b0902040501021605030c0609012604 64
    0x36880c155080c0e200d06411131001901000040c184840c00e15007061509200130003035082c81c100c56540710b00f066104d40207580f551700080010402d000510480b00e400e40b501c2c4034a61100d00d01120f04107110711b40029910701034604c0c140b01d40c040105903800310501d0080d00da0702c0d0340c80108400e40030004070716207050030390410144400304144048070505658001c404601440c00c0c03181d0201881090309008040e130724000510302002545841080080c40000e015008c242801d03410030060009594000c45c090b4050301c50381003560148454000110344640c1603140055a070010203000030302c1405203401c0a4041c10002400082c03070072090740255551400d20103021410ba5a1204200d4103840c00c642614400d40200000344001c101603008044407031003030784403004010341310706017056010183c2c00010f0b0143e4005070038002580c040005032040c400d60811510390504040c046602ca00300307540e8141c041c80002c55100e405a0241210405600704d68880000300701ca0303544501402c0c20256001e852500740c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 575801924 1250 575800674 575800717
    0xb0a050114010c0804050603130b0c0904050708060306180c060415030c02030a0e0d0c03050f0f0c240a03020408030a081b0301080c01080705090a080610060804030f030f09020a0308 79
    0x26180c03420380f0b80c3e088440b55041c1450701043c04415400100654280455408400c00044a00c14018082d448240141d501c07060740f1801e0000300c0300041d00c10014040c08404111403507a000501e10f6005810610074003005034410300041c0381458010406c1ea00100101740840c12400d8010b5a0280f609250780a0041030215101a6102d105045c69800007904503984500a030418403142d91980344600d92a02109549444850030003c010b0a10707021a04188134080c00391a040000007801c160882d80255120316116025a041111101d080903001010507400301860003503041d06c0c0148401030a583d560310a20f04000d00c1d084c8100d4080080c1d00303100340300c040711401000990381a201801c0003403044210380c1d0019500340d42e0082024081040030454001d2a8a4246103003004046034402480b45040100202c521640c40383c00400c20007a110042002082d84003204250494031800c0002c0c0403e0041c0301d4001900300301c4000b94101c01540700000400c807040005044402c91108120090f55 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 575803174 1250 575801924 575801927
    0x3050306090a060b07120e0d06020702211e15040503070c150f050306030709060f0e060904050a2d080a02060603010606050d180b0a0b0108070c030906050c0a0b0a05011401 75
    0x40f42c1e401a10160a0103200550010b00b807850340401c030f040c0341e052150b69001d04e10006005191045c1080b0341580e008101d040450401d1010440740c070311a4002c6246164621300c4550751009618615850401082c5030100005820f1240441c80c0c01c0401c102c0f007092030542005540c0b0f038000d010494409414001c0011007041101c1104c058030314070741d40c2c04100e03420b4400480c0e05400103000594035000300c40c0001180c0d5024400d802c01401100000030f52a440d11000f00003211b40104424000c003454010000042c902203140d10409612140904002d000380410740c4442074400250800201e441012034240100361b00588030024031076086500990b5100245801c0c0c88041c49044041442440070041021141e00009016400c024541c3d5604517603450b030340c2010206540d044120741da40e096600072568414a0294001281c9c10110407087c860394000306401550f00c16102000b8000c00c12800d44031082c441d26105940000588120f420116074403001008203129007075440d05c41450882165 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 575804424 1250 575803174 575803181
    0x130b0f12010e010e040311031b0d0e01020c060904020a120c18050609100e03190606030203061308040608041103030a02011e060f09090501020408030d0f0f020909040f061803050306090a 81
    0xc42413844440543d031a107640645c2d98086100491500380810f0142a11b20b54501d000c0445000340b420007002040b48026000c1c041c6c0d41407440203411500814404034a54640710b0499141040650700160b0718180c45608a40305020500102d84490800f4100d01784030f03500940400c2c5010806011210b9181e40e20100003c038851105150f80200d034603400d0201d458098420300c0040400503080e40c030042c0202d007072180c0d00c010142c1c003203900d20f6484070280298101001099409100d1250341c0c1182c0c4025140c2809902440c0f0811041004001c000350400c1600c0c010300051321005401c80303803103821a19029001e4110f030b01a10308240c2e55074080c40b15044440c00390320103c0d89400d04c2c4e54522401d004465000c0d201c00601a01e02c0c1d9000c00001412000406c0104400d850028000401c140300500610542e081140740d02442401070001d40c03181e07560714851a4200d580028100c10003802ca01e0104007a0404196902c08801c5008600741410b800c0b0009512a6008850030902a519010a4001c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 575805674 1250 575804424 575804429
    0x2e0513050d0218060114041706070c0309170c090c03160e01053001032301091106130305010c0f0219030e09040f0507062105010501020d0302130b0f12010e01 69
    0x802e402400f00b80103416240c00e181c110f4410725000302070b000d0020442019a2240d404880303200d204030302545110a0a11209400100360300d8002e0245d0b84917200104880341d28020076030000c2d003051403480f22071402c204c45c0d4040c03003000d00241018500410440ca25800c1103d541e80c5c10b909509000000b1482007112445010051b119181080041c14a025030800d0381c08900041c080d00d000090b40301030500261038000c6120707003810004155198041e004210360003400c4201681020701400c0010200c401c401000754040c0d03503803601c41103060364911003202c0c9944050095441d160200e81450f900c5071007210b92400700c4c1c00311880c951003009141c070000403102d000780014503410354810f1603151030303c02c20350041d015070103082602c4110317111503052061540c420404030b4104548a40840c1d0290401401007501a0701080150301d8440040d4498004802c02410150b0002e91000102429175509018040380741800e61a441d40c1808920765901c0781856440c02c400039030000a5490071820403034103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 575806924 1250 575805674 575805679
    0x905030a0c03120c2006121524072406030501050919020a05010c020d050601080d0801080a230f010f0605120a0302070e1008151f050f2e0513050d02 65
    0x1d0381072a12170000310402074a289580311000308a05032138642030741c1c0d1040c0034607410301011801c0038241b000c02c05c04030305500355032650100070406c905001540750b0540740401d411140703030003010100c62010f0b811501c1914081d031450b0724184022007400307030561001e0b114000b000100c0d83c21090408172002e038002c8459000703602c00201e00c001d0016500c031701ca51140e100d2001d8144800c00c0741c5a9949820034500341c0104105900c0f010703104241588c800703081030040c0485000380041e10107a80b1003002c04004007810303914546c40c520b274400c96030000b040315070480c802140003040340360000d00c0654081c3c40300e489000d00c02c03901d05802d0030303c5141c0450480c180380d41c1500203140343c9141441e60f0300c1e6080e004010840c0e0f400005c00026840e04140301400c8022100c800c41903da2809445207040d015080c124100c3c40d00401d02c0601040d240c0c0b900d201c400403821103400d0100750202d00b440e01e280d07104c0c040b0786901c654001c4580842039004000f60625891030861000d100740c440007072102035441d0800103503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 575808174 1250 575806924 575806943
    0x803040b0f07020a08030307081e0601180506070b0a0501080c0307060c020604050619020f16030f05010608031c0f0218011b080c030715140103080a0905030a0c03120c 73
    0x14440014014102107001418940c201182ca030006110000241c0c0034220035000007041090311540080d0b010343c40b008100410a0b40c0d0111404091510002000507062103501c20103941d10100b0b148062005040041c28565a80c039030703243c000f200c01c00a441c0c0380104d900740000446e4082c00481c80480340c45014000f0314109161100440c0d00b44804102a0f03040841000b010030309445050040070801e04000782c000c845c2e03182010081c5001400c4000a40b41d81150101d040c800f9800740d600002c0300c1d0001422140d4a8a90a0cc2401041a0ba02c203085501c00084e0034009803910600300405c0f800d550b4000c1140f415109020820b034402c80c502d80000764010b03841d0312a65800b80785154843c01e0f41301a006002045980c41c180f40ea442400e4240300d41d4004988a010000c011041c2001c0d1540b80c10144211904084c65001414040c0130041080c0d0380400c085200318415516400202401400c85210b55402d090880303602e00325000075541c90000002000c440d40c002d40c49801700725444031800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 575809424 1250 575808174 575808179
    0xe040c05091c080a08130c0f03020306070e10031e0501060309050d03060f0b0a050d0905071e0b07020f01110105010b031e0601021209010c06050a0f0605010c030c0204050717040507031b080304 84
    0x450317049200410440e0194100d149800201d80820034040180110241840c40242140101450b042c0d000b040070b01042400c011044c41500d546071003075018035560802103003c1c4110004044a21210f4500d00440d80c41d0078000039600c0c0d0b06402c071a008600460a48a0845c0300d080300b107081c1c0301680501400d600210104020707480318100100940320303c5103401400c010341d0f01d010000b602c01c010002c0d18680d00c907020500503022034504501d100c3c1400c40014400c181b40142d050080e0003007120180c42080305440d8800c503a40185001130058078844020000d9686603d01c040590704140d802d001e180c05e000c2113038000800b15036101c60148205030020040708245080180840c0d21480d102c504000316184408002411030045074041d0919400108100042210380c004a501581c4414100402ca804c842c0110342c0080d11074990940548001c41da0b070703a600c0380c181c0305007d5142104403603810750030030401803020120705d5000b81c901c91402120008040e003056030340d1444034000c6c0d412a41040008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 575810674 1250 575809424 575809427
    0x10e090c030103120e12060601081806040f020a0e160f0804030e09060112060602061608010f1a07080408030a1706100507060e0304060f120501030305090603070e040c05091c080a 78
    0x8803800403a514051710240107040106074507030002441110381e54020000d100700742d82c000f8980c0707500004c0286510340c00106110750641c0d071000030b00060320a041040d100c070159107a40c4103241c060211034004140500b0601d000b00e51f1028407113041e4001806085007040594414140d09001e940c0550310285021201420040450b40c0503101e0f9040c018207500c050341008042c060031008142c0d640241419180004140700301c007209035021810040301e01300602c00300c11001250415191007a5031440110801d02d030341c00207441104005046114041000560b4001c0000205008602a43c07101014544078070030400128081c1c1d01250f003c1d03480d014078143c05103d04090110b10703000ea81c000c90044040600d00703003103500680041000030380006141d00e0f050742203000e5620011219604200541c51600d0003040c42c000c14924034412880007001c106014030171001400401801041001100c0110300068015446020395900601900380c40c6e04d850314807810884001500440b40d985840a201c60 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 575811924 1250 575810674 575810693
    0x3040218151f0215160c08041e170a05060a24080d0f020607050d020a120c05040f0603140403080405190f0309081c08280b010e090c030103 61
    0x145040c1441c0050980c0c00969440c1120b03035903425140200c01140a070700c0c5009041c031a00e000b40358100040c0714248514558111220303001440d081c50640c0081407503103031080b428822940445040c8004d08089904900200c292008132038a07403103202061980d001c60b0a45840c0705510281c12034000c03100140d920403032600000d4180e01c605180c00040b02d0142d20300211100503030000402540158460181d05401c03002124540156000604681c0b0744104010041d1045100e8414100d401003200a42e1501a014200e00d00c41c00c2c0e242484000021040101503421511585502041e00e0200055081c001d1081c58a00080d210564a42d691961800e6645c02d0010340200d95600c02c1100301102d045c2c0d041e0807215214882c141038259103185040080011b100c54002010503000f4100d0181710740c00907050700f2504811070038010b5030350b80d4010351040000b011017030440b0014400d007034603c0303050110703803001c1d11500c42602d54208021241003805410502211803180302d81c001c0006202140d015030307 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 575813174 1250 575811924 575811931
    0xa030f0903020405150108060a080d050702040609021207020c06090307051203040e0705210f060907090512030d060e0c030a0f1107080c0d0203090a140d021203030f0c03040218 77
    0x504400c110340d039501140448104480c0c1ea000e0381036140085c4031642e882003480e40c20000c02c03a111005182080826500d80c41203c68002c280304000078100c0440d1115040321009180184085481d9060848803080182c02103400c800140654900c0c4829464683c09443c011170015004080450800c8207011040300221987ca10a00c4240400104001040c000a120707414596a054407180b04018094225030030080c8150345e0201001008020b03090080e0701036010074219900c00040e200c07900c06a8160589801854001e5145110b040c40320400000a02d50000020303410441513650701c0b80d042d60500c003543d01801c1c042c010400b00d140710405400082802d65050340000d03641281c07885403541f9074005003084032800030100300325002c401c041c480c0340c82075015070000c0d51510391030f100054140f080c1400340285095080340d91060030b031919207000c580741d5409410a03011003550207038569260400c450110441c104103000907541c07442c001c2601d008a0340940361001481c100400f00010300d0004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 575814424 1250 575813174 575813177
    0x806190501050d090507030f030311030c070609060b03071202122e020c060a050105030c1e010c050f030c030712091214150408040609120b06010c0c081f0e010e0a030f 73
    0x8100543c08a607003448400d00a41c03023510040941c40451502606507030340070241481d902020701c20000101d440c5800ca0700007541c00300c0001010b081929040c3c0042c840d40741c2094240c401d2100118035003a150103404210360084900040c07000100311019611110091111540407001c2c040010807140602250318100c80e83c41c016082c441d501183d036141c0239041301e601000581b50300041110742818000003080c0a010785420012010420b80e6062402074520703058100710781c0c20102c01c00e011003844648950014001541d0361100e8061681d0750b03c0d04a00000e50780c5d01f03441c0411007405c5000700f1004017140c0131a040651004056101e0294041010305601028040c4031050010420703501c00d168030841c80f6202042c2c440c1c4c04d05500511502c81902310415140d16135000d00b0101e100c52050b181e0010003464042c0032180d40303241c004010b111651111105105e045036259050b81c45081c9c0d0400081d0142042240342c003111401030a940d20080c0d20f00198120300c0390b49010074414000030032a240e00303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 575815674 1250 575814424 575814431
    0x114043204030932030a05070b09060f030f04020f030d080105041a091006030c0201020403020f06030703270303050c090916051306210b060d0e01090609030f0806190501050d 76
    0x150703100d82a4190a440c000c01d4144420100c1e03442c038042d0500013102c0803805a0003445060140c4d69169030700c0d0000c1c0070f40310840d0300c042044410399030b40300c048031494200c5841d190340ba41403100c02e1448840064034100d11441800810b0155402d001030b61803141c0b44a0740e1480180e902e80340902004103104c480e071000707220200c41c4400c60340d103860312250300940c40400080450340c03070241c0c010112540d849254085900400003040580d60300c1c0c87e002da001404031100c0d540c0b9141c0240c280c00030581100310919061070701880c4041c41c0c004004180c1c20600944060041d0b42d070724043d500715071040440d002ea0112502000c51405200c5c450702840400c0c042c02c0035860805d5070305596031fa00150303600c05800100000c0000c1020195140040d81100c2c03010014030881d095440011131501400701203101c0f0b0b659400d84004d4901c001d401101d041900508100154809403c00502c103d55036502400400c0d810b0011400c1420080c110840d0303007400410040800d410840115590780c41400c1091100d0b44 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 575816924 1250 575815674 575815679
    0x30207060e0d02070f0f090b060c011e0e0607080c0d0b130e070f050d1401060e010f080c01080603060114060403080a0e090a1503030f110601140432040309 68
    0xc40c41010301c841c0707100d0014558091100802403810005402c1650207014007681041711800510001094800b41d80340411740c0c2c503810340461202d009a021184c820340c00e03ca42000703400e0540e62908598103440d181400818245842c80383d40341c0040d01c0392000030f01c080000402c0030100074060502c800c481c00300070070306110b441c00242074010007948014a242d501d070901d003403802041015500809205a440c512503141800140c190081c2040103450382c0745010003144501400e600200142c91207801c50302e03507540c441004403001c002500620390075104600700c4001e03a40c09904101e1040391700034028103484c2e080c10100343e450071400640c141c100c00240b1000c0f0014481c0070240191942a039074151804106004101d40810060400400d003131500401000040401c9042000d494060404207400000200c0c12030300141c90024400c40340c0500da0002c952584d08404030088400c04a506201585116600080101e03150003c65031f24840d006815690b0106a170401c0d038414000d044c03a854007907 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 575818174 1250 575816924 575816933
    0x9060a080c0714010f0c090e0106050a0207083028050405090a050a0c230a0e040221100f030b0405160314070e01032f030706020a0b0901020325030207 66
    0x164202000042e510b450651720f0f02d00300d80c8581c041150711407170f002c5a203030315100080e42403c0060140508015001504d80e03006402041000300404440301180d01040801c0710100f50074003019192141c1611107035071200d4850401041d142003407100c1c0c4980250034400c1c00d41c25026200c0400200c188481440006a2565050b003414400d1455031808581c9140c40c15800d0f0450789201040001d00011000f444170928103045544111108110314541e00d28400e07905170f0344601c404030f000d6071040c0001454102d4014800c41c082069880c001c2d0108075031120842c03010042400e014400d80200d480c3d2003000840c1070398003416001070103903003039030030381c044100c010144a12503402c1500d40c80d80b0081c410180754400c001130402820070b103c0501081d41580c0d01d0608211400c0c601c03441d0845045402003205503200c1207018041750050441d5112542c41a000e5220305840c902540e04412410004000c0301045c02228481c0c000c481c1400420b0f446080d0440404800f41300e48070415509210590004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 575819424 1250 575818174 575818193
    0x1206040b190f081207080a0509010306030b0403030906051602030d1503020d0b04140d0e091807081b030111070807060f0f020306100306051e24040303090b09060a080c07 74
    0x10700c2c441102d0032a00c2e05040a8a182c0952142e684400600402c691004100390400340d5030512440c0c9401540c0701650300049014100c5a00050180c9100380c0900c4109500342d400403d49500c9480d007400307580e0300c1840c040c15a150f00002c0c0b1001d40c00400c102e124040e421342c0800c540d01c91404105040940380e0300400c5c4103802c812800c4600005000c140024000700320030407028070110000906a010082d01c0c002d01a076641c80c2d40e01d000d4410080490040b64002e48080e00b00000402100c1029903a0031031941d5508505200c040c840e10106e0704c11246044c1802064500c00203091918a09200c075074a8090716070200d40d003901c0e9141e1b50400c20a8841107400b5907084c1500a10b030140e16401c04004103c0c112081d485950300b414a80481040b0035140c01a2900d04404644600116040d00c04041a021912024a07102003208900740103d215254000350040d68069581c0491458980051400a10454040740d41c4580c042c4500c0c07000910800109500400170ba5100b81071881950b070340c0300c50 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 575820674 1250 575819424 575819429
    0x21006030c0302031522031e08160503011d1801060305060f060f031e010915060e0610140d11030f0106110a0f17070c0b03040213021206040b19 63
    0x1400300d20301e400c0095180401860b040124800a40d41c0c503401c0c9039000c0000e0300d43d129406a0881c5102601e070781410301400c00d80485d03864440c04c1c401c081d4600307030f8010200788003201c0504450300c1d01016080345c2d91080301076a0580707981041401060312061010341c0e10510050090000d001d05e56170070080c0c0c400c01e009030340003075200b58010700d017034200000850908980100b0040c00b0f07207400e07030854089590000740c1a100030703101d03142600798108008005026041c0d8010107400d640540089102d4074900354481c5088035490a4450700507101d110400c66143c044004480001c1c84002501c1c141502c440300600c104042c0100c00268404007064010749504119040510482417030010401c1d19049880e62280e90901000703401440180e0f82e810b41710760086200907154040320000c1c42e91500f41030080700e40303480c3c110400f0200c070780e92100b074980e196000b00c3c4c0413401061100002c02154404e802078880703400008074000d82c140d032002c06102c01084103403d03003640020b007000002d51445a803c001c001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 575821924 1250 575820674 575820683
    0x307080303040c090b13050402040f020f07060c032906070f11040b04020a02070b1305030a0b0a0c02010504030c120c1523010b12100509180d020c010210090302100603 73
    0x407245040e007054202c80720603910001d41c0c1c1e81410b2446030716940d201e1201103e0703000010b001407551554004134005024210350701803290310010b950103502084c1c1c80074060081c4102c0c41480845415541142a02c00c007090b558089095050443c0c07120b403998400e00102c10700038015500b440110b458104040d8551502629501d200c01d030403229600703190041043c00c403815101503141a9003560029a16005407040c10fa0300d6002090341665501500c24510003000000c3c01c8030030307a0000e400d1181d49944261041d40e01c1602d843c0c0722201c0140107020309807065800d612642e40c80100d80e2200191882442c00f00400c1040022407080090801d642241603c0d18084001a514100034103807015040080a4030011100d20030040016034a414101c40080e1200019080c25481d168200c18803031120781c03c0154007011144c200007680b080340c540c46003020402801c0303a0a482041364107903154140341d640e16005802000c0401e48000180d00600a46442441103d9100d0030075138101d0111503551300700f180e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 575823174 1250 575821924 575821927
    0x9061b0f0a023a081e0702030114040305041406070501020f120a09080316020a2a05060f1e07050f0c010e19050910090e0708070602030a08040f06091a010e01060927060503070803 78
    0xc056003424494070304d040f40c402c0ac07001d55504080d24040d02c0c9004611400300c0740100d03865000915100c40c401c0e604425400402903444480d4607204203450f030000d4458881c00d03510640003c0840e02c00e402144c4005421219562468070381050316152410301c031110005500c52103013140c0000c2c12042d850358841d1150b1100100004e14056030f182101d04691007280b0424045c002256030902d150704540d40c000400c1002003d0140840e004900c0380680c0314040d100e400b501204250000c8003080c1002c4140c0c1c243d035484010b645041c20003c070380c120b107060041d00320001003041c07149003800522150080e8404402c60300d01d0750b4520f003c2d016100b1900b80c40b003c0d900295030030800c00001b008604007904582c0065410174144d01d900a0114000900140004809640c41810b2003600c1d4010750302e480d00301c20440c101042c0131388030b001c99030028420409840c01a400001d6a0b40c401e41c52441034504411480700320310800e41203902c2e60b005c000c62000c1010b9450030000341c15501003050700014403080c000303075 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 575824424 1250 575823174 575823187
    0x606010905120c091b0f0307091d0a0917070c05030c0d0302120a05120123150d023004050105060d020609061b0f0a023a081e 55
    0x400c54000c940c8414040c2035644541e100d224000f08214038503c5080d0b034800039907a1500420380e601c090032213522004940c0003880340c4824920500441c45102243c48a9149a98503d81540d0400369025511104071400001c624011040e0f04100201c60003454100300440f0500c00002441c0e10108040f03d46c1031a464040105040520481042920460789040d895906880207500c034500d018000b41d1414000440000362400b40045c1c80500070705507039542280d83c640b504940104405241c16488901e1001c140c443ca02c7c00501040105001c1d451a0f414425480c02940194000425982003043c0d5605000c1081d80e11801d8841d0004c008003000f1250304040c203006d030840d0b402500d101c1c000d15465000c90056180d03241116408407050302c13890394400c40c01a8464031b80c18040c1110700c0e180142047c00d00305400c000f940140507030007100c0000714001c2203003140314441c4148011641c9074555504031a06101e2501000310401c0c040c1074034504e0010300104642020600c407005016014010a01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 575825674 1250 575824424 575824427
    0xa0209030a21170f0705070305190801081006140f01140a0201290d02060d150f0612020310030f1406011d060d020d0b07090308041205010c021c260405060601 69
    0xd00303c6125124076510814241a08058040403004060000f0310000003031041c105071286084694544920030703140120755a40700d0042c01c51100788501d134201d00c18400000121201c40c0301d00c108a5119503d00305200786008248001d02d4620030707566050160f1049401c01c011111002061400c0c01a80001160709400c42c0c418840c47c2440304084507000b506000c500789072141024103003040d4040381d03095100d5080300e450501803c0d00d060044071603c600c403c00148160041c015900f80c42c1e4945480e00c40780c10a0700300c80121300084414a071000342a45007000411510f140b004041402441041600e401c1007603198504238080e444503400c5070680f21801505503214000d581c001d40c007200c003081600000d8001401c1a02a080301420304071614000c01c29090003202d09a000759400307101c5984495442130f44020402c1075100c181c42e194280242d01004070b01c0800e001e50700015078204101041840c0714101d1b00410940c400c2401804403515900c40552240241441244210010291840c14200 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 575826924 1250 575825674 575825687
    0x11010f0207080d0804080c0a14011a0a0302060915040627030b060910150203090a1e092003040f030f0305061302070503190f0e09040b0a0209030a21 65
    0x1221000c54001d000d06008201000c070311080555150f140c0941141ca85003031600a5110741541c80041c0d2196104001c10030810306c5102101c00380240080000440607032030002e88807100304000d60311000c00c250074030041c50f01001914041a0180070801030812901660344160301c50381100c5d002c41c00c4c460784100c1030b40895034400360545038060a0b8060b06c1c40d60781c41c1c100740c10019028603c9683c2c0c0d02c00003080344c045014400c00501d03010b4150580004034050181d100c0d032010007030364010424044082411200740070004151301d81440a01c0001e454104200c004001c0c00340345103000ca404003030101000880b400034501860280c0c0c9018039150203440c010307203822034000016060504181c00c20803d940c8a91550804080e00200945d8504862038030034198030940082c400e480c2420f200150505500c212160808115511640e40700540e20082051030f49003214010440c1c21f20b140010b0503810707590050300c0044009011151281c54980e5861501040c0391044040414030314010404581c1c00750 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 575828174 1250 575826924 575826947
    0xd1502040f0305070f1d0711010c05040f210b0a02070203062815120309030602040f031b0b030a09050c030a0323090d171312150e0a0b100f031101 64
    0x51245408a2401076202c154598400d031860f540301c85140007c0c0a64082c846180340c40010400800010301c100c82d02401c9500700d1300917040701400726a808501617401c0c0000c204401c6090110590303010055442c255254401031006464903000c0c8040d01c0140c5003048564010b007280400300e0006525280386520480c018800b11f409642010310b541c503d403e54510140c16103141d82c2010715003d030b550500b41c84480072a407000744501d10005000841103000b8000c002074900c03d08074440c502100785007900c40c824060103080100003003000070400c0100c2d03682c08802c540d8400ca06664004400d10000f81c1400c0e070400003540451020722440c410221a02c00c018200304526280c4c90802d12840041505071401110050921220b800c00e00401c186c0041540d0070007201c11414008240c5803a0441c914510034123045036400354482c00411507101b40d0060040c00325201300205510344041c4c840080c02c80002c0c140713a002c407203041c2000ca07050301aa144a0f0296010300086900d008105000426010307030700 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 575829424 1250 575828174 575828189
    0x1081c05030423030c06010905150307060e0402090a0b0c010914012a030b030f010f0b010801030b06041e0c051e0f070809012a2a03020d1502040f030507 67
    0x4200b0403000600f25980c016071510010104240028541d950724070b14451482030b4400c1e40310318000029041e0050304024481d04c91092175001c8681501c00b899543c4006018a1002c28030342d0042b5000c504060303020b001580002004140d1250365900e220f089a44429803200c5543d45074030310602845410030707842c00142c0b0144001c025049408007949100403003041480700311726500001a040602c6070304154050000181a90301590406c048240240310b003d18601a850030f16000c0890b0398042e15540341201d4104440c86201e940741c0c02040001c01c1900c03284540d514280d041c280d001d0485d0700c1a40350041e03260310f40e50341d614040c941503d039408c807558100420800030401051811000026100d003194400d03d220b0f150119100183c036520303d0061403050b13142071011480110300c1507043d00c0121030300525040b800c2203080800400c0004041048002d05d080710704040005041c41200540c45d01c1c020a522061315401c45200c1050340c0c8070307902c460f40c505680074040c810700209001000c000c00b400c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 575830674 1250 575829424 575829427
    0x903050a080603100509014b02130b0c0f0105010608040f02030703200f0d021c030c0f150e0c01050a050d0b0d0b100603090519150e01020c0d020703052e0501081c05 72
    0x460042c00c012a51071603230300c0c140c00c110b425200e151605980540e0700410b140a0500c2a00d52600900307000d03500b1110800c42c2d103100e003a841201d5071a061107200c0c142c1e00c0d00c2d52001c0c09075489072034a202c14941c2142c00c03601482656000004140b000105100b0041d5456110801890500406c4040314114115620410820f41c0100060f42c0d074075840c1041250984c1c0c1d421028116040c10b5607417007413101024200d602c1803400c501c02c003c42c0455043d072484c0991001c215640800344a59501c8203400071981c0480e50411a0f00200342c06040580703090009040d011620403d56804034aa071204030604403030f81200c50040c0a22100304844640c058001071804020350740081d100c007662210760008031a540e815500100007400b0f0076407006010145094001d2040203a03e407600c84c003e511140300002d007030045542c00c0300a140b0100d01c00302182d420030000c0070140c414403a070241c03c098820380e00c000c40620ba80004001282c600800c0c2c02414010301503d14561070600d40c8540204800c600001c0000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 575831924 1250 575830674 575830751
    0x1030b031b150c0106120b011401021509030c0123010b16081c0c0c06110703120b0a031203050601020106170a0605090c13060302030c0102010903050a08060310050901 73
    0x1258101c01e07008021203094040c01c5a020710790034a48036400d12404154200040840d0840140348280000c905c0740310555051380e65003d04009030707002d58020382d00582190905250030020003000ea600020200c080c3e0b86005580d202682c00c5540e24810900c0c0344240c0c2d00218a5000c00034036850040140d840300328540020300700e84510a50800100401c41d0350b01186040c4d88900a00c0b0316549807140000c10400e000b0520030284c4074401d01903007140c2250170b00001c94151500c007070945001e15859210711031622030101861010702191200140c0140c001d000000c04200c09824800151441e40c50015090070110002420765036180c1011911a08888000550f17200c001f40c48031a0a800c580c0000b00d548465004504002c09a134603e5444018174074200005512a0300200480f44210708858a200c00c0a00590036a00118805808a4801d00008100c640281506035119000400b81c9030504250716003001124001c0d00c003810640e65420554840240d000d034807414101c482c007004500841d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 575833174 1250 575831924 575831953
    0x20a05041502030910080402030c01020f100504020d02150a030b030721030905131505090601051b0f010c09061b0c0510030207061112151c02011806020c01030b03 71
    0xc1a40304000d1204160464454290300c203106840c29180d000300410300307400f003060004003452400e4409a100e409804d62140e165800098500e204545400241a90200962403c002003000410581c1c10044085500c0010382d600007001c034192030703480300c03c50b1282c400f80da005044580704854207001c0d038489a02030019851009103120320854126507000c81c0c801c18607003200c0c4003207c1d60040e5004043c3d400d8002540e081078200c150090840990541c0250340d41c4100300c1c40310010390365a40440c000300703c104400d00c1c241d40450764200080b01290250b40c1d032102c1c00c6003100c0c42c0400d12000520140340c107008296120b80c00c0c61a600300c8000f41c01000b0311586074120407020b240304442c459a20114030f1082140280c05a48000340c000008005000141441900d10750200d81c0b1443c1e2200c04000246c4403801661001c0503852002d40034616140c00d4260380d0361441c1488a00f030341480000707c0d02846d043e8400400d10060b19856002d004020601400501900e010340400781c86500302d1041001c009 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 575834424 1250 575833174 575833177
    0x71d07080702030f180a090c030c0203070f020420030406020711012124030b090d0504031104020d0902030d0207050118080c06090109180b1801031e030908070e01090e01020a05 77
    0x1034942103165a65045d01400010850b031001c110f00c0d42140442500040d602240c1d4444440c000c12a1070621220402900898682c85140320041402e4130060380381016042580c00303c1003034086507040400d0045017083d41e07400e9800c116003c8465a40010b07181c6d0030490003c0c01c071400e1060a00300f2001c507009100b0004400680f403c3c1c140c10b41690b03400ca42e200741d40d91080d112281044140394071200303522828240a1140111152602841614050020035109100301d6003242e401c843e440d12411540300800c00650300007103c0c00c0104d40c407841942d0151307600340140040303040c00760008d18805181000142074450042061100011101d104000310701c004100c490f5013540c01c440242d03940081c3d200507511080aa0420300b04002e01c140a650304c003040d684284115030007114039942c090002070741102c06917405d0000800da404411a4000d01d86d054284801c50140300f800c02010041d00c3e020340f1803034948203a001284003000100100b04038a800d100e48502140690000e502c0c1155030b41014205 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 575835674 1250 575834424 575834437
    0x15180f0209060d27061415060a0f0207050a09050405010e01020f0a0804020a0801060303090e130f0303050613020f181806090403110d1e08011a0c0f071d0708070203 72
    0x31951141c15607152050b41e80c13200345109039108140020004c1506140d00109082607038560030038600343c04038840c02442e00c26502c81c204002c098502e030907004030046070041e06410307984040d4441c8aa022599a840c0c40c10303c8060300b03002d4000509440d05040c40d07425610309181980142e481001101c600c03a07040b0301200d4818410b400c0c440d0031500e1b240f02080c0c820605900c1200c2d95482c2c24008010150b1021111044494580c1003c0e42a2641e901458185403605401845183c94050140010f07000390010b80d44401c00034604880f02e0844e01da90000d82c1c0c024206020210000612100710100861410a100c030041d5520369510580201102204101610961040028500040c01c00d442900184a018940030642e441241503207805040c143c035007001225800c48800310406041e200e200f669040710b0f2860701485003415444c00c4001e25900c0011082d80c10b0092039581071821000304143c500034910981102248900d294915100e810003408000402c040d031400d0040740c0f9400000d4a01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 575836924 1250 575835674 575835697
    0x1060f03200901140d11120a12050307050a0f1817070e010e070507022101140105010503280e030c10050c0a052205030f0f01230411030115180f020906 66
    0x4000816061600d42c0c180c01b82000c551042001d000408811404210080001c4c42116404140303940c602c0265041c0c00304030b4004001510520024800781e201d544004481d1134030b800c0181c400d0080041150200c07109411010103180782d6442004a03085c100f0034040107011115458241d5410501c14194002014142c9401c105003c5040c40665540054103080340d403c91301c130090648030105409000e0900100980c409190070350000540c2c2d4090700c200c0f03200780b103200407180140031540c0840510048031900185003964480034107142d160100002d002e0740003072500802100d0a0028000159880141a0551468113006051015130880244c600f00400005031500303403a800308640c0211302850b8031099061080c041d101403d60300100340b444aa000070002400304015903040c0400a0181e4000b0b008107400c5503001401140f010602004800002000480c0c03914111591411880060b0005860302c114100149034071101482070362205c540205040d420170b0800000038910b80a0200e0f04107 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 575838174 1250 575836924 575836939
    0x10207030504091a0901150806040b010215041b0b12060105070c030314070b1806070801050f090604150f140103140c0d09060509010b0301061707031401060f0320090114 74
    0x1128400c0402000c804c0303560161119446603501e004200b00081a1480d1601040265001c210207041c5405048070703203d01a0001c000c0f00310001000030719880b0003030041e504885554000154242141c4440006040701840d887d1242036000a00c020001d02410803410700104109100009421500950072a6003604000c4890f042c0040075402d02d120726100106000944001c0000c60407901d0140c0031652402001c91b0400d40d113428007900c810100f80260f590000901171100785620740032030f00d25170041d40580080340842c0c0060b81c00c410b26645403c881d5494881300703814881e000c100d80c111115041c0900e03041c02002c00c82d408005003494094203000380c0000005113801c00007002d40000000e00e6000004015074038008445900034104014402d100c0e5007402000101d40e0007034020109004200c0e0050f12180c5d1441e42c1d4030742003540081650703419549810000071481000100400103501440010a50103402a80543c82c0001d29291600c03504001006000300c5240303d8070310804131000e0304c844 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 575839424 1250 575838174 575838191
    0x1202150a030204260d14040b0a0c05060708090d08070f030507170a0c0306050a050a050105210f07140a09061d090a020403050c0a03200a080a0609050c0301020703050409 74
    0x85000c0d1040e500400e038540300020070200f00341d821aa0707401251030804140d48201070b456008651b41c10720b100f00264521018002441f81e1401c440c001d00b0701c160981064403a208203a0f458034100319045440b04041030070f91040119150091044582100040c0380000082c549004060409203459400000b01a075030000074403480d0207000007001030541c1c0415140c403880d008081501804088400310700290921344002024100150440306641000f450884018204401116140c200d805039080801c440c03400a03108a04480315140142624111350a032841e1403071002d020403a05002c0140b40caa020800d09401703d500c84402429204945010800000d0106044034040011104280c2c0501e65500b8003040d0700d0140d0081040fa40704e90f043d200d0b00328040e4100200c1c2d241911001e0120082180c02c000350b0490810401e80040005160400d410340b80c00c64145403d05101040710035503900da8021082c0007080260f281c40d40d0f0220002d500e010080c0c2d0b0020014019441211650398552160 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 575840674 1250 575839424 575839427
    0x120812060109090203090105061302090303030c071a100303020d050c0c1003020c01020f03090c040603020319060f0207050606090a1e1d060c07030e0a0b0327060703151202150a 77
    0xc6900500700c0f030b40103646034189004418020202541ca80703110f20849013440085900900030b07034500480c014042e50550780c07503844a81e550303806408110340c403c0080b0480e0610f030314805d461600803032030310701c024030a0b504500d03004e49400400003a01c0c040c0038003840858502100096070704007810b002e48400c901460207600076000382c007030710075202810350001c07500300e4560000c64055841000c01c1c42c1205c20180b044024042100c1450001075015000100c0d10144040c0200d01800301601c103690000d04200803160050032a00500801c03505034002c0428000075240c070b88203503608103265250130040f81c40400d0054010320400b280b4008820b0725030030880b944800c0c1114064030680c0c0c01e402d407005442c3c64104504144d02501003100426103d102003211410003a1031141541d40c61104680b079607d80900e01c00003138500d58400074171609a4002084548001e10609004a43c1e81d180882d4404040d09400c15440d4182c00c0002c84d08410081280035075540320440700d2180c07406489039503400da401c0c1d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 575841924 1250 575840674 575840687
    0xa02071406120a090f0c060f231b0a0c06170a050105010206071409180f0106030c050403111c0818030616051614070911090d020402030702100908131208120601 70
    0x103001c6c01d54441c01c400050f1454010305069160006070340d074088800903603a844296244400d81601060006004034992800080780280c042e60010040b41d40b4060590b691214164907600071900150300318013a490500a070a00c855000708450600b4045e640c14800001d40d02c2a00603c0c0b40308010b56050b1045d646210030040f201304100103081c00c3c01c1e6959034440c210030000141c80c4c041c0e1159041000180082c40707441a90b400b22625502c0c2c500d041d143d42c03150860b05030005e81041c0d106c0310400700b410180400c01c480021041c490848503890320101090192121032a1061901a0304a1010050320080e0100207000c05203050502e0350b1901e511b0798240494226200300240203a0380d40c00e04030f111000006000045a807140c40500105942d00d03034140c10740c001d0340300c001c1d08403441d02c1c1058010300d815000b8540c85266441140c909243c120b020070196481900143d5000b040003d81007000703029110014094507001900151301400b40d51081018800c9400313618600d090300c00483c0060b80321301c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 575843174 1250 575841924 575841953
    0x14030c0f2b0515010e1303111f0f060501080118060f030b06032b0c060213030f0b0f011d090c10020c1206070f140705030a02071406120a09 61
    0x101e01150000100038044404100200240c40d20700c6004042d91a5511032014503060351081070b40601700d83c0300c1005081c03001c246004101d060100c001d0080c0ba00d40d80800c07413240c00c0c04075901078805405041184400b1100c201c005c40c158035003440703400d200d20f98112a5141c112900c0f250320420300c6440e040340b4001040d84d41c12560b0828201c2d4000000c1c0050000a036025040481c150340d41019400a404040b0000c07800781c0f40c5449005095a00e511b0240a19112586c0240c80c00751510310710399400241c552450b002101c60030320380360107803042c448000107990b44801101c24119195040007442e181650300c811180209020000000f42c900c0382c18840c086070b84601924a140001c01c440000c0e450311003c0c40c0c6103014a00703028841280c3e00300010344c03601500c615211151481c2c51400c00320b0702550824005001c0c4801041201300142081004103090300075a40900ac00c0da041090340408180c0300414a446186d040c000c202c1414005c0c02000d4010131010070015042d4446d24050b00307103020f01d2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 575844424 1250 575843174 575843209
    0x40203330607030503100b0a14090d0b072601080a0f060b03070f150e0f040c020a1e0312060503030d051306050f01090b1203030402121e1614030c0f 65
    0x700d034800030150404080d40c020b0060756030028906d5100c585015035070080801e240c00040340300c9100c040401034a4021b000300e5102810326203a0140540f214211480243c3d0140c001406500c01041d2442c1c0d017a10381c0500103504103000c3e415516100b0307010307522105180040c0c0f6000785c1000100400074035074010300080744043c042d500b4980e6030710307690301d458089486920740e210340e40c0c95035a41c10f81c0700c1d4050302e0800e5001400300004440002c1884010000c0d00080310a5219a50100c070101d071f4401403c802e0441e015000465500c40c0f45001490790515442d6000303110b08083c418801c82e41c020040d51502140c038800090701d551490069443c0e24503941000c2e00252901d800c0c0a440390440a00f01d040e110402e000780100b54114052060507204124914000d810a01c080360062802e51003a0741c80f40300034070484194025588250002003c50400712196a01001150580081d220f51a000803d0421610410b0342c0045c0d020a031200910300c0568401d5241d0324039000c09940b031060070b40111401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 575845674 1250 575844424 575844427
    0x50a12060609090b03151803071410061a03011a0405042901020a110f0a1502010603020103050615030703051b0a020615090402130b150a18050402033306 67
    0x907030901511201e0240140101d050a0440a06403420f0004401056028120b40c0344540e40e6141c107483c1da01107403400300c0c030894041000044080b40f154864160700b2401d610161541c0c204014050044407e2503000300c61084d0316520010010391401c0c103580c1140c4640426440d400000c2c8800c128900c102d40189034024541642003402401558102d200e0b0400480b02c0e400d034209070001680c1d43c00a07450b001301140c0300301201034500e0900303071308544249a01402c0c6c2c82d4485d841c0d0300d449e40d260b10241114401070395602010800d56902d406003d80201060b12110b03000b03084a0b4400207030b484024401414540c640020071844001d00a08642a84c0c03d82401900c4041a0300002d485001c01e4441401c3c80d02d802303c080c80c980ca050602d580c042ca03402000c0411401c16101103102030030740b00300c050780d014010020100403159030340000c0440c125541c0d5160920b982908104090300e10507000315001d94418070821101000a01d003c03c0c0c604144201c0026900e45150510a4223a4400420790811b10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 575846924 1250 575845674 575845679
    0x20703081c14191a0d08160b04110604050607030e010c02091014031c08040f0803012709080a111606031d0c10030c0e030d020309030d0c12050a1206 65
    0x6580c4a110f000c1c42040c50000000018901450190b412a406002106041c0b00e540c3c0c3c81d510345a0f005032181c0d8820a0000c1c20840802c101c404020684041a01c000f19003804200c2001910710608204c2c1d80125419030406007400007185c800d00030040e0090901004c0020000c503a0b01441030410f02c0f0342d009210503090b21f48020f005600740620b00c6426042210303a4048002460003141100707460515100c0d215890292103400c60b500800a4400c1d112040c10081e81404503020318000e6001c0c044000400d02814000e00da070403131105407c3c0300150014580716114001031560802c403843c02195141003030400004140e000d051500c00521800c1200031080b000034210b805800a03281c440c06c44030601080141c071034410b602e0b108820b400f41d070300c80c8070070341c3d68000705021303a00400700d9481c5480d00c0c3d0080588c02c0003007441c0c07901c2450040050790000c11380032028942041000c4040201e0300c2c0030340300b49410f55940740340700442c00342d10002e00c0f0020812208407485021450404c0441d810203000059 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 575848174 1250 575846924 575846951
    0x20304021f0e040b040509060610180b1207021924180b06010f050409022a10230c0a1106070801031e08120703020c010f0f14010303020703081c 63
    0x40d034000b22035016508007489412580303400c1c0b240310b01c80d149100c003405407941c881c3c0401c200c18200d20b06580a11482c074403c0303440910f030482082e01030040003007500e99a44c40d10040c3c91500718020040d078115845000c0b165020b850b0b6081d50b49485600405140410004913149031442e05454200203040c2e1a0032030900d5448100a880c10640d400b424074030075a5110310b001110a400c2d1071000c0b1000c117000300700c104080070082e8028002d03104034030080300240000c0c0d0f900568809450400300c40540c0129042c2c0c04000036441a0780340148190f20411252440210151000100805d50710044001040a03114140120030040800311120242c078a58a030410000d02450707028001038420001011040c11200c0c4601c003950403498103d5262414000d0402e1100b54042004280d441099000d202484503404240074030b10302455440004180701e130012268904550320001c8201b00403081c20010004241c0110354503007070740d03081404c8658561b00124800c3c0592042040e000d9803e10b422181001c15 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 575849424 1250 575848174 575848187
    0xa0f2405061206091b180c070b100f0509090a06020705070602150f180708060703020406031a01050301050108361c09060f02100c020102030421050d020304021f 70
    0x200e40c200c0b440080c540100464541d41c00f011519080c1e154040c5204c0d040c4107003900c400c050300340d0008100d40d82c81c42d04580c0c45842100180d5034507000103c00301700c43c0d080003041c4603040d030701281611359080803604d030084000b506d07032591003094015190440424642e130000e00058403030300e802c05001d6546401610b030640ea03e213940c0c800c00c0c0040c01003e00c003221070300e80716072014025101c0e40902c9055484000360400160340b2000f440c0343d1441b1307032140000c000b45c0c2441858801c0b003140d100141c4552800e20054144c0e03054003506441c0d0050400e0190f50f9a8110081da8103468080c13038000d5469440004c5401c52000c000f60714160074001866201c0400500030389004a00c51b0442512800300d090398081e035545888459113000724041250911034144034542031842a1420b1048600540d1640d001d501115030302003a40c00143d400008200c00e018500c41d401034070168104110101030790504c8014200d024201c007860328036400101043c05c0d503840081200e841800580a50308424030303814060400f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 575850674 1250 575849424 575849431
    0x6030a0b06190824100b031b0c010509030c070b0c0d140d0213050f01081005100c06020304050a0c05060a020d030c050702060c0a14010b030a020f03150f01050118080a0f2405 76
    0x106150028040179542d00700001103580b041034241c2942c5a61410041e01da008284030a1184020302030b081c4000030134000e06009042c0040610390719081c01100c075040031441d0700b00f0f4030204010805485041f40001d00c45450440320301c0c04d07164035000091071000601c21000108045800480c1c0c000300c203581680c00301c0850303c04441d480990342000c1d0040d20151801c6445044648071b84c401000a400c24481406400381d440c0340c40e603004c00e0256264412030b00107580503135291344144009001c105020428202402c411901181401030440000755504540845001015154241002d91500650503540c4465008000b0f40e290144042c4e007680d2400858416902c10602c00701d001404101072082e441008000340140c08100282d400740078807201f40e0350100b601b611440d00ea2041c611441c0d4103030350141141c083e2050455241000050a04010f81100480c2c4203004100b0890000001000740b40b240c1d0041451100010500700a0f002d00003040b400d403e00ca80c0c445c00c09050120383e5003c40d20 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 575851924 1250 575850674 575850733
    0xb070305040608010e01120f03051c0f0515031023010303080703060b09010e061b030a0503250c1101091824031a0a06051806010806030a0b061908 64
    0x85a81ea40c8060385001c175028801d030f040d4102c1136100c28012580d01011512524000d0405500d0803407540d00040700e105092184400a503558507504000560a004540e04240d4000260070031a10030b000094039440c48031868502543d48800c03007100c80c12448038010024403c0141c410030356a4a090140503420107c41c1000001c2c5884004500c0716030350700c01e889403450182d5580d01c40f41d44030b01c20b1000c0e80d0f00541c0703008a80040d40300521000700e401c20080003c40b5842d51019220300701048111008549410407083c0d0807801e141e8035400340e80c005000100b032500600d11018150201d001618400150340254400d4140310318011603040701e94020300203003094602c0c043c1c4582e409007007584c41013016000c0140b042200c483d140107a50045d0000c03030303008464440006141c555031000144912080e10f1040a01c06000d02040a9580c100c80410342c41b500c2540580000b9142da0754280c5e00c4000100f4661050000c00031800381402c29824038000b61042a04944e1045200403000200340c084005d03000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 575853174 1250 575851924 575851937
    0x11b030e0105060a03050d11030f0a090519030b0a110c250b0301030b070f210f0b030318011d0d0b0a0c050f03071427030d0201061404050603070b0703050406 69
    0x210759040c440c4d442d000b03c9402201401c802c00b1a00703801c8583c0401d8140403030b0340c0e103c203000020305140c61000410002c0e1080e1500e224481c41c143c1441080c3e0042c025884402c4021031040010400c000c03407407503020700703e01d600080080c400005042a8011114014180c0c801d10f0000744005512226011082a104003c1c0d00180e5540c84c9544680c8000d02001740240d482001080c141c902503100340c40c0342e6140342400005402c0c00842c0c90080c0702c00c0700c50501c0203500c0c1c074001c100c0d005103440f416082003c160061841c00c1d011084500502c0190400c0398104030910501d83e1031f01c5600320090480441c001d01b00480704801e0b041900b102d0f201550202441482e20703026140711801070f411a803095144081940c11030750360410982b00039480700300c2c203c0e00348404c0015101c4048800d000210010748806000101407890043c9841d100b03011201c1015a0f240001c00d00a044000c80c02440c0d00c00c08550104243d581d06004c203041c114158003290035000c004c50b9901c10581c020000e04240d440603960003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 575854424 1250 575853174 575853181
    0x1306020304141902030c090c04032a0b07031e050903030f0706050c120106080a1419060806060d0f0804030c06020a03031b1b0c0e1305060c0a090e09011b030e0105 71
    0x1880d001240781c83c029407503400440541ca55081080718680d01041e030403407640c181a500c1d05da41c5400300e200108800744410f00c5858181e4142031414140c003800662250504082241d60050a000c41c0241e840e440f41160a19160100d841507088940c0e020021342900d8445c00b0645a480f00c2e5001000d046461034103000001d030b21b00003d1000e94186860000144000741d01c3e105068a0040380508903810564540508031903900040d00031a00440b100340c12241502c1e0000059000c54101d0f400458140c1c0080e0148941582c0301c0310b5448006800030450300c1d101c4c1603031038804854420f6a00c024484029203200107121030300072030110803c5010f924140007503090742e24684624886a0a00404a58004080312050341d01c5510b0040b85031145801c642c0f226103c250200c503104e0119041d0060768964004142000014001c50ba08411002659402c8c10092000072301100154000c0d1400c40c461040010610b140c250041e0003040460280050106a41400140500444402c0340031560030071010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 575855674 1250 575854424 575854453
    0xc060f0d0b1c03050f070b1003031e0801061215090b0a120c0e06120106080309031203060d0210090e010b0d0e0d12020307110f0f01060506040308040905130602030414 73
    0x8992034142e801c0c00341204507041c0c0e40607941a00301d060340301100e40040c8402800070b03003441030807400750807128036080b442482d45c03800500040f140302e1040368201c441d0149070349d000e4018201b6030540d156401d0403031041300f0300d06116005001c0d01d140100b00301d4000c100090044c0f40369108a03084401501c030282c0c800d4403104d02c0c03207007101451002840281e21810401040c0c2082085540002005114100321100e54580e43c1c25204640c11070101c0350000a1020f00d9494104841892001003042807811031601400149030b681c80850040d001e40c000154000c0028402c0c40c90782c01401c003e08540c03105585401c0d00300884d410803080d158402d843c00503100d2480c9000280318210300d18507076841000520a40054010b908060201000e12185c000c48000c1c101080c880b024001c014440200301d0300c07242d85807150a490f8950f008502a0000f00410703c0801d4100045805854040c1d00c007043c42e84520040092101340840c0140000d480172052004001200a01d004012002d00880340401c0c4030119 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 575856924 1250 575855674 575855689
    0x702032b02150604050612010f0e06100501020c190e0702060133121b03020909011e0306150b0c0c01090e1003172206080c04030309090e0c060f0d0b 65
    0xb00c4040c89903203880040c1d03035803400341c00c49540b190000d002c1c40551940752007904d0964854030b12403000103843d4504a04115010081e0541c4070003013004403080c007498000041e40361000d5501190040c14180c0701c40030b02a40c840e01d090004d10a0480100f542d2400d000c000703407103160030701580714200d2401c01c480c070020425207807001d11000340064200c10b040c40a0401e42d040c80d4602100064503840d04400701442d0104038001495013890746002d60740f090058100503c004058001401003140120440c100e8080459920f0a41c1d41c440000a0385400c0c21105003d450602e0b4480c4211361400102d500d5980004509020f8950007030303c0d001c0200d911240030031083d24003200c1d214044001c102003000800e540c40800a0800359100084d854081c0301043d040c402803072034142c800340c542c1c9250300b0009213501403d4a41c2c0400f607000141d007024210354004050000c540700c1c1000c8241c4400300794141200510410080c20700c024817055541d00600500040f940040080750240e902c1c10811b0390f1581010072 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 575858174 1250 575856924 575856943
    0xa020c0a230a1e150510030b180a0308090304030b04080909100803090d140303071806030c080a090302011e050108010c08040f121803060603120e01090306050c0702032b02 75
    0xd02c510708042500d030b01c0f090a603e0807103050701c00b01c011500d800401d06071845490300900c009515101c8840c203504280c015500d01401800c200005214006120040450440b840b280e261401241c280c40d0024100e244d80102d0700f02400301e048090600003040200c80c02404548e1050b00c465071150740700360070681120007900c02e0410369001086034020b40d14204128000b42c51060541065102540036840e0bc0c580085a40202107000c114014032524208070041c8002c008503d010700800c4a5002c004240c400098503618460b5152148a800c01d4000e410103103070940018103040d028807401c1d00c3c130702c040c003420b104d6110300d9440c2019603038801c0d00c01d0b0034a82c41940c10009100802d111661060503008500d1800c000700a00c0220060602d000400340000a6006100109541c0d05500f000b40b0556501c014200510a14000000450b60000c40e8030040343e80241b8009801e56070708608064903c1104070081d0b05005000410f4445840240d2203d8000300440020101c0d034030008017a0380c1d480508 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 575859424 1250 575858174 575858183
    0x1170405071806170d090b0f0d0b04061d070912020306010510050903030408010e1605180606090d030324030b19061809030e0411070b0a020c0a230a 65
    0x150140030030400c076a02c00c00b0ba0040c1d200002521503460888014035001020f00c1e40c200e401c00c2c144160420b44c050760b060040c142e040c446925040c0c0c0d280c298501031080784512034100745c45190042403a9955030042e00208070342030b04240401c0308405c64a401c00c50468890300425440700010030401c2c038800b002c94032035602400605a90742130000300038040603030780c5025042010401c090421900d050001d4130050512200120381c800c01c0400090905041003600607419501d0802086107036205881002e03000c0132501c100084c1c3c0c480c500480c0d40f134480c1014860b0892a900c00314400c15516074054400c1004910b40720400d26681600d99407008400d100c0038040c080f40e500494441d40c042180480c0c0a11000e45c0001c403542d4034482c0006400512240701d4030710750380700c103130009140d0032030a8869080c44c1107a0400400c0300032a00015180a0100e010300000c840720001908510564101c8140a88690440d8649051807505081e09003006504a94508170540a09060300c1e00040c0003035110f520 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 575860674 1250 575859424 575859433
    0xc0d03020904230403030c020d0c06020d11030c120c0c0a0b2a0a0e1923060c0d0914011e0219060f0b03031e0702190803040501170405 59
    0x41441240039400c18074040303510640c0e03268880c074000750024107240152070f030950720a01840c00f414050119030b6a400020150b401c04c400300041142e0101030304032120b41c0442c0041e00d034500d509840c2c0c000d11403030340101d15803200001886075401d10a005085400250a54034006507641c00490729603019859098645d90311020f07a000000f00c4480c611b9a00110381c4034042e410401603018800540340b81c4d091700c07c0003c00090018104c65005581461040c0c01ba5204103003200300f0500d81500f20107070f114541d032071599015001c0780b02600406100340a60014402030311249914051502c0c1c1c01281d0071000850211a000200b5480988400b2401300050719905244099008036441c1c810031244d4440442c094032a651400b5580020354541c0a8091800043c43c0c0100100640c02c55141144980c071a50042c0079050074a03120340d5000d07810190b018411601c50350180702007041d00a419000800d00d140320030380800e4850340040030b0300464500345c0e280480d80c040104040717401c68082d00c000d03045820 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 575861924 1250 575860674 575860693
    0x19030e070b03220629130e010f020310170d050304020f0103090b040b1008031e090409080d0f060605040b0a0f0e040c08010806070306081504020402040306090303020d060b0c 76
    0x30200246a12081110190036240643c0480390084401820202c0c0e03039698600c40c0303003000355110503082c8001c00510f406202040d107400000341b9000700304c80d0402100d40c5509130200d030310b402900407855801494100b5900e81c00c00c03a001c100001c5403401402581d00401c049007200f0700001901c0c100b5020300352681c1c0d146132116000c5c483e841c3c800c030a000341895107940c00d0100240c0084244c0d440345010340b840e490582442812046c0da078640380d00021f401d41c000c0c40114068a0361200130260b400044810544c0c5d240303504c01050140c109044054925840820200c840000c02d03000310300c680f00c0005082250a40fa48826103440c0503038000c00e024140e042c05691601405211003100c800c0380c40c00c01291547c2c40d80300040565446100f21000110404c004105500040060a800c01c485007418400641400c0e8900e94881440ba003005440c0082e00c00f02d803d40d115641264061600310078103011149031820040d0180d40107482c9582e20620b461000200c030800c00341a1807036501084090080e07240c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 575863174 1250 575861924 575861939
    0x806160f090b1303170d050c190c0507051816140d0c0921111c0f0f0204050a05060906040e0c271021030e0108040f0501050c19030e07 59
    0x40000f1451020348510744000f00c085030300404e81d1241d138a10b80040569654204441d0320584501608003001e00380180106540902180c1e00c0c6010241145004001c5401c5402c01c10315155007030b400b854026442c3c0000346904080d81407614401c03080501d8083e101e6501200807240003010680d0007411900910241c00007015642110141d01100c0c90b02c80394054413542035000c60030130040c040310308203a02c1c850001002120400da0165142c01c0301c0c541c400303030406d1006048110781e88000919510111030b1b80c00c00c0055980e042074095030050410800c504d000580d842c010401920503500c250282070000d6810300d4a40116540303086614060402411128140704a000840e003a0115854840c080d000020b2000c03000a842020824a00c0e0725442c074101d00c0c0d2400342c1c140342c841c4030b441409801610200e0340020b4141c41c148003e00c0d21a04980d2503080214401e410034200400035400e01d414400e24500f5035001e800c010004030702500c446c03016014141d0403a851000c0d00d2145030040c000810095 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 575864424 1250 575863174 575863177
    0x80105030c1e030105071e050412060507171306061202010c080a121b0e0d0c0b1b061f06181401051b060106120203060105071101090f0806160f090b 65
    0x400072034000c00b07600112140000e0070366400711107650004060050000151032003001481148406d030625600c0e0500b04a225010402c1007070780505410385031404250343d03034800c1003903003e0544400d0034481e05d81041082e80720702110722002541c00742c2c184800892062070980c044161268140c454901211300341d95120126040b000092090186024001c41d400e01c0602442c140291801c4400c03c60284600020340800c083c031846500400c40c82400ea400255800100c80507a9080707a0b40d251103410440ca10341e050401c0d8804105503005500500c403e40c07008480d160180944489090802511158200d94000c00001760b5160556800810030030724100c07071228002e4620625010b8078101e01d10485207081d2404400c0d8440300d41c0300ba00100411540100c104801c212400001e43c40d604210303000070400e0083d040040c2010003808020f282c0d40c1c0c02184564020260410450140d0741d407113420035120407048075101c0c058200b41c21900110781c0704420102d2803242c0368a800c1c0c1160308000e1105103030f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 575865674 1250 575864424 575864449
    0x603160306050612090f01270f02040908090a05030d02250b030c030108010b010e1810170a060e030301050a0b0705010908040905070215090601350105090706080105030c 74
    0x6160361840701258984034540105915403811041001a0600f1000107207040c2e00000752528a903d80350b03103035041d0200611000c10410520b00c0c01c02600003281840401018035800095005240c040800c04005034000503240f070810494075000032569540500d0b4440041456030f200582096204045040031600c0244800e1510b54180c41c48903240c03204418168425501e04205460210040040400c24021705080c0b80342031805007002d64180740410481c814000481c88a1900203000510803071441e40300d0001031001100d110203500000140340e0301d80f02410000d407510781c2403a818481c8103000108481c1226030281692551a140c03880344001900596011141c070b54075094440c005c00d43c80030180000d0720165100055500345040060f2070144280c0c46107405042e10410082c82502c0802c0e81411100c0e8490080c0c121040c40c0100c412440068601115130f042c031103144080c1090550101c1c3c4190350840c2210b4085807100020f68043e0024411107915900a02c40d00c0550305103559207140c0c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 575866924 1250 575865674 575865677
    0xa05060a02073c0b040b031801060e060114040e070e0d06060303020718140a0209041d030918040506071b0b1e0a0c0e04020a020a02190806070806060316 67
    0x60180e21586400d20030003510086140441d5000350958111101c499a88600c407980c0f21400f058515050341c810050142d80b154030000400031000400b019804500d80700c1a40359000208005511018002d04545044d87c1c07284c00146000c1880805c5522442200d06031540640c4011050b6580b507400c407402988a010140c0144044d80d01c5400920b442c015440594800c1d0054170b0400d060031050a4290038545422401038213041d040d520843c0140b045030b41183d40100c016944501e149c0202d40a804441c05258214a40742c8821207289008000740002520031940c80e40c010000900c610141c843c1034170060220341042c4081500310307000d80300514240c211452500c41950550300c80341400c070b60445044e1200100682c10b40400211107240540c440c01610040268501400f402043e0030b440140170360080703900140604109008024000d00c00d58004c020020449100c001c45076548402d21404010340b140d040410f500e80e004008a9200302005011203040d41d0f036101400807410510741041d0b0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 575868174 1250 575866924 575866933
    0x6020c04090204110c03040e070305040b0a0b0a12060b04060503030408060703050703060e07030506130c02210f0f0a090801020403121d04111314030d080411060a0c030216050a05060a02 81
    0x1a4a1380940083c0540c0302003103020310784851030140000701088008020030201490141008005880084d14a80001d240400020003200080c003003401030440d030b003000c01403403101c503002e108111030703a004031582000a0b40d0500c0341907583c800303266580c0114041c100042d088280010481403080d404503510400c00e15022500555031124411452004d0320581e0019807900100042418107510340ca0000c56401401c101011069100945030440394001d038198503120383c040e038020100c60046d00ca2401000c2409540da41d071002042009511044c0d0b410081010910001041d03101032003658112a08003000d00d10a1046500403583c195802d0b40d03234814200100082461500c0310320488208445280d6030b01c1d40c0b240080300619a441417540104600701d04440342410523140400c8608941c1d4403402c022046403070341e281046001008008840c1c211402081c8140e40641c00002101ca01d4029003d480d416200f0803402041da44950181c5c58000301ca490b803c01c103c2c2002d0f001041c49110900c140c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 575869424 1250 575868174 575868191
    0x7030f05040b0d060e072a0501090515040212030315040b0402270103110903030f07140604050a121707050d0209030a0b1510020c1c1a0405060a020406020c04090204 72
    0x1090140c010f45082030040b03035100e4003881410100810300750040700350f06081000380c03410310a4129181e00c281c80b183d00b038520000706e142002400d40080305c040e5405429102d00c020f0204040140d0101110305904c00c40101b070304454a400048100c038011440702100e4090580d03101c0900004e491f08017402030b0850307402c024401c1c0d1118041c0e403004010311480e0a400c10301d6000000142a12213603d014822040b08001215180d50000229408a090307408441e40b9901a410207032161030100c840c0e030106010ba2010842000408603015440030701c14101d1408841900000300e13650002d00d403c1d41e100c0f02c1040003040307080303021300f014102c140c00703585000d07240540c3c01c0007003810407a040c1800c0700d445441c00c0512078400c2c0807104064020030140c5400c0c1d00300c2c82e10703003000b5550420003244d10b00940e8500f4200d1810341d21b0601c1c3c1c1000b260441d50494941d03404003081c0d40b1850b401c6034203580714015200480c0603110380c1c0c0201ca04880e517139401000c9161480d0b0070040107007200300080380e00a070b803400700 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 575870674 1250 575869424 575869439
    0x1107120f0e090f0f0c0f030a050705040312080402090a06030f02090c1903020d180f0b04050313030803070f0905060d0e01060e040318050f1309020102121b0c09010b07030f0504 77
    0x30035100e0300d82288110f00c1c070308004802819011026002c10310240040c00322000505204065a5022000d4640496030761640c150584141c0308907000640366640e009074402c4100e820440b2140260300c01c1d00c240505640d07200c00c41c01141c0040c0401082120a003981c035001d490800240c507000b507403040101d440c041130408200e00000d185260341001c40d40104000c0e40110840c0715405080160354500c0305981d099a45040503050880f00003030841e01000042400e00c1010029514015200031912913038a0b100e040c280441c0d041119a2800070b4600860202e03001d00c51803a0380100da202900080c2003150948102c8041e22071030901c4102c1e9961a0380000e042603150fa543c901881c00b0307840b0107541305022000456100c0035500403500800300040000016100c501d0b403415000300388800011162183d01c0108d0030b09440005070b4041034004107101400510b51982403d000240508a966440700c81d0148042c112092148192083c0d00b0711280000c00d001c5e960101000101d480d1103842d1a444000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 575871924 1250 575870674 575870689
    0x80c0c120d021606020d200102070305180a0305030a052101030c0e09030301081b2701050406061b030305220b070f030509070b09180103050a05011107120f0e 69
    0x40c000001c0e40030309006103240d03405000600703034441a698400c0c212410082c010390f03039002c00720344401042000b8640000d809460a001704810131514025550f402c610304004042e600402c031503030440403000310111810316000c00070303404595012015500b03180d101c0c20151190340101c1901030341030b09031030300300c1d48c00340b84510405020f107102c0e4000c41c10300c1e030801c06071004500000306040c850360710800c0140000400080e1a012007001d0820a04203000f0060220f2044420315410030210b0301982030054140c511080900c0c141c0742c064038104090762b42c8100032921a81c40d0820704c0800304802010001191080e0407083d40101891081c450400034600d00c1c03001d020004405541c0880e406007031100c0240d001041e050300e03114501c0c0c2440706091010718280c594046100309084010300140c0794020362180ca0400814401818000c501ea48c3c1d00d0500c4c0d900e13a08800000c59181d460003a60302c070030110800940e103101d42c01c012521024030001c081070b00c10032009a000410b014050151108603980c444 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 575873174 1250 575871924 575871949
    0x70f1d01110105040605040614090a0206090109080d0f0210140103110a120f05060708010302030c090a150303020c0a05092e0306020f0a0f140a05160c0b04030b0121080c0c 75
    0x1700c0010145420b04041040324003072082201340290700c42c1840b25168000480d5000903804890f6075581e610900c0041c0ca4024080d41b0010060050b12496076021717421000c5540c1c040c00300d40a440c1c910f01600b002200312481040320707504022311900184041059040300c01740084000d04411440c0d03844d41d0a20400c604d0180c4110303007070300b000c90306070080000034007099411515a0402c1c540650556000035120704400b0210390041d0643c0c000100f5a0140d42c2180b501c2144041500c00c0c001d841b42002504c81d140c6960042c09149010000202414802c003103030b1081080e203d90504809191447d80400e1305050304400e8105165403021003c00c02620003030900c82e185004095950510840c0640043c03a041007940034000c2400144500007003042c103c0e0711000d0300349803440c0d07100c41e1521155026412040060704602c000781d000314500d11070800a2050b28021f881c1429580c0e07a42d030441c101c40584940c409440c0010990301000a000759010f04046408601501c4200306007a0100d41c0ea18040c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 575874424 1250 575873174 575873183
    0x1b0105011e150f0305040204090605010612051030081201091404080d0c0c050709020301030b0903040506070609050c130b0f0301110711060d02070c050108070f1d0111010504 76
    0x4010101495051805080003444441d90a1400342d00240014125501c400b40d200185602d8400017400c56a0310b0303200e49102039100208014558550900400c1c6d03c149021488501d0301c0c1101080034070a070070501404840306000e40c1c0c602d081400c085104503100b400058030030040140446000120781d90041c006000204181440d55890078200805842c00a08001084544e040c01e00002c03984940c2110840e000c1c1c8a004903225000c10340c101c881c40b008440251003401520404110780030160000d40c102c90160111a010303460b840d400c00c0e140e129034850346a00600030490390340064a80d404c60f00c80c0314000d00556585105610104074440d06242a4a100560350035220000303251035a403000d0780c6031058008008500d644008070085110740c0c00054440166a40c1c05901c5aa03210122501700a07000800d5445800c9441e08580354200c82c02032901091301e000c00184012312417041040d013490541d40d03920102031090070710350b0422402c0548070704001e0b01c0707545032611070001d01540b03010b07a106 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 575875674 1250 575874424 575874449
    0x52d120f0118200307090209120303090d020c0a060923090405160815010504090c03051f05010e160f020708150f070519050a02010b090a14160f051b010501 68
    0x1107140c0804070810f1004481ea01000e80d0280455586000400308280d40c2144401a82c50741348000040310201c00d41c030928241e1000204108408902041c64000007013a078080b210380407070000800c40c0074543d5006120008080d04010410621064403c1c8080c201d03c1400e40c4041154001103032080d0403c49007034031a5484101281d2000103845000030082424002070540700c01140c140c130992203c184a0a4030441e100c00e0302c0e5040c03040c090400001150b2003c220750580c040042c02c0101034009800070445549004000a4042c0e980e0356003030701c0348070022568600c11000b04d506947c1309804807031540441c8215a0b022851100400c01f404400c0311107043c148442c074010414081940d001040740d001c0000c1400400744942c009950024810b5041c10140c1c4c98903444c440403401807410300302c030a501906500500aa1074041d034000740c4401d0f4225200341041c3d445a001203103c00c01d0044190005151814840e1118803a20140c6200d0300907445402401d441b1245403802d42c1c1c801e8101880d503541 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 575876924 1250 575875674 575875721
    0xa1d0a0213140111011a06070804080a0b0103060501150f110a0b0106030e1209030a120e06120604050a0c020712020d0501091407080f0613030507120801052d120f01 72
    0x3080800e0a944c0d01c8908006c2c04002d0002c146001c3d0b14010000440c010500891540100850714045d50b015200c1d44049685e4010f440c1045080790100303204c03d549813840c1c00e0020980b0b920052940c01e510500361102030749080d40d400300315401c00380a840c0c10114001e9040c10f500140814800700d000300a20341e4045100401958100e00740f0300c8640241900351810090040186c8011448200f0903801004680780c024080c0019100b0650300100c5983c081c200090701c5c00e0007446054098020301059804200541c2c40c02d200100300c8ea0780302d00041c05603002400800c540d0301d0008441072801c0c40030303224034078480362951583d0a549160f1000c030781d586d00c6201c020512000401040c401860311800130300008038042d1b61307540c50b02c80c00340603040071010381d200c0b00c424180910100d61049921041040041142c1c40e0020500d100070f0140340c2c480c00000d42c00c00c8000d1540400c40c40e03c50300404080c0e205490310070800c607002004aaa03140a800360586034584201c0a101d40c031003d03855090036950307000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 575878174 1250 575876924 575876927
    0x903030c02010c0305040c0909031106040c0e090c0a0b0307030905100207050c0d0b0c18030d09050907211a09180c0d120810090e1b0a1d0a02131401 65
    0x951643d9207204041c035020804c004114034600803802c0310149a03000441541da070404179500210740000518038030a00083c03004100009134403000301c50f08a4a096102d4890f41200350f103d0303018200c401d0388040311610921407420000001c0d9002409400d0024000030721741d80b61810314074603e4010507000d80c080f4802091100910001c06181742c01c48800c400300d50982c1e120003c40c80b0203401e05196100108841e106859082c520042d44d5000404450182c03c45002c01841c0c55801d0041c103008500b10f60220704091700403504d410185e42054006c402082c00b2401c1100240752501c5414546170340b4800c00c8516440d84c0381c0f0342c0d00900303440002c0c9a40340355051b401898200900301d02402181600c800e10089884031180b4420640305140440071074941c5003103201d1072103890f08904401403a007240380111134800140d40000c045d4030070004013210301c010308000079a06d851050028010070441c1400b00b1203090110160b00101c1d07440f00500f84038400d0905052406036070406502106200ba4100039076 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 575879424 1250 575878174 575878181
    0x120b0603010501080109020105030a020a1404032103022d04090e0607030e03030c0405040911030f0705120304050f0112020c0a08091f0f0f020a0803091e011b050d0f0903030c0201 78
    0x1004004c0080c0616041940000d210340300c01810300700c04650204001c1001c0d4800c0c42c070380008001c960700264849840303043c546006c9022901c20744004000d6629000524000d000361290483c082a00584da00d4401c10181245041500c01e500c0e01c0404000200f07001059101340030a10302c1a4008010911345104045c00701c032503160b40000a940280104410584140115000c1d02c0d03081c0c401007034010b114500100b10301d42c400380581d403500695518501e440c40001e100c00859404131024003001410790046038403440b5a006580c1c02c18807154040d9030a500442c0a1401c02c0a050b00c018500b6400114440c140070344054100c908490004e802d2060b071902284e08a0728880007801104010710144024055011b0820300c04180410300325464100340c024004410000d40000c1d030103a0702c0c5004401140c43c0c009002c80e941c0c56241c4e03280c90594842051042c0e0034031541030542600c0c02c030058202070342d142e0020b5045180d500d4a950815007410814040e48010038842e84022030007440e418400390a4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 575880674 1250 575879424 575879429
    0x418020f06070611070f120c0b0c0d20090a1d0115020703061107061a1818010203012d060e0616050a03170c1314010e090c0406091a0d15120b0603010501 67
    0x70408c0509108011a0594119136000114100120b44c1d818440e0420005000300180d910354040c010002803410480c00001014025421180850f5107030b22104150111202c02240c103402e00c0085005008806610030804200c0c0c0e201e00481d0452544c80c1d42d50803e541c030b0000c01540070940410b848042103420b01510218241c0c04510b005105604400304092107280d0512001234400d12021510400031300e2504040d0180d400004d5580c0e40e100d0000820191900321101c803902003841c615000144505862000e845855840c484180304036000c02005800441c0017101d00200b810a41300045c0c1c081003000000e51290f1a50f411103440c0d00ca90380700c2018003d0070a0f400d1070041001a4041c400c5038135580035526008249111202c5250048480b10781801d241c0d504241000140105014180b001d0021595a9030341c5c0c7d02d1490721b4201c020f00d10160000220b010881c00d0100c0507105200d9000381c20480c40807030f024140944c0d249064500402da00c00d05541c01141e00c0700b880203504081c020b00f4003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 575881924 1250 575880674 575880677
    0x30e040b0609010c03030b06070c080f010203090307240507030e0714030a030503040807020a0806010e090d0906050702040e0d030605130e2a03010603110418020f06070611070f12 78
    0x6a6110080030a80502c690945141080b150206030b004050013036001102c00d01000e8141500c1d02c2561030911400149402044424403904880a1450707505000b101c0c4603106c80c0000d1814075859648103110b0311010184441a801c0c4841c0e8840c0940300d511407144550460703076000c2600000152414103118075a000f951603d0101d9400000e40d0f1070000d501011554140f41c2140d5a82e51410210018054100003d501103d4000c0c0001d41c01000141e20f41a2046000d00003e00d0301e855504a540383e10704d20400000c11006042000301d80e0244001c0e000c45070001c0c00c0440c2104e040c41340b550907c01d13143e02c1c80b03004c41c3c0d40c0d200a01c51401e081c0102c80d030001c41c0c044104900802014001c1d62a0103c0d02405080b15550191801000740d1410040560402a009000003501c3e46050b002140c1c150080d02c0c0107518000c070248265400303100d044500ca4018024a00c40e095800c14088641c1c001601610101d4407603401004208120000b042c001f40181c41082c14a1420710b45148800d512103203540 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 575883174 1250 575881924 575881931
    0xb0103140402030d12020d141609052b050708011a04020414060a0504080f060a0506030109030801050f0109050909060702060c0301080706031508011d06010504061809061407020a030e04 81
    0x20060f00c001841d121180c559040103401c191031444100c004e40710f032000d43c451060404c088402c10300001c1d0881c500486c03d09a000c0c1c01085111002c03280c0000382e20616070300c02c10222001c1c09a000d10030004440410b000a2030440030859107405242941c580d209411603991140c03500c81035540c104100307040d480b0440301585058504030f4a5403003003480342c0c011446814001102a80341d4000c204640040c00c040741070b68855490303020314984400d0102c417584440ca0030100056075600c1c06204500c141541500c44e46503690900d824010400182c0800c40c0c1403081490010409070b40c3d0701001032003420120000d2030300d07251540c0e0003070620a007d0402c0c416480c080c401070020000204254050fa51145000038521314041c000d1043d01003190705c6040715500e41000081c0d40324080c3c6880b440702d07038040c0072188a642c0c0c03a4107020494000d80700d4000b00074030846000d5015266500030348461809400003140303030011110ba50126040a80d254000f603403010103c40d0406801108205030b6503002c42c0d081 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 575884424 1250 575883174 575883181
    0x6090604030209060f130213050f030d030506010504090e0309030f07210204092f120a0602031302100f020d0216060810241404031e03170403030b010314 67
    0x8519004a0100a204081020004145032903203038505180c541c0040c440c94044138a80e0f2980000d41c8510340d01e0081c104401c40100317290a008416030442500038000700803200c001281140245000303460581040020880001c1350f60b120f00030030103a868140051035451500c60209841d08602000b0404241c1000b00c080082503845a50b071000c025000719844121400c034800907008100030359000304107102955541c01c0803030141e24003055280c1220701d5100b410450030b0402c140485000000111030380580d80920000391181c0240da040702c01c0102203035014070075600040b0000800007101b800105095003581341c0d640c0c100a44114049180042d01442c0c034107004080c420380c014000d0f0070900205da4017282a120745d1035011001040c049a00c800010406203182102c06012400c0030006000c684080054102c03000407601141c1c0e01c0010700b000243c07816110894001c141c0c0096003482180107035124a0b60220014074413841c825a400a0002803c0001500311890904a100d8007040c00040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 575885674 1250 575884424 575884429
    0x2090f09160c0f02030303010e0906072d090506180a0b0313021e10020304050a0f260f01140a050903120708100b0403080301140108040c0b0702060405090f150609 71
    0x58040c15006140100240b8118185005041c41200700250144400000000c00d0111081824041c4510609807501c60b2241e00b41240c801403910f518215202101c0d6101890100261240341803014908240402c250780700005a0780b034205c420441020108224600c0d00780c43d100d0b0307925011702100f40788a82581440d4684071000c40e4801c4000303004620003243c804480c804203201d0700c0661001414202d41080c0e141c0025229081882154002c011411000c50744908141040c801d9864000030b0071a441103000240da400d80c0e040140c00101d0140350060000242d0078041c3c80c02007681c071a808421403d1400004003141d90003041c00109400c14402c41076032001c480070742c0e9000001460700ca1080d0b210301c1743c40d68905103207500c07600101c3c00016001003002003d030090340c1211202e44081e5500c008001c010b4451b008212001800c1c5400c041042c4120b010381d1000e80141c90010708110708043d01d400126111040641e4100ba201b10550208502450310051440c07041c90103039005820301703a51002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 575886924 1250 575885674 575885701
    0x10e030a0f020a0c1505091207030302010e0d1b14060727060c0b060609060c06040c080a03080406020d14091608071224020316030c020601030c03031d1302090f09 71
    0x100a24005c95000010480c0d00c603c043c1c584500703008011076074201000c151913079140194030048016500746625200059070100e11020418401d840c0d8a041009118241c2e016880f6024211600e60044c44104507915040058522480080d280c098400d200c051204001c2d264400140d070030700c10700c5407080c001d46601401ca43c4540342d1041e1b040b01d26495010003d4454000c8912840c0c203d00045600f02100300300068050050b40a00101c2148644132107007551102c4a12101501045203000443c00045941e8010074458803000d00c00200e040f194400743c05070920030b175024559944101c00f07010072200e6801c42d00340101000d10007801020300c0c1c202d02c3d080d81540030301c0142440d141c4550b81721400c1114040301540b51002501190350303142c8580341490205440600c00002450142544c0e40180001070f51410317641c1004c0c0c0341035038034510b54041f203c0402c4501c1c1820501c4c0801c142e6600c50311201513080c0c0c07014482c01c0141e164118902400301e04c001250040d4800c0c107000b42405006140f520 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 575888174 1250 575886924 575886929
    0xa0c0318210f0b0c2a0705060d06091e0c02010c0210021e070614010e0c0304080c0f060a021e04050a05040e0304120803010e01063905010e030a0f020a0c 67
    0x9080c090440701c2400c00079072190800300d029001062010421400042450003070603104c0b4070a4103428221109407003511702c41e09414201519600c10304040c071071850301001500d840044d1010106a2517100d00644003920600541d010a05c400c1c048802d00c4184140100401c1c3c110600c020004404c090400075600e281c20303036100e0710840e400101d07c88604030b50084104940000c0d41500e40c1c2d5103440c50480c1c01052070711004507181a1080002c039403a00482506070044d07410140f40341c1941c4a644030030310942d2100c1e4500ca458802d48000c2d036200001800114800c07542e02c00016160980c140300120109260b50140b8080901004180003560350400f005050300c00036a00024008601800e26245208940290b5007106001c10820108410340c80214161241e07000d146003140d07601e40082d10303242c101c0c00c003411002200800340c0900403103481c002c401a01020305054684201501c4042c01c41e00c60380d2202543d504006441072610341c03c507506061107149403005040941064030380700513850990 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 575889424 1250 575888174 575888219
    0x7020f0f0306060f15180109050117040b0604060e070201050a0f230c0906040f1a0403030c1104111c0507022a030109080c0a02010324050603090f030a0c0318 69
    0x42164403c0d07215240d40a0b02d54030103039503050343e89104000811070700d0903101c1b80600040c2d03a0400072031607510621428030b116000d0490704007152143c2d075680940800041c44550000e83c1c501000401100c18550180070f1001d90700005001d04241c5000000d40300400001c0703103c2414105c0c44403030f0500c0c444102c80303840d00e00381c100c82070340d116030307508080c94810008000d600c410046400b00720368504480c00c03421a0300840c0c90f0340300305011408181b07150103184006004200000181e070049403182046a180e040000c200241c0503203110380300300858102581b160504410b9004801201c02d8910503150000030394002842080b6086810303201310b42200901a105d8800c43c1c1600f091600e09401581126a0100380700e900e4001c0707881070a039076020b07482c000d81c000f03814007400e418400600d000c207520504002c3e820100d43c40c28401400020390001e0005201d038800c0c151890710b820402e01c0904144002540c40c02c440a00c02d0a004080e5030b0340c0180e550010794401c0c6c0800c080c55014096280d002d40c0c8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 575890674 1250 575889424 575889439
    0x30c0309060913060e10140904080a0311042705010312050d06050a0611010b011416030521060a0e10030f03020a0b070201020316020a08070f150f0207020f0f030606 72
    0x3110042141100b5030201c0c41d5800b03080044c017042c110155003255106000d5184100d805d141d98800400b14030240c600825000a640300226020030500d400518035220f02d4200418030409500d0703810440d42c0181d101c40402140390b404e5101d45660101001c0c0401c810f981d05000c55415070b107580d142e1034003100c110401e0120004c0d42c0c0c2c040352119084080107050060142d00e1055480d0310207800d5680c0c0c540e41e6017407540380480c03005496008004884e1283d070fa040800703050440100e1550100b04604d0415418860244545034030b111041403614500200300200100c1c9040401c144054920030703070042504a9600700401040c4581c00a01d0350444e90050600b40740f102c0031382000e034141003c684e4050050940c2c44200b00d0070300d070150021800341d0711403120140484490002281c0343d081a0200900c00725040000750b021400406a4541b1140140080300310010b088110750100d441d0748054407692034001ca840304c194941007003406049042500c1000c0168902c20000ba1101c10083c0810b20480b030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 575891924 1250 575890674 575890687
    0x10509040f061a010e10080403050c16030f1e0317100b03100e010b0405030a151503030801030c0603050610121d01061505070b011a090d080d0e030c030906 68
    0xc20701c0d50031000030303082502041003c0c19100c00e0140380c9101c19240340892100000341c4800d040207503031101007400540d80c00c2196150340d6001c85180e4002400d0010a10815a084200c0c02d0340181c3c0c04000c500c11081c1044c001c1e11407900351a143c1904945903200c000c00700a000201e500821303c2c52080c8100d5008003400c4c0d540f041d12240c140c0700d5400a003007400d4040100200203114440301c0c001d44815182c1d50160307a982c0c0c0540c842910446c0100790b0150402224100010a03481d085521402148804100264401007188041200398415000901035000400070b114800c144c0c01c024059619040c440743c50020041074440e40740c071004000308002c441c0c1c1396407142d1841d444000c4c0d08121a041240825480e401c040c0a402c60380901c0390400f0000e8801da400c6400340c030860301202d9000071400140d038a80600c911024500c0451078550319410031410b5119a503809654003824440d0703c0c202d454810061900d8104e0319171001d00e910980c41040f910074400400004d54841d0b4108179501c507641c50 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 575893174 1250 575891924 575891933
    0x307020d0c150c05030406061a0703030e07152006061c031815090509071b031107030c080c030723040f020c012a0806010e0303120f010503070f0b0301050904 69
    0x4415610000091408443d1410190b011000b180658001c14041c030086d0740780c62498448550301074401ca480c101c00c10120300082d010b41c104201045190050b203c80303503030315144944001909400b080c0020f5034949418584808040281282c00040c40140301c02d00d41000131400799107600d1162640e004003640070404251250081e9100c2e5641ca107401b01c0141d03554440541e00040400c05040810049000460241403440002e031048000d07a581035601076084034800c002a207090826410020035681000100c3c0c010804080158410452041c0d00c0c1d10303080401d070424140c6001148240c00404d8200f0460725040b1604801031070700c10155071078000080008004180c02100c007018140082070074a0710050641c00404807402c40c001e20510601191040b545112030281e0180200e4004c50100b010707540301e20003000403880c0c00340840b8034104c180d510341004880100c03000c40c90210110014441810140641c1c801405200c05810b40d5500301180c500d594041401003a0080600000150901c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 575894424 1250 575893174 575893193
    0x60309112209081e03040f021c060507050a090602150412050915071b150c1406280e061303170c030103020103050f0112020d050106050a08031b030307020d0c 69
    0xc01c010368100003680d4035180070040c0380c00c054084596000b4094039010803007102e404880c4039030742c807444042c05d030308041d03082094100440c007120400e50841107041c0c0000f1440d12030309003e03034210345a41703854084c92035009041100c0342c2c10031130464102e140d05440300ba41014050750020360004031541511070142e011903403402003900c09075102c0d0003d41d06840c1080960300400c0840d0189038107100e00720308900380c003800c11514861240300060004140380f00c0c030301c0348141100700ea109440c07200581e42c0c40000d40c2e00d003040c190b4004040001170340940c4414440802401d0442c036070b04409101506224000701e0315500e000b003151424402106030a000c240c4a6800c0100170282109842d00a0400d202c3c0d608103904240400c0740400c1c0391001052036181111002070480758501622050001d41e9800d02006c1d4000941c221203030b40d2503140206650f03590695403405001048011625041e040a149840f407078030145042c159081042440800e6601013041d94516045041c0041c00d0b1665260940f0344 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 575895674 1250 575894424 575894479
    0xf030c0303120a060f0b04030b0709051f080f0c040302010e36070203130612091202011e09030207031202030d02030f06010f170112020f0301050106170106030911 71
    0x5000000b62030142c078074404420390194020701c0c0c08002d15600c0360303280ca40d40b00890113841416081131004200042e42d41a500b90311151524003d8411680c5901150180301c081c01200c05080b02d54010000c41030303002000c2035002e0a0502401c0c514109034140c8185841107000c042e04102480c00c411a06880d07040f440a00520741860004e010b40c0600341c05281107043c01622010030728400086208148004195802c00090b040000f240070300d0020f0640f20f0040c20034011080b40e84a404a2010807e0041070b02441061a000814a001d8a01ca180c10203c2000d421100c00351801c02d139407010960004030030701030300d900100b03440c2c0c403446001e0300740d1543c00703880000b65250b800081006280c24030405450b001e07010a80365082d200106240684041c80d416504803d900030f007034010000064000b00711507045001400c01120604000c01180c02d49101340c0004020ad0802e400035103c80c0303101000745004201034902000181c00542d2542140c09080d8070749445440c404070002881c03000c92803035104 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 575896924 1250 575895674 575895679
    0x10b1002010e060718260f0601060f080906040b04050a061b0e09071d210105010f05090405030d050c0c012d0b1c06150311030105010609140f030c 64
    0x6401884a8000e028188000b258640c40c0250700100c0c40c090700034030a041d20705040b030180c01103803410310009101300c03801044155010030209640c070844135818841001450604c0029020340d6040c800041c0c080e201d000d56400c2041681c03820050f4462001c01e42135003041e80401081c0307254845042035442c00c0d0704880c0107802103203400c2c0303800300d4001c50702e441407004480394031500d043c900600c0c01c00c107903c00120b6000b808140702c1071401d561144074104003649034400600740240b0030f80042c0341c0089143d0039511000c0f1695110014880103200c2d204940c001c10003210401030301d00d07141e80d0b00c2d41c50b070040212140301e00740c0390300103c2c10030340820042c0c0742035601c91402081202e1008040391200e0030707400d40120a03003000307900c001d591054901500002d084040c0c112003044100f00301c01139088034643d006907034040d952910002c10a0000d810344c0002d5024115550000791500708050842d035040e8042d401748218540100408060b4901a884c500300440d032450103800c148010a08105c1c00c070b00c0403039 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 575898174 1250 575896924 575896939
    0xf100e0102040e0a021c0c0e040b1f0305061e01050a1d12031905042d090204060903050d020105061c050a06020a0f030b03150402060a110105010b09040b0d0309090e010b 74
    0x41c071500154080c00010150503110303102c0d20421001c0404407145001c1540001c2c0c14001c0500231802c00380c00140404e5001346c0040b031a0740c01c480b60200c220004009940010b80c444041c0511454aa00301d1055105601a600841c1100f030703001a02501c01d04070301c141842481d004911340717070488015611b003815000d400000881c08902d1400c1e03c84d880140000400c20031f0040c40c0401500c0b074000d5500780c500c410305026000b120780080c04c224461604c13591207035030030a00c40820614100d00140c00208000d031200a0301505601d045410030310210b10001c00c45e890310301007008503a00e0b0044881b0b520042c02042c1d5080a007420320f1821700701003210242c216800010301c2c492041c3c0c082c81804404030305030740402919030702c1d808144e21580384a9191200b20100c101080161038494003c100032452400c5c1800c1108550380800d00b9180240d04c1003c4552001c12139100c0c038103080c0960740f0b800d01c0848181e28a0610303035501401c04804c0d0b01510702d01ea03540740d414140340602580700e00322046c401402d02 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 575899280 1106 575898174 575898181
    0x32301210204020904090c0317070b0c18030a0c0609123903050c01031a100e03010906050a15050303040b0307050d1d0a050f0f100e0102040e 62
    0x203a82c050341c01c01101c10f2598580c458074440d0340c42010603144051460418011042c0c00d1168008034050070420b6500246204e80c03c240c0c0101b5004500ba1104074144a0414a48803446440e81521500700841c040c08030780302406080341c01a60354164110348441c404202c01e031030900c0040452500034031400403003500548180b400102d202c0305501440300e80102c040d02c0c04543d23000380c8164114078805e00351560b04d4000c1040f8208910009540485d003030001c61041004802c80c5020803201040114003907900390004030700d550300803e080c8170a0a00c030087c980113014046614041903440d481c00251801c012060751f04542c0ca101005003540c1e50302200b500e03a07a200d007203260551540d42c0207034580c583c0f044142c0380b00c49070a6801010250703034a00d44140380800307928100045034491940b0100160300025800c031030941106021074030b2071101e0711580c00ba0143d9088a01e40b241c115041 = true := by decide +kernel

theorem cover : BRFrame.Cov 575719424 575899280 := by
  have h0 := BRFrame.cov_init 575719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 575719424 ≤ n) (h2 : n < 575899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
