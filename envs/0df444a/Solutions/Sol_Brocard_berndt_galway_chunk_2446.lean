-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2446
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:44:26.520987+00:00
-- url     : https://prove2.me/submissions/599b48a5-cef9-4513-a148-98165e87afd3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 439748201 ≤ n < 439928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 439749451 1250 439748201 439748209
    0x603151b120403260105010525030903030f020a0213051803070606050f010f0c03030c2f070b04033909090209091f090611070305040f05040908030a05070309050f0a02 73
    0x280341c880409807020340415030000c41300002c2d00e41140c0080c01d186a0360b9010040b80f00026100d500340c544110f00c00507000b0109648402e04901710790081e40d90b0f00101e042144101d842d940c50701000b071343c4881314074416142c1c080c80313502250704030318852115603401c4070070400c2c02d082d504a00c206881741541ea5004000c40c0c11b08042001180d1000d00e081c00c034114180c10003524404403100e014017015500c0d074442c00d61902030780030302c0080344d200042001da841d030340f00d40f00c05014040004a140d03400f40b04800500aa4010240c6055a41c009801c180403c0d54005000c80006514002d80aa0181240d140c0919054000c7c0d14058581c1110116180c040e0b0b00512004690141252601d5480b0003180c00c40141600d01c0030300103100c1c021010921200318240300000d170403000d03560392608a0000f4030108040d00140100202c2d42920f00946229035100b081108a41c1c40d00710291244500b000055201507080d803029174004841d060015652050f6107030280341c00d406100c1c120882e8003101c0c1060541ca0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 439750701 1250 439749451 439749467
    0x306050714180103090b131502160308190f0603060c020a030e040e0f030301060206010503120f07150216053a0e03030408100605011103030603151b120403 68
    0x38060900d00203409841c00c400c0769920070081418460031642c0107101e0b55a1090304051400b582010104006040801c2e140ca0a015030707850413261f40f011000c11200108290080e50703115081d80d0030080600c090342e1001d85948000030030000c80055020318200b41c0c0c0c9424800d581481d11001800980c140c250702c1c000302160050b4503044c05650055040d080000e51092040340320303e000b80c03404101d22148004492401c10b10001c1c814003400003200104506030300082d11130490b4001c904075241d1401e000000c4980e4802c42d011510032103c10800c4002188850b549012202c0b6182001440c1071140004a45820b4000608480a40103118030a007a282c0c4400701025a090b5a810b070341d508041d40c89000d82c20744400b03c082c0d05000c0341c00c0c1c0d021070694007841520024010001583d03510740c1da54000b80f00600702802001e01180844000001071807000050b00c0c85001c010303000301818200480b2043d140440104010b0020003802203007100850041c020706106500e500703803c521703418107284c0509020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 439751951 1250 439750701 439750711
    0x4170403200d0c0515071403071b030327031b03030e0a0503062202030d020d020601090905030a030525020106140402070804030311011503030f020d0509030a151410030605 75
    0x81c1c441c5505401083e100380070345040758400c40d59101d040301c40340081c41c400d0003050301c0500081816008018040804030050030030a10448001d81d119814008190910425000140001d0090001150164403004005015890305449001c10550326501e45400c0000000707008042c800d468420420550408907180403000c04449064001d07003050701190740c41c40d00501c01d10b4410404c0c14020b03004d0720b80101c2c24103111340107003c3e030300c0510141c4c201954410203450f455006105040002882c0740a0384242d540c15a4444091443c11203800d2084014010150450a9041401207481918100a900c1402a0b0410740000c80c1403032a2260805120081603901c500070742c010021000022842c808540c162236060030700c0d03030400300740f4807840e8014510030328614605003101034040705058100040c0c42d1a0030580d42103a4401204800442c2d05003d910801038069110b02c2c00c00b40003806203010318a400c058420006194040f090b55a01e0358141914600b400c4c50361303030505006100342030058603800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 439753201 1250 439751951 439751959
    0x807093503090d02040203040828021002160b060a0b03180714240408010504080d0b0414070507021201050f0105010f02010b0609270910060905010b120417040320 71
    0x2c1039804035814040c0e90342c0c000e1155500000103401c02c030001c029507078594248000c96421a040e40700241519204452507000b41c441c4400003401c070400c90003111040c242c15030311500040d82582da5007a100ca0040e000e00d40c00b00500b0004541e049210020350b06c00c03100c880301c0303411402c84808240d0510881e90401c217440c044800241300c030350321800c02c4a68907400d030154613580c00c06090191030190089402195041d420001804140502200600b00242e40c001c000c10a402450f410402218146a100030704503c030200040c2c011030045018000d201c1c0040e003034800c184000b0803540c1c00c440c4100ca00702d01d40700710a030040c00503590200c0100e01d2691580000c100c100c801000041d1a4010980381510440c0481c0242c440310005403103004c400042c1d50080340031810000001600c60780100024034100c0c0c0b5040001070040054082c05040742c81340c0304581d10f000042462505c0e115801001600c1060003041180303c0011080d00a02c029401190b800d45040b5603148d40151900107050b409202d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 439754451 1250 439753201 439753207
    0x150b030112080309030714011a0105090a090b010309020306040624080712020402090301020705010c030b0a0e1b09150706060b040e150a0504150306060608010806070807093503 77
    0x20780d110259006003803a042010140c80b683c0740c00503585107110b5a04014070a00554242c8260300505403c0b0391840c0d02c62000c0070801074600c8004544034000c022203141d1000d078441c0c0402c01240340b40e200311a1282d044c5000318000b032a0740c010a24018041d1000c50300d10b691200d902c4803840e403407551041c01900c035581d004203017450280f10302d603508031a000b07446460441a40e501c0455a41d50304580d09180c019000f0b40d180d03801c6041c00d50007011000d0003803005c00c2c10202c2501140c64280d01c15015250306a00310b83c626101c40030301c6030964003081c030030b04001c6000308060206a525442507907020020310300440e5840c20285090070584081c3c1d03000c400421014003082c0031281002e0301099010941031001d80800c42160001409072004ae44260340048c90010a09895282a528603082d28099034061020b04e5540c07800712003c0d1024800c0f95400e070030480128070001d201d180d00d2500540b540c42d0442481e500c407068401c00d4600140c2c01042c000680031440c00403820b80d04008605001da030007442c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 439755701 1250 439754451 439754459
    0x2c0403080a0c09170c0112020408070902030c0702030106081f050f0f06040f0e03210f0123210607020105091009060227030f0a021f0e13150b0301 64
    0x110428014200782a52915500c00c507400e548515004001030182c1e83d1026218003c0e4441c650b260344524282c1400211180341c1c5034101c140c540200c8007294146802400414603040403940207400c040d10344460304c036007000030802580e001d00900026141c240080d1105481942024070000541c0402c1100e0700e04010030030060030106016168002003605c2100e5441c0d50f03d00004005000200b101442140740a602c503013413a000002404a040b0024400c0402031b004214002c400342d4101c4410001e80302140040c0111030341c00f0700410340b0300c104075490741e92500c02800240c411545200c0c0f81d07000c0344205148000c41c2c10100480780d0880ca4500080045003000c0c50942c0d26212400b81141026440d08100001c20800da41180e251b056142d508000003080412255018040d0040c0d05101c0d109040261034210004596070719180c0d030080c16030407200300002c0c903807480c81c1e600c041c2e40080c0301004010381c010341c8980c01c0d0310740d180010190018540c00400d11083c5d14400c6904401040f00040c80184 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 439756951 1250 439755701 439755707
    0x20f12180a08091201091101121e090c03060c2a030c030e060d11041d250c060c0e040c050702030a060902040b031002132c060a0f2c0403 60
    0x10501c5604004402d07a12001e02c00810301390381c01d19014000641ca000c140c581480b170b03081091100b59100343e941d040d0350040045080103817028140b440414008000c03c4111481d03195000e1107150744143d400101c0ea035904c0e115441103400310385010011038041c484c56059000c1125240c60040d040c0e0b6450803a8a5007600d0080480103400002403e11110751102c0c400e86d07842500340c80039944030701d9040c407011000b04180c40e1242c11031b210b84e83c164501910f44072000e5216540e000d215a005d19240041c00700d0152182580020805040081c003503d4001304010481c24001c1140922a9881d13180190700200c0901003100c07286400c40341080300910244005a03404644c2c104015003040c404140400c07039000040062002001d4181d06119000c0008016102d58010b04003101500ca08030700c1c6580d961030940312401c400c0885c03101604d5107030411f0b085000c041c542513030002e501401d400845902d8030481000500c4541081c1014414a201c102000442c25243d4454401588803036005091554001d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 439758201 1250 439756951 439756963
    0x90a050a0b091e040905010b03100605011b031709010504030f0e0618030c06030f0703060807060905011206050405090a06060b0711060307110307080309060f061e010e0301020f1218 79
    0x14403e141d543da04043c00d0040354011405a04014000c01c4607000ca4600680204004507490380a0301844012028202c1c1c5481044200e45068444045a10607401014461603031460210248100c0070103050a0149a400c0180b1a00103074000190340d00b407a08015208010080c031450400212505112941d216101030b030380001d101d440701d04d0f00b2306000e20002c0d092130011145aa006940401007114001c00d00e22640c1c000e0503a41c40403c03a55403140d05194948103940540804030718885c0c010003065101d00c007165601c03540e9000c00a0059140c4000400340c034001d0b00e007240785a00c0540a0340c14809a44654001042d210342c0b060320309901c0e0380c5d441044d202d1401016105180c08000220307a1409441500c03160b1200340281d95a5080740d1400a8090300159030103d194402c450008194000c1d2158a9024010007000b8107505d401035480100d4051801500504008148905440c140c03001d0024007510078419241c5921001c0d50300c81b034031784040c0042000c00b403441c0711054040103503408504 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 439759451 1250 439758201 439758217
    0xc120f18060203180d0b07170f0f0609180a030503010501030e01270302160b180d0203150a1d0d0e15070305090d0209100806010b0c150405190305090a050a0b 69
    0x28108134420f07544001141003940c0440941407481c010100810264414012501e4060007070b80381500e6260031995600303600003181c05040e0704ca4000c001c60b14030f1a1032101541d0244540040d010ba682c254043c0504003050628100c01045020005020070368040c00750204001c46031000304500c000c404000e10f10807110415501051032a0b000050503d4801d009406490141000040b034541c1d5900b41c54410b5402120b070a5603030a52000e041d032145c58800d102040244d0010010300000103851151400100060322007005107039200b2002e020030f000c00c1500d00c810f1140102034110500c849901a180303050390f02c010352142a0849030850a201403406661806800d407815507180d10550000c6107040c00d01d1800030354030001e10f504105c2081c119003000e8094403689000c1d18420790340c400c10300c41d0902400741d00011325000b4402e21020507502d0020b01d6402400b0710210380c0002140c02e620b12201d885001c00f0340002d1400a90520340b400d180c14520000e203000d0752540b9015242415440490080e868 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 439760701 1250 439759451 439759477
    0xc0d0215031f061805090103121d030a05010f0b040908040b0f1606150f120b09030403060e2b05041e15230702060f0a0c120f18060203 59
    0x808039942405140c0c0710a11100c0000050b14480d0f11080c0c043c000341040f2004082d01002040049502d080c404d40403812290301000411104084a00c1501d001e0f0a6101d07400000141a2441c08195010402414014003580c000038051200e00110700580740001c1d4024015814011302400040561f01200c085941100255849a9201c5900e500603c01c80ea00c1003a807402c24203800003070088650245d0030011000005190160380d030b41034000304845501c10107d203082c10591180200f40c0c00118264071051450a40b41b90a403280d03582002c541a10b04442c1483c4d01000e19001d11107103184061803042001d0400740c85080c0d2031000101070380b056008400005800c04001c8140100700500c09010341010360b0303c0c20542d03440c004002c08001000300709075451500c1d0301e504420a00c005046807106500031300f646d4030b0080b50015500d07140d4422291842002000440c40000c51980381c004019030300d0170b07650a0043c0c125804028a01c02e0703000b0389081c00d0000e0b0074040208a8001003160402080c0134 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 439761951 1250 439760701 439760707
    0x7080702070302040504140105070801080601120c0f03030c15020c031605010e0f0105072705241c0506101e050f0409020910170606030c0d1503050c0d0215 68
    0x408070300700300903944000c3d0014181703c00d20040105143d290351040010a000300200d59510f034085991080030f1180d200b80b0f0b00305000504c84e06044000c0842c6482c01015803d9405a0315100461400419401a03002400340c041d8031081115800d0104110407a100c01075041441511540b1b40364400d40822501803e000403009007041002e4100d00d8003008000c040d00c0b2040d9400c0344250103400d0880301140002c02c110f06440640d01031804036488400500c04064180341040d051106908508001990400c000c48284c4526058000104803035648407a2135543d403035024113554252034011703000600ca5503d400a4615581e402507010a13025503000a4000d8040d40840a4480340b00750130b40703d180220005408a84034a03190000e00c2c84540503903040000302e5040d401280c100c070700f0800518400c0c0014010400b07c0c645000075580102c4d2100003107181640d103041100403280c40c1d0b000d10607801d41080003081404024020020784000947c3d000b20340e6152580050303580201c0b0035008052100c08 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 439763201 1250 439761951 439761961
    0xd0201090501111f151205070504181a161d06030403030e0f240c1c06090f0603050f0609030d11090a080f100e0c06030a090602031f0807062a05010c03091511030708 72
    0x840d00c01e00341940004030580c0291070705c4883c40d13600c00100e85e909a440b14003030108280c503208550301900c181040002441cec0c4600c00040000d0f65201600513010513440700200c490340401442484803c0020f040108008207810203207400d4000320250007411160007900700400c04001d4021110070081701480030070022420070750311004000c84d42000044030711b00a158400740c00d00343e1010b030541c0d014004072101d50a0030004141d480500f01c45e42407164105028400e0801080d401c8803503019030525109040100b448041102c81085901980c5140e0108441405400e018001850212001c0c441409600400303c0340d41c0e59841d00c04425805188000005464010264486002a60b104ca401d541d02d042c44804002c104181c00b441010605140400007510400056268100d809903203800140005004030040e850001c0c2c0600c02a8800081c014000100300307102e200d41c1c0d10060f4500042a18050401c4111006c0f620710410845280005180100b90558152580401a850901c0700380d515 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 439764451 1250 439763201 439763231
    0x10c06020c151f0806070f08070915050403120801060905010e0f040e03030f070309110f0f0d0302030307090501090f09020f070501020a1d0d0201090501111f151205070504 75
    0x4400b0090418054081c00d10001182e4010a0040018021226003406446201a68031345c041580c0b80c801180045014804c0d060261100310340c00b80c0b180c10045001039407281c26940100400c408bc8000a900103000d004118501c400340707041c5a06c2c0d24051506606082c0040c020402501540e411310041c1b4100d14442d94400344078004c4104040d01c24440200401401613881e0402c0da41810f42d00d503000c0004402c1d038820f100702d80c3c1d85a0001d14061704a80170030148551509a0f0148642280c5d40c0d50300c402c444e898a05910042d184a64000c1d82d032460204001404800c80d038100904000070b00c1d208102c12440f2015070400d6510802c0c0c0141e0310054044203018920070103500524030350004c01c480c4074035a000f1048001c03000525640070ba000101c50100036821100c40c000038085004010144001d5116450301180140060300301c80c0302c030700709284092240b1546803913064840c1d100c000c076001d01010070001400919654162403c0080030740e41e100d403240683e0249901940e541d01200f090010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 439765701 1250 439764451 439764463
    0x4210801051504090e0706022811010e0d0c08160305100f06080f0a0201080105180a0902010203390319030c02030d02040306090b060307050319020324010303030e0309010c06020c 78
    0x100d880c10040717840c81c070f200c07aa1030301d40e0380c0301d0400940640b982c0007190011a41c10b1800d420a40c40c2c080941c11030b43e41c0c3d010034110070091060b04100c102c40c1031810301c1d2900181800c9842c060404194491700c3d250381c05103031075904c0740103601641303d84c00100f00107031001a08246060164030301164141040301d41c81c0080c107259101c5800e500c10017008035060780d000710b103541c1800c0c000e9036040e03e141c0e00d070018400319044545c1c2c901040380040001410707159141c2d0188107540e1051050f6454260380c1c5101300c208201900c008011841800d040041000b086103608a81002e480082c0d070a10f290744100070744110089500310245511180342e11915442031044922402c1d2092045403500e8030f03030503c1801050280c4049860aa4000c0410182c1c5800240a01180c070001d00500c610125050104050540c80c00d040342c1501c00d0007252112000281100c4042050104903000d445d8510300b4020141d45180c0112501030f08104031114260364808180d1014680080b4096035815101017954581a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 439766951 1250 439765701 439765709
    0x5010e03040f030506010b3402041a040e06130b0405150a0c12060b0301050d14030403060917070c0b0a050c01060e0a0b090903120c07170304210801051504 68
    0x1010000340881d1100a200381941a64004e0741100c07041da0700d81c0c85003105481608201c1d407212440551101d00c6400c0d9a01c800c45070315500c690b0301e203c2e10666012906541074105022582c0030500441d600d41d00303081c8a0310315909400801424142001c03018100c50256a00020304044034500006007408406c1000d48890540d015080311070b8500042041e00900d010b84d48040050702c0d4003444100701c9101d00545c015a8500c600310b601c3c5900c0c2c201080b028400d184000c40724820044150100100144007501c003d5006a0340800c0c011041d02d0450344041150031000b00d80703c401d04c10303040421094400e55090368212030b052a80c500001c9425103040c00b50341d014925642c2000c40101e8102103018840d40241004501400242d00c2c0404200604004548071580c0343e0051103070102401264030502e4100c0e1480704e10038a44080c1e40c46803420038000d8005018014400418801001000740c529040fa0003a5041c00d00700209100b0001d00b8100c041c401c081c4a402403032800ba03050b05003030782281d0041c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 439768201 1250 439766951 439766953
    0x60510080d0905010f0507030807050a020f07080c0312071101030c030e011a0906030a0b061021020a1701030201080601271205060c040503060a2007030815010201110a050705010e 78
    0x6440d00660050140b2118080e03140000c190320210301d107440c061403d5031744440c0d040c2c4501015030b4030303c1012180f40e0440505c032802c51091206400d0201d41c20300c10740b8083c101c9500584ac0c54101ca90525103050604150f4483c016010030034000494036884090803489c609180218040d031078204101d01412400d030348035103a035280c8180001a04201414080d03a12025a01e40006c3e03520401015140c0c482040702400e0145072000060341c40c40c1c5190244070070b1019003801014880342d820003000c0343c48071200c908040c50b4001a981c4400303400000d000d400745241d460613503443d070555000900e14040509800e060125000070500c2e0320b0450072481d20b0b203883e100315160390144e96414840d01c1d04859841075840e4010403012a640307842d140121410b07148040c00400300c40d120b00d1041001012891000121010324030000f1085c141144014140135010f0761b91802c4605000c07001c290851008841c140c196071502850791800050741c4181e500d0107226042150329192541400c82c0540302d110601945 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 439769451 1250 439768201 439768213
    0x31c0309080f030709060809030723010c021f02181e03010e030d0f0203090a0212030409021603120501050310020c0304080d021501080f2d0607110f060c040306051008 73
    0x5a00c0b201840c0301d042207584502c0d0700d5594807400d6504450680394558240c00c208411404a00c030394000303000e0354a0014404244401d6030900d0f80c21140302040840061f080b01d1020203401c0840b0407030031400f1203c0c010441c540302d28111410b03002c2d0178142409000703000344ca4802040d1a085460b0000d65031001d002030000510f680d03244c41d100d50185800c2d1404a00e400d10007000c3c00720705d100b41da220300c007004018824030f2030304e8003040100c03c1502c3d020b62503440100004102043c1c14005810b504035858818135401d401440d024140109019000c018503180200400842c0c1d800203104007109042100140c1d1602e26185550952040d40c01c00d140ba0b00c00c0201551881d0380c00903c0c842900c0c0c243c1e141c0d104a90f00c4458003501c40c130b0b45000a00b04c039408043d1444111071361031030a0980345094402d4424042e074142e0001d0424500316016004102c06042c100b26480082c003c0d10104030130080a0310031460900141c4090380602e02026040c1c1d0303500d0300000e0310403003500303891000b5003036010403118 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 439770701 1250 439769451 439769467
    0xa0c02240601022107060b150a08010330050c0f0303090705150c03040308180d0f03030c17220f1b0605040b03070c0501060b070506100b09031c030908 66
    0x410401e44181c0c0c018801c0c2c40110019902c091004050395450000302d40c035000140d01d0b202c01500311301d0409644001a4400050800a000c1c000d00400c0c1c003540b1071752402c1d851030038500c075004d850703e07000b0800584d0078044c4c0b080c01c04100e5a01960315402d0030480d8036250584a014a46940c80d04070800700c0c8000803c0c420200c00006203c0c0c11517104542c61003d09075000f0803d43c041c011088010b105500c14001800000d44520141c1503c02a900d00031445108100005040c01d4800c43d064642c1e074054084030080c107030715018403031a80509080c28590341d1440840941c000c44000c1c0381000060718204001030602e505c041904d4060b801c082c80500c100883d0130b000e19113660a01903420a48001d460000c0c03100c1c01041034a00f121609110541199101102a0380689440000722215503070707840c021518850441c09010118000c000501c0e85142c110600c9000c004241c000740c00840040c0701d01c400c0c1d45e8001078581011051441c440c5041241c0c030340e0a4018060901c2c00601300080030454030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 439771951 1250 439770701 439770763
    0x1e041103010f050409170307030b100e0415050f06160803090610050411030105040905100e0a050f0601080a02010f1704150524040225060e0607020c06030a0c02 70
    0x41c16105451040201c5a03556010401210380c00f4070f005041800c5021145040b02d1800301442c1c0c011f0143c2004900e000d250340014804800500c000c0001c070300c0c1d8014889550030305105800d0f034403070480103840c034440c00c20000880640c6180c401e40d22032000082c00c60035490540c4461022240e002c0c0000307441c2d00b4181041900c0d41e40413164950881700902c0f00041614050003030300602d00c5030300d00307441c41d50b4200030911010f45288030042d01ca07440f40e01e00c403050800103841100b10034071303115020f00b40200851501504000f01d201540d10b244c0d0207500148019140030072140110b0f80d090a01da01408512841511800d0105891001e203012040030442402105610150180c1d036000e01040b450740c8070000b8510390100d940b0319160454000b40035041509203a8000d1510342140000d2030b407803440c4e203410300f011715070380303030f004540c42a02c0e0304903038015942c1000740a4010307480740058845c0608050100710b007804024402010180c6178080703900340034020301001e0b1401503d0012683c1d01000344581c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 439773201 1250 439771951 439771957
    0x60f020315091303120e0c03120405041d0705040902033408060f04061a040f06050a0e280b030d09060206161b020a12050607030c0c0308061e0411 64
    0x1d240110030140004100e2005880e5840d40f29a0544403c42c109200e2540340c4010002520203010318071608251a0709644e04115003a14080082c4815a9581c20401884107a8819903011603e900169066880700100441c140054078010303140054405504d00000b4039000d0340c0a00c03c100800711103908030840702025045a05c0714400c152101d80290345a1000c0e54501c000c9401c0200d031000c1001060001d4000d80007894044c0b40304048498039a210301c002000c07511200e40c0c8c4e80d001e55482204000a0801580c003100400203103050040d98901108114013645030282c10f8107040d2903407600c1c981c0081e2240d109600f1068007900300c0784800750640c405815100107005d140094810413001506060069594946845136652407010a0401c907401544001e4100d5040740d01104805010030841407490366508418060070040400c5e040c4980040c2c1142d0880808108004881d411040443e8000c0120313a00040107540c1c51000c108072101d20b00d0f01c0704410b40e9036588541800c0701124000e1884000e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 439774451 1250 439773201 439773241
    0x80c060a1805150907080304141009180b06070f11130501060c0b1503160f061b12020c10020c03010b060325110d031b090b0d0207060f0203 61
    0x1041000d0181840c25034496019850018001da000914080c01030310f054080982142001c0111004251104d06a508680040c0c01c8140c0c0035420f0080310007945840300001c6401240c13070405200a904001c180810316020603254241640c0b640c07100150341d121001118403184c0c025900407182d400c2464a2001e41680c034145c18400c0c501c0800c810648d11140c41014100c2c1c04036242c1c1c0468100d295a16a42c100c0020408800e071000700b0844105921f0500000441d40148000e0a0005040c0903c4011200050300404100030030404082085010528400080741e0040404403194025035001c900e00394480050035040a11120780f4000c03a500080c08010347d1204400a0102ca03054009000081c00216540304401009247d00c0d050710101c03000c0d0149418081c58602c075002026420149841d4000c407850340041da8400408080b0490041341c039010740c480c1d2809088003480c090208040d0b02511030400c20403a4002a203108200355580f1005290070000419502c91034200b0903001d12a0721600 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 439775701 1250 439774451 439774471
    0x306050402040b191a0c060c03070906080709260d05040f06021b0420030f040b1f0b0c0304030f05060a0c080c04150504171e0c01020a060216080c06 65
    0x140d00684d281c03e040c4c803020b03071002c81e611603809442c001c014941d0f0200708010000009041081c454420350620019201d1907254103802c1e505e0601c044010002c0006034408000c0101d10000c0c440b00300da00c40000e10131a5078003840001d603460b03410241040000d013901549a60300c240740c08034501c0d41d085000340ac21580c10300d010031511691440182d0b00d40c0c4408030704134005903103000e81840c1c42c60254460442d40c604010b507c5c450b0200340c4201c42460b40180c1d4810448400070041208000080709003641c07018400c00800c07100b5200341c00070440c403001f9001340d03450108080340a41540d0b1080040c3c50003542c1050440142a116042a90300c40300c09580446801c1e041a80207680c8a0040c1c44413800303125000c0d6518505443e10028690940e80032079217108224081000007820442d40c8a8983c3e00c030040d50181460219841e04030800252949203020b15401c0f084004101e60f8020800319041a0812401b582d5900c0d450050700550080350f000400d2000003054840400c0300015210340300c0c80442c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 439776951 1250 439775701 439775711
    0x2220f051f0602060609090304050607080d150e0a050405030c0115090b1009090e030f0a1e0f020a03030b041b091d010b07020103020d0908180a0f06020717031201030605040204 77
    0xc11822141e18000d12000d64410790205215040001d0314a40c0a60444284c1c1d04080e11200001ca607540714100c02c0e03400d40000301d00b2000540c2c2511030250000d0080c803009500529003651103400382070062500700d00582d14000134092203400d00c215480903035183c0080041d04070006c413044c0e09400c0b600610450615100e10748205040210740c20b44000c5041e2144141d13079290441610103405900c000e03038040d0000f800700d08040c00300c4030050300c445405611400e540030035104401d501407807500c2c0e12004000074441034034502c54021540349000c41d010f147c0410b1100320340010a015140c0c840c250b038501000211542040c903400144802030341e4202e00444544484c0c21404450b03024207004600102100700148030056006c0da0003044034040c60f14011540404035120503899421944605c24041c0f010607241d440c9181c2608400b02410301c0c00381e0b0b40e1180d820441300030b41e59001801407515004501a80a0501008000703441002840781441e02181d030b120b18244024140c2600c0c2240030f18104 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 439778201 1250 439776951 439776991
    0x20a0204111e03060a05060c010902190503010b030111030c0904061e0e070807090e04020310090c0f0911030105041d0a0809090106030e06040312140103200a03050a02220f05 76
    0x82c0c0100e03070056800420042050303081c8020444c90b07621007480c2c5001503584566a80050711813500302001091600300014010745400289400d48909500c2a40f0136490184d0450600c0a45c03800d03242c0004000c0c003a181c4442c0b401000c600103000c00d40000c0704100100d1315400000009401710015101744d0024034400340c603011401d4441403000e4641d20040741006c1c13824401825150002c0d43d0190000301110300c0302c08003000b540216144400141c0f44221190070601c83c0100000f841c20007800a1b0500300f05051403840048440c0c00117004045c030440c0c94405c1d0240b0a404020b07150031417900401514446041071400701010f6000364136003070180b200000001480703400780c42114142000400544129940c45d0340072241001d8500310034540d255a6001030380d1541545a61034041c0d8400c8524000d03c5144110403142da0117a090450310039100c0b000c0c180001040443c0320038600d0350603140d11172581c8264128000750483c402500d10b00c1c038500f108081140d940c0c0d4120702d01a00580890207082c2c504 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 439779451 1250 439778201 439778257
    0x130212070b0301030807170c0a0606050d0309051c05030d1512080d0507110706110601050a0515030402010c151d01050115080604110f0d060b040e040f03020a020411 72
    0x3052089500c0d0000500042020444401c0107201c401d01c24203e038952001ca52145101ca40c0042d105141a036000741401020071000d4401c14001d04801c81e40d184c2204c2041d03400505003042405101d015180c030b07055550149000f08100c050f900e50110581e038540f90080d40c0d031001005081c0903225042c0703440c2030018000b040c10a1900c08240c000a0f0030780341c207080c03e0604014003c090103c0d0100030410340c881925031014810a009014141c0e01d9000c0b5140900380689001d41c10303000385205a0341c6003010000355941c80c4e81045050f4030607a520740c6075a110700043c0e44408013548046d082c01c0c500c54034685141419846484560924803068002103541f004203401c0320024003ca40843c001406a0b22025020304031081d80b1500c01040800c05008a00a00380c5a4105102c0411001c8002c10140075801a83c043c4030060499200c3d1941000e10342020840d9504003d00042c20401d040c1e10681d0515100388180c2c0c4030181c01074414072045420701d000c140300c1d80c80015510303416030003000d10350813105c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 439780701 1250 439779451 439779463
    0x3011e050a0204050603040f0f0c060504060306090218100e180910090210030b060903010905010204050108010911031501050c0609030a02010b01110c010f090305150a06050315010314010b09130212 86
    0x60050121743c115a11130740c409192290309802514221003240b5000c00040c1000300d60700c00780150340d1358203840d03070f16104c0d01809595098020b020943c1c01803014800b502c01c20107007011400011224180704440c801c40030741e41c1420584856070040c1ba06080307800c16480010710f1038000e84040c1c0894818030304c8103034810100c944c01c200c0294000c542c03010040550344a070304003520b4082e00800107850901c1400000c1c1c00c540c6106000c480594010600708032940c1c03c41c00ad20f0040103421420702c40150b02c0b03804c20f0070390f00c001400c3c00c11a0603c0c14010f003050740b00e0820b44420700c489004403005414602e42050380c9400c038400100043d820120400850351080514200340da542c100200041001c0b4030054440ba00d40120102c20403400140c0003020400c20005109800f03011042d503055400c1410700c0000f918116004540203a00a000c00c512542d00c03c142c281c11aa0403001311000904646000f6014010001055500a020a0070711150015400d0000340d20741c030071200f414446c1950850151100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 439781951 1250 439780701 439780709
    0x14040807060e09070c0602210405150f01030c18060b0a09090c03020c060c09010201110a0e0a06030c1e030617060105130e03070f0221101514120c03011e050a0204 71
    0xe00c940c0011030024080d500a840029623000ca07901e281400040d10101c80001203c054400c1c3d4000c40090b1b4541c1601280550840120540c0b290550705640325100c05904501c1880408001c0004c00816142623501c40c6002e00a0101000e64400300501e005092032070788d002c2c2c604040d01c0c210510761a54024400c403011403080601800c0e1a5454490b6010030307812182007a8159500e40b4503c0410380022001001c170090385d41c079101c2c21094035000f40b03d40c150054000d0010325142c0a03c84441e9030300102d001c071400521044400107810410011005000c4640c170004c0100c041c034030b04170210300c0082030340c0781030356000d450954505441c400351105071040c0055009203508104042004a1b180f950020b08a50008e0b120610000c1840072841c0095188004842d1079040404000303068800c80c010001c03a02a201c0700014554284414040b081c01c9500040d4407a85484c1d806610f0f00000340000055160000c000300114080031400c4043c410310003903142c080524042c001444c001e124801d5906075 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 439783201 1250 439781951 439781957
    0x110318011d0a03030905010902091006030c050306180405070503100b120c360106030207020910150c03031d0d021c020a020f0418030201020d1a15030714040807060e0907 74
    0xc4400b940b0154024130701000141c8855490b4014540540c849500a07401030040d610074499040c94008000c0854107a1045401000350820500c5100d0f0744170595488010001c2c04003518940b900d00d8610315044070b5a10090f014092010700e44d007044100d900c04003001c4070640d40a500d011129070800e442d14004025140e00024240e020b91881030407401c000840761a11070140444250001c0200d40c18400740e108200103a00092a8400c41c207003070300150380204541800d1503a40f400d1280c2200c9280d142402d031020040422145424907209401008030840d8140842d82c0e0b0f5484100c9954603041000c00d050050b1080b020b0740c1d1003100180160070440d44a41c1d02a10300f60f00e082d0301300003494400c212840da0080d11030700e64010002940308020100c510a800050ba90311803c501c140c02c0e12040c002d400c290020348003808486440300806101c604c0818010b541e13680e51030013410b549240da0800c4020008202080c08200700b280001c034441659a680c1701d0100f8420004c04000801c20200c0b144000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 439784451 1250 439783201 439783213
    0x13050f09120403050601140102211801030212040206030604390503010609091a0603091506040204031a09031b06040b1b07030c05010b06120f0a020a0503130501110318011d 75
    0x102803071f4500f455a05400c14415030f03c45406d40030380e0740120031010580c20f0300700d030000440e00841e9a05841d00358070a042800d082d424098003508040444000500190203880000000380341c99803198000800c0e0a1540d10076503d843c1d0f50342060502400919411100f85500d0020048041c0070300f040d43e040342c032642e444001590030810b070704001d486406981c003446115002c03c1803555880c04080d510410f604c40040c505299085a0a010312002403d458010791040000f407000c502d04d2881e014031803100720303154201e98540c4c525442c03a512a06510040c200c405502070400c0900100c0c10901035030290b01d0801d51a110300d940b01c004038040100c040e0300c14004119000010340260032110f0454000c00000484640010214145902c1005030140c0000030030200455032a00307002098000321001011420041c612002404d43c0c4009061103030f07200000c0e2214001c100e000d4108402800030f40311401e0716800d20303401c01c5800c021780f008190107650030085c0c00c41d4107469502071440380380302002c01010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 439785701 1250 439784451 439784459
    0x30a080d1e06060503091e0a030c0c12031d010315060e0a0b0f0903010f0b010c020913060603030509030d0c02031009110405100806100e011413050f09120403050601 72
    0xc000d0203044406051049031128000c10100d00e072054000a0450362562a81c80c034040102d2414907406a03d40304080020800c480f0349440d0005100c0030390b81e450305200078142da00c0e050264034240700d60b004c0d00e044e480640d2440101540841003200c0c2c4c002c030502d26501c1c5440d40b0015029684810040c001580544004001b140e00c0344011582000c009080600400d84a160040041d80f0104404e00403a0001500c4901810709210700c03196482e03010000c2040b0313a400e90000f0040c6031410b4001c0c0c890282c03000807405140e9070b0110350603840c3d403188042241a680746006881600726210091003030144415409800d8054020981c550b0b600070040c14403484070910721001021413903400d0b11740d10b0003110a409603844910406000e126080c010381207152810312a42d20b131480040905a038030030341040403c400700c5202c981c5d905482c0c032030600580c00d0585401107040c041101490140c800e08100a0102c810701e80d0700e00901643c0d01205071026801c040140d082c86224510000b4910303070050b40100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 439786951 1250 439785701 439785727
    0x7150b09041502070209042001050f0d020705030c0708100b0f10120b09132a05010c03030b1801030605090c0607060506030712060c08060108041505041104021c0605030a08 75
    0x507070030358002d100504220032900400c4600d03404a07012118501354608400900c0808011401d2001d001d1030407502e030180d407070842d8040d0300643e40040d010b1a00440c50404005050069078210440e0100f12036040f41d440b420190344820645100d013405261105c64034850811349c0100ed502c840141803200030348400c1074111514500c20030920400d40e0358805803111070380c4011046024400b0070422910150050a11281c1541e40300c008219200800030010030140030a81e603002191003d080000041842d4141640a4020031030304d070341d11641d4040d00b0700200e01c10701059030603240601030401460b43ea0901c1680ea40001c0171400394070680501c039a20014501da0002984940080c8c103079803e542e910b1821000300c81007040f084a00c0e64403018407100c2c80d035200c43d143c0da0101c02480c00342424101501c41600396080c0c0380c403030122a904c68000405001090034205041e02d4050003c652b40c01a10661001100d0003030101d041c03050500342c1c006030fa86400110b201007240c01880603454034030704d80c10003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 439788201 1250 439786951 439786973
    0x307080f0115060f05310e0612070302031915050109050a1a010207091107060912030c0e0109050424080c030c06041d0a0f021c1401060801090b010507020604060507150b0904 76
    0xc603e101101e00c4a81c409082c10f50b06680050202d1f2492000504161040104007030000701c1c2c141d41544008000c101684d4009000145440300325090013000c00d15040c100005e141c6582d40081c0281805c1c000642c035800d80d80014840c0d684a8001c0000c4100b011068684080c03440c3c416005a102c401c09200500155100c01d000201d0703c9115440c2000359074561081e191a500180e40d65038a80b0310b141410394040c003585407501007514001c0c003800940000600a6422801a503000f5965464107040c00c0440e0f078404403c0385030040e01000b01590b00c00e041d07592003007035040781e0b8040e0003850646449420508291010703906c58100e40d42100f0340c180d12412940600414030708040c0d4072805e0038031081d041ea02c010640d01c0d00c60a4111300d03055008400009a95000210100d42c041030001008501d91021085056424007078001c10b4402000c40126858004c170007004c1d42c400307000140040c400d80c000c0e005100e807500c1450310205602c42451400116003090354070301e40055400c00050000750000c015 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 439789451 1250 439788201 439788247
    0x1014040f15020d02060c1c0e160f030213020c030c010905061906080307110105071725150b2205040b090706050f03070c0803100302030c04110403020f0307080f0115060f05 75
    0x101c0d0b007c00300d0102c00c0030a0714441102d0000b29045801a01e00c40e00880e00c0c135501820180c1d810f888030524550108010012078a0010380f901d502092800800d0401d0013112002d0544078024895071300b480c200303030f0f80381d40301176924944c1404d0b003900c0680a945a809010200c910070b00207141070480f141c4a04070780b00c10145450f410040100302181c0040d144007941140c0f404800f90380380c4c803142e034486400f2262088503125800603860503000c030001006040783c94000c00b10380f00b0201d21034500c0340c040b454180d2100440c0b03841c0d400c01a00b8086228403030f40030341d201e94001c3c0c0112505454410790a52a0f911a000c0d80d0001807080010001c0d50920000854004081345880c0150601c070b03440741c084a0b0000e903010f545c4c503980d46900300150301c0c3c1008000d102040840d800c0104100b0070240e003c80c0e1189100090042d900341122600d541e40c00e00c001d00c010721408080d5290501070102060003041030394a0000d0401c0440c04c040b030340c0c2c2c1c80344600241d01040d030f4852500d0083c101d400e0348000840100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 439790701 1250 439789451 439789477
    0xc0506090109080d1d0f06160203011d100b04050f040b090304050d080d0f0501060c140114130b071b1119060c031d030c1014040f15020d02060c 63
    0xc0000340244081003035130303080c00b559502c260a6140b03000c403003040000040f000c0d0348101d64109586035586e540d442124043c183e0030300a913912540b44d1021901501d034041c51001221129005220750510110781a11201444d030401c0046005820400c812a101070f00d15030018840c54000400144d0ac0400c1d050300010304400310303410199035400041322044101004c80c1c07150808039613a00c24403024001c81754030017900b00d0240015030414500410341c130005080035019000003c11000d46400c01e61100d00c45040c80600a000c51500780fa80c1a0549261402210360070381030000140075501c5448092050950f5810454610400da164006103040c800c55941d030048135082584c03460300e458500760008007125202c1082c141042d08002e021440b25902031410000d405e80100320547d0f020a03101d40c0060110fa8100c550032300e10500f29520214200c25410520000034040b03440c00a00401c101101c1400000c0c080c580c001c03403004c136101c8060b180d001c0b000d688404040344140c149500a0039090160003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 439791951 1250 439790701 439790717
    0x2130504050a080a030b1504031b0b09011b0507030629100807210516020303010b1e0403060f090210050a0807031d070311040509070602120a031d070509070201090c05060901 76
    0x54000c40c4025544042d8030800102002002915640303408298480f00c0c4484ac05803400d150761049201d50b20289040201c0360042ca089951034892600c02c2a03080746c11600402d84a192000c0140701800d00401c03d0280e80c1c850107418130a401442881c80400303403400c2c41e03100c901e29080e1051103003c1c111031f00303012210b036501c14020401ca034658a018141c10020441e81440c1000552805400e0307c00d60840d0400c00c0144a80b4900310201d41c44c2c1906500c11b00014050a001c2564501460300000c10701c90401c810036400b420280c000c03110443c000c03110050251002141038401340b1815145d840440c900600203001c2c03c0c043d601803100c40410345e039800c564114032504107080c08a030360001c84900c02252040030b124100383c440d1030351110300c00000700175203401c2c0600a956104040707002a4003050008c1c140501c94401d41040c8070300c0600300c180c42c117429041081c084d1244141e0040c103003e07408110001d000584140200c451042c1c0042c080740c003140c02c01d01408002e0780120390090520a0b14 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 439793201 1250 439791951 439791971
    0x10050d050a0e061f060c02031509030f0714010609091110020c031203040b011a03010314031903020c0624040b041d0607080c1315141602130504050a080a03 68
    0x43c04102d1140113840e4403500480d4440d0407580c01281e00d50449010402c46812640058800151040782c880c1d542001503115600d403203c541c6144100860305140100200d80354081100040140d61802e40340c074000e12807030361203a9140702199066400a010303000040e1203940141499001c0e42900041881585c0e28004000e010a18002030f404503c000c800000041200780103007965814054002404490120001141c0503142400103000c0600080203120589158500401c101e42d030b0080d1134075404d40f1340304070040c02900030b41180c00d500f4413034041d54002520205407003402402c403268041d00200340d0350101091000904400340d165421650380d2034885a44401080c0e4154000384000041c0403902d000e0500800060000e8008038840400380940c3c001b90340a803010703070190303200381403045a402007090048030303403280000004c200c0d2035000542c003160f4000030b180d00c0c2001d8001d4031102c14002c80444550700b00c80d0201e40240294219150600c005a41c110013040010010700d03000c1011750036 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 439794451 1250 439793201 439793203
    0x1b07151103150405100b0a050c010b130f0e010b062b020d0b01021504050d030905030d06090204060207080c060d0c090f0f0302011d0a05010f020a1704060e10050d050a0e 74
    0x402d44080100d4003558801c000c4500d070600079658841603005510419520703040c9400346a0043d410688140b03c00401e82c0700b44018254030140c00c4090082100d03441c0280800f071038004180d0519200c00c142d08144444191034014095002e0103880a07081c03515005003407a40c81c0720280304410402c6440310300f12400c1c0700c003441d40c000761104002c0b181c0001210000c542c0064a808005040d001c0c2d03480d000c00400000c61000703ea68003900d041424045100c2402e0b11748170307040d03201c3c50700c0b4044100e10706036002c501c40c0390503405001540d0349030302201c0071076454082d1140d507070070b1030780380564000d8040220003120b40003034221680c1d00d2514245560300c5c03919580b69004208980d08083c09801038602c00300700755a4010041c60941c881c40e1a00328603440c525000c51244034040c001c90741400001c8882c6004c2510030020f2411240c0c01000c20340500d800e0a07a203c0c095406845101d0015010368200c110918140750240d22440050315420b1034030f0880d81112000d400e00412043e0581e030354070907000b44210 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 439795701 1250 439794451 439794457
    0x13080a06020c06010503160b090d0210170114061e0714030c0d0516030e1c1b080d02031c0212070e04060b0301180203040f02041103010e1b071511 64
    0x110a00001d82c650410041241c43c12105030b02c1144039910101d501001a0b410388010801d40300102e1100d9603c042d448042130450110500003500300361000107828a50f0703449180c1c070b003050b8010001a4184d981e91404545007400304100d07141e00c90700802c404030403242c600340d0b2041c0c07615a0841041c140145a1980700054084079501c070140d81000400002c515404c3c00703d0340c0042c0e0981800da0a10600c0c60171070b0300e00d4210440c0101804400010301e182682c03100102940c1c0f06030710601a0410850b890201c07400101d02c11304a481c02400c010120310360b68003113401d02076005107034000c500b4800c10200072801d0100154001840d04e80c00c00580c1690440d01c0342c90703072089003242c6980c6145200300d02072000f11703403541d4400842c1c3e00040c0014000b110440c1000d81410f41c0122000d601c98071142464205910341100095009141ca948819032825003005141200c100b60380408040c2d803016070050403040c82503800110401d04210b2040018040d2108000c40ca001c81000101083c00000f4807400354 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 439796951 1250 439795701 439795703
    0x2030903091c0f080d0c23030709050901090c110f0a0b150a0303110c040b01081f08031b0f030304110d031215150c0206030f0c07060203040b060109170c0613080a 71
    0x81300014150002441038001c08006800500d0000c0e82e0386100d000303140f210306015a21101c2e400d130000100c0c0c0018071607010b01010305002420f00005503910100c0000034140c40520201241c4a103c40f44c4c0170550100703c0854030f41c1c10102500b03034520141d0302c400034030600500150f5801d403840c04400b52500d80b030341d403400518443d46481c001035044c04040307864192030181c19880b5038201102c09001347d80c0201016004140840800141c0080d030307446100100782c9401140c0103100105000140d031010204915503042c02c0000d0368180c00c007018074035403644401c0328064800c0788410b00c03402c843e0808038003c1d40c00602a1904501f181d0760030302c04400340d0792181c3e24804c00e40400c1c0400d0040e841d20400c800c00c114001e003084104025140e000c20028040108030301040c128501c00242d13940c4000b02142e400c1548134204540d00d240510701020081c005440e5a0300144809002042640c000d0100d0880251060020000d102c910420800a42c0c0102d90400c40485a40c03800030f9031280030016032a040e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 439798201 1250 439796951 439796963
    0x902030c030a0e0a150c0908011a18010803071e0203010212010f061701090b0103060506130315021215030709111c020307140c011b0e040b0402030903091c0f 69
    0x3814008015815900c104503c80d10642060401d5030018800740310741e42059a60807000b05d40004901070a0740c06900380c0d4003200b02c55081400720701009420200407814000c003110043c035003400b0700c07401c80c0311910240919000e0f0b6100300100b2021070003001c052043ca0108030684900c80d40c01e071f404207003a80c100c81d51018645d0100001805004200c120420140c403030b0b407a140e0685c401c00c8246100700c0d60107110300900f440d80d50349150328a034801d4003e907000d418050402640d030450110b0045280900b840182d40314001100b01740d5100d825402160600802c4845800544d142c0905401c07050710310010195140c810403030000b515010700e002d4624007840c202900c80c1c54424008402180030f190702243c4002c40d2040041101181d004080c600d420203040d503034691105440d41150340188003004520811209000140040340da10a2884400f0201503a0600c2545100c8080c4016400300b40c4034603009802c2407084961a007441050303541e0850700c4910001d0911456150404c518080a00a07508 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 439799451 1250 439798201 439798207
    0x20d0803040b24090c0705010510150f2a021509040b04020705061911030f1e10060e0d02130509071a0d020706140a020406230f130902030c 61
    0x921507040e0900fa440081d964400443c03c041441c541c211021048425100f98440b00103d0003100c0b04006442d40c480c1d110008014506009640300540411849003402c0e030a5003a58101510f842070041031034911460703d5503e0907070b4445034030102a032643c1482c4080750604460140c00359981c0c0103000328549060102594981c11a000d01c0140e0300d8400034980158010424500000c0c000a203599004180e040011310350342c030080d00103020300043c11100584100200a00c0003281d8601d140c14000c6813a1540c0803041c4988003407458603407000301d504559a03200400100070650090681c00c081170070007000008800b14a42c00038048960461b1481a4160342d64100400c0800c01c0005101410551500113a643d202d070340c2c040120710035003046010058011030060200001c0f074119040c5400b0150041101d4545901c070341c0f00a411501ca034400150001300c0c5000f5540c0c0c00c448210344900340991481c6040032a500e0101d465004004242d070500448100040c50001c0c0d1018500500d01040c20300c1d6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 439800701 1250 439799451 439799453
    0xa0f08010f05040f0311031204030305190510090e010b030f070e13050a200306040b0405061612020f090d080c06060105181e030d020109151b1209020d080304 69
    0xc216900e00200c540304901c1d1500b03002c0401c81360360341c14121580c585004c1261a401003001070950050383d110613016400c0c08240f00415426411041c8100b40782150101000c0e16680c644003a564141c800152034100b100c400e1014030019089040501c4c100710010981d440850007080c60050003a0300e042c080e40181d10306006840494100340e41141904503100ca101103580c480540b00c40c9940e000500d12035071400340c41aa111480c02c1014010402001c0d10711a103001d08003080c441c102124110348501a103000266000004601c150142c000e95681c42e2840305260413a100944c8a21401404010305000c810303601d64601d180e800c00d05204801d51a1519100750a03146041800340c030703003414440c0c24000303000c107803000c000c070418142401c43d0440441400301c0e142652120342280704580601459521484480e01504103100c030341c0c403170300310f0204890030f81111400316043c4601c24551080b03e03c610a440340c0c861000110608904440084c00341c0c0d250780090b8503640c81c80011070f001c030404000c101c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 439801951 1250 439800701 439800703
    0x5151e092d0a0f091208040309030b010e0a0c020f0c010806040e061f050402090f010e0a030501020d151a07141203130b1b22092301081c0503150a0f08 66
    0x70680e426070300e1050284c0b2000390343d0740954280e0000f00b501000303000300004087c144622880c0c00215006421030410396107034250040c08031400c4074142038850807c5070fa41d01a41c80040e20380c50003823101e4082d0100c658a03a004407038000002e403081381d0090311034482d041d19107818060203024248815501c003400c1c2441c01039004400c811f501c180d2049205003c84801511070031500890740c082481c2c00801e640e81000045c00000181c1c01c0034041e50f2020480d00100e400340d912510129941020800703040359500480b50385080040e14400040c03505001485c001030b41a00c005200c07106181c203554100f10350010301c00c000e0700304072151003e00e480e21516500b4031003580040c540000280405d00f10462040c41d0404881c0b06960010554420903100c1c49500413800750300d0000b0301010343c2d050041c4442084941404d014880402e03002d43d5895000060b101c400141d06e640e80308800d03030700707220441160030190741d02c1e00020041d01016008203401c0c80c41d0380d1030400d03c501503c211040c030111a03040418103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 439803201 1250 439801951 439801961
    0x20010e01060303021c02031b01090605010b090a120215280e09010815040809040207052b08040f0201080403090b0c010e0f0706050f0702010212030a05151e092d0a 71
    0x18120480d44170900a4003c1d40403013240c01080c4250503004e8080740a014250050100003c043c0c241403801002280d95202c00c00104244101190880c1c0d0044c0c0f502c0348203c01d5110324200070b40c080700c451002c66100d0380303c42c098a1942400c8592068810402c80f10400001040a80c14005460501c0070369442c605295100d02600e546c800520903000e900340c000d43d16003406400986018404030321404a503540e901100c05e0294040300f0380e1903c4000502030290710561600321040c1840d4102c0a149082c440c4103803a104a8208068807040f0207550015a42204090002d41c01c0202110010400201034001009a864443e00008507600c070b1041c060700345a04042c00d054160030160007000707007540c130405031032034038441959482d5201524030040c3d250090107041d0045100000c0100464007000794071040c4246100d40c4440c2d00080c024003041115980480789808c210104801c100203420a4031255500c01c0c034101042030301c41c13681d0100700c441c0d802035111001c0f034000f05c100f00444d4928030b00030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 439804451 1250 439803201 439803223
    0x70501020c24070c06150806010f0611030406030b040f0908090103140c0703052101080715170f0411120a0242190804020f010809070620010e0106030302 67
    0x800c80916003a400e842c2100c2000e0180c10400040749502000d05c0401e45c0800802c10480038055181c030342c0d401c40c00b510761009200d032a07a540705105000030305900071031000c2d0341080002c01031803520342818400e0703004201000c2465042550740141c0049607200d4820603030003d00440480b5207940840e400101039440c8081d10084810f07001c402e004010703200f14162a9050384c03504045490b19500044030000c40e47c40210254501c0319200001807400000c628a81502d50351b9440c0c14189a07214001e0f9100018140200c40d11045030000440e80803460003072582151064040340e5410007600300245200444102c4140c958000304044001c503c0d080d03a8080000050802000c0214952844080b209100070030849000c401c2d40c0001001d543c0c02022502940c3d5640060071400c0c1c03040000a141903802c4800f01e00030601d0b01c8400382658007400c1158441d45080c001090000d04089041316518200842481d1131114030161809500d004e00500d0240c40111000050440c80c1d42002860305c242018 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 439805701 1250 439804451 439804483
    0x1090b13140a0f061b0206060d1407030b01030309060f200a060c080a0f0506060304061d190c080f1e031b011505010807081609030b0708060109052b0f08070501020c 72
    0x1910f0b0340341a004914140c8c011021140c10303e140e5581e00f81001c1030f09144c0061030042c068030390007100300714800e91264141c03406070f03460306aa10349421050b544808010001804244132180c810303558003403000040400c4030384000369100300c055661a8001e4500c04100c2130085541603003000302d00c2e1480c2c403550391000e41d0f24906002c14201324002c160345200184c0050120394843c001000c0c1000980b90500d8000c400104480d000359007441030030022128058110b8406041c14800103c9140000300148091d6800d03018010807000c1c54000c80d4508142101c0051a010a1141c0340444884d4104100384c0c0f110b101c0013046254a8810340c00742c0003215080030b1f0501801d0414000c0c10360340100129071004102d03030030840170200001d003a120047c25070320041c100030401042040183c1d100e107005c0c0c02460207899100201d511101001300b4071051514400510070580d4003019142c00201c4bc042100c0c1c050000500390710f045485003260b55101010a80302690000b924444103802000100004001c1107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 439806951 1250 439805701 439805741
    0x601050d0e1c030c0503010506071a040602070201021912121b0306030b0108070303080f1b0f0a0906020f0d0e06090a0b030f01120c06030203070e060d060e0901090b13140a0f06 77
    0x2600c007405c42e00040c002c460107004081005002c02c560f2003010241205210100356481c5840d152490180d442484124014005d04445860315101000340c014960fa11446281003070074003900c111a00008402c140e1a11600d502d042c0e80c107120b00d400c40300c0500d440760307501083c201c1c00d45c2004015801d042e84020283d074081402080440e80c0041c0d0a50425103403000320344582c680300c1d00040403028116403c040b0920000300c0b031a1240600005043d40c008503100c10107882e40d82c40050b030720356940325010700403500151545501c3d18030804400304034840040c50642448151008074080c52007540220450001c000140003880480290950041c4210080c180c42d018090707070b41003901d681c02c1c0300d41028186c000c00403072050b030b0040082811040c07001d807490351103126043c0c1e0440038024601c034421210b250039001c03802c980c00600030080402d0b0401d038200d41d00d441d2100005e41c00d0008550550300b48204a00d070b41203800041c0041c805682c040c15182e081086141050800ca8802d403005101c61a0f4103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 439808201 1250 439806951 439806971
    0x6140903030702010c03120f0e010509011b03020c15040507060206090307050304090e0a0605041b05040213050904080d0603050d08060d030806010302091c060e010b030601031a0601050d0e1c03 84
    0x100302c940305903080c0b03020421619180340544181800d5254a40303903a00705104000d02440681c001410070f0744200080c000c2c1e88440308201e08035a03890980070b5407240401450148107000c0d80052455074041ca0884000401c24036498500c000f00f92412160750f0840c03a420000c243e0b04210316504800f000000d1840d0030200c0c0d0324103036244510300c1201a103644500003640200000d0018044c4550004410301c02407810345001504054030b214440100c0800c5040440c8500f0984241e805071041039005000c52824002000300c507035401030040781c031000304121164409084d030180100443c4540000c0540f80c1041038003900d01900200664042c1591100c22804079034490441500030b41d082c200144e9603401c5d800072034000d041490b10700c210301007642c480d1410441340740d01071980d0481c500000c2080c2e031075100070162141403e20010700035082d025894540b03508807208258102a05041031460807103000c0b02d076000d8070f80d01d0414450a41220304030a8080003042c04c075148010003481c0c10811407140e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 439809451 1250 439808201 439808203
    0x1c02030702130b130f05130215280c0606050603091c0306080307080d0b0a0e072a1b0506040f09110c19060b0303030c03060f01120c0906140903 63
    0x1030098064401c1c5411140340c1201c0c10075a1207203901d1000039140d241c1100d400b14406000d00140e00500b00454942000076428096015040840f5071380204042800f20044401107801e4000ca8040e0001d6202450001c00040c003000822401120030f48802c42c2e07142050a000f42201e22541c0b016004140420801500075800300e0b40c00019000ca80c2c11244022003580b00720004c0400740c0250215100018980d010303c240071005c0e121441c0c50752001d0117403c1c83c10050103021241c40c852043d010841c1d1011603001e9008907044100700c800d40001030303105050314610601c21440700c4002d69202811141c80ca10401d500f205030005000c090704c00c1407070540b0305148025180e01c3c038810801d24a6803800e403071001c1c00542e07049419101d075800848644000120b400924101c0a034000c4420318035024300d0703100d07a040120649115290802c11182182d46d90b5061241c6070b100b60648504200c0075148820344680360340300b1015000d80035510745041508080e0060b081c51b014629007029030000f88160b990703540d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 439810701 1250 439809451 439809457
    0xb0f07060504050c061b0105160e01140d050a020702030f0111090d05070b0711030d02010606020304030210121506020f0a050703030c1a0c0d0b100c02060f040b0415021c0203 76
    0x40d100d10300060940c1c440c01d0850038048080300c1c096021200195141074503c01e5156504c2c811100c8000700455199044450007101c00c50031204d001c162074103852070240d030080000340c900d000341d04112480c00c030001d0111820dc807001c82e206884258045207690941c14100081031440c1c1840c0003c1110b54295010300d06107010b41200b0901c40c91046001c2010800103110040003040c080200326241c42d01803400300116040100114020301c10b88a00c203070094414096102280d40c5500030b0b40c80c00c0e041d82c090050150940c40c1746420f0001c0d04107039004c692100e00c0b846c0c82210301d0041581d640b500300f58000b401c2003021510301c1140d900408201002ca1004283c12003104e9060420b00215034403881d04600307d15000780a501c01c1c1300000100140c40c112803000b084000100c032001c111034202101005040c00a25060100090240c54084010b050280c01408005d111640342e6041c10781d1210240c101e43d215400c02c812850303000b00d00302d8203a50100200404400c40d58401019010000d0000356a80 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 439811951 1250 439810701 439810703
    0x60c0b0613020921010b0102070e070305250f0f18120311030307020105040c09020711040b0f0d0c05040b1c0609031205070203130e071b061b090806010b0f07 69
    0x25600d0116994141e0590407108000c00151522a200c6082ea03013030f012458070049035510950070240784010541c408070b514829585005903092168540110890041c00010181105002c0c4407001c40c908a041400207a4080c080d43d61b070044603080004010103010600603d01c050003a00002c0c80c0c094030042000d1000c1d1040c0c451342c20b4403c800ba003002c0324448011604a0020b010002c01c3c0402a541034010600c5207015044c2412203507540ca407100201d1041c1000942141c1d914481005903140603001104054002003044240741c80c64400104d0341038400008813031141900030204498101400342c0400184101c408903600141c41c144240c0d51108100c0c014562580c40990a04241c0500c12103247c903004072000300401c0c078000350003075905d0303028002c0500048082ea01c0010b86600090300e50b0305c500e011380d44a1205040d020810217946883c01030858180d03889411030441c2070f102c68101411000c13259511000d4615214455061030410b0b0026003907100b08104415405010b4003c81e4022 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 439813201 1250 439811951 439811959
    0x120509060708030c070b090f07060e0d12020a053a020a02060f04030b0403050301140406081207141903090b070807080c030903060f0a060e060306070315151701060c0b06 74
    0xb65a03900009000703115000c3c009188a0110007031185007c1c001079442802030390101221003098440805036100d1002110650f4000d9188404a0024001c00520a030446450040b01e032550407961720319040c5030100e00c2d02d0041c900c4040b007507030104101c034043c100340c0418044a000b0303040071144025200e5000841c040d00602e00000d005100b050020102c82c000c542050095089080510700104640c2c001c3c450f43c1c5000d034115a075052549020300c201c1080f2000b444c0180341024180c6007041050f0040e11044ea104244004148921a001c1c041d298800e0011030080c2c0d0f081c0a0f41c41d000d401d11005404c81402c21030240240d074002244401150b099a030464030641c1c44407011407032645180708000805815000f22414882c011b85c692680b41d0283c0200b8000b0b1054540b90f8520b000890340c11280791358140d100c6004074050380e01952054041403454944101d406464180c0b03400001c640c0103144000860241d0980d00c0c00f000e503541d8901510480c6481070058140e03032141e611110003e0500c2e0b1003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 439814451 1250 439813201 439813207
    0xc020d060e121903050a052818060501050a0b0f0f03100314060103031b030203071403040314030c06070906050a030c12060e0907080607050703030903090e13120509060708 75
    0xc864010026822060502c2c5021583c50070034006014103099420b640e0030220382040c001c06d40d40c2109001da2403040600e5180300e5400c540288034001a50201c04e0644642c03503503230010312442c00841d0301b126956402140082081d5141c001846a0780700d45620440c203e02c0c0034013500440300070306411109051000d001c10303074a98403034107a090401c24080c0d000410070340361801c0c015600b131004540307507049038003c1e2503a4060650004207180403204845006006030001c000340000074844841d12540e0f0740204080300d041648980c0d51000752001c403503414905a001244003048240100007440d40f140e200d00c0c04046a43c07a0074005800c0d80a11800301060580354a942c4004030722800c00426120080c100900c00b190b81c403200c68960840680381180d65015186020030507007000550140100050b980d001c0c0b50007078a8500b00c00419203a801281005520f890000712401941d445500815540109010492092810b003c1c4000200307a060b00f442002c0c0b0240140e9511007055a4074a80c00160a9607 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 439815701 1250 439814451 439814471
    0x41703090a090f2004030b0a0902060f04030b06010509100e220f06090b09220f240b21031c0204060f18030206090103290a05010c020d06 60
    0x10450040c03103089a04860003020028800d40a0b0308014400101880708010b00000301c0c003641c494111000700c1c2c5180120401003000090822100d2070307886000348100040c2c1c1c00c010f134006034055025091051011001040030700a120044410503003002007400e140b850b043d16800030400c8400800d101c201032040009103041c0a4035080014590801c01300143c0c1002501c01112070018400360040084d100d2411002042040b414815105640801844400985da842c460308480d8109222400a50070981d80f140b00000d03030051901e450988911840710034004440da04c41c00460b1040e004142403814500c0781e0a0b15164540d03281c03c034886880081c24191010342c0300c286944103c00400703c0c540501140403100d112a540584103590041d87c0380107014500480841d815031a05014900c0300c0f44003c820001440e01400911446030103040124020b00302c05c8030f8000170800c1e40c60703c1c422007084c201d0311090381ca07002041c50003400090828208404c00764012541881c030303030200181055611001d8031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 439816951 1250 439815701 439815703
    0x7090e1e06060d0e07080c0a030b0a020a1107032d0f03050a1b1217010807050613050415091b27050a0f081504030c02091018020304110301110417 64
    0xc40d0780c0300103032040c080311101d11401385d07503625584240d0400e8001c190a180b1a032406c840c0403c1100d8100d1062581a2940410500294091070032942480f0300310f5100e507040c41080c055040118000e000c0007515403402d640304a84003101154000c5400074421901002070980140760310055010719025850318410340065500b041076000d102d01007940c80903440e081220300110b8031101d14941c1c1e201d41d03081c094600f150000110a010701075050700100018000750800901604810348600402551240e591000c00c0841e9a5240c643c41740601e01d0005020800c29402100c51399500008040403006201d100101000c1007280c100c148180340c416100320321005c2040d00c80250000908104000341e0360843c52032803017214070801c007081c0942d0a0b100585210309044920075a0103403544c0d1185030b6aa82040b024200042941d0700b1292070080200b09190b00404081150400030310050341c0b420942801e140740044802294444da0500342c00da0f04441036401034030704980484036001401201c0400b0700d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 439818201 1250 439816951 439816957
    0x30f0603050312060a051c02031228050f0406020c1f0905091b0c030d060608100e04050f06090109171e1309050c091f0503150d050a0b07090e1e0606 65
    0x7441c0c3c0109680c2c2500d032601e06994502c0c80c554401c07021122141e2020302b404403207009034640e4590491080d9000d0184107110410040200312a1920503d086161405000301d07800c16000a80140d0011814041c241440d86c00c4c1500044103140700100b44d04504c5d0020040007041c000c071030059460b0000701e50764408241c101c0e149402001e0040d0307241c0c400da0034121f03900d421941e03200f01041c1c109400001c05902541c1158000c20b4107500302d40d001170515405181d03e20740075000b140e151090075400304000b20180001c60142c40690004909641c6900f084604503c1c421141d98401d44c0c2005000c4400d820350580009088480c00e605850340f40d0000239141c0d1046036480b030f9020324100300804c60307051441401810341e0002221031080d441040311101c01d04000740801c02001c558108081180f030600740d42c170001e02c1c81c2b004080c03c84e4000d05a540070f062058042c0101c030707810030020a00400d1604012054058141c0c2801c80d42980342c02d0084940e91140b0441c0c40310f62036100ca0100d261600c8100032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 439819451 1250 439818201 439818209
    0x232b0e03100203042f010c020d330e0303010503030a11030f0d091e02030a062d020408013c1d0703062304020427080a030f0603050312060a 61
    0x210f450b0300d0941000c00c2640301192001d00d48698a00748000103001c1e01c4ca400b00c000d2410781d2482601c4000d0340c28028002540340302980e034540c001c2c10450030f112260124101e818500712126642d2420600c410301620401d41260749990020700040c802d944000099503030701801840c25503104c030945070001e403c52181c1c4250001c4628005080c000055182e000026000c1c8241000000600708823482c6418144031807000f58103821284017000402d01d25001840360f2204e03540b24601810200600c103815252070700c0080312007a0040360030000300e082071040144002184040410010074403030901c2c019401c0d900c08084406200310001c00080c0700d540408006500c0001c1180800a80c030708642c1e03610344912048034200e041141083d60300c2c0301d9003030864000051000705500c0e0744071f0f64200001b0301481c0f10707441c6c1e90868005c001c62410a5035942c045800b4007035003000d035a0300421980107080e5040311405400c4d16003002c50400c0010300000031180c120a0144a0000a855400001da40c5001d6980 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 439820701 1250 439819451 439819483
    0x7080a030203010303120b06030f0402030304080a03020a060f090201140703030b060d0b03010e011104260a0b07090f030309090c090305011a0307050d080a0f020a232b0e03 75
    0x5005000103030103500460689003e500c0b19140c5806101001055a003180700d401d07000704003031000c40d01c0003201041d800d0308103100034162800c00b034445500c185464120301c4140d00681c03010711024140117251117484e0b200415100c05100311505a00082c0600380720103c5640300d2100010450181480b0390303c0803064510042038555034031852002d1001601007491001c0c4294607011a4a4008005104060241d51040c0540c9d0400e49404210401002802c4410108040341e044000c4041418001d18507043d01c56821704041d030418a0000300341c22202d0300050680780c00098180003298001420808864480001091174402840100c4048286600040007507080c150341007040c1003401c06c00a2030303100c00d0b402c8441c895a04e070200104110380c400050721001b0108449546188141100d550242a40c0101c9110802903a1204000c01640c403215202049040d624190550305208000b1280e41620305a24001280f02805416890b880ca1342c3d001d000078220855030710344050100e0524403203071007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 439821951 1250 439820701 439820707
    0xf130905040309051f1b080c010c050c070b03010806041e02220b060301050d1103071205160915090b011107030c0e0c0f071104020d0f0608010507020f061b0708 70
    0x100d4007916203074050080d83d00c61070320408550341900c0c19011038081c0c0c1c881a46c44058109066483d114010319841c0140d656079020800545001c1c000d004092445000c5d9840030740c0d99050030710135801c2c10600c1c1c2003002520b20410040044038000104a80c101d0340009804100070141f0380803c00c1d000030884000d4000343c07500408075000e41643c0035900c100c6064001803010b0110a010841244024051a60320070000300295000c50800760034411030001c0501159a201d8a0b00c000440911511f101121071358818251090786002c2c075a42c03d230041110103028011240031064103003915146014240c409a070325a040e2040740c4c0b0403c1c04810006c0380b14256034000e0703200d08000c180081d103802400d00350b48914001c1031303104030301a0880e8001d581d54451641001040c2d6155003a46052041c6554010380a0115420303003501c40c8103008404944c174034000ba4907454208640c5c25900020482d40641d00007103a48245500c0100300e4951140d0a03520344210101c410310303248000c0c050441c000d801e141000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 439823201 1250 439821951 439821953
    0x30415080f06011809090311010606020c0919020c0318010e0603060f1201060b1201081e031215060c0a0507060908031803011107050d02060a050c1b070e131a04080f13090504 76
    0xc00c02300021300110710020702c48a07484031000ea0755850f0b240007040d00302c00b101c0c0000e1707100c01c0042c4801c5030f100c01d510720151070b140d2495503062454001c0030061541c0c41c000303003c3d0800740d80c000402401e0300e0030544409080d4945040050b54022070f00e81c80c2ca0103400807400d0407880001c02e5003e6000340200d015010b8540c4959070729079001100901a2950030711400000e0b04686400d642d8111140381070070015450711048201e01e0143c07401c05031480494040040320b024160340d400d8050300e1520340680040ca15008541082d81c039210055110800b405107001c0107100000012040310800d900744026800e099800001107801040e000011000c044004a04a0100000416800b03c10407050342103c4140d00c81c49682d5044a10035500d451000303000b0030903480e14240806010350780549a1094900c01e60703695111038501c440c104c0e11034901011102048040140141d01908030340898075201c00ea500e40303503039440c034948070794036121401d0035000c1549040107040e8030960014003d041000d010760300302 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 439824451 1250 439823201 439823207
    0xb13020417011a0906060c07080706030c020c0f0f060a0e0405040506040203120306010e010c030203070f080a03060605090f0d021903060c0305090a020a03080d140108030415080f060118090903 84
    0x41607500350071035003010800d6904004598040d280054014040c3c0401e0300c506040114503445402d58184a010340762002810413400d00007440103040c540c4000c02c0d01c1001003802410050f518200d1446036040c15407082076612110444030744c40e8400d0390302e03030f0750340c122800241c50450308000c1840d0300c41d0515041004000003c107403140214401c1d802c440c190210320f01b1b0b54409010880f189800038905040c0030200350300c1001c044036058001c0c0150303854040103480c0d028481180700000c2c0d800000c0010600d090a0f850720a4000411451a004d4204280440051581c03140c0b10910303442140021480300540d47c1d1100071044145641005c2c910040e500e241190142400f01181e10100f460480007594003040400c002c61019801005c0e01000d80c11175840c800e1035008103000340d0345c0342d69404010045181d0b4441d4503020f001108001d40d00c41c0d00e80b11010b041c0d03141141d600703020445c0000510814400d4040c08a030081d00900b4001c60f42031048122425071072940e0301002442e424034414a05041d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 439825701 1250 439824451 439824479
    0xe070f080105010806041502030c04090524120312071b0303060509010b0313151b021b10050d0507020a1703060103060e3d180c03050c030a0b130204 65
    0x448002440142c0c1d88903080754445e0300842c1c02902003041101400030302c06241c2c2c01554404406078015007450344030705a0104445080300c6005920195000240c0b001c02c43c40c1c03841041e0881120302160091402c103003141c90b4010704216401d03209131000402c079024094500c8030012009421110207100c00341c28024040d100b03c1c0300345802000b101001188988600c400c40c0c0c800c504000c501c2c42c5032400759941c2103031030184c2203056501603554640c1d00c0024a00e03840000e80000350740d00a01420802e04d210088542214202d248654103840c041a40b02d40c00c0020380d8000018180002082d43c0c940c0001e03401d2904c92403006100000140d41b003054180d82c40003441c010042a602084255151544070f400700205440700144c0c0034442c2d50703145003070368a181030b00081d858660000201c41e540c65480050414642c2148886a503103481000c4d540c90540b28a6041413040d260034031072400d090440c0075040c0b0001d01055007564407403104424946860b0002c11007420000411903840d65201e0320110410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 439826951 1250 439825701 439825709
    0xc060d0f110304051b0a031106132303010e03210430080603010c23040906080717070e0105100302070b0903030108070b04080d030209150a0e10030e06011502010e070f 73
    0x950741026014142c14400c240c6e1003a250b0000340c100c1501007284c00c00c40560000340300400099800c0401146e959800c02c80c0301e6420b800482c10b119815840782c1010300b0b5502d509070700c2d440d40d0310502c044840b50440142414440a5221003840035446604103c00d4441c6208002d5682c005111a11349181c44512210700e200012691110071513103646042500b41d4085c29614070000e05841e84012200070303038800018101150115031031402c0d9903001c2e2281603880981c044040d9030000a02004604160100d0866465404024081d22270510703110901921041c0034103409615418061010540254100c6820300d42003008403843c0c0ca030105081d0342d80d42c824041e000003400f4078140040c4400500e000e40341a031300108040d000003240c1d03e03c120008c0d0041400550b1042c103103240c0c181c0100c5001c1c002d0500d81030643d64001c1406901050088903031880c04090209480d021001d40346072408244141954000d06030500c07c203a1030300c8100d001d081054004280c602a5000025020901d201090121 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 439828201 1250 439826951 439826983
    0x2030702040518150606070204090c08070b040b040e0c070515090d090317030a0209090712050615030402040c030626060708060a0308090a09091505090c060d0f11030405 74
    0x40d580c65034405100584400400f0b016405091185800051808090740c03140b8007404160429299030002000c0d50510b12050300c101d00030f0707803003800144e030f09100c502c01a01c1c00e80c10451400f850022400302078403840c824000b804100c000810441524881140d035500d41004c203c810103002c04c064500f80380016141042280310305004025400c1c004e017100c0c012681c00540c0044604140440703105c0c0c940c0014000954240c1c01c00000c0c255039a944441402081c450356100c043c100351601c00802c43d140075040701c2c811401950400603038800601105da000b60f06460110742c42514003415005440c0070f41202c9402ea210342c0d00c1da107100c0711079440504482034038130450b052510755200680b02e01c5020303100550403841c03006003840030501342801031605400241c400050160341d8641c0e80c0880e14800f00845000c200700200032120354060140c2c0d80c1000c640c40c0a0483d910800000601b544500f00c003c5034a00d40302c1c00440362000342030b4804d10300038004040c2c107680c070301d440c3c81c1c0103440b81c010b100c00d5003903 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 439829451 1250 439828201 439828211
    0x10509040f0b1311070b04050c0904030206070806010516030c060905010c0e1903020d021908013209101109040f0c0908010506180408090d06151208030103020613080604030203070204 80
    0x3d01c10901908404005480b130652800381641c6403981e400c0310040c000e586a1140c10008000b07a110f02004621441c0258007030b1800742400e9800404130707a0064070302e90400200384002405035082004070481d199041c00d2042010b1880d20b40f0001800703c48401030469403030200840b0015070031a0060407110802c440000c242c210429002c2c0044025000280d009150300c040100103082081e00c400922004082800c05640c1c0d4109040c01d43d608590082205540840c20100c80408002810404a800b0010b2030356480c1032032400f076481000020740b2100940702d420f050312004079003045a28840c0048c00034055104146000c0780a440040070340e0700080d2a50704001a00b02c410f108250056000801d90154407001d08182040340c90090400d81e810041048482035594803d45900001842202e000c1106a0210100d864615156011011100c0402000000502510116410b4a604075401d0791641003004982c041440e4540161603e03105400c1030005040c3c001015042c401c4c401c56060107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 439830701 1250 439829451 439829479
    0x1d0a08010c20060609060d080408010c1e17100e04050a030905031c05070c1d1f06140c070e0124030e1b03010e0d080a0b0901030804060e010509040f0b 66
    0x10035503991114041850700300030f020801a15022405130b030445001402d10140d010070703031a24812540941d10000c01d5a6562000d10340443e040307a04680703040c0044080c514044040d1b40058012010304000c40400c99800000444c4003c05031024005014415455013141ca0a03142581c0c0e2102108416804106d24000004040c40e001400302180f240f2000c2c564841a0060010b44064100d42411240300000c000301142d0307500740b8114034500987d40304440d141424016a02201d4190159032103500e80000841441000e0304402171500c0b01c41c01250982c0e0361803150842c0c1d400d24074a5040b07144007250800001400f03103022140484080d0004c900310704000070310103013a41195001522814030b5000650340c010289404035000391150000740c00454003003282c503d041c0c240b2010b000b0785008526443e0078403400b152140b02d02c16884074242c40100065045480d04405402180b042e0000c20030000e01020146e4030a6060310420140a00103111040c070700b000079400351040e084118001c07205801410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 439831951 1250 439830701 439830737
    0x4030513030b180718050411040f0920010f1413180b1c140a120203071407121b0b0409140708010b0d0b03010b0603090c18040c061d0a08010c 62
    0x1d8100d484c0350785e075100c008911144070f90241400070b1064402a404003112806600c441c041c0d4601c19103501400107002c2c000d4074121a8003a00040740c03079480c1316a180446c1590f40c02c01740401c06007645060244044c1c440440140c130342d12595406c105142c50000c0002109016881c40c0c80031a291088140070300b40107601032184050030030f03100480100b00c044100d0082608600021810310001c002d0751560403441c0c0792505098000034008005030f00c00200d9009000400c0c40e1a0148502c030409094618a052054403400d640140e0140c50280c584607401c54a5150183c0c0c5001050b030300401c42d40710745d940c4048030004d04881c3c888620b012128800030300c030305100f003443c0c034140c60000d5003041c00e20065024003001091070403031840e019035803220700750801d03030703030400070714071400081006040d0b04844c2e009001015486000010002c1058001d0100042220100b1400e483c2c0c149401019443c07104105a60301000d44d2440c0d4103d14000380108150034190400700322841d00751950305195140c0103000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 439833201 1250 439831951 439831963
    0x30903150e0304090b01052205040e010204050303030f090a140c0111030a0207090b04110304060603060b09222102010e0613020a05040911060d06060e100806010804030513030b18 78
    0x3801c41c680003040180075840e15984038004810f01803502501300f9000309980c4640d0300c0b110074003c4c4094040442005580707407034061380781086900310096040914150200756240406881c25510411000000b2080c1034208107035034400c0c7c0c00245245500101181540d110b00c10029844e00041c8140c1405a84030070000444c0c01d0700c0740f50740c0141281490f04800d074000703005080715254401c0d00c515100841707603001800307140980e001703001c000b0748603107036203826012a540ca600c1030b802141030f01c0030401c502c0d158215181031100010701190013242580380010100d040410303e15500d4041041c0742e41030560551104c454070071104101c4080d501c58082c003403207a2041100003980492204000d20082c01c00d90000e118452243d403065250010f0b100008400303403c00c103112518640c0d00d0800b000f01c29801040e50410040954250402c20308142c001425484001c101c2d60501c110a0b002c00c0416110340300f2110410529a0711b075010680b24508a868120251401110103c0791405456404404a1a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 439834451 1250 439833201 439833221
    0xa170a0603021c030306090204060302090a0e010605070b0402060d050108060a0c0306080c06130f080f240a0203180f010f140f04120915081f050604090f0e01020703090315 75
    0x2100c1c030004803820b9240f002d2410b1540c2202007544420001034112a2030010740301825003510302580307030301000b0203006030301d80c8542c081c502c2e40e10714800400059411600311000d9513000140004503079a103001080051148020305038665280a0001407a01404540940107803203980061103000300462088041d5010303030080100d03940182c1d508402d2441c02c00300070b18001c10501c09802d07440b5640c18000d1260382d2143c1c490f1006800c5803608561043c81480040c910901100c1144165040d00c01240c030441c00090603c60465800004542e031850110302424031180020100d44c0e01c0031840c80307420301800121000c40502c60801805d003140e8040110418401c0c9456005085180e5a680380d15040c0314105c3d546006000c00c410011860b00c805000c0e04d21070010580703441100e400c12900038281c90a5016501004245504017440540d4a501c01c54041303e08a0001250720b41208040348010040c0d05004040c0c4d610029441081640115025007168040c0b011103001d081449640426581001d50f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 439835701 1250 439834451 439834459
    0x9042d0b06120705040e03070308010b271807030b0f01020105012d0e01030c0314010c0f111501080604021002060f012c0f0f07050708070206031b0a170a060302 70
    0x1c045080080c402e20402610100f142c2d001c0741e80340080b80c04c862021507001000d4100265100074075800c00d0b0003500528078414a030b40b0704580c4e0354080031080720548003446038600070000200140e0301c6040342160002070b001c0c1215103043c01e050280003084440c1036580030790400d20f491445d540c010300c0fa45040b642102e20a654014010b660742c5603408500e070032407904010f00c81e00810358140c401d40c4140a0f44c0704216100c241819800e0049515000081d2801c05030304041d003800c001540b11002552103840b40c100101101114100182449410780400002900e100000141000e002815500a81c029144140464034010040343c071450112640180705080000401040c0400303a002d0503454643c0d07590a5000684450204d8410301c203803820724005400400340040c6100100045400410a0422915110099490007030354050326101a00c100c5c00800040c2810b880070b480b4542501021070700c141c1e0b510705518040c12840081e034258490450303a50014016500904c1800e090f00d80041c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 439836951 1250 439835701 439835723
    0xb1204060c0e0303030f0402041805010203060103050a0b1320070c090509070b030f1b070b0f18070311040e03040e0906150a05040c1715150711100e09042d 68
    0x8110881c14000c042c00880c0c1180e681c94ae200344d840c0034500507521a6119500150303803410030307800040c03d942d0007420314500c0c10300e040903001c9180c0e01d000b10b030901101e4401c404500c640d1420001158040c1500000c140488000b40c0c036020401c045401406440100408200c10f0301c4101c05a540c5200340c5c020111b00001c00c1000c54030740d4034000e00746640203036403603443d61000400400104081e045400100d40900c01070084c01a501e683c20034642d40120b1030801c554858035000e4036699100d85a100c0a070203881d0451fa18201500c0310b4000c03d0000e42d0900480b42c1c3c403079503210070500b280421a107031110760003088041440540888201c040c0c0c4040206403100360303400d140800005010030500301050003440300419010800450005104181196030440d03005030000030b12014503030041004000c0d444c2002140001003002c7c81443e103202042d0ba40d180c40700c0c000310060b02e240382001e80031341d4000400e404020421441d00071700c0d0701e0318000a44c01c0c1c40c0120035508011a07118a240d00038010001c02c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 439838201 1250 439836951 439836961
    0x1b0c17031005060d021c050a05070c0201020d050c010605030f0a140f070e19050f0a0605010c0510090c030f12030b010509011202031329063102040b1204060c0e030303 73
    0x70010304250a134081006103841c12500c44403804886584550032220703110801c00242d100d0301d10803190f04c40554100250941c201d980000c2d20360082c040c1d03c4041c401d000c0742c5844407500c00d622490140c00301900700c03072490b039114029076511500c01c6002ca40301403246441c81c1007142c0116411080040030790040002d1800c01302e0200051000500b0780c00483c01c240c03003c032442d004030f0240b540a91007103240b00c8501d0900e800c520040c0d40190300824140b0251000c105d0008200003000184681096800611400c0c1c030319108006a2842c1c3c40035080b0596490403070309011180e001130101c80c2c015203041144108140c0150390038098280f440b030100b8031104460781000000e40003560f000c2080410000d44040a0f038800ca407110b5080344410400f040c20705c039030102400d5070203003d0308880211100c204540007200110000100255202042c01540580c801c000c0c101e601544c0103440c2c0060910344880240210a000f810111019188641408071003200c1601a00d825011185c0180c0034618558131 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 439839451 1250 439838201 439838209
    0xe010807050c010906090b1e01030803090109081b07170607110319050712090806180a0f030c05071e05061e0c15060301110d0e011b0c17031005 63
    0x8003108107108080012140840c1d080c890300005521510780020440f240b810020103004004100b001843c7c60300300750540a4060040b0541140d0b44079990079a02c1d0b40c0c262001c1d000d001800340051420602082942071410441803020500901078201e500c1aa62032030b1440004c0700481c10811240c2003030f000704240038880c01081c1c40520f80c1804581c640444100549050110b510703452000500c0401c43d1010000100800b5194000703619142c201942440540d68465501919011914901c804022107052080c041d98010341d4003d0b9200d0207019072400d0240003002840c2003200d60740280000816218015603003141108030104480c100c03103040405000056026a0080901703240c05040301c050340160f20010040713080c10101600f441d42441c400740d212040f019143c584264141450701d001d417640070302a00d40d4000c0c003c40c0800d2442d580c8042600400c0d81c2c0e00c400c1d042c07050001c10001610f80200c0a079207118812000704c403125180044281f11808240c6d00350040712000306003004903281c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 439840701 1250 439839451 439839467
    0x30f07020604171b03160303150605190210050c0918100909020a0e0405031c0e030a0e0f09090d11010e06040f05250302040c050c1e0102040513050609060a060e01 71
    0x203c007603044000c0400440000e80b464102141503941c400424a0341301c1055414003a0800000d271401c01e01301c42e1814500701030b010707000b500b078011012201d03402c80d07240c01807080003113001c2100b0302d80303003003000307050111a804480d485444014001e000600c07014801150a50340c3c248280f00715004040520300f00342c4030b000a0240035105076407040b00d0070301c08185d031200405034a0056100b0001917555040040c1100903912003d512400024604000b4104415011085800c410480d1500595030ba5550300051a40414040c02c15007010880b4100604604002a6401c003660542c99200c050001240d420f401c1e1410a1f10404844e0880320125001455241007455900d01ca8415a04d910b5080143c0300c580040c103041483c07451101041c201b080d410300d44106182c0c81218a030031494a1500303400265036150340c00e4210030903031302103801900c0c8540c01e46c1500c0142c4070040c18526580803411420001d4501511080d21810b04003000c243c240c43c2001d400800c03203e0340c0e1600c4076105003880064401c10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 439841951 1250 439840701 439840717
    0xd06032108040f150f021c05070804050607030f060b0703020d02060c1602090a0b060a020d09060f080f041502070305070c09020301030b010b070813030f0c09050105060d090606090908030f0702060417 87
    0x3680385d95008000071000d00150070b03c0603c40304c4d00c4921042e04211441501c0300a002d0f9400cac001413405110116402244d00b40c0e0000e07a0307050110f41c49140d50040b100074145a801100000f80101b116000c065001c10440c0401610b40c0c03c80d1281e4640001c008001d04c5031413509040042c0383c400420041c00c104640e10b44c04a0130400018080d0a0100415942c0d404020243c00680000401c107401c6900411030402420720351038040ca8042000c44080c00c03592003d00510040c4000704000390401054039600381d1480c007284d80664a4807007519014010f03422100089854401c4a1004a14581c5910a0b24102c980280d9a140c1343d9103420310003a80c41c1e04c06481594103034810006103006801240e03016000b135115600c0c90340708401d81c0c24614241021504021a000d007010010070540d91a0b0302907a298003094003000600380702ca454040d00a040642c8030f01d036110700740741300442030140316405180700300c0d40311008200076600c060b0201d0b11154201d50040c07004080380e240181c0d6041d8a0040c2c1107070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 439843201 1250 439841951 439841993
    0xa080711030d090602041707060921110d0c08070e090102090901030f11100507020310050115051606140105031e0307030302090f04050408090f03210309030d06032108040f 75
    0x84e1640120605038050540c0d2401d25031012300c04201d000c0e406421140208103512401c4090703d40f04083c40ca5540180b04050001c0e1009100c28030169211644002c007150f0195140c480f181c0c0d160707261511002030707200702a0740c02c05840000d014440c0c10f0088820124008000300181c0c1c0c00e40d60b8503042a0114607059810080300307403070301d00d40d0307201e85040e04490042c076144e20340c072040903104162070000203444545480382072034010400d040943c0142143c5c94440d007070807901c4080382c1c0000343e8040f03010b0383c002d41036030700340701188100e5500c90700118145c403015000e0358500070849050b0803007401035031000111a4420403204c0023081c402d81c0606084d040c003c0044040381c0b4a90001025a207050345c080e28400d80c0010b032030f000c0740f40400707034403448030019006400300854000039041d00d03401c0d100181010840000004100c40418411240858900d600420015882e4204686e454440e1400f103800b402d8200030b07012040d0b0003180010b2055a10094031002c5100980e00d04161030742500d00e200740 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 439844451 1250 439843201 439843207
    0x30717040b0d0207020f0f03060115030209041b020d140d090809091509010801060e0406092a0501080114031f02160308040c05090f0a050405210a080711030d090602 72
    0x201007500801009000d00c402005a214612401044500692040c950b1712480c010a2000b0180c4c0b00802c00b0f0307045440041c0ca01c208907100c0d006c258007030701c01c0c03a159580c07051401d0b904030300714060301c2d00410210716294215041e00e00210400d80c0e404c0c5108a400e5000134041c003682c0030a00f40740d003140d00c056204007001801c1c440c410001c900090b0003500c4c0c05104000c0d240c0004110b0803c00781c5a401455103500030722110340741003410f01d030300c1101a0020b4511600e6245c0c0500748540c0044003044407480c4000111000441148504004018001d15000581a00c00001d039000d00912050312040300402a043d00c200c034403c2e002c0a1040c5492000c900e603008c3c054180c4404500000204843c065110b001041c40c03d490600b1440859811291080d451603080c0203100e02c4514040d0352150b020b4600050a4945040031032510905e02ca1580607e8400180c03080051103043c05007603a41355584901003140c40e4480c02781c1e01054000d001c00c03142d50043c0720001e203400c8aa00302c201c48501980006203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 439845701 1250 439844451 439844459
    0x20060c2104030f200f010e040203100f0308031914010b0d09060c050901120606050405210a0818010306051f050f04060905030d09060e0922030801080f030c03071704 72
    0x5070f001d0008800f542c078112180300300704a0781c80c4c114aa402446084030240c01d001090800600b10b01407030460640204e9000c000980c00386c8001080001a042c114882e003429544c0f842c1c614a244d004903007910700c01102e14400c0c2c80078501d074060b0b106440f21f00020165960b003414040c100503003100940740e101c6074a801a4a01180d514410040c044880356500e91307a400e0700c0e000140851140d84c03911400ba503c1d02d00104641984801a0340c2504c00c121868071303000240b42e201012801500101c0d05640c0103240c690f0b01044090001061000041c03900011101f03042c90065040b0f0348a442003d8201d0540f854202c07c4c09081012076600b0141810880d0030300e41c4d0082090041c0c1c1158000c032010a40c00b0805200070310b020880d20340100098078085071134a08090004200342c24585140d401020300f50b02040d05580d940079079010586020500d401148007034200200012003e126401840c095000000f0f4051004404c0750311148070f05000b23618001040d80c420313440c0444603c41070180c07541480080307 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 439846951 1250 439845701 439845713
    0x2031204110a0605040308160c0f090603030905030303040b0610020f1f290402070213020706140709060804120e03060f150904111210020720060c210403 67
    0x5000e58001e00c01d6140118012042c040e80050603002001808001d000c1040094003000071210b106101d07000948544d606450084c00614140d0402c08803c03903c10000f0605682940c00141120f000c0d90f140509d1583d143c05140d06c9101c1620040c1504418100007443c03400c110003041e100b0510791048078042e1500341413003828508500609032070b0500520310081004528010410803001d480c03201002072841524411082d89505142d034050b5030080340309c506554170a114550031a0301400c0540d0358612525141000380719605043e40300c00e04400100c0c2c01188201c008005403880c584131541981c55903100d044814019465039030030010000d107030103041d8030305100c800d0040c2540780810707505041110b4503044410f211440c0324080c9910070300300400314404500c0380c060420181c44c1e40c42c440b446050150701b020070020808040c54000100001049040321343d034000740100c2c1e40301500d0a5000b801700710440c03058062403045a84005a461038062a14060b520485a03404201e0701d0180c0e40d603110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 439848201 1250 439846951 439846987
    0xd030e0a03080405090a0509060411131803030c0201020c030714210d0c031b0c111c020a05041515050c100204050907080601050f09030f0a060903120908190203 70
    0xb00d5000c1e00200302001340e82004040311380c009401c51014041c503d44020115500c00004001070003903d030b400c41e03140d03441d20303400500f001030b05244500b400504440d61043c80031000000046002a00d01540421414070620034ad0b820000a880918601141519890040d03c1c4020020510740114140c1e2800c03070614160552801d0341d00c03902d458039030800c840c0c6541140c0004085005050030507654140340385d10602005c840000c1810444201d840900f85200401d994403c010703044045200040c81c1810807401e92070600d0300c21216055501c1c0c40e03070240b10640300c0310b40f28115041c0c402c034014071140c0b8024201ea0004440303407401d079040501c1e00c10007600c0c2140340e02c5140c110030b81c0058288800e041c83c803a000d9003c0690b0038420071a04200300002d1031440381c0c1011884981e80803840ca001c5a509205100300c403000345003221743d403000905105004105800085020640040341c2e10601412401400002a00118401e080a00d2542a807a100b045c083c00e040850000f0400e420031502407440c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 439849451 1250 439848201 439848203
    0x509070807120b0f13090b1f170705010f11060c09040f0218120106120501060620070509060a1d09010b0f0306040f02010e0603070810150e0d030e0a03 66
    0xd41405081c11200500b428488000c21100c02d0704203200c4074a80d460300c01c1c0110101c242614401c55410741c0250701401400380d20320040009070500306010f501c54000707401c4844115408401d103006650b0380c2c2003807042c600480806030142c04c2030500f085039600548068900000a0402000b801360365281603040440482d0350503110803000c07520202e0360a00c1e00c0750700400ca10982085107009941084a128080f40c0504207110700c000601d01802c0c9482900300c00020800600b403050828050328080740a00114020348000512000301024100c003000c264242c541450b030007a00700341d420310b4140044410b004207696003000e44010000b5988001c9516000d0003640c1562a5005060560319070b4213503111500868401d04181440e03004036540450165001540315003400343c2a016440140d03000940032100c15070121011080110700c82e00015030b40c0c882c0001007001d1110585900c1c00051900044c2d200341d0014600201d901010305104400c0c2200321301a0415840789204400001c150003034a400c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 439850701 1250 439849451 439849457
    0xa02070b0a06090b060306091305121209160315110f0408010209190f120f0503070c03140604030507060209030705030d0f020c06180907050c150f06030607120b0a050907 74
    0x80c00c102c80f4805100e19045200d080f220a40340d400d1920010712440d001a2080004807a080401d0080180401c407000b07100d0103d880c03981d2030b6924541300c0e40e4560340c121139100780c0c2c4c05040415040713488080d0f003803029280c2c4290a180700303001ca60f68440c003c010701c0c40781c0358030140304000320601110b50802600c000c1000c40005030792000c982c4244030540404200201820a4410080c080140a01c01050690300a440f182c02200302030304126505150290b00035045010009401c01400340101d031440c180c0340909182004031004180a07640c600044501030b0009400703000780000038502c0e070018011220001e00311541961035000003800c04c40540c04000200f01c40f58105601e036074042c4808c41480408541e90350424541d590110708010810190612680380c076400200200d000c2e000740c9180e008240d044406c062030100c40003401c181c05981c00c6003086210f40000e005440d0001d60700d44141ca1a50b50544040e0242605401406028518651105198001140070786502c0d035070074840d05040d6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 439851951 1250 439850701 439850711
    0x50c011a040c02010608030a0c06150f0f08070302090c090d02131d061311060f0d021b0303150906030a0203010e03040603060b0f07020907030905010903020a020108070e010801030b0a02070b0a 84
    0x8000c100032a03190020b003800796414004200102d0402005072014407001d41001945400c0c54603094008105041c0910740c0500d14981c08282d00000200a50a445400341421151a243d000341c660f90510f40c4002584544050006815540c1302c0d4080d107510a0041e00c183c0810945600048003a9030720149060303001d0340d440308800224000f1585510420300e003405040f8500f018080040001085240039010026001c6460390b9a19260201c0e0b40080314000c1c0c82e03403030340710680810303019600903152141d111300890301d05694108003000300ca004221030340416841100550a1000c001c0e401404035034540030711005413000da1028042c0b154041c1032140615541c41c10b01e8030150885200d900001803198041c04280883d101c0c0304101c812480d0100c0d281741c02c960718800300b140030706206070004015500b411400c03020107800042d60003603640300f6202d8644541d240c1ea42200d000038404095400550044010008208017000054019020034400752500b5896203a042e0041c500791080f1507515662 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 439853201 1250 439851951 439852001
    0xf0c080109210f02030706200a0f09050105041202040e030d11120702060907030303050a0f1439030405030c01150f1a18030c03191401050405120307050c01 68
    0x10000310b81a140908202c85800b840c0b4800a40e00d00510000410241d0b031121946041240c0490a403d00d0040031006075495001c3e0200400c1080c03448403c0d00030800182000c20030358050410396098540110140c0313500c580603000c00024046d103c1a42c080b40c00100200c80a42c8401d0207400c2d08441c189c410513139608030300ca004900c500340040c01034003107400600920660701c001041000c100d07a018540880c45442e10a40390b0700802e501c034070b04500c091912100c480c40c4072041120520940440b541000001c442e001c400600202200d03a204e540e000e03807512106e4460601003d580c1240c0a0780c2140d041120b009052803c507940a544051114204001085109180e05405020307290310356480c00c0150345400400c0e02c2e170068041c180070014024070143c603291010000d4012811008049800d00152500c146441411001c800e44034000302d001c40072550b28050040d0380c09283e0100c0109202e100100f520314140d00301810900401104100032803e0360300074051007005040405440003200d840f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 439854451 1250 439853201 439853243
    0x2040b040e010923100b04170c040c09120318121401090201120b0f03061008120702030c0409020d060908030106271505040305010e07050a1d01030f0c080109 69
    0x50384041d0b042402d03c920341c01921012007251090b00e40400400b582034403043c1280300701c0c5d800c58000d8001503e02150014408440c0034900e80303110641010b0b51168050603081c48140c0348211080c1000c11800c0b41d04006081c54031440c030507103a000b803810000c42d0504901200072100c0c1588070200700301081411106104c0f000f02e20301c141c520000020007510300c03c0d40c006021103050344d26180b6116900c0c84040742c60749440c00000640c142c02416180d80d07140a0040c6d6900d0f1076640684100c2d03225000e00c10b0803116042d000c440025070020020100c0e50720342d80402014040001c0300f00d070440b90740a100000a2154010044414401c2c42c2664503036043c00d00003009030038541c080b1440e80c0b0b4030300701401e84104845c0c00c801c10f40f802e42944c000240c240c00c5090380d17603205991005110f58a84522440c1039000031581c4000d8907000c40c2d48841d46503884d404041c4006043c5a00c003600c80040c80100001264040607188013449800c804a02650b565922400c5801402081d28104036100000903000d034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 439855701 1250 439854451 439854479
    0x1009080105180f160b0721020604060c051e030a11180108070c0b15150c0a1e050601063f05060a0f0e09010207120f021b0f0402071502040b04 62
    0x901c500804254482d500e0b0241c0c5680d0500c40c02c208017100184c01c40c00c1c400d280300380910010007000b43c00c4000c0c051020003955494121415955a072a14107100e540720320a404880c1441e0002c9c41a45103014000920b00155001034000f51480d60f58220050070101500d016210445021140b4004482010000350440c40014100303001c1241c80c90050b00080c103400e510542085084000380701d48400c40c4080760183c03801c40751405402c000030841c80391254000680c1640a403265051022560b140800e80382c45000c03d840003001500400d00600005108010510001d90b108200f08850003501041174144210107000c044e042c0c0e0001e01e81040300c000c3d4068590010000d50f05000c082c1e2808800c050051024020a86240032110124000d0f034002d4040c0c400c2c8640210b002e00c0c43d2100c219000d003415198a0309a00540503008000d80c2a5441d20200000c1e100043c0089401007021001c120096100d000102c1c1c80c249100201e6601c0c3c90b040c400b40020f0702c0010940c1f40d1300c9046ca040711000903 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 439856951 1250 439855701 439855723
    0x20105060301020a05070b070e0406090f0b0904050d08040503040905040804150c021509180c03040312061a070303020d060e060301240b0f04120605071e0905100908010518 75
    0x181c010011003440715885012201b00c542c1141c05002030342c03a199400c0383c070113035640f02d580d91041c1003980110304070515901c00681c0c404078804c00c200300402d44003071000e03020b401ca40c040c12540001d02104c0c625401518a9580242318405507840d0944445003801204c83c1a1000e580326003000c5011300040386501d046030030141090804c4040c0d003000361f00103440007010480d001c410110208210401761544040d03140d27002e04401b4001183e281c1801d54101581049505400241283d4041240c0020501c03800066030410100b403041d01e07000c03280250650303000e400708908041c1d00300070280140c0040d11076900030380f01a1a02601c4d134241b4004049c00d481c0d888042c0002029000342002c50310244e000c4020445200070020740d200d41c48440c00c00300078010780d804558018101c07002641003003195446140316031400d403900c0c00d5800401818a5104550784400130105450880600c59031405060000810803e80b400550064a401b100da081d214242c641445441ba0750ba41d020b0807100c2448648011 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 439858201 1250 439856951 439856953
    0x4030e090f01302006030c0406201b101404090513020a060f0305010e06100c0819020309030f0f07140d060203130218010614091207150201050603 64
    0x5041c2000d4426074107006209060b2000821041800b00e001d0207148500201d0700c104200c0301c4981103040c50101d001d002c0c000320341e14600521304075031180741c032000b43c074080c01a208045091504020055401c0c182071050a80303503c1805640030300682080014011603d400c100510415000c00b00b441140312448182e003040c0105940450b440345030107000c2d142212000034022500340c40d814804032036117480e10000b94100c01094400704071140c210b40d03080c0400407140c0d020004c60b1380c0c601816100a02c1075450315805004a0854501c240c400c84059803018080c00480c1e1600403035412000078901c2a00880c0c0160300040703904000340c5414841803a0340748251015000803030035080c034542c541050f03010320b0150901440c00300803192600080301340c5641d40540115528244a20144440c514400d012841542103030a0052613400144409040f14801d0701c640c03940e0310f40303080c88580582165401641012075020a69140300d0100a0307035005100f0030254580d000d00c0b142e0000d0030b51300c0c010401802 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 439859451 1250 439858201 439858219
    0x270a1d0c0f07021e0307150f020309130911100207050f0402121306020705070b030402041b020c060d0908030a14090a02030601060f030b10090906050324070c081204030e 74
    0x301c440380740101e44110b58122110203400f00500c981c001542482482540c0512030340001245280d40280c2d01400d0700f40a8985091008900e20201ea40b44140940590444103010444412102941046810a01c903826200c2e1303180540300070a020300340004500300107a009041c10091414012120240e50300140c17001c0d480c2c0520108082d1040402619a04c0252003108000c82841042e40c1556030443e0311070141c41d011640d94280050a03001a41c043e8441ea2401d4061903c00d4a18080b40c6000f9000380c019020b1041d400d8108030381074018030b6644464984841520300080c02c4600118855001c0107400201c0c2060061381c0187c6001c02031032061a079000c40c1c01072016a40c0028401c2c1144d600e45004c49815100640480151480142c05500a06a6555021031680144524050300c207090300c1008100e079030340c003091366411200301662220260780340c00d50b500c841c54100b5540e011115040203081c2c1400c603a50f000c42d035400080414003501c5c1c15410b12041552040c403c00030100102c03403a0030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 439860701 1250 439859451 439859467
    0xb040504120507031107030b0f06010c0309140a03061506140319110d09120809160504020d1b030504020a150816020c0a09050a0c0302040803270a1d0c 66
    0x50700c0040701410360920101080e450101071203098003000400b020000c1d01c06443d40c81c6002c8000200c00d8422429907a0040002801c40d480b07200a10101d9070559154409245005011a542500241242d070008240c0c5004030101e1280c0c020300340c02075034010440004514002c801000d40c2c07404111031130b0000080042c40385524002890140c0748460b8540094041503140c07010882e03219402d0202c0d0000c0c100390041091050904421181f2185e07525111916a03604a030140c445009030b44080d42000c6400c824085c0e41800e9002d01280d4484000000321a81114a000010301544142c1130000342c07600104000c606200c00c0380001403e213810383c1003100008440141c403400c0001e0082a000c2c2804403101c15003031003007082c5900c103a070240401102c0ca0701c9648601c09060200c50b55002c1728104034018007054464400c40b01103032050b002440c1003943c0440d11480c0c0000c1400c00300c1039242250540e07165039851085490050240148541d16680c0c42c00300811084001482003507455000c0c03110035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 439861951 1250 439860701 439860713
    0x20f0408120c0715120903020606031204080d0c0c0b0f042d060809010b061b1c02030a112104030b060915120709050f0603060f04020a090c021c02010b040b040504 71
    0x1100361500610302c00102030442c0313000c03100060204030070300c0618148079022003403640224000c0d015003000d800b5680b01b401000c2c4144030610907846901c081c0d6005028400d482845008140c0c66070b80b050260f911580e581d20340c241406d030001e80450034a602c0000c1d0070065184413041204c00605101d0b00310703c401e140300002c031404024920884013030029220000c0e224030002e51009558100040c400354032107450380e141c9018451078510141a6102e5081c070003805902010072a001c880c1150f00651905003a40c2c41200c00d1a840440700e13040340304010804409244680c009180300400a00c42500c0d80d10714104000308400240c462030042d60040284500b5014990008098000035a4414400000ca1f00800c1c41d051040e0300c04000345203000188900000030180321402440110121103007038998104104c40d41034103130b8000707511a21841082190f94100d4003e0004104107005940300110f4102450702181441c242040050755985081c0b0403d1600e8480c1b440b032b1880c256070400c01807925580714 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 439863201 1250 439861951 439861963
    0xd0507020105100f060207090902030a0c0906061106091b0d120c17091513030b040b010302040b091504051b031612090203030714010b1201050402101706010c0c0801020f0408120c 78
    0x4d03071001d0311007051202b5500c08008250072554003204e400b9240d541c0742d070220000c100900400c030000f40c000e812424140c0300051024010080c680140c43d040c000d0800651440f4081444aa04015450010380124212282c1500d8a000940f0b541511003140d14000b08041880c5180c0000302005000000881c2c48a9120301882d4640e03000b242c0d03039034951807e140d096081c1940001d0000310034408000402183d281e086049a00c00d84041c0108035490040050200084a0100c03c80c0c05140c5015003924007a04203a4004401d1404141074018404c03415242d42e0088400031184542e4501c480c0701c003540030070b0700381a0140c500801c00402c0040d0340000c0e181d21428202030300c0b004801d440c4030022031007903000c1c95105000901940380c401440603d14041d00c4200d8042e0701c9400c6404410f04054042c010803200c402d0000000c0f03d603990780c45d005507158080944262110b003560603021034413540034401010082280c051513521a4904401c0340d19003003418074a080c42074418005208551400030b91 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 439864451 1250 439863201 439863209
    0x90e04030f0212040902090a080303010e04030507020613030807050601080f0703230712140d08130f060f1a190e3303060f01030b0106140d0507020105100f060207 71
    0x1041d0040c07a4803001c900d001c41080d803800e5482400100018004210344c02010201400d58000314513a942d00d03409074483c0030904c25400d0302e00030701b00018002803007140101100ca01c0100224201030011221481c40f4070b031900101c80c0c1100006280081c01030400181340102250001003291b83e215030343c1151183c840f4403004040e2940c03010155800c44510380c2901d00201c0100c1214501a07407801030380076a0300c00140135188042441c81146d5040b07004202c15805a10b030780c41d600e0441c0c441c044910000700c80d110060740c1a502c0c140301100044d1150290304081c0c08240c0002c208000131810f001c200d10300640340e041c45650000e105c090302200d00e542c00303230880d10707010140708590b9a0b4032a1003d5001d420070b42c51518840c0e02d1180303070414011410400c1900c1054003100d0050b500c0329403090241d1401c1c0800b4200c030000d00010010144a800e08044c500540c043e01410308900128900685000f6a0f000000d07075103c0040141c201c2c2d141c0c1038040108204204d040c556031814401944504071402 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 439865701 1250 439864451 439864457
    0x7020d030b0109030b07020607090b09011b150906020c0d020102090f010c031e020d03112a011d0601141e04180213050702070503070303090506031005030a0305030a0c090e0403 77
    0x2510760030703800380f00306400554008503601c08900c3c0c010b00003905d1b480200c5400303001c20303511003001c034241c0401e20540d0700c0c0c8041a119000003d2040400000542080e10100c0c0c8001c170300210010b22440c18014511500d20807040035807544101c07500e0300e0518400320400421a841031051100380e40c0c5020b401702da00ca200b07007801100070a0340d08046075400008100c5000108081104002030781e80054217210003401039800300180418040d004009200b21504684002034a404400d602d4011f000020204495040000341c200d900d1031091007010f0300c01200d564903800040040014500410440300c44140c119031030340c054400c0070a0030300d401300003848290241d640c07804d254141c40199000d04018070340040004551045440429018010071900480103000b4410b001905003000184841500d506480c0c07250400d044c9010f000c0c40d50801080392030715428203e80051980ca007032003400c0040c0e005e59a000e42ea4078000ca04202075510b450300a07400c2000c03c000410032a08180400c90300598145 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 439866951 1250 439865701 439865711
    0x2120319110412120c05030d0e010209120c03060a06050d110102011d0a0204061a070803060d0c080303101a04050105180907020a140102030115080a0e0a060914010507020d03 76
    0x148008000300000503010245200c00100450b507100070403038580450307206841031340c4004440801200c20384076074040144241e2040c03010f6001c0800a4024803503481044000508004d2104000744200924401c44c11107500154000807140c10244140c07980003e00350310520a0500e0980480e024005001001e42242021460210640e10030b400c074000c034003c0700c50030100341c15207240040d84405140c0c1040348103e03e007850000d0089203444641f040082d101c00d1003400c0900640f14042c0c0c2c1d0f40020701190b0312900b000d0701c0d00e001503c162400e4000e0419a4000c54407071900701c2a6000d924004c0c2c0000c0b2100780070910913104400c00504032003e41d82d00786000d0351201d200b1000f0507820450f9124050340440c8000420076603541c001003070494140a06051400c41402007052401c0f4407003801490003940400c00384502c0329000381c0d41c05401030f44c445000542040b0303840740a401c007403011030100c840d50348503464003051000e000e0a00d0110444d440c000c102a08040314060751f10340c142240030007410f842d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 439868201 1250 439866951 439866991
    0x9010e16050c0c062808040512070f05070308030106080903040b09040207031b080a0e011d0103050405100507020c091f0603110f040b04150f08010501080a060b0a0e0f01021203 77
    0x20f2008865852000e4051602d405000c0001040202c10f44000b075020100c03450280300c180d01c141d4859003d00c1e08030000c4c040020600034900c5040c3e0061600741c0790114080036100001701c04202c01c0004501805919849504101c00280080b10280c54100760b64010b020a0104580d41c2007100c501c05401c860050380d03020103240a590340400310415030190300105800c2000e0005070001003d03004c0b09039a4403850070b500d101c019580001c000708441c188402e00356940030a5402580440e410900440c11650141d1001030b0038000c1c0c41017200d24100581003a1824019400c0030109542c10000503264556408003910401107040ca00c1c2c81340c1c5e42010f40320728100350740300308590803107425003428202c4954071901c40c41210a254402d01c1541c040080c00c400250540b441800ea0304100c2c202ca40d1001d050b03920303140c0116030740c0402805d000c0c1002d9513840700040c0408040c005100b007111503107070b07245402041001c1202d091328807190300e419500b1003a100144001c82904a80d07100c613408103003194000c4a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 439869451 1250 439868201 439868203
    0x20c010513050d2001090e1330020105060d0305030412121401080c06040302031002030a1104090b01080105061e0711032a061204030f0e041a09010e16050c 68
    0x100d81e1102e500030030114040014050300c510010801d80e080003440520f400140c0044481800c24410851001000004a003c40e022094030070002ca02075400016410307030b4200c086009034087c006003410380c08000c0b08080407070340a0103010b5004108076a81d4061448a4030040d016100c014801000140c1e050b420030b440074020614041071000310381d8108046104071030240a65207007809803240304d12074255207494501d452422281500d5001e009460f41e0200c24140f50007942010703007800c0000e074640c440c0303400e0f0780401c101401c0101045040820b00070305c468000340a0f40410f0700880c2c06150104502c080000c101d0703081512082410382c0059440c0c170b450526000c03caa5212945034140188200000e80048100303000300030860a1a42d00d050045200400800c0e204c1e43c0958031601c00705000003804640504203684076002c03a41000c03801e510650002030100c400c09a04030800980c81c49061105062101c005030142c10708400c0e00c001418050001d81e414a0b00507000c20400c18002102015244 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 439870701 1250 439869451 439869487
    0x302060909070306032310090804030b4303050c0a0c02030c040e0c011806090e04111522120b060d140109110d24020c1e0f0d020c0105 59
    0x140145510110f1b400c46032080b4102824400013070300314403031000d42d100010182e200d5400c9540c0c0c091405840d052856440f00141e00340144000310460751850f600706040800c8116421081c04810b250004254000501c0222100210780b10201468a4204040a02c40400719104001103003004203540e507092001900d002c00060010b90400e003040d0408444040004050140010980f00c2c001e24581144041920541600c20b403400076002180810203001c64060305500f146c042d018240e0102043c001242c1c04140d054045519820001100030703090b00080800c91800c0c10401c0c803286140e190411404012100d2070001d40356405000c003280256031284000041d0aa00205e03520042100c01300c0d46000707010b40003090390040e2a0303c0c10b481c424a40042e03207201c3d00340d1000741410f10f0fa01100d5440b079400c052003103e2480c00d508104000815804014910708086800b0440340a01610407540c1c1c14440524081e40c4c03d43e008895090722540c0114008000080038a41b15031101c1140e40000a582 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 439871951 1250 439870701 439870703
    0x10c0c02091005030a080904060e09030d0c1b050705011d0906040507031401270207120e0604090603230708100506030705040603083a090501090206040e0f0907030206090907030603 79
    0x22242c01404010000204058144507008a602700410b580e40c80c2d40030100207045444241070742003005101400302107a44144c50650240c6409400809007905441003103812171800d075810350051800300415a4001d070b4000e107044058410300c2c2c07601c1181d00411203801d0050b0000340300c0d0f40c44100142d18148071358040c0140b1054084041d020f56034501c2102d1050124440220140c501c041c0010388080043c0200d0b00010350002c000c0d01c5003410f92000300c905600c4180350a911500070040000c2c201090b020f5840038601036019003201401d1a41d40400408414600050507040b4041c01c00c500403000c50917402700441060046119560301001034141500c0341c1016500900e0b01c507000c0180a003400c04cd10700075201c5e0b1140c8048181344030100c102c48500348034041103910cc00501c8042521107400c10845680f0420000c10384c806182c0c000780d426003013070b040020b0683d450020080001500d41e9280e41101d4000040c26016046070080740462266082041c080c0800c400402c0c00544241e00c084021 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 439873201 1250 439871951 439871953
    0x303020d1109130e190c0305010c03050402090a0e07080f0309090901091e0f05010606080f070903050c1003020c0105070c021e0a090b0609040c0201240f062609070f08010c0c0209100503 81
    0x40700311490700f101b03030140d81e000c203890310343c60501c442c3c81341402803003424000ca4008006100d29030720520781030f02410251019203041d01982800003025642001040201c0141c44091a2101c3d05c18042c460b00110062007603100d603060403101004170301c010300c0825011020b00a100c110221508001100c0303003c11400a200d50f02e0301781c0c00200143c2c0500c04c40e000d101e8900030050701e038039240c80449032207a01d400090126001640236010b82e1501d4001914819071901300942402c3c00024220b003150301c110340603400306240b502c000742189003090070a205c20107102c4080c40141d034024081103540310140074003110715580b02b0481843c1d564480c203491502d00c00510520800e0342d40c4074028083d149078640a548103401505d18100f407010380783c144050f161041000101d05103403403030880e46c00403070700001d02006e41c00f4145618001600304c265437003480d050004100c4c89180c02c00a8440001c1d69110000e9a4503045000e5007050f840100d50304100c1c0c0407100d402858940c11000c0200c245030f036005580c9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 439874451 1250 439873201 439873243
    0x703080a050702010f031b0e010c0b04110108090a030e090c0c06151509010e040507170f1e010b090d060b030304060c0605070e130c03060b070303020d1109130e 70
    0xc968000c0062030050f100303030b8519141000704035041d403d4030341d40000d07000004840d55048820318030904000440c10014901040e0620303407919204280c20301600c0640320480844003458455030041032072508000b40c84d00800700030060ba1401400030007030041e1a07114004603c08991144107117800d403403025808109640075800c00b130340310342c50103071605a400340601041180c2d0b010000090055a8030040181c440403424050174040100a040042c0360000f03110f204803200341c1c1c8040600c000ea03c120300c80a80c40b41d06003001d041c59000e03140302406032031b014154a40180203011440f816103014503c140d40c80301201c0c4031854414090040125010b4051101060002e50307143e2211030018a1405a07208000540302e880e4211507001102501340c1d0007404040b10111005130a038006c0d1079000440c900021010b844a1100d15964042c0c1c0081e00041d40200b0010095006841210703000c1c04001080d926140302c401c00b14103102003409242c9107aa594207814000040c0600c54a400a01184503440c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 439875701 1250 439874451 439874467
    0x10e09070b040e0f0108010b150304021f05030403140301050a0608090f16140603070903080c010b060d020901110114070c080c0d052203080f0304110312030a18080714070308 76
    0x1c00c1c0756045840c041407040c0341000050740701d1b06105601c003e0101030b1141e0510050519050304542c005401260800038410900104046032a44035801030b0702136582da075607401c15040042400d003084542e0384a18a040004005554442c04c102048a0a40c01c2c203c07110340c1c0301d840190901d20301449401c928050444101c150382c1c40300039900255800015441c2d110710000d002d0004a00085402401244800324103001040a140182c840c408070503001160ba41441c1011406d50f4010f05c00c82c1048070b4002c80c610b41c003036070040f00070020044100000c03c18090001d800c03c0d0107010180800d014000c0c4c611455041c0440007040304c000344900811103200c80b179103080041c680e03402020b80c008403c80a4140500400c2083c4e25001120740040030030341400c0c2890f9903200641e00c00341c0b04851100002c0403206207520306124820200f105111303040e480703140c0407440409403074101c0400c41d1403011076620080092400d800b0b0b901000c0c4c0180c0c078800c60108160b80585040e43c0b907000074040d0703000803070034078 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 439876951 1250 439875701 439875719
    0xf1401140601020d080405030f0c120c0c0a050603250e03070e0f0907060c03051b011e150e1302030f06130c050906030c040903050f040f2c010e09070b04 67
    0x54051202a400c440041380520b0302110803650039200146035810410440c00701c4241c50000d0007a42103040700342c81c2510100c1001103499400b1517091517032a08015003030f0040345080c84040c0007d00303041c0c1c0c0c282d14515024803440d0100707071101480403c02403084109143e80e441259812034064000d0210780306c081c1c9840318512145c104480b90015420714000244c0c0e034200100d02182110715039100e40282e80074580e801c1d221500010118038100089500f4400940f0090240da003030b206050151700c1e402202d20b02403d00b940c0501c151440e1070f102804c0104280c00803558035a9202c0a40009080000c20910019003000d606c003010368110310030b5200b8016610305108254088921400710b02e0815a9100107002200d00200e400c55031540040102c103059050a0f0001050700d80b02c4d140081c40c00139800001c0ba0305800c10b030041d04018111003020320400c1042c0003d810400e4050003095407610048401d09040e50050003110001d0802d42c0218050742001c108103c003619000e038480b902e85d51141803036 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 439878201 1250 439876951 439876991
    0x17010f23250306050423070509150307030209030c060c07090506040212090609061308030610090503030d0212011d13080d020a0e1e060423031209010f0306080a0f1401 73
    0x10ba03100c0ca2500026000281c6c2e283d0100030003070920b140042d042da68441041e0b03442d410040300c080d0003001c5106510b40e6403404e240194070a00e0907403001030301c800104081c94604100c0740c007128054a010014805081c0c400100c090854180084c04140d60ba1410b0100e0064000d907107a03054481c00700414010b01e6000854100d10480d0042d040303800f0795a03080600c0a145840341d502401c409000c1001c00e00340e0410340c0b0382d22442c08a5042c0b00c904d01ea036410200340356070f1040c0c0301c401d4240da011031428940700c000c20425004200352107402c6010308480d103a10441a0014040f080d502c181c02c4074074400c001e4103c0a0714503500e87c0b414215154400e4000161071250070200c80ca06c0382c12080d00d03000350510801c240310908100034002900303041c180400314201c42c2e90705c4801c806015400b90040d9942c2c0e010041002c80a0501083c41d480300341c850005030052107105480b4050505143c03003441409d03c0024400001a0000b40e1301c05d5203129428043d5a552507105a0768240d42001c512440040e4090f10b4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 439879451 1250 439878201 439878209
    0x4050d080c0313060b04091b0f061409060c07030b01031109181c2703030807020307031205070c02060309060f01050607020906040c090f17010f23250306 67
    0x915140c0c1d80d800038264224401201c002e803030f40051429580104003582d01500591401520000d41001c1c95107807000c1c800b104d000b81c1c2c40e003025048001e208071030204c2c0c0d01600034042410502500c18000000490307500610500d04d000d200c003c00d400701e41d410204644001103030001204503031940c403820a207501400d5150034601802d14140840c0e18401c030381080c1010405030f038024010350190518540003003040d00c1800e004110480c8202e01180080da1680b1125800100e1101c03842440c61501925004008051a0541d0401d20492000c00e4021703440e55205085864002441d0359004426a04501034510203500701a002c006c000400000290460090500702070007140c80c0e0740c842c01c00089124241009400402e107901203606401d241d001400203400600300384c0b131280e48031103c80440e660030f070380701c0c1c0003031070113400c2c000c2c0300c01e40c284508406000c1c03204007400a07070012000c200260300400c6598580d0484a0f000034100007407140f05401d080c40040c01501e0700b0450b0a0000c2c040c04031409 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 439880701 1250 439879451 439879457
    0xb0922140309012006040f06060503010c080a0c080c0a080c0421020306010e010605070206071505040b010e06010503060625050f010e1e0a020d0812040b010e06041e020a0c02030604050d 81
    0x2413010411500144480c08841c1c0c0794000c161950381c95440d0342ca009a4804101c6200d6181c580c0859151340a0248400507800c903525054070786007030000d14058885003c8004184800501800140700c0303202c040f9146410b19007003040c2d06465070030070005d440c401c1c1c2d400501000e4510840c0d20307500800204800105000701c04580701d076600d400c02e0040c000004c0c0304e000c0100310100500001030610801800c81a4020001203407040400005041030b1242110300b1103400b805c4800510102c402d0b1000603400038828a0704504504c1c0c201e000c1401072151441040071400362504054142090949207100c0560280a030307054100f6004200c1d010781a445000c00040c040e500c06810201c0120301810031805a90000300f0b6105095001d22036038030300c80441561078402c04c100c2042ca080a4030100c902680c07051103031050f60340c0341460740c0c2d04035007003d0030080c42282000500c005607502600d100c00341c0c0300300310340040c1da9200301ca2082e1014140400000d4150240101708014041c0100344002d10a0540d2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 439881951 1250 439880701 439880717
    0xc15061202130e1b01020c09010311090a0b06070201032703050406030c1409010f0216030c0302010906020105070f08060d06051e011e1203050c0109150c02010b092214030901 76
    0x200844043d81c501141802103548044051585150900e000d07030403404042c01900c9841c460781b000705840201c00d80045d100c003100e5180d114500d0418181c0e29601614021003003009021700d0380000d410307200343c10000c4d041580307500605418a146e040101c80301c180e641c03030400e030403820392a010740550014840d00c1e0101c0d18044030062007070b000d400100d03e131402d685500e91030300040394010749025061081e94001c51140a00d032521070828910500c0140d1f0290074403400d6240345200042210446411400071a4148410311046980000700c0b074401043c94105101180d0301e2070040346940651401c050081820030f02440082d007501e00240310441e130041203044042e0388038140000c4038103291031100d000b41e14005c400c020702c0701d4501807246040d200c0d2814620b048014000a402e4910715002a21215809100d440a225091080302c88020300c50000f4810b5441306070004041c1c0303030014100c4070b0309294079110392106003c1219018480f9402a0500081c505040340280d0b01c0d044201e5081c00700b0303400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 439883201 1250 439881951 439881979
    0x4111602120109081c1805010e0d0905130902030c10120b030f1c020102130b030a0b01030b0d06050402030c0a06020d0905220903020c120a0b0f160c15061202 69
    0x18010f107030040340c0059015250180041c0200d0791a036a094048501c2070342d4480e12000c000c009505120018026800800c01c81d90b424501428841030304010414403400820400035a11200380c035070000108a1000240d061440c008642018204000c2d0341e4050044100b841210343c00200403582001c05070349c2008617a00200615aa844403882403a5885c1e01c0b120710050012009130300c22038a02402e100150800b5100f8250314281e0003140c00401900c080401045058240c0d80720350442d90809290520404880310045003520850a101a203080c2c2c0710310000313095413010050b007030600e0805010301c260a550361a001791200c02c003a0b05403000440900000595140c80154a1252550078503484442d11403914907600800c00701c0c0c011410350107002d10344007056560700c40e12a07603400b83e08003502c04540c461820620347c02c0000c0a01c04015181014412448030260340c15910742103a0802140107256401c181380d4514240c40503401c101d051800c0496180e580000310302c02103100341c1d121100c0c0810 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 439884451 1250 439883201 439883203
    0x1d010e030a2f070b0705060a0b0f0607031b05030a090b09090f040f3203040b12071b061e020910051c060e10080a11010e0411160212 58
    0x1507040030030018030101c0a420690503480a00d5401c01407040d42603040070501c1400604200455000902c05003011a503074050010a01c03460f030707118911800030130070201c210b03002644201c1002c00c0c080c007a44010594104260191000640141c4884c0d1a40500d180c075191103a07581d442203500c1c400084031604001510080501030341c070800700c01840f92203141e68102070410400030081083d9003402551001101003003407504c0101ca14038514a41902c928402940d441000ca400300b113405855100300070400408601d441594941c032007a15132040c50f525090401c4400d81c4210002c248928032040001e820810300d03512002e06a4181034083d000714202000388012030140100740381e0054400c001d01480d440c4100028400344408401c1c43d40306180c10b6001e50100e903042c0e04403070b00320700c0703180107005004070280381200082104500405018555980301c0401a24011220303041c44910b1140c641259947e4000149644040400b1034645005600c800582c0240300d109a006d1b034880e10101011f500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 439885701 1250 439884451 439884457
    0x11100c0e0d0f170712090609120308010e090a05070b07150b0906010806150d0e06130302030406050a2313050907020a020f120a03080f1e0601030e0c041d010e03 70
    0x10b041006410402155120000c503a02c882120394000030342040700c80005541c13580080400095070307503580038090404202400040c585d421040041c14900326070000650f001c2082410340b45180200034103030710f42056080c54044c240000a00c04e015254011485408000140c1440760040b15150704003405505480125040ea000507034020a00c2c0c030000b089540141c0c0003a400610180241d02410b50030100b1100c160420041358412944440c44002081e60400105800444500150f0304040c440d40d4007a40c1c0e4440ea1256206001c0c0101c0c980035118014040030505101005400e00024003005c2d0000e400c0c0d000f0846a486118066804034190400202a80c4a8aa25002040103a44035002c00001e412040030b02c60f4410540e0a08404258060000000320391180d02c1c0c0350000d050101c50303100030a100030034150500c1d109088060340e001c0c296030b03801d07003042d000e00340000c118142c203c0d885d080044002515800c80d00304028080c030307445151100610300030b072140208030b000c43c284c62840c1c83e48 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 439886951 1250 439885701 439885703
    0x131a0a06051201151b0201020a0816020405180a0b150a0f1e080303070309020f0a0f051201091a0901090b0c0316050f040b2104060b090f061f11100c0e0d 67
    0xa170a9554150801e0700e03003081c540e080f8014012541c102d003182c0d0740d4141c154004050342d01407025856101007181440e01840d43c018400030307a1007011382540c00c116603840481d0035003c0c2c105417200c4003090030700b2549442c0c40703d40c0310050a011002c0ea2940c0a03501c40748079612a0100c03400820b95800e0001002c60442c50680c1c0c81200a03501e15111200d046010f13011418007aa07001c202440180600c0e918500c000f0010300c2d100e00312000441c500010498103200c101560003050f41403280c1103001a24a01803400450341c0c8007a04600303515000801e50042624000003800030307082e00184481c01c023020002c0d512408001d4260404480c940400312018011609400442c40050001340021000c1c070025007445c4000040e8111180703061a004402080207403810380b001130f5500c0030110340341403900c1c0742548004401c0c03807400380741801e40100310428200d10b4103107844051060111561880342d09400550040c0404840748110a400075100070154a0208004641543c00144250070f0090400b09a1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 439888201 1250 439886951 439886957
    0x120f1309090c031e02240c010207050f01061e03081e0c010b0a060203040b090420030f0105190605030708070302090d14010e2d030403060207060b0a05030c131a0a0605120115 76
    0x10206c2c00d980b800101583c03130740700d21100f2414009141000000d10180c00124014001043c015007620129821108541c000310b01041c8090314072a06084014a080203c99001c0b0b01c80c1d64400c0650400031545200321491241c518002032002d40c0000d0540040180f000200c50070850715595107021382e540c4c80b0314460540a5001030144007014a001d521507010b00320000b07d4103820070141d44030a01a548215180008603c4250040c06a418014451220781c400680300c601064240326014140740001481501000741601c006006284a1f030161455007001038100501105585081d039001425491106140c2d8a440c00340080e00b080010b554605140890091050000c1a0654040000780317503e441510321007004008001801480148402d5015004c0021030b200b201d0304003c9080d04d60350080b84a5800600441995070b03031817458040803241010000f4010a00042108114410b01310480d130000000c1c8000480a07000002030a00c20481c40e800c6400340c1e22140400890308440c1040400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 439889451 1250 439888201 439888219
    0x30e1e090402060c0d090810140c0912100608190f1403040305060c04090f0e0723060a0302220303080402130f051f0602120f1309090c031e02 62
    0x400e0500540d40c60304140090400b0707152640d80f080a9151101d2140d40d080012049841041752003004d01c0001c010040d410401d02100801d0f250142c40c004014201403039201000800c1580c80c3c0e1000740b1040301c020301c04240c1e103031104007203144001458940700307042180c081c00354050f02e42500680001e400a41c0300180c115850800e49508922000b40c08021032903201c204008004520304010181c8143d104465641d41d0b00c1c10905220251504000c3da02c12850030b04829482000c408206c800550342c1079108071004620f10741b0960f00d00720740e059200b0780200c40003c4840306558160002c151820110000e401452010508080103445611018002600660201c0d0040c50880c4005108501840012590501c2d101040c02107a5051ba404000e8017590300c900d60001884000c000c0c002c00c050f001505140308107120010491040c0410307280071400014628a90303500c0000b01b00054106a0780420010080385002c45207441180000d603a03108120764092984074070804c0e159505603000d40b41d000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 439890701 1250 439889451 439889509
    0xf02030c0307030c11030301090c11010e07090f060b180a12051209010c02040c09080d0929120a090b01091b080703060506130e0f04030215090705060d0207030e 70
    0x4010f06040c6013800c00c010046002c0810f029040000d14080c01d040c080000d0b00703031900c40005c0c10f41010302e00c0b0340c09240d05100030600629030100f82c4504860304507101103907011003080510000c10484d00202949140814a200003400744040f202544500b03450341d15419483d8a0245440314813604010031a5000c00d9101143c900d845011b0601d0f01c0060400013200704141c2c0c005015107e11140c00400101c244004001a980c10070803409032130f8050800003011410140d04081100c426040f112403107a00e94207100e0641c0002c0d0450319013041041040c102c90504110710400b03491045015201d0404000003c0303022805403043c1d078008214445034410600c0c6082e82907030404001018130060540e40c80000407580c81d40401030414100300581500e040e410400c5880f1040d80181040302400e8880b000c1200181d00003406a0301c05150206018003562200c182c50301c1d1034460340001b6001100883da00c1400c400c0c98028201c0203201c0e4907185940702c0200240a0312202401100742082ea0b1112a00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 439891951 1250 439890701 439890707
    0xe06010e0a140a0b0a0302121f14060408061f0801060605030106080a06091109040e07030c0506180d11120105041104090515070f021615110a05070f05040f02030c0307 73
    0x42c00c140c1c0701070224405643d454803201a290040d00c0c41401103600010140a0a584000300d01d90019442e04040d00302058440c0181c200c2e401c5000d5003045d410308074481301165a4041c00d5900070007891007141c00034600b002c07e0142c548103541d10070444500e0300601140310354040c081c25060b20110b0b5209801d61303103041d4044410090203400e40822681d00c150120300031105003e00d055074002c010702181d44a00c1c045c01c2c03204907002080010405c1d00649028000181d03900601c1040780c0c400c803051070300c070301080c1e004038030030340e64920899072004003480e01e1020800c1c181d549043c48202224004260103064043d1070170380b042210300400100803076441d50700524056104200140c0030b10b0031107054030406600781322804004e54a400c04107903542460100554108181c80c0203a0005100007255443c183c0283c0e07007004520910018480f08201c020104402001a001d0b40b9420104440d900307603440001341d20b51b09082c020f06006504207038444928121328000c990064004440052039a5030b501022 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 439893201 1250 439891951 439891979
    0xb04032f100f14070f090509090604020909160e04330e0102070f1110050a0804060b0d02190315060302031902030304030b0c0a03200d1d1005010e06010e0a 68
    0x306445a5160002c0f0145a0b8491089200704800d8032070115291140c0e402034045400c0b075110f140702d005650200044281e02064054000d50306461440c19038440d54849400d0031884800002001c00b9118001030741e082c03d84503640200c0c060040005042c202c0f2410420a031070320080d510300c412241c45030f190410010f41c000b00c10b001c900400141000040ea0b504404448100015241120143e07030200281c40c0c180f10203240710405040440c6011300d0030030f0190582d10b0085c0081c00c040c1c1c0e00c40e5500082d844284112155030381c02415814001036506051404d107507140001d94048807141c24920100308188541800d031307600100281051084040d820101740840b900c00c98050000303001c00030009005804140c0604040e840c130315120725000c0c000030100ca551000b41076800202c5407620721104180400c0340c030b200710305100c0400d001e40e88802e4203420075801d9500070524070411100541001705d5900046c142c80300c40c6101074554035004d004568580307c0c002c0060340100190010400000c40300c3d10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 439894451 1250 439893201 439893221
    0x3010302030c0906040f06090203010906080708190c150302120604061d0a140408120708060604031b0b0c0708210a05250b070206070c170c0a0b04032f10 67
    0x40810b046e04802441c105540341c1da80040c802c42d4001c030050080c03d4103401800054440b00b402451901e1501c09040e0343d40400c210241c00e054400064041445170703891085014020a11a00101b440c204031f0050082d80080624590789810201080c1b0361318003401036400b1601c850044200300010101044507103030010302112407155446203900340141070300340064411801951811345803000c1d10403940c01090300402d06420050100100301c1a0b030f07107040660301600d8019950f2000c41580228000c03020f0425000b0003e51800494041020070002900340c0030344503050103880b10840c0110300c40410280e41609442e80348418840c0c0640f1511031005040078821649588840603000d05600381908038402003075442d080454200281c1607010001141c10007100c0c58007140c0100c3c0d070f8640d400640081c2a20089940c2c0000f11070304211810080d10307403059049504081300d8100f514024101c0001c200341100c1101106c90110fa00c0700d02464100c1f451080040942600610001903400421140341 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 439895701 1250 439894451 439894459
    0x30e13060e0c040f0f05010f0509031f0f0f051509040507120c0617060f0f0d082109030304050303060f12030a0801051507082706031501030b0603010302030c0906 71
    0x64000340c050700c810600c0740250001406696a00c0c184010001d003000305404c0f0302004152070600300b01d281d0f408420704110f5041c500c4c0c115112040080000e06010406c0b03100340d2982d00e0100207500d2243d11713074001c02084200b01c20070841c6003441d10780c80c0f058030f200702e601a85100710700440d1251410a00ea0045e0300910a0b810f03600740f80c0c3c495003401d086050f200304c00c0d1903040341c039031043c000c84d03412084150ba501e01414045221b460034400084683d43c40034140350140010022030740003525a4211a6145544a0b4080761905074407031840c00030010f0412085c0742d01c81640d020481584003c8100d0340201c0d0000003944c074507918081442050f15900c1c0d68240c00080c110a21105090244040d104080e01d60f0b0b60070819500d030104010141500d400c84619900c400c120040004e01610205c0b01060b1059a804031050b400e0078920b407181400d4608580c0111001003002100e001c0d040203500341110036201004000380b00d01c1440303c0c0d80800d000c000e4060340304450f500f03564904025000d510003c014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 439896951 1250 439895701 439895711
    0xe0a0b0d0212070509180114040f0f060b0d0c05041212020a02060d020309010b030c0607110a0308040612050c0f03181e07030302060c0351041503030e13 67
    0x4000100303607810442e9a00005a40841c80d52102c0c40c0100003009503400048010346c2a50401c7d449240c8440d0101600f445140c0e6114080d0070901c440c1c101c135902030815602044000e5480440740c2480c0e004903003000c0c100b884c00c203c40700302c1809601520147e43c0001c004400101c4540c1e690507014003a0701140c42584140110500182d407050700910b5040c071256800345c0c5a0a040b4009400e450780e12004601c203401600000d04c4503100c290030350300001e0b0020011003c000510380818840013042e04090280c520000300807079510703003003041300b04d0381106100200143c2e0f49608034500d05001e003c81c113400d104400c00101f921180c0d86600005d00121080c240d80d0b05e000c40d58038000b0180180207140d40c16802c681070030800d150301485030b280e02c80500702001d407452406100c030101140460032910b910f8600d0004489016142c0d039600100800c00f0032407400010b605120005120704507013038644c8110b080c0240c4410b0007038061041c50840740d05427900b0014640ba00100301c211007008858a8050f9510 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 439898201 1250 439896951 439896967
    0x1e15130501020f0a120b030a0305160c0b12101505090f180a050717060307090509100203090601090515030c060f090a12062a050702120d020708010b010e0a0b0d02 71
    0x680f008094102d00c3d503e0303d03002c0740c070691103070020f541401c1402d0f48641c0042c4160030200b5080012200001da80c40310000000840786441207050030b0642100c44003c5000c541e88610101e8404400e0007110f080084606003680c5034945a61040b9040944000a6040c07201c2050f030304141441c40c00707601d0020b009641c04000b4440030040e07410215400d20705140c494007808111604140b40754166070441c1030a4800f45040c40c00b0981c3c2e8440e80c0301d152007844e51000000c121030000e11039401e071007040b004299501e0400c403542d140d6420080c01060b40f101d03c3d00010950024440d00d0007184410013402400c00142400c0c1000060b821442e420b03008202c04200c0c59900e0b5a9811101d405000c000b00b03e07190b8805107090a0307084944c15451310202c01c06082c200e80714400c00c00c0c1c61700d100c0b81103440c0aa5035a2040d1002c140d4092020803070220034071810200c114120340110302c00b4280d40c1408000c01000481c1130044550a03516004a82c01c040c0c00442030100701d00b00b20082c42c4219440d2805440c114030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 439899451 1250 439898201 439898227
    0x20030a12060e0702010c1d0a05060c0a080f03091b030a1104021603050c010609020903060109090204090c03060b090a050c0901080915070f03060519050f01110f1e1513050102 76
    0x10850f600c20041c3d66940c00803034296044417420008003030b546403203100318030210085114501c1034055244240d0011a4503a051102000b540c0e804981c019850f5844801070704482d085e43d0000c1c0c82ca20b00070f00a003800c100540c10080151001500000e009040c1c4880c0d40c1c0f035010f440c1030406403080d0082e0302004403000044c00e40404000c00d82c869500e803959840814061401c582446c1c11012010f40104618025030f80c001461605442142c00c000038444040c4c40090000d1080c1c003001420300c00301480001c144104c5502200b1414020f0764482d0642ea40c4040741c0048820803100c843c4007003001c6c000f03104554440e4030a40e03405640242152a54030080000c88202c4004864090000c1d00d43c1c1900443c1039070502412004001c00e444000c82c90035542000101c0e00c0703107401094010089014159510b80c841c1c60040c01c907078211020790f201e0002c02044030f40c59850145d40028a4182d4503505114424001032002804034038503065140c0e519000c581402010818a007a0350030364092001e4010400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 439900701 1250 439899451 439899479
    0x140a1a0a0807080106231215101d0c0412030908010f060602120903060103060f14010803030106030e030924043305030403090b0319061520030a1206 65
    0x3003040002c00d40d180ca41400c3c9800d50b102e94210303184010f21403e1400e0088a200e5404d03a485034100c520070a00d00c4400707007803071600c1105110881440d103d0010f0010b90751241c61201c060364100311303a5461b101d642d21070300f41c3c00c02c601b40d03507010413104100801c01240c4c060603091480248607241c5220883e07a5030103441d0954500340d10341c800d09552180c08001980e0104204208030341c0d2506c4d818140601c600c0001c1d1100f10500c40940402d0b02d400d1a210700c9216030740301e001808900901107202e540c460703a4140d90b0390024080c0001291400e02074106a210000a652209000901c2c00074502e0064150030781e000500c9022101c10342040c0000b040007824854068081e00b80e03890301c080b00001400d4020202d04100302860140001041407201190b4844107040a5820030300310f150707030303900d07814003c001c1c07168400306e2158118a0041c005c10101c550321300c0c08410820691340c19082da4003031652944130b10201020789a07654410442000d14074000d481540d00c5070039800e000102a40c5e1981c880c14041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 439901951 1250 439900701 439900709
    0x170a0207021e031c02070905190207030806030606060708031302030a0206040801050403090608150118080106060305180d1209020f2106010e0c070206070501020c07120c09140a1a0a 79
    0x2e80c407061103107014181001074181440080340010055101075402070744075035550003107880a94071600028405100e100c05002d04011044007159502d0f41818000c08000301598031504c04e000781804901686008416a203000d41c00803403061070740c0c41c2c0102c103d01d604e01e81c0c10200c0c4c150080c81e00c6038001d40c2d646c1001e48010310100d4000700310f619081c6401011b102440d0003510500201e00113200c5640103005220180040030f0030702513003d41d0824040c501c82c98140c0d0019a140d0b082c4880841c840c0e500d5000700740a00c80710003448111522243d001d0340c42c0c030070300c078000000200440342c003246a1115402c906803440c000746c808450388581ea800318050828078082072a0380252a41203c60100d010001203005007601940d4940500b0010060358451042c5500030f4443c400126005050007029811a0003105e004411181d05994400f00c40c4441070320350f4002c0d2a042c10700c0348001204031075800361051008260031002e070540d1b90405a00c1c0105003004103003900a100450050071921041c481038060 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 439903201 1250 439901951 439901989
    0xf0c08030403030e0301090b0609100f080c030c0d03020303040308190f06060f020601050108010605130e2a190305040f050f1609111917010b0703140a170a020702 71
    0x1c81c01c50501908289000c2c000e640a40e14050b1108046181442d03041d800070030858140c155a150000f1030b01d03005903039800c48860301841c0740380014000000250701d802c03581c05906564070301e0f85010401074940e440840140c0580c10030800640041d106108603075001348403841c80c0240e090040301000860f0400034621030401e035540024008e1582080580c0360111b45031004203465030500000800821041c0310b00401d10001040150b9000810494000544034258140e5205e14000d0010101040400a840c0340102400d029644280070ae01c05c50743c0c00b80750112501c3c10410a0036044008060042c42038a025423090f040300c0024070b0a014a039052040c0c3c000505000c1c1c130f42e01d440c130610324540d4000d4050516000004a000c20a08282d6281130101007044401621074078084d68003002485040911590b1500081030040410000e80510f43c0295207520f0b000f05100c40864040c858544410080f03400c1c20040c1c01084181e803405e581c80980d07280c001d401c1071400d40c081003104c14645c00000103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 439904451 1250 439903201 439903207
    0x709110406030f0e0703080a020a1401060e0606180f22090c05030f0a0204020f22090606210b060904061710020f0a030c500f070f0c0803 60
    0x290795414010030021001500081003000c00d1083c2140e07441c050780c413006100b02808a000c4414174028003c1a40940c4c012000e02084035100c1b000d20300034415402508d020394000d40104200b82484000e6a40101103081d00380030310040001001003900f0f002d60076980c054a94018100c8407241414540c0c2c03c5209000b0116112649203040305102c041500003901070707803040c0062031005800240b26203071700f03406440040e43c840d05600d0316800c6114180034186070908038040c122200342c03640111400ca481d0081c0c00c218550b00c900e0126452504c1c0b40307098008081c04061000240c1940e885004e5407c40181018a450515808030307055036520362040c9003103010820341800c1501c1c14000c500704040510401c602e80381010140403243d006a5450508259891303509590143c010080b0b801c03141e40b00310308899140c1d800000304035201a10300f81982491f0300100d121006100206006010200e81070640342480242c0f85c0550094010b540c003580e4440c00c01d2646008600f80d458490090940c42001e981c0d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 439905701 1250 439904451 439904459
    0x110a0c09050a0e030c120904020f04060804060e0703020a05090a0f06120303140903030f09010609140402100c020a060c0c1707170a0317070c02100513050a0f0b0c07091104 75
    0x102e0326040030390f0310242c00400000c0800c02003c13640002c1c081e40c6d042100d84812421000c20b000340180524110641e000103800b0882c1038010b8441440345102e0700c0d0a126500b90428019240c0e4024400203420040c2604280f0151405111455112a4068000803002101ca403503070180d6040f03900051040c00340400701e000b4103516004040c0800010002d821040c10051842c40c0e407071000400e00c07021042a030011407040301081d00584021b0440309402d000b140d80d0044c844101c404242c40481c13081c20009000486580211548a41740f500103005414030f17071a200c410346240f0a4103130100e038691000d502c04a90359094041d5000307a1031143c4000c104a60030410344074101c207411074000480e40d0022200e100003c0d401518030038580c00c1031007a1100d0b0f480f101c101b9503c440783c0b01780082d0310070100b415511036280d0210142c005200c0305480380140d15540d409026004e54036018032600c460f4210400d11200021900415418010404542400b0380e102d4555040392000301c9103100a40001030108 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 439906951 1250 439905701 439905721
    0x705030d1b11030301450b0103050a0504050706030f140c0310060212030402060901031103070305060f100512060f0901080f060109020316080402010225090c0305060d03110a0c0905 79
    0xd058010b000000c40c51941401101411b03050002101031001c44007980b6070503207007074030807414040d001000401510185d41000c44005045420f20490020f4070b804005803481103640941d5000320b070428040d0000606182044010308030000b88140e0f49a00c1c1d0032031703001e06005000d1031407140280c040ea85407681860302d003e2410b10300c0c0b544201c045500005501e14026042c100701c0e5003041d4110780050351582101c00580140c85c818030300c1d502040700407003008000344d0190041da20a030007c40ea11171800d0100001c00080b00740c521098000100180800421804501a81a00480c000381044082c80c4070100080b0342c02c500340c0103880d050308170000245014a0801820f4003606640c0c0040d4203500d450049001400f20501144041043c003801003802d590003401030f0b184070b1100c0c080c1c4400d0780e25155070720500340c2124805c0800c00c5141c03a072800032a503c070744611400f4500090505501c6030083c0c8007118a52094100c01055010303d04061000030400c0015100404040c0008a1603140040d01c003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 439908201 1250 439906951 439906967
    0x20a1214060903040515131a1306030c14070c0b040305100c081936030e04090309120c05030114060306130c0603111902030702091e0105060705030d1b 66
    0x690300343e0f20902c0180120759a40240d591100b032000481a01c3d5a40c64182d41c44c44140d0340d11100d400134452050104e9000c101c00140307240340008071590721702e44e41c44100b2401c688140c40c0210008440036504155040f46e0740043c20403600038000c815a0030b4544090000652050340100c81c90340c080251981940340074028608120301c64207003d003951030141940e64402508c0d01c1900310b61640c0d80d041d106000d820b41d051000343e48404102d0301411249001803c4200c00443c4241c02092100c002e6095600e1b0500906006586c1940d0741c1d00064a00034040403084240c01048035403102c1c9400214060f142441000c3e07540e0500101e102540c1081d200385814400040c02906c48042c41c4108000030402141c4c11030112007040c030f40021309590030440c2150b00d00910040e669641400071034402219400005010f800307001311f6001c501c6071078200d80741d5005000c0b0016100940030040040205140c034034050040140218142e900d80220120640100c0341c072542e5446918401f4030740d03d0302a0ba80001ba07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 439909451 1250 439908201 439908211
    0xa02031e09060103080d20030618060d060902011103070804091118010818060115021501060c0204050606040902190f020a050c040b0102160603020a0f05041809020a121406 75
    0x10040850800000450715182e0500000c3c24a000c001074114400c1519030040c540c0f01d4000c0540c0441c20814441201c60b0f500540d01c440c41a6400c901e00c0b03200c0600500c4003801074400070081c11407143d280c0d0b241400390000032070581c10311140b40305030003642c84240010f10303016224231500d640d41c1d41000a508103e410030b151074262058240003a0700c081d1005010800d2118090802000503503519407003000d0304000d81d440b0200707805030100000304c0d5034001c1450080950300740c00b80e4040f40a41d0280e0800030340248668000103540310796000c05820682d01564000101400d004d1905841c0d0004206992003104c141c3d0000740c2240300c20300b4196108400c070000440504c041c01804e1004c1d201c11b69107140c0300304da0a01c1384d56186a5030f85640c0c001c102040a009003160801200c9941c1d44015009410000b04000441c4000090081e5540301e1422541500c10384840d44420401620220000300080c2404980046c00e41c81c2c013080110481c215015050700c40d03280070704e92003401c100c6c2038182203010b40 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 439910701 1250 439909451 439909501
    0x90c1e07021c0f0b09071701050a05071b080f121302011d01051b010609050702030a020c0117010e1f0b070c1a041701020d05101e0308090d020303040305060a0203 71
    0x2a1000006821408203d03140340c0082d0800010f4448a07201030800c040355101c1070100005000b00d603860001900880e124500b561000c00141c0e66030742054407495a190404080d031188005c0583c00510360602600012245441c01410314080482540c00d00209940388224040c622000310115a0f200e03401064214051032040601c1450f10000390243c0900e2080c0d10700d03401d43e090144204202540b0800c0203003c409401d0245007040003010303460344d126056080040c020120702c412503502445907408004d80e80c039024100b40e8a031260102d4604005001008030280e5905419070307201d04545641c02410b0844841c40d5500320a1030003441884c0c50342d01108070f440c0039900d0701744170034043c500740c404030b80325500590114400c1084250080c401c0083c1407004520349030074040d5140084410030140c071400c1d0052900d8501e4a001e06101d8080d501c0004c050030805c00000c1900d05050081c41c1300300784040c0889082580b030780d55960808030308803458498107901000b0044403c1c000044812100e40c028 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 439911951 1250 439910701 439910749
    0x80c0f0d0504180b0616060b04051512010209090f0a2c0d03110a03020703090f03050d1101181407092406050a1b14010203090109170a080105090c1e0702 67
    0x10119280e801440d2481b6803070002d0000c0101840f445402031828604020320400c101d02d000d0358140c0782461404040d60003048405002030000d0014801c5402040d002006881e0035918038a611100010040016000c2d079201c480800d0300401c540401c12088500813035030904c96481d00700c05468446450414400c0608046010900c1042c010403600484010720b8050398036000b0341402ea4820f8000d80c448400022700110010074040c0c0460041c130a0b038010b568520181682029903402c2e00c4821a4903501e0b6401d24070000c1c00240c102c2e0104044200340000e8404c00750ba40c281e09811035070860400d441102040c2c842890031201c40740b91002412040c1080350070f0080000b401000c519100414000c60344100e4400c8090209450000079411207200095540303141045d08030740a040d0a4100320740207601c0203204a208403a40055601c1514295a05080d580c0380c07204000321030402404907840c142c001c2207a003800311000000306d14808068001166103c2d214414084001d40440648030841111 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 439913201 1250 439911951 439911971
    0x210d02010b1f0c060207030905090a0204060201050a060b180321070b01060512040b132112020301140135010f091e0203061801150909020906030103080c0f0d050418 72
    0x1411002c620f640050300140c443d001480d0940d0340100c0d5030481075100c0415001c00104103440d800400c00d80f00d0f150300900998559580c03440a80e0464041e00300010b03028400c51022480003101e060b8040350040c11520881c6543c4500d02070024960140d403d0104001015000e01c0545e0005c1790040c001d52415034981300d000750010083c1c540151005000c1ca02038008035411100f05040403061a40289614107000340001104603158502c41c4548c0c007262042c810010081458401d0b641250200c0c00030440c0161020011280380403804407000505861684941c510700c810311540070b501421000300c2400d035042c408403200341041640320010f9581001e288410346a410100c0c8176000340c040c800540c0304e864004c0000c00070141d0001803815460f890340002801010402e14060601058a0303030716000351a07052080036407140701c0d41141c00180800c01000003642c5600185442c1c9400010b41e40c00e0b4480c4403140713007406420240b0b640002ea01040030b1100b042040328001e514070030804108005100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 439914451 1250 439913201 439913207
    0xa0b04080c06030103110909011407030203190506060a030207030912060e0618150402030c03100b0f0a0b0f280f08180a0b09100e030403110a14210d02010b1f 69
    0x502c1e01107e01132031104000c260204070035049114581c0300e2480da10f11924000600a000307420031100c0d80d4068036203171741089071184248201401068050202c514001d14140258007035482808201c080020031000011303409410440c00010380d2160070041240d903203450801d0f1070140041c0814140c1042840700100d500c4002820070103210340d605c072080040d6260f00010b4100240d2444c42030301802640300808805d0509d82c1301c01c107404001c03600e00d0344014485090001180880c0202c120a56082044681c1e2030b414402400104d0300017400c901091020f90040d202d107401d02ea030004c01180c1c188800081d800e03081200d09620020425610000e5542406040d82e00d6604504c00b0f422203040002064980f10203000e4814080d01a06051080625405186660b50720511082e01d0201e84086160800d2510741d900e9000c88400007801d00d240100030781001020007081c10f060f00e03e40f4a003c109550309009115110071011160000204001d00c5030620002c3c00c80042c3d028240d21207500c46c10700c01c41d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 439915701 1250 439914451 439914473
    0x2070b1f120206070b09010903020105010b0f0d15030f1a01050d02090f2e080706030e150604090b090d120e070905130b01180e1209010f020106050a0b04080c06030103 73
    0x104007200034200ca840d5001080d200d100b0404080d02c031084150801c00440310541241920743d200354001c002a81ea0f03801c00d41070340d00444d100703221156400c122005a02c03445400c41020385075001010300c1403030f960355502e48a202820208485211041c42e906694010214205d0b006002c20b03118090381114543c00504d000c50300810000c8035043d03d00c040b85948807604202138041c03159290201e84c0c010400214109181c491103410040e1003243e10119180c5d00c039000d2600500d100d10000c2c810005845601c0740f03a00402001e09400c680c0d140307541004035021500060259005070060302e948840008024521820054054091418801d807070144040000341407088980e80ca00c00201501c0d52510744550822403000507101c800001e00100d24035145520542c891001c0c54020004140c7e10000d1a895820146440320458000c0c0119100e9501034204640004924400041c0300ea4513980058415120f40e00204182c0d080490203200c480302c100301070f40303000701d040f80d6090456245684015140c9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 439916951 1250 439915701 439915709
    0x40317150a030b100e13060615090e0417120a0f060e011e0b030a0b0108070c170a1106090304080f0a0203030d0e03040f0308030f150d0314090603090102070b1f 70
    0x140c1ca10f400101c8003502100301c82c020782050903440401d405d000385112041d10910382c095620782c4c60b0442c0090007011a2400401200c050340300c0b00c9d81e6616204842403203042c018420758103284c1c03400968100c40030817801082d00013568086620b50381010b800ca0012112100002504146025418083c010f03426007440d044980c050b20200e00501000c10548100c0e5140e4070610080c0b0011080c80008601030300b00c1c4002d1a001c2c0d1320f49083e9590288200c0301c10000250140510181e0200150701c0e05001e001000805020300b000f038400d070358002087c0d2078500111500d4400342c00210b020311200d9000d11039004450795020089c030818610741c000035100d1144d003981010490faa02c94000045005000791401000c00b51007401a465413420301d601300c2d900849944028802440004c0c44039822042c1c0403031703d100045c0400800c0c80f056039007500d00b00c0c1c40001c02c030031415040c860036070255030f0301d00110b21881c080ea001688540f410700d003111150070040c6c080c0300d0840300f00344c150035440034010f200350461b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 439918201 1250 439916951 439916963
    0x905030f120a0e0d1415100b030a09051b03060604060b0414030106030c1805180c04050c1b101508190c030803040f02030709020a020a11041103040317150a03 69
    0x20390110041a100554902540e50f00140c4031100b90044c004c56174424084c1c880744c0b5050301c0f1401c0c0000c60f8503a201c042110190026103d5100a001c4007a514000d15407000170700300c00049003d01a1a81450455038229050400c04287c0440c0c42504003840701d280c2024044d1030500103642009507101c1d8a0082e4060401c00384010411400c2c6070303401b5009207004540040c022100300340c076540d2070560708800d90f0392144458100340100302400505413410704151502806007414003601f0041201420300580040c0c0c2d040006e10500480d04403140390481d413040d0b10001880e071043c050b2007100a075000940c038002a0900c885080003c1c1a000c20006054a0141e40012074001d0515000124081d00c1c0c001903d40100801040304201c158544400d115008a007252503407595401c8000030307881030350f031010016003080f03564800059040d003a4000c6c81c0c00090001c114400340440c418426081254140c00013000400481c03a0081c0261086030801d00328109407500000140c01701d032100019200003045 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 439919451 1250 439918201 439918207
    0xe1c03090503040905041a06010f050406031d070620060103050c12030d050a06140306090c0d14010c030c1e0203030f070e1f0306121a04021201021201060905030f12 72
    0x30070100307100700c9000d00351440007080b280c1018201940c210400085901c1e0400c00e05020506e03940c000c0d1801c0302e140d01c03ea502c0f545042e0404c0d41c02c41c0a1f0515820101601488010322480031a040c41900b0140200380d40b141c0c89410300450040e0202042c0c2030715200d50b00400010320129801003528813005070706607520204100501c020358035510942d000c24031201d28110a020fa0310116410400884103655a082910800a0708040d01d40d002581c45160b1075101000c1c556807401d002818620147c007407a1000108040c000c1040c0c2510417241104000aa8642010740820703041000c0400c003080450416034007203140c40c0c01035034901c00a80041085410070000900c8075109422208011034003800d041195111050003001080748001101b000c40c1c00c00c0d402080f25001c0c2d05128010a030010b00c41d1142d000405020b4425503c081c1040c0d800210080d01d1a840020900041442c500144224641503140010042600c6219003150348650044038007090700c04000500110300400301d0f06050f45e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 439920701 1250 439919451 439919453
    0x9020f041d0114060a0509091b010e030a0c0f0f031a040807020d0c0501080c1e07021c030c1109040b0412110d020a0c0803030403201e03090102010e1c0309 68
    0x49600d00309a494000b9801c040e403012078021003590040c0103950940d450b075142c503141c2c0c0400104450860340c0c8281ea0303003c910390022040b00f5070883c00c580b410605109401031400c0307020070704028030100c096a0008065404104a81d0700e031742c10100825032038202064407030071543c400601c80d0002030105a80e03440500450107100180045465882c0e005100003030049540c60551106070340c41c8611404034841500184070304e10080100c03481880c0c2c005007014520064817080e0841d801411041c0e030085201032101005200d142c542c03001d0305001e9201c00051486624025460103080c3e41f14501071803c2006020010b800c03008940e4000c0c0d413264280140d00d0f55000304440e06444040c44078941d22030981051815078002c62021100c0d401080d91003130207a00d46100560b41e11003910001c0010320070080400d89604e0507809588003144d00c006072403201e8202c500a08004440c408400f02d03039000080c19841660b02449a100412950340c02b03880e2590848140002007855048150149611883c180d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 439921951 1250 439920701 439920731
    0x30503060613030308040b071d01081902120114010c0b0403050d0f0501120606141008150409030e01030b1813050c12210306061b01230702010f09020f04 67
    0x5080706419a90b00400a6a20f0800800751913090364195012175090012844040c0328240b071302d07144580840705030100410140112030610008250801c081645240b86441d911503000510810102c4e698901c4035504008a82e20301d45403001d44d242c180640c641c44517000807a405060396000d901810196101c009101c0d00e180035000a201c1104014038000c004160061074255101045005020030400315481d941c90800071038410303000d07682c40300807404c5075038403280300d002d81c0c580c01040849501066058080420140e4505800407004617a09512550f0305503454803904024410440701140551501241c5c40c28401000e000301c00b0710340300c0a00700d8003442401c00400403210030140c0503000d0703107a400300c501d502c0304202da000c0d8100112148010300c020340e070074003502d0050000900f8185803524154035458031400b440d9101c100e554864500c00c03e040c41424882a503c0d1603504060154a0040c0c0c000342124004243c0301300301ca250000708400740c2c40b80a00320003100001d0b0340000710304800861038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 439923201 1250 439921951 439921957
    0x90e010b0405010608180307020d0807050f1b010314190c170f180609031903110a0305070216081b030c0618011e02150411060a031406041401030305030606 68
    0x2900300e03003800c1c0005541d80d804410310384103140f4006144102040e06c9000c940300d2140002c046d40c807071280355468020580740c80080c41454401d00894007a01c5201c400a82481c4640001c01c802c0b0b0714000a0700c0d40e55816006982c0d40000d0313200340605618001c611030308601c914208080415580d5280c4558403409142403d4542c10b5022150905180c403400140301403104560700000031110300d188143c80040024114018107200001d0340c1007016548460380b000113860703026030406803503050b20a0303215410030041011406a80d808143e501d4010b40c003078a4405a150300c08007441071050100f016281c041140715101c2d21040c42620459070360750009103018004001e00c0d901800024044a52100c0c00c0141101044280c079480d41d009091200c1a098800150035800580c10402c4aa02519410302440394403a1040c0b840d103041c000070001280c825005449407101081d50740b041c0152007613004848035071018085a06200c020b020b280c400070644818070006040c400040082109a5110416 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 439924451 1250 439923201 439923221
    0xf061213080d02040b041401110a0b06061b0c0f0f010f03091104150e0c030c161a09010f0509060105030706050d1107060506100e1c020f0a0e040203071e090e01 70
    0x20742d16035440d001d05c08815809445103180c1061020303400e80b0a94040e041503c0f41441c3c440140055000c65141c2d43e02d982c200809156203c0d034104140c5141c1d4880c0500e00448084100042100604210502c4202e04940c8881c40c0301e01d400016083d0181c0c0e1021016075005001e00d8003182e03a02c50b600d401c04d04c00401c41c54566000d414251010421f11030341036007500f2920004003e040c1610351041a1203d8401030325140a8010100310440b200400c4a1005031503c0c0328150350281ca0f02d51900b00d8100e130006542566569464074540109103c590217001d80005000d0b025040369454080000c0e0388001c1482010280130010a801c16500c0859001084149080e00317410340d03604130740c034200c00148400c6035114441d0742c02002c42654181302d50255195200c02400000705812050003c1e0f040c0c2040e848226800f012a1082081c80d4456055500c02400809a2403029080610405d400e0508540141c3c54501034100400030078038000c0d5a070400c9611503000021140303d05000540503180b4111 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 439925701 1250 439924451 439924477
    0xa0c02090112021516030f02030702030105010605040f05030708030a080601020f0d0c120e01120e0a02150a02240f270c0a0f06120c18060e0f06121308 66
    0x800040c04115a03449802c00b103100f01d910b642403800c4082509801d0082d5411204003003000708001e40028052005020340f0030040c0100c904180d1039600103401e440d03090b004000000c101080400c0900c3c6000f5040010b0641100130b80f040b5410510801d50344d000c0c9030031070f2040280010200b000d0380d0092041803002544201642c918000181c405404005203030b50071a0926000c14044120703921a201007001c00b03030141e6079a4000365184010b42c3c003800d20201c0b085440e002d212400310060761307070203440c0065082409d0103d803505014100641050860b000301c44034182c02089004110b5545140c46511460100014138039498061010001c0c0000000070394100520721240005400000350300034000d4030865040040701d8585000181ea42994450140800c10307900210301c24032917035003041c14040058680094003c188641200001c101e6500c0400442c40f40940c07401142800c0e03403054641003080d0b841c246800e80e15001103011b001300520980346443d8024424007008a0041101e4244581c0a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 439926951 1250 439925701 439925719
    0x12161b0e0406090c090e0606010c050102130326030606220b0f070b0702031c0e030705160305011812080601030f0203090f0601050a0e010509040602070501060f031401050603030f0a0c02 81
    0x31400b2401807416400c1030b0340f41c0e13014000010b0000864041d500041c0d42c0d80c006001a0b8071084010b51f280c220014045a040d5000c3c4103406406000311342d9800194003410b201284545840b8003030398040480b2080c1e0300070010400400c050ba03281c80044410f001038500724003200440403216074484151303540101c000d0f800b000603a082010700d502c0203403450034002c40c0340d46255128400144e1781d0b48204480c134280c51108044100128100c0d61043c0c5040080b41e0690740b5200071030b03849600703000400007998103c54001e071090041c09002d1280303241803507206040d050204036640300c0300611001034285004011509001a18a1f442030300f1141c8480c001c000c00b0364076810150455911103164100c40c0150b48030f084000526441e1540c0603c0032140703803000d04041a400c1c2000e01c1840c0f81e0060080c0c0d0059000c11240000900901c00c020050440c00d030100c14050442c40d000e6000101d0741c1150400d80c0c102818000c59540102c216005140000d003801c0e81c411100d5400e0326000d21844c8043e61224110b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 439928057 1106 439926951 439926953
    0x103060b19031e210203130b0f091309060e010606020f01090b0103030c08121e010909020307060e0f040e03090414040308011e151112161b0e04 63
    0x2031300c1580804080000c2c080c410404d009038810044c0e00006200d42001500c1900310301515090b04001d1501c03400d00026226400b9010895104c1d504103c0d004100c11065840200401d5000030140303c3c1c5080070910500030f10341841407102600408246810380c19041c41000c1d603490748100c581c1626421910201c50801c0034030710880300303110100050a00301010b103124501c0b40c050540c201424103a681036024041c00b041e44005005414043c0d02c5006aa000c1903a101b40c0b102480c1521881c01c810000450a684d90b82003181c0151a0800304803071601c0100041c4845d44041d40c007072150301400010051030030000c5030080e0001c1c04290040c45075401e098110007040e248114800c800035101c1444480381d8883c3d250b00e00114006800c243e81c0e07001c083c081000d400c814010f1300c0c1d0401c00c08c8000d0314501c00f00200000d114580c0d01a901002100d500c0181c3c01400320100003071058605 = true := by decide +kernel

theorem cover : BRFrame.Cov 439748201 439928057 := by
  have h0 := BRFrame.cov_init 439748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 439748201 ≤ n) (h2 : n < 439928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
