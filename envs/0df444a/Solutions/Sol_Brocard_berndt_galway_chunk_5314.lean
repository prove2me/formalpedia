-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5314
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:27:56.068437+00:00
-- url     : https://prove2.me/submissions/9233f3bf-fe98-4977-b6f4-e69bed5249b3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 955575539 ≤ n < 955755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 955576789 1250 955575539 955575571
    0x20a120f0b18090a15090201020c0901081b0613031b120305180d0609080d0515100309050c040204031401110702371203120207082d12011706 62
    0x1419404024024648440c1344103140c1da04e00007034994414921488004540020b21801a2000900f44228405420b100d61000c80c014081040c5c0800d49401d0000300a0380703c1c05001c0b410000c0344082c0224441000e5160000d8000000e104102d007480118408408140a03c29102d01041c1c001460065000e00020002d2111111442111401c843ca49100030603c4090510503a00c1d5816281100c0c3c040b0b480c0c00c0302054800300320500d40142034225071401c0c560550807901c6400724500c502c240d0341020800d130301d80c80000d00b8420b060055600b0454003410940d078650722420107040c0080c42102001d903e61800e0017081400000d42c090360483d0b0350060400808030148541009004000184042d4044d0242d042034503800c0d401d03c00000402d00c070054000c000e40b0f10709020f08038400c14414075030310f103004000d80340000d9081c60889046051241005400d03d400c415051301d107020b034000e91301c490000000c008041c2202c4200e050304a481072090280d04c040d954910340d440c1c4806480e9043d00b8a91303c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 955578039 1250 955576789 955576819
    0x8030306060a030605060d0e0d03050f060607230708070e0907170f010501080c0a0608160302131e140d021e0121141807090c0c0501020a120f0b 63
    0x300a1442030f071074007140950700d410000700d00d0307800040c0c540c0d90a6615030796900c54100900c01c1c4108520701c1c0c201009140b404407a400c00d0708800820b07040c800c142c00540c1c2c82c00c00011001a10b20301e159501882d039000f0034080c5e890759402c2e19016000792449120341c0002d07140c0780014414490884d01014208403031401082c7c2240000c2ea4205414034081e0044001280c4024400d2500801e01040107100c05c044c0002480035181c5140c1102c8100301c070b5002045070802684082ea5082c01082c9401030391240205504d814141003900003c01c1d05007001c0000c0000c440503040d08041d18294101d8088000c220340030007030000302c80f0400075003290140b000115400440c0c94540740215042c100082ca0068031030340000385410120740c44890b02ea450882031011600040e2065002244000345d1035480480500250340350118450f10b08441d031202c1344c0d510201d00c0341c1406018141d12400135903c82e1110000505164507501c0300f00754042c98801c0300e480020040c058208500c1c400342c1a215098141 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 955579289 1250 955578039 955578049
    0x3110408014508211b0703050909061206041208070813060902040b0d08031902090d290c0a021c050901080c090d08030a0609150e1f08071e08030306 65
    0x4506a0b40f20078244042c41000f0000480044c01010314402902c1503e4100703c0c00040400d20411114046028082d20001030340241c100d5118000446200b040d6590300c00024a42540a48407241c40b0b0180300180405c203c540e10101c50900607907103a0002e555100c100c12a18858112040c08455148010450201d00c00d940201040c50025001040c0544800003103103800c1c01e0300703004030b422101c0003040108200d2210034110780c07020400000d6103031104210000b4085907a085001d8103080c4541c8209070f010300c903842543c135685080c44200203039150162528005401c031a801c0005030180c60340b04140d000c2c461410780008105170b203c650400314000011641d01c0300047c400042100208001c400b55a981b001c80000d00d4459013041c0c1e664540300302c01401341c5079160712000c0d5007400c1100c0c1500c1100700240c010b06913052241c804109030b455020482000441440040c90210280ca010444d404c1c01315800042c3c0d1904001039030718603020301c0c0d0115420414071800c003490300700b4400300b0118034003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 955580539 1250 955579289 955579421
    0xf1a0f030f01110a030605030a050717070f090c020105070215010b0703030e1903021203070c0b09150c090411160303020f0c12030a050121020f010311040801 69
    0x405021104049081c00500d801c4a240300c0700c803c1240d01c0401d00550301503050140314042c182c15406055900c0e500c2d51401c0d600c004501400154400320980e0303c218241c10000000207013042d03414984525940d150103401481e90303403046401035084c90006162a030001940131341c0c1d886086201c3d04643e00c2e008251901f5008410f080781099220108c1040c0d0b19001c1100003501c03581800941e0141d1854600030b40760403003a0404241c144000c0c4100584030ba004a520505142c100300d03520520707a04d2000d041d0826000d82d545070144084103060120740303402600035110940082c0c608214403101080d4501e194090707006080c040c541900581e500180c403a80281003a541415111800d10700301619107030520307049020b0f2250032007002c0704210032150280a5140140809145411604401003089010046400c4042c2c065014941603042c3c607407080d409618080312101005480d0742e00d0305a981d001e092199030113035444401740440002e103881c1d918102d012040300055004441207403040c02e0102c0c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 955581789 1250 955580539 955580569
    0xf0102060a050a09061506080108060c16030c02131d0327010903080301180c0504140103110906070807060b1f0c170304080306040c2a0c0503150a0f1a 66
    0x610350703030318130700180490041c1c01c030056a060320038602c0d500b00000100030000c160300c0808140e01c03010a010100c1e1607801207032264030749010b444030003903105c0c2820350f044030300164000d40180c6075018000440f001648441543c40e4100242c580d24800c000c9940d03602e0040a2015403030a01d40c038000c0000303140e000d040700c28a0f07006050400307030305540c2d446000756500b09a001135844200307843e801203070300d10070304c6400c09500e09420401c0c145030501410902044c01c8010369414940c0e170b220011000160001518003490000348155942c201a140580040c0c000e024115a03203070402045c03c1442c5003690300d0f0108566000007202222505410445544502010035030f586e17003104141400c04d0b040ca00042d4402c80c000e2011590300e040100602c02280d001c2e100090402c0044014a03640e204421600d240607466038100b0a408403481c1000381c804401a0312640d410300c1402a105d41c00036107100c840f0320442d410315041003100c40780100030007a02c0288a00343c00d9452512145401d41c98010030301800c2c1c0c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 955583039 1250 955581789 955581791
    0xb040812070f060603050f0106120b0118060504021318050705071b180605010e0d081b16080a0209180a030f0c0b0106020715020f030d0e120a0804060b0f0102060a050a 73
    0x1005803103d10440b50150820ba0321604458000d507140e0900740a86002000500b061081d2045503481303103007030030906000d9441c80b0414560704468012341a00131a01400d001041155103c000b44001403010100e441903640b41840d022081000000c1807054501c143e449885003032070142c40d42e03242e610080c910001031000240140020490007800d070ba0f007034078022a10b08000b840360f0809001500c40740032500f2451141e20010f0a54000502c41c2c0162441d011001e800f0f40001c81119084a081c8500f44a030412600300d400c100159140000521840c072034025150003070b0a4844009540402c100b44604000991040c6402c00000b841040490311848403850030755500b02242d540c0c401c02110a0b848840140d01101d018002c0f40d11740c45032031601160500091100d00d40b02c2007015100c0c010343d818a6030007541d43c61101d01c45002402025004c8005c18203803507982481c24006441d0400944040d9038161a01c20126200d0400c084401180b41050300203113016951103209002802d0001c0501c040a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 955584289 1250 955583039 955583063
    0xe0601030c08131e080a0810140f0405090f0a0807140a05030403110f13090c14010914120607030e06072c0406091112090a020a0303050a14040b030a060b04081207 71
    0x807461000140100103620340e1007401506100703004014450710f40d0428445190038202c404a43d0b501c40c1e11614ac00c2106031030220301a0344401102e03050070074001148026024015816003085514401400c01e01d1140d4149131181d0305042c5a43c0d91000d40355030003000740d0303c02c110030f10208250a8111a50010051090042440d08404540e10006c1007035424043d80d154140e40d8204400701c143c4030054010321607280119988140000e040c0c0d09140f25000c40880301040f110302d2a07d0705c00e48501d0071100c0900311102c50070100401001082c0da021061824050304e0f01191010b8420b04000f441800701c240c4429030500c212100d0003030740c0000d88000703078060783d15039000881c2501801512070301584c00360580c5d1aa00ca44800d0010102c004001541941111402000503030f1000c80072010b507a01803900949035402180d0654440740d003840254204840401e0004450030100c0046108000760b880c180013a41d954014540345008034010995182c110384c524000c0c0c1c000040c05000c59901941140c802 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 955585539 1250 955584289 955584293
    0x90618090f0f0c0e1509060c030307020d030e0a0308070806010e130c0e0f06072604121b0b030105063f010e040302030703050c0a0c0e0601030c08131e 66
    0x407501c0200e428001d141d1a8090015408603500c21100390796150f08200800310941e0740011807554540c00d60142c2043c0106074140316456803020307501d8000224048035900d04003410040c1d5100c8445545100003400c0c100b1241110300049010110542c0c10b40750000103440300c0c00240c984030030007080c0c1410000f06520240d00c641d40c03408010342d00e25405400007203004c0c07080001031204405241460280200c5000044141c542c1400c6400054000c030020f1010446001000100b404403900142c00300004100481e14581089040011900c500c445410700124013000301c410040900c900c03006090140010404d50401d075000b402c0032035145006001c0c03000c103d00b068907019141101f01c800e0701d9403043c200303d103004145021409440034000312121850076643c025524460180020b04201d004034591981840c01c00500d4202e5502041c0c044856440320b00203d1500030884071280024240380350815220b000d92203e50003501041100c0b1071100f100d8480043c803c90410030b880259001d40c1c40500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 955586789 1250 955585539 955585541
    0x9020415030b1b0301050d0b1306020f0901090509041a0903070204110901030b0d0803130305042403051003021809070f06020a020102010b121b13020d1b030c09061809 73
    0x10354400c1c0d032180c0d0b10741007070f0041d1a4032281215039014486400c00050140d60f454214101c00e49503c01c06400d42603417000c400c1c0440c44031080c8011718150000c204108400d084c4005000186000c0e0380e1611626038980400842c004151806442007207000c6640c09071031036038039205601501c241d00f1245048019404141194100300b42e4204c0c2030804540c14003150b0b03242c00b030703100089070842d145050f410f02a11076140b144005003d031f100c0e400c1c10f019403004150040d0103850007044140c0341304d07c074401c00e810708989250000006000007868000000e0254011030010342c1900c1e006010002000d44440c0e139080c2031100500b001100e4401e0020001e500008149201c010384100e9001c0e101e18201c40c0b0001e400e41d80504590382c804c00000b50100c02d07003100050b85280e1424900041030005c91444085506580e0440d05551502d000041c0b8155681450300301e41c0c0014051900c03500b0001400300118110b07030030100c003400011071484080203098400c001080070081d80c044608002942d5801c400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 955588039 1250 955586789 955586831
    0xe04050907120b0a18020a0b090a05130c030f0e0304050d112806140f070f120e1905032d0a0b040201030c0e01120c020a050a060e210d090204 62
    0x380d6070340f00c00080142804031405003510107a0b01d000a60791803d40c03a40050740302d6045024111018002045261032039445d4400e000c0103181c054241d40c00c23281d862020001400360a0210340c042410800c601c66219214402c070105200464080c40c00c0c0b0782020200301c1e003070000500c1a9902c00da2104103c00340c0e80c0311080d580b180400d488074103004086080c0d040040750a668090418440c111407440c12008046003100c10a00184002550316505481d200982e00c02c84080500000701d030740703642174200350802d144541d0030004a62000f001c022403180e07400e9400c0640505505074010041c005c06001107060311501095058a0f00f401024400c50b404d40340c15030301c4c40d040e036003010180e040c0420341d40c151240d1540a0400d20b02403034002d02410010b010b80c07a500c00003a211b04d1792003859003207440c824030240d907603075500005403400741c1107078203042c4084e114442d600107244c002c4004411072408540740d0481c0321030129084504015500d86150001e2180240c02c0e6007050700c59000035005c3e180c0304400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 955589289 1250 955588039 955588043
    0x1e0f120702060a0507080406050c16030201020d0605190e0711010911040f140612070914071b0b01120c2d0501030b0913050111070510050a0c0e0405090712 68
    0x806200d140c038440003840d060300a00f40c0b456192800c0140a11181e10035621940250090000b0980c2d8990501034183d030310400038210010060458500f04140c0d0640040c1b201001c0344005120480c2c0300d42c10000b1880b00039155204c4010303800000c200c2c0400d01485154800214204410410400300302c450a441188800302c6041710b03908141c2c4854a440c2c442c041c0c084a1280c8204451071002541c500841c4020740780622400020001c1d406802040101c0707406803880c03120a1109483d1700202d162181c509884040201700c0300c42c6030b098446190b003410080307581c10500d1482140d10740081c0300e1401d040050255040c08140c80c1c08128091001e0300ca1a800d010a200c2c520003080005400c01c0b881c2c029040141014200404444141d80c1c91044a07080480c102500310b240302d11746880360040500075000c0700c07011004100035052010108403d0058811000244060340d1410722030000c686003c0c01260208490303030031108031400c183d07102541c4000013074220340d14144c41e4184164500c0e508281 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 955590539 1250 955589289 955589317
    0x51b130503010c052b1b0201050f0105120d0503040303020912061024050d020c12040f0e160e0d0618140102070506040b040501090c1212141e0f 63
    0x30031090400b403084a10200d00c03807030701c9800c05680103036449048110b0240380d101c040c0d1400000c0d0381c0c1c000c00e5000c0c02640d8131615180558030903d0602038083e001c05c6580c0440d100808000088504240301c43c052024401130140030f0029490b1015a00c54002a00940c1055424410180540c5072403c5482080b00c240c00140b43c1c40c83e26089075004c4011642000c0b00301900524102a184408803980340428000e0801c41d4a501030342000a0080c0140003010443e84a0040c291000f0451240100196051f03c00f0843ca0551540e135008000340041e2488040103a0000c0b207800064440d0880402d4080001c0118220324441d4031507030103030380c0107102d901c855601540e030000c20018440003401c650b9607904001d41c01d10516884094407890b000f04058141e0981c50002002c1010a51003104080d50210f87c219029807142c2c401c1800f806007050072102003600300201d4005c940224004811000d22001c22403a00700340c2004030780100b645034a05001d500381482490f49186001c0050043d031240015 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 955591789 1250 955590539 955590577
    0x90e1b1b0c0307060f120f05040b040210020c031c210501081023040c090e01020a0924110c030a050d021204121101260403020c0609090a051b 62
    0x62a41d080900e0070034102d1203940094401c00c0340b160005543d103640c3c0002d0402c04040766020314008054902a1105d1030340e1480c1208000800ca4400c8105024030b0007901c00018024041d031090382d030b84c2c00502c000c030341c0740d40407007a580241540079207855110b01c418641011502440200103c0a0558010b6200010f450700c0040c41412420001c0440610110300140b14646900c4c1d44412038070801101390468400703407800103040c003001c069610003c000400040110704803403d5414001d410403498000043d011620002d111641440300e4042140c04091701503a015040c0810750303090b4411189403600780261500405580d9040c06040c100c14001c001800380d00c245140d0003401c200d0706204d20707001c10350700344814084c0784001010b96282070b9000c14680041001c5400585002580b4010202615458440075404403540551603004030f1083d02155101507100003006254052143d5094204580c000052074a92458121941221b00290104940d002140f042c580d1907011300e60700c070041ca0f0601 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 955593039 1250 955591789 955591837
    0xf0203040c141806042f2206020615030f0a0503280801090b0102010f050106050909070e060f1b0a0b0f01090204030201090909171305011b03090e1b 65
    0x644000c0da005021141252180c54040315054100700c00b501c0140180e9850a58403110f146010440a601135400c0440740c404c00d80c50340401b0f03a40d0203040c5185d458205181060321b41d00f550b0f0000d0b030940d6142d4019129542e40d01810307228410f144480e20b5854807a03641c00b1644c47d4401c0c40007031040c0b0f00501c05565a030884c0200c8a8400030302c1d80084590030500185002d12303d81c000c4443d4195010800d0208490309402c00403400352008142da003100c1da00d001c2c000580710345c1020081182c550306030784540e01c90750b0b0544161040313840c21184a411083c10800e51091180740c0780104408030211074400c0c03840d0941e44c2014039040310020308594100c2420b0038050b4030071021704802c0c01402200010340c50107055600007002c00281e44109155140c07111008420814400608220014140582a1075180d995004c010064152140601060100341194441020307c0c1c1911111354054450580340d0f454001d2007120030340300030810500381410480c90052101c203040100343c070350b500054a0405801035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 955594289 1250 955593039 955593059
    0xc080a0207170604030c0312060b1206040f06050a0b1308030a03050603150402030a03034a0313050607081903060e01051f0305060f040906050406051003080d050a0f0203040c 76
    0x2540c4042c0c5511240130480020b6210304800c00c41580340c40e081840c150244403010107002d40e1381200501d5400865411403c5100285036449800304880c14404c00b421062010115115402115000440c8441c1071001c0f503003000041803c250039240c0c200d1907681c3d1303054103815a04201d02d02c8000070344400601c021840c3c00c001c41c600098840e42490901d0500f50700003a034070042440010f06158403034030200c0110703d8180b16500ea051110f04101525818619404424415124a0960880c44000720302184400106880043c1c10300c1c000e070424a414441003141d5070300251802c0b20604820461507003800140380c081141d0b200319440c0424490b0403c5820340d04204160032444c000c01114050100d4170702e0b1581c3d071012220190400251035210000401c5038034040380750300754006040407150803c109d400da000a1142e40513840070001500c0301d40d090803040f46944800303030564a0502850322071464560045410200403403001a15100e10428002a40c10484050701c609040c1c8500f04030072001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 955595539 1250 955594289 955594319
    0x90501151103250809090709051e0d080c0106080a0614010b2502040e120d0608030424020312160801050102060c041e05041104060f0513060f0c080a0207 67
    0x140d4148049154032041d500c10903442c55100b041c1c0c030780c24402071004070070846503000c0c1c014050794007906d0005002340240d0803c3c81054014200c2c224092042c52090451982e04900140080c0c8110300c150ad9a8011790440c00019001d55611440000c1100040164442d604e01c501d0f004120481664100002018160302c1034603504420841c4208410240c0f00d1408188500c40311108071111768004100284003c58000d03400d4844c0601c3d20f0072032300308900038000c060302ca14401d002c2c0da506c4980e6152280614494004110b40a01d000d807060040782d41e100c01074010030f01c1201c2c1000000385a240000b04152860080981100d407003509890344103001ca03002d0602800181040c2c240780181e01058401c5105a4006034503402c0c2c504080010900000020000140240b241040c4140a40e81c154006c1c49008081501040c40310707242030007442a80ca2140e41030300c01c15142c40c075220054030194418000703001000074243c140b000148a4102400c0b980300c0d55402490b00d141030940d01103900c51 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 955596789 1250 955595539 955595567
    0x1d04060c091a030405210c0616080606030703110a0509101706040b010903060e010e0d1b0809032d070905040b0103120c050d020c1507052509050115 65
    0x340c24203060145441c0c1103800414042d812202035901d686504019080c0700000849075400040060081d18024901d0040c2c400c41500c0c400703036203941c0c4807031241c170344049008520140810700c040000f612a25010300031755404600c608000c52082d005003494441ca9005002207008102d0100e90390540e820710703100024048041c1e0030541810f00d10700c424030281d0a401460f0034441c0c0d40311285405264401d003040070003164404030900543c405842514060706000140c00414413500086554080c070408280307800c030b000003222001c036420944401c40c10303600c422000303501449a0185071240c59034015580c02d00d001003d051000c01001c1000d807906001160f440190300a040005102c0450800341c1d00e10704581c3d1100050300c4542c029401598030104445000e000390280d001604a05500880c82825011080b600d00401c1031103404010403501039210081d040364040b40b003440e0111f4085010f004441d0108030140100c0e5601c201e6001501c00c00d81081e0003584072001c43d10b1903079403c140f507084450 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 955598039 1250 955596789 955596797
    0x207060906030e06150402040302030619050f04030e01030213150305250212090a05090406020403020f010518125104030e0415030506090610060c0b0c041d04060c 71
    0x10040c030283c55540d5101a020551080611503445040e0740e595044030025540070b41592118079000d440c1811020442000040c1d441c03d00001840d01428107060b03500c11075040e1544c1d20381d004c0700340045000b50040c0000e000305503070b4503201003019103909015820304840c982d0042401e28008140c461a00702404001d01c51103201c401012400d60040340e4014100c02d03681100b0784844440000411101096001a4124032400180803d00c103e0340c008206580c002c0d00c5003000046540011030b0703188140320506114500450f01601107240191a100c0f0042606084555072107199044140e0301e08105c89100c1c480e040b054068a5098543c41c91307045100c0304000b0030400d40900c089442d800340e070040000b4204040d0800c0c2c24030341d80c2d5607444805c660b00001c1e90b21492a4032441e00079505c803400e8a40c2c403c035101d01c0300080e03c01300f24000f000341914400d035620301c26100305a562940085014150700c10f2640c0900c400f19009108102d1712180031807485100d640d90415044c1001100e4004a0b084100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 955599289 1250 955598039 955598051
    0x20406030b191e05040c0b040b07140c0906040504030c02031b0405060901030f080c0102130b071e110103020f09033307051902010f0903020304090e03040e040201080c0c0607020706090603 82
    0x240c0c0f100040d00380c0d0281c00d840042543e0352103140051380041917030440f500c0d00b040882c0200f202c818480151240354400c1c101d414500c2e4136032403455034588407422410f901180c00b000044450400d80c01c4590058800d0a10b806031a02e642c6c00070741880d480c5000b280c0340d90200c1031b0307400781890a4020a0380250f81507441c0e5080754155260a4007001d4003480c041d01c5d6100000d10020610002d504440e003000050300584002d54803101040c0041d4040c440640f00f40315854078103000c01d034807045e03c034880c940d11100810701c400689006401a4011038041c140091060002e00b09644042c090000c5c001030090796200301c10504508010380081259a461803501050104003100341c00008460503041000864060b504024408030702618000d8031086400d0b090100203000c140d000070290081c5c40f008401031225490036504282c4c0c80c01030b4407804560206550202e40994007600b400d6070820111458180303810550003400e850103d0540d564401640a00c2e8100500c070350000d01d04016140600d414404 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 955600539 1250 955599289 955599311
    0x1d010b010813020603090a05150a0e01020309101104051210061508010603180f0606060e04090209010911090d081806070b15060c070e0907062307020d020406030b19 72
    0x70801100c030b000380144000004a040d07400c00700042a074881d800b20444041c4000c01544841c00001654034020f081c6c1040311240d01c80c48107000340c0348070f5100c4400404103407043d502440042c1810180c034020b40d42041001040541720022742040035801c2030010203c0690300380039442190319542c403142e00c002c009030420f18501c5c0d004503040e0440d2070915003c40c2c0780c244c07510502103a51402ca0028942048a0480010011300d500100c01b12030407a1984031000308070505000640e840040000e40c0002c06c20010b01200751184d12044000700c0500c0c0641c200078040000c2079400041d10000d076492440030a1103030758803107402d071030410605007500d00741d05102d403994944900003c060801101080107154a8000e9200c11054904030450007045409090755006405031042c41555075540c00d0260032004103c65000c0c0718003900c1104400d44814202610508112407a08250780417a444000048040b0150f940c60080b400a940611030200090070211144401410f0510b100c5030307180d003440710a02c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 955601789 1250 955600539 955600561
    0x8100902060f0901020304121a090d02151f0e0f0114100e030f07060e030c0301020406090e090c041b1d0310230127050c09060a030f1d010b0108 63
    0x40400c2c0b802c0516071921403800050f41503000d01d4000012800070307480084140811500014400005180740c1c0003503031540b042c01921341143c0a8400090ba00a40848090100070880f0030791000000000a0030010340d45028600c40da1140e009803050b038651014003200c07030780092070705004141c07030401380043c09401d60110340c4105032031075044240840312103c4075841d1020301100994451145c29078014a44566002e00440c1900029034060304c101d880c43d00b51400c0500c00c480690303085807111850607141948003010344100070001c501a01501c0035805d11900c40e2300410300040c46a03400c0920100003400024070101d201d10022442803800144100c41752000300741d0001c44e4000103008100420a0030000e02001c1d10801c000509080b60340000600c84070700310180000746511001206800740560102c8140c810503100c18800035030400054495203031100051414000c6402d02007070702620300c1482011925520311034280590303041982c014104084c411400c13202c81c2420500014105081d0f410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 955603039 1250 955601789 955601797
    0xf050c07060e0f12030c010e12041514070b01180c0e010318051603140607021507141201050a0f03030504180b09010915090905100906020f0d060810090206 68
    0x4000d101e0a000050b299841d540c071545540d440c00b070401e041c00300340d826065175a13500510100d0301c00d51034041403055059001c00d20511819080140e40e04082c00d150011154880c0c09145405001c013035a0340122044011020b0181d450050342a41c8440d890724811a00001c1d9445404249503e0245441c0c480e54028956840b003801c20700e030000701c003c80100001034400090300054140c0c03040420103084030156640060a0302d214521036483300d02190b48641d5105020b82e400700143e008003d01500613800c0d01001c5034460380c1361a0900c503031081002c3d6913050313034004e4481c980600c02940040c0140d0138070031380d000b0080011a021910261961728020101d001314003850305802028018002c0100c03171900308150b1000b00825440486d6911100d400007482220446007034030003e030100082c82d0300c40b4401d007084a90010042d024107080e03c007560006121100046078050350901c403090b042c198110282010601100d800120713981085a0146000e164201c01c0244604140c0c0070001a1100420382d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 955604289 1250 955603039 955603049
    0x703050c04031a0603100603080301080d0801080d0e010e04060909031815050c0c040c0216050a0311010509041d0c010210051005010c21080402090703091106090307031506060f050c07 80
    0x2900c494540c9130020b400c1900b0200442016402c2400c08018080c40c00300a41c103c0d0b020704121286146039441c1a01d131880240b20b003141139080325200c40f070664040c80e450107059105251080080e11a10001000c0b11117541007214400d548525030010140c20050142d51031502e20514800d030b524054816914003800040079040243c041801503803080100007031401120300400034040e202d800c00300207668070b05440301c1d51a4400f1841c0d00081300d040c81b10101003540e800c03002c0390080b00c08a400654140e886413000e903403c140c0d101c6e20f00c52469444070352035882c0b5007014042c0c5011810500020325085d80502d041216618210911030803501e55819a01100d400f070030300c400303400c040782400405002103001a1002c40754420101160703560200320203209602c210707141030172034441c44411021140710600090142c29008501102860f0000180c91210001003c03500070a850350b40d9030001c88440c0507030740e03801a00d4150070b100803a004961095085003510748941006850014141e03613080d58455 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 955605539 1250 955604289 955604333
    0xc0306100908060a0b100e0315061819140f1506070503030702071706060a0e0a0603020d14010605090702030a050a09080f0c030106050f0121140f0703050c0403 70
    0x4022052030060050320001c01222041d55004d241071074904010301005803040744101c50305042c018080740641c034280000c440240040114a950701540344820070080c0009030b03c03040c80041c08500d244141c2d00a44034669080d40034400b40c0980480d28155110b4080790240c960f204010446000c154000007075003c0b540401c5d0316503c54006001c01e81501ca07281300900715000000400011580026090003261010b82e582c001040861030169103459059898542c801c014580400010501e00d003125048122401c0c001034881d45c0f42d0009040d40c3c4024000c41d00c1c0340080c05042242d0b4001c6c4215002418141c81401080c41c0c100402074880c0700b900184801d2000200d43e9135003481c49000c501c00600301ca1021108941d84601d40b941c0d071200400300e1948603600740003020132581030101341c0301c3c941081a12460706036110784040c0b042026a01124410710340d594800c14030882000a943c50081c00c0200d03400205060043d00281951001401e03d07000b01010003081001445507460400c04880080c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 955606789 1250 955605539 955605559
    0xa170a020a062d0c0b1005090a061419050307030f02090108150a32192d150f0f0821310e06040504020d02060c070905161101050c0306 59
    0x103001d490b013900c510f402902500503030382048001d075000c1420809440741201c4059a03540c540650324242d85150080c1e000420344142d01d064107040804860100d0308041c1441c180280d12800840c2c41d1440e030ba071003540d00c400d000e400700d030079424021700580c0500020000741480e8054403c6082d2a1100902242c00c415520b50074242c50141c03405081c2a42e4203d403070b01400c4418012403101c0c000d441650560500d04682000c2208500c03d8401c000004044003040c0b0000802400214217442421448000c2c50b62100001407142d010340030050050b081441d10b8014241c10118102d9101c4802d4109815641c0050000396140e40c40501e551000d000161343c840da90b620600718081c1d0f00c01c100202110380071010b020b1103410700000443c50141e80500301c0112035592103904120544c2c80075240030b50041015010980581482d40042803130701d100c10102c2c0d140c1503403401c05104440080341d0444c6c0e212626a002c03001e142d48800031045e15105e4200a01480c144698010f94a10001c1c0803107100b024449 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 955608039 1250 955606789 955606877
    0x51806061c020604030804050f1020031c06061202030405060109090206090301092004050613091b0603060e07021f020c0f190507060c0b070e0a170a020a06 68
    0x280803901c000b030740580219250740ea64500065113401c0f601903584078072543c00c01e02055007481c1858041108040d500e8541c0b007042400c10002c0c8024105c80070440b40000c1003040100c580c0f906860460460725180041c149150083c0108080d042c00e1510368060300410a0001103440004c5090660310019400681c0f00300b1480040ca40e40708803400a030701542408c4e40042400b14103c586c6800d44d89210104600ca0074a070104411284201c1d8800d80c04020201c500000b001d1035801403400c1c6104448201c581001402e61107200754050340044000703a02e03000d050007031001c1c1c409842d0f04070301180020554911030808054114100e00d500d01c0c5078030f40c003240411841c40c0420005d501c400038103040e114410700c03c0741c80900070905400141c03200d1054a50006d41944907001101c140ea07017140100c0c0c201d4a0724070302203500502030390140b0b80c807c144030400b00d14038280e454607200c00b220010003030203030600620620041050a6100400340103100034103030541100f010703486110300b174441d6128040c1d205038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 955609289 1250 955608039 955608079
    0xb2e030b061504060f0905121e0a0201090e0703061e08010c0905030c0f010504211a01081903140d09031715040e1510080c0d030c060c201005180606 65
    0x540c7c0305550200906078660545a804a10325407160352008000b0041c06503600c50507603d02c480c140c000c0c00106110360400c0800ca03000400e03a0401080c0c50040f841b43e0340d442038140c02120301021820740230b2403a902000421401d129981100455041400030649170400003900c602540c8400d0740070303000010402101d40c3c4618200d8000c0c0824031440b0b44059000d0141071401420b500c001c980d080042400c0491021001c140340d030480380480010304c0c40c10007414502000da4410007045091050711001155032195400140924000c04200000c0c03070309840c00d0041010001040e01007503410414288400b800e400d1600060038041540c0225810420b103140900c0e00043c1c1003801e203198291030501c003124007984a50340442e00c801c4203c0d5a841e40000812004100c6074100501142d0384c1401c120000c0c2035500300d006e9030401800c1c900c00b0004004010110310460045103841600007400c0b032500f0220380e21075503400506d40100366400c80c0200144039540e14001e041ca5225141001c02115038046c9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 955610539 1250 955609289 955609307
    0xe06060f1314042c1e010f06090204030b07110a0602030705030a0f3e0415080a110421152f1b0304030c15080a180b2e030b061504060f 59
    0x9011741c5554042c0c0e001003160086c048114a00c03441400d00200081d21021802070350252030b0800e80c20305203525030f020140c0706000d402000e6034041c05000240c90209241d031010b03612894041c2c482c1135891600fa803940044981e00418518100e1411198001c00400100202007400207070300000b0f24440b030400451001a0325416540c1e1180c000034000c82d482020310384141c3c0d1094192038042203a00d07020701e01d070181d40c5003a10b00701e640c510610080203403071343ca80145846042c4007a10240c080400b610b50005c00781e188201d802c15141c6400d102d000c240181d448011440380071100240c2d0100c0f448450303d05a114283e81048480c03203071032855466110500c02c42d4021070788008048003c2d070350790500f0400c19000c0200070001c0b6804000140c1900c10b240a504098180414000d2608441d80d540000c0504007600e011121101400ca100c00194102e0000780d0800c0f03202c0e0b10401103840c62500c07001001c002811075000310700e001403040b40401c204003514141c410310f080000f078107000640100c6103014 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 955611789 1250 955610539 955610563
    0x50c06100f08031603050708160303091103011109102a1a01060e090c090d0f02210304140d020907030e010608010c05040e06060f1314042c 61
    0x804060006662114050504441c00040e260038101d40d2112441c0d100d018600003000c0802c00c841001c0c0000744200001c0000c03a11640d0800e062400e000201502030616080481c00f20750388424050a0110900c4144946001100207104d200380c5c14903600c505009004515001d002d0200000d2851401400d090400011260441c5420f03810319a40b0001c54130304144c00d1781c42c15204101120072283d0300c3e60300d5042e9040c0344c84041c0500c4201080c04a0741c0801844005056024040828941c1d02d100e56039040c940220300f00d891005081c0100b0070319500604c07422003081902401f012400300c01106860445001840284a00502d800460690440618001d41c402000e100f000341c21905075101c2c0c1402c1035641c008002d4035803503a407200d00b00c403410050840070400511081140140c120213256120402902c2e09090210700404401981c010034041080076414020510208032100303210f840d905411a070501c01c40a201148485414101c64004911800704002034101d40d001c214607100d1302 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 955613039 1250 955611789 955611793
    0x6020c01090b041101171602071503020a350912030c030901050f010305100c03020705011812030b0a0e070e1216080f0705010e130204060e04061e0312050c 68
    0xc0780c2e00d4054004502200d0803603075001c004030040d0300c0c0e52086039885950301d00c88000b1041500d5207081d849861002a03280d81c01c40c0706185000c100d8043c10003031101107040540300542c440c4081032000d03020361142440d81d001581d245d0383c07103c2c0408420383c0040d41034808110130b081e0380d160046d485040c50306010486209120010621801c60804030003140b14040c081c00800c07060722410131041c4031120038400a066544a41414141e606807580702400c2000c16003070051500c103250395000d003511188170001d0150624100002c0c24440c800304076400b40045490100500700340d0000003625052540a40401e07400703800c1c00207603d18011170000701c0c4860010125130398a80d4000c02c0d5551800c074500380c80002a604100024040c400155400c3d2041c0d100d8090100d40341070000448001030014840b65001d44901c4507400000c3c2c440c03000388041c1100d9038441d140d07044c81d0720501081e141c03503601040b00d003440715030160340803050356420742d003503903802094407503440c07010344084829002d8009125054 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 955614289 1250 955613039 955613051
    0x9110c061003020f030a03020a080a110a06020c0124092c070f0603140f04030903080324060a05030f060109081e010c0503010501090e0901020d0e060403110c0f0d06020c01 75
    0x160700300c02000e9007100c3c401c954a424940446052684504040900601607800011320400007100396000d020b42400034540103040e170070818500c41c901020980261801c80e80040e4900b180c40d800c1c0070b91503841604a0070394241c0c00780d000c4c09480303810591150001e060b65648140d00715444001c0b800f049014ad070f0344265001e108400c80303261590518895810b15448005002440034001d0286041d007204001049566a41c1e504004120420050080302041410103011000912640c0a14015000c0a0308040f075018a00710000d449440d0024143c80b40405002d0071520135031110031207a221182c8002c4000b66112030006940c008003a400909040c0034085c00070040c44294a00d02d40e0810b030150003804098800c2e60191100c0c4000c1c060540065562801840700070500d2200c00d8110785000001440e091950240c0c82c00c0751170080c24507030305800c01e005020074103500c100083c42c4d08071900c01403c41c50401c0e5002801e08400c10704604d0245104100032800d0080f654113490400190100038010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 955615539 1250 955614289 955614301
    0x2040e0106170601080717041e0b090105010b04030c03030e0f06160302011802060406110f15190c08070f110d05040317070507050f04020d060b1c020f030109110c06 72
    0x12924000c080200080342880005540f0340c86078410381e0040030652601c1c0e40c47c00b500118642501d1004006607044140c642c01c48040c241c2c1405a0100c20f030050080070700c20708040341c18500390380c0180d00c60480002c1c00e0000303101150b0080b048004490f45800c03e1001d020100010501c2500c82c014407550000001c6510b02c10140300002514005110b903000300010100c124a02c4038140d04240d000c6e400000911060010134060000851418261030456120f9140c0100084c505800030b500b4407040340351a0107020004030609852084404021018884011007180041c041d00c0000d200c03004001d0001e001d800c465000ba000402d0b0700d1a000c0170344501d103201c6100036015500c103100869101409405184405200340141d62059070300c0300180c03103407510382410866060020309589030f01c01c0c5d0130000d00704610340500c900c07002080c80c20592070f00c800386001400300d5070003030403100c20f58140104103103000785c0745000c00c0302d042d503100d0f510000c1c42941028101d001801120240200e6114000500c20 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 955616789 1250 955615539 955615547
    0x801080f0d0509010c1e0b0907091a22020304060212060409052e0e061b04030b0402150c030a030e010c0207031a0a0e160503010f0c1d060c030a0c020301060e0f010303030f02040e0106 80
    0x4030806440c8c040740d800070355138002c6000b203540c145041210359803d003071034002c503242c0301806048010b0308540c1c00b9150140183e81d0412a072088c0c03003c41d03009600050340c107507144ca800882ca03404070003181c0410521909407120b5841e502500700d138a004002da031550050b014403070f44080700e40805c01d0000704010354080080035036608055800074801e0903090141d01c40c1c80c50440c02ca80c02d0b25070210400f03e4a884660901201c22090f0207040940310091244001e036030b80800190080070b45c03070f5030b01042d110303203402c030883c2100c282c0074124086400090b024000700c0c49149c034000078200c2c000c0300715030a030381c2e02640c1c44014808028400e545004107000c141540300500d6040302601c50440c0208903100141442d101280c100c560322034081021030318030341d44142c1d030704072098030b01c800185c0f075289000b11110081d0704641c8500d0b40301003c601c1a569101c15030400740b0862000d0246000141900e003052081d03428030890500c001407c06889105c000a05450364041c0d0303004140b620109461942c607404050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 955618039 1250 955616789 955616791
    0x30f0703080405070f050607080c1c0513050f03121e1318150506090307090f0204170a050a1202011503230705062709070801080f0d0509010c1e0b 64
    0x10f240da2060480200c4e61050510182c0d0842c0c200030034042c50301ca01c665402c5110f40142d1280c1e41103020342201e0303801e07003421268440740014403596202d58980c40c111401d04402c01a4000c1ca0040988911365201da8400041e03448002c0181802146c440c2004262180c0030ba0601020b0010070700c001c1a0728900c2030414502e403095230048000c2c45000507000c91076904990760844800c074039500f1a4001c00850030804000e0003210406000e40c1d6a0540311075101058901072000a2103443d8000350800c0078a6007080b011103040380703041c080c121081070768540c15540c001030300015000b02080c00c0300440d0b06000f5030103c001964841034100c083d43d924288400f6034000d00f0a4008900e407801214a1031503030100e00301083d0f50740140740b1410405d5180c5040303c0180300d003c920041d4503540c0da40100540c1d6400c2468880c400646e141c1259606042c81f0505015042d90f441e041540b0040e92000520307040015115050400e00c1c08900c10f05c0a405c0020201c0c07001075000e00703030f044a401c0300814020761b1107480d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 955619289 1250 955618039 955618043
    0x40b160f121119060e03090919420e13022e08090a210e1f0804080f0d0f050709030507170c09010924030f02090405030f07030804 57
    0x310984036110040c0741c03140c200c940d89400f498180d4440307000049195004079600058030302101d05201080d0042022041d05a400c00500c280d402700c1005c01424078020810000d010855004240e0780c1020002d5480610f41400c002c41c135840910010303040d5201c0d20180050008641401c29400c100440620540301c180381a4011070028020340700750002d107611142500000c2000b03442002c0d8000c0c00b02c4032810050100c0303d050091a110780b02040108105030010700c101c5066441c01246980082d041c03032201200d860203009841c00042e50100b00c04444000100c040c14040c050355154a00301026114108000c0081100440c00440b0f04001e40e020b0408418945010408bd80b2101c400340d402514034400200280e00101301400503116103200d1780b182d83e107401c00300e510a11aa0000540d030043c05d0b08180c90742556404018140441c151030510041c10f03c02101c20040c2c11900c9000300d0020a140180c0a00e001d01d01140c10401c04100b1101c0035030b180450036403101c540c0d00d0002c0c807031042541c01b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 955620539 1250 955619289 955619297
    0x911041a151e0a1d0901080d0f03020d0606020708070f0e130807020d110a0b03150f03070f06050a17010608070c020d05010c030605040b0a24110601061121040b160f12 73
    0x7584c1103500f09014298181c400741001400c0100450300c0460300c58000320070b030030300301902480000340481090180d50044c00d0550013a1072864184800146081c801d40c2c804405401c00d00801c00c002028003080c0d0750424918528014961410f00300313103426115842d40250010000c2d40c800042c00207041c00d611146000b01e44600b00c89a0390301400c0c3c0c440c0400e0381d42c500103509000c00c1703644920b0b041295183c401805402e4803121076a810701040e85e5407136588000d01017a000520081600c0d403003c0048882801d94410400a5050071030040c803441d00100501c041c0f16a210580066540e2540e00f2020341d64060024072150b0b54490004010f081d89100b00c41c050360401d9140c01c070510380098000c0640d8290500320303140281a6030f40514020221040c01d042c404a072020100c10f100c1801202e000c0e0440383c031252005001d0b0382c0d00c00c3c0340901c510400600e04641c2e0005013441c03800103040750129140b5a03001c948814400e200002191204c4500512aa0841c0b07100d0080280f900b0b9065048181e41c0c03a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 955621789 1250 955620539 955620587
    0xb1003170a030e0a0203100b13020d06031515050f011710170705060702311b0c020a0902130504060312030507080103030e06031008010911041a151e0a 66
    0x10f41c40303540d14020000258541c22944556000f00c650b94440200000001d000740241c01018000b44c04980c00441d41452a5071200700610900400d600c2600280000c0c8004101183c00c10180c1003500d40d5900845201c0c0381c04401c2504160301c900c8450098100f1303d0520403060400c0545400011a035100c0c02803640f400d90f520810352900840c0074002c482c0044c0100d850600b441d4204034080c07045070b01c060916030415010560410400a111400244003a80000e000c02400d4082c00e1400140008004105814140702e00513210304010404550031800056218015105c1c40d0240100e40d170000e54026281040003c10b01541d506140c045c4042d903101080795485404080b144c99a0901000c0c1c041061408509105d00301000296808007281c845404140d0b1215000b901399841d40b40290395110036124144051301d820300c5080d90542c2d01801096068000b6004518141713051495082009408a94524052045070044442c9868000035035942c0e00000d401420511058071608143c4918203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 955623039 1250 955621789 955621811
    0x60e0603150f06030f06091b0418030e1f1701060503090717070918050601140d3914030102030606040e131403070b09030f070b1003170a03 61
    0x2003030510300d0a03141d00c41c6521a580710541e14000e00c00c0a0300058040c4902044510440c106000c114051405840540f2041076101108045100380c0301056220307070b00d014417008040207505000403119070705080038114444003100050700c1044080c0007003030407203228050615140d844900120760b00e072015220080c40e6251003080300c01c2d01049600154a074018402444504107044500f0004404c60085031030f8103840320b0030700090351480703c1035124200404c032070981085403d0085601500b1914444140b44039044005030b04102421300c0a031003134180d011412420399416110900da00f00381e410311111300b82d000407071810380742039442100124107038044140038525060007120300801c402480d0501b000d0800a00b41811580035018040c034500c50115180014511260044141040d030040d589034902814031382041400100305e6659600200705440d174218160065031001a049048508c080c2c1c8c80700901c02d03c038091602301404000c1c0030301504400b464282e00400c0d580315607503420b11205000c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 955624289 1250 955623039 955623043
    0x100204060e06070c0b0a08070f030c324b0c152a0313080901111f0b09060a1e120b1608150609060f0d060e0603 49
    0xd00500300007800044040320685412006080c0781c40c09040c031842482d50304d2040e4400ca80c01040384c040480c3c02c04041004081d0040074118400c8a1400e082c01742803c0c0d200f00a00003401884050b00f030344008a03985000311500a258070139095007122031556100441e0101100c1c510040c004500b202c4400d18549484500000c80c440303402c10592074030021040b003441c10b40c090308201e609000300d00c245041d900c4c00182440030b2501812450f8541841500500b5200c0420903c034070025070011030800c1444041c4000700d20700c40781c032608850740715120701001004840116050755002800d10418004600c0c3c2c0240e40c010395540b0940150400c07901088406004050300b0442c0c50984c03048229004101c83c0e030000b2102e158520300d50007075820b003a880c0c200d0f68141c4c407610390080c1c40010340c0d03608110745040400988a411001c41c1889402c52421070b0180102416441107207025102c0400c1c94480d1307880f00d00035210b4141e454500b403611b41482100090003040756100d1500b892000e00c0104815040c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 955625539 1250 955624289 955624297
    0x60b04030506061012050f091606020a17070f0b15040e060f0a331a0406052109010b03010b04020f070b040c081c02010c090605040510090306020a020c031002 69
    0x480405803055a5880041140c980201d400030b030103004a0001c00014070261b80314151041c01041c903001401e0808065062034224210704810800c444417105200c2c01386c0005218142690000310701d00c42c082e050024034920300480341d0082c80c0324902c0c2202400c02800d95200e512654090701c81800c865041004c0105a9128034034ac03070295005071010801c0c074002c001c82180c0c0061075040114030710750403500c2500c440001030f1f14815110724041d0004076110280c4410780c003c0150301822040b1000000c4488034612035841020f00307225002035034168010740c5842030014018400c82c83c1141d460403480301c601074050652541d21139442c150140039186400d20a84809250b47c801c00fa0801c016903644201001c1c0c081d00944d4200801c00380016105c03420082031380700081d021244081910040400703030075a0103010300003040c803444082c02e00c030300c0303611100390780c01c8520413100718010300708000050300c48582c950000f61880d40006001d10380903400103142040303100150200d961061b0444001c0b812402 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 955626789 1250 955625539 955625543
    0x201111201030204021b0624041407050d0e101d0a031b0302010219171003020337060608160515030403141201030c09090b07030c020c04021804060b0403 67
    0x2034510014409810f0a80c0940741120140340c2c2078148080041e489441d00d4012110030104400b5401c0703034a10a50f06148000200742c041d1000c0c0008411881b01404260f40145100c080140100d031440041d402034101c0b204081c401000d070344004101d071801501501802c000c0e601d98035024592424074080004d00d4141d2960140c0d40c010181c3d9460308815090003d945080d4115902884040125002e0800482d040b08950b00c503862503403000c614880117248000c10804500c5080041000540c4002c1494541c041c4160b44122682030109040303441540c84880d094850012209010200855070b4019002d5411480c2140c00d8442842c2401607507040358002d40d83c01190442da108400c0b594080a590007500c00d003080a1003a010031400441c603004002c42d01070700d541d0f410042050000c0b225050f40641908281403180c56450340700c0484000000d82400109030741e500d2041010741c42400300c100c01040040c002e643d43ca201040c1c50840f4180c0d0284148038501d4100001042c0c0007003002c48044036 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 955628039 1250 955626789 955626817
    0xf0d0c03051e0c100e030a080301120212060103052d1507020f0a030917120f03060103060e240109050307090615030c0801060309060207080d0509010b030106060215100905070f020111 80
    0x4c1803000c02c840c007902032104075800d881007844410008142c900918040d190030000c8601550050040080c480690203520016800c01d00051000c40d0020400c04d80d000d10100040c048041c101c881c498804402c2c02108459010b001e420300810076404500368040d500355801c40d0003990310484140c1c0c0702ca82860b4020080350312100100140000c01610110f95000742e4113540080b4651420390019034015050108146000402c01002d0f41c0c240c030591010f041d944400c1c45407840e2409502112840e42c0101d218000d41d1000801e4160b8030440c1040045c0c04050159118503640705004000307406a40074090b104c000107514400c1c454403d12429003550410b907100c0b81c042e440e01c40190014681c01005076541a02049071070b021488400c010043c1c45440000004d0340c0c0b91222030242154030340300300e00d031180e41400e00c108401c650008042a00f00910745202c10b04d621201e100c009081e0b901e0348140c0009007080104000075800c60000180a100c80c4c0081c881c1c01c03403441a58003c5d11850070301c0b105803 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 955629289 1250 955628039 955628059
    0x290105010e01110102132c040c0902070507090c02010218030d02070324020f0306040b1906030f0e01150e01060804081801051e040f0905150f0d0c03051e0c 68
    0x2030b41c030589410341c9a0400c480018501903034022405100c40043d0040380c0b030748542059540b518555021035003110b2074401d21242540c1016514201400030b64852100626004500c1d60203000c000d12510000707190f480da00b00f00150000001034080d40203075504024140000e1070002c0c0341c2c20301044000d1040d445a0141100307d01f11755480d0020600061881c4880070250b02412440409100400c04940884072054480c90201f08002c19207150011043c0500300303002d0710405040c402c48200068481c1d03420049400881c181888008242d0304e4211203540d0309220206c0b00700d00c0005610401d840d941c51080c01c3e1a030302c5100503200c04806071002000d9110800600543c1ca035070b2190028042030514010389040c40e0000044401c0b550100d804018074400101006240980703003140c402004040e1052010707150038907100c181186e0504002e805495540b4030000160380b000d8403645d00552000c02c46000544038180159546410845419070040310080d8010f03210700041d4880c0111802001c00d946 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 955630539 1250 955629289 955629317
    0xc01021b01031d060a0911190e0910050103060c0807050a02031213051f060602010b030c13020f0f0405030115150e0a0f081615020a030e0f0d29010501 66
    0x10f00980b001c40441c40040206803181003024018540503000d5040041190841420942c000c111444106842921207401da040200e40000c01e24046904274841d03a00300381e481d40e15072800c207441c2c50380c0511501c0c500000401005a180e1129001c1031503550340c0d422035554030605403151b10602c402000036a000340840880c1600060400d6405071042c401c8501c5164980d494618000042a1195a5540036003014104051901c07070382e4000e0000307100a0149003150400b01e40c803500310940b07050082090f11400d60000840c0d404441c14050010380e01642c886010410709911f4106008080c829401c0050940c0301e00519108001591500040d07040600807001d000d503030907e08501c2071a049000c4030800244480442d00e00c100405990000d0030180346408003400b24403600350003e18040030303010040314059a00081e85d20120382c0c1420550300111040700041c41070041c0c51101c1f5480700c09003000c1c6040006603070416034001400312a81000180400d080070b5620b500340201070020305880e003000b071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 955631789 1250 955630539 955630541
    0x40317070203030706090525050d110301061a030901060e0421031e0c091a030105090c04030638060a0516050109080318010c05070f14010501090e0c01021b0103 70
    0x3000c148014100c0746010160b40c0c4401c00d0301c61900f81960300c3d8002c0101448120034000c0c400e5040b28108454014550800000400001c9004405440086c8403000e04041c1e803025030100000d03060450741140241d88044000c80c159108a818840650030010001500c410708451107004990120782d01d50b0410710090816602c659074031585c1e0130151501c0980700c4000300c0d2110341500d0300342280c02080d061003941001d00341d20388641c0003070300314440907013213804a070050390a07031381510400c40315a500c40c0c4036120a041039000c0c607040030304a10318194280060200f500250800d8500003407041c1c9407002582c0c0314000551544c0c0455400c2141005001c18162044000309041d5040e0603100c80004e90f6134482e10708494000b4012904044e0001c1031000740000103130344465165108000340a000d02660340207005026240c4010300b00c1c600c44600740c080140c030b059007564810042000304103660355a84440050288005130044c240110709241d4178551001c103c9040610000e02002d100082a0700118 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 955633039 1250 955631789 955631797
    0xe0f0a050f07050f040c032a030e03090904030e030f0d1821061d15041703151c0b16030b010302160212010e0a030302190c0f0303050a0b0a120c0902040317 68
    0x80d0415548850b414124410103502c2c4104100d07010f0235101d810308903c000b6048030710301b20000345141d0040c008050702d039558080381030703005605141191000b103924010070300d42500f0300465182c2e4021000440c1c05113500c00101040d442c0510840e020850f40c03403400e51407003207a02d80c03813460001213280c00e21702081c1c0980100a038081c6103114a0759881c4605020350510403003180740c8542061010602c4284003403402c0c00307841130050641d02899400e04481540800901d409414020000140b21021800021040f0003c0a070041031480c81481c0403028954100000c0b10180d010074a00b504100c403a502ca842504c80d0490040b004085003600c9800f0000d034041d010303841880540d2600050007612109008880c441817007501c000d80c4414038500100d80c2011400304580c01c0021007000200414040500c4540359a01810006019158007401002901c4860101508054518000250310011001c01c0002e54055180c0d212520f444607400d805178846c0703110103492040402c10404034868840014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 955634289 1250 955633039 955633061
    0x18020303030711120d09060609050f040605041a27010213050409020402070503190816170703092001020f030f22090c030605030105060103060b0a120e0f0a050f07050f04 74
    0x15400241c49513580c881c5030344030a4000d110b0380d40f00e508440812805006000140c00c0018040c049440c2202c8140811000244050032040e2510f0101d002d10188041101a0404c80f00c6401914502a4421000c83e085425802e6980c02044440c3c0d002510610035a01000030303036007501214a02d00340c02c200c0580710032101642d116900300318030400190200005d00709000c1c80710380800c3d4002c10010142040c500182031004102e1010325200b01c20303502c2500c04482c01c601d080150401d032190202100104000e06004001c44040d150070760003c5d44000384648105000d07401c640d43e08485815050301d03400350304e120541051051007480b01040c1d038010008003e082d881250410349035150101000c1d40d1a1403821070200c0d42d83c85041c003090a003030080d980d10030001e090910919240c2804609140700700c04000007009008855a0420034036900514501e480c014119205041c1401e0f2076900d8810076007044074113104003807100786044130204118084490003400140218280c40a110180016000c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 955635539 1250 955634289 955634293
    0x1080a0c050906040f0e0c0909060d0f05061819050706051c0f0b040b030a26040512060601020f07060e100e09070f0921020f0612130618020303030711 66
    0x81601503441d00701c003034001003085d00712556841e85420304030b07402c0b958064030071034001004003c0c0112548641009a41002064452405c0b51100d800d01d5807000c0801200242140a280309000e0440d044000254200100f041a02e90014030a641d00da0706c0c041902000303001e034000c00da0400917070b4000c5000e404000d00b15520f02d030b00712b92100144021a0704004908000d203a50340103900300307420603102d0400848801da0040030449229203820882c0902c0c3d60ba5808843c50301021044a0010001550020100546404603680a60702000d44582c0105c80050051151207034030f44510b080019041e0845103207840f4100c51030504030070700290a8902d0240b009100c0303400300300703022038841e41d01207846412140d440d82e610700321240004004486a90011010350680103620b035200b241400404c8a00c1e504441280380f440a503c0807030701da4007c0c03103c240749098815040000c95000a444031180c0c03841113104001c0341d44001036000e08680322603c040e4140e8010703c00140a18090000f6521b40840402 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 955636789 1250 955635539 955635547
    0xb121908090901080f070f061d0f030f07030b0f060a14062503020f0d1b051006030305120f0112060b03011b1101050a020c15070c06051e0a0b01080a0c05 67
    0x2001c14030b0000282d104030034660040780c0380d03090700006103d00405030a41114402860b450890010041c2c2d0700784e003103403407440410340c40c05000d9642d65240007403110010301502d010b142c05812140d11170b80c1e2403006643c2100c0400000300e80704d40740003085210700802005003507001d05000d00c4004070b1510180c103a170456420040d1b00202850044101c620001220869040c0c01c2e09250007814410b440410614540c410310081c0801134102e50091565488c001c03003004140081d0801a2400b1540a1400c10051410b0004401c4c9507001c00284080007400c40c002c415901c691400b4001d0280910881d606054489150800a02660000b02503450000c00215000b84d10007400700c0300c0001d20b4607000105400d03648441484d0030070702070350758080302c200c0d0f045003480c003602d0303410b5240e00130f2510000305440300c1c0000403401d41c020050798100c150440f07030810051070038030200d1100c214001c1c100b006031019200010151811805440d10000b8107035580c079100c0c0c441d40c0c80340000d086044551001d020b801c3c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 955638039 1250 955636789 955636807
    0x403080705040f260601030b010614040905070302130e0c0304030c1a0906060118210309080607021609051308030a0207080d06030b0612030319090f0303090302010b121908 75
    0x30580340c2c00b43c8241036001e134030302440d07148000c9990390001026030b0f6600110010404160302c511254111800742c1000c9082c004500c600380740c0c5105940200720b00510344002d100c00554194003800c400c20302c940000109a8980940c11080c15007110b0031f03810702d0030410009000078800c0f2074101d80d103413040340d0b0b044844a03028109600c910040f240e00d12203901c003004002c00341d07038003600366283c582d10a080c1240b8182480b104488021003100010954000c8140c10401c141c8070300055801400180d050b0b40c414241818000e4952038001c03407082485840a0303000c212001c1c107102381801410700c0c0062074004181945e03001640d07000240b0f131b0401141c7c240b0130790b0041000d00d4014141407528006c001041800d620700a0903118000c1e100c58005c001d15941a00300341c0700081282c1d0801d8420f01c1403080301e061456254041c1800701402008904a91600400c054240d0884d0410611940007408217614140030311030210304c41030706411207500116a1070030313800500700710906050040d0089031400e418a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 955639289 1250 955638039 955638059
    0xa0f020d0e01050609010f0602070302040e0a02031504060516050d110412060f05010801050115180b040b031806070c2a0f14010509060a030c1206062a0506040308070504 74
    0x41c0801c924142d440c0d00030880301e0b00d409209a03002d0440000b04066060800f03400035950815804002d008035925039844200030130401c44c0307107034180d4001c1c02c40358154080b400c4403000d080c01340c60442d10181410041a108200c1003171000d10540d05a440c14241140610340700003410b0109944c0042004c1044041011115010a00300684c092500491580c0b04103142d00b0071607405034403403040c5034503100044c0400701410450b60703000c403030920782107001c003440070204031310302c4d005038018070244000240c0054202e16020245d40f18952005a0101c68015403011035100d141c100c5c0c20100080381c5002000020b01a8845198502a0340c6603412000c00021800b680c018015007181404120190040000401c2d41c51a02c074400c00c2881c07d2400c1141d00400704c1d03614020019000140741d21031240c054580e114a170b0034040e5195004045c01140c0d9102c8002e0031050030f5403003008007180300d00390708681b0f80c080002600c5c11661185c0217000c01c0d0f03910f8030301b10f4070520064024401c000707007000001085010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 955640539 1250 955639289 955639301
    0xf010c12030c1b02010e01121517010c080603120f0f0a03060e0903091c080715020901171006030e0304080a121d36040b090c01170a0f020d 61
    0x740c9000510703080300d01c00680060f00d54122801506a141d150f40010b0341c2c0011850442c050a0811180c030b1110b44250b4805442402e00b01301c403803004520001002444025591411648840200801100d685046440d044103c2c5c0709034065116010741c1225201762401070034001002d42c041420148110041c112543c0500d050400194a072134050001c8051108410380001d203081c002d43c03031301e02a48040f601c080c2c0303040341d4024031b0b201d0061034038203201201d01201c6031150b120560000210100e18500000c0d08103003441030010b507280602c3d40c40c051110705058040c0c40740382000c2c0070750780c07420b2000c07406041e24241c000d000b800700380300004055104000d0170700c94a00c164500180c060001070001c004a1034480e0640c100400f103940300c030a6484400001c031080c0c0f940b484041c600e4024171080d0341c442004240490003241e200c1b00704024000c0314a12180071302901d0b003d0700c205180030001110030458202680c43c1c00441240420b00000480c0d1204121684420b005414041d044030b11008540c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 955641789 1250 955640539 955640573
    0x30711120c060708070e06090a0b07150b0307080303131406070c060b01052106040b0d140f0319230408030c061807030605060f0907022a0f0f010c 64
    0x240030a0044256500380700da150f00c103956140c841c030185010b103801841c01c00082e10f143c3c003410000910b15840d44074010004040d042250a0390f0b5030f4400d0740341c840c07200000700301c000018500d0138104064901e00883c07144116000383c801103085885410450f1000300362500211540305c0c2d00800003094440074044584a50b90903140e8940001090501d40180c4018100e001d0400c5406c00c0015070161100e104003540d46a0302c544100c8555581e00841c00411100e041c040e405090040b4038070801031040d05080a0071140c4c8150350400700a500e50941e00c0c01190070020b1042021814034121034070550344002000e031415000e401788510300c3c104040b240c4c481e0f00444200e8000240c0c82070002c60821400740c0015440c0209228070000d5000c0c81c0d118030490000070061501c40002c00c05503030703459204045641009000c1003442c1030110019580c1c15401800c00030740510303103120400381000b41a00d0b0740200340243c00c550f0300710854800c112010001c8805a4140000542c01202240d580700c25403640750 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 955643039 1250 955641789 955641823
    0xf0606121208371e05060d03050307320c0c0a0317031b0304200d03050a140d0606360e060415140a090510091d030703030c1b0215030711 60
    0x13000100c2c0324801da6a0061006004402c542c450300000307903002d801c0b23030f42c4a503007071800c800c0e080e442043c00000403600303483c0040d642d1540b5144191400e4130710b00614842c0d602004480814040e0020300a002c0e029100203400c04004506801c01d180c594001558030241b0740d0098a01402e10800e1a501908241c41c01e0329501c006072212602c80d04810800840c0503c00c5419251004c407a640040c400d02c10131402c1000c10100682510052429500f968000000040d00340700d601e4480d10f00401c80a1740603581c8000d4034140e03e070329400f05001d240b80100004454403c00030a0308021403c420510090075a54005640c1e200034010420007100003005004941c40f46909919042e0130000c0b810090b40000d40c02e54584000e104003c100000e4010458280c3e6101240c12114808100b24902401c0c000500394080080d4010404d07a2580c0803021004d0682c94003140980307024000e5080002c8800000d400858284074079004652540c09103600125900c2c094143c41142480103080401e4012085406 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 955644289 1250 955643039 955643081
    0x11d0a11190e040605010b090f06160819022b0f0e2e2a0203031209071a04060813140307060603110d030f05070f060612120837 56
    0x3120345c4c0229801441d42558490030300c20f584000403000c40300a0b80300d80c81540002030300c2e452011a92920b04103160481e908980b140c85d01607081c100f400c1c40102c0348005025900c2815540c42401c0c0030046d07001001010445c0750f0710001010b40d03442d54550800c0c010f01004104c004119500c071101038000b170421a01000700d07a9000e0003242130001036540d59505201c010301000206034a60142d034164034400790304010662000b4000700b8110f11442200c40d0030b10348203600300203c02c000080c0301401c036000104202441c01c031481c40c0b0341240c01107025607000109a240855010b60f075407841d20a50703034001c400a424405145902d21724507800190101e8286464503800c0051003550303d038071172001c0c03c20381e0201000702c15035400810405403007030044140100032864009121000101c88425540140e0801005840e00c0c6001d0b00321206044c2107600e09420290004c1d202d11820030309020300024809003801981c11501440988401e4942c440011017180c4891345549540c0580445134000c0c1d1690012 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 955645539 1250 955644289 955644293
    0x6111209010e07080d1713080a090807060507081c2904050606030105030601060c11030d0306031e0506190207060f1e051003060c020a0605100602011d0a11190e04 71
    0xb03040d00c3e54002000c44e009079500751410740e0030010000607040c003900004101e0b0b03600c104048466500000280ca044000306a900c1c3c205d8004843c403081e034281d0070444000ca40c3c0c0b1301049849100342c81d001003002c18181718150006441040c68100321103084400325081c6010f02030303881180500c3c1c1c440d1140b080790a4001810781014859190480c0080d5115450f660401c40400c0e038039441071054000b00421107418606000030009201207800005003079036182e82c2a150010060100b034001551000002c0044455403030242c900b941c0d40741d81c003001900c070075074400011045e4040800521520b0f180c0030032072980003400c54800c9114403a060324000a0800d18110340141c049010003c814a00d4a46401e10070214681d040c4d210840b9802000441c808092030740481c20703d003e80c1c0b8010701880c1080140903021645410200c10b40d20250300030041d481c46070300116591082880710300243d0300b1050103000418036010f400000b5490151640200c504060700c00c040c29043c41d03202c41445000e84040c081 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 955646789 1250 955645539 955645543
    0x161d030f0f2415010806061608071e261b030c21091c0b0a090b1302010905090903040f0b1908061c020f040204090b090703060602060406111209010e 65
    0x7031054440c02d06480585010110841071000340c0e0281d0b03044c044060300203031361035a6010440307110202044070144e004070f4a00d044025500302c07400840f0364446140390000c0e0421280c15a50990346c001c41500c001000903c45030714100c403114400014400200075130301044003030b8144108001e0b07080d4000e40e0390b05203080b2900c0c10814100d02c0999140c0140c04c46851040d05141580c03040941115840000140c418034440c0481c0712950080100303240504002c1c00440320380c0312071504c500075245c0c18801c1e0f0380d0b80c038078080c0310204034802404194030203000e001500345030260310b0f400070300201201d141a465548107203c4884660118100440c00146003881c8041d07403900700090500340c10107503010301340040051080c00307003009043c040b4006811a01c1c195518080c401c0c4c080da1014004540e501d841f2140b01019007421079105001d50500030109030418400d1003070000700c0d03042da4007420094403a50340317a1000d4020100c181081d51400c1c0043c044d00c4440e1000d0602680480c80001811100704400b14 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 955648039 1250 955646789 955646833
    0x100203060f04200705070e100f03120e180f06040e0a030320070c0311030d050f0d0f0204060e090c0a0206270706080405010f11030c0c070909060212161d030f0f 70
    0x3000c11070031023020000b10142d80700100a03030383e1000e03190b400b5131510741044400707031411b00110741c0c000703452078028000c88075142e40f41d8020a022650701c041e550b15041030009071603001160300c60f140c6c0a00c8071440400e20179482140401148200c50003480303021010003401d6001407030191000542a03000304104091400d5410300c03c441500a80304110400c00041d00601070004420384519000034901c8441031680e10103100c60280250854455495800003440040301410542c0100f201101241c1000c070a50b041da0701d2844a1b0340100380955801e040703080c1652416003c0c004000307403185075441c0300f1400d0002001a0050355155840381c134040c00d00b6800c0d101703251520580c0c1403a162003624184650302c200da41c48003100405e55951006203e400e8a0081c0da40d0003c01028604080c6100704100c5800626074600c1030a00072909071907911f48001680300e0300110b140854905a85642c10381000a000000030300014140da12046111001c00d0a2090f540005095078000e07070040e110540d6030310510 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 955649289 1250 955648039 955648051
    0x52a090d0204240608090309041a19140a0e01260703261e090d0803010b090a0e13020d021f030c12090803010504050a020c1905100203060f04200705070e 67
    0x190506d04101100c1a208d20841d804140269101e0703004120200c04003400c0d401e14000682880022110701c403030102124068003c13002841c9005900a01a241c440300710000c0d11241e000c0002d20b6480e0458042a0084c440b110030007020392075107007004508090103454011030050540d6100c941c04495440e01d000e00407480c54208020901c0b03043c00c5a1150606100301529146600d6030300c3c4609000600f01100300c500040004000000224005000c000034011201d0700b5203038040b00c2c503191280310303066040c1120466040c140740d0382140094904003550385046400600240e8042800019185c20074400e80c402c0c0020a858501d03000340d6652004030200c1c0c10150034001c1080100d141e60f1134030988030600c2014170598445010500009159040b541040740320340807031381c2c0b8500d1303604070b075100c850070500a8840d402101e0a6803c04102070007141c4c42403c00a1009810300ea02c441080f000340b052900440380700c0300411203001c10820000003001c2107070084008000c5240f030517502b07000083c4010b0030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 955650539 1250 955649289 955649297
    0x3100207020906041823010c020109120801030503030f0606070b0109090b09071208030c040e010e0f090111070201030905011b0509130608030703050d1404030801060201052a090d02042406 82
    0x15820f1750461008001c040c0b02e41c404080a040101c0a0f845c0041000b40260700c0302d035518045040201540543c00203000a04c100721180c0002034080042c2e9051100748409001c0d50000c0000401903410014119404000109400e0502001d619010803d01098004e040c10325941d889880603c01d400c42c01a40c005414001003903090300341804000c04103c803c20080c0085000300200d8580040c80c01030760003074240c1d0840c540c00c1d903030740314021442e0100540307060310001505404100500b0040c0a400154801d64a800b0301e800a241e004500411061000743c98035581d600340c0c4026001562001040802c103a9103468481c0203e10030008429004030301040e05a140800401102001100744c40200f9054203200d6142c0b59078803080b00140c801d0034400c1c031144c0540c074100f104054103c26500c3c140c80d00c41d802002259543c40c100810f020b03111640c00c00000791520300440d55090600200050070025292103500700380d503030100d002e4800c441d00c2d81d00c0c1440e171606401c420a08038034900000f842140340c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 955651789 1250 955650539 955650551
    0x6020613050d0f0504090c03230112031101020c0f0106090f05100501052506090c121a090102040905100302150406080f04061d0a0203070b12160e0310020702090604 72
    0x6075a994803034062000500780300c2c1c42003280c0d407072600980a41c0e000740700d102000d002c1070400c0c00d4018014501d1000c08401c620101000400240c0d43c0d5000a050f070388550b0161000160646040c0c07030300754102030354840a41d000c2005084090050201c074000c40c2c00c0000100d145400c102c0e03a0400e5819201284600c070380380804000c0c0406d2034a070030104482c000c4c01e01c00d94039081e0104008650498210780307103801005092070f008025056100c00c09150040e4424a28503031500b50400d14040001c401a102d010702d40040401081c000020541000c003102c001480c15660301d82c048142e840454220102c40c00b509000c000354104000d041c0d00000c0c0c0c268003980390070b04041002d07110042c040e00746d12072002c0420000301041603a03402480c2c802e4115440800c2010900d0000395100c035020030882c028040c0c9400007941e462200140c8580c5a6072100120890340c1d046001d1140c504108009420001031348424031042d14140040b1544112900001d40d8a607803900510840c0080030785201e02551a0030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 955653039 1250 955651789 955651793
    0xe030d020a0519020418051006050f011e05091c140f060a020a301a1813140303010e07020d090909030210061e051807110304090f020406020613 63
    0x101d22403c02940c403510701c80c0d12003510b0011030020102100540c01d8250211008014020001010a80c02c00801400c0c002036403141c0c00c0c451a410b40310174181c085460305902c5400540319151640d24a150340c540f080c10a4a0700b000a010341c2c1070350004803a0072151800001c140702801d40504a621502c0004040c1c2910503d0b840780c1e9404000c044000b802d5000c030b6074140891060390440281072481010381c0c24000712488000020050005c00c3c1d9201d4a80102c400070a44043e4400818203c000c0440300c2c540005080d51025500c0140760310408265032100c200000d0b845101c60403403d4030300004540380e605104012069a00107421403095600442c1d003a50000c2d84034907001c056a001700e1000c41d02540920b404d0745000700b09400400804c0c2040300100d40d80b060310b000d10103010410801140496925024000301c07030550204000b41d01d14410020b48228014100c990f00503040301d0489140607501c0c4510012540c00d100e11010154000a042103141da04114194100c0e005031160301d04d00da059 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 955654289 1250 955653039 955653043
    0x41506201b0904032105070314010308040603090f020a0b0a0809010506131a0a1509120b0a050618130210021c08091609050406060b072607020d030e030d020a05 70
    0x122403500c0c4603144010010b03041500c19851115001e40c24500940c81250144245c0c01600c1d0485241002918100d030090718120b504c0581e41c100ca070007050325843e103070900004074040c1c90b007514166260305030018080e005864800c43c41c00201500c1e84140e40751401e580c4010721042d00130303120704100da0504007032011035a40c441000201c070ba0150310024a018480581800301000c40012507031104801c2c000007511040c00070402240c4495568000ca400d4991390010300030441c0035800342c81d103003042c0001401a0001e5122541020703004200724401080380d03c140c0d00100003100c00700001103201c0c5443e0b045080400d07070014003a45a00150400c1c2d07140480c00b032505200c82c00d541c010000303c080842d11aaa01348114010070035070035071500800f42c8803030341170000d88400e50302145c00e00d00d8242c0002d40c0e02100429980220b5005081030f40255a00344145009150b4000c0d003085a01c04001070f4005030b4496010108851103038882d00c602d156944101030a06011405840c250f411000d0305000140700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 955655539 1250 955654289 955654333
    0x1103030a1a15160c0509040b0412051608210c0904060b0309061f0b04081c050f120601020c130b1806060a14040e310312050604150620 59
    0x180510f42c81081c0d503090410450700c19500c02500102c1100a10091101104030507102d2405100605c1d461050880c00311014401c00d0f049804031203076040007100080070389004003446601c0501c01950340c0c407429061510108240e803000e1500c00c0c002110700e0b031820b0074010b00c00107200390701d945801d40c07505a001d01d8440800501900e02c114080c10340c0c034603210380c0c0c000038800f41103003036209034480752541c18841da02c60b0b802c8043c9040d0560f40d00701c1d21016204100702da0300300001000503401d080c07410800021070900a0311460540c0940f44115100340c843d20000940d8070300d900c0e00480c4543c440d1040c800e45082c0c00421a1904640c44100001512554101ca0300c5000516041c94074041a21f081c5c10705d0b005541213250300041400c03d01100007081035464584c402454110051030349108900a00f2511070305000300410030b000200300150300550f1105911000c050408100041107448440301103105030410380108540c090505090402d0310903a002005910740282241200c0e20908909551 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 955656789 1250 955655539 955655557
    0xf120306130216151d07150c11090703020702130501061b08070f0305032205070b0c010b0a0e010602150402030a0809060d021204030f03090c090c1103030a1a15 70
    0xa00010b50030981c001049000c0c1e0400d800c003041e104503445541d81c40c0045d00900c072808203c0c0820000c42c00c5180400308554040301c01c110070340030051000100a07550000100b84c00c0d00e60340400c00007aa082c1d1544080345110316010f6074016a201c1c11441000300960322030f8071310300080d0f18043c018803800340c10184e100c2c1801d000384a9007462500710300e0107440c40e02c10540001c1100e074000c00c09108254001c1c0103540030701c881e08041c40c10641c80b07400c10001d43c10441d90240480d4820001042101181d00c02000c0c006c00160001c60f131400040080382c401c54031030340104081903407c1d00400c8029818002442d0388241303101c08180c2c90030f0940019039515200c40020303012401c00207410689071340700003c07182c030805400c07030542d1109403c5e0b54203806803000312810b602185880489044075403003446100840c079405001003103102c2c1003455032001400c10035203010a01c810305441d003980d200308101451045051180103e24050901145411200320b01045c81c052084624005003e40858040d01c1c0102 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 955658039 1250 955656789 955656791
    0xd090813082e180c0f0b030f1303030b1c050c0a0815070203090a080601060e04020304030c0b060f040906060515090607081e030906160f0e1c0b01080f12030613 70
    0x88100c0403110000d0940c49010001480925450340401000b001c80d00100c80c0418000c0803003e036140c0a600042c81f04031b91801810210500003104d600135400910720030b1303010b403400141034031500011524642d12820100740012070790800e201008810881381004000943c2c401030310398a171154680e506e4418039000710781d45900400150186108105860303150300010080300c0110341c3c605946440f25800e010300700005020540c041c415003001d00031280210344c1641c40c49989242c40c2c451000c0d000001d4440340c0d200c1030300805002e856a5a0180e960a180503100010fa040d103032004010401c031080321078000e021000d00540b20603035225800d0303130b00c0725400200041c0c0da1888081840c050514400114418007004418800c6586000941c3c510410005206041d055072424041d81d540001004100020ba1070703407540980750410030080d1003a1040030104c0c00d00c0b4549a6250401c00800f60070074910b9a104440b0300b0a540d404000c3c02c40745a241d09043c510318241070f00403e1000d0b00400d0071054075 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 955659289 1250 955658039 955658113
    0x310021804061206050901050402010c06090228140a0806010b0a0302090406060c052b050c160306050405060f07020606041a0307030c090b040608100e030d09081308 72
    0x525080c10508804480107004020050311140069030b03207500194280c410170725120014004100c1440303070790b014071780503140c560700005660388110181072107a10032608405103014580550826100c3c1c030a80c41c1e40303040300c0c0c1c2c0c0c42c900f028180f0120007822003c2500c50805c00004101402c40818943c0c1552415680b5903668042018103030082d1081003512a009441c0100000d80e080d071103210340007002d125100742c803001c203405045c0e0314079008400980e0b0b00d0404001300f4108114011001003130001c0341c040035150411680300b143d030050b11440d070041e610113843d007003080104107003403040650240f400f80624445052200009541e01c80081280340140d56550000304c4255001c1c0d142848208000c0859405686078545191000c03414404c52202900307080382c44215142600a400a0302c41d0040200821000f0944000c00b60481c150700000c64081085004400f101c5e5000e1801c0c128041e80d060390360707100501c5070681c0b556003a80c004e01c91904101c030b110300481929419401040c0c00380c00000340c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 955660539 1250 955659289 955659307
    0x504030c080705070f140a05190308030f0a2004050d02010912110a09090b0c0703030603080d05070f090501081803210108101b050c030d020705100e0c031002 69
    0x169805010007816445000c25400208140040c901d07080c0d5103c02842c2c1111651907912996048000e06100d5000140200901580c1800c000c1c160314100c469104c04c02080d80c0303407208442940140c4030003450000c00820000407150394051100180030150705110281c2100c41000035501490240a10a0b040058040f0a681c07103170004c4130103824201c481c0240c10000b4030300080c9501e00504040e003d60a04100010209141e100e07421842e9000070a500c0302c1d41e03170300300b1654080c0d101450443c203060340c0c0e00011010844120184c42c0d01494800700248608003041c0103048001016002c10810001c08801e000c1030b42e01144051b000b60a11003900c01401990900ca411401401481c5005e1501c10307507080c900550914680f8100e0b01000140c3d6215034000ea101816580107920b1000449040d009881e403852080005121850892082d21705185141c144134050f688015811707216a80801610306003c3c403144103001014904000910a215101d00443c0e1103005008560800590110306285 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 955661789 1250 955660539 955660547
    0x12021c060b060d0f060503061b09030102130314100510061d040c170c130515070501180605060a030c06120213030b090d020706081b120403032418050403 67
    0x4044009044075101c00b01e9072400c1d8001d11015100540040c00c5c01d20018031070401140d02d900074240e05000654541002034686007503800304801c0e940644d400c103c1046903681c05507808010711710650700c03a50236654032260a45420110003e0703440301440c00091041c410082c400c0340c5d04070b81081c01e0159280c40d042491010011260038400d4210342032200703411081e6031058080048091b00e0800c1d803010b4a034000812541d008500400b001849007010900c068030b05403009151421420540310f181c2100c80c1d903440d003500c1910303004e03c01072031880e01c03407408100690240d243e010001b0386800c0c0a091841d112508031349407500c81c0c40c0910915051004440f08540c0440c0d5440c100103080a003156600d282114103264202c1e9429860300509001446072440440d0309000c07a4016500c142c1c20f52180d025803421010032010784a0443c10801803002e803c0b00e00400c0912a5000c0c2d03d0000b034001c0400501c9030b0901c130150f10840e8000e0b05883c0bc3c001180c0c41481c0b9603155104d10000107030396a451034151703 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 955663039 1250 955661789 955661801
    0x30e01050d0f02030601031134150234150605031605150304050c0f0406080d09060306080708100f23070e090702030904050405030f07030504030c12021c06 68
    0x8101d0a0400e101c0a103000100c0d0002e500845013a81d080000030b41c081c1c0d0b84440d5000d000e40410705558000350708a00030000480000301d0341da95110b400384410b15030366003890380352005001030350803a0081800f1454034401c8419490841906140f144410240071507582180f5801c907004200c2c084802c101c69a5a0b402c1d40f00304050500501101c4038030410040f5550f031050340b03203d0140f00e100038900e00c00c0392760611402d490295610000810304031503d41c041001451406000d0394200b55558030014480008000c1102422031940318144500c0c10400020140ca07602e40154015902828007000440d60005180000700700c140c0000810840303581030fa0028041d03c00c0c003000c0501000e0420064a000302c00b1550240480791110620402d8034414042001811909807015810900000580d81032a812499000d403040c42641d20313108440c0003481c5250403822003078001910204040c4104021442001d0240c40c4100c6034030308001c82503000444d91f40c4420a0440c0351070f4094080010029190410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 955664289 1250 955663039 955663057
    0x906050a1202041d060f041107060513080414100302031b0c010b100f030e280219081f0e03070807060605030d0309110f09070c0c030f031710080a030e0105 68
    0x22140b0b1302405660224018066660700d103c0c488400761252245031500c180d515606000350018100349441c1c460708000c16008044102d0f011000768500001560f04009001a10440c0002c81e0001d0058041c080da403c1a082c000d001d2500c100305102d03e60030b180700f644070043e86145802e5034403a440301c60715025120980346140c1015200c004501807075002041400e020105a0702082004620090150780f9038a09024020004411907299201e01042007000022030014000808150400c01c00f03c460003e00c1c1d0060301030307411850885141e000c06e540d0072903420310841010300c405422448101d0f107901c00c807038001b00b02440010701d010801c441c60f04107800502c40101a14004d6043c000c015026111088044820b0781040d40e916086107011520740e0301742d00001d025206075a40305c03c0140c0742511440020384044440040c004005004400d1844003c0d101e40e42d40c580c08102e40401402140c0c0117000c15880540d088814030010318000381861155030140741410381c12001400691b000e1180c841e40d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 955665539 1250 955664289 955664309
    0x20105062d27090a121202130303050d1a0f120a0b0709062c120a06020706020a020705030a170f040e070906020d090b030c1821010c0906050a120204 65
    0x1504584255042036150702c40102c2c0c501809540e68074211611074041c940300902010080443d4660315109214040c0341012142005140443c0045450b4910045500c12400900700007076500c6010107e00030740b45a40080f6100e2184002010006912030100090040c0500000a8444034a000400c00c070790000b034105841e102503042004000b00740c41024021139001c42c020781582000c82e40380d02ca6000c0c080c1008240f0660074402103040140780c000540c5a46240d00c00c003003540b40030501620017043c0680c818240140c0e241e49100700642415412303409540310b90072401215010950001ca0b16003140388040d0815910152001d14004e0760066401038070b42400b000040191480d00000d90302c003030314416022610804034a943c115100b10480c00b07a016292028004106002c908001620509030102a800c488454035400304000040c4881811607090540c0f20f0344500d0b090a200d45854185103103071280415090503c00303071180c444c4440b0042082a45224408c0c0500c083d410345014040c2110 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 955666789 1250 955665539 955665559
    0x201150f0b0307020a0c031b0b0301062001150803040302090c0a050307050c010f0c02100f020405030c0d020d020d150c090e0f09120415110102040f0b07060b060424020105062d 77
    0x900c11001c0b041c0f0508a02988418a404a06c1c0c40840007643d04803110307179940c10303841c375540803009082601e1140c3c003818664a4016220508a1600b29800507140a00c0203580302c40c698010003520307080c06003c40b076021f038003001105682c82d072007000c407944101c41e41442035450f80002c4009004110640622050703a2400c0c1c41000100d41c0890312041c40711354010144021000c0403c00412071007284503483d8598440e0050341a141486051000c1050000b802c802030a016a00842d456a20303442e0102c5000140d081a00e0211485110350b6515018a01d0f15114983c10802c003d160000d015001b11450441c200014030300f071004005c826840f584d841d0502d078542c0e650b00401c1c9582c59084103030b04041070107901c0898140b0300c140b090313401702c0d2100a01d6212482c6000c030745d03001ca41d0200b541a58615195110495a61074002c0288020f11303912496440041c40d01300e003480d0f0300e12100700d10000c40e4106421301803141d03141100c846042c00d0341c1128440124080b850110b0007001400019044034545c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 955668039 1250 955666789 955666793
    0xf0f030302090f12071511100915090f0305090303130801020c07050d08040306110c070b0a031103040b0f0a1d1507140d0c05071b060201150f0b0307020a0c03 69
    0xc0c0107880318140585180c883da6900004000000610a01500080d0700c5032034200024290340c88009007500107410f0003800d58100c1500c1c5410040d0119656800c640c0382c510402c1084451172001e08034242101c0100000309050795180145100720002900304200401e100540380d07414011a40710860b031765401c0c684141d42d03c0f03405004c0d412002d0503000300e000c2d080002866042c00400c050036140e102807818035180c01e560b21400105907040c102d0810420602c0140809801000401e000c0c20222103044d841d0f0519001c0101a603191a00c203c01d01c42c0d06206000029006001490b0444d2620100c81019a903521821004101c00740d40c002440180c3e408078150944040b9148464407090411801560b850800648110388034546d01030b0f40c0e0340f08119401000c40c056002c488403025500e003061501046031150080d40700c4010810354669507482c010800c154091084994820241000b207039464a01701740b4000080b620722540503c81000030006040d107100307100c54500142c1c46951031050703584074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 955669289 1250 955668039 955668041
    0x6050d05060117030c10020a0207150e091b0901030b0103270b06101727030307030605040513080706110f07050c061612020f1e0c040b0105070f0f0f0303 67
    0xa1280001c2c40a01080b203c0f00307241c01004441c468406030740180900c840c2c40000304025400004540114043d038103012690442c2503d680d4509000c6030340350754401d210b07802000fa145c0d1014184070043e046500401c4020828078040c4c40c500842420006030000c6031600507400703030204608584681d1001224800d80b00070181d140260b5a020b01c0c0b41810300e9403110309000c0390301300084290380414000340206541c1008000c0240d0f00402c92021003175030030030380240e400c901909003c540110717420200801c200158503100e0a8001c0c8000c88040c032942c1080240301080030152180a07000030400035070701c03040c001075402c00d1140060320741119503920b6001c200b40d2030a4020709c108891034010100355a00ca440c000c002c0d101b0524034103002c441c0310030041c3c2c2c44121064240302c0001c154002c7c2492000080c05c02e00a074007140700120100a980c8400300030a500b8403150300c0d075940c4204c1c03074400b901080343d03401001da440391b075400300309000c40b061541440e40c21118915001440d00010034481c030109070781 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 955670539 1250 955669289 955669291
    0x80607030c020c060304020a121b030f0b090606130e030c0601080a0309060c0c180e060a0203010602070518183424030222080f16060f1206050d0506 65
    0xd25400d6aa00203e04000c2248502c4243c9020b540680020f10500840300180907010459108400307110500f041c0388034180b40f009240e881039a0307201401008106205056070113039404401c840c05481180b628100290740060058046043d841d41c40419054050b0301700211030410303c80d03c080364005e41c5e545064030f940b080e03451011400110000000183c090169459040080d403001d107484490303041c203001501441800d880706280c26103450200300751400600a5a02898204102503920b41c180180a4a058200e41c04140260200e500101400d6980c1c5481e0380c010410700303001080c2521501c0f40038603210f1290300d42074401501c0303544590518a12000100e40325000e144c811a220342d43c02d0035108050070608040b0030819201c02ca0440244264000c0003010102550118460341070001520301030707026045030005034484400b4817201041040b410100300b902011aa00c0346090183c001c01c500c0e00ca482c040c06002c0407201040741a00f050700a44d0203844080e0182102c0c1c0110704080e9600c042c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 955671789 1250 955670539 955670561
    0x33c02040c0f02060a02070f2a05030a030806040c090e0f041112151f29030903070605150d0b0f010801060b040e06040f060308030a15060815040608060703 68
    0x4640308180c610140102c00300c0c1c59040b19a000782c54255541042c40d8040d40c00740b041203600151a20480d000150a080080360b10607081904800c20031500c0c0001a540039960407851003030380580072490010340d102c602140d12010907903020608140300c3d0425213200c03030369401003043ca03403808041004d01000600c0143c417a502440700c2a06041130b1109000c051a0700300d903c490241c0001c0320718204035802e40b21160304550b803100d440d842511144003041000c0c00f150040101c0c030b08031130700542d010000e9030706580d404e0a452200038079500745401440d0341d0f442a62801070a4607251000100241449804d0070060352000e8650741c280142c1e4603042c10980230446800300701c01071440001c01da4003014450502a642c0801c0070520301801c100070304450780801495140d202c2d465600340c440c4091203024035002548182d2007141c503401c03c1a003500070703221640100c0c81c2d840c8c0c40b51400c10165a02c4150765400480c0b034144178200840b01404200038007601e40024055101d8601844101039040c3e0000c0c001c84 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 955673039 1250 955671789 955671791
    0x219260703080c0d320703090e0a090507140f120f010f0902040c081b0c070503010c02030405100509150715060e060a0801090c0e0603030c070b031503031201033c0204 73
    0x80c91546103c5d1a00713400301201900545034600307080707185c1d043c4001440c40f64080d0602102465a4180360400030030103d03252413545803140c00c03150810004104c100b024080104600c1d10181d4000e01003842c01a240191610541c00a04201220390003400040a55074181009000102d40400e401d0041e28284400700d00035071030500704000061203a0009030084c03001c00580034814407c110201040c0c0c00202d0b0500c900d0040c1940080c0d956404d10450b83c100410740c004d0342c2c446207400d0410460100e042902001d0001c2000001d005955030b10003040203910186900343c9403a001d0400949100b000721401c18164585040450029103010382d8a114170002c460607400c80d9190700c07403907083e9403100300c008050400c0004140300d200d2022280e0b42d4804000750441c0e0910024020361840c00701668071100702ca05000090149200e501038003030403540c800b034004610340800b40da1050000281403101403c0501e40b40c2d9242c0e0aaa5068140108141500c1841c02c00406007107641c0c01507a1808001c902c15 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 955674289 1250 955673039 955673057
    0x63406021201080a020d0b0612150109061a220e090601030605130b0612030909241f03112116090303091406040905070c0219260703080c0d 61
    0x41c003030010741c03040c00d145c1c05010343d102c0c0c0306183d503200b0920402078406a40182000541104500100b0288454131040c031000380d0513515100240003100e0590b00712a00304900c500103e41d030118000202e61120407003004210b011280c0f40200343d141710080c2c120707012814008060003080540018001d0581780900c07010403d17a02e40941098140105500082c04851544001002c901e0002c801881621514054034a0a401e501c0024402081111b106010255150011030804090703d40054180313000e503a50014091510310885920101d000440b0805071200b0964160342c000704155140c10140da4111004107040c020108001c580444685602c0b0664a11000b1101d124505007400c1300e4060b1106c002e424204031a10301055030021400e5040202003200241c0c41705203210341803040525550781c0c10a00f01500c10444400c3c04c140c85000005030000c0c080c000c03e80740c0c04400d00003031100388200140d0031150020302e0130103040e90300c0501180804907038007a0a500206180940ca5210783e100c02e11 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 955675539 1250 955674289 955674299
    0x30c010e06071d03071e0317070f060b0a1a0403020301050a02070b040305031803031311010908120c01153b0106050d02070c030302070810020306063406021201 70
    0xd41d2408440c10340000740304010850103400e030000c0d003420019001c3c056800b05900c4440003806c02c003c000c4211560041d01000300300388640d0b2000100150700001d1864a00726480c0c030340483d0351030043d4024048581da40d088034000c0d0b0742c0102880007400040102c0071545100e54070b00c1819003080c842170b4020750030700002900b401903038402c5808841e131105403602d40d51901e440444160300000e00030702c076041a0811480b141002000a540304080340c0001c0c64840302d8a02c0d000d4110700b1440c42d601e060001c40c0314140300701100410890218520301421a44550074415002e002d0400c06401000403610340340042200086181c07410b00d0035086a500c2c100032003840d803500766021100171000300241e40c1840144503048c0304000a1030302c014504009420401a40c5611006801991048026031301180040110b004140080710350381c811140d0460451420f01c0110710303203101d400c4075003c002c030207004e8400c4039101d092090005244a4002caa540c1c503100d191010083d48610504201d00311a0303000012 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 955676789 1250 955675539 955675543
    0x1b0105070206070b10030605010f05040c020f1015050603040b0106020705062503050408010513021e010e1002030c0f010b0a170c152106120d08070c0302071205030c010e 74
    0x20540c050609441c00c0781589542000304c00203014800c003c44400b6001010407214010a07018105280c981c0c001d0342d1a1000b00402c55107500141c0c0d040d5044610440f00809000c6043e001d20030042ca000701c2c0480d83d450418001c448107070001d95003c680442400144000403803510b050b91030903001c565805844208200203405418401b2070140d020030b400511420070710f814081403070f100342000c5060542380c2c00c80c6803d40e40d084440d82c500340c401200f054154039000c3e4400f611500c07002541c118200703600000820a104110410f8001c3d4080c2085080f01d03842042158202d5260311b0648940c04428041c0d14042e00500b200a4440c66007030101082c0c8081240408401d00d0f140c1000b0400030f41145e09200c600c4601054041d654030082c030282c200c0340d02c070300c0168142c032468130380c4045107141103010040d00090f0b403800c0d404035a000e0002d160041e60020040c41d005062410020035076605440c2c100c0c0b41611035005050400003900840d410000c00101800741110014000d02c0b0544104c00c61907 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 955678039 1250 955676789 955676797
    0x509100b03071209080703082715150603270607050a0c0302070e010f0303091d060d110438010e01030c05040b041d0c03060904110d0f051b0105 63
    0x1204a00c01000400c440a000b007036445801c141c4450081000f01e45621785c42c81d0b94105010581c0402c2086040164880124100186180090f801a00c0d1850740100c0d0683d51540200c150380711000ea030000c100c2c100c041c008246003070400200101e035a40342c0703001034031074005d00203044200301564190744400d40307c0c02080041c07098050b6a5070f1814010300e000102c4066000160940030350049201c04a602000b07050500e0181603100a0303007801500e03520300144039101c5607100b90200000800c100c1d2241c1d204196554020204480384040c1c480300c0e00340002d040c1c0303d8516599103c0e14209044203042d10280c010100c00d4203171140c250b071a2645104040300500d01d42e030042e00064141e0b074001015802640300c1c25140009140080c00d00c3c0d125007030058140d2098020092000104051245034283c1c1417032140e000b001040c0c05070a44c00c0001c04201412809031008082600c0072070345a0f019203400d1050102550407140e011038002c041c1c1021601c4410303110003103401400480b000f100c294003da08135 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 955679289 1250 955678039 955678049
    0x30b1504141e01050a0e12010603031e02030f0a03020306220f0506010201021218010f060b09030f12030a0506061c091101030e100f0204080307050f10140402040902040e0a0303020301050910 83
    0xe841d1203030141080310b03030801b4514201e07401544542d103203620100074400c21003d1817080e2155800401c1e40a80c101000280c00e465000315031003080b4514419805105944404003242009038503a250030000840c00102c00300d811480000b14050310101c901190040240d14007903000401854449030012420307482803041100340d4111400100790281c40c0d0204580300cad0022100002513102250580b03209686d11503104040c90500882c000c1003d14043c00358815130040c905c0103000004a6880345000c5000c000d00321150f80c0da40e00002030745078403403608444410b03800e40382c0c040c0310f01d20500400004003030344034042d0b0341c40c0b00342110307010503502a20031320514199010041c00140c00c1c510200000d0401c0800c03804485800b0f00c80002d44210801c007900300148500d0203048a8640f1100d428a03041080140c1008542051044444404100701140e049601500d000c64011814000b0601600e00202c014600d84200031a000a00d9895809141644c5080b02c3c0da6081d51290384008a81c40d1950050f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 955680539 1250 955679289 955679297
    0xd06031109061c06230f012411030d091506050a050a03060203090c1008251d0103090209070e12030304172d0d0b0909070501030b1504141e01 62
    0x9001000c004140a84031113118a070045140394a140d6028001c4200c809a1042c481c002024030040c15404c1203010702410301c010003038800c00b00c01c1039100b68000c0260103060501c11513000380c2e00c0148040c0211499035a80038400d209100d5503162900c032425191090000c1c451400c3c0006c9800e2900061a5045500c000d0404590f981152110b600a51000c2c2804c5000c3c400c407140d02d06103841c3e80503240c0250500f0b455261451500c0e80454030384020000903a80722002480380f07400c1080c1c2145e075560b242d565051407104000c1d4982c0c0103034018844840003940c452500c5082204489c1c0c0007507045812070007612510440f00b001c0141036541d00058500821140405905080d105004c41c081d04403d945000c00391545001503d00c0855101503a481c02d203808030016940542c0103480c028a4044030055401c0d800c2c6203004c070104e07525520140516410551120418001552041c06003055034559400385e55480d50759a410500c0300c0d0072600c40038000c40c6130840070707403015443c1c1514150566060b11 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 955681789 1250 955680539 955680559
    0x30b09010902210106051b370606090b03070618030f0f140a11090601020d14130f030201230706090303020714010c090b0403080d02130b0d0603110906 66
    0x2450180d049a0f02c800f00301ca1968070990070424658405a00801c5145c4030160780d245001e0f806151010803040d0f1584c181c2c0301000205011445002040e8a0000b044191025407030582c81c25104502000010f460241000c001054070034060307005580c140821000c0703805c0c0c08e80c2c41c4026500c2000d0800c0c10020441c41141c2000811006246030b81028030400c0345e1003004500e691980101000202100020362041400d0800c02c00452102402c07400221603012607483e10b600001e40e00d2149002010400900700411505241e009060b140c042000c8a2840b403465280d011112070300c045413006900040031038a410441b444500c49483c0700340500c8056038507001041e143e10026040303610f022010507500700501004208028102d60303213031071850b001180141e604c4000401c10210f9412034401603608120420016a083c0c04070340c0d1034042030380c02588070501503102c04001c52407a409207106a100003640c82e0748000c1540040c082e40c1c0b20742035032800609204140316012808403203a40d0491951a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 955683039 1250 955681789 955681799
    0x8060c030702010905060f070323060d02010908070305150a02121503070504052410050904050a0b0a150909022109100f14181c020a1b080607030b0901 66
    0x15070340007800d80000b05501c0b08550b2001d251600498403c59448401820700c4004c039494010070f04598110313100b005100881441134101400041c00e05889200350030030340000c5900074402d0b403008110032001e8130080395403428002c0e00c0d108203040800c004c800d010006081741d420392003911402e004840002d031132950790401c0e80e014a495100f03225850310401c0400201d0b50380368004c50344a1258880c69041415007044c05082081c50484058807900031841d4855402c0da005050360b040b03d50848001c41d0580b51307000f504004241346c183c05030300154600c01c0801e041907900d9001c2082030007959240340c1259504030b01012070103030a41d0703442ca82c42c10f00c040c503904516001c4d00c0340e00226007070b041c0c400100c1007e80c03100031500c0c482079640c0e100f82c49000310b042c40490100380b0f541c8000028005a00c0390140114661211140039074a138044244200c020803a600c2048491150741d80034404054840000d1103880603081d0741d2144c0403491040300002b42d4150b1180c066080f0011025000c1181d82c1d00f40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 955684289 1250 955683039 955683061
    0x72d08181905030c030327062a0c0a0501020903060108010501030c090507122901030203060a03120c1b0f12051c11070e0402030c01050316051b030703180f0806 70
    0x7600281c4461106100b2804c2000c824001140100303070080c0c00012030085400b44420340242040c0010b03440c0c20007020400510740c02c0c0700000d06003001c000400b480405143d50002180103220507201240704054050b000c110055000303028041c000c0342160440ea0741e07044d5481c241c4400740401413512541900130884c03443d094104036084101820440b458500402c45c9e4000c40d0074482d0241940000c1c0940b1100019801c7c15034403540d0700a1805500d18034200c408600b19020510008003032003805c0e03221b00c11040c441c86201c0d8406501140c0d200c02c88950660b441c0e044030b11030292242040e0010780000f10040442c42903140e8a0f800070142c0101b10211a2a1140414401c0105d0510110140701c041c000c0003841400013609060742d40002d6403e050060600d0117401c0c40050341800010010701c48104480400c1001d410410310b416940c544d2214161411085072303c0d9650b00921002c41c1c2d5004042e0401e10075a0704448003110250241d50743e00f4240c03210909445030341095001100854030501c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 955685539 1250 955684289 955684333
    0x18010608011a120a03080703020d091b090608190c030b0c03061318031d132405011e1209050a050c191a09030708071401030605010e09072d0818 63
    0xc508005050003040700c0c00b2b109603002c0c0e05013107502519500040d5580310302002c440c405006128810440d45040c80f4a0594840140b030300c56003042d00c810400c00c03c00c88241c1d407510203194045040441e1341071aa001c940b03150800c0e200c040c0f26400c01801000a111680304840010800c03095032075a25079a601c5c240c1e5004121900501c02c0d03051000103414580303c3e43c102d416140420080011141c000c50f10b07100c0d91000303021a45800c3c0304180d208000c1c036a4000c0a012600500a0078443985042c1c0c160300380c40e61040459200040f50420280c40e0610001050480303401d4029000da40c3c1c407104080400101d041c4070328600e0298041824203004080d007510302181003007a409a01850316800f58002407511447e944540b000380d005500c28004017103d449501c41c0e0000a080030303c15a0300740720010b019910301c441190300070750302c1e90000351085110b10321140d0f0407000c07c4540e141252452208040c0e46980a400d80c005c110040086481040c90b1001c22200809100c041e06100d16801841440420 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 955686789 1250 955685539 955685551
    0x301020708090d11030607020a0201020601050a150815030109060e0c040605011d04090822060807170910060305010507140403020d08031f0603090320060c0318010608011a120a0308 79
    0x101909104c1c541d2001c01442c0e01400c40b58000b08a000d440344002032618805030070050081040050402c1840802c4200c035000044a06041b0306aa0311440440c0700741c0021982c01d0352560030030f0440c1090103081c0c1d0010603c203046905442480034075000740000d654152180c980007814440c5045546843d030080c0c0812024010300110700c5141d103032100b080c0c5421034440380001041c503412800394a09030010050042000341401c842c240340214024000e1010f0b40c40b0340003034480050003e1140d50043c000102c04004551040210310f03200c0c1030907802480201d98080c00f040071503c16505641595080d9021aa802044020140700c84d0b61038108642002d002e045c0c15a0292600c0080034500320281c030b028107015038002420a54900300102080204071211940b403524010b401041e2a021401550110103601c0843e038030344071000501c590000d02121814a5440d1030740218929606400207050301100040d451400d01018040000e203628062450005a028070310100c0000d0040c09007a81c000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 955688039 1250 955686789 955686803
    0x1f0c02190308040308180d120e150d0c020601050d020607200603041407090203090c121623100207181e0f111920070e090c0301020708090d 61
    0x9581e0b5682e4005504150000c032480f04003c41c128010440700f4019030004102152000705146030b507140c125008801c615040304100b0720030341030f00c00394449464003c1021004042a42e4a07000c01014400400590070542c0050141c03c0c000035042c904031a0b04200e1b0303070f0010301c03683ca00910baa4400d6031044543c5455500a65424448010f80ea10540990310550054540c8000700d943ca501c04c9050441540040102e5481801480080000050007100e121001d559034580c1c004581c10551030031407010704075440c085c0d0f03214001c10380403481e08103007014070080344007158118905e0041094042c206d840440040c0d0043c0030401c105446042031505043c2c02041c002048140c64540714002a50b1075440600a0b440b1118030401a81a00c10354606140301244a424680e41b000c45410f40350909920f0020480b190196040e100320f03100d801800b00314008120713041c40c4c0c0c1c1da0b01007a82a6004485414642c05480301b507003c2c504060017207408036039014100c103141c00c03008401c0050440c0b0100003aa049 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 955689289 1250 955688039 955688089
    0x21012150b2b15080d03060b07080a02070305010c02011a06070f0314040911030708070801052d030607030b0307090510050d140a0c09200a200a0b04021f0c02 69
    0x3003000d6106018103003c0c1000395600c03450402c20101d00e03100039990341804052500300304100b420010000d5842c03842d404401c150303842c007100000300c2c07408000780c001503c5546802042051540c055001d82d00701080d480851072200340751400c0007114016100d000c0d10381c5074580c02c0c040000307104806003241c0d802c0084005085c187c0790b41c1903904848000d1518081100c001050210241d0000c0d100d59211081d40f0f0105076942c141030220301688414480c1800100c41849050650305c000c02804a0307020019040321154a0b142600501411208002c14002d014030280170070b80401038080e4030b20841c01d107140f5480013440c0c4001e01c4041104401c007620320303807008104644056000d000c804401801456140001410031659904070b171040100005205022690015042c1c102000c0e03a0301d018945c14030141601c1509440c01002d40300304075a0060740a200700240400c4500c500e8a03004070300a60b940d14282e16100f114840241074041500c0104036990100fa0040c9040540012800d145181c00045 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 955690539 1250 955689289 955689367
    0x140421020a1205040e090105190b03030f0706090627110d061a040609090215070305160b07030506011b1719020f010b0f0904030507020d021012150b 65
    0xa9400b404004000084001a040120103170140a1541251801c0003c1009007001403501524480c2001c2c10b00c3d205032220ba211032035540030300c1030325410311040704015a50300301071801100400d91088122042460020116035284131520118180d808003e50620090307001d459000041c0b650030b41c0c45901001c1c010104000400602544020900e18850002c0b4008514104070655050f6000011018a40600100582d940110000c6441c00310070503590740e0728160400b02d8151248401e040200c0301c101c0703c3c280401071503c00e1f0728410700b03041d6000c01842d16580c1c0119050320104510501c052404420200401c807001c0303900c42e046011002c000c3c90072400c040010742d58401a0800350160700004001c4240e80400e004206036003c00715a907038510f80d00100040d1600b100684003508104003c40c8800441d01e41288400460340c004203140d40c100c04042004102c00c0c8034145190718241030201700c0700407a1401100c901520203a40700c0c50700b0000d030011079031100c02d1300d0f4041d00c0d0140c00714a01840 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 955691789 1250 955690539 955690553
    0xe010e0f191b0305280b0d14030d05100e0a020903011b020703050715050a080c09090a02071e0503090409020a0f0f0f06020c0603011406091012140421020a 68
    0x1e811a034001d060b40202007900005022113400400120254045228803042c00380f100d401030740c00c3d400b2a100080c0c41c86441003c140fa61042c00001010b00c0258a4810f040e4a000009801070030600f207803c0c0182c2d51020b0850841d00401d105400406c0c20520100d0009c944d240c02030006032001400008030202c40542401c0b000900c503a0752800740e00504e10034401c1c001c00340b06440c0a1301014a0088002d6020100141284240c032110010050404086408070856000300d40f10404001c0c040405e6040c01410480254000c03501117030f11204c44003442c4500701000da420032401d40c200010314140182c850620010f030002d030f030040f030340302241c0329001c0390071420403080c0382c0600340608c501002a800c00d41540f1040e40250421000e55201800c10525a40d503c421241035542c80f940c01e5900c840a00082074840c0600000558021044000030707244c942c0c44030041c14007001e044424032042000c03803581c184194003942e014102d000054010302c006410100308414001c1e07148100c400070400394640300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 955693039 1250 955691789 955691801
    0x103111c0b12030f0d0b011103030403052a120a031104180c08090703081b0102120703060b070209150d050d020a02041b1e12150f0e010e0f19 62
    0x52080c0d80d1641e540081c148200c1c4407180d9019000158035240c2002034040c031030b00a40000d046503d45882982c1e4031a445000e1240900c12140100c036124101858043c10b10340010285c0c5c00300300b000c862441003105002ea0b04424070240480900314038034400c50701d03282c180d0008400703105161300c900d90240c600b4002c00040c4010901c842001a80d00b40070100b400c203440b0b1031460340742008040070038407000b81c0740812040200d90340250195600c0e1882c218034008426450100b40080d480402d180c00c00f507090700b090b688030b4225650200620b03522200701000c107000346500a50405012400a6841001084c400398540f0001340070460315230440da1030074a0143c0c402200001604030021384011410700b4028602004081041402c1900100100500d0203130700e02c8000c21445c0c0f21803e12450769000700446c0c0880c02001d14140804041409900c0c4012001d110754966621004000221100101c107035a040c1c900040308500745494000340304078001405040712401e56a45020a48005118482c0c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 955694289 1250 955693039 955693087
    0xe1b13030f0507050f03060a0504050a06090f02092a07060b09090a1a150f1801060509030639040f0f03020f01030c2c03060a090b0c04030f02010311 65
    0x148a01d030a85001418030080c0e6200b030b0701480411524030400d5078045103440e40b04544000004107503a903410000d1500482c51006230495280135039250a000c019504008810b000313491070a00340d121071020180148980b0211101c03c0841081c07014000640d00045c00400d020740030100c0d03400180e40001c1c0e441902511203590f40c0e84001550802c000c046580c4200000120f0074086840c0b400f15032038022401c1c3c03c962503105200550380c600d102d80c0e421b01c585402c2c120104070301c4500d42e118031000d0b142c2e90120050a00c203210303038400279100f100452101d5281040f4108030801e0b100c03040301004985149010114024842131001040d0b00f1050410740c0c00600c031070b01512a19a1030360040c02803882080c0e08035030406007040baa000403107070031503800701004040d000401404840003044005c54100d11300501d40c0b600a4000344440c0c826150054201c00d07010b44143c208a498141d0304022904c500c0c44014011049114103e000d580a54006040341c0d01007480301c0d281c0f20040d2104104407024009e0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 955695539 1250 955694289 955694303
    0x8030a020c24030c070318060504062a0b103506090c1e1f0813050706121803020a05060702030f040e0903090d0c0317040e1b1303 57
    0xc40c401d0707868800c20908007826050820061038010b041c00c06218440104114496000007901c20304051003020140c1c41c1c0160309405018660710343d40c1c010704c190311506c80c80b000242940324008055040e03400d0910300706055160040f061406640300e411881c1c008042e2000c428002100003243c111841c2d6502480c0c0e40d031003400f400d258002e50442c1400f04ca00015440355400710042001019002840c81e204c40c0013143c41400c445084180418614a500302040c0c01c004610b90b00d07050b1348041d809290303042061b80c43d0b2110343c1e80e98010514000b12600c01c041c0403948074443c104000303030299011a082c104034040c0842c9036041d0707421761211076a40e04003c0b801a840450b44400744030f401c0c0440717038010481d480650701c1d1410064080d0014051801004482c840784008510000d10402c101c3e40c52440142c0810496103940c01c0441c2032a8040c4010340b0407000d550524016201c4035001c94042d038070381c000c440140d61566101c840c085494081c2c1c2c0c0b078034054100107030407404160602c0200214403401d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 955696789 1250 955695539 955695553
    0xd050703121701080d0e1906080a0b1903031206150c0219050a09020c07080a080304050c010e13020702030c31020306012001060b0f0d0c0f1b020a08030a02 68
    0x8030090071242c1441444960120400050081c0000415200b0385414141760248170b100c9031400056040b0178850030808424a0039600140c4160000e40b40b41c842c401500e81001301c880301d0028820b0b5075800e0504510b0361203d03c401800007a020750901c10191188140000d1560b440e114841c070500401030410700841c1c9088220400c5140000364040c220b94ec0240701500c40b1310f000d000c10700c0108540210815603130080389941500344100700900041044100300d80c0306c10040d06080b11107600c10744080d1414022003d0201131940101c860029a20380a001904240704880c3c129009400c044e0040768140201c4181070181d981e07034410882c20121012560200003040f6030101140b9000110804419006004101c441c0e80c010030140320b03000303094151100002480035514010311a642000d81c102c100410300541d00c030007101c040c1c81c00e0503c000041110006ca01001e46204c0901840100059140b50401d0307c0c40728681e004419081c03000c2c00c94100f154445540f1170642d00260303100001070344010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 955698039 1250 955696789 955696823
    0x90f030306140102150c16052512081e0903071509060e0f060a1701080703060522020f1302120402030601150903110a080a0c0608070327020d050703 65
    0x140014150009000500650852901310303001000300804030b403e03202010800041c8524440400304110360302c072094039000588140000c0c030401038180721a00444070410040b84d501140301c160700c1c1c06032f007042c0c07214140351300408094000100c400002134080c0d4148049003190f14100b2030380024200003107506900e1910b03404000c0018002d03030b100300c0130000c8405140c6408c2d101e10080030305104040d64440e40c2c03040a00000d4071489803002c2940c8a2403000c00001031020404541c02003641d108200c24049610391850442d00c0c0111595050107184c0000040401880d00b200203000513031340640401d020b881e40c48902022600001950038031300900000b0003045150138041c2e20301501c805140c03d103c282c0d61400040030031246000050411454800b01031041c2c0c0c485940f800217040850480b00340d90084c0c070303207905010f41e10321440c0041030383c180226a05501038064070f0100700e1403a08486141c181107041c01401c1c0e2120302c043e6080020b8218141c003156040c44140051405003821042058241d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 955699289 1250 955698039 955698059
    0x10e060a03092904021309050a0b0a0f02091f111f05100303050a030c02191a0708061005070f0b0f07020709090b0402010c1502031f120203030301060f03090f030306 72
    0x5080c003102c51078000c03c40c1403603000c0e000007458025806480141c1101c4400b58158003c143c60b00d0003034050302c1904201e008200200000300e100d040705620500041440100010503030065590160384120b1051242140300020900d550200007149800103508420340070b501e09280d1041907076400c505465000078100c076198064a5040743c7c1d0380380c0807001c42e132464a006003a4003d40f141c50041689071160344200324420004804c0420b50303800050300c04e1005103410181c14102d86040071910f0400c0000982d1103018482a92040e81c01030220011002001400c980395400007000b168860f03c002c031020040354544a28910989500030307001014204080003a00c0c20811f584079101c0d00f401c041c00300c00024511444190410b50a007490744581c841d61520780c054142c0c403c405220644084104a4484040329031102c13040ca1031291003600a89409400c00085220030780a50541d004000400c80248035041c0034400102d18600020154615030310701045006040c0d09400098680000b403003051782c9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 955700539 1250 955699289 955699313
    0x1b06020d020d061e050909100f0f051b031305070b0a050913090f0b0601260105011b0f230114041a160806060c01140906010b040b030114010e060a0309 66
    0x245107040e134603c01803410300440400724000d003402071460201044285d14108411466901c0e4070780c0c1808601d01c1c80308440c0003814255408030399541004041400260318684c0b070744007240e0f00042c49183d5035560604005070005130300112007500c120940041c40b500d502014200c00703040ca40d82c00d9642c0a0030303401c0000306071a01d03405a200603c0d101c54000020b01c0c0151851f0015401902100c2550340c0c4070040e1904603210703104e0124003140415401100c50744188650580d9002d803101030b08c0358500daa004d000c00000f050020b20000d02c01c20024042580d529408079040301c414112400051480c0c0715909480c0ca032054407650f0038607078083c03004100e03030101c2c50000051980d08011041c0742c0000c1110003413040301190070601c5500340101c0c03456101c2104a40c14494007200038004d080c0b285040d50400903080345c0b00e0065006c0c4600110b040c4c18180e08407000c8440709a909410740c6d08042c45241c1e02c0c1140c07001d01e03060000c8001c80341c00d01e8440d540034121540340703501c0c002040d03038072400c0c4002d000305 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 955701789 1250 955700539 955700549
    0x302280806130303200313050106060f080c070507260105070305130210180e040507060804030507140709060810050c0c0706081902070b04170301050a05011b06020d020d06 75
    0x1604020100030680c118a50b401d4143c030380450003d003410004504e030180190000800c031400010408812803000c0ca000c4040e2081e0001c20196a03030300011207007040d031844014009142d030004550040145406450118050010b480c0b0341503403000c4003010954045c8030089100742003020b002e1040400c0c40340c564044602c0c03d06001601e889801c03400c1103c03100c41d00070300c00c06564142c07403101c5126040d44148981c81c02070101d0403e8503441044504102158120f52a11a00101080d0a441429514040c680c1038407424200444c0799205c101038401d40c41064094070406100041031141ca014500042103010003419805030b0099038041604c20050505142c00c604000d00722188000003002c404480c40c2d803501a5464440d0808409800d00c1c5801503800c0900105000d41400351171340002e0b028034401e90900018002074644501036000074807035180c0c00340103a0401c000c954007030103c0b004a001c821260b05840d5030f15940380e1003260011f8140540319a800304d007060245082d8850b203000b402c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 955703039 1250 955701789 955701793
    0x50417040e0910060e190b1203070b090703032a1502180d031416050304060e010906091202041802032b0201020f0306102a060506100c120903022808 65
    0x5052400803019548080c20400c5c0200b94121094449945a8802051420010b018003600001c070002d231030b81c82e04203000641c1c2e000107100c041400104001401001c0ba41e06803101301903000c0181d05c0c2d9075040c240c1c2c0c4c10407130b5a00400002e0340008207400c0e00a0b641410700a001a16001000c104940080178070658501170320810210102281d041002c13a800340301d440d502513a5407980c046511562104088000700f180c880841c003c9507240d00203070b0070940325034280c2e41c080840e50b0391743c07040384e41403403e10441002e0501012804090705240c1c0041200c00800344403043d0300303591039020070b14003091102e4142030002d0340304e41d0b41305440b040b89008412074100c2c4000e600f032400c54000b5200c2440080c12039803061500c90541d280050103200e007000c0c0902e0200d4884103101200c40344004003030907100112030141c81d00e40003801c80d02d0290040c0c080540560390313140100740c0c9640d078480700001a40708031042c080c0000002005aa0390310071070154901c00010000c0384010120810208451600002566 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 955704289 1250 955703039 955703051
    0xd030903121817070b060f0a0f081c05180409032f010506030318120a02150a090b0a050712180807081c141c0507110c10050409050417040e0910 63
    0x225164407290358001b081101e500d070314113181c04001105042c1c1c0d9803002c1c0c00c050348034000040c00400031504240202c0424454044460842c03421200c80c8a602c3d0000b545039032058501d0319900b0503900c0109501e00c00d0a003850200c0d07540d8841c190a400700c1000d0380f0ac1c80001c0301820394400080c002c0035040f8205500841c01c001030281d06000e00d90f1003c03405802012101c00070003540724208242200c0b980c014040b18003034480807015503841e5000319180c3c808288001400a5620103102c12100e148180d6683e060418403203564160b4910700c180014410081400c0c50522440c040644520040c640f4200030414a4500b080d0503051400484003154003c03030300103a040150b038000e0310051200a60000c0d180d91006840e2080c0c00d828003803080790080074601020020306c15044600c2070f0a5085070400c907807608440c241040710341c4482a040a0024030284410440f01b9819009240c0247c8180c3c101030a841ca602d8038410140c000d540311402c1050b1031400d00c14114000e2140c0a11034907070f85000e04c50 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 955705539 1250 955704289 955704293
    0x10f0f0c171302040c0f02190c140d02040c0201060306050a0501120b18070f08061b0a1d090f1b13060503060402120403020609010e0601080d03090312181707 69
    0xd40c81641450741c81c601600000206000340c500303031454070254020300c01c000c8064000c2005042074107060541d4007502c42c4041d100358003085008280740c503a40c0011407108041c10202e510000141c4141042e80080310000d140c00185e0325406248070070f004542c0005001b500d141410001d41c1c0000e0102c03900185800c1c014058948442d00004946402003415103454031000c012100100126a44800c6d40c000c0c03a4001c40d03191f800c20701010132100b00f4400c440071a120740710010100740300420300c81021501000328144450203242010152481c203c0e18241146054000c10744951044440e40200c6800000304010b02e070700500000c810704d032003d608900348118404055080301c1c042c0184024880d0210020b991039446030100c6094a1000e29070790b001c0c0c145480d010f55108800e0340e0b860280e5090149440e070b941c40005070035041343e804000500c50f02d404407006034010401c004060317040210300c0030b004980d40e80320f00844071004415150318140c0022420852984041e40b2003841c45c440c010800d07900 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 955706789 1250 955705539 955705547
    0x4231f120206090607020d0c09020d050c090a0302010f11010501080f07120317040204060302030d0c031d1f020f03030c07030311040308030604050a0b1309060e01062403060e09010f0f0c 81
    0x1034001000c4d42c0d6940d440510303000040b41040c010300f0003004a081c2d41c20110b4a5a115005000740c400905000c0c4040c1e00c0f6202e6108a0b070250200c0207400046200c0c04102641c45882c901d0b180c101d040c1802c04003031560107819400d46100b41c05c001101e0303001c14405054000e04000f40f01c005d000081055001200d250f50051005070107083e4000e1603141c00e03001c5010f5580c0c61307011600030740d4018108c41e08481300e00c0010f0682031884105802041900045a105401d80210154440d1300145034100e00c41903071200000013480080d22900f1846010182a221281080254014104003005a848032070341d14000b0140c6507034440007200e1341000d001c1040003507075040c2500d030005c3c0100c40c049440c0d40da10540304000c004410070140d001800c1a1381034000c03030311648040449401004140203c0b4a940c401602f641c41a01c2801d891502c8100c00303c51980c160401d86503451407510b0040707038003075130340041e40401c0d6070039a803c1e00740307035507412007070380d406c20b0034071070001c54013121101840005204a030280c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 955708039 1250 955706789 955706797
    0x6010e09190209180a0b0423150402130f0605071a091c0c0611031003080d0213030308072d1407080f1201090506030a0204231f120206 59
    0x46401c03001450454050300d0a8041c0d40c60120040d05204030407014003c0c440d03448030706890034184507140061000d140e041c18003ca00c029202c10500080f0240d140e4101040c1040081c1489115110044946246d580c0c2c0d000406848201d0081c450001c0e007020201c007115900d561184061080c00c0000703c0c00140c0c8040010103080c1ca81054080a44c0e5043c401414032411405200d45400b03521503404807203811108801303a26024507400c010040b00c2c85490a001c4c4020740b05105911480c4c08100f00048204004100e015100103001d410000c21002000c00241107800440c007050b4401c040003a0264003a00480d0354508640d138500c00604268400c0b144014081100c0e800c004d0141100c03403107900150200c1d08070a84c40b00c6030a942d1801106d401d60980c0040d008290840f07900300000869135000c0c0070b210700840b80240507051040c655420440105101d40c0c2d96520724841c0142544850822040d60b0703c40d982e1860200017030000003000c1c807802651034001c01440c40a010003980580c172410241d03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 955709289 1250 955708039 955708051
    0x30612150112210929120c040312080114091b03070c080c1608150c07021503070e040f110715140c070308070815040b0103180c030b06010e09 62
    0x342c10a002c182000700080062204002c168801c034446140c034a6807014139070045600818100070303400103070740c0d082c2c1c0120302c105104400503d0030712041c41001500d0201940250220030b0361468159256921400700d910b403141c000200e8100c0d00100002d0318103400c410307210340049549192603e00025003811000c8481c01e4011207100104c0007520080c01442285249608001100d446400605003e940c03201c5888400036084404080043e035803100040207500c0c8000030f03900c109503940320702c141100d81e0060341040c1e9100071f0141003a2280703640d030170040d4001c0126540f0500450b95040a010590700224980c0c229207142002c00754003912449d0503200100e0f444111143c2005c01d140e0301401800700768000c15102c0109805011a1741c07030300001402480d04c03c0d26a18060360b18800142d5009008481e0300354131503d11010a001458268130644800398141800a66101158000000748451040880f5100724a01c800d00038010a554041c1d440720092909900f22021400401c1c024030b405061 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 955710539 1250 955709289 955709309
    0xf0409081215040f0603230304140604030f1a0c03060a05090a0e01180309060f120903090e0106030207060b060405030c0607050c060f0a0e0301050c16020109030b04080306121501 78
    0x8a603070840e00b141e2003401030500800a0184659102c0c0f0b580007800c40f03100845000c112189540c607401c040400e4a00003100c401d0241d800c1c945490b42088001c2c0c3c40969496000c10200408000520346100b1070700c04c80e0150070b2003107008034010080003511201802802441409104010465540e551f4000c01ea030402d45059120751500c00e10000130709141380d80c01d0032030b5090a049440001031091350044031030195840c141040d07901c060031744602c5940c1900d00d000402c0c0410140e001d00c4290040d85c9030500c07078a03000300b58a80d51810780340310140a0b000240041d03000103008040c018140201300c10428101d800034541450700c80000e1b9100201d0000c50302880700030075944148042802141c040841c007a00465481490300d41c0c030f111aa02a802810118501030840c180d28281441064807800f03900003214900003010100d8955030703600700c00490400c40200760100000318000c050070b01803803140f8161500c2c0c0c10404108011041d2001d4079a903150704c0105c0ba01d01004419407800d044a2107005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 955711789 1250 955710539 955710541
    0x507050609040f020a0f0f090305060103140a0b0a0c02070b090d06090c091a09090f0a1b08100f0e061027050f010e060109030203060a050a18050c0f04090812 69
    0x320b005814241a9402094401700341c1240103504285545200c41c000d640f2110150300c8803a041d110304c40b41d408050003542c00380300144009170468103095040405601110b03440e00740c40d81c5040b03a4070000c9800100e061740302c0c000070701b4840d01001094007426400c0045810482c03081d002c1013070403a080601070121a1240940360501801c11254005400c3c600b030140f002c0c45030205540c00000e07034401d900d40503d04003000540340c0c2d1000b10300c1403c010200b2029003040c4001d23403a102400c9000c1000343c200f003482d000c40020114010000d042c0030521040c40030544510140c2d528041380c1c83c6000c1d481680d0041d20410a840c0c0249030304206481c1107a1b48003205440c0010300c00b5150107594503d0407880e203000e0901c94000c111038075550403103310354140602983c034440110b42c1408503110080d01603001c2d40210b030b210072203500090742c030480502d000210155001500801c3c0b060840c030a9415403c0705038010010b0600043c000300015081d10148020541d55070740070124410b94895400725101c40d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 955713039 1250 955711789 955711807
    0x605151e0c0a0317010843080d0e060f07020d050c1908010501060509060406031e02030a020d0c05191b1205070b0a0b150304171c0506100503060910120b160c05070506 73
    0x480f040c61540c40b1403c147c402612180d801e40d80e84052880b10020070015030341d21100389052000c540104030074080071070900800c0d9083c001040c1020b801111640100680103a5a481700340181c540c80940f02c1d4540d81d0300d46417a165a08507501a0400c00c10801c04103c107038110340703803132085038201d580601d400a44880d03c13100e082c6480b42c1c00351651398518000414403c02c00241d8001d0480f010441c1002c210f030b00005281903036188210329107202195100c03c03c00405502488102d602c4549a4400b00002d903096a50881c2c5640ca044880c1c02292000c10440f00380481500d00750f51042c0030040412004085500069030840141c41614084100000040800c2607180d401d100c0000081656902d548051005003503401800d0417502a052900c000607041e850060354568202d07500743c4800e8a10348484042c0a50782c3e10003401c1103000e2446420000303044442c5c008c0c084e0780c80e004030300106590401c801c0c1c4440c004940c1c07940070b0400013000070358004990089003110845900f00c404940d140100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 955714289 1250 955713039 955713133
    0x108180102191e080403021911090f040b0f0603060c071a040c290414011709030a09050904051209010909020d0902040605151e0c0a03170108 62
    0x150b001000351250040c101c190b07030f6000741980c07510030000c0d1080c00342c900700600121a826800c68028006134030200760b50024682012840c640c0d240a00c0c0001c10402008000c103d80490682d000350f9500300d0102000240300e140e005490300f00403400555042c40c102080040ea0b00c0c40c0242a100c02c074040080da070700410924184050131a041d4081100d401c7c6060f041080e03110030780d44514103948840d01c200384015240002d14603010181141000c1c00c29080070389425401c07042200300b5050046411100204821034040700303200740000001580d54000131100140000c055074802e50068008030f06000c002480468000c0a07856541062911604180c0040f12245181d0380508003d600c0003820101094154000406490080e20280015550741d03041c08513180c104480114074410a00480482122042056501451a28020781402901060941400b0190400314081014274016210744116914864014005080a420300340c150001502040442c400e125042d10314148220500c0052 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 955715539 1250 955714289 955714297
    0x6040b150d021c02010306140303191103070f05010c1b020d1e0f0b09070b0f03060103060f170d18170a0b0708190204051c151803080907050108180102 66
    0x603d80c0709042e094181075442d4005005007a40060f040c800080707100c0807040f181c1c1c26800000f9008500c0c040004130b004e4805007044c02418104613850031001f007a42001c2019140d07403030040000b810110b11615205003104d40c031003001420b00100034403100c1d040e52207140701c520450301540e040c44400e1580c0340c1104c030714102c00c2e801c0782a602c000010905110961040c80e031442c0c806d0390b14016988401d060250b030b0311400d2003000c0801004004000c0302280030405181c21100604011400d0742d141c1e0300055125080d500300c5415417114110b20300c4590010850390588e0300c0c803030405d002c811403400301d042c07120401401203141c3c1c080032007030240d00a0410001840443e406c1080d210f01c6003824580249081001d6440da65103034140e46401d44800c405100301c408403070000304003005504150505245824582005550319085142c3d4200f0780d03855401582c14100099101c0040920340b403078058110400945842c1c1035a00102d001c0c000f83c0d0300085a00d420a102105444a010280f40c41c0e5001e441 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 955716789 1250 955715539 955715543
    0x5040606090203070f09080c030618150103061b180b0711060a02031e090904030305070c050d05040801060b07201302180f0402130902030601110307120e0306040b150d 73
    0x310000401c0300580e48003044811405c1d09a4443d0740361540d40410030341c0d40010203042070303054200f000410140d50038039000010300d03191001074031138001902d500c0c0c0c10810001d038020345010b6203d9002ca030400c032081b1890106002c0c01d042c8900b02075940c42e10000c0c08403990007603501c0410001000c606220b02040d02079508400104000c0e501c1007283c0c6e00139125001100420100710341003030004801e0081e1004c1e500004805460b10390a0340e560b0324201e01421300074140c0c80034001040a1240030800c01d1000365003a03942d1307444060307850746000e243c14219860341d030124403c4401031006000142c42ca203202203041b4205e4001030505500040081c42000b000d407070700314099100161442840c0700390300c00e0765451103003100e000d8140b001000502092f8400d00080e40d01041c280030080c0008480ca60180d5004101031405a502c0c0c00d017090070070324541c40381400f91350801801403155410366200700300b20b80c40070058018051604140e81e451011b000c001d8018400010f0381003801c0640e4a40300b20f0328100c0c1c0c4d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 955718039 1250 955716789 955716791
    0x90a02130b06040b09120a030e010f11190b0601030b0607110301021201230d030e042406020601050901090c0c081c02040303080a11041d0604020f030f01080d030615030504060609 78
    0x1944c0c3c0c00000c0200e030b008000a500500d40802d12250303d58021070003c0390aa0075841d00c034107581038040112451041c02e4400c000b031252900280012580c20841268001710071142242d04100900f4100c41050005065074101801c10b80d02000c2a140d85040ea00c07610303808001340b40041d50450019019005e000c0d03603a20603902c0400005140e0103080742a0300326800c0c000321341d003800c5041014041c140b0b00c0b441020340070440300e440c0c00350a41401d52041c030244242c024403544589907401e0a00002141e64031000c010b0748030b10f005001d50310f071051649005108910b410080c541e00c040d0042c158500800c0090203184010411168000100b0300e41d01412520760411503586850b4a0050b245d040241e51000c5c0c0245081001a0388540c180304803020b541280e2026000070f42d801c2c240f01d007441c0f402003540780c02c16002c0c00210040310395480078602400d8481d081500c6513051000423480c0c00c02807203c4e88101401c00d941001060a03404100325181858640401c043e07846052520290a056021807122 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 955719289 1250 955718039 955718047
    0x31a0904050a0605090109020d120e040507050a2d08180106170d0c0506011a130806061302071e02060933030103050706050702130c05091206090a02130b06 68
    0xc40045940c02c86148146010000c6446180d403903401c031860018001c1d0082014800c003030209042d860305000103076440ca02852002c0410001c1000d4400542d20100860408070b840d402c144d810412070000001c0c142e440c480c100109043c61f47c4100303044244942482181d0010034403c280c6000007100d44420f88000b4060300c1e0340d40b03da03810f4480c00d6508110711406480368624405110328800e019030360b0131100504507a400c05045240c070507842c80750744020300e008115126000041d502241c0080144102800381480c00e1814001c103040300ca94101d45040c8104100b40010340e1781424003800d584a4401d283d11245180302041d0075124102400d030f48110039141048804500d940400401f1a800744507c039600509a05a0480d010a010081c125040900c040c041380384180040d01c0540d000400c0c40d0b064151305694241240d4040c0c3c03042c00040c000003110609414007108048810520000611440c80c008160f19114071404800a2003042c52488003000580b00750030110540780003e0100d551 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 955720539 1250 955719289 955719293
    0xd0f0503070c240e13060e1503011b0f0f09030605040c1503022704021306020d02160509041101140f07110402040e0106030506060f07140105180a03031a0904 69
    0x404080d03442032403240d9030f60520aa212a41c070b008004600401034560140c100c50460400c5244c007024036482ca406540e80c1340001d407104840306424040d040c89401c540300e1003071100074142980c807001c21030300503400107d071a040b03403550000300004008010318000c80046445001191600720650000d0899410503044c0010b01030350100400458084040c10500041e00d08130035026030141c80d0b401502204c4840c500032080662034a45a146100100300502d4800c0341c41d084245108039400010040e807140410b40d00aa40405c86e8040c5030801c480340d0704200c0d2031b000c00500304070f00080000b0144403180602110590141e400d88110701d03000309580791641d18030f00d8000350a0700009800d645c412440d0f03a140c0031a05252081314180c41e119000c0400b240c2c2400000c0d006040007405a94100360304000c2209041c09403005030500c684038012000c1e20800c0c1009150a403680a4105032440c1c0b03414420400d000d200045c0424982e41c0342c280820034103219010781090824204c21190845008410081 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 955721789 1250 955720539 955720553
    0x1603030507200a1b0b160519020f120a0624090e0706050a020708010203070903021e030c01030e07030501051006200a1515061d060c0c0d0f050307 64
    0x8071408055880c0c08000400a0303044a4a50341e001d00c0d0601c54014180507004142c0200341811a00000c026510300d0a80d2101252807680c025201001c104281204040420100344040141103240e03003020010708607140c0009044a03a08060700e4840d580c2464003002044040c030103502429048181000200e003161250701d034803507100d0300c99201459200c42c04510310300e240c0700d581404140d41004000450500c1c400380e5551340000c1c1220103610800c0f0000604203000d00095208041a0369503062103403640c0706200c2c4a824184c1c00c1c0e0450490041b14001c5514001914010040c0c2460081001c11031620464140a42908003404075401d01c4c0030041c0f642c1d24501e80300102c580310b588844100700981034005681043d82100e0351240c00964010010a0030503c20f00c0190040c10300000e07600c206c0a0250003280020b40c02400440c000b44501c1203050310310390020151801c10b8404030316240700e10060f95210341c03510b806039110b0108168078805001c0410300318010346922500300ea50719115810545 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 955723039 1250 955721789 955721791
    0x30f09050304050a17030a0f1103180a08031c020906040518060312031006051c020c1c09031e080c060103060209030c1503060d03030209060409201608030c16030305 72
    0xb5024042d44c00c8005014141c03031409250b40c1030160043d40c207240382c0e044201c0f292245483c1c0101042045104c2405c6d142041c401012039041601640c890200005c003404002c40c201e0340a558281c01c06d00a1644080907403a440c040162110300c016682c03d45600040c956000d55048a90440200024202d0008070f41c00704074080c030011400c072080c9602e2074010480d58801150416000c3c60814820842d15021301c2c0a071080071410b40c0250541c4003032054040480c4c00c031542108080c0d001c41c8410300800c00d28080d0f802c481c0035916001c2070341402e42e19075200000b1090a03152044048481e06018444040d0544829101c11400d0b5280381d652410204c01942014440038464061203920308054070706614244002030106011500303568442d0100164298084000c5c3c052503001c20840c1d00c00d90b82ca20007080a010360400015210705035051a04112000712582c0041e007800300402c0c81d008202800b0403007180d510140031a036130b94401002c6002c0b030040d403800f04d808081022100c000c240e0150001c1d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 955724289 1250 955723039 955723049
    0x11a090432060a18051504030c0f030c122a11030d17090a1a09101b0909020405010917030408060a0e010b0414150406210b2d07030f09050304 62
    0x90000c0303468240b130303400001c40340c0000030034a501544090101c58444000250301900030308000c4034600d200c0d154400c0041001000720000781040e80460100f0000c80622000340e0154940b410805941c50520f51045841c04080b01c003280c0800f25176010010700c0503050f4101c04014054415a500d40c2c1800b801602000d078160b440c521007140001d02c0440d0001d902503c51341c1014000d50901c0444640103843c1c034001e001c18581d17024050501070741d08900e00030380b2060301841c11002802090000c0c028545070150700070154550040000b0009680c2c0079810205980140d20602d240d11000090740d843e600c2103901a000d68002d503420010034021680c44204111002002030000300d00010421045414030402c030b01000c00d0b1007001c81c008100b80000002d0814001c0c000041403034030307601c1100034094081146000c283c04071000341c08004114500980000d219040300301140e0300e140d0851002034105890004c81242180003880c010b10a811030307907400c1d04680d01000030100344d013029130301e0364000d0181c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 955725539 1250 955724289 955724291
    0xe1e070e0912030403140912030405040e01051302150d0c050912010b1509060d06090902010f0c03080c0304030909020a090305061005090103060203040201050921011a090432060a 78
    0x500000d0021440e003440542c0e00005a2079540c4075642510b41d4402c0751408902c064050241c013055440c0c07100303503100280c40c0200858072186001d08200580d02c412040001ea82d050100340200c00c403980e070301400941e504448000c0b450141d0b0b45903081a01074440e175048403509113500c80d0520780c0c100300148181b21041e03484000c804e240324880c50a1307172400000c160300043d124190040c01c095007009007030000d4004226030b05e40303407482043c0025038107a07801841000c0c0e0384030410030841da044010000c82085608010071482c1568902500900c001843c81d0a040000800102058801d0f03440c5000340410010441d10350403c84001807610b19107010441e05442502c0201e18000d610340d040000701d039802400d220950382181d40344406500040c00480c1444024010891030b56682200b100702c4100302049490381c5440c501e0800d082d943d000e441d1492020903000c002e00f03692104120968071031341041c08414540c1d4814103020559440c0d12815510150102a012108101054450040c150800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 955726789 1250 955725539 955725541
    0xc06090506071509020a090c030f050603060f0a0203040204020403210807030e07030602070f08030c0c100501030213200a2d0207030212030702150a0813150e1e070e 72
    0x4140a09449420406000c034100240280d00d2003d207030300195a000d02c0a081d000c2c0403581c840f292000c4da12945a10070210351204602c0c1d180020901c10b01da8080b8040380100002d081c0703002d030388164040141c07082400d0346e00000040d096444540458004540c4500d400d84690752040c80e41305401c14240c421400507403031340007180310030340319008100205c14550040d20503689581e80308002580070420462380f040c0340780c000d40301140d2103d01451040c0280690703070782e9915030f84051604281c80c09591040d4070b80703000c0050015031645013480322292154440020b0203c02c0126611030140302c22803006403060005604000c05511465001d0b02c42c0f074024015162500c80e055600c5284034403481c40707005030700041d420000341ca040881608182002425a0300e4000b203500451315416400401c1d4140f03070070014842ca4965845204d41e0b900c0075651444242c100e140360b41c1c00c104d166039000c103160b8080e1207544902001c20300303010a841443c000310803250030201380081030341c03032303c00510440900069400c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 955728039 1250 955726789 955726799
    0x150303080a290607151b02240103060b120a150e0606090a022508070213050601120c11150105120a030507171c06090f090b130812040c0609 61
    0x40c0c107050602d21156040c81200b0140d002e0003000c0c0c005050a40b84144c1801104070195900e20640c81148280007094505400c0c5e5034000c3d2a1850740081c0d004000454160000000b00c52441c0c2419658040c10100d100c920100000f08042c050300c00c0c4141311b00861000c41c041210f0107861340c02c1016010800c0c0222401016002c2d01d8110403500d95400960b207800080603d51075900501c290304d041c2c0c400301c40c40183c000c0989600358810f1b00172129041e0000d0840d007540303031030390b209800000c00940a00051811900080c081c10842c00305c00b0141d40c8552000660500421040b0880d920003006ca0b500210f50500142c002e40007841500c0c01600304601c1e4003c02600031540c440d04c260580c652030302c0d1401b155070300c2d80e43c0c0301c0c1c950700f8200c1603000b03003c04e08445086c0907510b000c10340c420381c012034101d0600c60200126000e040045121901d00f0000f0000600204800caa02501400c8807483d40300c3d050030324040c3c41c070811030b0603140010741808000400c228021200c0c2501c0450345d8060320240c0b10 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 955729289 1250 955728039 955728071
    0x207081615021e090111250f0b0d11041509051302031b03100b0301080109050f190201050d060f03080c071a03041b09050901020405130c080c030a150303080a 69
    0x100012091199120303400350340300904040203002400062404284542d00411101d041c00400a10b0f0450801466a80d0b00511101203800014080238008503010314034042035404030303106008005040a03241c0315800780c40038001090750020200c0c0601861380c0400d408000f450b01d2000e01440348245c060340c10841c9006210310a50780300d03036444014400c1c0c01200c01b00d00c07401c07600003c0c0b41001c0480007034004140703040c001c4080e5009007143c0c000451052207624000d070030017921030161070482d8044200000d40c1416000e00701d019a0302030030002d96864ad080510005002e4035000120781043c41400017041100d400b00412450942c80c05a4081035112501c0e801450380d00701640aa0040a0000ca000302d034890b5503c10300580365a203061201d0795a215407800340ca44c21140600f45941c00b250822007410325120104050914840030002c18902c4d20303014000d600b000d41910700a00780800010b8201d00c0a600885440c2841034901035074990300c0c5401044070b54105c4105541d0307424980641011410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 955730539 1250 955729289 955729297
    0x1b0106050f0d050a050a0b16020a12050d0f0c0e091b1c0b18011703090306010608090a05160302040c05031005040e10060e040308060306070806040c03020708161502 72
    0x40141569011252071080080000d0480020760707180c003407040010001001041180341e890f21178001010a444d160000343c000404046c160300954200c0781101000600180e04030400003003600703015881e62200030207003000700701020118805614254810002d50b4000228503003c0c8421150080956070f1086007950b80e007030520740c58244c10002e00010b03403900d2001d103000440b00d11104c4001648440c010009180140d00451180300b0804040148801c103e103146240207010340720001c4d803802a1950100307a403204148503020800031580040380011000340325074801c40307401204481401c0d080b092201e010404c188801c81c42585401304007413665015006032486050342d903242071416450075040c00f024000300c04506500740140b60841c040c030756440c440c00001d4070010041000700c0c54245009041c5001c054100c80c4030758841b508225046a121101661044042d00c0126003040b03842002e03000f034010b2100007807035043d02107042a40356440803807400010303020f10940300d42210343c44100c50480c8a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 955731789 1250 955730539 955730549
    0x10110a09090218060706060f0f03170a0903020607030f0210050105060d0b041e0617030f03070c03052a0601060e030a08210c0d050c0a08060f040603050d051b0106 71
    0xd412400c0101e901e069014180300030806080200708852100040c034281d01c602c00843c0c900b5580c1d00244940070030000110003600c4911741c540d590301e00b1522002803149980d000f0841c244000506d07140780b54441c00c1000c0065a000d0915500d6500c0340c41c02800040c00d1100540040c8030360882444c521100e4041c8038100c4401622007407501c04081c0ea414082c0035140fa0140d0171a4407204800d5808110303842490300c00340451000203109040490205289002100b51006a03009110103200c41500304210398000e076080c14101c0da400310301d01d0252107502580004030300381520030b00014507240c00c0d40d203015601c1203140c00740c03040c036130300c985c42134034201400c0302c03c00d405074004080440011010401090603000b00c0c5101d0b030b00e401811060502c00c160440d2504001400820411101d203103074014540c200366409019420060700c0348c002000c100000300602c0c440c1c10545400c906548441d44190091038011003503c9044540490207840d9501500c015441d0072250f45c0c42d100c801038103100b0b04d02070303035 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 955733039 1250 955731789 955731797
    0x7080403121d100902130903140d0f020a03090501140c03220f050304060f1b3801081006142206140a050405060117150d0510110a 57
    0x41000c4009030010200360010044840c409002d54160120401c0700310030594451a02080810b1544107101040041e050000c01103414412090000f903002a0800300010840e180301d511030b20005510005010010000280d00f480000d031080e51684c1500110b01840c080c1c0028405c0c48807034121103140c0380701140d48850050701030011481c8200b03066006156480c11140504085002c1d8683d101c04000401c803c8030b06600009040001a80040407200c3ca104142404000504004541304c4040da0412000304242c0c0041c200303194801c1c0242503014082c0b84803410341e10001e01e4001c80500c2000a0007a000203210388000704070300c80348074028042134644201c0c040741d03070804180c00c3c84a00034801440801035058080392050402140c89040c009145086200c008510392400744000690240c00c4140074034101000c019041c4d070044e0703580f02001549208a80c195031100c0c917482d68012800185540001e4504010091081c0000d40005005950f00100502241440303034048520948102c84046 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 955734289 1250 955733039 955733057
    0x1e0e16120b040b03030c0307030e032b0c060e06010611010e0a020d081c14010f21210207082415030a2102160b070206071506170607080403 61
    0x60601500210200300c400b0704003050342d0720315200003400c5403c410100c6195070300100c1d40c078041c168450070b40022640141c0c06080607402501110405030f00d0f407891840340e51362110324642128070910603401c0a03508580c00b040f00310902c039020703a2180e40078032803140020456814080c12640611030b0f4000d030300600340141011000ca900388082112a4081a0740c00b0005000002c02d980301000c0301c0407280b06403000010080c0c10b00c2040c402d4060180c00c40002c24082003018443d0760f02c507503481840c040c0388031716200c1d15a00c0c51800d49980c0c5408540c1c500409804158105442e800094440c2540c04620950309041c141186803450181e02181c014039100b03086001c90301c070b2040c01680c0700301c160000c0c040d00d0008003140c48102c00154824010204188000350b00040030b9030520100290b45d6000305503280305890010a0100b60085090280c810480003507902d007042940480d5051901201c4000c2c030480c0e5403141403018920440600300310900a00d000210b1092240000c075100c0c2d0340c941c440c1d2200e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 955735539 1250 955734289 955734317
    0x70501091d040c0801090804030b0121030509032a09130b1311060a0e120109030206061c0519020114040503060f1f14031005131b1e0e16 60
    0xe038a00940151150055843c02040c0440c080c02021016401140342a03500c910b1494100c4800a05a010300c00d120900c081c182e8031302c1c81c100350200303045170503140041e00d903801680040c1c01c000d42800200441075103d0702180c0901c141541c4140003501c05c44120b007139a035864200850503860524002c0a168031640001c2002d010350091700c1e1a00c0c080d01200340200c18a40c0490851341c40780305100d011030194020100c091500d0706030706a4001d143d08c0203110301c003c5550302075520640900081d00c0b0b4610103000c50510303071a406803050500d82000460701003130101c0b68103106100c03070240b00b41d000586805801950680c41001c450880f5400342c000d00c1c003907807201400c85040002500d5992036040c51104010f041c50f4032030000000c0c080482011303145444c44ca0801d40b8084041079101030481c205070420003101011580f0f03510360b80d0040e40c03200c007001e04880401d150301841e070804070005501c0e00c40e01c1080200030601d90280c0f0340388134403410030761500c1100405031b40801540070006000d139454084 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 955736789 1250 955735539 955735589
    0x911090607060c1b0c1a0a020c041802090a06080f07150815031e010b010f020c0906030f060906150103060302060315031207150b0103060f03080a0504230307050109 72
    0x102c3c02c1080c3c5491407a00601001c1c8122200c0340c0c100c2030720b001000220920040d0081e207040124014170022a0340360204e200300c040c0d29140c814100074865a41e48180750011b054140c41946000e600420f032104a24108226500804070340c01460406d01c900c0c20313580244840010107805694443c0c054a9803400c0d81c800498007220001c0107505906145000c56515882c104542956079862180460072602815001402c440c5a10740e15410088010b600c80121500032541a845000664841c2540d9540e0b801182ca030036003020380f0004d40d100c0d4104000110401141850040711320107050103c00709940011401d4a11030301019500180400104024902e642c40c5400300017406016105156150b084804150300714440175a003401d40724000700551400780c031624210b5502400c1c1004414200b500b92090240c40740001000d441000582d41045401034098030000c002031030b189010a605040b60f410000101c25400d80a440b6514020910358041d090030410b9414142c4141d80c2c00c03902c00002e40d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 955738039 1250 955736789 955736801
    0xe180309150403122d020a1a0403030f060f05060d1b0801080c04060b0d051b030709260312040f21021c0f0f05090a090603020a08030304120e01020114040309091109060706 75
    0x171040d8030072030181800285008060080c405140c2c00340545030704c0c1c1410080d042da220130b09200345140c0f80c81c82c10300a02c04114071002c1030b0740c1d003039540f030751100c0f9444898001803072030140000200c4c20841481c1009a840381c14141030301c03100825100c3c5810715000f40310650320507028040c121b9100b030011704c030700010581c456540701f41030348420301494040040801407039100744c40150000740455000d120741c0100703080c8620020f02c5030034108032141b107840c506502c2e4002c0c2204a0000c081c20004541400150300c00b8100e4550418900000300030901120070059055404200250103594050150300c00c2c0c0312503401c4400f4440d100c0c4050501c41d80c20441e8070082040350801480000c0c803070020300c0e031151020b0001414004000103403007401c5004014282c80d00c4d61200c0d249510420401002942c040390300110009036042043d4850300d080300507409002c4410420020000f508100804d240d40202a0411100a0a000c000751410f441c05948948902d00010b07810034401c21001e000210290700003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 955739289 1250 955738039 955738127
    0x40c02100c08090d020a08030103030323010b030f15030d0e150c010c11030a02030414120a0b220305032a0406020c01180e18030915040312 61
    0x2840c010400c0c00e46a4044a03508110400011114803c1201004003000340880f0348045000400103034500b656100440d100c140002400c154450300040704000784202c00b002c0707100c01c00d0a4820302d5a168410309009801c2180c4050140802001040302d5400c400320107540104090007400b200d003660401941e061400a0543e6003210031201840c900700c07034500140c4081d556800c0080741d01c10a9000061165000901844140e0810005003c0743c2e60000304880c01c80d2800c00d10010006d0f00100041e4200030108880c1210340641a541c400700001541c610b807065020003440d0104845804c03254040014100d801400f00f50304202103254031403450100c81050458180305030300c1010401e9081e40c00d41082d4040c02c00f50340058244171456230858012106d240425556900c00b40c5000c3e4800f1115102418070340480003081e500381e05084060040f5546881e000d00005581b01060840200991017440141c8100b400750000d00c11581c403802c1040c06a030000c2c9900c809120095114120f030480308150 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 955740539 1250 955739289 955739293
    0x60c10110c01020d1b020610140307120302060f33030a0f030f080a050c04140111160e010510020a0b0709030f0c08010515130b1c0b012103020309040c02 67
    0x4503207001c01d00003044503401c6028086220510312140c1190906110341180640d0040001c12103030f111160f26100c21100001c00c0014010603003400310b41003440c240c1100e10306503840441c010a054001a4240c0107918a40c1040c0c6240d9680f0400150003490251008020ba82241101090403198892a4810000809440c4419019502c1071a103d1403960110040340c100c80d01c803086a40c0041410780c0c0040300c52410300903403030504480c01d5144503900a0b6100b0a616441301b140782d91107190101030045205080710200030a07010401c0842c03401340300790403060145a00200f40b60030000a0010524031139001402c08850355074800d10103142c0242003000b004441f88000020440114025000f5030040243c440c003142026269400c4d5a401880204803440150802a0301c0c4c0340c0740f0008801d400c01d8040082c03400e107106c0c0000c8000101080c4c1c141600090b0180e1014001e0300c600041c12142904407803025080080c1104804500c0d0302c0014000d0307081030001c0702c050300b002d410a080c61542841 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 955741789 1250 955740539 955740547
    0xb040614040518040b0a090f0201050d09171b070302030d11030d020a050a0f0f023003091608070f0e100302100f180f03110f0a06020607030b060c1011 66
    0x42660301030034400d40d0f00740c0e000303070014801032082c00541581c104008a80034042038845458180c0c42c07641d0340d20000e04220000a4981c0c090802d40e000910391036200c00b1907074000e01498111000ba0300000540c00a0791015100100c1d03210000070002d0440c1d038081c0180010000e050410b440c0030703046400c2d01ca51400200080d03500d0040710302c0100744c203001648580b511280590f400078000000c505015007804680c2d00d9610f11140c0002e03002241240380d07400300000022001c500649403003139907803c001d0000c0220034403c0c6a500801c3b25a1407611701103120100700c0c2c0d2160807950310030051050b1108000e0301101808040f8106440c65800b1604a0818100c9943d03940403c0000080030f49a10000e54260a09000d00c1e501092103040110940360000200e0705001246000d40e415100040224100c0d41e40f811461302e900100b151081e200800c044041030351401e000c0e40301c031001c40e0098002031600682c0b200c03a28088040d01c45a5402d01b005222140c0303000003002c0207280000607003004a80902c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 955743039 1250 955741789 955741799
    0xa0b25020c1e181023040509012c16060503221a0603011103071704060b060c031201080a0c18060e0a1401140105070b0403050903070b0a180b04061404 66
    0x80d02d091070240504140f0452600c030300406482102500809003410766200c68410000e4001e01048080c40e00b01d400007410380b039803030b0082d004042a40002c004d65250345003183d803a911013501c216043c4c1c481030680d86200481c9401c45501c5040d801000f021440178404502403801100364581800f104182c076060303012103070302c03010791800074108618504c82250301002428182030003483c80c105480d90004d41582058403025002103080400e284105d00464002418403106030400210100c0262045a480c0e00c600c070101d41301d600c40c03034811040024230000040c90701000142080c0e059040f19407954924100616101d2521520f800c2c1c03040c45813241004038090041e4042140a0250064009141d210f00a0428441d0105034080748a00952a0130301210366000030450f80d0050340004002081d690b1443c0a8907a8002c0007640b58041c40741b45800705400321580d00421911402e91a50340200824a2003692408100c0c0a280c81e040828401000900c0c040e01c46a00007601e03120900c0d003082c0d168 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 955744289 1250 955743039 955743049
    0xe0f040309081b2106060f130c0807090e0402010c02040c1817070506090f0909031606051b031003170403061b0e0a030b070c030e030a0b25020c1e 64
    0x7120f80c0342c0341d0744541d81d1082ca5103015140c20003000b80710030704010080c0007000b10640783da0009185c140a903412110184c0290f030342280d11a840b02500b80104480c00d0222002481c8840c101d41001c045001030401250701a041c007642886154140c0d42c1c0d0400c0c0780307182c0c24440607284150324017050001d1210101b07940c0c502880000f010b40800000c2c0342c0190b9012141c01e240160310381c4054001c41080003003003025112005c01821403072003964895615151000d031546144110041c055000903018481400c122254125601403807072600802003a0466600b800c1003440241e0341401003484009040000407080c011021171041e0210b509400e0075900e4031004250b80e40800812040210451010a8180c1040c68280c109200b034800003003c3d419035035402102d0b41d026102070706100400445038101841a04044000000035068070070581081c50100341a02c001c0c0c2d01c1d80002a0007455280c000707604550145400141c0d03900404100422905020544864000e0401d04140c42e1210b42555214 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 955745539 1250 955744289 955744303
    0x110405070206431e080f0601081e04030e15070c0e0907060e03121902010e0303061e03030d0c05030703060501050f0904231801150e0f04030908 63
    0x450700502403c0c98290118010318041034461008150203040100c51122a020041e01042c0000f0150100f0300d074403a8140e4101803a42c0b45190010024421040000ea00400407402248000c0441c1155103580005559048044038031620801c007060540304250059411590014005e0619a4422280001054a03204a50b4101100c0e901c0090820104164116154000c0a54803065003050a2401c10641c031100d1900c100c2017000701358010902035945c140a6012402d900405040c0e4680c05286070003044959018460059483e2000e16205000e000c81242c0c81408018030880311001300003441c040c203201d214140c80d0184418466000301c242a1301c0b076203030f549e8070319169283c0728586050000d0642d07440b41c0010381000ac0a00c14000c00c1807101c0c0940343c8040c2d04803408281755a40805400501001005044503203410f90244140c8240494101041100500007405891070104074440004624030400107103002040c001200718400184c00d54125210307141c2a10900d07620000c1c02d2400103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 955746789 1250 955745539 955745551
    0x1d0d09030b0f041b080c1c080901120213120b07033c020315100212030f15030a081c09050604020d0503211017060c0d060e0109050f060303040b030112110405 69
    0x1000700c43c2c900c030303900c1c011030454522040d0b503100b10440d59540d51040400e0140010382c50500c40c1d88100e0350440b8445806a924155030b55170346e150036aa1301e0605501c481c1e0485016240171002d032010035032140c403034007900d59802452c88860340701d60002c002c04031840100208030582c62007200c00340700700841f450004501903580160402d03a21182c0d8010808134a444070703212019580291300c510780b03055036441500c4e40540d2a51000826503942c40310100c00070380000c2202e5040c0a00024601008006000ba1805080b4841055030300d800c0003c00b44100e40c2c0c03458019005a010400040042c03030f110840e559402e1140050b40e041040901d9484600341c01d4801400400c0b08801c1002046909001c00000a0060149218280300303880304681d103800e4090188401248005014070301c0f03c0180d0000c400030030b4140324002480d0784d07a11a40d0b00400c4255030809445c000743c40030070042d140000030740381030f20b000c80d101c540355034644044855000c00c084003c40d5035150110041041d9503d520480d440740e6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 955748039 1250 955746789 955746793
    0x8040f031703071202070c1e0e0702190b130c1502191a0601140c0102030f010f060f2607080402030c0306100b07060e011d0d09030b0f041b08 62
    0x9095142541090481156910408409104006085500050070044e003004e43d500103030b90b5250342c148201c084100ba0004130790015401422849804060f40714021100005203842058541707100480c0c540c410b41c0c10320258a40800700c402c000c54054840242c210007010071035111201349a030b03003096500b420b07403090300403490407103030380d9642c640600174050300120101980118044540d0349034a6103c980b880c2003261006800060196406041c601501d107441c00c1c1c005032541190082c8a01075801205d400002c100980000506001e4010481050b078a10381c40b1840f2928400004a4015085400e0310003107181d090340d45a2514071070303288680070b00350541d50802c070f6145c00d0060601d01000b81042c14007036400032007042000c5032405000c509540c0301c500c000766210380c9402c0c4000501000800403503154681031140c0c000109684001d201c0e40b50040580304458842241a90500f83c14840600366412002c0043c06403110311542e80c0c0d10611400c607a10350030f0a0601500808240f50304918225 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 955749289 1250 955748039 955748069
    0x1b0906031f330512041a151e031c09031a0601020d0e0319020103090c09140c07030516081207120e01020f1801021509060a0f0b090c0c03070804 63
    0x24076403210300d0068042c1141a800300707039458102d00800301d110700e800c3c80d01140f52030301c041820011000c100c09007440d1301d13501c900314600708201242c55180b5400602032041c61511a01d070000c4032010309403640c940c002009041c06510807828200100c881000a0003004000c0c500400001c408034100014003100c821a01c4c07907441d1550029140081d821520404d0107a01c05500315941d60020700c0010380c200b98180c81076141120f10068016008400d0005c12025580c0000b1031000103541c420364201020300c1c070f00c148907220a044084103103d8118090006607041002ca0000030401054800301841105014640300884220350b0700c41c07000b0358801c4000f0350504410500010f15014581e10884841d000314640003140e015080584904a4003650469049800500c145e00034800c2010159034240101c0759440c03c1d19095882e510b08484440e0010328282429910741c0003031103600c260810140c00c01d9441c0e29481440300c89a080000c0032070007440100500d4000480560143c0014008111443c41e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 955750539 1250 955749289 955749329
    0x420090d143406050f0d09080306030c0607030e010815060307030c0f0207050d110d080703050406120b03250803040824060a061b08030f0702061b0906031f 68
    0x1540d00c2001c0b240000b4540c00d040c0c0c103440b0006666101101c03a142022580c8014032410002c0b103020380c0715443e5040d45405054001d0050000095100d110704900340d40c85154840100010f80c083c1c0d1001500240c58084400025409040f8881c1c00c01352072021103000c49040e1380050525801101c5242c00a5264421550840e170080c581c4040e9450ba400a40009824080072a14040c08401d014241400031031124849032902c1a0022010750007001140d91440d0500713001e00141e12500c10700000440c1983c80c1040c1100c18445c10803d60700007000b5210743d4013110204040d101420a0504006104070800a100e4004000034001480110b02801032400304170049041c000340d070140031080305150400c02c0036540d240000d00d0266641c5003442e0ba1400d107409081d058050328904020401c080000c2170010740c500ca4407245216260540c01c80f902c80c2c5d90485002959802c01440c501042c41c1032000000d9480c0850107194001043c018414030030340204052120600c00343e1109511004800020704 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 955751789 1250 955750539 955750573
    0x603121e0806130f09050118110a18200310030308090a050c0d0305040e010b03060906041509021c0501121202060106021b010203070c0b0c0c0420090d14 67
    0x5044242070246140c5400d0012407400f003000804498890342c4d07120f8001d03500b20540d101c0030304103030401d0003000b40000c3c011400c1c048648140c001e45c1c9164220088160600d02141c1c06801e850401115840b218035500d14480500280c031140c003040b280089401c003a104909018602c124462955100d0305461400e014241c00301c0505155150b030840e036181b03804100006482102104160380d481403a12140c01c04440c5401503410204942102d04000903465401c10007860003010110b0b5812030383e0b2038a00402049411545103511920f426203020011408141e018021030780740441c54902ca080030cc00c1400c12110f00340c0260180403007140c03072242404180190584108070301c1c0004c0c00e081d4101a4040e66502580210900d20a00010180c10036403003402540c00c0b10741d0019507500703d2a19140c2c180d410b40c01c906040b001c1c520824007841100e01e410b000d841141c01154041200268640000c5602a0705c6545d40f0354200f0401e000b03a40005022900000c03034800b0f008080d10701c1c05000a0006 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 955753039 1250 955751789 955751837
    0xb090f060919091d0c0f13020d140a0207050c0405180604060204060219050c06031008010203240a18090204060810050f060a181e020a0c06060603050f150103060312 72
    0x441d40700070140303004459400001700c2054800301150415003c083e0707a00001e9518082031480d80ca030301d00211f908000d4188035081200c0744418090100b205950340000541217000d540000340a990190030100c0c05801c140d4465a04403000103403503240442e10b522454901032050303400b1900998001800c0004581c14842d03000f00d803071a00c0c0500f80220250300c03640c3d40d611500101030b00c80e400000c04104105c00849244005104003002036440c1c3c07811a50783c0d0310007a00121210a2151001540b40f850314203100c13240181c41c91582c000c1c2400c000c1034940c500030b10952900301e800c5942e5038004a45401d003004030000c550b1441c0004115443d01012106000d00041c0880d800390600e2101800072140840b482910002d9809001650b940d150310741c0c03040a000354106403130407880014910711060340000c170468858081c503014801140d503140300706c0888104451184200c2100c00100740310044403503d44003c2c03032051401040e010f842e905e8450701c030b00c80d42c12010081107103880d041130600c0c440781c5c0c00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 955754289 1250 955753039 955753061
    0x60a020405060a030e031306021506030f100b2427090c071b18060b0f0318070312090e070206070503070c020a1d09070f0b090f06091909 60
    0x540c282803429010880900500740d0b00b405242c2c40f4880009000c00030002e58024040041d04040740c0c5136101800781d120b0661003a070030400c803140800a40e09003800968500c0704c07030342c60004000b4107d0109203100240640e0b1811030707000846540c070b10004110005403108504100151030340d611403001c07102d0009000640c0107001103007540c2813090b04c0c1e035a884085503c01d4070340d06880e5a80d00c041c60010711030341c00300e400c208071390010a10104a51085580401103018030704010085991110b940e240f250094204844400c04200b000440c105000b64640291094940458044507129521100003580000c005400034940b65410803800001d0383c0712a0300402c49001034101820100c2c4020031a10000306440144003580502d5400c5484000d1550003c1c00717081e00180f011169808101c01c00801510141180c0c4104a400310303d141001c98000c0880360796201d024035020150007440708104021000c1c030750120061102c411700e42c64511240001102c50200505424206101441110001500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 955755395 1106 955754289 955754291
    0x12030f141b010b040e060108070b07030918020702010e04050f0106030518030d05040201031b0e010c110402183a2d1106120a05090c031e060a 62
    0x74041958003110140019410202c9070b903952070003030023004460b401800080001045440040611074424200141c03031a0356240c490040c85034403020000c3c06500029880c04540e4000078260031a4000c032030410960030080324100e0032030014016201030590754008106200e40ca8440498080a40400c595440d02012150409480305075000c070301081c2880c07806ca120109258010340c441c00e00d0354500c0042c2d0f414000454075003880d080140e030030400c5003000c4101c41d00d40e0300080514a01c40090029160705290a015907041805410325051000c81c1212420340700a008d0085000c030040317081501e50080d070030400d1008504880940c944071030906800b101005148503001054001d4a001d1401c2500b2000c3c0300740341c8294484907501101000000711003c0c40342e0b00840d00500340c030703049525940113007021911f802030a200c1c1d40c1e22185001c0404000b10000c00c10641e06c00c1c15440 = true := by decide +kernel

theorem cover : BRFrame.Cov 955575539 955755395 := by
  have h0 := BRFrame.cov_init 955575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 955575539 ≤ n) (h2 : n < 955755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
