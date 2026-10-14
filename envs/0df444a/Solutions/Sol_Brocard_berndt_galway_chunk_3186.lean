-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3186
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:55:29.00238+00:00
-- url     : https://prove2.me/submissions/a57d0b46-1d73-40b1-9a5c-bceed68fd2dc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 572841726 ≤ n < 573021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 572842976 1250 572841726 572841767
    0xc0601080d0e10110604060c030b010e030d0e0d06050906010906090b03060103140a050609010507081008150c12040302011b0e280506030a0507200303150a08012a 71
    0x81ca151404007610016150145803c244078415481303914079148055404942050700c4403000390605034548100c0329985000d18203911004d8000c00441d4980048185a1041222000e00240a41c480d0321203821140d602050802c01c83c03401c1c40701c040d21100700380a4541d10608100307001458840900070341804250007005000030340d28550391048405507950806205001c0c44180c0ea01190080c4080d920503c0c030640041a01c1c940510010b0810400400740c0c103032001032490912952200096155040d0000c03400d01005d030b100c815a240d8a4000c410a50742569150003c1000b010781c1900700c4182c0048480969103603201c2c4400a6441c01140701e40c0c41e8100c4604202e0721034074040c142051030f001d9210300c2c1c40c42d145070310b600224249a000700c0c0d0410a0381c0e1190140010307190b0015001801c11078034811032292502c0302c1100303616803002034144800b030401120901500d50f6100d07684801030030110300812040c000d505d208206c022800242d045a114960701c0110407501615249000006880c0c10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 572844226 1250 572842976 572842997
    0xd0903051507030f11072a170a020d030e01030f0513150207080f0304050c0a0b0d050405012a090b0c0d08040305120415051501050d090203031606020c0601080d 70
    0x404070040c0004110104040e200d0030348001e907041c6845500e011041c0f2000890b0356101900303101c4428901c050510441452201c00e83d00e0140b4880d050f081130307544c003000b000b400c0c1c0702c5011454030f04039080c00041c0d4003d81e2180305804050b080600c0002c807020a03201401407020326621101150300445400a818200014500000d001e18000241c01c007a440001410440e07107450b9802250845030030340c1b8042c680001480240311041010081850341100d44607501170406550349a01e000f401e5240b402c0750307112404242005029003142450001020039050071540c00c401e9011520201e104910201d030540c5004a40c80800c0c10454041c8242d80000700721113242030b5001c880b1890000c005a082000500820004035003004500740a1030280b000e0484080a01c00c00b0412100094280c000780d400294012581e0798000082d40c2c800c1c081c8400001d60203305001180c10740c4550409140d000390101c491904120a9501410408076010101e910790707a01c464440765514000f203c01000f00d00358118 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 572845476 1250 572844226 572844253
    0x9080d021b0604110d1b090b0a090603050c06030a0e12130602011b081b0c030a0806030118080c07080303040803100807030f06020f09030d0201051f0506030a05090a0503030a06080d090305 82
    0x1704090b564400e0b0020003019420302d00b0000c00b85410f0b00034007a02511192203c800349000f5003420040e1003e58420040c8610b5a0f0380c140d5582401c0c20381c640181004000140c0d140c48540c844410302c094502941c01d4442d5034903143c5100d0f07124040c0c5452203007142001007022441480f4089403540c2d100030003011200171b8002503e2400c001030850300361030101e00102e000c4e604001c2c050408008014002c2d51a50000007020340b040ca03004101b02d00981c036100c90f0f5104885041e100050701c54000d0842d0341e4452882d640f65080085e0342d00320310060301c80002480200444400150320135180c3c00f420340070880d22408001d480d10f130705d480042c00300002440c510b00032500c298002c003038a031b1030004110300c1c0100b55801709080c07e00c0c151164000d41d43d9082000780411082d0783c0031038100000350907060f050381000e00044180c00085d258407200c9555070300052a07804208111070105400c40c00302d0303480b0701e092210f580c040d08641c010880240500650714460701d02503644501079a0780180500f02c010719078031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 572846726 1250 572845476 572845489
    0x90614090f0d080919090c050a020c0d02030309180108160803030c090406050d0501020d060b09010c11030703141c0c0209070309050a020a0617010527070309080d021b060411 76
    0x420a66141c0740400000d0070301c1d40c9a040c100840e140421719803200ea46032041e410101e45803000d20800313108040101c0c00001d607002c16004510801141d0702d0701800902d0022038030318081c074454260441011280300f0010980800158101e52110049a843c0e14004515026803440c41c8680c8003903910074000b0604010101002d0610801d02030000074070103590701c0004180c46020001940e080c2d40c0002c803602da6103010b0080401a000e65048103241030b100c03500003021000031030005002d002050004189658042c011140196000080d0490b00c02c120b00880740c544010086010010741c100074491910b40c020060240100c1c0c0040004603d0f9030703108401d401400c0050340c200c40c14007596196600503070701c038a094000fa0299a94441c800c044c0404019102a4180c0200344141405181e0b071a07616982550620200c00b0002500515240e1000a030702400d25840b00416942c5d0200f0744a020840c154003500f000b400120040480f551844125500c032042520041c0c184000822800420706264 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 572847976 1250 572846726 572846749
    0xa061b020d120e030f190801030b1906080a11090f010501091401031b020f1902030d0e0a0308040905040201030605010e0d0b07050c01021815030f0115050c0d090614090f 74
    0x209012a10300d06211010381140c0c400310f417100603039002054141c83c81240c0343c107003204045541800c0e00750f035066071240900303000d00404078810805c584461a0789440260059002070483d03e00305e649441c00b80c505002030013204850326024102240000301c00d84503c6011074102c80b070603101c179032240d82003c0803180d01e0340e80c5905140c10b040c0c50740c0c0092584804070404014100650f0b014094580c0c68070501030a0103122482120854507029031140035aa000c02c04a0b180e401c14200404412040b07008240054135560001e4101ca1010070002024907140d000035106034401d0f6030420085848400564035800050311503031700106500920400501c1c0d101c50030750822200c0c140541010b0b9298001c0c0d003a41d008419601c05440140b01005260514a07440900c003140500d0507429880d01c83c40100c00e011052150054410f1041990300b1501e000d00c0858001b180c0c282c05890101d07000d1500900f021041c0d204550009441c110380300308644000082d100818001490b03501e010000300e00300304070780440 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 572849226 1250 572847976 572848007
    0xb070204020a2c03011d061906050d060c03050a0e0a0215130b07140a08250b16080c04060e010507061d0a03080906150628020a061b020d 60
    0x42c9034030407480e0f1420790000382800c031283c03400c10020300403003041c5400c0d110080c01c195250104c8281c2481c00c0301b000b0078026803200800140f223484106800c00c120143c095940141c0d04044811a480c086c0101908041048015618103010f1034884942240894652100c5280642c026800540051070110b010560046661040d40c0c20030180f01c540c00302180c038a40c81010b0442e8000760207406c00c0364140343e41d05c46600e404054004141940c855850720310420741c9003003081c4884d030789075012003a8a031002d0800c1c6410001c03c43c01031401d2a01040105407e601c4030340070504003070028143c00c544a080320113852032541c2d8440041c4030710005407101e420400b0103e402c2c44c0c80344075885040180d040c514095149860013058181032500300035081c0c20024201c1178240e004503003008064070000600c00c21213038080e0742659542101c03a18620003100c030401c2c108001e503560240305103c2540020120741c0b2074000d4408220b00c246815001d50f503102c441c078032000941c100410700810603000301c0d01034622492 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 572850476 1250 572849226 572849237
    0x1120308180f0a051002040b030f09190303140f010f150e1c022707050d0207060606030e16141c05010504080a0914091b0909040f02190b070204020a 65
    0x551484070b00b400c034940c0c06084560f0000380440180041000013601040403054114030307103414141000c0705480024400201e80e01e4080206949240c2004a4070b2085004032030141c141a41e8079008000d0000c00c0f2601048218075000305d803a6843c2290114100d80c003001c0340c2041d041c0362116011724070382005050303001d000c0a1400c20303283e61204824105a20351030518104045528810801550751050b0707a11221003030210380c0042c2d100c40500d2117403c1300c820305149840e002500804400f905c601c800080001c3d0030a0000a25990182c01681c81001c0030002c0d0364640314a40603c80d2000784500c40d4880c000064231105090341402c2c0c505814100740c0c0c940f0a01c0c481126155036007581e005590441d1400400102a030721241d1120090b006012102000810f086e040f900090584001502c44184da000b0900d88000f900d4403502225601180178190003024a41800d1020800c06800b2080c0d000f03a081c6841d040003c2426000c200548014126690070144187c003400000e400ca0100740d003d002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 572851726 1250 572850476 572850511
    0x1206040c2109170301060f050a05041208070f11040b04020702031005040302030403210201051e070e1c03080114031606051c0f1505010809030403060203040206090d2901120308 77
    0x34034018a0941143c41400080d03038075450500010305203000c08a040d010000144a52302603247d00c48119000c5800034443c0c14665455030801107054441d500d0001e003210580341c42c020400c11541200301803000c08132810441424104180801e910408400035410b40001c1901e03010424030b548041e40050081c81140e09090303d0380d550404103055040049102500c181000303480d55030901509502c112850b600c00ca603d056403400b50241c01c0c0180580c018008400c8008090741c8035159110903c0640d5407211844140906000e40302c444280240d01d40c500e0b0411401c0814200018010204d403200400e4070030b082d01d090310448127500b243c000c510540c1c14a0818850b000c02ca800380c150030154400c00010b211441411559036030f54590321080c14007010b4810441c00250102c2079404984e045807001d0380d266a81e00c0080d601d0304c1450f02c502e910078812220701c02480b4081c8000c480d004d0640c0c03941451185508803d0707040030001d119440e520303803031050840b000078801d03c010341e000494030b900c0300b0056 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 572852976 1250 572851726 572851733
    0x6090f0f0302030403111801030b07030e030f0d15050a05060a0e0a031a1308040504090f08040806181216060f110d11040b0712090e0c1206040c2109 65
    0x4031140003a401a4004502442030040300365121b680032008440f13000f00b1154180100c0c049900500c4081c3c026868140000c411600a4100d90800d0b40751030143d035076650a1140b0403103690032000c0045450b5260929031b29100111401c01425100020724003100c0524144c01c02000703501c4003540c94100305d0480c09004460329000c0740003002d5407140e059054407040c4042c0303104c40c18100400e42c0507000003078402c2e2070220714160110b074141c40d004e49001c5050f40142c241061046001c020051800074002000940b040c40490600d00501410501405c4d8411106213590b0703030310118a821042040402c0f0301c030071b01001d080c440c90286100e600c0124100e40321101c10000c4552620b01980e82200001d100d03107580c41d0038800e02c0c03840d10086014500b00ba0800a00300c0b02400b4510b030050900b038042d0000c615043c02089640000d091003140c9841c1490f04003010056600007104403010007802c00c0c00700740071f4903080c022075104840d650740d4042c0a4002c01a18401140b81c408401c020791743c1c40e030106022 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 572854226 1250 572852976 572852993
    0x2032509180b06061602011d0901031103191e020f040c0906120c0e1203120c19090803030402040f06050604060216050d0f060507022d0c030706050706090f 68
    0xa845600381030103034112400c00344251240141000d00c2100c0400c411010404805c079015005902031918021080b00101041c1d21404a00080c0d41d1201e1006d000008211940101415120301503050310304d0850a0031640218a04d40c00c001861150450b8452080b102c1b007804d4003888034001004503007808104800308007140d090141100004140034014803070641c00c50002c80c0c06122a082c1000b6004156000403e002d411380c2c081c9128803054100719946041c01c0054030003403140400310390b54038100114007440507442411014181c500d00704840c02c190780501280d00856420320051480c6607206e500b0080140218454640907d40c1d804000c43c01d41ca80601a1010305001c0c0c0003040c2a08050120010414103944018400d00d251032400340060403441000361800d901510110b03ca80312508182d0600900207044184002c1c802e1502d00b44004003110450303044042c00680750081c07044418151104c0c464040c50f03000ca04200240d0000071100d503c0030402a0244101045002a41c0c1d668041d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 572855476 1250 572854226 572854241
    0xc0a080a11190b2101050a0308070245010b031302010c06020a0504030201030b0d0807080705070503120703080f06090c09011e090e07020607080a09140601090204060f050702032509 79
    0x4030f00000c50701c021804e807102c07618200c0c40040108040198900070024014404034003000300007007001301e8820110348842c080d007030408201498143d0600390b8a001204030800b00c1c821054a00481e0031207204028000c16610f040e54000c0b1400c61450b51600c0d40c0c150061440c00040303041101c0280c0348004541c051014007840e920541d182a601e40c80d50000508be00d000702d003d03034401c042c54051003000030703401021502882d078480c800640390b00399810f000b4248041a809180c040c00f8040c64043d00c01c2c8000c0091480078801e44810070643c4464080c0c51690404884854000919501054400000001601002e58149002c03090070320400e080c0103054450040312000b0600c90f1070207105880300f030b40f24103500c400c0c144014119440c003550003c048040240c401c8080c079a9410540043c000a12a1105401010800c90b059540d54035110b00003980980b01e05000681100c00c1e000d07607907210b0401c0300d51041d0014020700d400070104403c0f0a01d4440d50f01450250010fa000000e0706803514042e00b02c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 572856726 1250 572855476 572855489
    0xd05010c030b0a090b0303040e0601051209010501030b0f16050c0a0813060201060b0f09010c11060307120b150405040f0e06150a06030b0120100e060402030c0a080a1119 74
    0x14905155005005851929800054455050480b1014146c4001040d02c0c02c803944141c00e280b480d25a4001a29288140000340c030010300e0781020403c42413015003246041301c1c032503800601c4c5507072400c05111b6851820b8a8513044102600c05140c1d841b4400d6010380600c0903c50156101402980d852810344e5012078010040300c0c2594104110142d02841100e006058102c511850304030f0588001203d0b1169415041c180006042c02405011840b02220b0380880e02a000650302c0c2800c9001402601031424800d178890b0500c03180e850f0600b44180420010640010740b0740c20300b41031800f040041d1580c1200800c003990703202100c0759000d90400000e40903480c0046590f691030b4080003800102031160300040709050400c0341d48035250f6801403044000b6850340324a8101e21040180d411700700540d286103842c0c0603041075014200ba04002c207105015501c00c0f030485408500c0d0505100c050361452040100f6600103c00c0240410388003c15889540c40050a00c00d05000c2003c000e203032186642c1041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 572857976 1250 572856726 572856731
    0x20d171911070c0e090f150c040506030112060510080c0f1306060c03030609020a08223318031d10030204061d10120603020a080619090503030103030e0d05010c03 71
    0x100240c4c503d005096030040d01e0200600081884011401d80c1e072020a101011180036110015001044180030b0f100030748001003005580c0d595500c908038081c25850070980340c3c10f00e0000480c1c0d0400c0080130300f03070460381010003070080b0360165000c0101c1c0444004030b241d044502134414240d80c040b684681000b5200549a20950082c0e90900504459441d041007080b032744100314a8410750303080450301da80705c284020450301454200340a41084c8101500040c04d8007030b05036500010711814001507100b0010808092200c00798406100180c0e15014014041c01160703e9140c80031034807502c0400fa000c91680a14060003200794041400203010303074408000264081003e021a543c4284103401e00b590100d03003c10140942400940b0881007658604148120502031035402c09076900701c01c1c025a002007140d40925a03c041150321044202d400900d42e10500130204c406254130320034907031000d0700326008500b141e00310f9806035540d007142d41c040c56000150750351550000c0c60034000d0400c01070255501 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 572859226 1250 572857976 572857979
    0x3020a09030203240a020324030a0507080d0e060720061b10141005041e020d140f0c0d0507030b03010e0d08090727090c1401020d171911070c 62
    0xb48004d402c080c4c03054509a00400a206030070f6440c262482c1050010b0b02c038039034403e02030300000b0326120b601d450090050040e1040080e0804c80450401031100481d102c41000010070380c100013580c403407500c00a100da0745607810b01500f100c0400640c02d02c10720113442180b802d0645011105c00e5680d142141d4070035884048000702948450040c119602c0e0015150007036030030101101e41124200703015890181c1d641e500d0343e4601d01241c18916101904036181150744a12140010028010801d0030150031700c441c03400310341030f44454900540309808401801c1c0c00d1070a8104500003424014045008060319002904040d80e0300380315a0261412504c001c1602400c1100050400f0400500c1d43c9625080194100900d4825015030511032003040c0f50740a0048049810303500400d1014409454541c0e05030020600c00c212580605484c8800d07000c807550f40809510803180c1c0303030384d2402426005103510041240c449000c5031140c00101d42c0c20012450b07803003200c10358645804c0400240c0b1342c610400c00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 572860476 1250 572859226 572859283
    0x50c040f0c020309100302160c0f06020c0607141c0806100905100c0c0e0709060801090501060f0e2b03110c180c16030f0e18060103020a09030203 64
    0x1444840045000c0d0512903100c8009001c1d4590240c03185940c02444c0c01740542c00403034426411161003821101401c1d10b003500ca8145402121000d002e04c01c02c642801c000030403401e00003d03c184a84200501d0289015400c0c5d070795508020f000078401a82c0d1045079400c40e030200c120460016500c1a40c0d55140051405000b001038181d6411318107001c1c0203c941c03082c025a00d031280c05000300b00c094184400302207028a01402c3d008920382c03182910762040710a005405501c403602d9021914950345d1018180d0b240c81d80413049510a10031a0007182e82c402c4081e0025028514013000c060000b0840240c0400016004900305c100012540b040e4004180c040100b5800942c503104000411005100c51102e00c400716005514000004440205040010342120200070440315100c1c10345c01485d100000034940039054201905504010030141d0708021001d00342009181c400c0c45035200102415110840103600a40c001c1050034104065180d0100143e10200040341c9500341281d0211600404540c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 572861726 1250 572860476 572860481
    0xa140114071d040c092c040f030906030c09051314091011031e190f020306040b220203060f0a08030406030c0903050705010813050609010614040606050f0f0702060304050c04 76
    0x340003d214a00c0c005004104a40c041c2102059900255100303140b00700080c00085c034907402c40c40c11401c4410800400c4100201c0802000d0f00358440e4403036244281d150780c01a005d4401d4091128001103040307904010b42c0c900034030010080c034410f10300080c8a4180303400d18248650b040360034042c00e9020002c95400c440640c170449519891202c2c480c2e0860403c188050a858080c540025810700c03100301203040069846034041611552013004c01001a401c101a4043c2d0070880d182c030320443c501031305500c0900b025070610304103c071400e041c90030010103401080c0094002402e1650083d070262076440c180e840713055400000e0005440196200c9160040c020140c80840100b00e08100c95140108000354000501405a84090804000e666510103942c80d10000d501d078054660710504081c82083e80c4103501500c00d4030004000316591554040130300c41611120f00c10320000820421100000d000010f001d4010500011119031802c441c2b600041c2050f0010703542a81e05410500340000384ac80c162 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 572862976 1250 572861726 572861777
    0x80703171f0b1c0f0b03030a0e130203060108040b0720100f09080a14130b030a0c021c031503060c02060a060602070b030105010c11040c0201020a200a14011407 70
    0x414501c3c600080c1642e050b040c00b0710048002c800302d031a109100d440e9141600300703815080e006400c69440326000c82000f0708003402000c102c3c0c0a52503000d00240714007418000c8a200c3e1f8010b840304801511190745807c09002e001301450104000140b05071118140c007840c0c0145401003900078034a1034208460b110440d40410005200b0340d140203003860000328404140e8100307212600700a14515405411712001e840b0365616079080280c0041c0c040351b900d0b010400f442c0908203503102044003400ca004160b135a0300d146a40950310411340b050401c2c1149c42034003c2c3c0c1c000f043e25146c0300000c2e503480d82c0e17950070740341410034490240c3c1005040082028107403003203100800c5244020200d00e4680310800140c2d00c41070291038108600440301c40b0500151182585066201910803c0306014401e00207000f9003283d140c41c00000e1b07120030b410521100c00b0030002c00b81d41e61138001d04401441c540d107480b000ba400c240707008855501d03072100a0100c0d221680140c4984e6154a0314082d941e0784080404d1031074000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 572864226 1250 572862976 572862989
    0x106030207110a030203060c0c10050420031609020a0c060c02030a02191203020906070c23060f09090711010603061407080403081504060306060312030b060412080703171f 75
    0x8010f02000960360000d941c40d00103c0c041c0d10b0603a105015403256062070f06168040e102c403428a41070000300458230400400e1010590044081c865100b020503465020700346135007030480020030041c00241203a90040c001c0c080781e4180f60784008101e079941010340d15030300d0660000d40c1001c640c01c0034481e01400f0302040710b6181e0890101c4801141d480e0400f00d03180401e040201039020481c08415200c07101164000c81e080301d40400c489a9403c2812941000404203021b841809000d015213070400c07409030761100032443c41c400d00f406026003c0c0001468010113010420448a84003d58110f080c403c1d00701460090402103082d1020090724400c202019101d1070401030b0900400011952109070950800c80800011344402c53300d00001e009040c2541002c3c000924060000040199900c41e10000a00c3c68400b0701c4a00354030742c100841401584101074031f50441c01844400038005a004000e410320904100840c0c1d01e034545240c055a00c01c8881102d000c10202c2c01400950446250900400c607 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 572865476 1250 572864226 572864239
    0x1e1f021207170703270b04031112041502070302060f04031a0c09040504051002040b0903010501060c031b03050d020d051b2a01060b0c071a0a0804030c050c0405010603020711 76
    0x503404441c124801480f8000b01a600d018032180da060380e4080d902e018245601c9401c40540c02e042c03a040d0f40030b0586040f008a03850018041959a001c1034603100b901c8440f04142c1042d1a145103402801f0000c0300d4281180681440400103a0307540000d40700081c03030301c2905912242135150100214560f07086580140844400308482003024200315484013600f5100802c0580300d514285190100015042003124000f140201e0000740c107501506458804070001e001e280d0b6144000d4540d07200100c006030000b504020518800303c0000700d100d01c4680300f4a400f61404c04a91441b90403600508a54400c40d0b440e007043c0701d000d8500c1c2ca0301001119819414615200032010016008002900145e940c13001254880b0920700702944140001d10240940b0f1303542d0080183c0054071110280915524500e00705625a10450210700b0b0b02c6041d00640c813802e01945950700c7c141d42803800c212040301c0601c1010b0800009442c0c0b03004043c001c10060700e0141c0c40b0a102d20f4024904012500300500608 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 572866726 1250 572865476 572865497
    0x30e01020c0a03021306170c041401050109060f050c0102120402032131120b13030e060913140709050f1305060a0306090c090501060206091e1f021207 66
    0x261004950b20840e5412142443c2c0c212014000c00003a040c030741d001c16002c1000d55800401c0d800042a0403400b43c1084408122200c0340002d41d50243d007007805404d000902283c3e050003d28040c0c41000030120741c5007000d07030601007804a10b0303007607030320886100301000c02c4d04080c0400c42c03d0030003403c07102203040c54908034404074800340c01c0c203580595000b0000c001000c1080100520003522460340710f13480141015850341e250b100c00c500700c1600440890300300c0c1d800c0c170000e40954203002403010b806515030b42e070b070540782e1865082043c150081031146910440c250303101007a50007244203031036a20074001000002468600c8015280311404e134407490003031001030705184440e940d811074840b101c0e40d10707880025151076035404a0203104c107a40004100a280000c40b00500421901d2401201e24025041c00641e0f01c40004a03250042503038031902c95448040c00110300d10001d110004002502c0080718959180389024011003c4042c01104102e6800034071074103101d030b400c3d201070b81c01007a07803c10300c02c6003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 572867976 1250 572866726 572866729
    0x7050109032d0f0c060504060207030806010f02030301031b0902031806010602030406051e1303060e060a06050d020f040f020a03090210111216020d050114090c01050a12180807030e01020c 82
    0x40e030500c0c48602c2085a4405042010742c0503c041801c041d030400c00800c01e520303252800c08025800080c0c182d020841380030002c3d01b103608c80c0c0c40b4914102015805107066910315600c0107049417002c48080c0040b01c22400205400400384091072040d25503440501e40020080403160602c00180c20520841d0002c02060000701d410004590300c8001c03c240782d0710220000018178071a401480c00ba0200c1c5000d0f001c0010500c86e06070403034025581c5000559031a52100c00e00a41110341b50300c2901d8009450790184405454205003a40000c0c0c4007400214810301402201000c030307800201e05101080d9074040c0e450541c141740d41d80d60400003e0381080c0100c0c105507140b46a54200039121100342000c002201d0603d0291108284205a800b40107001ca41d0301500c0d10714040c11b800a2207000c0342c5d80030304c0000d00c00040040c1e0324030052360686074a0324180501e0802c55904001c0b5840070082c907124400c40d80c0c40300c095404803100342e0181407580e4036840355290041200c0008400d9904541c041c030741d4011607 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 572869226 1250 572867976 572868047
    0x109050f0d0b09070f0617010e0f040308040f020907031a06031e070302040b0406120b1e190f1202151312110d030908070806040f03030c02120705010903 67
    0x1e6000032200606a40310b110381403a0650070b0f0800020b43d008900001070150304824007442280b082a20040c1980c0c0340c00c10009101e100b01c60b07240070b07845e100c1c010070041781c00344514a070014041e220103400c96507240c001c41c80e860010f4809000007540e0b10410310f044168008201020031088421501c2c40c00e020603070000c1d6030b00003901c1e0404011a5008519a02d000e40e040303034020040c401845031595580d02028040b1961000404402824081c00305c00500e4101c841803920440c214011441c0c0d10100240080760314020380c030340c0c4a6248008007040350020050550028940c00c4001c07036502490303105110429000322403003a807100c0c0c148681b001c030000f03442030b401c103841400301042144003090410184080c840a44644c0100d0032a503200141944500b903801030303c44010495081039a2210500c1d900c03401181d010b08002c2980d1210302c0002c0c4207800080c110390707151045424480501c0304401032076200481c2103c1c42c0c4c2d07458024804054001d04c40c103851b140300200b184410034440703110003030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 572870476 1250 572869226 572869249
    0x6090a15030f020f04051207080a051005060d021302030a02071e05010b0a14060307050403120e0111030f03271b0907030c08040f0501020c1002070b0a02072406030b07030203060109050f 81
    0x1c02c003031f01c003120712601c00b041004600030300c200782c01c50380d030921542003403038079100c1d0170206585280c02c2100144660410348d8039002090ba001c1c02110724120401001002900b000e03200015040d000c20900c000700d8071300d0002002c803500342001902d40c11034900c0c0160840e6200c400b40d80c0501340b000d404016403426207a5074007607980161590b0341e43e940c0e03944007111b180c030454200400c11031003405440301c407607170180311180c07800303002c0e21007040405820280c0303507907030154491252005604000161a201c080014414001c2c0380d00c190301d950041250101c3d05003443d110148200c0b14000080003864641502c01903082086800d08100d070411380303640105084c1c0024409011105110069010480c09504690034000000c065074100030001c2d08034400395000000c00c0d070741c294202011883d003010600c02c55804503844a1039100c0f5404006102c01805800c0890141003036403030300000040f07440b02d54124882e5145660042c1d59140800016181e012144c01081c02180040708058180d1200402c902 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 572871726 1250 572870476 572870479
    0x90f01090b011b050c0108060102030301080c0d140a0302210306010e1c06110a0212040e041b030519140105010315021b0f0102070519020307050d0206090a15030f020f0405 75
    0x40c1c141250780c0140d510b602401070f084844441010094140312002c9100705203903030243e03074003411911000012a620b0000b80142a00764202e0800d03401c4500e03020b0100030b1840d109401e0701d051160800350352800c14812010607009a00401c2164603400ba0404070030310400c500c600d0302410741c00c140380020448040100064001c1104056075401d60b00c1d180b00c03902020340e200d1002e1004482c5c014180e403640d0040100d94001d0b100d018003003004050743d50103a03030a4031031400c07048156655a8494000032240c03100c600300307403503502480032000c18818009021454107404840040f40781c0c92519424084aa00030149164035010040c00090503103c06440c40f09903070140561a54820550316a204543c4260000e2521910000c40000c41c4c040d00988030352405001516514003101c0391174100201c2840300290b054000d4482404140740c6512500c070b0050016102a04100711540482d0a4168603040101c2c5004c01d28070712820a41d06000d0b07039180c07501d0220103509040d1480c1c40c80c3e03441c0c080d50141d035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 572872976 1250 572871726 572871731
    0xf21020105090904050d030e240618090c10030b010f0323040501050403020d0c08030115050f0a030e0601060914040902041103071806091503050901111209010506090f0109 75
    0x4425a885281a2650710074000d00e10032003400d02d444e28907034410400c0005401300382081020b040451000c148103406c00000b00542076007082c0c00060000e0014000c0003030340d00030383c0310030482030281c01815410300c03900c06000200390350401c41b41007203d050201d04403030b0101828945282541e9078403c181e1071061305141800710300d90551114152540c0601082d070501c0710400310800043c42815000070307010350b000c0c0c1c080d80c040e141c25080468083c91602d801a00058080004002201c80340c296035400c0d0409140c001c1c1000d030700d01e22500140d0322650344040082e4030385442c095070380c10038040c0c0f60050105003041d800062400603c28041c0441c0d101c80343c07080e0b80e04c034600004c0d9115904080b0301810540d580c2d6175680341ca02c402a0101d042d0038541040703a003640310049509030050040c17401341c0c1c4d120880c50100a51150044000d403800510b040340d60354030b80c0b4204644442c650098105201c81c096034142d5031404420107421030f1001000644100032110910410000103d202c2e0305503000d42101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 572874226 1250 572872976 572873039
    0xa08030a0e0a05030d0e27150a050901032105180f06071205040807090b09180111030907170607050906030a090803010e0601030b0409200a1d010f0f 65
    0x1104000240d104641601a403804071015940c0284225111070040f104048210f500c4501c3e03400b00c150b0f003a001e41e418868a000300e040c609114004010741d580027030810801a49600119040f200c0271307031044503113000c000702100c042c801400c1c8112030090185009820182401010459541c440008034080e0068096140d2141c480c10100c0b4002500541d8044a1740c19000c40108603511500c03501c400c60040c9800882c80c1501030040340380340e2034020400041c0b41ca80c40101c0c28014000380c3d010485650342c601512050219901451140d500c2e6005094081d103060b80c0c002030030981c10740c1070609420003010488919000005e4a07000d01058a8076501c0c0c0c0d840b00130520051110440140920102100024012180200f4907200d414281d0301840740c415007000348425503025110041c0285804e078800c402c10400e114240c02c1c81e01d0000e0140d0640f541c0c4074100000c2012122141203085036560043c410b080081039410024000303405640c08151501c42c0465000c02170141031042503208186 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 572875476 1250 572874226 572874229
    0x30b01080403090b0d15080d11010c080f0c070213020a092903220818030316081309090c050319050607120f180308150913030309150605030c0a08030a0e 67
    0x8040700c006004012883c01031f8807000415a11590091100001414211114400101801013000006050703c568025071507855072114010002401620308000c10300160000d42c1d03d8454042d0381c0b03000818016503072400c41800500942507908940e8203030411011081c84400114058190a42c55191a586a44036074076150121078800c1d17411001010046402c600307020644c002080728002681601098403020414540c5130700818440ca0041c004103000d040c08075154000034071850966030300c6060300d0313034660f1004030440708083c00603654540d400340c081c051424104034050188101c000c0020a0790055030311a565000001d00900c200040c52401c1d80440345190050300c141c00c0300310002d02420805407501060010544e80540000b6007a0000c40d507698121041034013148000b415150705a074406d10880068910110104c0403d41c1d91061900420603401c1c224001c401a108007041c0310b850801010304d000404010795124030550001041499000421208042e0744c5081445040020f41d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 572876726 1250 572875476 572875481
    0x311060c031e03010807170c010e040b04090c090e0c3a140607080903040b031302120f0c041e0902010c0b0c04050103110901050703141303030c03030b01080403090b0d 73
    0x1c0d9500c14040341d000241285501c00b90140d41a11494804c841d0203a0b920001f441d84049001c6154040b40c010b41c81026065210b401140314a00000d0b0002c14006509008a4100e0701203030425207000c0c051f03403400e00c4000c0030350103042d00c2d401030500203161654600000a12491f50441c50061410088600038a160b4804a8034071144010710000085110b041c1007038140e6086d580902c07241409200c0010b5081c90140c2c5455001e108448001c5080a08040c1c02a403030364006800944241c2844061074016501c800240d00200652030140400c521469925032030503007194503407403042e81040d090160812110b1040d0300c1c541c40b104d002240e400900d0005070f811040b10040504800c0740d00f020000d52440f210010801c440003a83c1c100501400702440110700e02842502074000b8030208200c4000c00c0c400c02d1041c210000c0741940a10303107400c000c00040c98022a50044003c0303a0211400000c0c15014452902188003e007001440c1e442c099400130300301c080c40e000d000c44034400411101c100304c0300b55 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 572877976 1250 572876726 572876737
    0xf0601050c01060e0a021801031401091d012c0304051c21030506011b02181b07030905010e180604050c13120c1211221509050c040311060c03 62
    0xd00807440f250501741066406940310000e0b001c010302c003c034403480003540f19205800c14240400080b604176400c2040c840d02a00c0040c2e1040e0840c081040009158802841000814603456407000c812010300801603100e20290032240034260418801002030761120782c1c012010215002560621119501c0e0090420600d50305412182c2c40d24421407081c541c0651180340180002d8072094003c699901599851309460030000b504800800909440c0040c40644103401180e1090044851844101c010010340c11144c4180e0000b4074000342007099513000410100c3c928009d03182612400300c0c1d060002d240381d00c0504050b00890b900d90000d400e000300103090381c01c2d1640d4450110425aa248005103031014101d030300361102d01d20500001801c3c2c10b151928960700354480d9101d0810003215041089070254150204c040001e58400701001d400d4034491407400381d149076940302c02642401289411240010310400401104010a00100d12403c41c0e604070350388121445540c60030345046250440c041d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 572879226 1250 572877976 572877989
    0x909090303180606050a08070302130506030f0a03090e011a1c02090409060203040209010605070507090b180702031e0a05041e030f0f150c080c1612020c0112050f0601050c0106 77
    0x142c00d4100482a00200d045401c112110041c02c0c1c0c8450110f07031074060b18403009510500000d440c1d5288102504100d0740400000e095072100500300c0c81280c101010808101c00080b90484140282103158560078094001c809081c130205c150b10b807415920348120b800605010070752422000300c0140540445020800190040c42220450310b04880a90000d441c00c03440ba04810002080961140040e907054035040402030003040e00c0e00300c0f03000080c0358a600031038000403040e8460704440d201c8050503000302c00c680d008503078561050180c5092010801014085480d040084812140c0c3c003005880039030307050035011b004901c802c00006507075030b02d50342c401031010740c0010080c000e0252540303107124603a004450b151f1117015a4080d0208890940351031030086004034001c9030151030380b18090f1180c0444020f900814a0700d645400d156100e80c03034401c0340181d11903c2c01190a50303000074101400c48481c07109000d14203002040002142005001070f0402c4401b14034080e0003c002d4000600401c403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 572880476 1250 572879226 572879261
    0x1b12080d0e072306030c1b012d0b010e09011e090c0e0117090304031e051e07050402030c04090203071b1104060806070207050415091b08070f0909090303 67
    0x40e5001c003c0d07005100d2581281e100849038000d4109400d144044034400c40765461380d035107444102c01c032070480040001c101c1000e541d41c1c1c9405ca07140f1030603030320b40d00f044141454200350700c0981c50900c4000d0360140c01c0000d0411824550080c26525070340e4080d41541e066000503844c00034080c000f0309120149030700c00200b56040c141d40c151804d420086201e010402a6a4465140b01c01c92214000f002c05030355a01250740100320410200c2c1118294505401010b00014003024180e1605803030600b20b080c141500088a180c950f640110170030034080240707001d903030035811460241d0390b10310235000e544100325201d6000000982051700c25512001811040c103c12801e000090030001c403000f000a8030940202c0c07525030046001100010890f01c82d800c56401080746034200301c18400541a56528034040085001010800d15018061207002012580c100d049410000304001c06c0c80360050f060505008480307202e042d0850388416801c05640d121403000c43c0d201a0f500c1c0c2200105400089296182d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 572881726 1250 572880476 572880479
    0x9021f020607030e01090507091506090b0d0b060d020c0619090c030b070203041203230f19090504021b1e060c09060f0c010f060902030907060810051c1b12080d0e07 72
    0x11003a403144469100e10000ac4442644a40c000e8035003c41a00440402c1d9409000303c80340380c032150700030404100020301140d0070a2603e40031041070341c0001c13080d007041e07030000700c100200d880c0c4003031a040309031100b044140620283d80d11000d02010303260002801c1c41d60601d0001c3c40090003002103400515541c20b90b12043c80060500814140e0200041c40c5000d03000507400708401c005038291201884041015031400302820411518400040030043c00d002d00b2030800101942c0307078809230500c400c4400648009045000c15242040003644280d0b206c808540040090b099000400710340c41402d1100c825a65005d0100180707040c080c0140500310390b00d002a0f9803c10010641000034143c40c611402c1c420750352210710050070fa0004807580c045680c4440320800445210b00e0b1616004040349401c800059103032804a5841c010301004c90946200507012001000303039510030392150100180214407024105644404500c203030308006040c510001c01c0304607603035070250f00c230043c0d004210046030f00c5513 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 572882976 1250 572881726 572881739
    0x9050421080f010806011a09040b0604090b090606070c210c06090e100b0f0703030e0a0b0402190608060108070513060809011a06040504020715020a0309021f020607030e01090507 78
    0x7000490301c1980200c503034000069a0900040d51605032a03800892400e01d01500858403d15040b02c141c60303510544900a010701ca4442400920180c0b000a1000c2038255038041801405000a442179000311001c006000109050403141016540d0158a05240264143d01d80010f14100600501900503038000003405940001e0707003c04a581c440c02c01c01035070760b40020410b06480780d4415000c442100700a01030001261500610960340b00b42000079042e00c1c49280d40e4504499550704442001000091001b54600215400780f9500f0f05036512250314240000146004c401600d4a0f0500078100007140c0d1070b6010724142c549800b481c03460450b52599528000346001e00c2910401e1065107068140d0080d1400945c1404142030090704d44e9251510341001e010095209240950340450700046206580c0c0c00c0b40001c00d02d01c08595800f203003444441c0100504280c00000000d5000c80c501da090104540205e000f9511040030b0070001050200c030840035024040c0c050b00108207000d08080402c00307 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 572884226 1250 572882976 572882987
    0xe1f020f1b0a120c050a020114040b0d150506040f14010c02100201060e060d020d1202071a0319020c060f0a06051002030c0f06060913050c130e0f1609050421 69
    0x3840d0140a0310440b84030503103c103481a600034074000c0d006030000103605000d540542280390031303a00158150391405070b1310746520f1841d400684a4004443d00d41c4d40043e1192441d0803143c01400c5c0465109152900d000001109510700c0d02c540c40c4c1000b0134504000c12030f0300031a0f15030003958015208002e580b800e4407000b40200361a000c0c0702c121024071408104c0b10304207405a580d41c190b0203418a0310801880d200e0f040d40100201030403007140302d000c0c80402c60204204410b108607d206400e540c43c0e00702402072428042c0302c0112030014034418042c2030350482c1c000464681002c608610811545c841081010241005400443e04000301c401482005680040100103600400702a50480251086210744075203003502d03160b6100c00540081003d001740d000208040034480d000711009082804089050703102c2c443c4800340b84aa9170340d01100d6440381071006030b039070900318000361604150002459000780380b1401040030315540c0c3d500003810008040c048443d000300101040e89481c0d10711400070704 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 572885476 1250 572884226 572884243
    0x81203070917030f071a0a06050a1a0c0f06090d2a020111060c04050406140f011107120b0603100c0206190608031b0f0d020307020f0103090f05100e1f020f1b 69
    0x6ca441c3c420004905041c0c51040304203a4000614422500c0d00d820310000681d0001c06084144000401040108000801400d00c004000902800151034070b070300c5043c280216140a001407142c03018851005150001d646000c1100c80ea1005001c100e02d0700048803044400300251446105071001e00c0354148100018104a5000715400d101441d02c0e1111600503501040d003d03908510301060b200b0301f640c06003400200540301c61040300c01a40d590f026888405090810660b0440700041c2400714034141804001d0010658010a100b8440c50010084d910070000748584202405070400d0842900281c00c0100200400000c40f520b541618101c07102080f11103070a0b120b40d00c5480c2184840142c04106c9608202c0242c002d1803c028a40d028803c0180c400c0b400181010307640c1981a0009001c501c4108403940520000e003001d55100b902402140c00041102181d90310480700b1120b040b00031010511030900d810780140c0c82e04180d1000320841d000340400e20408003010080910a4100000c8408 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 572886726 1250 572885476 572885513
    0x150513030303051603140f0403050d050a0b010f0e011d06040e091b011d01050706140a0b0a140607060c180303171b0717041e081203070917030f07 64
    0x51380f030309034040c098045881d100328054034003c0b4a40040e0b10f4120702d442041d4054001c0c2131142c500030342d0790403200499400700d80d100c2c0c5141e82c41411086a5074002009540c042c1c040c1031aa034501800400a8000e510580454503460000846002a61507400a66004200004003c505c0c1e00340141402d486242c191240d035141800311019040c290300c500120854030707a030060b02c484410b46017001100c03558042c0000750303900c0b5219081403640710394010310b45100c0c01d6042c00005401581508000c0300c8181039014076140d4040300001ca2460341c07440121407071254416000100035a03881c0050351308500d203542c030314110188854000245070300040180000c6080d540c0010303c039902c40f0b10011030030303840300c1038130318030f000c0910441c0002212420112041100d0b40381090800750f6642c40020000c0714043c12850140320a0020002c0080400c0140c62291742c201545040d4501540000c203070032440e2242002e0f800310501164101c02051040302c11051880786c2c00c541d2241103086c144010301070941d205 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 572887976 1250 572886726 572886751
    0x19031b2301060f0b030709121b1505160f050609070e160c080a031b09090509030c0606130e0a0803041101030e070b0702031213030203061e0115051303030305 69
    0x122003180c018410801540c000f2003907108003e091101c9052650401082c0030280807500c400401e00519104031a84400d02c2070030041003010010300012501c81160f4003c01c0194001100302c6070883c2c129054412014041d0742c0d014a070f10a504000038282c172100c2e0060314a01500040c0000130101003129800e4515a000031480c1d0388402102d251402e400c036059800040c001440b450019103031800070030000c07071149000300d102c00b00c81240d142c40580030718003030001c1038011200f04804040350168641c0560841c000c0d600748516855a5078951000900080c8288443c1a14002c3c1048550105102145a40444600524030710709401c80e60300a0760705952030000c6290810742c66129018800d074004449014011207494951508840e40010000b26410700914542c1e40aa51940c07014101808441c050300c04110710398014141400c1020308044641114030911800c2000104416411201c40d541c0035501040e50800480312400307080310001803002c0d000c0d40001410f50540005002d5102074200 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 572889226 1250 572887976 572888033
    0x90b0d090318091b0206041a091606200a230a140102090108060d120503070e03010207290103030914010c020301020c0c1002030703140c011d01050709061119031b 71
    0x91b0794482007160020900c8250780c41c0611070103802010a0b41110382d031421501255004000d0f408180b08030740001c00000e030000780e0f1003038031180d8151840045105c0300150001d42c820780c480b0500c5000c43c0100728841a10141044a2a04200050403030741e03800c100c80558140d8a54040c9020f50b00c445030f0f176400140a070b404915036281450030004040e03801500c0a41c1544510020b540c1a0401415907050010b50001e14005031428001843c0c420b03ca101a100f01c0300005000e01902d0030016030011103051800018800a41c001d8003030402d40703002104030f0840c0c0f4400c500413182d00d0711025000b5010b50012510007105100081c0ca0103142d04112885003c0403031044080743e80307000307041e00500050b001d0001c00e04030100540042c0310440d000c000200c0c005504001c1c814400d0021110795000fa991402040103050b8084520b1010f044245004200140002945581d80c0807400011a00b00034003605002018003840d01d000e50355800007250520b858960070310303038500000d031410440c03c1030400e082d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 572890476 1250 572889226 572889281
    0x17010b04061d0d030305040302010b0d0b040b0a0e030307050c100c03140a1109060d1b020a03020601051e0609030c1507030e0603041e15060f060f090b0d09031809 71
    0xc00c1100303084003a1610081c5150f0f610203c018000c083c1090b0159560b441203900e0b1612014000303082d86020f488546543c4c2032178541242c50440060001c50040d103001c841407588600071088a801403868a000d58944204842c02801c20311707003104040360310b4038043c084108a41c16030001010030001c580c42ca40b4940d102e00401d400d50b032101c40da060b1884030801c1015418503080c2c014103c0014921000100ba03d0003210039a09020f480d510315004d44d000440310010140d041051501520742601c0c2004596010f0341105010294070747c0301d5101e01c801180d001c0040d1010020b200c18240020800c0d02d040b0707010144100c5980c84a8425130000f500d201054495013403010840c0c1c041c942c84405100c410060245034040e1002070703501100c00031460021b6656030000d0f40100c201901604180c80c081c40d2500e50301070314411400c40d1040c14071007010402c101411068064601808010002240c180c5180c0f5044410f1040d241d100c404184070442d001c5204c40c0d0b142e12009030442c0350071410784110b10040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 572891726 1250 572890476 572890517
    0x702150705031909120c0212070803090607083f060f09040c0b1927091a06040902130b0408061b09040f0e070b070809040c17010b0406 59
    0x260010003140701003010a00e0364841c1c1034000d5014840220009242007181d40e101c020311108940440017034030800182056240000c2240b40e05441c1e03500400314180b038040819128001c000920f4443c0f0008101ca409001074401280c02c06918000c03290035600102c1c0d400944008907800e8002400050108a001441d00c00c00030743c020440106000c1d808003d144c02c101441000610846894000400000c0c4030040440500b04200f421143d038408910100c200408540142810800030303510002c4d080c03c80c0442c0740745402601d85484011442a038010320b124541e2060510305900008000380028507000e01d50301a2400351040761155a216980d581600f0080c01603020341c200542001c404668000b1031002a110039a5800030f1142c20440f82c1d0002500b284d4084054100e40e81e1980c210a0a02e4424481d50000d8910b5403000384c10500607840c0c03e00b86018982070079001d103a07115681d507021400741c070141c29040c4220140c1512507071a00c079004001d4205101d900e0104500c01255001c00c00d024 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 572892976 1250 572891726 572891731
    0xb090f0319150e0c0f0d150506040f060b031801110a0c060609090302120306130203040b0403080916050d0c090509070801060f1406030414060c09030f070e0103080c0f1005070215 78
    0xd90040044603100c6003000481c0d0360709108586e1040c3c8035050100060201c00c68a1502c0c5500f0000058515240c2c0c00d1109071043c0d48200410b4507e089002d008060040007526044407460342842d4144960200182c01049415031000d0072035400704080c440b0030340c4005a00ea845219036814440c20343e82e858944182c508080000300940c0005c50400007070b4045502440d03000100810503484445c0e0000b01004030f80c02603c0c03e680c000d1103601040241600b181c03c81d13420075524001080702c014038504044103a801c40c025288200070a03001c540500103e01e100201601041204001c24209600040d0b07072804581f041e43c2c00e40d4200400010032284116012044640580f5a001c8000040c0300300012076000800c2121112034824842d0342c0300000b0040240b0519024000903603c2040404051801080344030f10412640150403d00042010b00750345070460742d00408440e280d910000040f41012802c443da00040d1207181104800d242036600800d008503019001e4404040120466044c600401c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 572894226 1250 572892976 572893001
    0x130f0605390307080702280515060108011401020c031b100503040210030203190f0e01060f150c02060d020703090609150f080a110304120e03160b090f031915 69
    0x42c800658802e02440300b8941c00099841500c03600703014000e4055040c6c400d6600d07501f0003540101795500300b103402c002c1504494844417204010349050720008000b840d050145000300000e01019011076402040540c440c100020141d60f45040244040d100342d100382d2508511541d07410044141e968012401c49000d241c020b4140c2d48081d0f20005d081e4042e61024140e8200c0005e803031611620310f02681710b0390401e010f5034000030450081d0700705c050782510745a801080b00c80360030100410030541c000010100c1d4103040d044c40d000000d070f14000101503015110443c04454000945030080551040200c0b00355030941d22199401600c0c0c0104040c9580c00d130b020300d0081000303a912020454011208154008031415001c0340358041d4420000042e0826202162083c070b100100c0c40120f41c110303440c20a510804d4004040034101d103242605400c80342d108056001030009052410390700c1e03081c3d280910020140880b228580c1d1040880c1d00306610340c00603100701d9440d665540c203014282c0220140c9005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 572895476 1250 572894226 572894341
    0x10b0301120f324e030f06010906030903171f0e09010e031204111c0b0f07020606010905011808150a11040e130f0605 52
    0x450303510540c403054186415214408011952200c40611800d00160240c81e0105502002c090030b80f218a4220044001c00342500c403061842600780940c2920b58000b0640040031140d503681046032036202a4a880d071410300140001041311150080c2d096601a1034280d94580ca01c950f64182202111403100d00100001e010160603081c1c00ca070004001d400018004d0a003142d0303414401c06050142d216442a142c44120000f0080e60301c000f80700e502d04102c508405140b61060241002c4d005d20002032009051030200094038040741c68607110348424000b0354049440134115030400c010a4181103840d414403400800004507007500c04200e030740c003c00781a11040000307403c00c0015110962507080c440a441f910800c002011841008451941c030010200c0e0010790a000e6080740941d814910041100c10081204220f040c00d800000d541c800c16500c1d40c42c0e03854800303240401c14548101c00160045007454148003a100c1d8500c10440c010400075510000c81a80c0d81c80400503078102401d40849a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 572896726 1250 572895476 572895509
    0x3090303140703140c1c02150609011d0c04030227070306080d0e03120a030603030801151202030601110a0303020a17011505090307030605041b0905101505071a0906010b0301 76
    0x304240a840801707080307400c1d90004992003a100c01690004050000183c0c02401c00740e100f8199860416048802580d61200360b40c140744010a10720801c0140910355101240080c80e9000c594090740d0196074000c0000c0da4014600121921602c0c60101c5003c03e101030300003050300f0500070b1182c40210340180c3c0103091100110502079900610101d44107825000310515080c440c80c40350001d014074005914005105415800c0003005010140c0080301c9140340a150f00846a8220902e07120030901c400000d656a6181801210f50986101d80755926100b43d079518006c1540540103044000d10030764400500174040e06540da2b24030428460310341032440108013004038a108400a00d07405c00701a040b100f80315500e0742e5400c12601d0485003900e2003e4054040b40e60008402e8075240140081d80b0280480d00f072603007d280c0d4ae01183d100e140300e082d90040325400e44a02613425100c41a811401213051650b40343e10299080000b01c900c1d10700d41c0642000415076841d0402900d05031880d440c9a841c580 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 572897976 1250 572896726 572896757
    0x1401050f0109090f020f070b0906010e13172205010e0103111c0212010303090608060f2101060b12010312021218030705060a05090307060e031f020d0903090303140703 73
    0x30041351000f0154107800308188048450582c008003280c038420f1010104524000b8040d60803c84d0603040020529140e2080c804800000e0f001201c00c07941144c119850004000e8036060030b0b2180c106002c0041c00254034400b20080c110846104441c03082c0ca605801800500044085a0009485225400003400072400280c84400100061022080700529204444143e0020410244d004800084242c60203010065005030041c7d007000080e589040008a40300000700c401c0c005440c50076400d108404002e90340c10007500407200410b000e400c0c042e50340004000300400c2c41404d02041e50001210310084d02c0240c80066500b050000410106051600e10308a805a84030b14068056152085181c003058a0740c0303150041c61681e0940c0c071065540d80c1c101060504042496201038180000045001500e8401082c140c100d06182e1840b8a0f0070300d90070700c8003402801a00642c1d50030502c2c1070543d6080540114600c02501c0c0640c0f600918080c1e2000d02c0340c694420701c0001000201c40b440744036400d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 572899226 1250 572897976 572897981
    0x11040f091d0a0c1514032e06020c0102071706060d03090e0c031e06061c020c0f0d02120c030702150918011a0f0f090307181401050f010909 61
    0x11a000c4414030400000803040c11868181000026299542c010380108075102c83c5002c141d001540030f0a02c004c4066400390703d80d6486c0001407a840d0700c0761980c001c0c01281207209105054260903c0321103000c058548c1070007551280c20b00e110300d000d032060390710105490061008241000d00100010002c61307540301c0a12040311107002e0b0403024072007110070104a80318a1050745200389600c3c21456100c0c0780c020b101c83c24800c00815214480c00c400c02c2444040d840c0ca2080300e4514400c0b45a400801c1c0981c10020028401c4c8180300030030340120109265104004541d5500340c0d1090b5084441c81101c1c83c5075020306114428045d540b591003008034100504000362004181064082507a051844403c04500071010340110104c20015500051000d0540d14072a44500c1101075900c0e408c0500e9035071660114820041007a1a091020441c20304a6130201300c3c034401b814000805480490b85a03100300c0c040c2c910176554901c013410400c004a0642001c414034481204165078825040c3e02d8580007000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 572900476 1250 572899226 572899241
    0x302010f02030d0c031a040c0804020108062e0224070806060403120207031716080d1b020a03020c10050d0c05040b07080c071d0a0507030209041e11040f09 68
    0x2075000512070041c84000b030f40701c1c3c442d003456140c40200c1d081803544103c80e00783d425030001e98492843c24400d42c5589600010b11a4026030a003081e400300d446c0c00c0300150300b03119111030300c003c046404940039122074001c0904006611294086a000089801d00d000000001e0100c0c0500007400e00006000a032160022603084003001d0541c6281c0b948a468481440f0f9100c800312001d44e00a00d0304004000c44020f8000b40c44d00351100003400c0c102d03480c2c00d14134040e500300405010507001007a12052011380c4e900900e030a100d03800350742c1451030360501d02a482d038096000980140c0a00e01d003a400c20305000743d04400342440c9907503551400c00003900000050140d14142420084240300200d4109144002001070380d00804d0015190f40a981070301c0c1c513108003500403210f100b204000c9001c0c04e0407078522b040e42060310b02c0340110f481d41e80e01c0c20460090040c038254640c07182c1050003031072169080f440000e49030054040c0510050264071403441c075030b129520915143da041c032001000f21f000250300450 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 572901726 1250 572900476 572900507
    0xb150d0210030e06010602011a010305061c1b0b160b450f0307261b10110901110703020603100602070806010303050a0e011205090304050414040507030201 68
    0x160012956008203a44450304204040400e0350b0b00b108031a0300c0410085140101520b10091141840c0c0725a03c9076204081810181819281c402040c466078488441060890407007411000001c458200764004081300c6400445140c5a9400400d040d02803c003100e1040c9070301d83c251006a01250354201c05410300900a102e161008920300e1070201c0304481c1c4bc24010701201908030341c50407511003140c0c0061501400b50383c03a4021480e0003039118000c070aa40030560020b01800c02c80302650400207415500f085a8410480c0000740360100d481d0000303894407420a1481211409280660031400301d4410782102c04002d042840456081d6114000340541001210182d4203502c0c0d0b2a40410000e400c2950000c2041860a2081c005260304001080060400300001c080c10751461b00c0c041c00d00d118905620f0b0420100c0d403415801c6901034204005403c6540008000c2c500d84089101e40702d41160081c0c6102e94200049440040c0e28a801140540d400c800a4100146142d0066035401c4240800c0c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 572902976 1250 572901726 572901739
    0x20c03060f04021809031e03060f0607140d03051803090315060a080714180106170a06170a030f02011a04020a09030b0708040c0510080f1f0b04030b060105070b15 71
    0x200c3d464041301e43c29a004810080c015912150f1200c0c01c1008201000540c00101c2e00500c100541e42c0d98256840030806011740300c0903a90111727418000515422081e15003050b00c076960007014100d91650001e4403800680055031003500741d4800c1c05450b407040030090790f80740e8480d984001407001c024003803a40040d0010b200b000f04640e51340501e410144503510080303a1511134a003040c1103080c02d004000e402e042640d0600000c0d81010006403529002012081040621000184505840d54000809071002000030142e54a2420718555030311000c4100720000760030803500c0e40c0490f0050042070262003103400312500b041102d900303200c000c0d0801c1c4021810050841d000001140020380018015100c5a480360f403070303180c103051003032000007039600440c080c42c52040d074400016480f000c1d10741c0040340b1414110031070325680c080400c0d0588051402c880002403410018108580720000c10840e40718440000d0190398060040d1000d001d0351740e0142070a1000c0000450001041180d00442030004081 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 572904226 1250 572902976 572902999
    0x10e03010f050f09070f0b07050a230708030a090302040207060b061303050c01140a050c0a0c06120b04090f35181e040e0a060f0c0f020c03060f0402 65
    0x9003500e9154449a0708181d94105003c2116000904240c1c05000840141038081c82c06000501080561003014500321000c12103e0810000f0320541400c40c1d00050b09101d840d4640c80048030440e88900c7c1242680b03c1d00c140040d40d614040151070601205031900454140707550280400f0354044c80b070440f1103036901d03112020159603850103014400051407464031101d04501e0301c580b400d083e40180d2818050500c2c259500c01286008840001c2074929080707031220101c4096a1170071a10400080405d1300040020079410341c0810a501d500d40400300030302c10b80c00a801402704031120b640003c0c000c1180c9488030400f20700043c07944190301d84072080c44041043c0f140408040b02141c0e2000300054200000c04140d5441c0c01140b0b03460790f81c021122040c406038cc0c528040c0b00411200110740c016615a51440c3d02c84005000960b40180c002c2024408120004100c2008007440880d10000c0b8840891507102544009400b12845902034007d25080e220301003202181180108101e0780302818040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 572905476 1250 572904226 572904229
    0x6071407080c070302100e0a0303110a21021605030309150f0c070e07081306050702070b1c06170a080d27020405070c02060708090d08130501020c01080103051b010e 72
    0x4003008924440900f2050b403d501c100481c1c8040c54550400b04a03100c00443d8680e51160b10700400ca940c0350600845015005540354242100008094440200103070074016010000b0400d1845643c0c95003620101b115413044010000a0303400380982581c030030710140e60705040c520030802000341000074260501e0549200050756a0081c0c0b1a40c40503000b4102c100f04440e440c0800340c0c0c0002240c1000c15080c98200d080500b1800e01000140000340c40382c0110380e000e4001c0c4205005050a00c88842da28800400010105088103054044c864504200020f40c05988010894005500c20240600e000503803200c0a01e500040302c1e0602081d644c40242d203d850070000c00b00255512440c0c0420f491600e801000201d58004240c1c01c00e010383c1c403a0100050f5945400c40d20703041d920802e41502c44607030f50003141702e44100c15001481d103800010615003817007c03800010101e40c000d80c03c899a000c1d4400044411a41c00c0c40300500740da000d0301d07011240c544510010100420185000703d00ca10f0f4000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 572906726 1250 572905476 572905493
    0x1002030304060c1125091a040f06050402041410090501020d050a020118050d110c0f060c0709051305060901090f02091503030a0905010216080613060905060c0409051302010206071407 80
    0x7017070800e4490303103201512141c60712406440080c03141134000c02507140340e0340c003210080003903506107442166a210641d4044081d81c0c0110090030380900219103858646000c8120881c034400040e114940003601c41c01c0303661040b07080300240d94040e409030007145502003080d10142c01c90305a1780207554903803200401110340364400b604014020001000000c1c0c3e10b19001e4000107040030296000d03000040e50710300e5a01c88186640c10800196485030b580c03415404a0f505141440d005003880e1403d25060003034a084020301401814081d0054a119443d1045802d00303e451a2070300038460901c8107201400f5180c0008000d500201400080458031071841c0000c0c00d507030140d40d151020034099031091006590400901c00503540c840440103640b0b040002c03051b541c0380020807011508512222100400101e42c2090400710340c4030741180d003141881039030f078001a0454080c4420b40c0f0703d0b20000401056001880740e1081d071301a0082d00141d00e0b540d1007114214804030001c81c60a0302042407400042e040c9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 572907976 1250 572906726 572906743
    0x130b0303030a0b01030c0305070e0118050d03031407050301062001023108071a030718030506191404020f01020f15010311030a05071e031509030306051002030304060c11 74
    0xc0b2002402820640003d0110362000000f0360400d86000b04001600780c11042d0280800307824204026420721004030403046500740d07080903822400441d0100d0130140c054101c0e8a2604490034841100e585010307080724240000d02c0b59100141c44001c0703c0c0c1507041030148003801c981c80880050b1510130101078860444403a9040c0d0a96455449040c0ca1421195a09403000d41881ea014181032880c040c6031031107080840340701204003078000012900c40c0f40946003210708811241d21100c18541d40381065501e1390740407242102c0c0d41000d914403054800b2180f051341c1e98210040e032024003039101c075003d12001001c60310a190540c420301c810320001c1801089090320704800d5034883d10040d811031810400c81405040c82e180681d115250301030010703901140010079268054601010003c4084012120305401d03400039141c51071400c400315044404d608807000c1c0d1802900c040c00421743e1001402035514001c0070640058005101040000d0070b240c10004005a4500c0e2908800c01c0c0d0401542c20140039 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 572909226 1250 572907976 572907991
    0x90d050d1b1206060e0f060903150c07030f080c0d0903020c0406080303090118051903050702150d0b0f0612060a0806101e050a03080c0f03030106030905010e0a030e130b030303 77
    0xa1103a8031860149000b150090700103450550205c0c410240410a100e400c40c800c0340c41b400011600200302d44080081c4420f810801c0048040ea040181050000383d101d07c0b000d80006184505100100780170702005400703506400c5a0310728001441921000602d03c400080307046000300c1282400c160350340c1c05140050100c1102641c0c1d641024840c0070308603000d40154140030005188290007007030010030900c0841401800c11415103015140890b064855a10002e42c40360038986460204507042e00900150480c035001008140c03111000c21480548921300d1592140c401c01200f5a054000815142c020300302825103001652074209542c20140c0440f04031072051901c1d00c01304000302c00080c214040007801e00c180100c89003001d01186600c4054007001d4403840b00000c02c240c81585c208400c40384158001c081d40d890b541c546200802030103101750261141c1d800c00d05200300010b008960910242d9058988480e0340808202b48858600c0f404000041c641c0e817015202601e1318244021803041303e2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 572910476 1250 572909226 572909237
    0xa0603090c0512151609051009080a08040302091b0d0c110a06020304020306072309030c1009081029150409090308010e060f1509030a0f0317090d050d1b 67
    0x400c255800c01e0306002880b60442d290340540740041c41b90031980140940700c041d50b0201048110780c0e415a900d410650100700d281c4130b082858024415804058016244200c500745c00b59168840603d9940102c1680c0d0101c1c81410040c44000310980d034018403540e00a814101c241e809400405030500748402e81c20313910b2a0700001000304600c1d00388040c0354401d0041c20175040520f89100c008074604046080308240701c800140607c200e0f80c0801141e00d850034002c10210810544800080001c2d02600c6002198030403500902d20389000ca0151804e59130124a50030344203c10315902416403400c800200b90040840b201c4001c800c3e41180003000507000700400031641c0c3d60b6a28005044580580c41599441000000e1000d59a1285940b0240402c212007488141d41300c041c0c01170b2036100d62040366a140c0f10741d04a050030024084941c504450080d118400852000c8544030000325040f2080401c40d00603044050100c1d01950140c441c18401101c001072011a00000c40081003a551070b8102194 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 572911726 1250 572910476 572910493
    0x324061908091f050906130c03170d05130c0801020708070605060a0b0703020601051c0f0b0402011806080a14011203080408070606090504050c0307211103011b120b0a0603090c0512 79
    0x4804201c501d40007481224000307c15007040d2102141c450781070100804075181088099200d00003081611403489202d00d00700101c0c1020700328800d04807003c0d641282c80d130754042030000d1f01c1101032003a144120703040700035640307071500a985007402080b0003407106521480c0410301042401100d405010000d2094009003802c1d418541045044c5448201c50860340540c1c1052100048030100005001035000c074a81e0740c10b48903403005031801b10048109501100041c0030000300181e000180c240621841e103401c202e2450300c00981c0000403001d00903100340303150040ca100c0c0002d00c2400d42d660b00c0741c09480f446051414a0351140140c404aa110124441c3c9a2050200340501030042c80301c90701c03048004028040c900451000708401840c13484040b2030340c205c105030500c03e82082c000342c0818001c0013001110741110303444d01c20a49980800c1d0000d00f80c1e81800d0b403200c1680c0f05000c18403a004003601182894140204c0250880c09821503031703822242000100ea84841003003d80349140e100141c0030f280d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 572912976 1250 572911726 572911741
    0xa03061805150c19020703080f04030c0e270a02062b090309180906230c070807170c0609071508100312050f0324061908091f05 56
    0x4036070303541a06840740b842062160444041044840c9032001403400c0001c03409010041c1e050490740d030700140043c0070002d01e03000d03a048840000c0c01502d100700e00411f00d40c0c0d1150403040400600b10760300e94504c050f4201202d6180c80e50304200b440c0048103011980c03502681d070f01043c4590414285040c0b900741c1c4402542101242c0209045042e0300038008019204140e02c1c020070000140c424000c00ca080c10515100f0503a80f42c000480c0c1716080342c4140706a03a8012418100c400350342414032412105074006c1101389858008882007181c00004041c1403820076294103c080070024800051044100143c4484c00018803084e84150842c2010b00401481c0c80c40903010404c40c1e4850100308540d150030482c80074507044503042540d8111514280c00405684150fa0341c2c492482c501c16030800100411003402c80400101c4d034503c01c9440d103181e100ad50b90302440f0301409254001c09030080010204181644260a05036118904500321002200d01148034101e084000941645040d155410040c2d42c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 572914226 1250 572912976 572912983
    0x906030a210f030218010810030b090c01180b0702090705041d0402030d020a0b0c03131b0504060b04140112020f07030201020d05150303070308070e060c100b0103150308090a03061805 80
    0xa2142c00c0c00c00b54940402e83c1c180300c4800d18264030071410f0100380c0b0046820700505002d14030103950f00581641c43c03820304c1228a03640386240c0c090b050008601824210440c00d00f01a510100c40d1f480c3c86180c2000c05603800c002e50640c0041441c01040410701002450300e0f225070031011203100c0340c48004202e00f0f050040c9401d0100706007480b0155481341114000242c143d080792507210712900310341032301c2c0d071141801c00352109455070b0058005c1910801c0c055603040003401c05422030300212800c0100c1607a0f86140d0182c0d0180381320b171203610803100880461650159918101042e480e05005107002c02407030010a5540007045c2c1900146e60100c1c18804103e41885116048110b802c020b010400324000040d03580d1243c1c9a000b01042048800300b040d817401004107501015000b4412a00c0b40d0a40161a564041680c2c0050722682402840c104a500a11440701900741d0b203011302c00d8881c02c3d907c5111003540a151166045000c0b00c50000c04101c1ca803141e4072038071550500c0144803101c9400c1c52840d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 572915476 1250 572914226 572914247
    0x21051f15030f0216080d0e250608070e06070528020108010506091f0207081b0405100e010b09060f03040b01030b01210f0303090510060602010c1b020906030a21 70
    0x1000e1040100e859030055150713111100c05d91182c4242d0303544401010308000b03400b6114269030b9a1251480b40200c210f1004040c100301030140214451013aa220300c11600e004d001d07521b00300032a0803101352481c1824000c0040c00180c0c01001100e00203002101c04d2740503c03400c83c4849110303030300304103c0108540e40064610f004150880d8090f0901000c000021200c01d0a4180402120205141d555080f4001d2002d00018030648080d03c0300c94444048101a065200c0e00d00352080e403a100014044c5070300c0c2c60705202500c20700c00c1030500b07a07800c1244200701a440b01a455038402c00911044040c41c0c1e09000451080c1d2040c417102e0000e52652802e10100001a0442d9400e1981410206211a00945c0011050b60003811100c0b14a41c2403c0c182d00601c80084050700f1b9004460070108190002e402c0360044818990081006214040d402c55410304844510248500c42030402e801500d45030851540018008050f600803595550301c50503080c426a95660110080c80300480d49980c0026500c01c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 572916726 1250 572915476 572915501
    0xe0a0e100906080616180305281703090f0712031803030206061c050a050a21090b07050708060907031709060d1d100e0c0121051f1503 59
    0x7100b00e0800040c240c44030030007030030701401c0342d2034096054080f4071420340e50796600600f00f10152000c1e1a800c015403195034a40d90311160802c405690030320600c54070500ca10494009100324800e05082c280c0008550000e80144500d1050786054280e423082441000300900303600301e200c05c0c03000281c60b000d8811507590803600440702c2004010000b20340c02180b040ea20120032107800001c50544e103051082d081c42d00c980606241b180303005100030030000045801d10903002d5001c80380250070014259031030700111844680082d0030400100300c0d240743c080207000050310550980d0700c800d1320388070814074005044404801540c0040010401d00214130721000306d8142e03503402c26103070440d00c90204200344201e030400700e4065640c02d4180d00c684042903d440e0f0600c100c2e010b13219580c07441c06d80d00780580611000d0305400e0243c210074400a600a85020f5143d040b1210a546800c02c2c404e400f0000b003c000b40f1003507580303465242d15198000a500c1c2c403405820402d645141ca182034102c01411142080310b07030b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 572917976 1250 572916726 572916731
    0x5190c0215060a15050c03070c060e091506120a020d0c020703031e0504050f0117070e0a0e0f0f07030902060406050d050604090c050411040306060b040e240d030e0a0e1009 75
    0x144540980c00b120511307550340714280749940f810003003082803961044c50740160203846042e8021038540c0d403040300005814001c80c0d654043ea100c9881e16407403242d80c1545242d00c8002004980309103440c0903805a80b10700b205030300605181d00404031505070350b100c406070001078100c0c840600070941c01c0803110360403480d0100c000e048078499103005450382c42540526440303009139802000d070907031180c0b40d11214402034510032a4141041e0102502401c44c00305c500e0f205042e9140003143d07041c0b40d0a54144079007600c104440050302c461070001c5040303c01400041c100358889104201580b81c0704001c200501090340c80540d62568050300c48200c1d0340150040d48a1403d080344800441c0d80e24900304d0581d034084a00145040c22210130394007034852540004c0c160350500c0400540b160f4903101400840b26134600c40c46680e5216810007094200320804841e010042400d10103607424901c0c50740080034424205038100704c1c08140052880e8409902013040d0345a04420403503c500c3d030181c0c1400a00b90300805 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 572919226 1250 572917976 572917979
    0x30403050d0804050f101506020606030303040305130b12041103010504050c0111011509060503060105030d17070314090c01031a0d060b012303070201060f03021305190c0215060a 78
    0x645450781000980300342040790b6000400d0500005005601d05005840c003210f80401840406c40080e04810010502d83c1044003000990a400418042d100301b000401451441d9281d550590b0584c0107004032a02010aa16000c140c000480c1c0003444241c2009810007521318141ca010034441d1117180300e0070b009905003824440000e100049401ca8490242803281030288003110072070050094a40c000c0660030380d03c0c00083e4000ca2940180306540080d4141c8641e030380c840084c0b6a03507603500041500007511080c2d5004081d07945603078442d080310700d5140208030130f44460005020b504003076802c2c0c0c499400c484441034031580c061242c010140c11081da05005220f0b140001202c040311a08050400394860b041c1003030b180e2150040c8100e4000c510780c04840800148440d0134540c00032503100b07015610b48030003c144140400045802c40c1c1c4e00034100c0003054048804030001d00720107840154081e9440c007508031a001903000e41c0040080e954000c0c401d0420f1044901801c000c05005d0034010500e9600 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 572920476 1250 572919226 572919233
    0x602071e050d032a0f02030f06011a090d060f020316110c0d060e0f0a1a06150c0c1302070213020a02030912030f1209010c0f052a0f01020306030f030403 67
    0x28022140d800d81086100b0600e61901036282c64000751500e02c18030907000b9080700b041170700b40404102d64006d404580f03409800c509040e50303540c028010320015100c600c00301c4c0804000701000301000381c00030b018411610650340d940d5003554000c6d840a41095004410850a265801d2a90b49209881d10340400f0911582d11156113a4400b42c106c1c87c09002108a40c4081c008540c000005005000086480100409180d0398440441e1802100c60601c109040520701c2c01c0021081d0161000a01062642540b681400d9496104101d06a03c83c001c120300c8085507a640f5034880c0800380c40c04809130361454988104002e200c031740e480c0307000c084c0e2041c00124590740c0e0000c140c42e04104269244d00390711078100c41051860080c401c1d00035448000080b162002001800381c140500c90b203d0080c032400030240720580e0201d00900311640001c00901906002841409159503d4422240c400e4180781c00302c06d000b401c20079001003039007484e03400009004041c14100081070712004880042c42c28070303041d030b82c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 572921726 1250 572920476 572920489
    0x20f07052104292109010903090909050c0a09020a0314010b040b031b0c01020409230c0a140c0c032a0405040303110a09030203160b0906070501150602071e05 69
    0x10f14010320300c4210340501c01c0307203801c0079140d03000c00e10100058491096205209202c0d0041c0100307501c0c6800d11010940703250b414007410402e181d2588410740d9440c2007459640041c8440382d0240c68a1144110b030000310f131144180c00014004009000d03a80d403008503005826203144541d00080425542c004100d040b0a00b019242500c094a04030744e43c1c1d4442c880780c070303525490b03451250401b5a0000344003482e00030158010400c44200c11400d0100081030041c10741080320403217a000c1d0b8054003500113040301c4020f00062605000310b007401200410f4030000181389800c809030880341580b0040043c1e00c2850100184c3d2062692118007000c0b00d642030b85003074500c1c400206407501881c2c541002c44c0c10103000340c0002d600f035054251044e0f2a0702c0110402058a40c0610045c1d000b4022110000b04d4500c0100040d03098640860801e45040c0c00001440041d0780f100f901582d09568075184414242c4600c06108000c008540c02085a1818007182c584140003441d201040030202600c200126100c11 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 572922976 1250 572921726 572921729
    0x807080601120203071518240f020f1f050903090105040b0f09061204120e03211e0a0315060e09041401062c100509040503070501020f07052104 63
    0x3001da90b0440883c0c0b020a240c0450394102001000c2c100404000c8140d0100703080001e4003880c0340c0844003a5881f100e83c440e44030240d2034030703030601d16000c0c1e01d12030303280100d007403202032001032048423002c0c84482621803c218040c80c9440f812400020b01c0001c3c4041c5015581c0c1001e50781d809145000820f4001070f001e4407070380c4503405030740d980441c0074000c610321113054421280002e031106030b40c1c0c428a0805088040212000c441500d605600380440c0c0e403082c2e80303030000d0078005130051400c007030b64100c11940070904090b0709404003001c0200c0c0a0701034940c074040440b82402044203840d8a500d103400740039603900c0000e1481d102c801120410165074840c85044100310241c84d90506c6171140c0c10200c2820851500f100c2241d82451400900140001c521404e100fa050303403c400e10214401941c41d160b00f0645180703240d41b6042d9014040752070805501a0000d2007002140d1030600180c0d01c560031781e01b0030342d9021011100892080107000f402d008026a0841e000311816000380b5001c012001401503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 572924226 1250 572922976 572922989
    0x1e051e15012c040c030204090e0d27050301020711011403060105030a0b0f0301110a030f02070c09110d0e0606010e01230a03090c080313050604030f060c05210405070807080601 77
    0x1841d0010506050681c03242c0030442c0c000d4018000704030502e0f40680654000c1c400c0448840c41c007154001d0450000c506685004019a250440390103454460403040e51202420501c1d0b030710031304000420b65400d2000b01486403003905000070010b50580094085500c1d08000c0b03400303030310070010084941e030b020044a03030045010000241e002c1d58440410b45020301e0050040d010340c608910110f4200850001d40f04000c40c0da5400d0107044805142c0e4004e0303003d10100100140402d4074188014415600414030f03000e00b40901509214407850004291100d1440b100d18540003c0140a11960710002070030312903a003030030b001c8007450f43c01e01d0000c000c040d203951040c00003001003404130640307100b40c20001380c0a401c030a1040c56203440b85c12054480c1c1c000d10161144040300b075000112420030005407002c80e07400c20f0302c0321a141010389800c405050b03003103000700030480100044c103068010f04001409903412280c2002191400c1e02d46189009400c0d00f04440e1030344040810800072400080841c1580c01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 572925476 1250 572924226 572924267
    0x14012103031a030f0604060e0313050904062d0501120f0209060f1e03060601020d0c0b041b09020d050601031b0e060708030106020a110904030c061e051e1501 69
    0xb501240078a41d61034410702c140e2602030341c0c0700418241000110540954012582085840441250240c0c3d901c2110030b41c083c0050071200030803091810240c01c0341d0060080001080c0044215148000401c032094550321000791041d00410030a118810319000d802e07851104130842c1c5a5484154a0707018104000f4440c0c21202c001410540b100503441c1d10304400035000d81810702d15600810031071015450301e24064814207002032000d61002801002c002c1180d01c3e21000e45a050b15466213000000300705466a14055810032030f0640c2c00d60004004014031180140c032108000461416180042c002c2410135081c03403000c140300d0140c24240800303007841d82030030f40c000004800410b00500072a44007800c0c0fa0400b01c00025055000704121151510603180c02d60a800035200f00b110108007074601900003211100140005811540a0b0f0f80000009075190520381c60421408203079070301200c0d114040c020f520340d5022130620380ca07907060704030003203002081880303507550700080040389d40b403020707034100b42 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 572926726 1250 572925476 572925491
    0x3020a03061a0306070c0308060607210306051c0203010f0626100513030801090c0909053d0b071a040201050403051519020903070302150d0207061401210303 69
    0x1241c402c1e51510192014080d56600e24200308081d00c040d016200640c040340d000c100089203854044122841d00307500c503207100380b101c002500c1020080c500d00c04900c1407645c2c401010410b540d811a045a880c0c0c02d4a80b4020899540e205050070350b180c14040005141c1040003d005810110340c0c100b00303903050368013480b01c54201c4885152034000c27131a030f600c10407a10f0074081c080031801403c00207400901a4650441d01d91369007031510115102d00301c4070000140d0101080c004800c030794020503040740b0364460881c220402ca04a0150070450700c0b4155890003200c0c40c1007150101200f44480041c0400c000b298101545601c0780b206102c505285038100d201c000c000507003160b01800c1605d000c0c40d0072604403605011211031a24000d181502d0b4010700300f80d8004126a80b080c10300840703802200140c003038441c2c1441c0d58207100c041c861206100d00a000244003d0010341c0303403840a031100c0c0d40140070201e185560011424402e00c0180c01610108010f15103844084031010084580355605180028a40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 572927976 1250 572926726 572926751
    0x80615090d060204080303042d0609020a031527020f06031e0705030402011706030c0f0109080f0106090605010e01140f0f030412021006150809030d11040e0a050103020a0306 76
    0x400c40c1c0000610103071000c03c0110301c01000002841c40b540c85000b1142c5004130708503001201c1858841500740c40d110b42c11582c00080c0c902c1d040010082e01c05846c04d2040c40e02c03036482020025481201680300784d070742c031340c60541c080907d1910380700d20b41901c1e0f00e00b11000c8560003007a02041000001030103904000041460b403028240c40600000b0a480d032204207061240e40202a540103032810303800100c030103251030750030800c0044903406440014018034034041c0303030130038810313108014041b550501000940008540340c0901001090400c19400014080c2c14041e00c001240c0b45508410304218182301d100e40542d81001d100001c1c48500340e042c0b9111340820103103030f445221780a100301072a24080f0500041005015005072070b00890340035114080d00715102201250003d1044100c402440710b0a6507a6500403c0b02603040482d20341502d284c0005095840c3c2a5070702914082c07912034000030304111035100e1090039500143e5800050001e549180c00041e02c1c2e1020b8000507040c10380d13410300c10600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 572929226 1250 572927976 572927989
    0x90607140708070609080c180106030504030e0909010e070801061d040c0f1d090d1e020c030105040f050f060601211401030b0604200a030209180108011b08061509 71
    0x204800801ca03072283da1142d038010a051014862440e85d0322802820004500e44805221001514008200200d031f18110088000e4a0007400070340c14071040e550300c444a52204118103208014840011035154510742c1101e1400c1c0c09a88401200e91405100703200b1915510000c42105000c0c80e00071010b80c5441c1400c40c1c00740c00326407110342c0c68585000700081c0490300105d2800c040d0b40b2481216410b43e6040e60303107910751140206000011702e0031b964034001c043c80c08082c04007421403071040710070000f082e6000c00d084540554042d10a030401100d0783c02000400c000010a04180e140a84060705003d00043e100344560000040c0c000da81e41d40311000503000c4d6112f501981c0724441c410100e235a40e401e00d45c0d2024410341d00240654100a002e82080e038903c030203610700b42140c282942c9001e02a00e4210000c0d0040b507240c40e440481c2c8120910080c903600061b90103841000d000248a0040031302c007000110783e0404041c2805400c0e000c0011070750f26081c0303521411a1031403560f6510700242001600 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 572930476 1250 572929226 572929229
    0x20409030504080f07170a2a03060f0504140f07152606010e010201060b0d0221090c1807051e040f170f030921030d2306060906071407 59
    0x90744a413a1a440110000240f10000c603690810002244074190041c00c1d200c030116171005d04510418030b04080c074294000150707a0400c1c0c40020243c01a903c84e61604103503146281500541d940351400e11040c0030392822030128604802c802010300209500d82c00340c94544078072450bd6075542c0d00707c0044002d8020340c002a400a2100c030b604050503803104c04400d160405807071860010b64000682041540140700709410340700040689403c2c10458090388002c0d500010a42d400d011a06c1c602420400440440328000c25844003d041701c1c208072410301c4013110183c0483c0c01d442c0340303640074030035620380140403075501100280303984c6210807001407011140d10582d40000c0000500b1600050742515405030300e490018280d00f9211007044014140e96607018007a84141c0c0480b80d01c51440c0306004182c014a949001c1c0c1042c1d07418030a40b03210503401c803002086000d07199204882e128203000701c0116020790041d01152058140340881012071864012258004e003000110414444e43c18004c0150b0710 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 572931726 1250 572930476 572930489
    0xd0b06011e0315052704021c0506150a030f0b0603070314030a090807150c050c09070c06050f09100b012001020c10020702061603051210050a09020c0307020409030504 73
    0x752680300048010020140c00941c2c0011001c04103020a9600c0c0442c40c03000d401310105d0f2a4140840440380031580c20001400481c1c2c01319200b002a6a11700000d50300c002c1d028020b03070240c0164501500d1b0710b403030400100c120522450b6030040a000050840703a51f00c0085d81c101c1c2c07081030240da403080400d1038448503400103042c0c40d200310650321448070004010000b01c031031580e80c10a4107945002c441e946911310b0284402681c40804182c9040c0d01c54a0f40504030390044007150310403080207000c0740c0301250950700300c40003c1820240109001050080c07540003107500d181c501003860a00303041c546444042540f018001c5e2a40d1500706180e2141c440464500c1c4d010144504240300301c00054000e50151007005018007802c1105c013030007130080c400d9862294014040503d804015180700024070703c610011005d0120a20144561020000701c5600c01d03a2032940c0e010b201402c10041141c095401d600403004640100804281041c0c04001d54400e680e0649002c07030215034525003580c85001d190410f0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 572932976 1250 572931726 572931767
    0x712030c02150a0f0c12080603070b0d0219021c08090c04020d0906141b1c020c0d08220f0201110d050a080c03062101021308010f06090b0d0b0601 64
    0x25401c01c0c00c2c100512030403400d520f90412000a4000a5500540c405805412200c0c1900030101c590702030382804c0d600c802c005003607880040e1226001030032a040b440140c0c03191035000c60446908030089002003603a8103503000130b1080c41d621401c000000007100f102142008019804290310001c2000b183d40c840000400030364583c05d41070307522001048841000d60703010f41403d40d082000e40c0d9902c6c50398043e031907111030644104200100f5244a620541141403600d00b110395119041685202801010711900c02400f40080704803001001c00c1c03009800d201d00710340c0340340d2010312204114900000603a403001803c903c2d50386500042e04d003030752450f903107181a01130341408110319540107008010004c1d4513150b404143d03d403103100807130501003202c01680042400c002101d01803041804400d0b40c1440c407001516001039442c032102c010310258456002d503034580d86010001c1c0040e02620001d00880d040400003041d42d1000589645c0e44c18030b0240c031003803414000c0381c42da0f4806c0f1000c880081c003140d01e4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 572934226 1250 572932976 572932999
    0x41d0304140f04110f03040305160503030402041505010f0c17032a0313030806040b031204030515040c0e09160b0a11060601050406031805060103060e10020c0712030c02 74
    0x20031403449954000c0500c60200c8058040541c5840d20600700c100c070454050038141714010003800c1c61640b010b00180c0500c1001d0100010f810407406041c24a00d102d0005580c50b424144144801d440d100c2c0d82c5880401c1c0900381c103000d030340d03800051100005820701d00303000070840340d0a201c109003500402c20300c2c10f2540002005600160401015042c80d030f0070742c0d0070b9490710000e60001014002030307a40035181040803540c0b0010a10a991040d00410700810002d00ca400352030009140c505004010b243d10300000c1002c005001c1c4c14003000b040000110403a0300b4900d0981d459003285040c1c2d0103403200c04041000443c01c002000c12408102c6c07880d030b941c2018003d44911700f40f082a00010044000111190110f403011000400d640e4080c0c803068640380e00307003424400300781d010300050445a40c81914000e07c4030080f500800c20280254012100040e940320104940c80c02d010901044c0d40c5554010045440c0c41e400010b100c1044810700302c0309401c90300b034a1404484c00082da25000e036018088442 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 572935476 1250 572934226 572934239
    0xe040f0c090f060c0804052206140a050910050402071506030f02090114010c0b34110a05030f37080a11041809080414030d05040b09041d0304 62
    0x15481c064441c40500003407816519401290600c50706003000f400c401090200f0889802c0040002403071001c000281051464a218203408035080c1ea8051030b0540c890714076000d41070404800003c043c1109603485c444d989081155a004c680703c910409000b154001608000d001d80301c030002c83c552003c0380701072001c1c503524100341003441d110700300c1130f40310f5000800002400d40000bd01003000e8207041c0c4403c07100e003940c0d40304d00b030301c10400400300361400b1190341040c0c596500c0404680a2180350501d6002e8005061b1402000e802030007402601c43e07070014441e1000300d0b00010984a40450002c101660f07017540764a44807100c2c0c1c0022480c4005194100441280c40d0003400d44141900c3e560740359160f0b65255114001507032806134202c001c0400810041c0140f10f14902c0310b50780d10800d2200800c030740c40d40c0e6840c0109035010751311808400d00008441462407a05005004401c9400e00d0300c14101414655a01924400c07154190722880c1c0c1d64426146c145210500441c409070104140c0352074550303403507 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 572936726 1250 572935476 572935487
    0x21030c0c140102100507020c10020c0a03061b0201060b1c0b0d06050405010510120b0408070206031f080a230703120509130c02060103120903050a0c05030115080d0e040f0c 75
    0x30301207030242c0100001383c481000940302d1a48140700d030741e00030204100e10005000c0008032108140c400c5000740d0070300d802c0d90345400ca11000114410360780001c071485803190408440b03d80c05804000c6905261080012046500951300310040741d0041c440110301d1640800003c0c0486035849030001c0c042150081030001c9503105034403071801f8030000c2c003065550380500340c180c00c45401001c002c107610100c5900031606445036154403c4c030880d0000e103070180980001da03d50304110307140402003082c1c0c00000c0c0d03100c54105c0c00c1c0c8000e186000082c5424800d640d40c02c0845144c00000c2884180d01495042c0508010043c620003984c01c1706500103141d043c0e1100402507401007070f00c14000d50040030400c043c21007038800c42005c40c0d4564064840782c0d00350358a0216000182003002c0410100303034000b1010510170710920740c070140f082190340310440c5048281403d40300140004900621262001c100c0d200c400f2801c04c0c20400c0e80c0c42c02103001117030781d00002c0040c4001e152030214030745015100d402081c0c002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 572937976 1250 572936726 572936759
    0x10b220b0411190807050a030903050c03031f15050702040e010f090818030624030a1506031211100c02030f160209060306100902092803150621030c0c 66
    0x204036402150f44010540e12900180c070204002903081000180380ca00c03076400103240030300c01c2ca880d9143c207094040d600d00e1904113480001e1080e038150a41c40310001d102c10300130002c02c0304021601c1a0702d48090080d10900030700300b01034012900c40400c140302e101c00303622040c2c1d1111009410072603c007050030300b990b0a40028007540e085220850660015140c00544035114103070000c0810b4661210b1520444441e50100200d505031080c0b0100400141c0d011fa46a401450301a600007242851400e1485400442042040500400c031707200ca50b80480c0800c2007a880c030700230400031903052000401249103228000000740d003420081942da90030355041d0846030701140210f50400007500c0304002c158030f50030b00303944145240b5107c1c001084691103940203801d212000030310040704030300c99404820810030800c00c0308015050042c42402044840490001104ca0901d0304111072403e0180c00856207801051401001d0402c0b003210040500c100544800554452030071407420303690300c81414104001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 572939226 1250 572937976 572937997
    0xc0a03203a023a0b0a080a110a030828091214030f04030606080601090b030604060c18090209091b0703080604020717030109050f04020f0f0a0e15030c03010b220b0411 73
    0x8100d0522082c5c03038621444d105070fa0144000e00302c2090b465550003440110002e0041e000300f4240c0c400004104030201416610041d2900a610903500d1100004d541054084040a0100c00f8009000c0d00a50080c88a006c40d80406000d100e1110002c5491441c090400c440b407450500260220030003095811000840d000c540440d002a40c8809442d010b56855040c00b030f030198044070001300461140c0c6c0200e0680d202a042c404c810a08099907420403400707507001000201e0300010003901f241824175800d64048521484004000f1420010603030b07038840d400c0f002c0c080105141c081003080e034441d13040f1008a9481080c080c40441d4920004195400920a011445140c1400203c0030198902c0380d40c0308640c014030840f01c280b030403820400107200f03110b0a01e07000b004044011486c0c4200c4201c46001d803402010210b0010b200e1010540b81090b076042c01c9019904201c0c60014680b94160b00800f203821150300e1070740c0b2074940e520080080c00700400c5285d01504100e03900b4802105200141189900d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 572940476 1250 572939226 572939231
    0x3030f0c180801180b10030203030315010206090f1b0a0503010f0c0914100f031d062e0b091507080a080114090c0a03203a023a 56
    0xd4620b241402c07180714101d05008901800691000540e01c10003496008040c488807585050b140e401107403a5800c121026904412264181c2c0780d00e42e0108071040d8170048500003001c10468006581741c6400d1350b400e1040d004800c10b200280c156480324480c002038a4003400800c020029072807028042e10520f003104000c11004240440d6145001201d003401080141074907074a42d5491508494100340c41541e00d0801d81e03139210300c0079810803221b41411920280c01c02031102c0c1c2041d400005102004880c000340404043d501d102184d031100b07440c2c60440e41d501d03514544400010001c2155504220510000c82d54000383c01c074208100c0d81f0152400380620360350145182c1c2c031121468203a010068025030301030020340000c0e1102100341c00070603d1103524a80840c50800303442c0303c050044140b4a420480c2d4001240c02c1d0b00e61807020782c216071181c101c6018010814900c1030041078192032420384107800c5400090201c43d12400d03901e0303c0c083c01010b20002d000f1941512802c1c18202c0c0c0c43e40802a120b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 572941726 1250 572940476 572940479
    0x1401112805040605070b0402060412060e0c0f1804030e0a061805010f0e0d0620091302040f03030c050304150507050c0108011805040c0e0c1b151303030f0c18 69
    0x744200162403d4501e5515518504480d0b921400c4440c3c0000304226801703681080007251125001076030b1081e5038880c18021880b00043c08003582001c1d5405003490003092003503030f540e9440d80d4944481062080c80201d168281e22541000c5800005e01650315070440b03800c11002031210b511201c210310841080d84004602030f181c00c0115600c03000030b00200300040d03100003501c28600d041c4105401c040d11403140020001d41c10340402100691a101c0e20000d03110124600340281401240d41d1406010300404500d0b0504211851890000c20301018040000f000d218104001d030800807540503003c50881d80500c1c00300c40d00000c0c03143d4045107080740d042c05503840a20b0194000c84070503040e50000411501c107a0508060200101001841551844000d81000842200c900748082c01f81401c103c560f42d4460041ca844d4031000c0120040150315802040101c0d055820489030f01d030091010900d03005494441e0030b08401801c1064142c2106030321741003992040700d40060311000c00e48840d000c00004a07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 572942976 1250 572941726 572941807
    0x92d030f0a1e0810230301110903120301050901032913030f020a0c0911040f0806070801080c01080403080a0f0509030d0c18140102031207080a0621140111 68
    0x240203031003c020569000c8130074032000030007995940c8000c602110207250820118000303400d43c2c81040170026800400112101203040500800211100400690f403655142c031001c21800c0c1c205110240514003031603848001208082d00c1d50b80000e40d1440b96003a141040c080704046410080c0040703004c2804009041580c50000c11002000c42d04001134214161070b020616000d007880050602c00c02c2c008020110394101c0300c0c0c0c089005004031b04002e080c145800d0070f018112801c180c126000075400000101c407607070780c00390390554402d43c14074041903035446415401015003034500016050038102070401c010204000082c1a100c03161150034456110449429aa4441142907015610b04008418442030003d00c0790640e1300e00e4103204032480c18081c3c1c190018000d02c10344191001984250900c0303945d040b00d00908001d00070b44001c0e400c05820074402c02c4940310a20a00422090b11080d40f00d4408000798006d1072615440c1c07046540d5928800d00207000c0d00108004c0c207100460702c3c58004010b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 572944226 1250 572942976 572942987
    0x110f030610050405130501060801060608010b19050d14090d2a0803100b0d0203070e0105090f0f040f060e0406050906040c2d06020114092d030f0a1e 65
    0xc0070801640408541800306101c003a040c000d1401c048611500d2288002500c24480d005c000e0102c0070001415038180030000f440e0b400180d02000c1c043d0001e1186a840000880c46001e4000c0b0070700780103941d20025403070703840a40840f00081310b18107807400400152000220350114209001e607607591100c1c1e5010900d00324503c0554030500e64030002c1e0587c0001070190001581c200903c00c0c2d50148096564003c03840503440700041030030864020090020079030308080c01d0a070302d4209003005070502840101003a0b100c200303590300c148200d02e80c05950090b81c440d94000d100c51f8403207550900040e44c44002400c0c050005031000ca0f041403403c03001440402000c20054000c6512003802d000c41c0b440c0840c0200790b03280314071a001c0c0b40c40303400301c2c50380c1403002055415000703060b19000810b80282140c41000545401401402c02c1d81152000500f00c4010b0400003440d40d451550b12801c00041d40700b8280b0f140a0612807660603d000a88286065004403090440100346000301c902e80030741d42001c496 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 572945476 1250 572944226 572944231
    0x20f120c0a020f0d08190e0a0614071416050114030405120a0302041d0403110106060e15070c030807020a12050309060d150e0a14100e07050706020304110f0306 70
    0x40381c010404410042c0303002008884110030003040c1c44000c0c007403a101d032401584184003541400c900910852403071303a007220400c258903100b100c1c0701011500c3c01802030154480e40c1c117180c2c000c00f40019002c00b08222001c07100030300141881103c0a091090b03150b0001c0880c140261804200128000c00e4a02c00e4503088a220350340c42800b502c486900c603061885180c0101610009041c1c0a210200b035103081b6107242c0351a4038400c0c4c000c01240c01c080c10060881b8007a03800240c026410588140412504046420b540e00300c1640d1281c000e1841d0b4034120301034005c42c01d004140c04c1000d2000014083c0c4d50000c4c0c01c04038000c80e00c541013941c0c6c4251006036250710b620000c1540d08103210341200e80c94a0000740001c0107450001007620000c00e440a4030701c0c0d403503800c007000800080d000e201c0e9040c0325104442c03064154280c40383d0700b4100480035118000b1544500e446594a0600040e00c26200741c061b501d20561012003591a0b09040c078061003040159030b015030060241c000074003008c0c42c0000d220750 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 572946726 1250 572945476 572945497
    0x150114042007020a08030c031b0d08040b06060d14010510050a0207030f060605060d09050d030e0606060f190201230c0306150405120c0f090115120f020406020f12 71
    0x10001da20a035000192900b00d82c20581c0d0140101c440014075200920007009100c14102c06140d940c0f0540c11061014051041190840e0380100d204120150f08607c10540040c5c0001e01d03408240c2e50000018058803e485180007003d08101c2d000c0140e104001da501c1c103030f807000c49400217031848500b4110790601501050100584c00301c0401c00216200148145096005076008514103880c3d5000c0351955105080c2d1145082d83c030300d600d209228043c08070141c60b0303005150501034071094481840d681d40018081c1032003070000007500c0507010101c108a074500c07102e11500100080450704068020840d100807140316414407400d83d0f404810450000303110b595000401401c60f201c540500c019040031401e182d5460404020114103a074070b2004000060090400920000c0d034420280200c401040c040c05020304122001480140c07841d185c0d02b00713003000794500300b41940066900d91000d40908a01c07007403120720004010a01cac2d94041891980c000010084405941442c2d02c201d040f44221400308 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 572947976 1250 572946726 572946761
    0xc2a06030405100504020f0405070f09050a0503120d09121121030c0c0708032a01050c0910140a0809010b0109061b020114040e060a0611060f0c070515011404 69
    0x4031003000c184d503c480c0e00140040c041c003450a8656001c2001c440040d00c440c401300720302c0300403003030301960000c0100050030b420b941c0564041e00d13050119644000b41712105c0d50034200031600e06100f1415500c28403005400401500c040806c1074800790500001d811489a1802680703456203140000c20401400c444000c00d400f461907071024606451904020a00b030190300030040c0000b085001000034015240b1402c91912541545100d114400c5800440d449142d0341004100305201801909982815000381c07407561401c001d2081c22a0340c8442a8080c00d80c1c0310000c550025980d5000d141caa104408200c001c1024078000d1740103454141840c840c0700c002414824410262485901c48002100e03c18100054807100c801125102900280c00104401c260704081012601d00301d40e054008041600b00b0180e540000340c155034641c8130080001048000340d10204001d01c0c0c01d00c0464020729041810b0354009590b4911200d0405003c1c0700e40f0b1003030fa042000c8603c007850a88644040d0300e06091a5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 572949226 1250 572947976 572947993
    0xc05281409100e061201090b0a0605040c0c0c05061b01020406020a0309061d220609021e07030504120309170a0c0f0b120702121c0c0c0f03030e01020c2a06030405 71
    0x81081714005000f0704c3c0b60729500d4000050004545c401842d01603240284041030050601c801e02c01203810101c50603041080d2013280101050190307012009452050718815541e02c0d5014410502c50258130051105600c0001c000075103560200ea80d0b15204c0c4203a1b51000066640c8004a48030740355002c004900885030a00e03c0d19600d062074185500c0101e01d10320f18616551400d841d0b04403043d0350f120409098000860104100c0340703044048204955049207801e10856440040c175900032800b80000341c0e0301d500702141c1030500809600c1d0060203404166222011a00712032604d40d1300e60703c01203030804c004070300c042004500c042c602d8094465040210b42441e44950380b52500d00c0e0003801c001f05600a1300c200e9038034090404020454044441541c0e03003000c515200d2441150070200814040180c03410132640011700e141c2a0000094240c07601203411244029114020f205034980783e84d880c81501003640480800055480c05014184030180d0f014001e80140215484200c0d001413068005140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 572950476 1250 572949226 572949229
    0x6011a0a120b040b0a0e1e010b07140111040b0d050702031c02090a0f030302060712180204050a061e03020102190b0103031112041d130c05281409100e06 67
    0x40402c07802402000440c01380c0000000c550400000e821213040e07400800200000303501351030b026005070803084501020305c0d032428640302c01d5030040e11001000303882c404005c100320300030940148150048480c1255600c0d030b40e9041c400416449289851501400c3c807000540d824008016290b107901c0d00900220045070401030400294420003655602c9038260801040b01c4001e062610041c51180d0000c0a29041481c005001a400b4500c40d21455080c01c2420769040b548846012080381d0581c0c0108070750701d8203800389003d0105504030180b0007000b0035041c10306400101225040b28000e070291410f203600d05038030507240c131006035014145503500401080040c1c8906802a100307a17080041d10304882c03880b501300344694459840ba200901c2d505507519041d4466614042e000303120a0700c10919108150346000748503131a4810b0912a05e890340c1c40450300d500c00c5a000c084580c6084c60310050760344075040c1800300351524248030f0107100e403c8005038a0201d00c020b6901610f0241006110550300c5030b0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 572951726 1250 572950476 572950481
    0x105060405010e130c0f09150c0f06140c0a0f020a0f08070c031704050411090901091802030718230f060f0402030403030e10022718070206011a0a12 65
    0x480f441e4008136629104040001148103051000c1ca860b80d03800c5503007207040001040008142c00492030140d0707070005c00101c560001054200103601800b4141d4141080c00e2440c02001005081c1c1401c00d120001c004403071301c51100031300c400c0b00700303881c2d4141070100b4410891f6600c40410004018101c200c030702d90089510b11000d4108280705070040328405840783e494414050013400710001030400498244802c0ca89801040341c403c030b040001c42c0c01c008413900090322100061060301d180030790790503424148603e00300118078138540140441d0b185c0303940d60400348031003408207a100380345030b103856803c000800a6140c01503100355000c100c5195a03d408400c12124400074003000c0d808200c136003003074505031681c1c000b45200da4001d89000a207990a10304407401c01c400d20340031900c00c3d44104480d207c1160000070f02941d607428101c03a40612800794011a43c20005003e8580d10354800c5c008128035654005986410b89408501c880306411046100e5030060041003c0f00307002c40c490b070030051311014166 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 572952976 1250 572951726 572951747
    0x90e060402190b0a090f09050f06090a06150504090e07080a1103010603021e13050c070605060616050601060f0c03080c34030e0f0d0b13080d06060e030105010506040501 74
    0x800032242c2d15907031a030680c01c5074002000b013070103d042040104089110000e1101c010040c0328020b01c005e16000222441d14040100340e0382c8558400000300c4c42c1c1400c2a4060030241c0140303e500c003001404018050059003151180c100c1e003d00b1b01e134410320304200204545040700c20940050954150319525460200040307901142c00d99612070002000da510f08130300f00f29007004c00340c0344062908507400744113101503040300c0301c451541000280b1010381c0003842181e013070030381000c000600ea03102c00c1d001405501c2502c0744101c91034840442c020900c140459294104c81c29920354210314009140144d45215040c40b010300032441d1040000d803041203240c02440024960030400e000e20b0440d03d9005031030345440ca0700c14154003803613418004064101010040c50081211441c0c00c0040a00c0081c22400151100410407400f41010a881d00c1c0f0064804444980c810002601c0e40d01d10350801c2d009082c40d22400d07000600d0092004070606040c802d1905882001c0c0c0900d2500b42054010364400d50b80c0f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 572954226 1250 572952976 572953009
    0x12050d0c03050d02030a0c030c0905011b030c140d02071a03040809060d090507060f080f0a0207051009111305040b060915040e010203060a080f0d0f03090b0f070801090e060402 77
    0x1005050111500744c402907201c3c3c071003d600064801030700000201120b001d07401c440d06010f0118000d1080342c0e04440d03541204001942c0039070000300300d86004c68050b0354858004054032881c86194041d01d402082c0ca0083c015a5805c40d60f01554540c03103100040b5810b101c0c820031000400104000c21007000084c018000003a05291403c803000600e80c0884528030015100d90300f104609118141d80000742900780001842d0100d094108560005940e1202809141803558001204010010103003e400010190b24008200010240c10a450a8203101ca01c45114400c2c0303030140c0001201c00d1050038003135030f044082d680c402d80c0c0340700034000c00681c054024038906500c6c01032010b4966581c09681c9070300305a82c00150f1241420018008054515000388403150014058200800c40002e551004042945410600c1d040030f10010b500034445004050003d0300400d00304a031007118918103074041c03462035545161503a80c500007030088451025240e01250002d074007041c05031800e41d0060b4410001c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 572955476 1250 572954226 572954237
    0x4140606090f130f0b1021080d020901020c12010212010501111902030c100302040e010b0906160309030c0303030207050f030408071a120115140708031906090609140112050d0c03 78
    0x2158803070800141c0100c41c48900315204035402c1c040c20504031f44a025151138a000302c1c0a40e2103984d920303520360164041c0c000b481580461f94185603882048460000e040141026000c03d0025a1150103540b192034880c1c0c4c6c42d11003400024040d4450b210302c030f54802c0d018016000395107100700340110000006030281c0e8944602d0141c81e060741e07601007a42208004d00e480050f5510b10f03006445520000582c4200c000140c140304840d182c0c0c82d20812101021410b00780c00c001f00c8c203245001d45010040d44c00151412450080c003004058266004201d003c0c0204100c80ba400403056041d07030369104901030444160011101003003502c032012050520302d0680102c160903d024000c0c0c0c44d140300002d07405200c8170007a0a084c450b100b5003140d00b4041814840c420a890040c8540b95510f951002a02c25041c682d2441001d08a010541d0b00070000b920084106000456071401c19201070103c17030011005d00b6006900000c0d21602c01210070340a03035802000342c5009070584000392144641000143c09110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 572956726 1250 572955476 572955503
    0x1b0318011103090304060816020a0b07020106080727050114040209063903120601200a032307020307051c050106150f08090606060c0c0904140606090f13 67
    0xd01d6101651141e5083c4005680f9103140100050801ca00505560407190700c006451443e0b60780810241c0c83c2c0e54000003440c25035260720104a006240982c000c0d4468000c2c0440030810002142030404c0c00506a156800c1d1140c0001c0070208668081c802c449580c000440c42031a141003135000b0b4141004010100c6050003c1c20508200301e826482030200c03c42112030314400300c2d41c00180190075085030440150700b8005913034048120985c000e890707141030008542c039040600030070010881c440c0007220b0941e0400802440c028041c520169145c285181840c50036000060010f1300395a4119001001404128984001e014a02c21807400407840c02d016604080c0124400b4002d0030020712100d01044110846101c000b0601c02840b01d10000300020704040c0b041d041d0001540075040701c0202c07000786c2d4074500101c8441c03401d0310960700a50001c010200b04014030042c2c16414041b40b501d481a14500d684400800a0b03103c0100c44840f010f03a200c1011849801c0d80c00300a00300c1a104031070018400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 572957976 1250 572956726 572956751
    0xf0906030a02040516080c25080c0a0303200c0634110c04060303080411011112130b0307021908160807061a0307061805120a05061b031801 61
    0x1310b00455484e405514500494107540350301c000c4c0303242d00000c3c400c002400e1100118130340c01140c2d1205075090048114101440c1400840c0b0110f51400051100321860308069280c00b070043d18240300c2803280250121a5101d0364002c02040b0f070b036155400409004542e49481c80020700e4103418810391641c0002070b80402030400d2450010f101498683c071041a5085050b070201d140c0324100016034010750030070703d04000098100301c02681056008444d001c5d2140c00d100101c0303070a01d400d1301c581464800c0e29402000c60240d40014030344000200302020312a6194102702480344819290b0100580c800f580610005940c03241c4640158812488585800b40504543e44001ca00c80e5043da01c0741400140c0c0400c00842d4031801d08015916201e2503078406004c030010b61100301c184075582c10b0004034600f4891070089a40600b02401d401440d50820180f9031a000c0d030b6540758008100e540d4031440010510103855480c20b140901035031001a031540e5502041a00581c0c030b407a442c0e440640d00c03282d6082d0030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 572959226 1250 572957976 572957981
    0xc180916061d060909130311060a0c3c050f0d0c0809011109040e03040503061317030c0f09010c0501110c0706170f04051623030c0f0906030a0204 64
    0x800c250756480c4074200c582094400e40156100c040b80c4a44030800c5120f0381910b901c1e11803680410b400b41111032440132030400303882c9620030500402c087d005501c01c101c10300140b9403100c00840f105586608d02000386452405503000e02e00029110f00d800d0104403502d5005282c0150075025481c03510394102040200300910720342007005085100c548a882c1c2c465000d82c801c00e0698400c03556402802941c3c01503c071480d03d845a21481402a80c941c600c02c00c00030320400468000301409021250345d4a82028030101c0e800065004613044481c2540d1048045903141c20740c2e0145801a8040b8038000c046001c02149511080f26a8140034a40400e940452804c1c8070f03203c807242c0b55168595586024107a041c0c28512107400034020322081e1010014403a0225903050b5001d0b484420140c110340307443c00c20740c2c54040e84a14540c281d588003440401c1c03102d03031658601c00c0801412000c1c46080d41e40820191034031103060003240c010010344400807040c903044000075000a0060103540c01810544c02003410b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 572960476 1250 572959226 572959229
    0x71202190603061401020307110103020a050403080d0606020c0d030f0c0f050f0f0106050a030308040f0611030a0c030c03050609060904060b1309020901050a0b070b040317090a12020c180916 83
    0x10940e2210100644c1800002c0c06001d18001d10145141003141d81d2103400718040701e140300c1d040650102e070803000c0c03d0283c41100d02440c0c0082d103490300c44038201c403d000034101c035014100040c020b119006070241804080c090250342d164407024601e9078101c004841401500c4000d0321104403802550000ca01f0038001900083e0010340038060340d03400640e14500391070342d130380c0b0031703801201c8400d4100302080d40a1410b0b90403950140140d0001841070411901030300138200b01d40b20500000050028001c003030383c03051a000d001e0782c0b424441701c910684250308640044035020380101183d800070b060342c6007010380260b00c03501ca80e0001610f140c003e0302007441c43c0140341c081c58a480d511340e0007400350301c2d05140032401000700301ca1003400c0b07034144211403c06001e070b82e130014040703440717200441e04142c09245250442c4100c41c0e4490750900e003600446641e50040c034010740d00200c1070320302101c3c1e052001c660000c25010240c8100442d050503542c000e51032340b002b80036000c180a02c4071303441a02c0c00d21240810 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 572961726 1250 572960476 572960489
    0x140108060f07021c0e030a12090306111306030b0111071e0b0405210f0d05070209090a0b150d021003021308010507020a0303091a3607120219 62
    0x5a1440c110740103098615010380b1001c1558801d05040c080005041c21054568045107080c080c01d90b84c1602181c0307811440ca000034106101d0442c00b44145038048102011240111380501500e8040074a0140521400c082c805040304021000d1203041d010b50403c400140b8189010740290410b1003d050524006400c5882005000340140b000c2c04010703810100074000c8034295500d0a807510002803070724070f0074175640c140701104020f0030400900140210400b50a2040a607051071088000040580d03010f18403ca2044801d000841c0300c44000203008025154481484106501d076021510000c514200d081540301003010140b200588464400300c1791a003050718056110603144030340784490622500612521380c5031400304461503500117009400c440d09403e00199510880c248224201044066901c3c603892600c18042515451800c864115400c0c1070380148407403031080c080240d03c1d0031590360401588019070070b1003005040015400e19071306c01028000d02e210700b42040e21940456a1102 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 572962976 1250 572961726 572961733
    0x6060705060a050117010204051f02030d15061209030c02040b0423060108061e0409060605040221090a0c09050702010b030a0809010206060a03051b040204080a062405090c0d140108 79
    0x4005c2040903140e0420803052034002581800d042a01141400030117041c200c440f502d280c1d02c0044028001c1c0110755402003106010b0200d85090760fa02031b0503140e03510441c40003681d86170202511103124491141525416502ca20300d02030342e60200406807413600c0321640d0140da40c42c4040380c040d96600c002c0c882d00c2003684c40b54882e840c00030005030201c4002000c45010780c284400103611880100f48ea003903902030880d400580e149503400d0005c0203040c5500181d0b0000c0c400036028230040701001011074505400c84c03913080386035110000c0c1500c0740540e84008040c460004000d005c1c45d035080c0c104a5200c10103100016103010305d000001d00d04182c000b011b84a40000050b13000075540d05200107903100405980014001e031440c0d440f0b90707503215024210041d81070101c80d814003550340c9404440c01400d60708116035000c441e90425400804880807000c841c01d9280451001f44694416100e0403554010312121841c1e840e04200101a03000340b4001c9542039940318103106c1721060440b074a002c0c02214005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 572964226 1250 572962976 572962979
    0x20327040e03121f030b070203130f060518030109060504030801171209040c0e03100608011d0a150908120a1a1c0203070302060f130906050109090506060705060a0501 73
    0x280000c591100d045407466400401c40c104882240c42d00a50300036031140c0702c000c1c08442c2e0701c1c0460021a00d9400003040041c1490920691170760000203800000c030880e62120005598111101001581d4880e04001c9003061242000048102400c80c1d99440c0140010aa01d5001d69812044810442d0100d01040c007880041c03002e4516960080f117148000002880c8481d202c440c008494000d000101f44610384850180d0022485000b41006591002d021500340c0f030440000d0401400b040d01841d00903604e02200100304400010090011184840c082c2c90f0078000c94940c00790461004040701d030020b486208800001d0861002440480c001400f949518240840306074103480740c0c00d016150a80801c40381d01041d03503c042d2528610b280c0c2c030303801d944258054030110381440d0203584049c0d0300000114840c60755640f0304004040c0f1070001c81403100180c5c3c55110382c47c201c48442c016580050080c0c0c0040c0030300c1c40f0030307882907410600c010403140c100078a45e03840500e040f1046072a0780203103454100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 572965476 1250 572964226 572964229
    0x204030602030901240f030b060f03100b181603020f0c0d05040e0c071a070917010207030306051804061e0f0605090a11090906012109050607030e1507020327 69
    0x30800e20480d4041390000c40d041c80c1080054401b040340c017000d01500c0440300421110b5a40c5001e09029034070140c160340603451801802002410380418085c01101074000344924801c66280c01849554011040b040381201048128002d401082100070910000c201c040e030402e404000410a00c0034981d00c580d510350070249207a0318648060640c644401044c04541c2c0025452800b10f564030812603c1c006c102e81c2d4000c001c44400c8690340c07200011100202c07250184c0304044d00201800307030107500d013409a40d68501c144078070b007115032101c041201c0101c40420001052500148065000d041242d441001410140d50803502d00441e0044d40a5441a080200c1e0030320034410350340400b1003e01041000405207440503184942040241301d50050f00c0050100c0e0301840c1142104540f802c03021588411041d040c000404501d07600303895611805000803540ea20030f018a03224529240080e010b04460280211188640a803402e8207600081c4010074802d0410344c03258a94407210210f907162a40f4600 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 572966726 1250 572965476 572965511
    0x30402040f060821090d0c080d0c03080a020a09031e05011419020903030409021215030102090105041202011e03150506040321030608100209100305010509190204030602030901 77
    0x41198440d9414142d003041040f0010400301d02c841071803000d800c03400e203104825049900c03459128952001d400c0c1404405d005030b000080c01a580c161049501c1038044680070b031030701c0c0c034000130090018502200080f8581e00035006000c0c51303865810911f4080d522541c826101070010319080401038924948078062202c01d009480c0ca80c40c0e891707014003090500d454103102303801c0c078016803181a070340002d8076000e83d0b02c080003110010f000d48482151a030340d6049a107140b002027038880300200790b2001980c844034501882224400d0005841e060701e02407900e41010508004094164140302c100d6803000c2c6d841610560010342242144c1d0700048800e1660301b60440d041c40341c2c20540c01580300b4081440041c4001c01c0c0004405006601440c070420240000c401030b0109030011130881c01014540400c040f4140c0107890044412107043c0d80c5580c1c690412000c0b01e03000d20803181d200384403030046071890480075025210a0294080580740135200d481c2c03401a40c4c000d03107641c2100c1e0341d1190116000c010700c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 572967976 1250 572966726 572966741
    0x110a06090327031211100903050406170c09041e0906050604060f0e0a0b0d05031204020112090f080f090a08070e0f010e1b04030b0a0f0f14131e0803040204 68
    0xa0701c0003900702c0e08688442000052101c004024001210505405204c041168269000305c500003480a03014030f150040548e00248240008542c40c4e80940b6072112151140310311848080700200e00340803050f010000039008551f0b11040e0800740300320310780c4144031a00840c02480e01a2101217aa8240001440211402a8031179110710303a60041c01d1105009982d54150016900b00e400b103039101590b0700003076260b029904003c1041c80300007400c81003030010890381482a4002d03280c10701c4401c40300000005a80000c64010450340c070016001c00000d00380809054400d2148910a042c205058046040203010f6001581254807500041180524480c1415480641440e0203051545020780003e011003018045011141d03e03190007044601d0403c0a540c010f54010054151a042001c1c54400a080401c600d603c2c0c0e0b4140780200e043d00c1c01d075028003c0714842100d0504d140341c0d20707481c454440c90440300f01101c01c0c043d00800f45941060b400b000041d2507004401d441e81da8105403040000300c4092 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 572969226 1250 572967976 572968037
    0x20f2d07080712031805010f06090506031e011e05041103150708060f06180f0a06090308250525030c06050d0f0501080703020f1906110a060903 63
    0x100000030005038030900741d6a0303a40c3e200321070400020082805070042c0440c40e100e0010320702003250f5002401815000070021402140040140680b20501b240903070303104a1f42d8a8040d404a1f9001724a9a00304da50702020708400b9000144010400018610200040034003160303481c2c5900c144424403900e208104940c50085009020905c20300a0007910701d10010584824410780900291081d1202d4000000c00b441c014503817075450319002212a075000c4c071603100c0c500482a482c01188070707003003840d101d100f40c4a11380ca4088105196a80c0c00c4425440501171409540895514001c0d0b42c001c00c8811000d5072081c03000d030482d0107c0520703c031104060b0f604c00b0310070350f580b0a10170008100c6600038481541c449140032a0303a0a80000140c020300504440c0103006882e110000070015000308080c0156442242e02c01c1c513030300a0b03e0400907040c007088200c01d62068801002c009103070255060b4181c0240780826220342c0700356900e070003088669001c0260046442d240c10001201c0c0c03846510021440c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 572970476 1250 572969226 572969317
    0xe060c0309010909053309040305070b18100f020906070c150926010216050607020709050f0a1d030c030703080903120705090a0f0f091d030a0c06020f 66
    0x900ca0002c40e844000220f019000144051201b20160f04070207480020000c007510f0311041381020f180c02840340d4040c0c041a141126020041950b040da02c000b2644580e00c2280140304040c0d58203000801003d400c1800c5030070590070030903000d0f5516000d000d4841d040c0a610300640c5030346081a80b031803000d41000351070300300001c240c1c1c18010000c445900c90210b41400c0311103c4d190ba43d40002a00906c143c140100308491096505170030400c001450301d1044000e60300b580c8041d036403540d820090311026114265064442e800040617152540e01903111a8445107910079110250704059066900000c0d000c0310030b810002d41d20040c15040307040c0940000706140190300e00121041c00030b44040c40a080c400410800007914081079441541c0e00b0f010b00805c0c4c00440d0215074582440c50094100c0c85454000d509120320405516015141003117403101150207540752643c09202255540030403101141d0881c0d0034003155185591880c090040564200e184040b050803d000c030700700210860280400441 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 572971726 1250 572970476 572970481
    0x3090510050403030305040c0302060706050402010207060c0818011b031116051e0a09060b0c060903070c0308130b0409020705070509100b07050a0501091a0a0510150e060c030901090905 81
    0x2607200341101c0440e07406103400035190320350b03140811207040580d00c082e5101c0000304259091141070340c4200e00030761003602111001135a500d82503503030181001d8090215082405184a5084061405011900305261a5803002e010007800300101755000800e03000a410b98685840000e010408803e881901c00310410301240b40c0302c0090b200071043c01c540d80300045100d1400d039040e2941d40c03100c006082c6441c0f0070300a0f0368a580440f42c650300305001d14081c91294801040052101004603201e56410645080415082d0349501a46900803850030f015150103607030018943c20814007a0014003d00071015a40d414035040c071515080c6260400340c441d000700b6040c801900c89404541c4120340030b031210a502c66145041071390070401490307009440ba50a0514810030001042c422010b00e420315250070049444009603a8110348003111511006a40c0403418403d10a51000042030002a8070700168624204e00c040781423900040036075461130740b001c0351031f640310740e00100ca0300f02038017006e00104160b1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 572972976 1250 572971726 572971759
    0x70b0c1e0f0304031b0816060b0a0b0703050a1206091e0e0303070c2108011701050702070927031e0503060616031710030b01061704080315120307030905 67
    0x501c40600f00400b0b211100c9001d860f2500080b40c80b10340150001d021513124910350642d0180080c041004a07440c51030144a481c20b031801d600200c0c191051034200604103001a40e0642d0940d12403980d4400744102c004001d03e400c070f201d00403031000d008141008101c200100c2d211089041c1c403d041c80800c0741c00e200c4542c103640000819a1f5000810f0710340b2603180d882600b824520610980d03103d031040f100350009242e41c96008101e090403074081d5060040400c4030031410f01d00701e0b4026034000c00180c2100e4410003680c90250081c128801043e0004001880c11f00030103401c18240d00d000b100810f00c504043c0042a0b519244030801d40150b0a10300c2c0b5524100f40010340c03d104d00d810120200c03800906900c2418800c170700740659161000c220318528180321100521184062000300c40034044c080000c00c4c020300c40e0b400688405200785203054191182e80d54098a500002c0080450074428440b440d020780d0303006203020000c600302003c0d594a00081c10f008081540580009010315400701948448 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 572974226 1250 572972976 572973007
    0xb0405040501120b22150e0d11060105090711010509011d03091c060e030c0307020a0b0406021911060f0903010b090412030504150e010b0a0801150911070b0c1e 70
    0x21a2905c0440f2420f002c00c0030004000c11000340001d03200581c642d4100c00c000b00b840d48044481c1587c1402c8803603000700140119502201348011018941043d03004100358102401c42e00d4000c403046c20031f080d42c0d2284414841c211181161280172aa4640742610000b101c41c1d0008008095808040c515041031440800d003c80d8102181e00d514403580000c0c0001c3c48900e9201581d0f00c280343c0281c0c2e5480480708001540ca4100b0305050740308000c051030025813003643c4005c940441e0401c0d0040d01640c100900d1502d82d05000e1001907c0b140a21400012955114001026100c0460503800d417200866401d042c00c481c0940c0009001360521800d020106411400c1030004200600c3c000c51240d98507d04000000da512140c0c0a0483c03c00e110041644010b402c881d0081030f040d00c9684074103039a03152070ba003a00c00d541c90880c820030a000d0144105202a0050410315001031f00c01e074a050f0303c0d1303540c020312840300b103642104404000c17402e00700c401c0204400d44103e07034144101600b00350031080c455070b4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 572975476 1250 572974226 572974231
    0x50105010e0d0209040501020705030403051510060e0913080409060e0c0403051228080402011d2407150204051f05030c0a200f070e040f030e0105130b0405040501120b 73
    0x2007451368000080c1008003d4040760301ca281d20105507603c9030782d80d1a015684840440c0501d28810741d21002035400b012250307a1408440840c4d07a4141960b44010034041c100a0241c00103094002040790b01010901e214002c0c0000c00d40070a0020301c0f00d1402c8020f031440c0390301500304401d5403004c101c02c01c0441c0c0001010412030003180c000c2903490603298883d44070b000b41d00628042c108041290b039103c05400502c036a1050b4001c1e22203940c070610200070350307404c0c40e140d4000c15885561200301444030351003880c1d001940c0e017a0040c1586400740030303111410001c400c907101010898001a0520050400002051520722518030107802001d80c40303405005030000400301c0101000208d400d180d590b2240851110041c20b00c0780e001d0310800c0c5a40c482d500d40c154140704407810b1150071130018240000c01d1645119507000350007a20800303040c1d501242c103030032840c0629041010521042ca4115550f503268001030143c3c0070300d541c1c0d0303914280030300c400d5903170590000010020343d1790418007050b61801d003180d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 572976726 1250 572975476 572975479
    0xc0307030e070b09060a180605030a0506030114070f090b0f031e010b070b06040915091209180f1401060f14030f1503071e03060b0a050109030803070306090c05030604050105010e0d02 80
    0x940700d801c89207080702c61100d040d4041880380741283c1f0005901d500300004500400d081c14080c03056642ea0b2040c10b085e50380c5500b0702c1040109400008851901c00e4521140c005054506540845c3c0c1d9000c880205070086400e8540440c400424031000ca8014a5210810410f01010340301641c500080f5501c43e000d10400034090a0014001032034036642c644c805040160b110072030034001515030a02c10000c0104030400c640300383e0380d071544001581c001c00814080b0b072100040301203202007100076400034080f455040c0550545a02c1035900360309180c05007a018000503580d08117481d81c208030050030994803440600c2c0000040003405070254102c640b07958030a007201e108820040c21440841d1030180254481160200b000d0b10f07079590300d0901d400400841e0b00544c01441030050305030800003010110b201d81c2e030101d04060307400c1000070710580c05180c1c0081c0608002510700e42d2070894906482141c080c400c001113000041144501e42489181e0140c070080c40d10a64688130480419196102180c019 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 572977976 1250 572976726 572976739
    0x140406080901150603020d0f021801030f0b2e0527030f07140a0f05010203092403010b07060c021605040f091406100b0306030d030e0a0b0c0307030e070b09 68
    0x4180341025080003544610712242403c503941c0d229402402500607401c0c9100403410502d54100c800d41ca802a9000310001040d90030700395a02c400151b0050102100c11581141c842d0804211942c41d0401e0f00500d40c032111405c1c1d42052400b44421a2a8200351460284070040c070241c03c003810707101100296016411035407210340c004e040002c2e2810a811300c02c1d48062140140c0464280841da100c0d00282d40b040d43c0640d103141d12400340d0000c404803402030b00d00690082c03000380c4940c40c1c10f492000e005444408d131503454113071520030032200b54403d8126031441032001070014100001445110f02512003072018010304c3d4004511640d9040b0140711f81849030b0b40794222441d17100050380c00b45100b541d0000c801501c0c010581c0380c0075240c103c1292070750003091140400007190120f80c41103d101d040d006014102e65501d9850540082200020524140c800c0e03200035000500c0d040b011602800800070400d84a04e85074400030182c8501c9542e840341e50f01b19000c00c010910b442001e0714441c850441c2d03807 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 572979226 1250 572977976 572977981
    0x121605090a270620090a0806041101030902130c05120610270504020423030a0803010b07150c0306140d08032406070c06020706110604020f060d06030c0807050114040608 74
    0x41c4003420138003c012211060b19180030704004000720080442d014140c940700c0003695980080ca841314022500940745040700c440c0c00c20300750303c250300c19500700d1310003000c600002244070701d58011117109080d520080340c2c000131101d4041d95814011741d441442100c041310307105403040c0020716102a20710100301120500c0b5030030b0031013604481200080c0c14040c104540b00e81d641c0e12014000d4007a8510b43c0900e9580c40c08050260030003046840c00c89803c20041851640390480700c0c4000c0d0b2080c074050300e01c80010704503440810804d00818040011039a808124a414400005003021400c03061610034503c0320b05c0040001d0568050b254403104001d10451918114486a51601c40b0403410783e9100c00001000000c100c000c00300801030700c1700340e400c031184141c4841c01030754201c110034248860b41d8000c8001034014500414002900f5030040d04050504100001110646120307030800c81f080300c5030403010700c000d0804105000090000346000e0702c114507074510f5201944603034011b500812005100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 572980476 1250 572979226 572979233
    0x10b030411010c330c030501080a030f03020d02040e0412051c0504050106080604080a140414040911220f1103220203030a08150f01020d0509121605090a27 68
    0x1d41000c00703000300c131159071495410b10b84031600c1c41084903500842d16040007180c4051092261a06807400e080041a0303031091600c040d100e0320003000780380c010141c00f00000b44980801e800540f0042c501c411034908582030a07c0c20341e685000e584441c00401c1800e01900f0555031803811503540320000544001042d8840c0d051190141c40a44c1088020788241030602c01086003141c01844403090550b280c40d01c00c44041ca1400c00b82c4113a104403030388400041d000c90760741d2805034014a84070303214411165007121240c01040e102c2d4079043e0b44d05100d81c80d2808088502041d03006043d0b9454901008002c104402c5091b0900340c04003034500b400c4001d03d141d46080c1d60b81c00d02c00d1501034a4004044030b07220a54128000c0c155201102c1424150030342c90402e50440c1482c0810900c0110160003812400a0040d4212459006140c0707903688a041403580720240d101c02e0115082080621030b48504050801c400e00910384d4003c3d09030f1200528240c803201042c0c0d03021404050541c01044030303404500d410304 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 572981726 1250 572980476 572980493
    0x12020c030412120810030b0a050c0c0106180b04060315111b1606020d140a090317070b01060c08030402100509061204140d170408120f0609010b030411010c 68
    0x20001d072420862521003200348140740a032005a20f006a850340d40c0342d03844050f03c400040c580d00c4000d00f10030740100450b040449a4000315441003140c1540b600b8604821051400d4401a41c48826140d944031345030303c41050240142001d0607410b44050150519584e1441c11000c07010840c90b946c140d0700c1094034080c4007520101c40303000e43c0054141024581303144042c0d840700b26822501d10111019000040d01c80c0c0040340341408910203842d944048101825403d049078400c0910700200f0680c41004000203082c99811070b50700d81c0d40b40e0246d8035610ba624040d00800c5061701b20005119950703800f42c00045116046941c05607065820020090501c5010f4809004800c0003c1d80080c012402122801000d041248164002c0c45e08611111151031056190246805c04100060010a00c0c58030980728440c400d402c1403280da1884e1074030a600b09503100c0035105940d020401502c2505200030b900d801e4100360301405100980c5441e6080603540c410700c804c4488062814040000003c038244101007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 572982976 1250 572981726 572981729
    0x1b010e0f0d1b0e0f04081204020307050d03020a420b06221509120206040815071103180f0a030204060801020a2d1404031e03110d12020c0304 62
    0x1003940d0700c0b4210340c0021001c40002e60144103c03e82c4900e00040f0780d4030300e15405a010b03039041030199150261b203a005003c441c000600c140d805100b642d0700019203031102c42201450758004e502504c0d00d07000f14940700510901510180300d1685010403400034100f84201480481349407010700c0101ea0040e841000081d20b07000401e02e03848030021038020350080000120340a002045d400c4100e059460b80c44540303c40c9800300042002035004d00c07051045480c203107042140d40707000528044c146965058014a0015079902903110350015805100c1e01039008400000351108190255080c1030300004c01c200640500102d080c454010710220500795202d242c80b030005103801602c00e2051360b8071440998046e40c0b01e10800ca00043d840003001004101211100a5500c1003074191046083c7d080c6048410411a080d0741c0301132501044000001810350b8500103800d480341a0030030081c511414090030440b0788808030f110503040028000100303540841c084205403c001001601c405900d4046850b50103a07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 572984226 1250 572982976 572982983
    0x2b1a041b0503150904141908160302070504020d23070c080d0f0c02011b0908060601030c200c0f0402070c05090c040b1606062c0703022a1b010e0f0d 65
    0x550303080c0410300c802246c1440700e002d1000c0403a09a00c1801014a500381c0041101a1103400c0c140300d1604980100030083c8181c13400780c4101d07480746d501e4500040890348481100c003d020380d240e00c2103070754003440302c5403000307217404844402202d02d0000009080d01d004010014103005000030500d92007045ea80c07000521a02503a4200030000d4034441c00f0303000706621000040020442c0300881d5034640301782070080c2501e4009001c2c2a46407210303c01500544007140041040c411050020303a001295150a01030616915000301500b09c0802d06200c001004130014500460040240300080380c0c02103505030480340159504001603075400c0d046c000501075600000300000380050820310340b42c1d1410703180a4483c081c400c01c00043c0c0d69100020074034041d110f803000648207081d44004401200c00022075010111742005031810b800c100c0f01010b03643c1908032242404000040300191807030304002050ba0300c03204900030010b8207860307c0082c18007002c220182e4824061940c1c2c0d015580c60f5001d5400c1450761 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 572985476 1250 572984226 572984239
    0x3021e0c01090b0105040605010c0b0702190803010e1b160c080d03051f23040f0509060702100e1b030106031a07030b0d0b0c2b1a041b050315 62
    0x985522981c0a412110710035259082074200120380e40c070341880384a084a0050f1034412a510300703640c034103060000042c0998107602500030040001c42c1c0c0031002000e818400d410450b940e6040c103040c00180c2c8800303003501c42d89199a00080b0700199001007281c0078a43c80300c560043ea03042900e480c01ca517502980080a00e0300440e80700c0d01009805070415801890481c4515450400340304c0a0892440349125205008201025030082005641300307103100c2c0c403405800420120850340b8024140c1c3c000352104000e070f6000758108201250f040c4a15404115004814081c6012414400d50f4540d6a12900203d07800341c1c041c40d1000360740075400100150303800103a0968010801d1444581d0300011643c20010074100380c1500c1c410311305401c0c20460349a101000101544a51050182c9600604240183c021011507100c40c0720380c5616000038216100c480215a668618500c04c034040122940103004508000402601415868101c50400594031780191607503100b90402c2c0c2010a4400700642000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 572986726 1250 572985476 572985487
    0xa0e070503190c0e04020102030307050a14040f031a15060901110d020a03020d020f060708040302010f0603060606030b0a0e0f0606041208070b16090603180c0909050f03040b090103021e 81
    0x2e59090440608a001e10b140c124581d03600e48880c60241c1007100c000f1f006800410011350b00328002c0000d881c0011036480c0113540380341f1810326070340c040c3e0094000c2e002014080d042002000640203030001d02c002d05201d96081414048a41010381982c4407040c1d00c22000401e8101b0a84d100c0d000c0d860380200441d04a500c00402c0d800701a468031264a003d500500902654226007800002c20300c0304024040700800c007680d5000f0048402500c040e004070219500d500c825032408406001b0300024600507000056100d107410780240c2180d5035842034034040c0d1940842003100c00c009880c00340d1301c40e6025a20010f5959040c0c002000c41c0700b140c01a1721640b62003c084014009090040c040a40c41100c881041b920740904c04050300c050081444001400c50340188000c3e442a080320760040049100c0c61805442d40c1d070750403440c9125420002800c0d03074946203d02071203801c110300448801e402c0044d503d01740c1840843c040b1031141d10328890615070002540006548500c82c801071102d031005da1640c585 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 572987976 1250 572986726 572986753
    0xa02070309270f33090c0c0f050c03011a010e0907091e090b01030b1e060c0304230604050d0b1306110a020c01110d03090c09020f0a020709060e0a0e070503 68
    0x1000ca0303034406200701c500303045105131402542060081c08405100c40c0c0202900e014005800b9208450711942004010400e101c0080c262400000c1214403d00282c82c011103400c00389803c507130a101c04281001e0810035105880e176082100b94028040980d8054502c1d0ba0300d060903103070b040f0346a00482c444008000704050082d11400c2103410303515250418014a04903a0044066035008407a06a02010301000c0344d03102544584807003001c2a0117000c0030305281c261005c060951708580d1101004101c041c20802e00300c20f6541c8008a6034804540c030b6401c00c1e0421002c603840c200c58200044c190514800401c013510004422001510750010b020b001030fa800307001c402c11a400c40580800036104855207141c0710343c0508124680380c3c1e00d92004207070004604400310080c1c0070109040c0c8051181c0c50300420a0030060004103401018a0000d546c1e5108541d0001e07c2c181c2d945d4006800d680c50175805101d9039108244090b04812454400703c1d03030048a2581e241003c0d0241d010076030510400c03800c003252 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 572989226 1250 572987976 572987981
    0x2310e1905030a0e09010f0b0c010902100207030203101b2115140306040503090409080918011503060609032a24140909181005040b0a02070309270f 65
    0x14800103a552820041121043c000d0000c828010b1f400120344080c0280201c500b4400906034091448001040074003c075004280720031503e80c00c540058129a505100303600703040040c034801c1c3c0030341c0e8000c104d2018a81c3d44c405564010110040030007d5040c09440b44014801c4880c0a0f601e032014104000c11030b001c00d0403800203407071180303019a8000700001c009034075001c1005440340343c0050103186056050004c000007000d100004031000c01c002c0c0b044166940350307005200c0d01030f40f01400c0c408441d41081403007190581202c06150402d42008000d000d40e550090340041200ea00c00d8012905002407240100400f00c52001c1c01c100512105000612448503420f071400e00c02c1d9107081d400720315520542112a030442040501c501001000441c40350b00340309042c0c40d8040c20049181c110310000071240c17414001841d0302d90340344944500034001848203030001c01e41c0180c0700c100c0461070302003240d901811a010a11074007a412a581c42d141d59110707100384104807a104581402c00070f204024021000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 572990476 1250 572989226 572989237
    0x90509010b101b0b0c1326030c070b0319052502030405010509130e070e06011b02100305090c030102040b0c070b0906040b1e0f0702310e190503 63
    0xc180032452642000764060200988103c00480400c4511540c945030240015005010709500351410000c43c02506191000b410103030034403980c0c3c0614211404015000c00b004407000d140c094204201448200900040c1c11041710103040d16261a59500702128854000000740b401000b420030040180348911310325155003401060f080080d26100040003269240a20700459020510030001200c40d0715100ca60a405024184408204400200340e82ca082002a90168aa1440d03d00c00e01546680089111104048200b50700d102030550f5000161000d000c0001002807644d2503000c6400385c54144118940840080c009641d100c0c3c2c1c0314080444d5a00c5415584c4240c028030f40003240048a02048a820000003000d6034201410180d01060561000c1720000c1358802001c000a00105c01a010b4030360621180b942ca074a60340180180304c02c462103822440c1d501c030401411800b800c1d4200d104900c4400c181080000c0c6011700c0c0035464a040303200d0b0318406034038501101ca01d00300300c0004000c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 572991726 1250 572990476 572990479
    0xc060e010507020f12180f0d0302032809090f1b020a0b090706020a1e06060b04090f050106020d050c0a1505011728020315040c050103060b16060c020304090509010b 72
    0x4200040010402e81c441c117801d1854a11444208a401059031102a0056072100c0050640c01e00781c0c5048001030307170301d0048441140542c00101d03160a0300190401c8011004410003101403852030b460b000100a040e090240400c91590780000402003441d41e0310441752218069010803400c59103500103503552000031800ca0f01400403000090310100d000c288401141c0c0e040e00100054145507451410003a01c001e2010740849443c40410040f96450160340020142d0460041c4d489061131040001c0c1d651002e5200c1100b410070004008140c0d00040c089803c000314500940c0301c81181102508042900c54080e190354480101e940c04410740d980514100c42d413100031100481030050000d601d50b0030481003801c0141600000d01300e45000f8012140c030907840282a2900050101145400e032802a6016541212284004c0c0140d517003612a120180c010f0b000142c2c10085415070784410078498510050080303031203a243c0340032a40204155070240c01d005906015516042c5529802001c5000e90b00307 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 572992976 1250 572991726 572991733
    0xe1f0806090c06070c030b04030507050613150b01080a05061818010e0a320313080601090614041d030c060402090c090d2006070c15110615010c060e01050702 69
    0xc60035443c21404907032000d03611000c00d154561454403402001500140180c080c40002c001040c001401070003440e200c0c2104c146108819521070501c11140c900c3c0c2e280080002d4a0007880124070b81e0000001c1398405440f8070042803903911030010402400425150104164495080c02020061181c40d821040c188100800000220040643c2da03240c1504014145060802a800b0b8150401390564841800c2182c4110144640b061852a40e4444c000303541c5012038154090003092424814140101110746003440aa8141f480c1c42410120300c0032950721603561480c0445848540070f240400440c4214181c0c1d4a900502d12000d45412046404903c15a051000200804d01500949600c2c03100034154407201c001d16610503111745200d29030040c001e811840c12000c0d5981d40c400500c4114483c03d61401200e207010028130861105903000803c0c042169112419950006450b40e40709558401da901020100b10050b101070048d028060a603a0504a40014200054100714040d81e03059084 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 572994226 1250 572992976 572992993
    0x60609090a08041406040e09030d060b091e0a08150a0506010c080d0b0a08060109090b0c1801210614010807021516021e011e0603020108010e1f080609 66
    0x2101e4461240c948020803801c800c1c00140b0a07004080720124420b400505010301e09601c0d407149a241210840308210583c1c800619007008a515015040c010324140988a0a00032030300300280c890844082d0007450f58403409142c0c0003a50360203143d24018041d01040d00c681c0c1c0040700c0c40c0c280a0104030303150041a8144400710318954842c14045001130340068405050801021609000d0003419410310380c403d00d004004155030340244203841c02404400c100190501da5481c040d048410000c10400c0800018000003185100010051a44a109181905490300c0880130241d07040351a600c40c141143c5403a0000c1440a0244070103070690500341c0715902d0030360f03400c42c04907900c0b00c0d10070313081282c01c8030180030841c20058240c082030402050b0040d5080c82c07582c40c2041149a40f85440580e01e40c0d11000102c0303a1207500b00e10b14041074002801030040c281150006004c01c0818403c004040040f400001c1d0540060510800b0001c0481c5250700b40f9666500007958884040c0e5200b0154000c8181 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 572995476 1250 572994226 572994241
    0x8180109061409060702130e0d0f0201061202190b0708180906150a090306021206011704200a0314010b0103150e0109020904020f0406030905071211130204080d02060609 74
    0x75511201d07920782e4924035201240d41805040d4000800483e04880e004e400000503240c07a00840145441810040241022002001b4920b04582c041c00c000d5901d00103060000305031036040140580d4042e14140c4140c1400908181540c626a010780b50040c00450418100f18480c0010800504482d0401458100310010410400ea00741c40d1302c0ea1040c00c80d000b042403c23038403602610041c2c05508100518075070365214181664446481d42c0e10b1014a00208161503030400218024007903c08000c944c1c1e0f2500c1c1d07481f4450140300541110140b161000740620355510341036490091903004100007038801d0500840c501030182c2015147c08a414098140200c0001d05001e10803641c0d0240f00310003d910b00340400f07000f9840500c0454005408001160503400c00100500086c2100e940010300c488a5060003800c00d20385401158812584a4101010840b00c1ca0b04c1c05121104595102010420501c1c1100074441d039400f40a0303a0148034002c40032180c000c036202d40b083c3c8094510b0f2445035200c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 572996726 1250 572995476 572995487
    0x1c020f01051209064204180308010f06030207080a0813150e1e0c090a0b0405040b0702060703150302040b1305010b0a09080a050604120903050a06020d0b040e0601061107030818010906 80
    0x301c0b02c0174241c070b00c10a8241d4005c41025410038004004d0300c00a120305e0640780840c4010791400c1e040e4042101800104404801030020070010010384c58218105070955440d2052307841101c03000420449040040703400d10304d040f124007600740e074050039071104c0c100c2d45414030019024103040944503001e809004184201008201820021301201030008002140200b124003000544030b41812540c07186c030001d51352158800c4070701490160740544114038149000901d004401000b00c1d0825040860a019481c40141c3d101c058035070407500858000c0719200030845401860b1a6404000c3c2880000240700410400414100c016030f5101c298541c0c884050643d110806040100b9691040d070015000c50f031003c0540c109402030b0315002441958a8540500d0030f054403a0590341181c0c00100ca050400103407140c242c0007042958280460901c18099039280c00051180e94203000d0343c900c20f0050740c00140041409141d1200d070b4152a0400b031038001c0c52403003c80e024070740072074158140414841d00030b5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 572997976 1250 572996726 572996791
    0xc1504060c111c170c120703060b04090b0607060906020c0c0109080312060a080703120806180105151216091e0b07030509060304120801051c020f0105120906 69
    0x54000c19140a80c0d0320162241c14603c21220100007108000d0314544079242c482c203004034946165070361039581c2c2400810244c40050240001c0c5858480c0411183d0040403d0300d08460180100095100a0350b01103405440342050040001e031078402c1020410107991b001c0c08003001c4800403541d00703001c2c820042d140759040380036880050744203000c5100194020141c03070f584000080c00d2000042e0b07075203a250b881c0040c40d420448410340020300c00e03404654080c2c01341b0b0344440110f458400000120700b14240c0d082040c02803d02842c0690800800e80002c002100c2e80481d0b61134402a851601c04492011200e49108810015680c9030000039000303010410804039030112800190036a00e0100d080e1140d80c040c074000c4003400402d200c01d4006030f0750b03240503600c80c1d4040d210007080c001c08020024a5004160002e078440e4600d650401c0e2f0503803111100150699060b14440000f03000040103881c0c42c001d8a00314510005c01c0c2c03080029517580070500034000c004440700440d420702c07095245a181501c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 572999226 1250 572997976 572998007
    0x8060610080f0612070e0121200103150e0604050c09010207150e28091b12020f0c0307050c040b09071b1403090a0f0503210c1504060c 59
    0x300c021881040501c5480b80d0004030050500c1d04000d1031428184c2410440e501134003c41951400420034540a001141006082d200507107526004980da1f41a0b45503240120303044040d41d0b5a800c19483e402a8092013552494042c1c10f5595540e40850041d0700100701d40c04c40c0140e0505000c1000d6068150580b828810140c000d01080c5040064050f08100c075001d101003080b101d0116220b180d1124481007101c606200c0a5041e00100e500c40d2010055480d0f1010b4905132030104680d0101c084410f20f18100c11003480c200301030408418040c000b03405601041003036000b000601e004030080c0080242105441481502d4444e203038481084111001420540c3d001607112001501c003034803480602c11110f03500f284254201409884158900d02c4042c03c072545030b0310008142d80c1e189810040d050040c074128800c282170381d081201103070302e03540d00d021034505419841080341c84180e000030694000304903a0342110a020500c50b0f11448052040d10140c0f851440e1400c40035015208a00580b4803000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 573000476 1250 572999226 572999237
    0x8101a0c070824040812040b04060b0f2116080601050117090a12120c021b121005090a0602030a0203011403030c1b0109030b040b0601170112030e01260108060610 71
    0x70280e14169070f100051040342c15440400c00040c0c0c80780160034407401030b8010801036a40340f41c1480d01004680300f008074544500309818820103280c0d100d2460440c5180b0301d038078080d02100c11107d118581101c1d582e0034410418001c0b404500c0750400249035040380c1003642c0b6001d002d10200401e11841c581a6140341050b04419000c50110342007148401b4062140d240c54110324003014145d03c2107400d00c132220303001038000118003000d5503000380c9225199182220710788410040384000c25650108294110b08481e240e0b40010021842445007402454210805564a181c4080844000e500901443d44440c03e203240046080c24000165414244000e00802c3c07070300358115801c191078820700c002904110031081e001c40000c407a10030940c09644250040b4950b8205400054402041015441200584c100041014201c0c0d405212a01c907014203080d841100e4800c0101c40000c04800e441035804400750413250440746e844100b904a80c4e48038250f480645822041202a120044aa400044 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 573001726 1250 573000476 573000523
    0x1b120304031e141c0203160801050103020a02031b03040e09010606090f05100327030309060e030a0903080c030403141f0b030a15150e0406050106020a1208101a0c0708 73
    0x484078018102154070742103103e0036010150448045e84d208580d00e800c0e0407441c50148510f0b03504215107a01418003400c080d4101884100020b560380607890001e0b4603001040401c0d487e818080c030072540602440071000c2c103986007004050303000c0c15091154a0014862800000300000300d00c0d404016200024240036044003085400c43c0039024109041c2d0b0000c0e444000c0310b00507a1030055400d070302e230f02c2600c1c00701c0c0c18030140c1805e07c22103001e00c210f000a608100007150f0308591003240031064a07400b1204548401c0004001c1e480d45c061500028200010050407d50003800022040c1107400c9103a810207044d810303030b1009030075556070002171030305540070350705400016010b803401c07011650100000140d4001c03170303058801c840542d541c05800c0f81c811000a000030b114081c051b5034090070b4540028001000c40da40e825003071040d8144100100918032000c03d401d40303100d82c1c0c614018045440900c00241d0031058800b100d500c01a03100720345101d15035002540311004280883e5003400c884007801c864 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 573002976 1250 573001726 573001757
    0xf08070807020708030d0f1a1804030c05011a1f050a120f05010b1c090b06040c0c0c0305060a0c03051501110304030c1e1202151b120304031e 62
    0x4050708640a40c025440d02003482d40c020070140040c00d83d000e0f00400e100818036155002c5990751036104082001c00d02d0040b4407912002c180440c005142c1405100700d951f2400d044449101c2400010110350a0510400c03034120b08425000201c4021280c0d40d058441e041c222662081d000b8104602003003050004003d160300078542e2071041c040300306001c2541d40254100b0412510b098100e084980404900d500c02100400c200030700412282c1740410a40703006032580806600020055445651143c0000d1b544030311618807901c1442c0e02144c482d41ca25103901d0056210901101e0003c805480c109500e80d185100780103035030041650040c000000d0000341d00458102d001e800b40c0e400740e03200401c400800503c1c4040f5000040c410002d20121101441d00a05401003003640003802d0002c5036601d03080542c1c0c07424041c0080c810010b031526a03d150410140c60300344110001002580544046501402d50fa40001c0d48a68880d580e0004450b110410140e178000c244484000041e5200303645002c41c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 573004226 1250 573002976 573002987
    0x1090b0f030a050f15221e0c110a08070828020f0312010b090d05030f1c020a0203121009180519030503010605031009060b07020a0f060c1b080d09060f0f0807 69
    0x786d41608910040303621001301102698031914800202031100200182c0e80e0b0300c00d02c40d11411400c40d180610300004807071030156844240c0f6402518003c3e000581c80100040034007140e09581e02100042c1c641202482d50b61141c0700082181001f602415241304000b0b803000c400c4403d50511003800081a03402c03d6a807a1068006038030441e048880031000c00e0100d44200060084d4010040d5070b6035071042008199000324201ca80301c803e1490040c0840241190007009880024403112030b401030760350301c0e000410802c000f240d000c110f9a600e01101c0c0080c0075100161029158040d100310791038282c041c0404400080d1500002d00058014001031040038401d070006e54112054022004603036440c0c03459541160255404140201c174001207203804c60030a00c1d00c9500400703020030843c401c14546a00549881010100101440215090b031180c1c545030f5800c4401a000c0081101e0710700c0d00b00840600284054003c2034046100d51443c200000d224500c503083c98101c641d10f2080301e4481740003e071503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 573005476 1250 573004226 573004249
    0x50910020d0e0a0f030e040606050a0f020a0605130b010e0c0901080408091c1203060b0a0507031205070c05060907270b12070f08030c030a05070201090b0f030a050f15 73
    0x40a0b81c40b100d00e09844a02000711010305030013000c5108440d6100c1c03401800d40c0c84142803c2c0c0c0a141480c504104103608482690010400e5040c11130107910000012802d002074103400900282c6040c2c1401800c07507a1841244e84a84a0013074143c0030b989a00b407201142000301c3e00b141400600704050030a55204000c05904039200361005410401e02c040001c401d0720404100380e008440f60b81030b050a00400c05101c84078045a81820480c45040489030780452003030781e40d183c00707200000500b5420507210b45202d0034035074404001000103060180c0b000707105004e002000e0310f0921400c00032500303001000c902c060898282c20b00c110900900c17840144610942005101d0405589403100e001549507801160100c10340740020b0310485091101d40c0344104030980101d0b68039402481240700c0c0309000400c544a02425041407904c3e02d0152004035042100c0d0b4018000240002c00d046199140b808003460003404800814850750756011204003244604031002086c05c05030064444440c01c0c104071040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 573006726 1250 573005476 573005497
    0x31204110a090e0d08060d02010f0f050c01050a1a0603100504110424020601120b010e09161202010f0e1804080c0d050304050c09010303090b03130c030f0c0905091002 73
    0x101159584051412034110f040414500c2e045a8414200035134040320302c580c000401c0f20700340c405480e0390300000c0c80180403012080600440e100d5091010380540f05852007008a0402400705143c0301c10044082e01d40c014181e035141d44039032001c650520781303402942c1c82002d00c0d0000301c521500e00002c1001920111211a545100800000c98400007414070000001e81101044050241c0c4400091809905130700a0891780c1da02c61044000a01c001204e504442c800383c0d03600110b44591640310700b8045000040d6407103001404000401d02c0c004049a41014007d03200ea00001081c0d04040d500b41c82c0c00c00795a54840c450000c40c130034108200401c9a04907000309060342c10102060301c0c0764a010074896000010440c08010801040000c103c0c40070707081c20585001d441c952466501500c041c129020b024145140400015100700c80c940d03801603002c2d006040804901c1d600d080a02c00e154600c03400b40c5005048607408287e040890103158060520a030081480359000165900250040d07030554 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 573007976 1250 573006726 573006739
    0x3081902040506030a021b120406031d06071e0509130905010f02030a02090f2b060e0d0503010e09010c02100902210303010810090c0306090f020a0b041703120411 71
    0x4150b40d207800d800355104149842c2d0050361852201c4c042c4028403510318050019501520014002c1144401503400f145c03542d0401080b0028401a2160061030907604982c0f2031180303204000255030b0020094070a0440c0f41d01c0e0b41108000e40000310741d03c1c89101900f9030031428915000d00034176481da0280d00d10f03034000e10000a00e0708560b5824410f0380c0c4140c518008003500803032000c4062820b080038110158040b07410498901c0a40080c101c1e1001d9080c446504416410640050183d1504900d0032001d864080c3c981000552001030b20301d030400e004601000c1c0c0d1880010720b03118014417442c02d51200c150000c100461402d540b09000c1c15002c41c08130b81100303050380c0c0302d21900d188000000008411401a5880c1d47c109440c0706d1500d0820020202c503541000440c0012524502c40b0106803604000b001c00c008c3e03214100710080b05140c40c00290014031030000050b40c40e070400050001d451000d04541505422a20203551300c0c010b843c44140311002110101d000501c052290045100025240 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 573009226 1250 573007976 573007979
    0x190522052b050106060905040b0301021207571112010b12100b010c11090c160b040c0501020a0c0e10050303070c05030606120a030305180d020c030f0a0308190204 71
    0x4071421343d05280c0c0310002151007404148802d29050280c00c2d9171070002c0e00214204990240c0c85e1003903002c098a03000600c0028200c42c0c10000c0c031716035035010081107100b4450311107075200c48803200d42e41d072140480b54031030003190784803084105000c0030034a43e50800343d00c21401007840c040001501c402800c001d141c0d9030703c013020360950310b035130030a180c10742c1042020b4003071612000048001c1c4d500750b0404034100f000e800140b90020350b0407030401d144084159462100d540c0c40c070781205c0305885248011002d618043c2c80c03000030425460800c9208034401c0c0c4e8682a0a0382d18001a640d502c60400010035000040905218100c03130714113526400141c90081e00c00f96a510408070341180c1c0700803025103080006c41d500744460b0508100c842c1d04254141d030800c1c00c2c807104d852000d48688040e6002020141ca601c04900324601113171540524a14001c160b64040040081c003a40d170352038036010b0300d009010710f01841800341001305038a5983d54240e11220265500d00e1a511456070141114921840d8240030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 573010476 1250 573009226 573009233
    0x1e0a050411040f1505040b1e0304060207151a0f0d0b09060103050105061509010c05011d0c03060c0a0e0108040f060908030702190c050f06190522052b 66
    0x191149818065503120380e964240740d90282c0c1d8010580103449100b043d520713029040ca0740b110855044405504140c0d803500b20113400000100d2629110246070300002c01404144051036000b040000e105001c200b841403902071008064036501e0b11080c90f8040d1640b020055401e00440803208144020310f41c0e0350b1240d55039101103181c0c10984001109501140050040080034482c4607005002140c00b01000d41c01030b039140c080340c0715450a050411140d0007010f02006002d4011845c002c00196006400f114107e000550700c03442c10b90f00901c01d108003404110761000da1700c06c59500060b56650211118910b0b0015510004041c10440301a106940c182011442d02c0c8072300781100344035818035580c2e820082c07802460030600e48800d6080341c44525095000880a01a020072a00d0035030b00b9081902460000030034500852011a407c41c0301c5000e40040d039a480001461111000c100601c0040142002c030480f030038460144540048401440c21091821200176046141f000b070780500c42941d140e42c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 573011726 1250 573010476 573010481
    0xf1e120908070506040c080f1911090a0b0310050c0d0e0f01020307020a1403090d061815050106171e0c0c0d03050402121f0506120d020703201e0a0504 66
    0x208142c0743d6411400c240010400e80c00448030050401c20010110421000c281a890701e0840000e00c1000701340740422000c000c00700004001c1420002c02c04c41161030408900e4000c0d01c1030011180c40b901035543c400000c08445c1c400c02d4041c0f8001c42400c0d041510b003002c10001041c2030880300001d441800d04c003c0b81c5071424001140700b00c0042d4041c107040c84407803030b2010040c1c5509201a1650b00240917041d085d446190722840070903006140800c0c200f425102c0303070701f042c003450002406000098060040c03550041c0c000c0b6040710300c940c2d14103000c40a0128120080101910245d85052000c4040d0309402c00031540f05404c03415035a600ba1800424580b000e2400c40c4060032800800d840358104400d514000d1451041210740401414480100201450b040c50b171100c8a076003841c2d9502c0101d1282d881d081d01d141c851410000c00c89065598102010350341e01c01030b1200701c5840030705402408050415110f04c000002001d091300606000380c0301c0e030b0200324104411160b04800700d040b000900703039101e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 573012976 1250 573011726 573011737
    0xb0a03061203180609030b060108100b12100602010903050d0203070201020d060806041202032505070503010518010c020a0c15030b1009062d0807031b09060f1e120908 73
    0xa44921a441d000c6440c9000c0f00c05107075004000b03200345070f1410408150503814542e886002423078946607039a07030300301b03041c06812094200b5002c42c2804200d0005010141c20200c0c026516540e10000705513562208a01707079044400300500141c000d000c035a4041410380c000d11f4000c1d13010f000243c10140180030300710881e01c0359440244140d100e0703000d0100380003144403204264401c40c4060b500e04110b441e8450003102c2314911b500c60b068121400f403010310100384840406040c0040007404242090b50720780f111042080e9000200394030740076000c0d0f003e600000d40c2040c040d5200d200a81d0080c5000d101181c0015100070402c1490b8450ba903444442e034038020001112905038484000c21350030508014805d03030200034010310551031060700c807850500106020007a2501741c600b5101a030b60f28202100503204001c51072003020030029920b0001900008944d040d102d26030b580240b40429040c00b11001c0050020b80da001092141001040511501c040040110884004034040186a44900c2c185c0e01030b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 573014226 1250 573012976 573012983
    0x5090d081021020103050a0b010813020d06050a06030203240c090303190f0905010e0609040b010c060c081b180910030512042d14010c02030d0c060c020f070b0a030612 73
    0x8040d0b480440d81c00d881001c0c1c2000d00030313204000300400c03600041c0036203801401c01507105001520f21421940c5546045503815400b103002e00c000d003413600d00c0102a0400d0b0204a04c81c2c0194640d0680301c02d144242541204450700385400300c0e0f00c2d5040e03a548643d120086158243c0420001c802003171080b0700d03017032031001c1049d07482c489010900400205844003541000d41008030065802026955490648034001e004a500280c0f060341d450043e100100380d60402030045003451414114903400184140c81803c980c0c410f07030181841e46500090310b20900303c0c0065005a1540c0c1c050403400c064502d150b01c004802c4115846036120340301c1c00d240019000c10b2030450000040c00340000880c901c04910040420084034118006000002c49072a0181c020600003000c5400d0702b2415178810151480107540103400e8032000664480000c21700045100c0560b910b50600d40d140c2c0d40d4a10014a225805541c00007030302c4403508203240d050f40e03a0301c5600b60300105a20384001048150b0385d0309403400c50503c0b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 573015476 1250 573014226 573014279
    0x20f0a02090a181a0109110d020a0201060f1e050609060d1d0312160504030c030321061401020d081e040213240902030606031810020c030d0605030105090d0810 70
    0xb200c880013140e940140c10407002542081c0307082c11760030740c07080607513021100071040541c44016191089006204941c802c801c40c283d00000050815121950040500c0803c26007008642d101c000384105413294070340c0ba540004003008075801104503640024800007100354a110007203107442c0da044c030b940c00c03514814a045410000340038404403c80c0814000c00380900b0014141840c5803510302d10b0955a200c040e0500ca007894041d240e00d80c20320540c0340c200950101c100010b6842c0d080503040c0340384c80140706000d8484d41035101030041c0a4420240724a1803110115004c4a12560010240001400403600300d20082004030000d4110301401030160b01c401002c6040201c51741d441002c061003070780440c200380e204005001151b00c6020440354001c045840e41c041e910200401540340c400d2040c0c0d941d15880c8003280341005104088001d0000c034001c14400d100107521b0310100f5080321001d90742195141d000442d200a800e000c1d402c0f4030b52082e0382d10581002d250342c5800d0900d4802403901c91810580 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 573016726 1250 573015476 573015503
    0x9040f120e010809120304080a09030f03030c0e0108090d0c0501330e090d0302090105070b10050f0901050d06090503190f08150a03110f03121306020f0a02090a18 71
    0x141c2c00f030b1a0592103203040008151a240c01c501210440c800a07101400000000508500250103a05c40f00000d644c0b051201c0014102c904000740189844400c0c403000074803800b21041c4961141d0704441c002c007013030009084012904501603481c1802101c04a0f50355480d401144190b8030078024100180303802c880340c0c08051022580c4021096440d802401c0014101006e211444000143c00030b5181043d040c01a0740e005003e00507195030003182030040800d52008100051000c0c8100b81c0301c00c8640c255000100c0300c50110820090280074000c09802045440d410070115800780c02c20070301c4a001c1c03401e07246070004018000481d200c9440108012a1485180600c0382d540300c070255a200b00904108001d00d6486d0001a40d4115075100160699640151409883d6600d002c14080a00005c04079001d0b0500e07540e008070641c10043e401c401e5401c1a1100091386030000c180c840010329003c02500807405550700700b003a011381c094010711013039a0b01c01c2c4002564850903028017074140100300258109 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 573017976 1250 573016726 573016729
    0xa03090c03121407050c0405060f040e1513020114070809090903091903030e01080c04080f0c1201111c02070b09010f06090b01020703020105030c0f0f0c070609050f09040f120e 77
    0x214503d1092a508000030071140020030004103405004000484020030309884850006000043d40d882d8154010701e030044580c096440011101141c400b40d05022080b59140180c0400e20071100c040a400b14a101016100a00c501d80040206502c5039040500703080000300811031485085680d0ba060b07910008146101d45440081000111011203881c003c0d0703400c640c6c0042c42d040804500605004075030000c203182000d00400d0328003421a48040341c1c0010200007009a842244110450060a2a81f5038203404041030050050308840407a06514200401e0801c00d040240d0082208038107034244044000501451300c414000d1003244008508000041d188800703d0b00da03030b4403d20480c0d02c2d22040d140c80d0390300840c0328800c0f1307902400e116441c0c1e6100ca00982e070340d1046030b10f95140d0003000681d03008254414000b03044684810821507403010748880d4107840400050007216802642140d086847e45072130361090f580a0720070840744104501c0c981d6920f64641580f40c2c504042401801e05419a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 573019226 1250 573017976 573017987
    0x22020403290a05060a030b060d02060a0e0a090c09060c14060112030e0414010b0a02160609060210020a02030711060c01051503150f070e190e0709090c0e04020a03090c0312 75
    0x1c42c100c0700d030402c90707410000300003581840c040c4002406000c0410019020f070f510314091041041d0003916403562200e5465004001f26200b01d20b07603111702082c01e0041920070b82c504c42c4454500c210b45403201c2c1d0b1410440103840044503448112041c261007518210080c4e420b0140382e00030300401240328940616890042c0c0705800c20b029460082d454201c900400c00c2c2100141411600000c0800341d40f410300c0702c4100d00f488440001e259a603080418001240c541c8485040100d400341c2d400c0c1c84e0b0548080141034180e125907800c03540142d106004440203d8090700415084150003066a13281c80361003996142500c40c100d079141c03914051500c00c019181024007820f03044e034066148840861a10904103035140344041c08442c200402506120001d40345c5441c2c0304083c40030f2400c456002c982d56102c2c0e50004400700d076590001804080d001a6020113409a9a05407030551101564035a00c3d0003484002d42124424a04040c0c1f00c0b6140d40200e5954a0710902850007001010b50311044240040c04 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 573020476 1250 573019226 573019231
    0xd3f060306020d05070219081b0303090f0c03030a090e060a24020f070302061204110303030c2101050f040c020102040906080102040518060105040306090309030212060702010c09052202040329 84
    0x6d6400880c0011041c080d074444811502d50f00043c00ca494040c0f4116131126038401c044110340740c1c4000001c0c01142d590020f501030802c803004085034003031402e54042c90340301d0191418400c0802c004000c140481ca0720000305981c815409044081540c1d0f841d13640c1d605080d40ea0203021495848044aa1b4045505110340030f0450314150041041c2881c1d58046006481038a84c0d140d90f09002d400480c08020445d450100382d554020110b0f030b01ca0618209915465000d00402100308080b841c101c2e64400403461b15030b040b200000c01e100b42c4564203805000103060458140e008555003000007158100751071194a02800d00d100005889034105014041044098954696004900740070410310381e81c8401201d054a500c1000400d92000d035140907a10a052a04029840a003115000244034000503150b48603c40300d0b402403014004a450948080c407050003a00d40003800c4200c00c0890308201c048280048030030b813000500d81a540c1d00c40d820540d1020944078150028101c048600c407447d0b40c00985c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 573021582 1106 573020476 573020491
    0x121a06070b070905040c120510150e24030402120c0603191b080705130b040306050106020d1107030213140a05090d3f060306020d05 58
    0x44054002c40d03486002a081040002e0345203010301650512640c961512214030111305800e00250100408c254a2409900400118041100f03992031001000740d490380801d20101c41000396051642405954548014481d003200600f600100ca07002030741201c0105c504401828a9420300100d0403802e41d000c1000b004000c1408490300c890f411030201d42d881004000c080a10204d1082207184d403100004185000261500b40607070010283d006c40b01c4c948662031551840a02c807560301c07580045811903114001046003c1e01000f03140100358890405003000240b4070b1000d541c13600c0038070019200b205174084e43d54404086070b1125400404034407035403541380360115082c40648425100c0e450a4030a16080041d02441800d019886020545a1610302c82407400905145000280c030310b030555100701c4007000300700c603d4070035080114810403016840c0c4074002e55030011200001c0600 = true := by decide +kernel

theorem cover : BRFrame.Cov 572841726 573021582 := by
  have h0 := BRFrame.cov_init 572841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 572841726 ≤ n) (h2 : n < 573021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
