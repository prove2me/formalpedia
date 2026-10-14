-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0400
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:37:03.748832+00:00
-- url     : https://prove2.me/submissions/ce6bd765-45d8-4931-9005-082e6a2d0846

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 71762592 ≤ n < 71942448 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 71763842 1250 71762592 71762651
    0x8030c0c040c2c010309080d0b01080708090c0d0215070b010315060501081803090a060e1504060e060903010e0304030803010f0b0702130903020f03030c04170607050405011103041d04060f 82
    0x400c0000c0f00140c2c0500b9440401501d0600b021034034a42e01c01c05900054001d0340240e9070504c203681d4010040d03070f1040b0140d0301c814203540584100310007824500149c818060009040b414030a5110369034040a5018442c2210f1800400c001001082001c501c40900003814550038030520b402e10f00000c0460500805240507044106a01c0c4503524007032040720940b000140040322401d40f07a010240c0300d0022510894021035424440d0106070b040a402d42d401e864050b5101c1000119101c10030990b034015400c12540b655807840761300300410302000108000c503c501721a91700c0350724105020140d21295445154600c0c803c010020050395a6500f40111041040c070014607405242401c07454840c40c03401c0fa40161100000744564410210003503c1103c1c560005200c0b2034281d40f956a031915001d0b20f124010500600c01400f40f580102403084c140040e0300c0803a400d056070f5050203064120051100b01c12000d959080c4000c0c032110340520b8900000305281444003441012801080e9100154135680 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 71765092 1250 71763842 71763917
    0x3120910031506080f070206010e0610021006090b100201021207080901020904090501360605091c1e0219120c0512131502030708031008030c0c040c 65
    0x51590182d844405940440074400b020240c031081c010b0046541030310600046030480000a503c5480090a64184c0c0c400c0301c00c0284075283c000030b20164801c4074140ca000d50007084484000150548a60801840743c101c0104040040c070050049480c0f00c03064a100316401004440d09030b050702c23400c1c0340d085812460008125507c00c100c030b034024002c0d1030856502c00d00f01b19491060100540240003100081407204c044101140341c1c014020004104c02510021102d034040042151644060f90068190013540c0406c07110071100c6208040241d020404119030a0580c603035011112080c040f88246030008220122148126403004036200000030301060150381b4500d44944221034018445038014101c8400c50340300c4a200c00700d85c1125941a005950b40100001c1c07201c507411040ba1440c00342c8e000341d8503000c107585420581e40d00c028070308031401502c5400050070b50802c1005240f40094800600303002440f030030400060b2006104100d04100c000d01c1e600080340c41004030f0040701400502e2551 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 71766342 1250 71765092 71765119
    0x20d0e0112021215040b2b02010504081903021b010c1119270203040210080406090b0c1207050a02070e04050c06031311030607120c0e0901090f0605031209 68
    0x3020703228a103441c2100e000b103e0148031510780416034012002c00202d5040c4600c40f00001400a110660104010441d02a89203801c0d0301007286d00d07a10b420f0b030061410340d00d800d495901103807402d545080e80300d000c003513911a043c083c141e06200c0d18407c4109030400303502c0d00780c0160008040d0410300c500607111601c83c030122002980c0d00c01480300350075030031046120a0341d0746203074004651445000c002250290b07000d40c0c4106000728401c4038410380d40102500d0b1a089403100443d46242c0051088541560b901301c2e42f004034107160a810700c02c0f490322580541d91004000302c0d841c8404050802414018144002c4480039004a80001680c8900b4102c4070943d407641019032924042e550a00d4008800000744112417044e4543c50b041d081c002c1902c0c0d00c420b007041e42132640da020700311540000225140c401c0c048140d100c1e000250411220b01e4840c0380f0120f440d001591828086c0c1c01041c40544d20304052950802ca07000c1c0a0090104030054082040003059a0003988103403010319200d41030311500309 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 71767592 1250 71766342 71766377
    0x506070504210b010e0703240807080102071a0a060803040b0a020c0301090b0a090c180e070b0a05030f07020c030105070504050307081207080f04080307051f0203040c03080904020d050906070906020d0e01 89
    0x84423024a80c4500344810104900c545401180c0380118504d074060b110700416500d5050085502c060341c040c100140f02c9154545015070079001908030009642c440c040040c031100108040c0010b4100204c40e940e0300ca46a0502034604040750350054001e90510000e0408a40354515150b84015030107030204075850180f82001d031462041c0c0010b4400200945003440c03120382d590000780221101c3c0b003100c07000b540760b0600c8641d50007514007042c0010300420000d00030f000807411380d40d00031100d40116505802008002401d584e01240d051000900208040005140400c00300c170040001c40042c2102d5800c070070f0704407203500c030b0020301801c50a0b0000d1000e500030280401c48008160010035a61a2038051811646500c0c4481c2d030180343d0808a90341e54811651031007145e01903603000c4440182145185d6175030f1850780060718a10350140e0300384100b911400d607030300840d4800d5410001070000d03490540300240180384203820800c2194002c0c08030810850300100400d198000c06d080400342c00da0340f2a0300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 71768842 1250 71767592 71767601
    0x60c09060d05090609012301030f030e030312060405011a0f090a0f06090305100c05070b06040b1309201311040909210e0d0b130506070504210b010e0703 67
    0x40e41c254602d0301c002c010f40414041003d5001e2441200240106424900d444200c201c4005415000c03200c4a001080001c0768018403072507641c40f9003048541c0e02d0055001a041d50031014010100010b60420005149003620503140540f1142c000c0d60410040d05242c00700078010300c20151080940029902081c3d582c0081c2030f402803800404440902d610381000401600b01031004841c81d00c50071108541d480100d0240110460040d5501820b01080d52034858a42001802c0550080d9a82e41900019201c1d4400a8002c140c811808504001d05103401d050340f4901201c041090185021104c0050340c0f100e00c1d112605407003410110300e41450207500201407245038412080c4d6843c0c001c10f201040880500b44001400c401d248081c0449200720070f030b035400c4201103059400041744c1c94040005035002c01041e080407019130070080e5200c40c1c2d6a02440c02000307680f03442c049400030404016003803401c00d2400410070072020030340580e01d540c2c0c1c2c4c8130542c003018007a110060108000084007a4445e602 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 71770092 1250 71768842 71768857
    0x21804020c030712020f011a0d060c110d0e01020f120405060c01020f070309170f0d0f0513060309200306040209090c0901060e12160e060613080309011d0102060c0906 73
    0x44080781a01c440038003a43e140d0850152608179400d0020030703880c2310380d4400e03450381807480501aa1606911595400001d200943d112070500000c000c0c8510031010400044101500d25140d56425501c0d0500180c0f900702e04082d03451042d4040b18825a44860f6441580c0849009503007017619151003100c50343c003900580d012007035040703804030f140f0040c0355000c2100f400301c440300010188241060388082d602d4610014181034aa1302030108403d481d07200f000c80c0e5007103502616144d410803200c020301c94010611a400040000e4840700030205100800a03c2450ba80c0400840c80c4016032120200340c442d0300080000c1e200b80b0710b50000400c800720a00003110202002065000c0960315420701030010791504c0d46407405801031051181d605003002400309904844441800f035032501c1c184090f440c5081c0104075a42100d030900004841d000c0c0d80021401400d007031000307151228203a10004010401c0e01a0881881158003000b080300d90f008641181c020103028181c40da60700c00040400d22038404c1d40c9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 71771342 1250 71770092 71770103
    0x513021b010f0515040902030d0f2115060503090d0c0c091407030f020f041202181501140f120705040b070b040b100806150109031709010e04021804020c0307 69
    0x22001154941983c0042c1c4103080300710440d2261031a807818001103130ba02800003505540035110400c0481d010b50f5954600c00c0251607c280201d03a00341d4841001071031480d0700340c0003d480301e501020140072200306a000d80301d00c0c680a401c61905c40346282e40d44170078481d8202403001400b8010700344050f0002100140503601d90a0040000d180400a126501110602e0019140c4542c40f141c01140f402126900c41c8074074001030606050108203501c410307400004a03480030300100743e8070030740c250950580d00c03581c0b24203040c140c0140208005440542c6030b113000b180411040148014000d00d02050360342d0104110424019507586007000e0750b0510403900300505031f080200c2c0300b80420540c0200340d0b1096100b8a844030301c03601e80b01c0c1640200381150164020903081000052903e902251351400000030500d071400d00596681c4074200c80d0404c80200d004403c10014a070001544c008401c076106010035501140b402c2240a403003005040754101840c805d07500000c02200508040064502064100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 71772592 1250 71771342 71771351
    0x1d0d2609031b03090f1c0b130b0f0103170a030f110a0e0d0b0105010c0f020409030c110312040902091f02060601080a09030f05090105070b0412020f01060513021b01 72
    0xd900c6960780e4200780d111025640901c011180c499801001352000a5400340851844850400400c00c104950414082c51071454800d540049401814468010007000c0c00e1889103c1e4103003411031101c08002d00045802002800400024a504a60000702d14481e0070450301c400c6000b804601038149a54007400c0241406c0c108440e95013818010300c0d121025440d001e26440380074061000c13a1101d542d019002c0081c030401080a5405035024050551181e108038032103107901d0380010b0440341d00c01030039400590395420507010000d02c0d03051400d80d10130407002414000051000320003648120700030011200d030003050b86e07010394446015a0098100c01c0354265059040c20700c00a590781000c440007030004484001044400d4268440e5004c2d6a408d45c0c1c1d4800ca1090f00001030b10b03690702c81c2c802c00381006010400800421ba5046100340158844c2c00710b411102c22403080285005280414001d269144c1740c0c0070011a0307a620080802515000c102589618044501c04050301185041c0e00317065081 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 71773842 1250 71772592 71772601
    0x26010305061e01030f030e03330a05160f020f0307050c010f1d0d080403050d031b110712020406031a040203070e070f0c1104020f0d1d0d26 61
    0x820aa0b20407600c101d000551958424a19110a0000c1c400038020004005001010901c18500050041006021603030405400d0f010680200f05450780c801040c04903010502034540360b242455000400c5901c144014140140d40b0701c00360000200400c01e0200b40040100f12500034441030000020f80811303680c840540c0d08100703841d1180300c2c1f4600d0025140400c2c07000840e01814003980e9580d0000e000c0c0140009641c20700000f80c8102c0001c1e03501110901000001542c108010a00c400c0503a402143c810f03e0042011040100a40f202c8107008154034200c2c200280001d1500803500e0f0382c00e5480b09040e050011400a00137900b01800b19031100e0680d00020704030240980c040d500c20380448143c41e0741c40141f1503646005075405000140b9901015a00c10f120b030003c0c29106000d241d5524000011000081c00c03a40070001c60380300b26030045100c02a005082c40f4624004017042c0c61603408140c41d500301c07a103a10400c41000148042201d0f180503400500710100c01e169081034800c01e85062 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 71775092 1250 71773842 71773853
    0x20a031523010306090914060106021614030309040608010933020906090603010f06090b190f03060902160303141b030703090f0c081e06070324030308091207030f260103 74
    0x4444201c401c1f98032808000190b058800540046d030100b0154540150704d00300001c2c4212007841001c516070501c01400304100316075451140d100103281c0c4100000e840e082c0e40c64429005400b01d5600c041e504003074455809821044450411038200700000140d1ba08424000100c0d68010300030102e411000100021032224619000c00058901c2602c4000009036140351002d918441d443e0316448400c503401c0c0c901200ba01035226403902004a00300490780da620f50080d0350803a088200f01081e400b0149065605258040c801c0c15040b50440080c0000b510303080442ea00540e821403500a040d120000010702050b2095001000b1030b030784181c0015501c4018100509000542d0251110a000310008410b102c211701c08a00007802100016207103503a107183e0241c00510000d0031005c04000585843d12801d80144814000395100b0f45031540b540c08e1002d9011f160a0b1000200e40300448104074120109400180d4026002298a019400f000410400348601c2170b801c0e410348482d500c01c0c0008010040c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 71776342 1250 71775092 71775113
    0x100c02150a2009010e090402030f01090c0f0b09030601030209181002030411060a2106171c0f051225080406051308030a02070c0b0c01020a0315230103060909 69
    0x1900c124440c0a0302d202245400c00c51142e2030100780400c2d071102c01d42e01035040007000264020700041c241c460181021356450f00b52100740400b2105c0b81c4c9140c0c024040801040400401340c200c0c0805a0304011030007000c269a101c043c000a40311f0440e103800110711301081261020f0215030f0209440d0f029858500701c0020750000c0d40c040355090760048000255041003803c0e41c06501080c2d88840700f05520b40320031034010042c0701d8501c2c0045d03254400401e20842da80e80c40c1c8050442070000b0525418036059041081b00c800c5082002c01030416564484280c5c01003d80700e501160107892111a00c41121401e9403e1b103203201c42106d068400103c0784003d0308407040500c01c601846080c4925035806541c0e040b0303030800110007070144a050000c11401c40e00c40d406030201d41e100c1e81c000004c254450342414100c0d0004100354006a4002170740203406581801020320341460390204210260500507084400000321500c881889080e03058840c01d81c1c46032300030030010010494104500034803420700c0c06044 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 71777592 1250 71776342 71776361
    0xe15120a02040609180b2e030b070207030b011e030c061706040204120303090804051c03180b030402060c0c0603190b0a06020d08040f1203090501050901090302100c02150a 75
    0x103e280020000e910320240c01403005188002803204255000756645403940d03170780980801a810152012904030345a0004540050309004c440d40d1401031862a14440c2c041004265504640100c40f04000143d01990420305440c0a0000001c1c2c1598a802d00005519558000f5107004c40c00000000c8294100b039001c0700d08203910109680503034545d02840181c0c8614403401210554008400300420b03c0f951040d00312a219880f0145010f0380d440c00a0340420010701d49010b44258900c18104141c0c010240c18090074240303000880d10745c42c190701d00e103030f5000040c0064000d1707000252800c5402400d0000c08820320300280b4168490070484803408500d07411801c0340c401a40303424015010741c5401e01021045440590003080d003503521100488500002030f2007140c20070100500c0000040006299109007005542c001500060509000d4203580000d86100056458070340328201183e4049121030311211807240114500090040492500c0c001d400c51030381c5000c924051042c4034540340c21040c440c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 71778842 1250 71777592 71777599
    0x180a120e0415081c03020424120903091202010c12090f0609031205070203030c0a050102090901060c020a0b180312070201020123040b0711010207050c15040506040e15120a02 76
    0x72800300c0b810248842d0a02e000c1c0500307079880314040d48512010640b03000c0780c04201d45009410030356510f940c7c54104025030070303079941583c42207004584543d0084c110001d040071424240040e411544020f40070322128092055907220500d0f4440a40e4004e040d07014180d68460a80d12002e4501a00240255a01e008140b0005440d040024003980300e069260141c907041128407254611151042e036175540204800c0b40c0500050040000c1603500303004000c0400d00400007d43e44800840c200900c00c90140c014070180520040b40c1e00250b21100300581c1907903840140903544031015420842c5000e02400d299906118000c50b843c10070641201038100e0a01c01c0e0000d0040101250607410900307009908090f0b40803d04000a01060304048800d4210000703050404070405c0102d800d0342aa4000441134895170b01240c20b100c810300380b40380750000344d01400903c1803c00e400c19000544500c181d119100c03200c1c540c140440c0140040c0030301c042d51880020b003206c03299044540c0513600c03031b40c80c41c000342d10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 71780092 1250 71778842 71778851
    0xc050a060515010c03090e04060b060a080403141611030f1207021e03060403051c060308090a080105060d06051008030408070609081903030c0e15040905090c09180a120e04 75
    0xa81c1d502407604c10074042e03410b40311703491034a0401803042c640c4a0010426158103840301c44065058640700020200341c8200c1d1b032880c40c2880c2a0074044c15000800701400039800e810003144407820f040c1c246580314030b03902085800c00d040b00400044c0c502442c0d8040c030382d030380d02480381e2605400075010000e29010f8801d4480001d910160792000242c1c107601200c454140d0130000c00a4002881500100907042900e13010442407901d504220080358080e0b00704603240840020741c006203103414100c10001b4551314001340074038500b80f000704441c2880500000d020503110f80104102c4c452440ca65000303000000d003100e886a50320f09070607540313240a00c910000315074065400318504c1c2002c5100502c5041c035604d480040907280d0341c201c000f083d05811150400503c441c14605569500504d0080100e1402030182c0b11410002102e044400142007181c0c1c2d0340c4210f1900419881d0202c0c8190711003484207050310403031480c481540c18828584001442d80e031010010070300d41b0350098505c0070011019141000b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 71781342 1250 71780092 71780131
    0x409020403060e1513031106010f180504120e04060b12040b01080706020606060c010b120d031401140d170309061005010c0f0b09010603080705070801050f0f1302010c050a0605 77
    0x686481031080c40e40c800c8804000001e41c9410b1500700c5c41c159521034940f00e51450701010030142444020380042030807030140b0000301b00c0440524803800145442e21010031180c10185e950b001c258031301c907060405100c8464403580880d83d440d0301100c02000265012580e80c05d1a800380d02d408a01220229000342d50f0078008282c0c4d200c005007000a65807260010b04c0d45448041c200120303034000a040c1d001c80e64840028a0280d140c40568400e10008080207001603601004003405490541d441000301407080300041251982c607a0129840c81010b071140205043c89052180080d4404500b0005036034000041c0030f03818000082a6104211180346141e16079200c500440d5440c0785074402070024038944124001099441c031340c40f074001c0320340350000510710b90325a641401500000e10540b600e4101900800100a080c01a15030007081050943c6070362a2145c0c52210195014081c4214000c0741c2441c4421a400703040040011038101040340c2240d00d1506c1c001002e860b0450701444400e200c1c18044c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 71782592 1250 71781342 71781371
    0x30105010e0103031103120a11160c081b0607110a12080c060601030605010203090f01110708010f0b0a051005070503040302040204091506140a0c0c0f0b0a090b131202120102040902040306 82
    0x2071f040e400e20f4403403407091a222007150001500c9845490300305180c04020140c100360380c0000c0d00c05028440c2070000750552605002d14281081080c00c207100034000c8903640155038850044448587d48215040b43d80c2c5003410200c1d00380c0019800030000c1c2d103407400301542402041c0000d8038441649030100d440ea0707540c260045058610510a02e40581c1c4281320440c2c003498400320290141c281031401a20042020342c09514140700c0760b000074140e95443c420034036184520300407018128000c1c0e5806002902c4d040100b480c40058034160420400701007448030410906200322002035400520954540e51a4191040104031000e10980c018841c1c15001071041c4c01688044120b00e04d440c0d85c207083c03403495001038a842c9c000c00d0f03040300c0020883d540810780d80044c020036006007101101050302d89442c150054203602040d0004049880244a03500481056101d00016a03c0381d11120b14480101e2011030400d12030b02010701017950002ca408280740c1502d034080c008590140303409010303010215480 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 71783842 1250 71782592 71782597
    0xd0b0301020a05030703020306030c100e0406090e060412020304080105041a0603061b0f0f0d05010807060e030a080d0902041e0b0414040f02011806210e0d1d030105010e0103031103 79
    0x480c00402d41c113200090095000b50b000d564821005016503002070418400610a03026008000e8042030508010700c0c10385c00d089c4180d0011b4403400808111840b0a4040340d03079141e40041c0700034a40c00c403d0441e007081c0341c424001d84006012090003070045007058503001c2d145070382e04a2850310381444072000032201e260028800703003c0c3c1c45801b030780403e0340c91400b2020003a5216000b50482428200441c64580c21344100406c82d520400e0b000040715414412000d0400c15180d010b042000300c0300202030841e40e400f140e0103800c40d5000c0d080c04d5503001e001c0900c40144c405030f00060362280c64012001031240e200b100c02d11900031130700010007030014004100b10440703881402146441071010700060006d1803d480071120140141840c0840f226000703070001401c1400c1d000b400c0000c03001070103c982c0c2c41843c018168072001c02d0b1014080d020800c2d80301c0d907840d015900c40705d0030002c07018882c80d202074130b04541340e0001d071026009128668681880303001050083c481100051211041c180145001005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 71785092 1250 71783842 71783857
    0x703050309010324141225080601080d1b02060a0809010e01020403031d060702060309070f060302070f060b060d36050307060c1205040501090b0916180e030f0d0b030102 74
    0x4080f2050904000e020071810810070660480c0c01c504007980360074801c011000111400c41f45078280228101010014107040742e00607030495020310014800030501140305000a0000e01d0f1802c50080616643c1e45403420884000e900100009456501598401480c91107202050000c0c084010f4000d19039082344994480900041c5203021031005040214004ad80c5601000b0a11070038548143c001503801c1e4000d58500d5001e030b0021074100011802c50070554020111400c085003015941d440f4159164641031004190079070ba0045000c0300d80d91801901c0c0c1d9540b070300c101000500b1280c850314030f900342c076020341580348104110300404031984055001845540400914248001030f03540b680600944840d00f41800b2014128100d69452407003000c0c880c40c01040003082444141c24404010500513092640d90b41007a44411254544c0701c54450841e417440103000340c01c0601c141000001c000203880d50099020004a140c0505680000341c6050800072400b084007041e0102018202c0c8566070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 71786342 1250 71785092 71785151
    0x22503090e070c0803191815020906030f040c090c020d0e0d02060703050d060801090602091305040210050c03090d0f050601120b0a09020118090617030301030f021c0507030503090103 80
    0xe00020015444901646d0030040340d0506000040120507913100380c500c103010030f054120185590100380310407a042c1c1e04030100112021031074186444041901844010040c41348e001c0d900c00460100b103280c41c414401400c040780c2c10021205106402034407002d002c0003250000e426407112026a10b445007014030482c2d4010512441e06c000c954040c1c030329805c18100700180e55030304c800000760164280954010796120300750042e5604981c600b000305e02d003210785282032500d02c0c003c02c1000507107542600d020400700e6801c105440e200b101e1061440c510494141c0398104040c04034400c100545607a8041d0003070b200301d041e10100c2c2c5e04c1d080412200b1400d0034000e0280ca40c2a004500300c0c0025a2040400f5401071620648000601c0e45505005402c1d0f8010041d00b03540d541c041121078180e00070021805020702c09149554990340f51180c800c2c00503600a8851014442240000f8041030a4020354a0384441900d4541e69641850740d102d4000c4044517002c1303410070303000c402c00c840e030708a14080d40c141d00e9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 71787592 1250 71786342 71786357
    0xb0c0d0b040513030c0c150c0c0b090a09020c01020424080609090a02100c0204020307170606040501090b18090103030c05010b0603061c050f12071a040b070e04022503090e07 76
    0x31303142101c00050181085d29601c06103030010500d0050054180c2030040381361901c0f10005401e103451520485580d02c03002d080407042c840b019181c2d841e07c40352000c0301c02d2400050385940003400194020303c41c40d0700176a07201890101503840310710a05810500e85e4003584800c50113503900740c00d11240c2c01d4101d6080700c0342e0f040403043d1001490308180500c1314074000e2030403500e030700c0c4980d020500b04d038802d41c0c6450120b4819101c02ca4000084030003142d0141c020380d401428207103403200103020a4080e008800070200003180d201c0b07014003036404036849000001c044a00710359407414044c01c050703c442e034161419401c1031400702c0c5034280324080b030740602e03030141c400764540101d55601100011a031030308030303854000c5060300c000711007080018250500c509540d45654606615000e1a0481c01d0440c590042c0141c40030403001c151140291070348149036042c40707108511036400280082c46818803480c1040502240711103000005005621000d22980380c00003610b8803180301c1810442c0031541c0200068170b2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 71788842 1250 71787592 71787631
    0x90a020d0b04060605100507020321040b160c180b04050411040c0309050105072d02060c07031b080a030e0a0c050402070201020f06010e19050601090302010c030c0b0c0d0b0405 77
    0x764903401c0e445070003100d0006031a0b071210300255220014001101c0045c0d404a04041580b81c2842a14031010003191048003055441a035512680601e1090789011240031501c040760001c401520442164820441030340d644d01c0b0241e4069004150044107030407803401110020901307043c41981d0140c3d8108801c00e928096100400000d03042c016645c0b82015110481180058000d010b040e00071030164440c00c00701c1c054429500220240d0a19040703011043c0c41c901d6020319004140b0a81020280a00d1643c5150340d00b070030341d06180020a01d200b000321401c500000e01c158071028043c1644180c0c0c0522000748200c1020b0b41c0e51000b054007412041030002d08004500d041c1e030003880380d1481801900c02d00d20b440262242400026848100c6002ea4002040ae030142680000a24030042c030804002c1800d256000800301c036140e0000038180f0941140369004d1601880300300064030342c04002d000b802d1a00b4020141d40307402600b10240000e00300320801066140500480707200b26070040c4d00301a80d401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 71790092 1250 71788842 71788853
    0xc080609031e07060906060806061302070b0105090408190f11030a08010902090a0905090d0f050408150c0706020a03060302010906090305060a05100506070303090c0e0f0f04030e060d0b09090a020d 86
    0x3101203134020760304c40c56003000407054054013009202d014090186454140705000101c004094040c100a10412444002542a00b04141501d80c01c1e01c0e40c80c03465031607160100d518419021050050707011080600704c002d500800700c40780c80d040c9030b1381d08441032031841000340d8a0144040c01804103108100622441c24144d004d045040c1000780090a020f03035560781c01040b110155110706907504144104102b142c1c02c0241242c0f08001c503e029450f00d0b20b04419540c0710320140d030143c104c0030b4550b80881c007002420401c3d00c114582012045644045c4540041d00524940c401240815490080020854029001d14040b41d8202c40903200d15682c0c202c5030001064020100820700965482c081465103d5034007814a0f18800c0d01c0020310100380c0c1c1411001c2044c1d90b4050800c5d80b032640101305048002d10001a04080000101e0303070592900d00d82039a00000011303015401041c085403204078840280c01c280389404050700c4481d00b0382c40d1070324055198082d00701d001c2d401160345a0240d00054 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 71791342 1250 71790092 71790097
    0x301030203031b19080c070b0306030a080d0f0204090e0706020d021e03040312021609110a030b1305070c03140c0a1502090a0603020301170a0b060d1b030c080609031e 73
    0x64400c420394610168086507002c400341c404130181c803061030229441e6081841080040d01a203407000c841c504511f44030000030f540341200c0707200034070a00d00817070b802001280640020b00d501c40320000554540d5219a1418010804820048128030036444000703a50750010580300c01030100c0d540900100854140000040040709aa03048644810400000420001d00b40d40c0036801b80c0b540941003825441e021420302c0c9086400040f9540d00c0d010004800083d1601114003030765142c20041f43c2e4001c0a000111106c001a940708506800c00082000d010307400a45880c007288030744c807804121016401c201405001d1840d022101c1d502800190f00800c01202c0b4500113400c00c01409441c101c60180420742c0a0075640c00040420307000f20043c4400c00342008018440ca030818000d000080158440c03072030000780a029075004100780f641c0e84040c01458510035140800c4580030740c002c0d03542c0c0c2c5003140e2100001d200e04410307402820041600c1200200403943c2e144c5250003c0d0a40d42401000300d036840c0d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 71792592 1250 71791342 71791387
    0x61b041a0405030105070905030607030605010c032105150301180b1f180912020a0b0601050c070e0103050610080708030304020103360201030c090f1e170303070e0105030103020303 79
    0x550305210014035035809000d0b540c400d806903070303602c1642460b11050510f05000942042c040c50300304413042c0403503640680c0c0c40321a2905890b058203100d000d1268940d141c41d1401018107041c0c00d1804204140c4034241c03240507078001c203800070071080000d60601055116a210001d04006400740400d090640080300c400c489151002208180307592110340c08281880409114000c1c2e03258a0100240110064098140702d03950001d0140d520307a550b9602c0ca4060020941c906002010900e0301a50702e080200c04050316200303040142550f100d04140d41d43c1c12080390100101c1c41c600c0703008240890086100412202c22500031070071621703280e0054000d802d6103940c40707030f200480c289010b0360407950051000ca041c0c40000c5484184d001c038000103054604403c0e40e2804c0c040200c00c10030030132582161090840b11038084203204410148103040800155511411100c000c0e144060640c020204c01503000b42400d13114504510005001502c00307020922029601d030b0002c1c0b06900d000b0680c4441324001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 71793842 1250 71792592 71792639
    0x5090103060b12030304050a150c050d05100f03030507020a0915140d0b0c090405070216090905011419050114100e040e07080304031a04050d0c060609020304080c061b04 74
    0x1683c180300400ea01d1900300b00ea054420b9803083c4840e5082c0949030280002c070000151082c405d45c6840c02001c1c005116010901c0441d540d22400261881c0001e00e01202818134424801000c0d596410020550f800824059126000e12600041c4407002445004000400a071500d840c8a14004000000511802c09140c101039450381400001c0c913070302c3c1c440b481600580c0c0d00c1038603800c80741d0034803040351002415802954000c10300600c030320024104440444d404001d02064100c01c0b0310b00ba902400d03105840b240c0d091040c0003840802541010408080ca40c4040b04200c0c0e40e031f031411003000c07171010324a0454004400c90319095102c0c2c030859201c40c00a2000c1c10100d0100c000ca0f04e11341c0340103142d5114100310f40021800340200452940010405c94110780d4011181c20f19407100c2c0d48405020040c101407240c440103040400c00e09030070038401003041080031900d928141c2440c2c2c240b903020340400802e034041d400000b6250040d2582c0819401c02c11040c1030300705030030132401e992241d805480710f104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 71795092 1250 71793842 71793859
    0xf090302040204060503040308070c0b0114130c08061201020f0307052b0e0d03140f1b030406060e090d120509010b0402070809010e100203190318060504031805090103060b 75
    0x507894600052004000554696560780f42c2420018070707805000d40020108054080c400c1c010580d04450507043d55142d01188003d10f50903130009803d0308089070b401c00c40c203050440900806411444071845040280c4030349001d91501d840c1d0600300d12070124001c0301030000b4000300d00791a2140c0064080c81d02d4009905405100300d0803000002c8004900b00801d813034071400745103c403403000d00c030080c0d1800e00390806104054a000328204a020010038507403400c000400021400b101049072045403000e40d0f008580d607400c050404038050800e9005081ca1141c481000c50142000040c120441180c9551681c800082c0d000b402005000003502d07006180d0349034414100070b503480384018401d262050444558510428001400300480001028072400740c031110441140c3c2c0210484180c07819284506805904420094000f40895030041e00e0090f801d07041607081040700e500ca107004034000d403102c0700d56140c8200300c041e050384a40225600001003c004000040580d0441180701c02c00901284 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 71796342 1250 71795092 71795099
    0x30606010c03021c05070213200403050a0605040c0314072603030402010f1e0503060a0e190f090b0f040302071403070b0d02160c030308070503270705041b080c0a080105010f09 77
    0x2c84c503001121900362401d54500b507510100041c050102051250270074524105469922215120540c0030780140105860720700041c2008007442510001d140e000050201001d400c691050781c6440302e00070848029a02000c00b00d011540b07850450b08d890040005520b165502d600455210a50000407402c2c4003000c00545540c5201c6040040c4c00405a942c041e00c03890400b04210984c41180c1c40780c4501000d58007400881c01504d031040000e841000c0b004104042c004007141c004180b1001d003d8038180441c4240300c1ca01c1d01c032081c2d460280b80070f070b03084440c50364031501c00e81103541808000036415030000104120700d12910700900702c5a6101390700182840001240c0429403d0a07400072601600101000c3c01019000580e00341c01001504d00716045140c0071205280303641c1c03042c11903548510500504d000100d0100400300243c980500103100310346407901703030b844000c40d2840031001048003500050007920280c0309640d0701c800380350b841d0803590b40307805d00551b08400416030f4081004403450f00031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 71797592 1250 71796342 71796349
    0x509031204090c14040305070302210304030303020702040b31110a030b030d0215010905090309130e012a080c0f22060507320f010605030606010c03021c050702 70
    0x7400207000c14100464110b24030000103020040540102c0e0b41c402044c0320500c00b0450018403082501d42c1982c41103502e4213501e103140d03841410f0f04169015880001000f000705a41038018001061003501c09011085a550400c0501c22a481d0041c054007030081300b052205480381c104087c42c02403040001480c01290559011540c45804140040794907604000c0040c201000080000c03442da101a058a1459005102c030454061140d5035801e074840001c240b80100500859005860040142c182c50442e506004040c00710040841041d52803c02041d61000710082c07102d010a05051500e0741d826060031050740c50710006400005d041a00f88241900746000000801d103658001080d07101c00400003a0b2019684940c1d084101088418488640010701c03415500f00d03110103418040c0750f12010410309000402103980040c4842c480c86140040d0030f101903020105a64098007900e04135606c0f040103590041601e4802001a403001521040807851043e00007803110031850304070f181c41c0498002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 71798842 1250 71797592 71797597
    0x1209140d0b0c04121211030c0c0f01030605041d0601060507050a0605040606080d110105010611030a0309110402040308120601051201090902061318050a0c050405010e06090907050a0215040c030305090312 89
    0x2c80d543e04105417200f0f2080c0c0c20a00740003004248000a61400d1849030031140c940d00c41c00c401c580287d0b91064012500d038020f030031050103800b02901c200010b414480e45070020b911141c0700300029014038000440c0b100d200700c049682d00c540201c010404c40c0c43c0c076030340e12008200051059504942c3e90401181040041c1310085c400c00032940c44170014a400041e05084800682c06482070016903084140d540380003009451f03c2c0120f90074001005400f50921180001403203084136403180c400503003c010042ca680203000c803c255058103410981c0d800005540501c604803683c0c0586a1080042241c059140c00165001e031010340304134103003480c07989202c41c001d00d190440e44c550881702081a020403407500c41c0d1540200c10001c140064502400042d00c11f120310b008507810420507a07916902da0315040110b401c00c54010344488a03500d46158000e1150304020024030042c0600100318030300940c06c01c26240134a401c452240c200510b15501642c8940c800440150075004029065640910b000702 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 71800092 1250 71798842 71798879
    0x40609020a020a1a04030c03050d0608030309010f06050405060604030206070c0504020a1707080115050d06080a050309030d0809070902090f0a09061a072109080a1209140d0b0c04 78
    0x103241c042424500914481d0b400361101500e55007131402c00c03000c00d50002140144503003508102d560341c0e00c03034958000a012140c00001aa1000100b84980310701f056101e00c0c0c5280d60003104120340c940710170410003a0b0f01d00b45d62196211100348828805482c010000303040f0720380b00e40d03540303041c8658a03004141680c100c0d100100c04500092503070803c000d5120200c59200c1d009142000d055810070110400d55001122071404000300420543d0080c1400d500c688040d06000e4115901100d843c80c1c0b450f6280c4c010b20006001c0c0c001d4800040040f8010a00b1a0241c462a0054000c0344d06090048000790405040700380d206500d498a640c05850340020540071307144024010900a04089480c0105040400107800d00601042903001103480004c0c082c03010708400f0400c200346800c0c2841207551100c2c03604812480d00400b0408420005001d20724000e0420030340780c54030503e648a280d00410800c1c00c10306038000e4084026032000642d030810305903001c0302c40f510b42401c040d1076410700500e40301c0020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 71801342 1250 71800092 71800097
    0x5060a15180905010302040605011e050a090e090f0f160501030902060706020d05010509060312070b04020607080415090b04030f0b0709090903020106051302030603071406070b090c040b030309060a0806040609020a 93
    0x100500031b500700390180802910086c207150301c1e500942103a400703808131291042020480041012548a441111846d0040c9a42c22003607009042040003583c0320380c0c60b101020260703c40c80d14075119800000c03030284202c5071912030410b08030345010015405858091000c81e0712036020070954000802c0c9201a15104120280000d21581400300703001000744080c001c030340710f9440341c9a03a130401654a01114070f0150b101181c0046606c035440424198050741c4001081d07400007090100d040c90381222400506125542d442d041c00d640c0700400d0009100d2408050021201d8940207404100e802d0a2503402c80f40301d18115625940e1401040100d8078071880071401070351140010030991400711802e210380c0040260452031400e0000c0041c0da51145445010742c01c0f840c2e4030800245690b18002d807a40c0d603401016140080c50107900e610340756108036208502c9285400c0305d1043e00c0c01c000044e030386550344c0601101d00d4600e60520681d2290801002d40ea400b075103415010440c04540d00281076204500d8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 71802592 1250 71801342 71801351
    0x30207031b050c0901053a0609080703080c030105011d0307180204060e120c010f020307050d030e0d0c110d0203030d0606020a0b0901020a14090303070c060e031005060a151809 77
    0x40100f05100e08103a008034403c0300e84c81150000d81f400c0300240303646e4886107003074028000c0850124590003030603c0006880c1516210400007071102100c01080414880d5a8244c0d40e51b9911000100b580020701960b400507400ca418044819584403c400c80d9120060441300e81710f6580a0412490399110301c0012102d402003420422950060200c2c81000000c8030032810f40b40500d100c00c0d030380b0495650410b0400005100f1041514000d108807884150801e055039207415415001901500100818040900c0350040981c202403041c5012426190301c581da21800d4071582c403c00c01c400341c0031038040e41e00d40003c0102e402d00092030f105503c020906600581580b0080f420800c102031401090f11540da401080303014010f80c3d00011080204088481081c0c42e0318401c4042403a5000b4a913004000354958071002c9003244c0c10288140444030110211580d1203400e07220002991010783c0c0003070f0820542c0d8018014914110b0469a40f0901c83c80d02020081c1c2d80d89043c2922841d5502444a4030f50302c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 71803842 1250 71802592 71802613
    0x50a0b090702010c030b03030405030a020105090109120b0f070804030207090c020f16150c0f0b0a060b07060608010c1d1c05030d020a02100501050105070f02060c0706121406010f030207031b05 84
    0x1400346e030313816000450180d810146054040303a1203200040009040002c00a81404107a005125080c0500501507240c00303401100e140c140486003007a034003000d44c410001700107038826200d41c06041c460741e8503901030f101c01480c000d003403070281012020607025070044894030000c0810811417220080303102101e1000c0c6514080707a882e00b01c414110000204020041188089103402c0780c5c1d0070080ea4004030300d4111356280d9400c10300920702030f040f202d0a1034001840b0001c2c4400b6800200903913800500810200c3c3c01c00505070f40000911805d08205259a92441c11034a011030048440041e0812050b00e4084c15075919420356018411003c841540403c000380307d141e04000722402c00d249100c040140d9410003002070301c9070082002c020140092341c0741042c02c640341c800969030000000750844507842c0d1a1540501180c44030008c540d1310519141080e1801c1503004220b40c0220010707110140e91420a43c411030196000600175024000182988412515200c44840c1014000c4010b06641c845 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 71805092 1250 71803842 71803847
    0x170a120905030c0f0705040b010813080307121805161202010305150607030c05060606120609060114031306050c0405010c03122403210f03020a0e0a03140d21050a0b090702010c 77
    0x70740c48c0189041141000801a81855041031894001d4110404603240c0c0e0300c400d0b00300c50b88410400d586180508120038841d2002007806101780d614403c0040c0c520540426040e481c07201c00c50700c10801c9510a90804ae000341d40070b584069000b056100c1d800c480380c10110041a010350180600314005190b4030781c000c090006c180325490300208119096858101c100c4203101007040e010f8846403007200c9840228000b41c4c02080080500000311b465141c03280307440c0f0341c8106000d0408505854160801c1c0000380c1144400c81102c0503600140c5501c450003510351002c603100800d10807260409076841c1ea2440341258000360b48500d003d0404044c058647c21490b0507000c40348100010510450704134640c040c0b15030041802051101c2c6803500507120040a841121041e400e07000d000d070002079041e000b2052041d44c500420490300400100d50394268444c404a4641c0c0f038915140c0e040c000c500c03072009564480c0f90003141e0803910804001c110b120324100000d5455009583c2100581c2d910000188480d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 71806342 1250 71805092 71805101
    0xc270a12021008161103091801090e07150f050412151b0905060f0d0509010e190c05090406020405060a030f0605011803021201020c060a0603170a120905030c0f070504 73
    0x1000f46080300c15810810003c040700d0303214000c401c041c0f00c41c0e46480c202d000f0082060b9416010300a1441503030020076034200510003828000d4821050605103c0c01c9418800600e8408a96140000510400382c05104603258414070950131b040103c01c2000094480064105103422401000c8003c49156503031400d501700c1d40e0901c5000e80c183d0031203207071070a140d4001c8504021030b602030302c0c410b540d0031503d1001301d1537100715404120401d10b40001e001d111541540516a600d44082c11514030382d65050001900641e032810003000c1d07d04481c014000350800171700c1503410070f01c03801d400340c2070a40320400200d950f0400c8004c100025555000c4e4000c0541c203004620040000307007001440940c2e001c030f00c52141245400041c1c0968010041400c2d890000d40c1110184054282074030313041d04103040f4810150a03903100175103805413180400f49000306018212140316400380c07a0002c0102011900b10083c2206141c1a510750200f4040c540001c40c0030b0004152007503460000c2e144a07820030741000100d8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 71807592 1250 71806342 71806369
    0x181201020a03050f010b0313080f0403030207030506090a050714010207030f0302030307180501120b030c090c040306050106050f0301090903020c0a2909031e01061503090b070201050c270a1202 84
    0x100c40c4100100b06c400d400000b00d039002180005900c1080f0704905103400d20b8410b400c001d0141c070400040000600d680400c04000780d80c40343c0140c0d07186448000e0216928500c000d0007420719000208200030a11540044110180060040d560b1542e40c81e00c416506c2c110204003030700503070400400c01401b1030b405682a83e1160b00070a40d0791807a4140400242800288105140f855a4541d5038206d190b4040010000300710f0020601084ca10f0141b8964041d500b02c0e20046400904001c000300d00e10740580c0a88008501c1c50103442e0a5030320304030020004d0101c3c042c0540540c003c24804024a0311141c0441002d04a26944840700c0221001615021848444200b25404040c0301c400202d40c1c020500d00c3c14000201400c482c5c040d0106010744c010000380e40000550800350100361541501500240075481c001c1e20703510544c2c0c2d5040c00c00c2c1d007a02c80413210581c28040420403040b605a404c404402090300115030050310b1801c100101d12100c0040d008840280040902d00b011481c0c10684130002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 71808842 1250 71807592 71807611
    0x10c020d080705090f1306030b090105040f0807020d06050a0b030c0a0b0a030b0a08070305240402090712020c0f1b0312040e0604022203110321181201020a0305 70
    0x11400c0400500301c0001400b01020031400164a0600303540b41680d4844c3e01000404801b205440510342c00000d25041c842202c850075000d000401f0703000e043c80b60611881e000300400c03c0d4070314945c0d217200d082e500841c0c080741d100c0008024035010134030510405106040800002400038100d1042510706105802d50b01d1141010b44024004444802e05541042c0080c1c207002c160800d182d80001c11510150304940c0003403190003070000a0000015283d9000e40070000c80180c0c0601c800e1542240e054121806508481c00f01c001c108040d1044901c0c940c0116458001401c0440d00f0540a050058004c4400c0f19030380081000c0d8088180701c000395504020440c0200640210b01540198500462147c4c11410f21020f00081641d1100e404894242041d54618220b44100005c04070110340540030544801022200b0321065090024080d0354602c000d010100f480800100601a5580640140c541345107954082c4010b54072001c584002d07038042c0a00260700c600d035841c1c005080740d100030041100c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 71810092 1250 71808842 71808853
    0x15120703050712080405130f0b0f060a180f17070f08060a0e0111040b0d0515030a060e0f0607080a0507091d0a061701060807050d020913030e0301020f0c010c02 70
    0x14100090b21000c44900420280e6108858100020940a950300060708000140c080c18440400d6510414180348110420000c4940360402e00000801c4400c485401000820000744098054400d07440b69242c0782c009a42550345036203500380d07040c009902c0b8030394403c0307824a900c030440c2051280c50041c1044e086800c50f0240340582e411307560303903010300646205942c680c4160384540b42900310100700c00b51140c17a0b030b94030b545c3e8124205543c1e203d040d08040c5189048081126148282c0c01c1665400c0014014402d800c46901c41c24020318042d15140c0c181d00c40d41002103010b080621206108845988501c0b0440c54500d0070202134034001000c075810040301c05018411910f0210105603112281c0c0d0214015564030903810004210036040b40403410354504000c6003c075015007011050740c4040054560150703032002031020a491454009503c0b404d264005082501c00e201c2c584201d40c081d140407006100d514020908903800307a594441c040100050324214840c007402000c2d04000f05200408 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 71811342 1250 71810092 71810099
    0x1e0b030316080310030c0b030105100801080606120102040f030b070f02070305030f0c030d060b0a0219150b03030d0e0303040204060b070c1404060302030f06010e1e0f06040f0203151207 81
    0xc45628030300d00700421007080070003c51035801100510201440d80005034203500c40d01e90840303c1040e00244201803154204800d08030019100c1c0c0070300c90494204000810950726a90100200200d2413195000b01d5036007408005480050512008010b40c010301440c10541085007004000803001440d0900b035500c144001c20014100000f241c5080000c10701d0a500c441c1b405000f03900b18420801e000480c182801001b1076401482d0b802042d80c4a1580c084492007980d01d03168901604100e0f400be00440c40d5848000385100c00c58018002c1900018280c1c1d203450001c0c1d84190442d0365004890207a9030001c0100011400c0c10300c1550050a201d44035a400c0043c00d039076071211300450f8069451134a4a5414204a545440e0000d40186900030152200d0800804540380e84040921401e110a2803800c04518000d00e2841c0d85005044c0100c0100c40301da91305980c1400808014203070356003141e50f4646480c80c0e00194405107019000100c9200740d4006500f0400c0341880c4103407807880c015081030300d082 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 71812592 1250 71811342 71811367
    0x30301080601060c02011b0c0e07020f070b0d0209190311040e0307030c02040e120304061803050a030207080f07060902010306060216092708030a110a120b040905011e0b0303 76
    0x203a04442580c07130000c02a035420b10048801c0c41c642141302d260314401c6c07242c02c8100104040c50100703580200f1980801c81d40c50900c101ea4075141e102e03191500307402a401c20721418604000405800400000c00b51900f1707802c0e8040ba180c00b12980a0501040c02804140108004560800184401240c05001e140107031900f42d9181d124003440141803242a041880464545422481c0d140c204041540c2096005001071140c2c0d510403201140c070545002ca16414042c611101c5115894140c1c2d52103080403030300b010580c002e40c000981581c9005080c000030300b4402c00080140341045c440d0b0408107403504a132001406072019a00028155041964004001842d95260300100d4441c00b074041200c0840741d42089091345a00102d03d02e202d050200802809001002103010314540c2e00100445008403038403040500403100f00400180c24100d8004902172070390080c0d003070004000d000203a14612550340c1c50841c1c513034000014604101e01c11200d842002441050740c0840203130040c502e000d039840c501 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 71813842 1250 71812592 71812603
    0xe01050a0e190e0307020a0801090b0c030c040e0103030c050f01050f06100c0f03180f0303080f0a02090a03050610050103150302010309170a1701050409051023040803040308060303030108 82
    0x2840709814006000030020403820740c4115081c2c06000342049000301610358070781c40303a01c0303d0016809461800000901604144240c01041d50405494142e6803505504040c5c142e20203081014041d03070510001c11110082d0581714004e40c030985401c280c1008618100781000603d1208a1060b45800c040045003242c01e028a944a1021124460300030306602c41a107a20328013200150001704202e00403c01c05401c0704440c8003203094502080030640d0764442030001c4000c64040180002e00b0400801ca403078902c0d030a42908403292140241c2840002c2c00840c3c05422a6071083e13500ea0702020910508004044802e40600000c0c46c00380a040041ca046543c0c41c2d8251200a0415503624045401e11008608920700385a007200310981e20300d800381c1c0082c072203480a40c10f04180307003009000041a260070320440b0f0b4460761110180039502407102ca88801800c00070381c0756044502c0f00380c00b12488001e914545116a00c00c0d034009490342040d040003008000c0090086020340d008000610504100141 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 71815092 1250 71813842 71813849
    0xc09010302040f02130902071103030307020a030302210f0a0e190206071704090b0109051c060c050c101d0a020303160204021b0109021003061406030421080a060e01050a 74
    0x42c0412002404101c0400a01c00d42c07402441d0603410003400f080c4160b4503001021054024004800280701400c00c040d180d10050360308001681c84034505070002400398000e814450b070003408141c5c0c14090700104a9032103004072018820300207550100031540429108a11a2403a1b64008141c081c0b0480d01c1018115141c01c1c0180c800d52000c00c500c0d04004001c17000960179100d504006490399910034040c0d020702030a4440c070b0301040441c48003080d6407c4c085403040310005035040081a848880d10b4203401004504072560401c44100030721040c8107010020081d21080d00c1c0c3e000110a403c0f041030844101c1c2483e41d12a89420181030200541c1d00002a0b0b2040341c0c0c400e9800c1506d00140c40020000c1c49551f40084001101c5003c5a0320f034a0103601c1041c03418000e5a00ca10034225040c4200c0888003107004403030715108902480c4500c0c1c200f81c00515809441807140c0b20424050181c9001d04111076141200041d200710100114140240200d10051100c0c0113009065410312002501104c002d00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 71816342 1250 71815092 71815099
    0x50d0e06041a0409090507080105070c080f07030905031e06010e0106050304031808100606120e061302030a020603040b070219050705010509041d102d0c050705121b0c09010302 77
    0x10b03007664140c0e14800b203800030b0401c0c0c0030030400b161481c9856a1101c0191184802c654a05400199440d008650051501c2d9010712030078980413640000b0507858010160907020010b02a10108558400f048124803020032045825624120303555528500f08050300440b8a50216000400c00c043d0481c09480d00142c1c1420840310361060385c06142c8810400e075121146030302c41d105528140c1d4150354045c03800e890301da90303550828128880c020003d482a204d000e10041d0301c100005113401030b01c2c002c00110203100400f0f44000d0032076500020595002035500b903d40f50070b01c104bc00300c4a601000782803850300680c3c00318120300340607860705a11943c951095505110000804244a03541daa200860740712201d032100c807400032214110350f81c440c00b80502c045001c0c0751007418810451101304880c60304401c50140104100c0e115001009060071000a40510509001c40000540140154142680040e40c42500c0e01000d184440201844e0040c2c411680c1141c02003001d00d403200f40754241500e8069 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 71817592 1250 71816342 71816369
    0x702030604030e03150406020415020a0c05130f060311011e05031f0305060f0702010e01060b030c16020a0b030601030b090601020a0308040c090608070f08030f0a0e0301021b0307050d0e0604 83
    0xe5004c641028410500d8100303400300c450802c001c118071030f03000c3d20a4a40c034552460401031101b5041e41c3e6003030040d0020740811069081000145007441305440c0102c409a0302041d180407c13840e00040e554903402c110303a840d08018690149507408490641c0c03030141c0c0d021901d0703245c0d00b801c0054190701c8082d003d09c11842105640308200068044503200845d44141258071a25000c4c00b400042c007002c0e038541005500b40445003841380300500610741596041c40072140303580c40d4201c15003025403090250003984d25524115001690b41d0000c980000c240d4a121303550749241160004044824001307000d4801c009103014800d090764001882045598542003001c0e0544035030130b100b2007042c7c9030717800000b1072800d100c004100c1060115070740007112000c00034075a44c00d455040ca5034a0b401601000c80515809010700714003107204050803032003014007800061500700908041c5a15216011040d1215400043c48004000041010840500785860400c501002d078500141c0c5500c118415442843d004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 71818842 1250 71817592 71817617
    0xf0613120206120411091006210e0d0804030305060d0f0308190e0d02100e0c0d08070812060f03150105060d15030b060901060810120311011103061302070203060403 72
    0x11007003129000340c0400c2800f00240381c1460036090901d00b002d0150b00a03603003600803c40700300c00302030a6001e0303a1880d10b44808002c0c004844a0540c0384010000e0002629440c010400c54001d0114601a02084c0d03140300d0f051800341405000da0f00090b0640d805008806c08440203c3c9100000100c159810315180d16030351100840449440c110040d919420752500c02040c4421500041e01440c2c0c0000b5003d960301c0a50842090040f2144a8840c404070742100840b003029107004c10380007000900c554400303810210240c41d4294141c01c005c0c280f22110304004144516480c00b140381064080d0304400400e0801458840701900d10810300ca000d00900001c210300d1400001034100918181104500714411680e90a0404001c00b095071041e006041c13210000c6001481616110711902400c144421400e00e440515510328081e900280c2c00c00540c00c403c4480e15400703004450000702480401c9440c0e050080400100141c5540e030341101600c1004154016140810899803198043c01c002404045 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 71820092 1250 71818842 71818849
    0xc031409030a0c0f0614030603060f09070306050406020301091d0c040f0617070501080601050301060807050307030e03120a0605010507030804060e0f030a03020316090602190309050604060c020f06131202 89
    0x241c440000f041c00902c840c0104005403080c00e05400c440560359074851913081400100901d201c25210503802d50003020000300c4076603c00811941040301003081b904c2080e40e944074103040f65015101210715540000042001013b1401003900c081014141d2041390740744460060340d02c0c9882c2c8030050240340c1341c1c803100b0340c01c041c1130388238000402c0e821910780c010248042a541e2990f03018007401b40070507a10408201154410801e5a040e01e000b5103c44900c5d45800c0000c3e6030940000b803180d410180c0381c0c2e44184000f1300038000f81c0a1042090300c00442424020103400c11b03265144c0206040210501150010035800a2003e40098000c00005001d107001040c0d1420055241d14003805403000040714802580d15a0045201e880e0741c0400c0115800d0f03020084940d1fa50600c14107005078000344d104178281440455642d0142d202e414050b525a9a0394081101604140e12040c00f0a9601d03480d4070640c180060800c0c0c01e5642106c1c11480e001c01c0148203145240701e030060011203506001600d08549 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 71821342 1250 71820092 71820103
    0x70e0301020c0709021c060506040b0705010219030b01090608090312130b0f071211070605060f040c020c130501060504061d0d08030610090501020d0e01020c0909010c0f0c03140903 79
    0x103104402d03030b00e0f800d0b141c900a5010303602c8284007460b4845004141da400e10782c684078401c00c1c1c070001080585040d2803d69014a80c1c5c210b190b05036142c0d542000341c1601001400c008d030f4186002c40c0c070003007103169521001401420055000d10306114006c0108040c0760408411100b440d45215030186081e01c4410f00502520290398006141c0506802401202c1c00e810200034032480341552158800c1d00080100c0b400d40e00104248481c41e10709100440016800360081a40041e010300045000045031001409454640c03c280015800070110000380c1e042150300044400c558034800d01455161240080142c40f03140301e040c1c10005084804210040034142501007040001d04c0780c142d900080c00d2069440d4416100d2610418000038200202400f4204450840b01c058000c2c200b941c03034881c4180d80b050f400e01c40f000e0450091a1301d000301580e074010707054010131600c3d00004180740c142e030025002d44201b40d1200240840030010b08006640001242403042000544640b110000c6004ca031901 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 71822592 1250 71821342 71821357
    0x70522050a0204050901080c181e0a020a02151302090705130b0a030605011106010608090708010e0f060601090f050415090c020d02070f050f0402090a210b0f0c03070e030102 76
    0x2508100500041d400c9540141054030801c4074519a20b99907040d0303983d55070f03075000c03505a0442e0741d1000f4540415034000c0c1c0241c1c000b0940024180102c0010740b00ba1942c0c00c2250409645136002c2540707400103604011510480c003e000d4907512609040000d4030010b00e4203000244225482070024000c0c40c86401558050788140c10b01404440e250001008140c10810100c40002d00e0400000313025842401c51490042c038100281c030980e401d00000701c8643d2402001001103200f100b80009a56209210f01440040b510740a80100f149000d8402d040c0500907100c181000303404202840005402d600002c200e49007240c000031200015840c1b0595480c03070754400100e491400400321400c41c0c020a100c0e043e018150b0a0f112a16100c01d01000918020b02605402044c5016110420308181d03005020000c4000d040001c0c60f07603034603480c0d0312180b10b0f07501201c80c18102081407020010754400c110f4000514403452807251500f25103030b90071800000c0a031030801c42c0800001250740c4007981100c040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 71823842 1250 71822592 71822659
    0x60f0a020c030f0106141005180f060c01051e0127090b070f0807090f0302060d0e030a170109021204060f090510141503031603021006030b010501020c120705 69
    0x3000e607034060303c038002d200c580708400c48850842d900703003420b00d0f011240c2804220103032542e5003045400030b034011905109190781904498091000401030f91040064405d868001c0e00103d203074a000289400c00c4c0c00e02002c1241003046c10b070014003400399100301801180c83d44824241645055503010300140940c0300f030103080c41c10f20030700b1322214031303404501c02c49141c4c081e44920b141525101002c40d80003d8070700c2104441c5031400c009000525002c0000c11840c2080301011510a91103111235080d94040064000410841d0b6002c00942c01900121401018283c9085092051000514100f0070740100020f1a65584002c3d8002100c11580440c4440d5044812522440300d04170b9030300c000784002c51002001599988c00180c40494180596840b00c6001d4043e6007040d100059a2089640008044041d40500406640f000c1d10034803481d0000d40c00740509071360b154074010000e4104008d090816024004400390310350b00c080300058000480c0c50a456064604045900f003001110258040400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 71825092 1250 71823842 71823853
    0x90b0f19050912060108060105060702010c05030c0304050a0e0c07080919030809180903040303081b07030201020d0c0f090506030c07020d05070312050309070905100302190303030507090302060f0a020c03 89
    0xc0c6501001901c448541a00e40f101001c040d044075a958040074441e020195004000520031410f00001420080d031041c10180c80004040d50340c5400c64002d200070450301d610100d02001603141540981005040c0b17980b0000717140c2481d0f0015a44c9106c0c28402400c905030029402130306441e98000120340c1c001c0385090820030750f01c80c50480e40c1688462002ca2107403c401c8a0a206100004421070203591003400a42c6440e00d165010355150000401c6407156003117481c2a00302c092241c00051a54a10940c001a91a41c4054034101220111606035081000440054002c00c3c1c100d0307a1f440c02d490702140d10a0316035a458601c80843d00c52010025080011820310718204440050f8100581c2c1c45221901e12441001030202c2e03550004540520355503000c04420402c2800b20f41c005030b00000b10303c03490503045480790040346c0403954902c11804426000c3c0c45c01c00c1030560510540390820302a2030078400c03840c42c2d900051224000d0b0850089980746c00588490218004c0040001c100b0b0058250340 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 71826342 1250 71825092 71825137
    0x1020a0c020114130512070e041a0c0a080711011803030504021203160305160f050a0b070503010803070611040e04120e100f03090f020901150306050a0303090b0f 71
    0x30114420380c80c00324007080a1038803030000d540140042d02c1c524680d0710b0102141d81c1c90401000303580c0600c808000349038020740f0300c0411210200184a031040d03029002c60400c0c589201d200500c012002004a40c031740405200d072000c0329621029403904615507281840d103001080321403070300410381c4240b81034103410015012800c251301600310302c0c4914001c1316280b00c2e05c514000b03c15100d1080e400c0940d9011503480f50000068080d0000d000003640c11031200359511126510b14003e0403008509658560060288004201203050101d0b4095100d1424504551403c2100c1b5a00e002d801c900910b0b01d501c40e4504100070440105840092000100140d00c504050070441c107c2d028596400d40000e9402072825000c2c140440550201d00310350740c2c0d070100c03590035002c202d000300081c010848410423000850405a035480d01694040c0840101c2d4100d415a0180c0c082c040b43e12907031102c0e0040c8005501040800d801c00441022102e50341c0cada40da640d0305005010511803145405000200302c10001c110b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 71827592 1250 71826342 71826347
    0xa0615120605040207050309061b07122001020303010b0d02090406061e0c02010e0405040510050406050105040b0d0203070308031003080406030207110609030d0509040b0a090c020c06130b0304031101020a 89
    0xa505120000400c0740315103480500c804d070700c14440040c003554410881040d150a00030000c008030303c05d040841010100454038542414a158402000c0310100300000c401d1101c100c8041c1c8030b903a81c240c1141a56544840040d440b400b05204e440f04424011031000c0e02d03580141c045401d80742d802481000341076141c0e07402516843d801c0895101310090310041b007281380e01070480c000c02160140c44050140302030034100000b812004104894502503140541c8018489000d25800b541c440c1d6400300b9203605100c180411590001e28440c41090411004400768070b0104410098980103112190703a9a00c40c010880c9140c601d610080400ca4005400101154547d02500300c603845038810685030300952080154074011000495031541001c2590b0406500a20003892031f00c1c40500302003088040c0c000007400704030044d8003003840c040e1501500d03503225a0602c0001c02402e4129026070030078050341c102c141c5400d9180542c000030800040424140350140000d201c82d1451a4000c0d5030301e01008000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 71828842 1250 71827592 71827607
    0x18051207060f0f020c10090b0706090b130b040206030604110c100606031a041e0207050709180c030b0405120a0f080106020c010e0424060915020304060e06030a0615 72
    0x41c40002a0316a4008901510403001c1c4983e10400754010014002030f1420060b4400c2010a03020034001d003048009030340c140381c074041c09103640100c03000541d80c1418246070a420200038001c5044000740c600540000369803048103074001d80c050390155260f64a80e40410001d03c812000c00441880115003510010000903544904641d0340c1820b00a4555482087e0159030f40001d044581c00070312111400942003650042d032150000c40d2941d60709030400302820b801c1340e20002003500c240c2c200300e1040c8049082401030b101c00648a03c0900c403e42d00c291030700d8401d030540d40402000d100c5044045410b200c0d0030410580102840ca403101d59809500c0c1010380340c400800d010a011502c06000060070f00e002040701054407206842e10840c3c54810000c01005241c204651980f8501d05d42c400e400e45500304d40008003605058680d1120141008007205503410171045070800c65008220a10041c0c1d4096030310751401c401a83c4032601c03500c0e02d0f01a01b0243c902900034105103003801803102103180d4800c01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 71830092 1250 71828842 71828849
    0x3030e03010b221808030c0a030f05070302120105060315100e04050709030209060a03120509040207050106170615060d18060c081e0405060619080a0c0315051618051207 74
    0x401c00000703030040c103800c42081903c01400418051000803a2001204010b1090305958680000c12b0040c041b403140454805952508c0000d85c04104211619a21810140541030886085080d850444a6203901a650028213070003040c207070414190850068100300a0b980c0000e0042c881448c4c1020b0060008026101c1070f0711030320403000400d8050030b00480704401e5a400140c82c0803802c118200503a501c0e40900043c5400540c204409000f1400a100e2100a01503407602c0111003022005040d01d08035000d408081d1042d05a44030b150702c0d640d01c04c00c4904848808030049516100c0000381d40c461092400c2c0548120b0074440580702036944814042e00c101c0c3e003d0801d850b802080702056285600c2100d0040c0242e00030808580385103400b6a1540400000360101120f058491400a08040340700714100c80d2502c40078010b0040010245800521081d002003c0281c0e190065000c1412100b21400500340718042c02541000800c80f801d04002d4040500660624203800400a41d280d00c0c511 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 71831342 1250 71830092 71830159
    0x13020a230306090f220b0109050c160f020402041809060e0c012307050d11010b060a0203090112110c06270a08030a2009120303060a03030e03010b 64
    0x2a031411400301016a4080c11001e0050050341c3ea07201d9909190b04005441c04000a00503d80d045500c405000e080c28581e200f0025450b00f03500d040c00000030344401404006040d50203003c400000c0707100d16003040030a608207244414054003400400c0c02072146800600c5080030348a40c01440400680049251601c83c0074100b1044240200d40c0c0d8503601da4901d803d00061204c2c2044445407802c0000b04002618080c2852400e1880d0b41d5992501902034091408102d529468041d801420f116180c03103100c00342d9800d45000c80c0a44001d4070b91041002e064144140e000300e2114900041c2d001c803001c10210080d1f181d603148600b401c00d036104000c4840f91164103154080051000e89031401d820501c90345002088a001169640d000306d40000f8116805295942c41e40e00c0c07122240c1c1481081c150840b026256920b079804203100e480c2880090351040d0780c3c020420700c403080e101c8444d90000c49806d4682004c82c10f070303520f001901610410f100c00e43c0c03105814050581c20344c0d40b6002c100840c031022 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 71832592 1250 71831342 71831387
    0x3030c210b030c0406060e0f03070506070b01031101090302010504290c0708060a0603081603170103060501031209080d0c0501090b01060905131107030c031205090f0d0e1e13020a 78
    0x4200708005d54007a4040c880000c6c642e960788550504100703840d840c201e200103090380e4009848201040d00b03131704114815074200141d44010010b10100205041c3d00303076801c4c80c0c844101c0b070468001a03c0c40c81240314500e800c8c1c1316884d421607071031405180150340351160f203030140c1e03124500d0a0301c99403811180600030107030041201140307444500f0301c01c42c0110b0f540b281020f03040c05110020a821400d02c3c0b5025002d0005a02c02074050003a000050303070180d441213000207280d505508207107100183c0181c4a60903c2002c040070702440303000040140c1d10f034409142c4500c41d86010b1900c94090300344540d005016482d203d002090043d0804510704c242c6805445002c081482848180280c6241c3c4099860043c402c20440c80440c4c800c0103240c0c0518000e04000e04890304174001c410888001b02c0d10b022080d000344005d04400312051102c0c0c0c035009030514002d00150780325800107146130400b101c1c3c00c130292683d40d1001c2540e2a0341e041643c4218005008544848600d5000340c0046e501200681814404c07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 71833842 1250 71832592 71832613
    0xf0f07050a030602030717040615050103180605060307050901180e070f030605060411190e010507170d090b090c01090902121b09040617010e0d02030703030c210b03 72
    0x2204011524001c24009501d461500d80b08021351001e40040c0401000c81000703543c8117032041500d40114420140025171018009214480341401d80050341014200318101340031465005a50454941109001480d078990340e002918144055020681101203803000065809140942348803115418609102206508a03155141c04503401851421941960203102045486e400036500c0710b0050000549584d500c2d00001c120b070400030140012114000204000540c00380b00008a580e00307081443c149810350b40c400130f07500ca640f104000c00c10004540c03070034a5111074000c031821540103442031000e4209201240c2c0c89901040c085404a0303c5803400007104c800a1084602200c00c000e40148640c03a20240420240001c414201d141e01d424001900d8a50311441004024000031034120303a8072078500445825211100e8817125203800100000403080e40100031200700c1c0d42e0618000800d0110142c2c04d54031240300d181c03040c0b4860410301c62443c940d080d0380e100000c84a012401c036054282c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 71835092 1250 71833842 71833873
    0xa0504020d020f0109090e1605010f120c0e060414211905150906011a0f03070c14010513020a0e0606221e061206060207060c03030906020d020306090a0e03090d02030c120f 75
    0x400c00000083cce03146170307980c0240303a10780c0509401829454a944040041070014032150019008002d500204a80421451070039500f101e44001d201400420050007001d07050340c40309a5014a081004c1c88401c58008025083c440899802020350790710701182085040c5030340c2c8460074020b40f880710164850f030050780c042d40010350755014240e00202e0700d182e5804204540945008000319103d4a1101801301044801c0c000c991151000074a482d003caa280d00402803548200e52052003506160810300c0103030744985088850140d041c40700780088180c401000c1440c40d48a9200e00075150503030b00b00340e6421407410240d00c1290040e90f81c2003024411400c0b068100c07551440340343c0240e840b41d4010050300e8024041c241c1e40502038200050350f80e44640340c007001e81e071040d01d141a08540c00000c03c2000d240514040386c10082080c0104090040a8205030362449081d0724613106400c0d42e0004021540d041110440b00b400240001c0d0301c02800c1d020295441c0514040d000341d0f802240d0151002c8403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 71836342 1250 71835092 71835107
    0x70b04020a06020f0a20130e0c04090b0703050417070507030605090d02060601140f030a05060109060908120706060b120610030e060f07140708120a0504020d020f0109090e160501 78
    0x1044e40028004164260759843e00103440180f03500745400346031903c50321960b510546c0c0340004160030004680c45100401c01d0707040c041101990351080c2d01d07080103100800c0250960380e0f4840c26606001030641c545080040581e002d6031021105000d001448200300040416084201c038401d140030700032500c910400c01e859841034044040142d20810005103590710515107034814400714044c07985020101081100d580d842100d954103c2c548810501c621940d002a0030b0008008900e0800e088a05064480341c555500c95040c1c023155a01144905c14000a60f00c84801443d0f0710804555904141480c00d0910000303c8001d80300e40320007100144154020b0003014640c0224001400c1555612000c2c0b0320000000b60a00d000c02525511070105c0c50381040041008a01680c08a9100c0440a03144640210010300b52613121b4104024000161140c81c2d810b003801d94102e0b501c241c0301c81c00000480340100240d00a000880c00c0cc00d90045807140441c40380c0b60a280d202e103001c4641e44541c015100a03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 71837592 1250 71836342 71836363
    0x2a08150907030506040e0102070c0510080115032703120e0606010203070f0804030507120b090c0a151103040b070515010501140d09020907080f1b09060d11070b04020a0602 75
    0x48480c2000444862282d80196030001c002400019043c00c1c1620050032a0007103081180c0303040520b54140000c4c9420a4060003990151038060b20729070500e030001e26100e1881c4103a105242d258800741d1190759044101905044140410140d4401c10382030080140c407070010000050b40c5400002079502d900414058854007041e0000c0d07140114559801c020481800410344008806204c08400038406008400040a4004011000101608003a514020050440c03031003070b4405268002287c65203120300c030444442074855018054280c8007920504561500035105000004012420143c1040030345041d43c001c00495105101d07260390440d0540e001c1c000c441c042842c1c0e440001c100c82c00a0001c0a044144180c04503d40d03080358042121038005840705008620304004011082400710400750344800340ea00c50390f9107030075144034444140c0710300c038a4240a0710001030220440c24681d040444003900e412011541c400303180c01d01401a2000b0b07a8104d1042048003800100540f0015040031503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 71838842 1250 71837592 71837599
    0x405130b01140d06050a05071205010e011202130c020303150405041e08040305060103030e100806010807110309090a061505120105130b040c020a110105070c031202012a0815 76
    0x10390030000070302c12803821580440da0100740c104902c00050758900499004040780c403008141c6040c5004068000000c844500c1d12062500c40104031082c02c4030750a0741121400b1038200f01003a654004206080c9681c00c0c0c05110505044443c4500d43e400002107101e07107413451600e01412030341fa040100365503040c0e40c09400e030000303981d0711034445200e48003189107180315895417450166641c0d02c49040c1202607100b900424445122007100317040800c03103545580454a04400c080c03030b001c000a444801e014042004004444204040402d405c00441d2450000140201c180c0d00c1c1a0b6a982c01400e60b5020354048180d600080784102c0c0e000e14152200342400c0d8400440d26030030b000c140080c85012502141d178080d201c43ca904001e85881c0308030390102c041c950260110305100d040c503042a00b00d007208941002030070040345010981003c24001030329031101d01d0200c5880c041504a02500c002145003600c84d4401e40220948a20400c136682d481c1c0c02522082051307a1541218124041d00001040c0c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 71840092 1250 71838842 71838863
    0x3080301090b030a0203100603060605090c03070f020f12030105030d020607140c010906050f04020910061d0312040b040e090712060b01020a0c0b0405030c04020a0c031d03011109040513 81
    0x50600305401482c89810050201d036211107281e0002031030000d04c0504980700301d82c0c0c0d90040c000d2201500405c3e01418081d6080751990902c00740d00c802c00c1c0300050a22040201110b00480414400d015124a810911342101e080c1c104402c612002544284100d5100740300300d0507070031940c9001081c910301c10003160321407040000c0310f21420a100e80c4261050801c0e5541c0b012928001045407060038058405408040300503e400d1040c80010400506401d51500d203046d4100309180e4000c1101c010b01c078810051500030088079010a20b019481c89a003504640042004506280c00d88050411601c3c1e942d0201a6600c0b402c20090300e80d03a00740188020b41c44060b04140100d80a0b070040c4004e844103104030b0703108005036152483ca41c1560b40140c0700d0117600050400c441c0c941004441c00a00c0212411482c2028004000e840000001c6008081c03105102d5108440001c5c0080c010000d00007900a10000c200d02a005500d0ba0103461010311581c0742001160301007a00d01c009107249a48900030390b4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 71841342 1250 71840092 71840099
    0x1706030601051210020d02030703150b0f0f090a0b0a090e06030a030309080909070e010f02062208040e040b0a060b19050c0f07090b0307050108040f03050a030b31020403080301 77
    0x40d0012043d00d2101151245030181c0c19000d101d03100914203c03852400058480c10001001429208035124a080b1104c600805001c042c1401c400c0b0340003403074074080140c1e440000404204090142d15a580d0780000d00070700000d03100100030001d0140c24dc4a540c0e4090807a00c0710000b0560200948103981c2560040301c0740c0000030301943c001d40ca0a40a404000d0408070f1000014003242c504981c100001100c0304000c2c2d2035540c128000003000901070000d09030a00e0424141c1d41c481c0f400250f0104441c000300d58801c05d005202080710041c20807041e03050201d141904165200c0c41040d10042c0c0b0303540c5032800c0010014883c07001e45401202e440403409840c1d11f01902102d881e0003d404054180c002c001600140741c07000c100d040000c107901200458001c845104040c2400010f41c0818144698074003044001140070701541100341d4181480342e00c03541c00394412002000702d110800d400c00340000c559104600507032903a107620031407001f50742107100c402003001c0309034041e512004242000500052 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 71842592 1250 71841342 71841349
    0x4050606062503090501030c030e0c0f041e021c02070302100504061d060411041e090302010204030f080c0f031602010c02120106032103020403080405010302070c0503060106030606170603060105 85
    0x1041118000c030081c280000c050b481140510110304000c401080c40f01100308150358150140d02840155410100f103004214500036494150911b009032240b1010310f048485940c0720f40c404511061a090b86014450752000d21200a43c40842611040000c9d50784d140c3c0489064000c544946905178060003400f40d0020000c00541406881100c1158444d41d25002e001d031507240d10800c03040054020562803e103410105d2a11f01d00500e45809282094800ea4000c03404660a2003030710003591000501100d00d003001ca0081c00786801c001d20300300400c1012400d105c0c10402070041040c41e002541c403070946481c1c03115a83e01c10000000000e0601c4140f00d4095806046041d10342400600040440046098424212150398000f11611100a548410701101c2d150301c071000807a15050861915080da117606015000743e01c102810103400060b02c108004000401800802c005000c40b1400e584401020300a00110300983c00095080300b0700e04400c202c00b43e0b11601401c005070140006908103000d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 71843842 1250 71842592 71842597
    0x12051c0905090406111c0b04060510080a0e12041401080114060901050c0616020f0303010308030a0b040207060f020408100204050901090b03120310050f120d050a090801230f0405060606 81
    0x98a81c03a85c0d401c000c140702c010100091040c0c10803110303000302c002d0710f014007401103c200b030380342600a514020082c09507807035540035110b4002d00341c10720070340952b04c103038404004d84042c0048080c6405590030718010016490094015649100c5400c069143c2c81401100c0e2401e0901c81d841c1c04100c600c0e21111142030a00050000302c0d010725140d03184c00201a5518502101542c0e045c0c072480c0d1420709200920741c14421035002c1c2a41304d0142d4610f51460301c07003a046000240101410a50716450254603980d20740c1183c82c055070000d010300c07811050806500003504288200301c2d1500921904440d5422244200e80036200018150219139003802c6128009201c6448a66003512a010000b454032880d04040e5100d5203c1c25040c8410720305207024080f64000c560041ca018810102071035060b02c9011603a0301c105900d51518039120b0300003443c2100c07070b500240c1c0b11000c01d51a2988201c40400c1c10900c0381508007449084100503112803000b41d140110403035000d40309800c011302003481881c04000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 71845092 1250 71843842 71843851
    0x3060a0315110f0705010501080f030703030515100207060206010603060b0f090105121510050f07030c0201020c06040f05040b10020a120c080a11010f0b03070506030c0d020412051c090509 82
    0x10b48800d0340c0c0b01012aa40101040d000c0700ca0040303005010400240542c1d8050012800904905150000600d54074015020001c050644400008501801420f0902d00c4110f004140d0069180061006503c0e05010300444005008040000c560359020740948021508000035951515030000390441481e000010500e040001c1045042a0006c0217810070703002c0c0c4207a042c42001c401001080125515580c00300200313102e0180240e050090300308050703840b040d815052070707844c9003103902c0100e0030030740013040c3d0b5540848082800b08490214407002d42c280c4509440400440c4c03181e40130000504002e0300c010313006130700c020380c5180002c509014030082c0d14828200041400616a22101c42e070f007009007070308001800a99800682c20003400b600044c01c900c107108100f186000c101203604d0300050300546018203000800b080e007843c0301000300d551034680305e08115101d54440014144114030f5034000c2e540e51007003500c1266881411030001c82e444401b51a0203001c1e600d4030041c000c04000041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 71846342 1250 71845092 71845133
    0x110706080a1107030909150302010e0d03021f0e0f07081c0306030f030c0203150c0423040c02010c02070e01080709051801090305091201020f0a0c0f1b05040509010203060a03 76
    0x7a2890b40000c81c024200c0b1034400d1700c40c10310460600c00703c482291000e11000500800c1d5050030001b43c3d8010003c03010782c603c191485200d103078060805a10701030054003010103400a0038020030300884140d1040604201a800b612418180e00e21034641d25080e40c0030381400c1d90000541e04500712000b01d0300b80c10403402410040303240c59917510380c180f00900c264820b03004281010034080840c6000c3c007480e42042d030400308050441c2001c80c902607641c06203001e009280400e003081c030b00044500705242d2203c400300400500c01c04140d000f00030701900c80035440368054800c441000c01c050448505440c103840c40240101030141c50006480c010741800b410f0f2900841d04948204a131100a01503220340c58041c1e282c1941d9514510240000103d54440450307007a44148003402201c0c511404442e0000600e241070039054426040224041c20303a00c00050606098030510610310f003207000b0504c00c9503400c0760204031a03500c0c04003076401c5c1d00c0125130181e40140700c60800d200042502c15220281d9180c072 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 71847592 1250 71846342 71846351
    0x10f0609050609060a021f05040b010506030403090603050a0f0614030705030a0807120c020303070303050f0604090b06090601110706030c0206070903020d03080415060e1015050d2315010e01110706080a 88
    0x1007110a10107c950040902641c0c42d002044180024040141c3c010401664010705e14a00794500901000d900d00400c020141c880000c60f0507070800d0b4009032540215400d080020b0303139440c444a00c0d140d20410380c0d0342c001d010311400041c1034a004900d0301c8400350000205454015903550b060f80700300171204240103020000c0080c10150300d080024210035442034400244a0400314900b0006880050010b44034904141800e80010712100d6000c2d084001510f15206580307d000c01078034040101c50703070059144520b03e0002800755041c1c00650120b94103070295840768588140840300c03010180006900400105044000684669581588107015515078a1504c065806440564503a0f50180054a00c4441401103820443c0340080c010018400d037880300d01f5160b0009040c0380905120107401aa580c0040d144000314101c02c071403101940c1703c00d240ea80c82c10340c81c101150341e94040d07000e00161000d043c081665020343d0382420360710485001045070a10301001141c000e50010842180943c66 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 71848842 1250 71847592 71847613
    0x303060e09010507080f070f18030215030412090b0313020d0209071106010b041d0a060506031303030f0e0601090e03070c0602061b031605090102030c070e010f0609050609060a02 78
    0x86100580076069007030012030181000d0704000c0c2044c00150500b00c0c60310303221041c080342c19001002c2d0720038000349080800703480d0808200156010402d600281d0882d10031880134036208140c80c015403182e131288550a03c0005002c600725400746c035500030390030181e02c100081208904190704020500b88010180c43c07884400d80e0100b440745405541071000f00e102c03613a5010312800c05000060240c540020510708146c508a1701c0507000010407030700f1030004a00c3c400709d1080712550300701101808015222961700e041240313004800006401c1c3c1540007a20740341c0a003112520f14011500303415088001001e80d40d0800384003000520760000c2c0100a071004104a000060a0700540030040900783c001d41242c0c81e01d0305490301c0c0144a0f500da5100401c1c2002008852002c0724041c0c0b40b0341450745443d545414200780142d00d584504024003086206540340003404850082e10207040c1e0b0400c00c0100c050750354038081610a440c1074018158007081c107010b04d5080c1e04040018240065640c8100c84d0710005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 71850092 1250 71848842 71848859
    0xc0a060e0a061104080d020c0a06110a061415040207020906040b0d060e0303071407050a3c020f0301020403030207121e0f0201031514040f0b030d05071103030702061204030306 77
    0x3103c00156846a0021408002d026800d04c000c800a84003400901415025100001c1c024925402038205100a0340600c0001c1d0204100108946a0101c010070000710110300040c007100c02110038502c0402080c5150701d807800c00340240c5d24180d0780503120280603242c9604000180400c000b065400804040640c0c003c500c0034002c0351070000110028640d03074100a80014840e44562011400c002003c018510005000081c001d11b49908000f41d0004001e055040c0d40c1044000011864001800c0750050380d42d1040c98903500700544200c682c0249038042c6001d050a074003036444058007581041078104031140014030a0040720f8400c125046540d50031540f5020481901c003c141ca680103101035640c210350f0540300c1d9980400c01080000040d620700300300b411303500c4c0c80700c503903d8025034880030b031288180c2140c1c1020740380c0e1200400b03071b40d44c2d0240b220004019412010056400003030300c04000001d41800300c2201c00c80394004c1d160030310300350019880e02c0d01600054011030030580c0c1e03914002210030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 71851342 1250 71850092 71850101
    0x1e06070e1c08040312030204030519030302090d03081806070f050309010e0105040c1805060607030c03020a140a0326160219150b01020d08060f0f0901060203120106050c0a060e0a06 79
    0xb44102181a201c9086040c080510100c50501c0002c0c140b04000600105200284107201643e04514003181810b00b803500b2000790103040e00258110310040c00840805030000301c00341c070805d415980c03599840e1200801a60f103d10a44030b40300800c080155034611a031155005580c8605031030000724008110f140800c0c00c4840407601510000d901841c144610601480b4503d02030130349400130300c854146a000104d19100703611004082c808040e08070b00c1018020b10a40510581041c40c0041440140500648540480700c0880c00104d0303086c12090003460141541c0180e0540858222182d5250f403503110000c0c0500320041c0030352103031140c1c00d5071510919910b40d80130792084d0700c007004809200c80e41100b0307035a21018513415500b01165140605a10a000700d070300403003c1380c894043c80640e50208620000410581d504014400b0001c40d050f80c0000c02071080d9500140904aa681d903220200c8240c011881105459044000e096003c45c015410842c00707454036109079103080045070707201d0080300c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 71852592 1250 71851342 71851399
    0xc0e0607030809060a1a01081807030b15091303110709020301061e080402010c0303150302030307050604110307030c0b0d0209040c0908070501020102040b07140f06070905031e06070e 80
    0x150000b010456941000e016482c0c0040340304d80284401c4200034040030400c0108134060341001860b40004c0d07c124070f5038003820161603007902611403240c0c50381041c40079814201d801102010484400031190b04015080034405c1c80340c104200d0108281d9a0b044401d16000e061940b064801c103200401c0104103803000314000d0210780c03240c803074102410740150707182c3c503072681d100081c00f00c011b0404c80981d8210000e00c0718954546400200c2159120680a03484020341029400d440003140d41001c200300000e800c1e00460180d60103660708040101016510412070100614840c0d44400401820092901821004441034005800c2121150114089a17910407004e0005100403004011400d0140040b078083c0000b880254605814000d100c407031841043d10040c800e841151424101000a002d60403440030000251105418a40c030000c080b1111402014801d00444165902c00c00c0040500c298040c40d940281c03640750303500f54090716409540760380140c100260750281c0d15651690909003030103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 71853842 1250 71852592 71852597
    0x13050a0213120c060903030f1101020c010609150e010f030803090c042f040602030a0c050109080a180801020304020916020c061b1603170706020421060f0912030c0e060703 75
    0x4020b0603090000402200342c0c005070074401d04a4041c0086030340041c41c000e1104182c01c2030b0740c28107103442115009104400005141c0d5207007a4012030b80f441c80b500042401c1f08000074074210f080e02c0b50040784800101b8820b820300d46004c2e49003000041c92481c0915444004d407030941e10040e0b2a0f4000c202980c000c1d440d0724007080c3d00c004d848041308190041446268110111203400c290a00e00083d5507481140c1d03850042c090900d040c90b0400000350402080141c1c09030750141c07201d0148034050321101d08207038252911010341e100802c002c04140b0a684c0f003541c0050044410342c844a61043d9a49641d00000c411400741054010041e100d800040a1030396160303108600303c18030042c034941840244e40804415000c004820800300d10401403034032500083c2c00105d0798a81440c80d100000303106503070100083c0f5040400384001e034003411000c000c81a004603000c0c0803007002c480c00c550031aa0030120040c02601c1c584400c2c0310b0390303109a01c8941518501d04185550901e4600080c25641106804800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 71855092 1250 71853842 71853869
    0x10c0b040807020316061d101209150203060a0905090a0b06060c06090c010e0d020d0201141207020a060b040c12020a09030203030f0304061d0703081309140103120e13050a0213 77
    0xc50f6440b4640d1f06655292403100c000007034020b0000380760b01030072142c40c40401006541c00b150808140c0e0050311070941c8855400140c03100394105501035081240d5940c45880405800140c0a00c10300811780b04105403c00b0307040007441640c0707036014060040d0105801070b07400d00181d0840e060800c02c150048a1401c024500404203200041000390040c0e10107019150030141c8078010f0f15582c80e46007181d40d090a00655424030114550090b005e070307859851004607003009100242c2e8006c50b06210090042405102c8401d5a0701404181c1d020012410001110130490b01403210f29603000c1c20b0303441124640344444542e0385d00060b00e150800c03030a00666490010074801040b590b8441d007800c0004445002200c81004001d10351210020311014105203c0080e039070161010742900b5401921415204000c5000070111040d13403102c003404225681400003890103002ca0040c03000b4ac46101000380300d607100044000e107007000b130f00f0041c1101d03002c0380d02031040a501007602c1b81040d0242c803400c2c000c40c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 71856342 1250 71855092 71855099
    0x2031204080d151e080718020c0d0c03020607030209090613020d0212160c0b04060e0111040e100506040503030405010e030a0f0b0906150901120312020c030405091005010c0b040807020316 82
    0xa039280c0b45000360541e2201341181080030040105044040346e20300411090340307030924007250f000ba12920786041d00a00a181801d241c0d80e03080790701203c6090107a401c9901c262389118042d4103d2051982042c2e2060005000a55901d80040401100b040724a0098140407451280505036000f024102c40881c01d41c0d010014880960007000052600c1d030719040d001e0507c02e44030320240303020150000e01003c0e20740a2400440e20250803440809440c0d810480c0d440303a5580d90290088400d4895071111302c05074500082d146002001e94080e10002400f0f94603080c9000015200d1140040701705406014590242d0082205081c45d051498040c100b640e1151404072481030130f04100074030404a9000072111000513499030341103141550070180c0341d50b03038a100da0b083c2030b20b400b000140c8500c08140001401498840084058001c445d0145c41510090720b40d812001036004641c09000c1c009100c00c1050b0001ca000e500100d900903000d42e0519207444c40e150082810041a803115040c540c44059042 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 71857592 1250 71856342 71856359
    0xf040f060c0201021c1a010c1b090207020301050604110316140a020106050a090606050d090501090b070905040b0a1815090c02030405010f0c05060601080702120d0504030e03070602031204080d15 85
    0x30036400c500d240e170800c032600600080d00d0b0010725480300541040000401001004012200f00818000001216001030b030703a852641c0180d03120075802ca000c3c1d420000441c09a0421b03020f0005244108a045403c40da50f6000c1c001a031f03074501c110882040040c0d0380c003012001c10351004000d89802a400810b04a08200c01e001003030210340c2c403040c0014903004040002d203500005031403c080a240011611424609040d80034100011000d44401a03c4044c005415080304611048400039501408850202d0080214500d86c40c8200c14511031440c40c4090240599480705aa070400c08030003941054940039024211149442410b002d07900001c1e00788995a00600b81520480e0a07103041d058502d810355507d519904040c0c0094188030080022404440c000d0040894034014800d005840700004803054000c1c107000d84e810360200382500c100d141a400c011507a0703002d031406d039001549016010842e0106011008009940d02d100a012201da19001c41c0a45003100000000c204035141c2403500d103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 71858842 1250 71857592 71857627
    0xc030c050a08060106050f07031e0e030f03120406020a020f03070602040303020613120f0e0d0606030605010b12040b040218010e060a050301020a0f030b040605120f240f040f060c020102 81
    0x81c2c0582d5024000400809600800b11000c50348039000c0c640d00c41c0c0e440c7c40c0030f403041c0420fa400074038070036061024000d10340e078030a0002c00e0304002201161040114034101c0d40d243d219031b0940401000c42d400000d000300d08146c00804807002640f040380c00c1c2c60000c450030707800c41c2c00c1210b00301d401680014041084c1581003108035046100f0484010f000d5074195501540d02a0f41d070090414004448100300045000d03040070450750b80c01400403044020103240c020700400140c0002c5600900c0c1100200385109002c0503142e5404420b81e4455172070b00c454030755043c02e14005108990061003200c4c40d441c2c9880d03d582141c000c1c1450702c44040c007410003504110285001e50051802688140503002c5942ea016851600720701c058140060385841d00d80c0804c0180415030407054001200c440000c2290130300080c088560340c4900c0607140c28140b202c0070194281400f902429641c11018003103426102e0411044e130308240724604039862005690380e2901911828680c4001507540817032603170f2400b030041a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 71860092 1250 71858842 71858849
    0x804080618010c09030b07110d090602070e28020717040303110c2d03010e03040302090a1a121005010608090d0329060d11180919050604090c030c050a 66
    0xe10030004100c000074140c04d840e10002c0c10011079280401c10703582c0110003a07074481340e982040da1003982020f5070113450b0390400d100b01c0d4014400d0312000107000e0001e81040e4021aa0f1200e90b40c403c00c00d541102100958905045207019400c015020005520301c2d200c480c11041d01c0715154445186040141550065425206842c3c1100b440003482c4e540f02c61654000940050135921100450306100c0c04d1404070000c5e0701d815620f0710541844200002024004892084404c9070503955141441c80503510507008218030702c06050047c12862501c150303003103122191001213601c4032480542c0c100a40e4020f80c03040c004182c0c400b050200b0301030280011054140641003e0050111151050503038250100c0311000c0310b030b42d08036401d8080ea21b200407107403802c503818020b03c02040d2602410346660700044c8010920840090b00c0d41c1c940c207141c0c42c258420301c5042c000145400301d20700b00340050240108451b501c50f507141407034400a00c2c0c1038900d0000d1400b4040a0400c41d040005000303000310180c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 71861342 1250 71860092 71860141
    0x120f060501150c03030e0c09090615100f0503040f02090a0e0705190e18030a1e030e030703030b0a050a0914070507120c050319020606150c1e0a08040806 67
    0x12085490580242007901c22a44c103140c0001c1c2e00c046620064104107011104645c0014201c0600036261400034945020b24000c03458000454603032010041d507500421f0324080418001040c07100464011805150711a00540351b0400d06181940012401c9004651081c211955041d032130540e028100601c01c05000c054400c240c140600d8402d01560000c240326444100c1e2028002803614100c140302044200e000c0804c6a840702c1d04502e0141c008102c0150002d02d05251000307a04a0510a0050407003d444810240d4903000c5152821009441610300003600311001c1c80c0300150710b44680728000c0040070051800290700081d580400440c14003d8a40d1301000818400c06012604680d40308160561904011310307558041e24000b03007140150f4400341c6e4403a08450040344810340110b0031174450312089581100080b12025070b41500c0c0202c1803c404254410580c0b0816181d60001401c140140300007250703a40c280c05d03a00d001c02540990402c06058100c04244007a2401c85412860b40b4440362 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 71862592 1250 71861342 71861369
    0xc1205090721020301060504050705040306050702120406053103021302030c0307230d0b011b05030405040221010902120108190201050a0c05011407020f0705130213120f060501 77
    0x2280701580c40b802e00303140500046500809400315502580102d0040401900c24801d41c80c1c00c20010300740703402ca44020f8404034240700c0001c412900c0800d00010b00080701c0e041904060521400325440d80000c0c0b000031414900d072045500b641c5440b0f82d403485510221100120079420f61062182049251504002d10360052061000036081d80b015664400309a107082c0c807020004c00c011001108885448007459040007451a10b0108c403908103c078071103420f8803030344840f80b0709081401c0205040040541503030020300c000c3c403280c2380c180c000306030700100c1a0700884038560140c900c2002c060b083e0f1128200650015100c684e000c0d460301203500429604020303001d07c0e5a44100000d1228400300028100400011206aa58010324455801ba80c02c80000c200c610040700c0d00301c00a01094413102c0143c450300000395800c841c006205070540c0e9001d40001c0f2640070101c1032002035004030b2602c00510fa220f01022403402d032607039210320f40b050142e00803047d00080c80c14050101c0f04180c21201c003042e02d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 71863842 1250 71862592 71862599
    0x6010801150602030f12070c060207050c0f09061f0c061103010f050121051003051b09060301180f0201020a080d02090a0e270c03010c030e070501030b01090312050d0c12050907 77
    0x850041d11b44180d14040180c40c565107852007200d44202000000f03003620301c040b842c0780520a0000d650190b5200680c2d00004a440a03010070181040449420b58481a002c0151400d04103120280300d4404050600c07140001e050382d2890207540c003814803c115203001000400071440388000c1100100760070b0820450a0441480e9140401d000c001e180270065211404071b0213800c00d1402d010001c1d500b0405440d028662007241c1c010380803024280b24881c90026010030300d00d260601c190380000401d200701240030800707a034036a03c102d03104034001e07415801002c100401003141800284400015031000681d00d4844504114000c0b030340c1e800c039040e00e81500e0100411070030071190b50070303030074140c0b04000010300da400350514a450301d0f810009426500340100040c1594050700600300b08034114054401d802e80f01c0c401101192110154640026888070080011500864a40f5440d02044c602980380101a0074002c050321407000070600001c1c0883e80520b0056040e210702c0384c104500c040509925440e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 71865092 1250 71863842 71863867
    0x1810080f0907050a080a0501050109060b09011409041b020d1d040207020310020409140108010e06010303120906050106170711031c0204080703030e1504060c080705010b030601080115060203 83
    0x400600380502005003a010a00318203007040064010300c8002c0850a0194907081c8040d154074800703004407115030030030001150700d2885004010a07a903d210105007031070182c00046907504285410405d04810411611020307455501410005c804014440b6454000b8035400a00d002955a44003041241d00100301c401c1040000c1c1c03650110030101c034090380701d005d40c0c00000c0c144607200e210300640741d200080c0020340d007500360003000d00f8044070f05030016583e07655a0003600303990150324207400c0394204000620000307001e084c41540c2c40c480d030403000401040315a10789040354030a0f00810b000c52441c81125400305010280c0c00d0380131240e4a403c420310250070313400d10b82e28080c41e4482406030f846c842c145092054180c0c1901d004140000c11a0700855580c1009000d407050412401c1c080da40805800d402d00e4110000c8600701c95842c1e0700d020000b0420f07100d00d40d80f500480811511075407600911040d640c0c080049a01a013080c02c00002c40d0100c03003070b2000400c051544035405542050000c03500405 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 71866342 1250 71865092 71865107
    0x80708010b090a09321b090103060519050405070311010e09010608070c0b400201080c09032407030c02030906250c0302010e0901050d021203160302031810 68
    0x380fa00004100d500b4507103030090000d0540700d941407050754050403d00342c0f0b4035010800074801280d0400c1d01c1d40d00b0302000c00160100d0f90954010b4108680000400000e00542c1c4042e911080102e003480410040032146401d41d00141c3e8141d03069449610140203001c119042400003070030074200106107003402c80118081103014443d8009210304680040c00190003080c1004180703600c440c48504524000c01d0085046090140b50b542200c11542159082c0100148407101900025a0079020175126070044580341e40040802400b030600740403110325600c01304203502c8030401040400e8904451400040710049004106404150030040804005134000c41124500e810507a86643c3c1c640c46000300240c804500640144400c11203a011424030034420001d00960740b007665940c20811020041141818080c040c8962001c41d41519070018a490701c82040766000c2d400030740b400c00c8104810701c40c081440380001c1e409604000b0b068102c1c0c017901440c281d001001102c015004c03d00c00e4400038501d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 71867592 1250 71866342 71866351
    0x30901060518060f1201020c0f100204081209421c09110d030801060207081b0d030201060812040518010303020303040b040f050319110d020c011d060309010204080708010b09 76
    0x30391007010181120b1700c0d82d055014494404100a5540305411020070b59a80486080d0301c0c010f00030380d02966280100f030300854040321001c200600d240110144d800d181075009a213a140c0c0400440381e12134a0041e04a15560005900800d00c10388200300f0032004100b56201200a0040208000140300441c41b81d580030f0b080040700c40e0000392010a803401d05244c0ca090b0300441c0d442520b8aa41d1002c055000140303a0503194241d00740e4600980d21024140e48114046042611141e100b40c402840e0070449907030100140207100101724669540c88080c01d119410303504104105000805001600340a1607043c2030400320768480c8102d43c51038400039142d0102602c002c0040c00050081004c0c010b1403001024519044800d49540d034841c13030346200c101c1d13001020700b03004030b0302c4120b407114031110200313407508403c82c02e80180985240f0703c0011100700e000d041509040c46917680700002e098443c800a103118190503c00140d98504281d80305d4070741070280c2d000b64800d81c10320007200315039154403c101d03800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 71868842 1250 71867592 71867599
    0x2100c0204090203070e04021305070806060d021c06210807020d0c080601060203031e07090501030f1e0b0102010e0706050d0c03061d070e10090b0a090305070b03090106051806 77
    0x221041840080c0203400822000796061240101c0800d603120f04454441c051482102d0880c203d107007040a59003a00d80495011003c64402c000003100340c00c0400080080328007210b401072030300f80298903103a90718000404020103281e403000c0a02a440c01010407031011010407203a40f11111895603050403510504a009004840f00003d05040201d10300c8207070060311528040c1c800c2982c580034000e689410480340350314000c003403101100d505c036001a9602d0180380c89540d4490803a0134640150058088164030301030a0b6a203031030405603001c2030145594092054080810703030a00c24800242500c1d0a0300b003208003074000e64400c11802da0040100c60907a0096040030803600e0a4a100b130300140744a0384560030350196040e5a0b0150210040b201d8442d0034581c88100c0011502d5051000704070700c0d8805000030400c620420302401c8a40030107490307040f0306481d1401245403648e8400781030040991180d030409030080305101c5c8400c070a001d0800503120540301c100151004010031003002030080c203c0c900 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 71870092 1250 71868842 71868857
    0x506070309171005060d0302030a0e010e04090812010614030a09020102030415210c020d0c02120304080703030201060e060d0605071814040509010209030304030212070503060f01061107030210 84
    0x4150050070820000c2010301540344060582c20842038450200040d107030402032811000880c01e2500500c20f910050301540298203110b00c95405590074034101600d54180041a02c03200c0d81c40d40c413405082c100764441c010158542541e400c5414140c0410703007041c014420151202c4251191070350549a1245c0c0f4940d0224241415000603415445140c104910310106840030a5a840d0016141c4001c1104400d00700c2000641810f844100c80d2001c84440058102c00030085805208503125122107000a0216566014003d842031444d4043e0740300a100da000304008009040e028030a140003040c80300001c00041c41c040300082c0b942809103030000e100c1696040400c00c9a0b10031602c543d090824403c0c2da0201e9601c4016088080b803240069034851814040054030385030041c020f58480ca08090011810300c1c1c255400c010300c982040364007504c80d101d480d0002403a55002c004260050380c98041881213035050490090114840070540b42090340900000c000503141e0100341e8107801d81502e403c20 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 71871342 1250 71870092 71870107
    0x606011206030602030f01051008010303050405310b01090806010f12060b0907030209040c0302040b0f03060d05030a0c1e05060106110c06040f050414091005041a0a0b100504030c0506 80
    0x8001c01054001902081c030100400c40c1107403000500078161b840c1244e41452000e101d007001c480c068000d0000400081e41031000308500e00741215040200d01001d8001e681c1241901916032080c46010010f20080d6140c207042541540c00c45080406081c1000103072015605009121043c3c48551140e400c000d8105e08104050080a0344000345200c002001c1e5040340c00c1c07040001300a50003080c815445149007001d621002c0d4001c0c401c603021110040c0e08913041250105e5103800c2078000400c0c0130b4100300c0d543d0808c00007920a10040800c0c0400fa05d540b44000b6141c20903149a0300340e03001100d9818929204140426800580c00d07046404a180030641030301040c030a1801c240b02080110342005c00410007182110514204400f981e0090702d08000c00c0800703940c29046200f0030354880c00b01c3d82200e03400b05150390706074002a80c41800b50f140e500c10405a9180306c10182c20883e0390700380081c1d941581010501d005006145402d8203481c050342060b0540c0c1b20020820054030072a03100f00703030002c1c410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 71872592 1250 71871342 71871377
    0x7050a14041502060f0106110c060703050708120a0b0405061305060307080a03080103112704020f0a0801020d1a01020312060f0405010e1008070b0f0a090902030c0a12060503060601 79
    0x68020b8407451032001501e010041002e0760720402603410700307a400098400405c4062042c0050008400d00300c00a020140b003010a020f42940308030405d03400c00c8400c110100100d003401c0018804504440304600c464036001040c00121107442c42070314403c1c0d00f042c0a2002990b42c1441c0381001d0602100c00080c103441c1c42c00000e02e4001507a210308031601500030010107040d0802a40c60490b030140155920000600007006500c000a0a0016080b11805070080503040003210041d4020301c050500ca2206000d03c00046c070107a071a60004c88180e40000301c040420340f160080c9642c4e504066000d100e0301480c800040c0d107a000307042c00700403100540c0e400903106a5540d1181342c00b011010300704000e00e5855002c0b1500445044441180c11603540e07a001840c0c0b000054443c040342d143c00840d03801c0c03039a6188080e403158840401d45040080c2200c0101e502e201e9440114003959045240075174034540000c02034076401444201070032582c42c1010802c19603d01281c103690116092820700440f20306030701607 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 71873842 1250 71872592 71872597
    0x20309070504050a0906060509010308030115021002030a0204060e090c090d0809130b01081005130e010b10031a010806030a060c050c07080105040c0e04170306030c031501090e0607050a14 82
    0x440e4032034100310a012400d480c0345e000a21050007000e0a0048031780300e106000c0f01810038480182901030410040000c6050003004068101a0784182c94085109101d484240e801c107440c03c0fa504c0e40c0c001410003000740c00203040e03c0d05101c1560940454540f140e1520000d00034241058050162070700840100411003080302d01a860040c5100382c070758922045032008100384640715012508110204106c840d20786c00140c2242e80090100c420000042c114602510600e4200c001e0356407503640340002503a0303072107407114545215500050003e40c14000c0d55000c071222001c1905106202060041a40340891400100c7d80c000720082900b04613054111014810304203803070001d00a01c10049190b100c190880ca0080d40200d0400d240907448614030001c01138140d400804224540303070400c03c3d00d908100550fa11440c024152451103070b1000c007107030500402c030304a50f0490795801c0044c000107030a88141540d042c0050010017542ca410b42008d450740c03141405050074042c25100300d90035003031038004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 71875092 1250 71873842 71873849
    0x40e011401031e0807060e16030b0402040911060307110606060a091517010806060103050a05090607110c12030c07150c0f170a03020703140a021e070e09030309070501020c06030a02030907 82
    0x855540d420f00c0c00d01c031009100401280d0a94050100c00c1408c01d090026401e00303032a044403240c107040c0c99a03070030080200244142103e010316048440780b000d55504000e1071098503d910b449a48050080302182004001400c1d148545420b02280140f154407070880810354080b02a242c010901ca2802500c0b90710f0b41a8a081d01d0a22030400402d80207404141280141c00a0300c0900c0181c4403040d8820680e0707022103241d0720950012000400c094480c59014030003800d12801d803075a08200d9404142c803850000900c066a60001406c142040010040e540c01400100c0503c080b18840201c01000c02880c5400500240c040e82c1518060200800710200c2d4010002c4a00341d403901e03000000390282d0420007050b0f0100f4558000f0030894400320045821141a950280c2130003a42d07018620862484e054809a052048950100300060302c821824000d402420040d92a840c2c140d10051078580d40303400443c11504546150205a00c4134001e4a4000d10b0520000d82c599a03030b2504585040107551 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 71876342 1250 71875092 71875103
    0x1050f0d05130b0a05040809190504050a0603050f0307020a06050a1209030903060513020f010f020c120606150408120304140d09050103150f031403120403020c040e011401031e 77
    0x2400d002c005104103542c0c916243c0301e00030040d032560b68480002c0c211101120083c10f100c03010484a0780c0c600e02044041c034091020004d1411403604c42c40410229281202c5185003642e43d03010a1052242c00c00c00700d940101403134021441c10005602065200406110345010b000011842c0300c0c019000c3c80300e45180b108240b204001540e51400e004240340030510054907514602804103072039090610310340d102c168015044400822207800112040a00b44060400314090703800030100341e43c0d0b820100400b0b890050010702860402c50f0030010341c0c0502d01e401d29101c000c01c0108000035003000c40c070070003502d0340094000d46980c1c0e58140800b81040d4101c1c215280d0051001030084241c209400e08207581080e6020030041501c3c103404008078034180180081c0c825010810400070740700c1c1060a0412000c401601d0070581051035801d544201694114050b82200200b0400b03820288a0200c0e1005008024071042c00180e0020b007840c18180070141081d2000000b103100030301a580d15250066026 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 71877592 1250 71876342 71876351
    0x2060a032a17010509091e03070204050408070209060607030c02010e06120a1d070b030610031814100504021011030f0a030e0f07060f2a0f02120d090501050f0d 70
    0x40d9004007a120030700c40c15202e061040c400800c4904010410b2840380034988004c00384180300b0303910000340640d640e40b0022588020880c1c0c40042e00c071070003242d02a611501e40c054a4150502c1001100180100003501440b800c1c405031000ca58400003001e2515020f0278400000750803a8081240c0e03104120545aa9501c80d40610010302400d500c403211913000c881440c0480c20a00c107103541c517862184111001a101071010501c2443c102d070000038000460304002a10503200a400c4140c120313410f009803440e4249044007140d034001441240b100b040041010041e07807415500141160b5205000441003200842c580040d00700100225a10041c00c400300359101d2001c1c68004015040e038141001090284d03010450360460001216070a0b18005e444140e02070742c03000ca0464405211901d009004030310b1091039130300c00c4141c0d02405d03085405501600010341d41c0d8018401041c95400c00182c560f8001b0300f4829150790b01c40c6013070303096920900c2c0543d43c40b50001804007050041c0e00c0000941e43c40c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 71878842 1250 71877592 71877671
    0x4050409030509030c06041503020c0f0118030206010e0c0a0e0f040608010605150c0706050a03140f0f0f010509010501120e0708060702070f05090c0901030e01090b060f030102030402060a03 83
    0x11000d0f0a401d14201c0494803100072803410302003140500e00c640c40c40c998801c0180c0309403178029000352100b0344040f030031122400e00040040c0c1c00d4922400c0c010049107511401501415414003ca80c00740181c00c5028415080a0465480d240b0030417144000700480245c000500d80d17a4844801f4007e03100030028004107885200d40350007000c140c4103d80c8500c1c041c04100ca1903183c501c0545030380711140300241a4051a102d0f00740e500b6030024484504050b82c941000f8117021400d0300c158000ca5540c4d05000043c07a0000d40482240d5002d49214500c0d9072910040085aa9020b42141512001e00e0310040c880c100258590283c94111001d55090258200202e00754600042c13891080c580e960840c0c0c0000c0ea2500501031403c2180105600412408c0000300c903c036000004107458030b010f1600040010072410021300b1103204030360440b02000080107205807441c7c8010303d5045608120000c500d0b5042c1680000c0203445080484818140c0f0b407022045e5041e05041d05082c0072030070450301c1032030a04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 71880092 1250 71878842 71878847
    0x1101021c062111090408040305010c0503010620100b06041809030f081b09180f0105150405010914060705071518260c1005270d06020f0405040903 64
    0x65401061041000a0081c64114080000861071207821800c00014183c00e40c2c1444040c9000400585904608000001c001103007442204550f0005613100754495050020080a620110700302d42046003000d29078100f00c200208001c1859810214001034a09021001c81c516008a501c08040001c0700d5061151000540d0003001c0c00911903564031200740d120b05010b494a00b42030381c21080c0400a84030b154002500c0e40b00509902200428100400e1050307072458207070201c04c5414291000b440c070010081400d1100c01d020355000c44169072410542000c00082914040744110600c00403010840300c1141ca41c0d104031098160040140c41c405070300c51003002c42c0c16811280d07039000501004400c0318002a0000400195010b2030741080c00c00b0680d07001180c10441c45014442307c1e02946001105580d1203184d5603a080030f4036205c80382c60302000007807010382d0102a108480340d070b0080514003030259210071342120390702d41c01200141c48040782d03a1403402d14051500150741082ca022000c60900d0f4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 71881342 1250 71880092 71880101
    0x609020405030d0305010b030106121116030f020609151b04080d0e060301030b0105010c02015007020d0812040303020306040b0409051207050111071a0a0204080d1101021c 75
    0x798154100c0b250310f0058001141210780c00d00c507000e4160018001404000d200350440d69900002e4100802e050700d00520280e03441c0d000768104c0a819802198203010190803950352403e09000d80003403c12441c0040c0c0c1140c4407071082120740c01402c0c003070001503001c1c400550f0034510400c196014070748460f211004240c2e01c00c0310f12039210128102134a440c0c007070300d4040c084078180c82e0300601c8100540d10301001076503c1d03e100c1804a060104211070000133074030481400d60f920a10405030020341400c3d680c546111010280d140325003224100441440c0c603441012206003d82c10f841080d015200c50400e40d645010300184003984040b00421310052550603009036005290440f0300b00b0400d032810007002304440040308010890b4000584403020641703000301070140c5501510022a680c0003c880e0020035500c406011a4407190902003540c50b0040300d5041c82d405640108110700c1e007030a054440380d0b01c0340d140020a00308202078517960440d60382901511560f04468052560103004c2c42580400380 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 71882592 1250 71881342 71881349
    0x1707030f05030c0f0703020a0b1c090b180a0f0803070c120f1b0b01090b040b03030d240303140d0b030109060b040e0a0201090506180d03080615031905180106090204 72
    0x20704c5040c0801090b000f01054100440794001c1032089524a44615500c0d641c01510914640f041040094120340303030f8034003a400580e0b2003041d600e032a5240119011040c045503400e07420702c40d0300c11000c9000161100802c14000340d000a042c1d5102e0380d40640440e134150007400c000b04004080d03c032001180c1d401c148070220342ca1007900c0c0c0c00c2c401207240400d0701e0740640c0303000d015000c8082c03c001000400c6081e88280200d480151003c201c07a0300d0746001c80e00d1544030048a610040d920240c0001466109040d171001c1c20244500c0c100c600e1031074500070a032144141a4108409001500b11225117503584030148000e0081d0013484142803a041c035030010144409201e00176030030308442c80ca47d403401062413003015030705071103400b80b1604006c00c1c4001c58002c91818004c2c7d01581c042a01c0940c0c82070b0103821411300c0313a640c05a06140290500c14500c01d0b8068000c1c0002c024000c3c804101400040d00148a40010000520355a8a5400b120310900d09942445075440e0030404503505c2540c0d00144240c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 71883842 1250 71882592 71882617
    0x408010c02070b0a080f060406080706020c24030703050a06030623070e0a030305071401050c030115050406080604050603011506120506030c010c030c0804030218010302040506010311041707030f0503 87
    0x36555541c0f11604140f00345138800000808510006400c00013200c00d298000c0c8003d400040c0007030301c504026241c421640c2051015900130074140c030f83c51030b105460031b503000c0344400c2d4484400e0341107103407144502000d00781070207154030b4a00140e40b2003407640c494001150400c3c814000310003504e000900b84010000380c803803540e4032500010781d607500a481c2c00e01e901c040580001404c0380365031012100c607040070a040300ca180c41c9a455580d504000d0017000e001c4c60312440e04c544d80394503100c0110550010b000055060100520040000b41e4008021a0f8400010b940c040781503550040000c1c010035440310f41c1c0c050318603107038404141e413079029000c004d090450351002c200c140c07034441c10076130f854040704401070001da0741032a030f480003c0c4034100032480ca80c81081c0041c10180c4960015070f0001034124610500c2c2c892400400661500340185500b00308282410081c1c071002030320380109489580102460741000e899840800c02080004100840d0002c103003209020070340c5466a101d500140451b20b8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 71885092 1250 71883842 71883853
    0x1b020a03150f0c08060d0804080d0918051009020c0a0605010605031509061c15050a090204050718050609030a0203161a030c19090b0c0d03050c0403110402030a0b03030408010c02 78
    0x20441c041c1e12910403240030640b140c403510f650743d008200d51b003d00c40c074080301e0b440018003000441c0700c03081200742d6103212951200705500d0304100e08410b00c010300c1c9852200d014240b5080c044d512400301d005800340c40c00314031b000d03a5400c041501c45107084102800280841d142c20700010384194000040c50041da0710320480c05210402e0401c0140580d002c0d0b803900c0c0d0000b0044034100c103e00440c80312821071485040c0d00034034241c202c40c0e0041110411641c210030b0b552a45902821480c00c0e104566000c0e009041c070065040a814035002100f4260150038001d41e4001003070b100556081192014460b0300608440481c011078015102d010403621072162003000e0f5a480e0004a900202039a01c01c5020380c440ce07080c1303114101b0000c00304041005643c2803108c125000b00310721280e02e001b890321005c1c41000301850054032500034203c03003008143e00c50ba0032060000344005180401109100c140482e4003680703980381c0304404402020b4464025030f147c8000500055075540c103420492100465409450 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 71886342 1250 71885092 71885111
    0x50f041e1e0903021005070c1e021f020a061104091503050606010c020303030f060414010b19020106060c0b06030309040617060708040807022103030106020f1006080303071b020a0315 80
    0x4041d580c0c0c0b0310000700540c10242910329488540d078000e03640140180b81003e141d148a80b203285040040c80000c01c2c03540c2c2c20101450542c181103158482a010155400806082461000751104814403004020588403800c08130700042d18410703a00070700644c00303040180e1000e59182e0080d8645910049815005000c005021507008003070804d18103801401840c515a514010545041001031509a00c640d459400d2940c03000301541940c0039120308c0d100583c1e981541036050422010b1101c0c11800c42e0704001091004c15400304116440590003058120551a09000030b400d501400d00b00582040c60300c6000140c40100e0a16407103109200703029500b9503140d02104442c2000200c4028040d40001c100483c0107060400811140c482540c0f002d00340320700040e0b01203066900c28ac0c44080186d00803480109003107010f20011021031030290302000030a00c0c040003281c80e804000c15001c1409004032004400050403002075040942c0146500c508a4981c0340040009664910880c03041385080c580c00d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 71887592 1250 71886342 71886401
    0xa05040506090c0c0a05030f0c011b02120703050c030703091703070201050301050607060b040f05070e09100b0307050f0706140f06030a06021e030109091a01030c050f041e 75
    0x307001e01c10142034140950f8038061800354651001c03601e9584d510030600080c01040080c0083d00c6c1c0c28903c80c221542c0d404600c04454255407012001c03200c000384c050300091149800142004c20519099101c030340718025402d0a42d018050000020700c980400a518010103512a0742c100c2610360300070071450254100055103030740c3d001c1c03800028080f9804000600892400f000508862445010045140041840401c040d517041c200c0039031115481e0b07401d000046401c441862010320050302d84482500d40700024103241074207845032542004000000c950190321036002c80d2007a043d5001c92540d1031a0390301e4500001c1c03400c107044e2180480d114002c140d450f4800d5409600034030f4020000c1c0210070554849800030751010042c030051602105048400300c1020000e10700078042d007040062199032605040c401207601240f0710085d40c18034001400041d038510110302c1510310175280729144224550105c0c0c01810221600c2c1c03629028090791403500a03054101000c00503070020346041000126006 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 71888842 1250 71887592 71887601
    0x30105090915040219091e05090a051002031b07030903111215100915030203010e0609030a08091006091b0201020405100e0402130f0e060105120601080a0e0303150a0504 74
    0x9a45207158800200e80545000095201c02d8505420179103c0182d440e1a603004a51804601d03680d03a150340010810b0b485240d218150740848680301615a519882e81c03220784401ca00c060410b2460790100c041602054546030711044000d0301d50340d8641e68181c90901400c1003040e4801201ca49a20042600c5036041c417404040f9101c2500300207100494071100340b02ca88a000a2a81588128050000400124600a101118040702c400101c564258018103003035075242003641c0c0c0326030f1004062203030010000080700c1c210b40140c81c1003001502e614520380d080c00010009d0391442c500b012404504200903030702080035201c00c610541c0509200c00426800d038020ba114003940001901c858081d8540107100182d00801d000b08018603100c1000d00c6042440c81381d4120701e64000500700284010940c050a00750080024204241401d00c014515403031050b00606903810440750402082c0406841c0d00280340000445017607035200d00d00604132201000d1100714040c8103409000000850f800c15114 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 71890092 1250 71888842 71888863
    0xb0a06090b0f04020d151401030605040903080c07050f0d0f020606150a0e0310090605060907030209220207050a050f10110901080403270504050604020a0f030f0216080301050909 78
    0xb0000d02289480c04101c02504160030030050b0030707182c034218a40c6007072410604014103000f1400556068808000608940258000a004c1c5213084140c170f01082e040300000d50720901590300d8a03a140d4052400c5801c101c01c204842200784200076441d4481500000b480d1844050341d4200c80b280d0b927404040010488512a000040140800c080e50f0000d00c5100d05410b8440040d04642481c0000300320390045400b1003505a40803540c4806105503450280c80f2103402000f54a0b00307600300b0350b0a5000401403110680419004014003004107111105a0107031401c0542210690f07140f092141400d90300e845200455111600600c4038409a191042c8280090002c1c01401035080c07000c07050040d03602c040f01600c150184410010326800c5048520251550008203800e45404c840c640028802503807409400b0510550060041c0000c50380c1c05003100703444080d14178010130111540a250002441400464100360b030482803d1000e00980e00015812550251003035071641ea1142e90468a0b14610322 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 71891342 1250 71890092 71890099
    0xc0501020f030a05062d010212070f030e01021605091902070c080105070f1e0c0b0a0b0307090c020d20030a1706030307200a09021b010606110c06250b0a06090b 70
    0x41c0c0e00203486c40c0c0c02c404603000b0418011194001c0300800b2041c10f03074010000403900c03842501c00c3d8078201a031150361040008420700042003210510b0300c07014154803650050b43e018400344800a0302c14282d2400c1d0303110a03001060110f5440f00705085c08090179a142c010100300358204004160301c0c0b4420410740d01403403034a0343d038401c0403c40b002003410b105102038901c0341006510480344000c201da1582850184c0d0030650000b85ca8003000041c1401c3c0310b80ca5122800305c40c504840c04410701c0c2c01180780d158080711894203090100b1074103524540c601621000f441188800700343c1031030241d040003050589080540d01c0c1049a540c9400301030340c0e840b807060000c04583e01500d03070403484c18820300218401c010040000074420707290072921040b42c1008e0031201005600c80c1380383c26004001e1103241d003c0c0c21b9a02d0070503024840d11010f50350719008003e40c0781c0078140010f042466800080c400940c0117a800451032850041c0341041c0e80504000da803285182441c04d000040d1104940c0319640c50801d025 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 71892592 1250 71891342 71891389
    0x609050d0803060f09070503070201200301060e010c05120c0105010b0304020a05090c090402070303050105010e0301150b0a140309071707180506040e300405031009030c0501020f030a0506 82
    0x281c0da2000e4680014111503005107040c80101200e80e02e1420103032045203203a446507100e00d40044000d083d5990b01b420fa01844031200c0b00c01d08c0e444403480c00c9905680a90a01008880803140103c0e119003000d00c0161050040e00b401409100d0005c000305103030790f0b5400c024000d698840710004868401078400a5000110410820003800d202d842c15a0100c0b0700011103051a4810380440e09a9014030300440000c1c1d42d50740144030a6820081002210300240c0c020441100c0500e0b000b083e5507070a00800002c031402080c60740d881c6224030001a01c014918070440e85a040500806551300c1280c015012070706200b0034181420003000461004845a12080817040101d90380e040e0010603029010b20341041d21a00714a00c0480201301400c24401c402444c1d04585505140d6803400750b8401c2110840100308000400c56a0707000501c12955082c7d085001800081601c0d003075450102c8103034018590b500100301d04030300404107805140f08410090060005035582010041e5a0004000c0040c400d00031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 71893842 1250 71892592 71892619
    0x503270304090c02370c030605060108012103031802150903060108030c0706031d010912030f060806010302090a1e05040210050f070b101d04050f0105010513020304030917010b0a060905 81
    0xc4903018005c2e1201c00c030380e402e94118192a45401106550070550b80f4980b00d0041c0060b950b030001c1581d00500014009080706401c1e8a150060045281c0c80a000c0646901d5444159144080c00320803c5070b000301000e8003850307600c5506846402404082e446406275a00024030108044215101d9481c0c0001070000741d814400181e00420110b11884a01005e143e14203020384400d104442c41c2c64000e040240140d80c000c44010243d03a0b040c01d2405416040100400c44c100300003441c50306482c0d0440c0c820300c0d1541e502441c500200703100b40080c086485100b600f8545400c01d81d00c01d44c0906d0007074411128140f1601026035540c407422940e8031814504100c4280400d20140b4296005550408104219540c40c5291036942d0b11880c3c850806005810520040100070002800c800d00b55200a01c003943c03400e000204150300c0d042c4201880c1c0c0c2c0005c001001c2621504801c00600030084080041b04000605c2c5402402c0341c80308180240c0300c142001c070350180111300500440b4401441800030300030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 71895092 1250 71893842 71893903
    0x11802240316030204030204020c15010906050d0308040204091208013303020a0207090204081e0d050301030f14060f010518060603070c06020903060109020712050412030503270304090c02 82
    0x2c24221101003640c28440440180d440c2d000401c513100d5000c00a080b064428842d103c20508107910030060940391070f40c1040b05881e2454031108070754060030318004550780ca002040c060700c0c103950000c000715094500301d03042c1c07900a00b0482c1603540300304683d09240807036100800d0703402c2c002101c04c0141c58040800d0000c14800e80040c0001c01c001c2c815140750b2540c0711698010780e041504100400d0f0880f100702460301e2008150520700100d828010b0180f0000d150020340700c0d100601018007111849078014041c402d01c0d03840002c1d18006034045030310a01d040040c140069801303014a134801c0f03080c00ca43d207000c0100d000d0340c5402880700501e06860b54881c0b03401502c440300360080407150540c007400f5600c0a59018010240200000040942d031840d003071130061240304180380d6400a014040c40b00384030110040c0c1d0440c0c00715a0505213640d50b503d0b40c0c401d445814081101c143c512080d250210768902801101420031a0b442b0801440004100e00b4145c2c1c54104940c2501284d0080300395140d207240 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 71896342 1250 71895092 71895121
    0x612071d1e36180a17130801020408100204030c0603051308030106020709110703024209010c1803060b041404060b100906170a11190801090218130e0118022403 70
    0x1110b46070a1401001e0b1450f80001201b0794000c0d075003a54046010000380314140100c05800c48902e40c1140361030706590b200c82c000c01d518008c10003059504c0b0700140590307828036910403003550024203d0751613695840000355900e00e80d02607001c2032418980700c0350740400c000094860b40c0741e0640207807010755100d0900c0340c1800c00404030056104440b50340307240c60003400d040c20000d1007110070502185181c801c1600c1d00790b440c8441200c08009481078110085401d015202c41942e41c085000f00340865031100040c00f40c401c003900b100c60226108140010001c40343d00100311240700f910f0311410346100300000d0760300c40294420708000c1002d1506a150091905d5900c5078814140c0c200041c10011090490700345401640c1c0301c0c28030301007060320413203110f8000e06804e0041c00310000a42c40d141e800210341c00c0c1142c0c0800b030140074541040d0b80303030b05108654001c4041c800401000b00701918054800d07a2021264030f009a0064900d01c0c3c0d01c0400600d00301e0341e24116555415100d10b07584540344064582c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 71897592 1250 71896342 71896373
    0xe040614100e04090302070e010e0702070b09061c09020906040605010e0405040602130b070308090d0504120c081609110702030d110c0612071d1e36180a 67
    0xe22540070300b81643d2603218a26a40340241c1c01451002d040c125005070b0301c0e106130004400b49240d0010040740d40c6d400181e01c015a482c6987c41a260000000802d0203402512100036420180d00355884811003d50700460020b03000311030100c4141c480500344012030f000c074052203000408000200409040a0f00426085440b13a0030042c030702250360a030b0040c940c3c1242c05c0000c50302e2001820406156000c0c0c01030740c022040c040609510161400054844d00c502d12a038607001a080410f9010301c00920a00c4004240110941d00c2480d84d9604404803055030307019040390701b8940100b0b200303174205a40c00d8409943d4041d00074542001c003100107a0750b00d01201501040c0e8411a506054580c541c4406004031802400d65002a13040440300a0110402c0e081204640312551101441d2a901c141d0fa401d00c90400070745090308001141c0101c0c4803144203200114001441808c0c00302e034401d81120031a0a580703101094150390700d52015090300c0702c1181c124001c40c1e501c0b64000dc804a06100901d0100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 71898842 1250 71897592 71897597
    0xa03020319030e0303070605011503060e040f1b06020d03060807080a031404150201020702010e0904050c040510090501030f1b0f140a0806040501050402030606030d0203030a0c030204050d0b070e04061410 89
    0x80783c40ca6400203140d5842000110340003519540100080c40f030244803400940a1402c05004040c144105903102c080c00070301c0503000c00388079000d040a000c22038440382500707620003034a503121a8031000082c2d0746d500c80000c0f00e400a0f1401d50002039070640411002c056a1402020f0003080406440440d4030131400b003011091840c0800000451941e00d0350480d880425580026032141c0340741c00094400c48104100368080c0e11580c04000004001040c4802d44000440340084c0b5030f110b003064140d0031a5290488403216103044008014881c070306843c280c200740711b480c04211002d83c18000e152000c84038411b004a214100805006002081180824451f000f515640c1d4035961460a03034a4818251410b540996444003480f065003001d10005609c40d00580040529456140001303541c3d1000070081580565548e0841000901c25011280100700041c80004c04030b020341030401855009613800d0380031504220144845051600031131040b1150085400d01c650042e4007400940070b1015025000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 71900092 1250 71898842 71898857
    0x6010b040f09020a0302130305012702010e0415080d05030a06140a15020307060204090e070b09060f070c08150a0f061212032c010e01020306030c120a06020a050909060a0302031903 79
    0x4044e1f0180c0c08402c011800344002186108208036009003c4054580d003185000a4400075130141c1d820a500c5402c46009035000218075044068001c02c40d0714640018080f40201d8103070303054655106c0301541c003801080714100306890745c031010041d031804849080d54101460910405c2a01c0c01e00440350b29201940c0192858400389949280803688603801060020740d888401218055080260340050443c4811840c030b00341c40000001d00a002319038400455a40020f41c01e070800c00504240c0004001074003c075a1424501c00900345814000c440c0602131620341030b001c000c0caa0050244c03074111500c101742c03011401010f0300c6104090002d032841d0018592a00c0f21004180c20300c01c949404007800c12818650901141003450075110401850506030780180f042c0810b0b0340e80464840396151040703030746440e4403c0046096090a510000203450b00e0710100d41540000e030040010804030008644015940e501c41c4e003008603000d0f03507000c0690554020504c81c840d194402c2032040380240242029078 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 71901342 1250 71900092 71900107
    0x61809030c010c030f0b090103021c0203011805030304021009060807050a230a170606090d030c171206100c060506010c14030702030c010c0b04020d0807020909010603020306010b040f09020a0302 85
    0x40c290b034810004000045d5480b10b080520845611034107020880c112402c041c207500d1500014031130340100d80084114010a40c081d0115a825030091070a000c641102d207038081c2a60500075245d400444041c4e00800109803400141792060a0303a009544140c0c440014a4413000c1c5c1c11101c64103c0000c0d03d040c0f02d140c11030102740e907644240c2c200c50410400c028660340c503101d07000140220300101c10b5002680b4142c1c103025481d41c0e07440540304428020340f59108061400c3c1422034031230b821840041c1c40c0a0300d055250f10150680e400900740c03040101d00e1641c403074440d0404c2c0451042d540c0314010000c0d2080300c4030800140b4036017042c1c1d08a80140340c0080151481e864004001d0b060891131451503000048503000c5080a1040d080a59024242078010034080d8561075992400144001e101d501c801103043d040081e00070070344607000d40107414500240350090180c0d000740a54042a07100e0311602d000058012420300c100e409548218a01d40800c615041141020b5000003004005041c0c0902c00310 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 71902592 1250 71901342 71901367
    0x18020a170d0311040918050714010c02040b010504050603010308180d020108040318081212070804030c03110312040807020405010902180108090703050a1b1a03190e100b010809030306180903 83
    0x40030380c082c4030a440c10b0310703042c0f1310b819403809469070b2100303803040a44441075500340cbc0c0025403080a01e4040e00c02013005c040c40340c0106c1e041d00c189d4204a038011404000802400f0590003c2c00c003100010481da540405180f00700a0442c1200200078001046900013a000a1160f480289100c001b451703885500c40d110100c80b0306044250282022600002c00c04880003000c0c41130b5030b40c0000ca00c0c18244500c0c1429280100440d01d03444001c1c3c144034150032240d440300e40802c00c6a04425aa01500000341040c2c0341000303c590009006901c12030828001084c0c090061003294103441001e21951540606035006507500d8800400c1e6040d5405030500002c00f1030014440501828440d0039105d42501c0b24400440042c503113600400c1020240c058041a40c402201c00c0b030380c108101071201d410fa0744c1400711402c0500403000c1c0c505228042d1800b0029a900326421000802030309888070a0380356100401582d82e070100311075a0381c2c00080c2e5003800140c14054005030707070007854040551b4540302d1132a851 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 71903842 1250 71902592 71902601
    0x1e0913020a02030c010b100203040b0f0c1902010215010605160c03050f0303160801060807080603030705010c05190302090303090d0201120911010f0206190b010e030118020a170d03110409 82
    0x1070350150300f00241c41d42401c2020300c40d40b0000b401c110b4400f203201e10700d05402540d0780a603000303051901500140488448401d0801c0c1da10088984040701c541c901c0b90a6203080f00021510200c1c05445400074001040c0c2820140394144e4006a1f5460301303001c41206060703c1c0070142030003510040369128001c008286c0a210607d50030344010000d43c0d907424400b6220340580480c8820108000c04400180302e0a80d00c0349400742c020340c007031a010301c142d02d5441c0000e00710b00c40d00074014090b62a040706d0120264202014040e50b100380468ac221001d4413070002d4040e482242c030340540c190810000c0051601d000c00c0300003d0240103141411507085c00c5071a1400301d4080305010745a12a41f011002c0c96903a2008004910780d8061001c1d056505001100001004000c8120010b10703458101c601da999104903880c16035450010004e100d20351043c000d515003c09007031026405020070410110700d500d4002042d440c0d181c814070090c5411039458134220000e08094002d0f9070701d0343e41000009200d4007517015 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 71905092 1250 71903842 71903857
    0xb010905010509011208030601050304030e03030a0c20150304030314090606090711060f09120d06051906080106050304080d0911090f0112140a1b0303020c061e091302 73
    0x8001190750508042058010050748012400a502d205050000c2d110300c0550ba08030400f82400350301d07034442c1e2030b0503600312407454000394044c440030550140e401c1c0c2c441c0e1800380036070103005041101708842d0b28400800000c030f480c00d500301c96001c4040e80382d007031218000c5600a0080c9400a43c9006c40e0400c02c150203001d4400e45140d500c544140185031401c08030701900035003d400e2111440c000a4591606c940e8002c0840315011590700001d03940d1102031003031140491180401030368900400d401c0100a15860240c0c3d8024540c01d038409103090450102181564020b0f1200103450386010000c45071684010b208580c001801e00581c0c12414550195014a500c1b400e030313100746002070805114101000500c00c0588101c02d00c01041800580b0b4a00c0640c95049020142245110070300c41f45094014000141051291542403192095290780d8a0541e84a582607d11061118080204078000c183d5030700100c924800790b0603600314041c1e001b4007901d17a029203a00e58641281d600081241c201c00c2c07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 71906342 1250 71905092 71905109
    0x109050108032d03011710090c0b1303060c12111e0f07051006030204050a0902130c0201020c15100801050c030105130b03160612140c0304050f0f0a0b0f070c120c0b01 73
    0x291b04c1202c610501900701c1038410b50710b0812034184692285641c2440510403a407015400088810010180e1140b40c03000e5500200140700702c0c81200d0b801004401d030402032003503140c6030040000300d00030040121103814003c80c1d15848481e695a4041265074440c80207000021804c010f00ba001403418800f010703180b46020700000e001807460042c0000c3d50340c014070100c0324516042e0200d0040c0d0b00c0307002c0c0b1031100c031079041c0006040d511690b080e8028800c010f80c0e2180c920030b6544140b0f0300c0c0302c0c29881ea481081d2400c015131045a07104020790a1700c0701030311249451041400180402c0c14000201034800c1c90781507000c500a12150042420102d00100303494402e11300390003d00c080d071341000001c450801c1c101c1007000f010341d103c502d40741e62903006014800c8031840040441c0c00e224080140004070300a0704140c58951031683d440381c6c0e0faa02c440d401250081d52100005003202296800503203d42c81985400d00b03005030564801642c4100c00020340c003070066900c0c0383d0010420781c00110f40608182c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 71907592 1250 71906342 71906369
    0x8070f06030c0305061003020903070504020d06290717040b07050f160506030129130504050f01030b1501020106081203190e1504020a09050a02030402090109050108032d0301 76
    0x22038014180d510b256103480034181000144102c5840d8101c034042c080d02140350040c0c8a503040c0e800a0300341205940300950050010450800259050b0310030411113202902c0220600e0030700d180312140c0030b05801c1e42480301200b4405200811a80615500c1c0d41c061041c0340380c5019100d92030b45459030000300045c2e48690000b543e0341c4a440040041034100d5101c2020000c08500e0500000c665100c140510b150345940306862044a6a5032040211103210108209448102c101c2c1802c4815806c5d101d9103205900705800b007070001d4100403005040e00d030441401c65040d51100301c1119211158011281150750711000003c070000f0500c0441d50403290501d000c0d9076428240444c04400041e1108204000d03c2c00103a41c2c01928002620031320f0382d5904094051540d02ca00004416195650007a040181041e04020448800381e00551040788215400c0d0344503621040c102c4c0480d102406075950640c020040341101703802d4101070001c2d540c80b00e021904c808055904230002900207a10845030040203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 71908842 1250 71907592 71907599
    0x30a02010b0108010f031509020a080a060c0e0d02041a040c180503010507171906060801090e0606011409030c0d030c0b0a020a05030105010f03091208180613020f01020708070f 77
    0x2802400d80d91807091810b02c449505280004030300103158800213005c50100c100251241e0f40781d42088404540003420a407030b10769074403a00c03900e4595166040380c40301d103081600408140107260305109400007520079944103000b58240303c02011850f28000554003024403142e881c0d0380d180110004101c1594645c02045140c0c00c0070410b52281e0f412040c403e03410041048201580a0078000181078841c50b60825500c0d06110240013116407003002441500304507000c20302075080740040f4101e6040d56020002501000c4803e074035a00c043da40e50340000c0004680c44000c07000c1c1c4010b010008801030955055a4000d000038102540702a421000300741460b000c5005e0100340c1c1c0e4060b13481100030001754a40801c1960080440c030050248605006501d141440302900c0ba5001c0c42000398403034008900c12505000207880030b403045a00070703109940301108801001011442c02d0060381c03400b0301030071035044560800040780540b075003007411072144890001e2030b9081048004001c021341411913031811305 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 71910092 1250 71908842 71908847
    0x30601030f09050d02012d15091b0e040c090e0a0b1f020c0102070303140703090b0c0106180c080a0911031c020d0801030201120e0f0f010212070c02090103060f1103040302030a 77
    0x4082d820b141504410034000c900242d5907c4101c0d100d811010002013503c0094040a940445504401449403410003040703481c8809200c00c0c090040c1c06c0d10348a20300c0a9100420050f41c0780940c50b1800160961002c0120300d0029268903002258200d011820354000d2010900d04481c014190210080c2200180061a014481c07084402c2c800c1c40584030301c82c00e40d04d01034416030801d4600011501e0000c0c14000303051090384d03080050400309000c5640c4d8a9203d04050280010f030082c3c0c0c40401c1c4889160100322503500c00d1a03065a640c2c1c41303807401d41e46e61005c00070040840410aa076103002001c10019140c3e010300480c52951100c0040d41c0c401000604024a06070351b0b4258101400b00e444014030150782c004c20380b400403228101e0081950346070350300c1d07071814148404a580b1175031140b034045464426040d0040d20051410792580803255690b0401110301601107800690450006401400461050341081d40c641d043c0d2a40332a040307100c80000101a44212400d0300140c00105520030b1296 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 71911342 1250 71910092 71910101
    0x4060909150b09010b030f090a0609030e03060601081005040f06030804080304062a0b0901090b01261513030207030b040c03051603020306070509010e03060c0310090e12030601030f09050d0201 84
    0x4015290100998107003240011581b0000c0c203001d0340d002050b00020300b0030004004100501e0382c04030007844400b01619014102003501c681542c42030107010002065035106807115482809800208003041d13180900b030100803c0c0e003c1c0423186541c0c603503c0c040045000500240001c00b00180155991890000014104600c410605106011b80c3d03100015401c682007440000c01e8100001c943c1070303241c00412138014400d1031001800e50108100024156140c00006003030304041c8080480890540845d840c5ca0303a64a43c401038011290001007400c6039101d00c2d0040000d8401d00440310348035203030340740d0181400d81281c048941103041c1c0f005008111051000c0402c1800f903164400000e13003164000390701e4502c014000c1c0704122000c40e041055030300c1841c11100201010381640e42c1420324030807048840e84102d80d080442c20001e0000a001c0e42948141e140c1e01403150301402e00c0f4015560000300b0303036001170503042c10941c0315502240e103c050f0f032046186041c0f08100602804002c90310190030b64 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 71912592 1250 71911342 71911361
    0x210905120705060901030203060f0901080106050102010b0406121103030c070e1009020a0e0411090402180f0306130303050709090c11250b0304080f030901060501020114060d0b060406090915 83
    0xe030007201e401c21180d100c1c8025104118005d00303000d070b100e96800c804104160111094a42d0183c49180001050722040d40440c0a175282039000f13110b090320300340610054400c5441001120171600400303902244000d681180800401801d8a160080d00d0582610740f1105412219090021200380108201e800301410028001450f041d810200a45006813003640d00c50800d81c06951a626031252a4945104441c00045c0080045440c0c1d282101103511030141420180d01070040801a8005480d00084451040322401d0300254020180d0341d04034040d1402600301e00a00038844000300d01c000540c0241078210405c0c1e80d41c16080da5031100ca243c5860800a06107010802e071402d41c808402800c500f04040d18400c1080e240d0b6515185090105c6100d85c0c00d040000c0305010040c4648894190000c41c2200c900f6402072200c0b4a0b1480728112010040d02c1295000c0d140641d40380c001683c02d103085500401c020300004400369030301d12610a46241c07540c202e0303515400802c0014500207500c6410b154 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 71913842 1250 71912592 71912629
    0x709060524030609070306080709090606090216060b0f0904050a021e1003180c03080c0f031602010c05150c070b0c0c120705012c0f060f070c210905 65
    0x31600c41c540e080c45840090401406103d5003030000d40758034002e421a100401200084540301d07030307442d0b10880050407000012102030341003480016000c01e4600a030350104584001400c06003086a40b01c60081000ca1002d84c5c010032158001a825031f0792803c0244610301510146c0a41e8540e031040207203000c0f005401194515002ea564121a200d0880d40c400201d500d0400250505503240102c075005144c0400130400c0d54520740c088100506039019110001c031501c102c80f007880100f40000d45a0149002102d4030202d101c0134440503603c60305078141054020005d40f00200340200c2001303040030301128a040300d440c0c00905442004522040700e644940103032400d81c14032045c45e2030540c40b11202d0407c4101c1200c085860130a100c4c00303601510804050700c4180c210382e808041000f62500301c45407d14014010200201d042501c0032a003984600310808000031136a44024050305c02e42880542590f040c1056070300844035580704888081091400c0d1100e000c554500f074108801030382881d02c02c212 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 71915092 1250 71913842 71913889
    0x30304030507052512050a06020d020c0d02030c0c220c21050405030d0207080d0510030b01050303160210050f070c032904060203071e0905030d11060105040e01090507090605 76
    0x2400e016011300005480700d00b0043c3c51104c201d0704240d840c2c0340350f10402800e51840000c2260300f1050036401041c00141039001d94040e0800304109036100c0c001d07039040c400f040d0172140650201c1d203003411200c45904640110f12031983d034986d336000c080f61480200c070000b00318018000945200c001e00c4d050303c0032003c403409000da450999162900d0340140820300401a801048042c00c102040c17094641d0119052820012480c0c50300c0e100c07955144078841500d91400310740000c54941000701c00c40d0140045003100c0c003450542a0700b403003211101030301c1c1c82d401c2090510002c05500300c610010401c0c54003c040200030350b0305502304502e4141c0440f0b08070290700440030001400c00040340d48a0f91180d0030040068507503580c1d1200340c3e601e041904028168040e40b2a040940315000301d1a18241d880680c100c034040364140340103941c00e03181c40e00b081c20700d603022100400c154a03003a00582960b1030000004122001e16541e10303843c045841c1c000e440507a4890f01e05110303e040041c085a510600600b2048 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 71916342 1250 71915092 71915143
    0x160b0f0f1f030209070302120702030310230f010908030a0e030f0309031b0307031202010509010501080d09140307030b01030804150206070504030308040c08030a090626060d0303090503030403050705 87
    0x1850401c00d2000074001c140d803200051180d802036040d030703500424840b41d003020340ca01a80f009443c1e51003150018094140c030400030981d00201048240203130a400e1f1160488400c4004003c1c49404c03076201c05040010034540070440e00424030141c8086110341d1980c10540498404040c03c1080c4c2109000c2c07641d0041c086540c4a660015600303d040c00d40029000000c54420082814040c1541002c2e02a101083c81c0840d860b81c154443c1c1d214030314010003000544d032a034400b90b4454203d60281d9000a060070018001c0084c4403c0703c01040e2401022140229902d03540c0913440351090740144d8a031040807600300420074080315503903090b118501c080c04061034a2107002e0420301442c040a0f040165a5001908011180240390302804059045030344503181140000e200320880d0180e030b800a0500b21804030b100c41216140c1c8840000c2d00020142c1d9a030741414081c0102041600703904164139241d40201189092004501031030182d504c1503614032007420042e1422010420441003100c4060418 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 71917592 1250 71916342 71916391
    0x906032a030c040b100c080d060303200705060f130905010b0705070602060f13030c1b0603140402210307080a020607030b011d010509060f13060f110c0402160b0f0f 72
    0x82c40070704032504055030140801d05098187d03005003551040c015223480c501009258005010811103005145c0d1407000c0074182c44000d803a880306208690f00b1090500003650600d000401915042d001d2032000001e941c0c0d200102015a4400e0740a0000094001000024450280440d801400c605d000405003803e00d0022111211401001d002049120215030f10406100c6c0214940d0507030804100c40b422008908010140300091165002003443d054074011810049100310b842190001d202540b80d102807d0f40b00c6003000d9103c0008410b0100304190800036514002500c051f1007960f0003030850b860100300241c112401c14240b1410b0007480c00810502c0c1e800c0100d410007426081c138120340c49260440c0800d0040c010920100888100031135144001d02e001070100c0b04071400ea6445e8070300001c1c0c40005580f00e0042404400f0141c001c0c88140741d05040640041c050503040c10200b00c0d01a215840d43c440c2c0700029201d1310b0301002000c080c000780d1031143c00c5050300001200c0c3c60514148003400364 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 71918842 1250 71917592 71917609
    0x7080103030c060e060f0604050603010903080a050402010e03070909060f060320060409060e0402040c03020909220f030216080706090e1b0f0301150207050f0906032a030c040b 77
    0x3400c104503190b4003000c02c8600d0300b2450340030080d0011600c55007003030801a100c4130f804850250040d440c1c03a0002d02149014000e50301060340507180c54817107071039130061078026000c000d00690501400507a4464151020032900004081c0e4000000c1c00360b2841c07034550140c2e420603801d040d405041602c00d00101c0e4402c80c03044481e030802e203642c1640003032910100305c85026030f50298000e28a4404001012002e0060052081c3d108480420071a40c0303400303058080b405081c10b103541240c800030006680304c1c000d44203c00d9049910081174405000b5581d01c40d1012400281240181c210301c1d890a42d030300c1d8a5003104080c002c0385010700307001c6041000052241ca0300d841502c40100300d000c0865150600000c03500c5030011a1070368a562082d6000031040e86510030f229003040341602188654801c0c0c404503480381a59001840c80f1010b49240080048001d0050003181c0e142c0500000d60f4040a100503000081b07919500031201d03c08850f81c2050304221503142901c0c061802c20041c007429585a952 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 71920092 1250 71918842 71918849
    0xc050a030c02010b03070609060e06071a070903020402070609050d0e0303030c09060405030106090207030207140306010b0901030b1906020c04090b0106050304050f0d09170c01090b0f0d11090301050906070801 91
    0x500040c8107406440c12401350104449a07a0035000300f080210300140d00201440c15625952a10100c1c1504181030001c21300c40c2110107000302407146015181075801c26a030075040002c0b0714040c1c207415240d0b00003500726441410101d0f0190b544059a204001c41032254030a00707001402c00580c41006980483d13142d00c030051280d000042e000544402d965506000e032006400050002c105654845442d40c00070740c4540ca040e40948100d2400044581e200c0060781e510f0180540506056464240410442d07080480300505045e1110070321800d0b5103c062200020f41c0b86100702e8000c01c0c0ca40140a82017034103104800740201d04001510012810440106d1304481240c58450784c1ca51f9281803d505000000084030002d0094900b880101e40d8407901c000103544c0c044040d18035406640040644d21f2000d43d65841c003280313200c0c1c01081f15031031509c050049500e40000382d17072409812220000c1201c1c11103442c00c010380c00c00300e02c000311400c00744642c660041d80b440041c03500707003407462014051410521 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 71921342 1250 71920092 71920097
    0x3010e0106030c0e240d0f0513050a06091e0b01170c010c020904050c090405060702060c090d0210230c10050915070c080c0616030204060c030c0c050a081e010c050a 72
    0x4000d044081172100300c056514003020b107258450b80f94280c0c40c4007410b1404064007040d42803001180c07076501c903031104c8440207601c00010700600440d41d0b02c81025040d0aa001d442c000c90007a0302866504011002405541c41407411100c15030606a0b400803514500c200000a64460000140710340d0f04a1100300d0030301d80441d60460702c0d035540d00d01030780344c004111400e540003111041403208000000074414044c141d10b800303403041d0b0b5445505103180b034040c0c2030f151603000d40228609005810400c1040002c402145003a14506c08001100020416081424014a10001041c0c180f00c8400d010001d41104440c5082c032071350412b05943c0da40e8010100007090805c07800c0c0c010425241c002c0e0b00458250b54405156520f50700213514071504c400003100c1001c1c0035884001c074240d90f51300c28400c407400d5403107903183d02c4022070080c0c400700d8540ea140807003260049945400880c0c25aa446908002000f0310001011050744000300602d690f080c0b60510402ca0303060401c010041030b006810340e45854600d1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 71922592 1250 71921342 71921359
    0x30408070303110a0507170c01020f12090307022101110a050a03112b0e012313150b06070501330609050103050916060203090a061b030e06071703010e0106030c0e 71
    0x4144030b5907d442030017420a01c543c070006000c2c10302440c2d030000c0e10b0b1074003200c901071030076664005603140c5900c1a900025801501200c0e85131680d1031408075040303441d0b044000068904203e142c01e080c141d01400e0442c1c081903000ca0318003052981802008003030740420407190308200d948411400003110b19502100003200b070800c0c22081050550040c800056484000c3c00001e4607042d507080480c42c07a01110307034034103c045d0000c2d94007c0e05c1d5001120307030b96101f8551604203d0343e000f4100203080c113210303079603004004200200106000b40600421990105a580008260050315403200008595151205000a6410002650064201022150203003070102c1c403550362080fa1401c18402400484003034407003041c007145c441d038000b0213084040801e907015500d040d00d03200b0907181041901c3c1c010300100505821980001d10507034220850741c00150806040c20055034544401d00c0d080582d0075103049010004215840140c1c1c60203005003e40d003000c0007808a034441c0104415135400003e13015180740d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 71923842 1250 71922592 71922623
    0x10216020d02030a170414030c0a03030315030203100e0f07060e0d0611070b06030c0a12080703090f06050a0201060504050903070f080c0a110307050f03060106081b030408070303110a0507 82
    0x612000703001175840b6600351000c024000c80d40580350000d000e80b01941000c0f45c0d000035103050006168210250003480c1c8003081c3d1a42e541100544000001000d0b10b0702c10b200c0c00801601c0401001244440c00305c03011070040700e807000c664940b40340604c80d100030768800035040118580000210f004500c00b501c2c50003542c0c5071350034141e001e03020503c4040c41881002504400344804901d003680203401c120162003540a60704100800c11046010307007a00038614a4a8100040c00b040c004c0c84118402d08000381c00f00d42e1800c5107030303401000b42e001002042c8002503c421301503080c46003030701410003114100038038200040706942c0c0380210a0028145400d000c500400d018500050324190340d9100110740b400c0c9801d203005510209a00a403d0080c400c0b082d0200f811303d8850651030308201c010b40240311980c6804811248003c1c003070900c0e605592047e1800b0f4140c0c0507900114440c0d40a03206907951049646401421a8850065900c0c90441840700b10034550340001102ca5141d044401c11040000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 71925092 1250 71923842 71923849
    0x30c0315021b0c0907030516030e12030709031104091e1a0108010606120e060c0a09030209070806030d0201050f1306020f04090e10020306030d1b020306040c090e010216020d02 77
    0x9907151000740c0c0301500c00c0b9a1061000040301008940305460202090310b580703100303a050358026181c40004007188458480c180340f20360b00403940c00c1400380031108010300145402c0360541c02910441c0c0011582081070050181150b1010304a0a041e1030030041810170ba01e800041c01308407c1c885840302058000c20381844140c40182c1c42860000c1101000c550b940d40205000303024030312803034000c00c5e252000078a8681c81d07403080c00c03442315540c006000d046c0d580c1d2480800700c0c0e110070100014001104004005600d803000d03043c0c843c03851520b80f14964106501054900707400d084145045a0401d81000001c2c1c4100c241d054111958040307455110781c031441c200b030107405004810320303803030101240010f02e400381a001074141c2c4c0d04401c10380d09414402c00c80710080e4441141d445405a01c801715260016101e088201c0d41000d9060b0750200e00101540040d047c404140d405440d8030241c4001802140701c54440d0340540005134000710b00c0e0101c61034800c0811560b1810283c0320f0b540c040041015500e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 71926342 1250 71925092 71925097
    0x10803090907030c0e090a02090102010b0609030a020f150c0102030f1f051003020c06090105040615030b0c13090f0c030b1008010902071e03030204060813020d020409020f060a05070209060a030c031502 88
    0x500404c2225640347c038144000094000341030150040d8240804400981000400c54610110242c0035086280085e024402d002c0602c1c20300d075802c841c0183c1140343d41001da402a04e840070160001603640e0814a014510801010b00340c4d01100c85036822001c101c00030861402d0450b1402e0754031080c20031a4402c198000d0251400f01d540390300418080060582c0194001d03480b640c401d80080140c026082070003221441e25000082003603070350368042602d081340034000d040c903005110009106152146015015240a10040340b2172a4403102e001442c0c0d034140c0140302d6070507025102424003c0c50424010b00c0d120061051035401640044c1008c00c0c45525203810881040c50054804007491900d0700500a601c0b0b48100740007e0fa90401103800043c1e4501201c40e0b260700200030320325030b080c540c0800004000512089a2000c0c040a011003e6290800a09018003240c1c41c2c00d6111401401072008140000788440c0c40707900c42400900008541c800b039042525048549800e455483c48803c1c0000d2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 71927592 1250 71926342 71926367
    0x90a0e010f020a0c02150a050d090c0302061908010905090309040e0a06060e0703050f0709091d0d0e04050114030a081b06010b07030f020c01020304060302090a051207030b010803090907030c 83
    0x142c0c00010b040c0200c0da0414035a0262a20170744aa4104000c036000182e80d42c0240203c2d8000214100b2010841c807205e50000c0d04003038021704104003070540c0d07640001c0c1c182d1700c0500142c2c002c0d0244c2420784031240d00b10103c240100510201031200340303071186505440740310718085175100d035564099403507854030104025803030781da44130f10200704084c0c691740503140440b001c9604000017401e00c800924400708001310b03e4001c0c90315444001c0881d040c44002e030b019140c070741c07006d03800700505000d24440c0380d404215590081560340c449000104c122428001030380d8050f004080e10360031039541c2e40038070307100060000011500072410360f440305116640360343c00307005410034080d20780306000011400d070820f440240034480c803036142c0e0307016019940d5041e84c603202201462405030f00240f100f002854041e400916440d04000d01410607036448500095030281e0070032824400c2c2e48440424400c0003084612240541210002076003055003020004180890081c9154105911948411302c3c0c075000f0805d54400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 71928842 1250 71927592 71927621
    0xf0d0804050411040e010605090306090307050c090601050d1104140306060310020f040905190b042f04080f0c04180f02060a0c020409030206060108070f02062403030408060714030105090a0e01 84
    0x1071b56035a66004090303400c19035686200f4003403d804035181c0c030800801c5a60643e444809170842003545010815600300081419040c818100401404903c0a2155440f18803080070003a40b41c600300040c0d0640e0751401e400090081d0b01000c1440541c2e603002507400e0b00b0300444440540d4900411000303404600071039002e100d0baa030410003400102035004100c0c0301084e0003100200b1091701254200400d075045240d001c00080d52000300310040582403070742d040202005110440c0341c02d075070b000070515003281542c8000b45a080b0105061710391a05014490240400d101d20100c41d0303d0a4462081c5480741810007807160b0340000d10380302c03c1c6014810340000181c008000708058041c50034041d441300400c54807940081c500d94001201d06010b151403404400c02c560003440c440e501c0080c420320490384000741148076105412203800d190707010801070014008a034040c000c5420680c20103029400c4805040000c20014001800705803038140440e036100c0c10010001c628462840c22180c010a03482d0b041d07804 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 71930092 1250 71928842 71928869
    0x70e070309020d030822030f110f150420100e0102010f0c120605010504150804050a02090103050307050705060301030f0201050d061806080705030607170403020f0105010303030b0f0d080405041104 86
    0x80c07540000520b48148812000300b00c480841d1b410f501441205500c0040204170030031000c0820030311075943c051401c5c54000407242c0c001070364412940303005c8020020700c9240105030204010011568880601d09010131411030390340c0e44407030004d40e0601a100c0820108000c40c02d084100c1c0e0b04c00d410402c88018035010800c651640100005c012590b102c1c40c41d144103041c085c000505522031422241101d00c03c034003520b0986210807044072100005001a200c61240054800150b942c5205c407d008510480080d5914001860060b00b020100e900142c072460080c8010408100f15031090700c0b2060b4240b809039540e11900309090300500c40d07034205003000e414004081018090310340c421300589023032508455500d41c0e54010150384020845a160005404c000c444420441040c030058001c3e01c030f40161440400107030741703035421248242e1095000903203400c51440c02c1d0900c246000649030381541e29465140030341d290100c6038820b0348070382405195203900340075002105034203031405000c0c1a00c2005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 71931342 1250 71930092 71930119
    0x60c0721030207020414010303080a0e101103180703050606040905160f17010b0f0409030c080f13141f09030609080c060c03150d080d0c1d060c070e07030902 69
    0x100250044601280511b00d8450080070b80000c5840044c122030341a6500c00c4249e940c00280c0014001503040102584a0100341104e1440603014040101002428640e1640b805420240d10300110290b400c0342074008010910118501158650f8840401d40d800726000030b035441e140b80b80040a5014902400a0000220b041d00c1c403000c411040320080c800c091b11801c480209a800c86030040c0030260b104080c01130404503400c041c4c00842005002c1d081c0110244030035100d07c205640300c4061a0380703580000507072040d52000c0010b100d014041c0b070040e00c41c50703074201c002003105528405050414840e80c14141211180305030403a030041d40d4024401e00a000f0540740003082030304404460340c0030303001c0c403c0060700341e160041c01d0340e228400410244600740c55403424404007821080c820340756080100f18118800056006040c0c0d501d040b5555141c040c5081081c145614424049092152100303f208400c1400c00140c10b0081d15008002d961040d220f54800f50300030312041d00000d401505004015 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 71932592 1250 71931342 71931347
    0x90518060f0601030e010b010e0d05030405100c0506011706061201110a050301080c0d0305040303030b0109030212060928020909160305060a0e0304030b0112030908010e010b041d060c0721 82
    0x75005240c00e8805018180d0807800141c242d41804a820303000481000d4280c0e180d14154821807002400f034800e480c5003503214804580310640b503800400105041c0700a100801008101450041403110729800402a0425440e038880c6009404c0c1c51082000d98800311355100294883d0b020b4100446000340d840341c81e030a01400c1d5400910038040c91380140c1d900346603e07007011010078040075815034a491034242159000d8000700114100c240c10000080c001200503203900c40300703c484d001d4060050056146c60314132549001c203119045c0307404141416900c4142d8481c8404400307003680c108c0e0100c24503074410b00118513205020384460040044e1080000c180000420080d0180d0200c4806101000c1e01c1c030358803075881c410f0b8400202500401c9004200200d0344504091101d40309107042051242d9440082d8295108252400b440765911140078030b5502d007500ca5002241311512940e580107803154409520b8100050416001201c0001e00200b0000000790b03207074400c11502c920000080360320100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 71933842 1250 71932592 71932621
    0x12031603030f1103010b030c13030f02030d2d0c08030a05010501080c0705070603020c0c0406090b0f0f0a03260a0c020a0e10170109020d0b0f0606070b0109051806 71
    0x503800320b46841d0102d01e052a96019038100481480303011491a441c00301002002e506c01032441d220704400744170b5144d0b0020418442c400841c003c840080c1100b84500416040c00a0213a07070406101074201c00d2561080014240300700241c030840440d0364103610110a2765160242c500c010441c40c000003c0161001c92a480305042e21801e07030300c007503040d515190381500034413808102030f20a034081402040a50f104c0c1e0010a02c070040072042d034032010308100101d02558a1904000350154551807410154141340004016441d822141c41000086441c04030f0081103450001031b256040280490046d5000c00c001c918602c04119105991046d400d20300510980811208a1140e280f013040002d0042c019800c0600031000c44110400480c640070b91f43c0000702200076050919520365802c038015030380720300c24141d50034050b00001c0305d01d1801200071b80603031380001c080922560082c810640400c3c2c44040030b80c1903443c02640001c0c43d0700e41c001c03101e031101c001c0840802c05103c1c40040101102103010b8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 71935092 1250 71933842 71933887
    0xe0d0c0e090105060307060507120c021002070602010b0303040f090509032703061819051e01050a0b15030109020a230706050a0203060d111f0801031a040b04060b1203 73
    0x200f006444003403c05884032450b00c10300c0002003045c400c2c40c1c081170008210905401c0f0a082825000405a0110345020314124000d40541c00406c0e08201c0300381c0a004407926803808074041d5203060b040c4800000b940c0c02900451482c180d40385c000460508080084501400d45040d6030540c06840c2808000e04081c0111b14500a020b0030740440e81c000c43c1480b08119040312039000d8031541054000c1c4c03d80d039400b400700644a030712a00c41c48003d05a0994810102039220200101e030901d00f01030044150f4640301589801018056404426110004180c906503007420501503920030748403c049482035580f020151500903070747ea6100303000000c0ca000f00041d504c110400d07c07043d5503440b030800880c0800c4903c5074003c1000b07003120b0000399581c81c01508101e0018108041910a4078148038510400c101c4200490312070300c014410b00043c5100e00000c1c180d420312500480c54039a40f88082034102074801040152600001c650325529040749031481c0c44404100ca40700c040f004000078640c0d45045 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 71936342 1250 71935092 71935111
    0x305010b0a0308040b0903100e0705030f030703020a0b0a23010302040b0a03170901020f030408070611070602030f0711040903051305150702090403022b030507030c020d0e0d0c0e 78
    0x40104418182078011408803500594400e0805150070914602648101030b161303814014403846c02c41d110326a1003568982d00c81c4a0043c8403c6003040241460422589801201c40c0d006000d13903000a540016101d00469111500307280685070708410038050451001800203194802e41510a85100d250007107048070700846050111041000c20301c0040d40e03450001134050944d4180048003540e469000b07010702c070418411511641c0120fa04642180c0040d0007407091394002580c1085400e6100c40012100e00c81c45025201882c60480003075540d2244d03000550406101080306002d0048628038511a5000074200b4814030a00740b034020034583c0f2040c41c840a03502103901c08505810001000110317604603202852510500303408001e08254000c00171000c501c02d03e100c2040d28680700d0301d07800b03c223041210700c0010b02034052009020341e503004103d00c0815107081600202d9550002d0034007008001c81c240003080c03e64003408200440100c603c09419402c802400080030668600307050321030300050 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 71937592 1250 71936342 71936351
    0x70819030f08040213180b04080a1412070804110d1505070f080a0b0d081303111f080c130f0f0501080609040b0604090b0f07110718020f0d090507030501 67
    0x88005850490003503d0282d0490a19540c05056041c81d6000107444032403040c0004020b45d103607903030070481d103400c480440b08100e000c500484403540000038500b10482411142d81040d98541200e031400000816500c20001c101000c2030a01030f19107200418610050036440c40811503051100180303030204580c2ca0540e04d01000036040c1d5218036074001307140c0d0303103030b91400e03403d454041004000c2d0444070035165104810900060009030b03c0300040c452601e40300111955103165080041c485040621414000d0030045c41406ca682641041194100c109091000e02512911905141c134040c1d0b04124280c3c0c00e04010204403c41d030780312030b0401c5402c002a840d001c5074448004603003006040d00c0140d008190700c0e000c0f030001030f00d003445240d0121001e80300290303020140c3ca1320025000181e407108002d00041c02807102180c3d2041052403002c2804008105043c640040300c440214090b41a0300c100d5400300e091921044a0030841e840009404418001c4104500b040c036140d1101b840215071399840c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 71938842 1250 71937592 71937617
    0xd060306111b0712080c0c18070201140c030a02071a0703060f050d0803180c060a05180301090b07120b120c01080115021c0315090203150402090616020307081903 71
    0x3030020a9840b0000071a139004080c2d5152174460304000e07145002801845c60220503602c2e010744100e40b40411101e40305c201d00b000c94010382150f500c1703c84111540140000c1080b040c82a00c01c807070700464030720300c016a02c1c1d0742030900340081c2401d142c0c50358104490743c0c140454141c0c190409070540c1c00c022000602d50342c1d148200410450030190040c095036041c400600280807140b485620429400107031010340050303400050071644082c1041340864008683c07440220031300d208a0ba1503a1041d0020011140780b46c40e61461001c00409100c1005000c1310315074411003042c0c200b40c04503000075000c207200e203c6003030486440c0d48002240343d001904140000600d1170200e1200d010140454020300b00500e4007940741d40310a1003880a484c03d050725080841b604a030036860380030040c001800e00613102d080c0044482a580c1040038110700c02c2c0d006000800c20340c8e40300001c6a080c0e810001440084514500c046800d18a0a0740203181d2405054020f076407510021050070656882543d07000c0081c1070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 71940092 1250 71938842 71938897
    0x61104051318030e01020a050a0b161d04110c01050c070b060105030f01330c11040e06010b0d1103070e030d03060e07140c0109140607050f0d020d06030611 68
    0x500351855442c0c0d5403040d030064046401a40305100900040c81900c2845001d51111403421215100c00c07640c1402030f008000d034030780c409503485102c0d00c124030341110841026104400c003190720034040c501c100d9a6160080308a010b65040301c003081c00d01e800a004c60301d801c16502040780c01006058038480280300002d00107600c03c0c02103a2080000d00032035081a400d00c42501c843d402d17000403205451201076280108207200725040c00d41070b002541d6000c140c0c0120319100d80540840c4804500407818000c0f0703501860404510141501c980582640d03d44036449088030160000d44c600ca11489070010070b204000b64851480e440e0801c0030b4085410441c00710308103d085410030b00c02e01d80a0740740417000c10503a52040340c0400c050b00e281111700741010180d120741421034003a000300312001115036001410541091004580c024a5800d0260420800b00800c0c5107a1080c15084100103500050394881d4950a030b1124001d103400c81810011141e1144800d207082e84000301c0d41181c4440342507101c2ca441c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 71941342 1250 71940092 71940101
    0x130806010e1b040603050c0702040f1b2c031002071a060a060f030c0c0b01270203060d0813090501120209090d0f0c0204110c010501060f02030408070e060105070611040513 75
    0x10003010b04949010314001d421070040001600c1020b04020030010350340940d4880c000c0b42e013051801200094201207610b000600180340030103a006000c4c0307400001848440503100b218450514060440c10084e04400007405d008115010010641c07000c141081400540101e04007a200029800d120030713241c5c1e80411040012507c1200001a030460264042e1031094101030f4010b0303c142440e03000f20a81b0750794040c640306c00b41c01510114031404042070110000240e0070304100e002081c01c42ca1400d281010404040d42c528014050110010300b102044030307001c2400004098094081010f940c5484850031103106445050b4400c02c506004a9030b0700c200440c1102464403d13460b2401d111210a07001d940c2d642c0c00210a036405640c414100e240710340d210300140765600f5004000111903050901c0585440702c00500c010440d03000340014082003030001169000d6070201004254507680d8400100c0b514820a071004002c5800c20000c042e44070b070340354043c4c415540110f8035014150031600c942c0b81200d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 71942448 1106 71941342 71941381
    0x1103010608211e0c10020c010b01030b040b010206041e060f02070309170d03110f220602011103060d05010204120803100b04121502130806010e 63
    0x5400540741d100c002014040103800c0400d0310f00141c1d518030000c0340c05103a4001c00210700e9000c000800a0b002100e0071080103665465110013054080c10f031001c0840d000c28200380c0000f070540340c54040c4003002d81040c0e00a01c25940c4907201c00128800603500c1c0c021403403011801e417004c04c5081c007450420f00540c010140c3c2e181003a24000307050901541c0a821300c0d107216145840c2401e00480c920b940074440d40b0b80031034036120343d4880e900d5910840d024083c500200040070940c050f01c1c00c664101c2402810811810aa507910080c0d003038a40210708100c0b40107082001885c5031600c80e0040244602036400142040d440f0307504c01e114405020829200e03141d001c0100144c420042c01001c000c0c080541640e42018a0260070f0381c1d4000224000601110713101d55901c604801c0c0f075041d90090103000d024006a541d40d0f1074540d4480038203000f083e0903a1003180001307551284240c00711402 = true := by decide +kernel

theorem cover : BRFrame.Cov 71762592 71942448 := by
  have h0 := BRFrame.cov_init 71762592
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71762592 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 71762592 ≤ n) (h2 : n < 71942448) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
