-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0639
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:52:02.614792+00:00
-- url     : https://prove2.me/submissions/e449f018-f442-432b-ab0c-41150089d5ef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 114748201 ≤ n < 114928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 114749451 1250 114748201 114748229
    0xa0221070317010b09010c111305040b090c0f0904020d061406040f090b01060c081e09040b060309280b0a0c0e010206040c05060d090b0717010602070617040606050909010204 76
    0x2d5a01000340b210f040b541d000b64542e041143d01d2005403104803800310b0854508011b540401c103241d0302e4001041c00300c4503031074000907107103020318040480d00342c05031030050280d010546004150361030f070841c956141800c1c0c5940c0d41941300e030f00c0402e45010340564010062401c0c080311080104050304528071941d81190305209500c00c46c40141c08554990300c000d0840e17a00400140103041c01341d50700800503842401881c0c070b411900061592404031400300e60030038940028a00c84a45013a01840030800c5c02114001e15504107210f0386945e8601962201200c1d005180c2030160140c5d08280200d9401d420801c68041072401c0340010300100010b40c00307000482d01c0320103508025440050304900c61030780205200941820001004a507400100d400c0a0494940d210310b0300186513400168040e2066850b03031502411840c1c070035480c00740140c11a0045610100080001075481031208980006d80c4103151002e48450030017101404641d00310783d42100c0d4090600c60958415401081121803168046034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 114750701 1250 114749451 114749477
    0x30a05270615030304050307030605060306010f140f060d0c181217070606030206040305010504110f01020a08090a03050d050409140c0405120a1b090b0a1203050a02210703 75
    0xc1036449849400019a201c10000b494030001480000b0505100500b02c900745566800000d241948a07003049508945a0051048034201080ba55000d00b5292034208161800c285e921402042800750783c610030b4184088030b42e40c80d1a484203c1c0c006105082d0305000c009103017035029110080c41c000144918400c00c00005507401103c001d203405991080e551183d1800010343d4440c07035081389800347c0b523003a03607800004010b030f84800040006500c118004a01c0b4a05401d001c0c0310742c1c0c41066000e008400703c8024188580e03010505803402640705408507200c6040b900490180d14080d000201580301e2201d0145c001901715000d88100c651200302400000c0d50596038002944059901c074003402d03c14041070095280000c00450150320510403214400312036280c07004465880d05501000340b60360b41d070500000714a0300a0716a125820327200c09070004d15007940600ba08076a000050204178000c03a001c0c80c1240f0912000c079200240588004e241130724045070518613031020804034042241141050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 114751951 1250 114750701 114750751
    0x31e0b090a0e15071101090c080c010e01020606100c060c030e06130308040209060613180b060705030a0c0219031203051807090f020d090c030308070c3203030a05 71
    0x2c0445544601400520442c041d100d18032400c0a00490180104c005451007110801d04c6140c480724012069109102d14148209080042d180421810407200c0406407240781d80002d0000c0e00440262113051801142070b1003210703022a8403400904150604490031038440d4103030003500c0c028912a050b40e00544a514070b29088070b00c1640014003080000000801500c3c0201740550306c400045c3c03c0d1440c04181d0f642c10f107107004464100400300444c882000c80c07420014400c13450a4031041d20043d20308030080c1c0300c0903600c0c00b8420300d480400008801213003c41d100e0444000b5644d81d40e51540a0230781c0c50313203071031080c0075007600d40d180000b483c250000320700580b441d4406141540c0b040140c52424100327101d00f000341038694841e03a20190208450584456284544004a8042d58a0b10401815480e00402a03800079000a00b080888410107001c2203411041e44801100042412000c1084200000303804142080002d450301010040120b42086500b03d1071190142c07c81382400090000020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 114753201 1250 114751951 114751961
    0x200a0509160c080f0c010606080603012901030617071806060e0f01031b0c0204050703140106030218061b010c02070602030a03051003020a06180504020906070206070201031e0b090a 79
    0x6248011201140801414082c01c4080da4040c00380c10f0103498440c008030391038020fa0046842c100306039586c040c00c10007250302140b41500107000b00d0092010804080e10035070781c505003016401c1c25100350042050030703038000d61200004140e440d034041841103801131000c0d02c8043c14410000360072000c118005602000c2d11444084d90b4007612004191105001070005441c030443c402c1d03060580d141007081c580b25504a150709006680d5032400b1f04121644140401d0b20006091101854100449407446c4002102c00a05540310740c81c0040c5c46003030440f41d00440000552049030070080004072811a4200008036468400c2d0b943c00920a051039080100d956070780328412a00160002d02c20340703105601c030790440d40e0006034a042980609413030b07070005110702d82c1550000c004540d641030f0401c8601a900e11344c40c01084101c81c1141411504400700d0355511640703e0003446103d0005440045a000c0c0d0710207200782c885080d082070158640d82c100e100402c4000101d6200d60328910018403d05014091 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 114754451 1250 114753201 114753211
    0x10b0609060f0306130e0102071505040b0c070f06020307090311100836010c0908070b1b100f0f0f0207170304031e0302090a061107170307200a0509 65
    0x50515100c201d00b4445840e0308050421540a03585042c2c0445010040c01140c0343c0e185480001a662442ca00c0d200500f18003202541501e079007004100030104000c1d06105a1241c1821803003035807160035103410103d0000b603a000506052000c070601484c154449090030540b4424840c11207501103002c03c0018518256019900181011002500140310500c14000131101542139a6a03140700001c1c44803601414845a07410f17030b55403c0019070940d40711107160000d00c81000500345090400380544031a00c41e9542e508203c480324121080226810010200228401c41c410440042100303040d0000c3c140b5032207090241ca060031581c003115141e61080b1590150b1149004e2000390070108540400c2d00300400590505c84211322803101c840c0c94803200d0844401d59900141d4130718504d410401482142e4024500300b001e106c1c01407070940c2e40010504159040d81905206510303113070000c01d280d8403501c94000c0510640840e15024450030410410124804441009030642c4401c20b0000c2d104046031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 114755701 1250 114754451 114754459
    0x403140424020a200d080d0b0427030305060f04090308060102070b0c06011a121008070902030c03070c02040e0a03030608060106050f0d020f09040e03030412020102030903070209061818010b0609 85
    0x40070004d40401d00a503201c0584025001401450058661104542040e00e0f60707642140c450f801c480709403501d4410003044078001d030210700700a048501c0e1008540480d80004051560300d001103040ca035103100310308a01d100001d04c240070050040c40c000303086040940e007407405403240c5e14010440311400f406a5000250f150b0050519a00c1c140c5a0806c454141100e810310302c0c001c0110071020f1a06080840c8264014004102132038581400d20b0b10344602c2d680403a800e544140280060400540100c07500100140b030038940d5201c403800043d005181d140803810781032107502c0380c11040513010b170002d0046804060607641a82ea861806a406119140652207110010401070001d40c0b99503010300001312a9440c0e9500b0310500d080440c003140d000d0351901e102c95001000300001c06c18070201c0720740c2061080c4000e6040d42411040160740f07006525009202c0c1c0074140c000755240c1c03034201c50051859207038106d002d243d05000c1100e0350001454600c3c0c9540d03508041e040c10030703800e010742164501c6030058 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 114756951 1250 114755701 114755723
    0x207020925091d04171204120203040302061c0b060c0a1a01080715030608030a0c21050405100e09040308010609080303010f030303021605010e010b0a05090f010e0403140424020a 78
    0x441403c4944800400490300c00c400511000185483c8102410b07060600c0ba00c0301000307082034249108415040b1545808542c4100410700050b202c142c00e03500ea055000d8034580b0020b00c076014200180480ca82c0c0c0c182c200c0404603002c820706c40000752000c00c86008619845641320702021118200e0400d0007801d44070b81c00b206081100059120074019450154540002d609403203108150956100039000300019890034654070600016120b40c0d5800b100328400b90210350b0031000050054050703440340178800c2d50030350590919940208070540740480006e2000d10945000d10380070307089103000c0c06404009001d2180c086512400042128140c40d880d41041804910316502140a54444c14608802e6019a104d420001300e090007840c5d0a107600000104189203600140628a01c0c40d80c085e900c555041d4043c040c101c1d1070f190709241940e0040502030311540c1c1e24103090f02c1e000304254000c200300c0070004000070394032401c03460140c0811000c070b10031038036140091040745e890b8040b41000c0d100820132 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 114758201 1250 114756951 114756989
    0x5180603061c0516030803042001020a030302090307030b100806070c03020a060f09080319050a2d0b06030a0501061202071a04021f020c0909070b0304060b04020702092509 75
    0x5054240000b5201d801100c04103a03e40c0f10f014400c01c0c403540304450000000c0188401c1003848003490401802000d201c507842801080000d5603140303070043c00303000d240c0c1c005003580080e20140000005190006140c800c0341c1820381032200b600125104480841c0900c20110b00740601c21070b402c1c0e840d0b81c3c03d6401403051400507103c0d0340007462099040c0090366550201e01c07000864032000740d403180c042046041038030141a8841003d4640052110400300c0c9462110300d0a120380b080c102c1241c044242112a4400700c81c515a4000c0c0040d01c40c9513403001d0080f04000c0000202d802c40c44c10b80c0d1850b0307142d0304100900388800c0c09901980400420300d0182600112101118118056005000801d003e00c4078092844c41d01e21107802610000068210242200503428003101098001ca0198010001c2e02e160403c10420790101030001005a034803018045119951601902e101503002030016405050410300f0682803411000303904007072030f8107250811401d8099820041210056200040c05883c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 114759451 1250 114758201 114758239
    0x60904140703150c020706080c04030602130801020f04061403060a03020f0411031905010509090a031b0203030a03020301090f0605150705010207060e01090521040501030b01020f0109030518060306 86
    0x9100a03500348100c4800002241411031a031001e0b100d903550005142c000000c00034140410340e0014000d00c1001c02c14021403901c40700844084039080b50006848901c0003031400b100140d190310603202980003090b61060784d001c20740180111662900c0c2c6403044003020400c058580002c680840c0d0040c80348400f0400750401d000c20759080703100100001511941030380110015041611620b460914946600c030080145100d000c9c05098211503c0314a4a07240749a1942c5000b00726008080006082550a0004940e00c000d0311307140c3c2c02000c0d41d813100001c202c020001d40003486502e1103181803650b51621541988501c1040c0d4070044c00310010441d96458512080c1e004400468066500f0402a00450b035940b0440480e03803442000070485203060300702240b50a00004003520040c10203019095440305440440c1d0482e0000e09001c29645e4105005034200040c0f92607500640d42803918000070183c0c418002e102041130b003465403a00349250750520800d0b0008954258001072190307000041c01345 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 114760701 1250 114759451 114759473
    0x3060b0403061802030105010e0105120102030103350301030b0403171b030c070618170a050a0309030c02040c033201050904020406030f030c0201020606090f060d0c1e0f05010503060904 81
    0x22050f01d10014024a80d0129003121001d83c0180c00f0312082d003006015519092000241c0004084020740c115411500c90390b42a075248100c2062450042d41da08c103031041000c1a62a400f0706001c3c440d41c807581d40f810269207080046808400281455503400c0c010900260002d0044d2a03459451104000c2851000c609a1000d4a00c0c82c06560501101002503001c1c040e1000d500c075512074600da281c415181c85218a18520740c00c102411040c04a008901c0d4010180c1d2101549460042403802180c141503c1b030b500e107000c000e90402e041001020310303542c05400c10710398100243c0a20340c1c5104041041b03210b2204000b00700c0f0800d00014010080c0703203000705100350004d000520008440c1e640781e4034020110f0a0384070031000b02e0042103004055603014080d0f1688000300391609503080c5005180d019850b00b0080c0308611074507401c40340700c09000ca0681d0520150041002040c2c0750002e1301003600350081e05204407840302c8122070340801d155106070182c90040c5000303460900e4949440d0b50b03801149d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 114761951 1250 114760701 114760721
    0x71d01110c0a12020f04090201080a05130b09010207110307080d110f0d0f0f0801120f030e0a140306012c04030e09161806081302030723030d03060b040306 68
    0x11007055510419039503110b00b544003c0c00f00d103003007181601d0240b040c030988000c01040d2030b1142d0314100761f100260341c2103c80d1951102c10684001400d90b58034420408008000c00060a0701c001a001c2016081055009048440c01500303800000e0581d40d040550712241030140d6101034008002d1020700701c2c0240001e104a0400300c003541c00404420502a182010398040ba0001845214400c0c62450300449001821880342c82c24071041c4d810302c6032185582e090003c00402404201c0341d0802818400c0142640060f0018103800405594001d0728682100e04034419100f03018a00c00010000d4844034641074410003c4100d44c81e458606054000c1da43e4020020b03014072a01c400180140e60307496401c80e11802a00c0d9244000011081e1700405d10090f0f00d0428005042920b0306200c1950042407241d409080c24030075044600b014400310782041d115510a40042d078410b13000d90710302c010300d08440d9243d05055044a0302c2030b080707000840641c2c54502c20f2503610348080000384045080c6400c180144 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 114763201 1250 114761951 114761953
    0x319020705060c010c09090b06160503090d12030c0201020903060106080402060408070b0a0f03091a0a020408010f06050f010518060a030e1009050c06130b03060d0807030512071d0111 80
    0x180d4420100e0200da100d50f95000c40c40c2d641300319900d0b0301c580041030384d0040c1c0500c0104025406c140d42c0810100d104d07940d44000946034406100003000030400840702035600241c11072110320124a4041c20307a442d65411880400c0c14400d1801060f4414402d442581d5401030017400303940d01c2c26905940e03100f0b001e4030076600003a041001156041040144030010f0041082242e030f55120741400501841c01d201146040506004202d000300303c0c117203012060307080009000b408075180c2c03503030a800900c2941c1c8610025404d20040410303840e40e603405001111010b035100ca003d41c4541700116a240f192031450a0840e00d00c80881c002800d0820180160305518100029404c40e00030109261100802c1c03860300c00c68a4207816001c00005003c1018440d03015102c2c3c6040c52000103110a0b40c8a0070300891904160100026020b5030361440d04420403900000000c0d80c60169080003071183d8001c55109200702030301e03004200b10300d102e41d03542001035441c000306440030f50304400110341c40003035100b6440003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 114764451 1250 114763201 114763213
    0xa02010e2106090303100501050304050a15020d2405060301150305041e050c03070b1903020c031e0403171314130615030f05061c03030204150e0f09010503031902 71
    0x103540c810000c00e800303441c404005541703d00d0400c0305078425802e0b54104604011041c4180300020300300084401c0100d5000d0461005000a0f07442e000090241072280900039050400140c110030342c1d80c0000f061900742c10250740f034140d19941841050311081c49055040300840303a020452f41d1203030b44960380052007920803009221140c01c48003001c1e00c01000a4680b0b070484040c0710010700d0304102d10801400c00d01082410554810900038901f001e025050052580000358001d00460600032140722480707890008040300020318800d100354009000856190300c40603200f61880c20000306a0384000c0701100700409041c00e0180448c000c000500045d03400a1240701e400d50540c40740e020740c070b001c0c01000d00c3d104072000340124010b0549840d0510226414070b0001400110f0311203072020f50742d03030174030101180075a0110302d021802031045500ca15010001c044040c01031561002d00d0000c000ba00701d0301c0f03070006c451500400c070704800c082c80b03500d525500c00c00000c160961290303402c80c2021038500540f81 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 114765701 1250 114764451 114764509
    0x4050d03260114031b0d081207051c020f0901030b060912010506030d0e030c010f140c0601050a0531020403020d0602091f2c100905030105090a02010e 66
    0x315440841e4005209590800140810184001e1400544408400900c0302d10b0145041000304044504254025400e50f01200700f030004003011152201032555104a4918286800034115003108100e0f15450642c1800000c141803507000f80d070000d64858880601d4124000c0065004195011000c0c0d000b0500380245203441e41d0b0381c070f80c465030f11107180700104e07082c81e141040500b484960301710303d814070402d0202036119443c0040c08008031502800c02c266244c1c3c02120079a0b1030ba840d41c6420140603400500c03503510301000b01d03c2d00e04a80050b50520348141e260300800c20220f442001076048000340301d030001044040f103c5042c8004840c0c200061800d912a00402c20300301d80301c0b8003510301301d030001070b80c1416042c501c10000b03040404000404041808020003490741d940d40b60710407208900d4481e020000d180c00b1740104031082c0010a5000c216105280103420b180a920940c0c2c032a5285c80c0004401e000003040300ca40c429416900c485584803004e081003240d0300041c00c1d01803503c0d1703600c1000e8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 114766951 1250 114765701 114765737
    0xc0d0b0a1e14220809060706090c03050a0c090608150705090d05160b0f0406030c12050708060102060114100c1109041406060a1a0c01090203100c02100203040804050d03 74
    0x4181c8000040040b02d481c500341d40c1018841d060f003908401140300400c0f020300491038107402d90b00b407a0402c45002d0760f6480f49007004000b6100d02d0401a1050300d03200000010018005034241825104d110b403c0c80e116078600d0b045040340c0480c454503449410a0010070104d0351880402544040c090034803c0c00d0440d51004550440341c08001101c07140e004851481110000b240303980c004102d9032041c5481c00102007040c1c00c19018078490030b014143c43c0da08a1203902c0c0102850300200c003042c80100510b00e8054402003110b0b0781a07036030502501070750b000031422820701c41111000f020702520f8803410030300c1c1c1a000c41d0406203c00c001d880050a05c07415200b5551840041d0b40100e000d451040320391000280341d6030914101600c003600c105d818540030030841441c0c00e81c0d140c1c2003001c0c03c05e40c1e442c0c0c601d50803458050641c2c00c030002e60502503014000d02990307280d03002c0c044541d400c2c0e080307646c85201382110400300d110540d400741c0fa03044c00340020001c80c54030500c4400740b103110340341c025001080321841d5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 114768201 1250 114766951 114766961
    0x9090203091f020f04060c03030f020d050406050601090812090414010803040f1403060f0a020c01060305030c010f06031a071101110406030e0607090b0f040e09030307020c0d0b0a1e 79
    0x414a03039044aa000da03284408003091640c0300c01000350840c90400380b4407a1403441e00c41c61181c8018007900b04187d0003414041d034000d08440342e2807001559200000a00503006010407101150040c0c82c110100380d80b544079000741029210f02c03400a0901242c136400500071904040742c110742c826100d0360221049004503803030f50b00a2181c00003c5403100e081045d82c6d80405859004a141c40464240c1d4841907034000400c00c0d08260082a40721041e100c40742904082c0c82900c140358a40c1d820302d076000040100000c0205041d0315100020061400780102980a99030b0f01d00c0084c101001e2403072490070714040f400445800001d14200650054040b1300d181d070940b420019800c04621012034104071041e05400381c040c0010104019001500e80342c440500700c0501030040104108021402501c001c2c0c44108550242a8140340d4070064500080515960340c811211080103008000f100c10141c185005082581c0780d20440c0903074240e030744d00f8040c40203045a10b001c0b15404c8400240c002c4d1001c19100d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 114769451 1250 114768201 114768211
    0x90a0e1b0102210d0c0504081c080108070e06060a1701080a05060c030106270b0403060204031b05030a15060b0d05150f0102070905060a050411030a06050d02010f0f09090203 76
    0x142000900c5600180c02e04212400083c44400d800401c0e00c40c1141c0c10048807040f40303e01000190b8000e001c81c085a141c0180d4019900500c1500d81100e07541000281e0480c00c00540d50310b0300550780c0c90310307402500c1381850311030070300e9850040c4081244d134942a0007418000205107050501c2c1c4000303c01d09078647c5030030b0f0f1056240341c020a050b20203114044c0100b070781c0851100c0c02c05196503d802002402c1282c8086105102074180d0b500100007c580782180c80140100c0b180c2a0301c4036243d0070b1000c0258403a200071034250700e010101c1c0490413030031007441c0115075004014202c800780c6500c0d01e140d54058804007040c1c9550f25407010405450070700c06400e480c1c100600001e200e180070b8041c100200200c0003501e215030394120600106a071b0020700030041d200b20790404100364030b82c0004169000700075000640e1041c240030420703a0248214015511425016000344103607a540d0090003603d82c24144013a0024449800310380025004664010810200e40707092508140e40b03000c810700700c2c0c00c00c1e58 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 114770701 1250 114769451 114769483
    0xf0a0e0406050901050105180a060305100b01021911060705030d06090902011d09071101020c030307020a1a04020105030c090315070306060324141906090303030515090402090a0e 78
    0x3031009109141c81215070228036800204499410b00c1d000444004c11041a84460404a00082c028450b81e810400055505c80126103100c0e0006400001614030448154018411480000303501c001801e00400c03159041015020302818101c10f01c00d0701e0b4007142068960f84010041e0f507011480390701c1003000a2107a400c0c0081c1c01c91540c400104444083d0a506d207c512606d03c0d00b0382155100c0111507004041400c00f000c0d55206028114064014102209040c2c0001300c1000442d0f9000301e4a0b41c0780c0c600c10391080c581105a42601400c3c03480a070340c041d00103241071002900c4901040010301100d000201110365000307825401a4104104542c2d442c0081d440d00401c0000c6070300340c00780c0c0085030285024100e50800c172030a00b2040314014440c01030011140c101401981e2100825204007280464171450b50540b80c90011b00048158402100004e1501d0002804041d11001c500f04100d4020034414542d2625000c012950304054000402c15a56950a03842c5410401c0482c0081c00c18072 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 114771951 1250 114770701 114770729
    0x14130c120602030f0c03041716051b03070f06050f07030c0602072a12120e060307051804020705150709050402070c03020301051b030a0c021e0105060f010509010c030c020f0a 76
    0x42d2442042d100060176805000d1401d0060200045041404294603032041070b0564031120103108100c081d51003010090a00d02424484250301c0744800100c509281059080303900555403030b142030148018902c100f1000038014400c6144e411008001007007154060315160700224165202d510032680f010f40c0444400c140024000010200009600c400d044032100b81e81c902840c1c2240c8110300d54040400130811200b00b603009000c3c5006900c0481501800340c80c1075241c2ca0400809800355020f1000f204140c5000d440c086101e00d898000c484c2042d82c0b08000d8010019050703038040c01c40101425080600880b5500803481d40c9640c070182040502582d0610107007880c500500d130840c0e0007e0b140010070b600041d05044c02c4400d03001101d401c4889140300181304082d03680d08904104060048240010800480b0a0b480d07005400c9907010b040c04984071882039492000540303151042480b001e01107059030b040c07403011901403c84242c8960029100e60803000700103002039030301201900f08481d403120707039 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 114773201 1250 114771951 114771961
    0x90a0c06050c0304091b0e0109140d021804051608010516051b01020d06211a070e090a060302010e12070b0d0908070b0106020706090506030a020a05070506160e010314130c12060203 79
    0x1003210102e104001303081c42803270325080900d0010419900c814550080100352405401c54032640094510442008004c040038106450400c3c0c55100030b404418940300c0144020075004418410b182c0528a41d1100c4450359600000030b03a5903412241080503448510000d0000b080002e0004002d4050304030300004001e41400c2d001c80150b0b40c1064a480d502d0f5081c02d0443c00980091040c07800104170840501c919660524201d5019028003036081d000300e01c1c9024040030301920340050054134401d88a40318900c10100234088009050300d0501540c1d808400e0801070b0403d0b100003051129120030011609a00715224080c0a5000400c202d50030842c00c0300400919905001e081c0240009190100c00740c2e14180c00520180006030440c0c070b045500255420005018504a45501d0b5000040e2010340ca014003034083d01c000c9000010b0040307040e00024650305e6100317204841c2c044181000e135040948480001b26007114046ca0111051390381c441010030018080c007400c0300300c0b610480026070b8038544 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 114774451 1250 114773201 114773207
    0x1d0303180d0b0103082d030a0e0f0d081501021903030b01030e34080d030506040209130e010b060f070b07020a02030a050120090d020114040f0f0905090a0c06050c0304091b 75
    0x1e00909071b540030508100c40c5845503204103c0750032541642020501c002c81e11562414152a048900302034401c0c3c03408a1a0f0913041400d142c45043c2240c0d080100c0b8201c00d0044e03850f8403900d09a960b240000d0800040003c0c0242c0c803000c0002e01c18500040c0750b41450184031b1400d8001e4203030b0743c40300a072800300304014001161000c00c1c42c0c0c2210407942d441d07450800826542d00340d85e0091010f260701c8100046864a40e54141c41040c0c1c4010580d04c1d801c915050303070a005101048280e00c80d075003007420040150904034121510282005a003618004035500d07000075581d4050944801c6014100700d40d00036a40030030503007024901070700000850499050300d1102103a454500389203210010300c2801403650f150110640300c5902824a00e0f1a40b4004080710b402c0d03c0303160068041c0e04000351000c00c4144401016006071140c59004001b15262509415504e08078988021300e241e00792401071248030320880c0541400d028010480341811b448903405415603210240c40c2c0b08140d0304400c1f2910180c2c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 114775701 1250 114774451 114774487
    0x40f182001090602060c0705010b04061d010902160b04020301141008060f040b07050901020705041b030609060f03170c0307030e010e090702030301090c0903020a060f1d0303180d0b010308 82
    0xc2420000006841c1c000041c1d00c500e4010400e005228001c2003541c24861b081d000008003050052040000390344444107500154560200d02d40c10303c2c0c0e20310000c00d40559078422516130700b541c00744440c030703002281c1d0310f000c1d00100c010400c07605035480703000c02c00c00b909001c2c42c03d40c001c40088201034411401c044445280001c024091040d092080042c0001f1a00420503107401c03600a1600966480e00140180e103040e125610450b00702e0303d400503108100c20a001c080c00f00c00c1c0b0555007840010342e1100003030705036401405140c0700e00f0b5503220108001440304c80017010310103141c2c180e01c0c20402c03601e503943e0441d0082e0b40c0503804500d0034802400e4a42c0e00800d02d1014074002ca9140410f4201484025600d0005014110b052a86d84042c1407505000c1c4408800665008200c210700da600c410b001401c0c902151840c00210344002907031081e0341d14080080c0181b0001074011414000350550144040d0f0014a00f01e400c1054008500f001c501e26140c03e50103140281101070f030b5001a8800010717210 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 114776951 1250 114775701 114775763
    0x1009111804140303070c0308090c0d060203010f080304080c1014030406052e0311060702030a05010606030b010f2703140d1d1e0324150a06050702040f18 67
    0x14000300100045d49030840003c22045806140c01181d9a40d2800c94901c1c045140010036031181d1264411001c0013010f4000b58143e8180034a061036450b55011141d42d00c0c01140104181e540156107040b07500d00f440403c00301d100e01140f900307e4907a0800b1040c40c83d9640151403c1d201991144108002e04840406c6c1d008010400d090000310041c440e10301c446900c240b0301004125807403003481000959104000c0d1100260010b06030340c01072a241c40d015008041c24452040480c2c1008002040c541c00b0b8801c001d0b2210150320384100800140b100c504400b1088141000c031000780b400080701290804042c00038035250f000090080c11a5000054210404070040f8600c10101811720a80d540358034101160b808030040c0041000c4110000003420100c034a01c01c00c164018038140007001165412901e1300544103000340350303190050340003484041000c0d400303908040358040102000609190b88484810303c00e0f14000107517003405440780300001008480a854000c4902070404049100404c484454 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 114778201 1250 114776951 114776953
    0x50307060b010c080909040c05030111070b060102060105010507061815150506031003110319050a030f03060b0f0c0a080a0207090b120a0305031005030601060c03120c02100911180414 80
    0x984044c3d681c520041c840c41c41c04501502c1c0c1003001ca0200711000b82072001400d40240280421701500052035019003101c401a10400d540c000410701c613500100311181a2641a9162840c2245507103402d006001400360305000003994907000404601e01000101010104900115041841c403040b0f010b1041903801c49482840d0401c144089881c0026403502100d600a0340c58072903c0302000003074100b094070041140c004140f05002c508102011402d608a05e1103501c0750301a10140380c000700c080754454054403d40d41010004003441c0d1084101a12a50b1202c00071134200c10043d507103d1103030360451501c0760090b030700031602400810b225001d076200f600d10075966010b003440080003043e612058403402400748400080899580c1d003020b44124040c06024007150403070f596569004042e1012510240c0001350050900c4070307030441c54048e42000c5542c40e4000d0004521001c0c0540c01003942c0c200c02c4501c030784141890800d0340c6a5032840043e041100c0000160f9151504103207983d440740c20101c3e106 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 114779451 1250 114778201 114778217
    0x309090f0c0207150c0f06020405010207090504051005093d020c030906090a0f03050d08090a02010806010f0314150103060f0305060f0c0904140709050103140c030901021303050307060b01 82
    0x754660000700281100ea04440003034803102c40600c02c0d036070583c49050143c0500b0540c1d96180030302c0625002401110003c0e4211490b0641d581440000c84200b61402480c0e0381200e203a00703021490715004980c12808030015a050184c5180e1040c0412201c603800c07000081704520700c0e1900401c10303000300990050041c015490200519190742e00d1b4030038084014443c0e88081108030300c41e10780895480c0901200d03082050003075182c3c2071123030b9141e00d16105000081e01403400560055408100309e0100c0e41d041c2c52300c03400c076140c240054442581522804040566451011161139405140717940142000c6682d515050b4103000010165000c54000f4490300503005010400070f400000d141e5072040800b160301d84942c641220160291042d00801948a81040e161030072030f00c2d41c0300343d0600030300c0d0310b403604144250380760019000e5488000d2441c0001004500013034910848000550340720600034001842c00340c2101004035540d07850b400c00c3e06d5a600210b81c01c2c0c02c00c1158440e241e100042420030402c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 114780701 1250 114779451 114779471
    0x5030a02030a1202010b0a141009030f150b03030a03060e06010903050607140706050f0a0b031605060c10090c0807091806020c16060e031606082208070309090f 70
    0x640c4141506000b8442c903402865450f01030701c00e5105918000e0014403140300d66558a104807103044400c1e040c0380c4180000011741c10300c41e0007000f0723217011258842034807500766999484061440a800503884990354070b80c4010440360f501440200740380c0910303443c005992820030039940900c0e00010041410300c4581c9070140080760b40050070560041843ca000002d0308544800340e9428051340a005000d58181018081d24201d02601c40d0304c60302060208104440030401015500c82e02160318400601c4c0000c420300c03c81c2008030040070130341034440803603c03034007424404d1030106e40c82420140d404242034401800300c104140142001400401700600540c0c95201c512003040e00300c06030080c1030385e90000e2281c00c00f100600c103074082ca00100354003024207503480303601030304130f000c615400c03440781c06400319400030381d40a0041102a41d525030340d41f400c07654503c0c6885030815090b503008000071040500d8000051030f00030003000b1032840ba03070780c192983e8a80800d24065031000c404c1c0d00c04036410092680 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 114781951 1250 114780701 114780703
    0xc090504050705220305071d13150b01030b060301030503030718030506180a0c09021e07080d230c071e020306040813090f021306080c040e0402061c05040203060105030a0203 76
    0x4118611143d105510542021690311844e09203503c001d040f0b01407140d0016021108042d843c04c06600d9150798441b41d03403600c08020350301030810300040030302406171512440041190b208603050001810300051400360b450004080340c00c264400c8074540c1c000002c1000082e0710a11208405074185001c511542c1540c1e80d0720340302c1a006240c9030300c21101144803045070204202d0107840d40d40200100c0f15a03a11458a4006940640401c00414801c01c080c0c407182c100d12411a10710780d8101c622130303081c044c81000c0c40c805020303685158003074016aa003400ca0180c032545407890141e000d8a114a80c4ca000c1e03494400004403071920720344400030100c4a614050707200801c06c01e07446a4460b940135a41c19503400c00884100307050300041c0c540d0345000001001514254004d003000344a170226a910f840c5e4400080303070382c204102c40943d034000741030104121808580b011140c20138401010321307083c03105060b203010101c103015040c0e1101c19100c01c140019400c00f400320501402c429005450010500c0e0042 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 114783201 1250 114781951 114781957
    0x51c08090d030c0e0301090804030515040c090522060b01080c0c0705130e0607020304050f15120402010504080d12060b030c0417010204030609260a02190c0e0106020d020c091504150b0d0c090504050705 88
    0xd032015250070001d620b10344104100e000d4444464794845240040e420000300420040101c3e50110341007402080302c80d020781095950300c10180004080035400c100038445190f00300045500003585896903645110000d01c80d60384640703c69030086442d6460a002c0144c003c092040daa80218620f0410f07608504a070000ca8005c0f55a40c3c0107100d60340c0380c80c07004a845228a82c00643c0c2806601282d01c1c20680c00701c940d80c0d00d00c4651354244a141d8584050401c2c40c0302c25208122000001c00c81000a1380b0290400e045200c03000d4001401c0c41d90301d0b100c550036541640030031500d40d001868102d00c040010a032031402140c00c0d21501e4108050030b00065070390441b03c064030340c1040200c42604100000b0281007000341a080c0c181d2281940d450700041d640d02c01ca08ac0d040058001d04803c90703484e0810511851042c61376210380710610b4001c401303100007082c1403020214034844040d0045424210000140900100c208001a080d030152000500d0b5030200d42180b8030a0b41004180120300c4e90240c25 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 114784451 1250 114783201 114783209
    0x12030506100c082803092901030308040f1a06030f0c030c12070902211810020d020c0601060e03010b0a0e0a0c0c0f051c08090d030c0e0301090804030515040c 69
    0x103090796602800c2888201c4124549105155050203141040c00740d170300d0382100c01460710480386021244000c40d414520030701c0c03500400320080c01c07071f20041010911802c0c01c1600140600c00f10044524540c070748080f1081c1c0800b200d2800e80d1520240f01040c00d041009901c0000d105026041c00050840000d440c2c14010568501c100c00341100ca80d540c407804d2101c1d070014400401d0843d07036542500100741da100241429140c0c15606840024075404802c80c00700c040000000203440d81000c2044500c00039000144d2081c40c0c650b09001c125906103040143d24064596030711034890001c0c0080401d400d40d1214400940101c588400412030703d218003e105070402520903010030400e104400441d010300f0340b08805060302c80b02a09100a0144c0440c1c0c452188007800758400e5451803024007643c403040155080d680d036500040c0e54110706803299120082c072681503e0800310480941e0000303030030350740164000c0e074480400050410800c0020031840d9004006a08130b06003601d80b5456040483e111881 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 114785701 1250 114784451 114784463
    0x90c171507030b0604031b0b0403170d0b030a03080a050703060503100e0102120c0310090608030a120b0a060908010c0f0203070314090402070605090114060a26030712030506100c 78
    0x456070303250080e0080c03482540301030902c0f921203a03641807400503014001054190042c600102044400034001114240d9402002c8070889040400805446500c0b01d030b5605400c076503038110801f0300e513002ccc000d040d4010b010f90786075611801e0811440c4101c0720050b2829051601d0028204180d48020455400c0c0b002e07613007000a603285181207100e01a1103022081c40e40c1c0140c0f08100082c118058002d9070280b03d061024190190b00d92820004072001c60103100f895510034090079200c1d03407243c405024946801180410740d031603442c000c41d100e00800d800403004212504000d0020040901c84c03c0d6460390107240003800d42c40403e03406526845a004058100401100301030b41000804007103461001018104550f5503020341400c100a001c183c50300c07420b950900d509100c1d038910381000180148401400d140000f460012034a0414082d0041c5800354a4200c4951510903803e1014103030660159000703000b1000202402000c0301d4000b4499486070075410144001309510500c0c0705050795100ca = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 114786951 1250 114785701 114785743
    0x30303070e06130f0e070e040b0604180902060c01020d20031b0f1602030616050409020a020a12030504260304080c1905011b23070f0b0901090c17 64
    0x680c1107407000b40140c01035000c0f01e080754000a200c5c0e15800c4040c0c0304032026502c0d880d42c40f180000300001e0300e01d44224640c4c8420140010b000c07001ca00d440b00001060807500015040c400e40d80411101e40280c045041c2d66540410f48511891090107005000003014000c1803d078203041c41f0b21340d030354000900090384c0c51010180c61fa1910320003104403620661040c20342600d81c1c1e995101000d491400f42401c80c081e0040d1804285410300c00e0b071254180991076141c190500b400c1180c40c0c0001e4028a0191302144100002c03079010482c000e0221080003403a903000b00311803600b03081250340c0d42011440b0750380c05050050a01310381500383d030030750360402d40c0180407030b0745d13400340450304c0d883c006031552030b4070b55031000501120070880154400300c413140c1700101c080c2c084500c4020075210182490401c180e001341d44060589140b40500080800f40c0c81a0507000c07034084103440c0c14108c440b04032081030881e90b5401c2c0b41c5040c04840300003040240082c0c1941400c014412600740d403181c80f4442e400000c00120 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 114788201 1250 114786951 114786967
    0x30f0302070e090a03030f0c120c0309150e060612030d09022803050d0c020a0326040b030f01050603150d031b0b01050405100509070c030e040c0c11030303070e06 71
    0x740008002818000000520390412040f01600d91000d6001100800d00d0120000c0b0891024040c542a514035516801841e21452002402500b0710125120405a890102c0783c00502410658210101d030460001903880601e11660b10b000c0001d01103134415150b102c00c5d542d450b9000000c8944004101001081c8500b080c4007054071322064036030b0034000c284100e824042e072480c07134104242141c0c00340e001c445c0c7c4030150304d10030f540301c10041c80c2c081e40024504a0074404940c04002061410b58082c01c8100c03400131291030f03040b19802076040166400c000000b800601400d440b2072034090281120100c1c40e600780f00c020100c410a400e000319010b14441c2e680c800505024146881082564607134040381a80d0b10718040b200b0000c2400b4040c03045181c200404c1040050f03410440590303901074a00b03001a2a5800b003521394100c3e80404800300014103130441705541f0351f40606580e945a58440c02260305651600d0078880045040030f078003070703030081c000c0001540d0302064030041d04100b941c06650314405 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 114789451 1250 114788201 114788203
    0x12010501052b0803010303030902040c0306141504050306092a060306130f0c090302041506140f09060d02040e1f090231060f020601080c1002010b030a080d060e06030601030f0302 78
    0x5100b001604061020000005154243d04800082842100c080002201102c816000c0310102e016032101303058501d03c0e01d1001e0404c203c4d103807554030b541c4030303541d0400c0c0e9a200080d24010b01103800350b001d45c00141003402810b0610034205190140140051414252240444c00c40c2c000203220b140300304084801180c081c455640070a200140b880000d128078045400b000e441c2440602c0100c8c01140344c5200c215450005445050075100d00c3c0d61010702c000810f469441542d000b400c0c0d618001035040000440760f07500c01000301401c1080c202c2c05030b01c031803034400030130040300c0000d11441b04140c2c81040c8607503000744e800c40301c015103200c103c006032215005075907480c4d2160107000401c684501802c00000c1c100712200c800d030480b09940e460900f14101401e089840313130000e2065011a43c4099210800f92800346100203029545100004044640f280040d20300207a00700141c0d05001c00040040c00340300d4900508015100c0d552031600c031070500d800402e81d102c20511000c0c04001410f00c800c8100340c8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 114790701 1250 114789451 114789529
    0x1030c0509040606051e0408030702010513080a0b0420180a0f1d010612031e05070803180607020708030d050a0207051608061608041202010e0102040806061201050105 73
    0x400030b0000c2000c2e03600e80d5805803495010180c0c80307449401c2803034190280300d10780c003c0b1001d1711582d0f00994140fa103254019a55500284d140c5152034881ca200868039020400441501d41d001d00c41030101da0a003801c0c1244018088a0103010400c1d0710800c00000c0e890b100b101c006161100452004140d032202041001083c040f000040090b090003441e02100301581e0304240a141c10300c0003040850350301c0084002e0101001d400a0104d101c440d43c407601c00c140f02080901141d0301d03042907442c00c070003a0341c0e0140c15441214441006900300c51480a80300040080e140e00040e07500007040700030f09001e0019564001c100c620301c8090740b60030000e40030034103030317015030b21401d82c07000440350f08070301c0c01031411182d20a90280c5103042c82607800080c94a8801800c6245021440e128540c95840d161501c002c8030545000400c150364039048100c0007038009100902c01030041d14090711660401c4810418100a4907680100c96810440188803a40c4c460386640111b4140c03001d03184142a40c1040d40704000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 114791951 1250 114790701 114790717
    0xa0320010c050c01050106080121030c06020309030c0105010e0601021e0309030d0809010f090f08160206030711100204030816051204030b0103060509070608060d081909060815090601030c05 83
    0x9401c009500102580110141c1070a100000c000e102681e216042116510000d104109203010401402c0151107039550508000f58001c1c5402c2100001ca510b44e40181c1e0b2084d038504003c5d0340f0000d0b2030703854090280b20312400340c1008144000ea50a113800002e60f07890048900d500107031546000120020350800488107404000307825a860804540e002602842d000c540340e4025500308410601b00304030b00c0c0b09031070905901094400c1100d0040e200e000b4590040e100c1d0624a4a5956084015940c2d0700f024504c03980040c0d0380e02007038000c621021810f0000743c040210a60b0300520003880046c1c014000ea45a042203c0c1a01c13180750114101249000041c1a8414207520006000f0090109a5204506030307401004188055200c2c1070303810790307100c0340b40c4100e0000484c120301062051814442420440b80103021380c2d400d0a49008200000006400c0105d02045079240100325003900131400960100c0c01c100c40451000c00c0f100420035503240241100e040641d201031070110b090081080d10b00c0a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 114793201 1250 114791951 114791953
    0xb011106090105100603050103021503060f0d0809030c0d0503121b0d0501050f060c12030709050613030203060f1510170a05040c14130209031f0911120a0320 69
    0x380c1020010280244020340365131140035200c150100e0981c0c02070185a04032580900100802c0401c400c0702c0f82c89403c0548141d5004e4a0b4048114956452101e000b006500400d0b015036108100c8080610340041d0881882c050600141d240011400c0030081e40c56040e50324444131420b503602c0b0000341c105944105003d00c030080108818000021a600050517140151203140441c880c1c00104000d5000c1c4050200e030070381c001c5551440c031074100320195402940904001003065203480c0000c105402c5003003207209a0130054420400d5140410895030007181c0d8440c80c644a04050b0071002c2074806201c0054060344480c6000a1420320840080c000718003d01211030460504100c524080c217810769003580c10313540700ca0700420740300f03403d90304181340100044c1400c50800c048183c41029411000200d07a25009000c00c03108801d80e241d24080c1030307244081000460010514041c1001008500392a000e00003404203415520303030018450b4482a05800c041520942000c04085007a00c043c54085813 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 114794451 1250 114793201 114793213
    0x7021f0504031b080304020102070506042d05030f03071502040f090b0f040f0e0c0901061209060906050103030909050907030206030109050612071d090c0105090607080f0f09030d0c150b0111 83
    0xa0104e8000a9405107200b6401e440c4219666400c01100c2e001d90700900310b4608070700c104160582070855608440c42c1c143c0e05500030a65841d000a810800ba00c1c030491900d420001e1682e00700510b0240c1004034012290013182428140280c641c59410107000d2281000c1d510940010b6503612a028000150310040090001052400c080c002030080030181d0441441860100f9580e0725000b03c816069a51030703070b200314450001f0118030b0007074240d56009982c1142e4030078049011130420300825018500a40311400303c80c0c5050510000c8070402406280c0c0c0e03800ad64403d200507500d4800b220b04540ca014004507031502e65000081018001d010900001d100f0080001510702141d01c0030300003080c070f0440851480d500e1441407519904100c01700703800680e042110701311a01e050b0015020903806040000d0074400644080c6040c5d51000c6681050312070049018692361800b006116050021450901c13051101075503038102400c80342d0f45504172291070341000d80850340320f1000066000402412110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 114795701 1250 114794451 114794453
    0x7020d1719020c0108240a12080901020d090f05010309060e0604061d0105090d0809070b0c100e030909010b0903011e15080604030c02061305060a0906020607021f0504031b 75
    0x44107810780c0c1c030020054094449548400d6029840703032842080c0050304406605040c0140081d080898005103a00c0800c070907000c038035a0700b074001c428110742c41032007810384d82c180c54400a1b03d0704580000e0316082018605052055461652941e070440304c0a00b404549a640b40c9400c3c0050724080d218015544590000c00c402d01010782c001080e040c001c1c106120404a01140c01826a017044607804090b40c0280d20481c605032007941e41c55848540300003a280084d8850642c04000d03840454212510b500121844143c00c6582c82000c0840c86008011854440c8500c00301c1d5000c81c05100e03594001ca00403907038021039103081d0800e0280c00120240b135511003084098101c014682c04451100d41c0c1c40a480100d402d120004000b4051505a11580d10709800c507401c01082d40d102d1032019103004d14a950029071a04c0eaa00a0302103000c4944507245654180400280360210007806e030011035004640c6080d540100980c0016040b101034404922940c580c1000d030340185146003002580d010440c6100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 114796951 1250 114795701 114795727
    0x90e010b100c050303130f020607140715020c011206052709010c02070b03130c030f03020d0806130e030903030310030501060602061902070203012004181107020d17 72
    0x4400100c129034412418224100031034001d00150303030051856104001041555062040b20000725108075800c42c1400a16408150076400503d021502c51840303194001d8511400d100286c0030b40b42031800d0003a89038040f58001d580300c0c1c03981040c9040c051403944e208100880390300800040c11014004606528111810706044039070b0f10381009034640d00c0000b2039048d60040c0640030071964154014082c2a04204000e121584003908549070b583c03484104500150594414000a42c007a140f082d8803040740f810040e0802806510880030088a241045441d5460341b02e4550290b080080001e2064180841180b0794802e01c40c1c2d140e858400402001501280c136400601134030300c03c000a10600d80c1c1d459050341c4c0c500e0181e0b1042034400398418140c1c1010304a03401b40102034001400440c01c2e50040407010082c6410700c168940801d400074051245030074450800416050f256010080d40700b10800c04807103401280e01c000e2088200c07a01200c103101e110303e81c00900072114484503070354540c041e81d0342d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 114798201 1250 114796951 114796961
    0xf060903090102160f06050319050411010e1008070c141b0112060b030f0903160303020a03150317031b0d0207030306060302090a0b0904020714060103020109080a030215070306090e01 80
    0x950052041c540030802604151130342d1002ca882071824103440504040c4151003540005000242ea142e11682e2211101b1481c000d0b0f6004034040c0d605500c40725525000140a91aa40005030203484050a4042ea892b4010340c001e0b400b030340500d020008110369281c1407200504040c03449409120355011035407109009408001c0b0340400b41c8900b056040520503c60076200144904400d1010a20010b601420f00481059115211200342c81c5000d00b07070320016200c24030060041d0700180c0d001c50340c80d861980500c640300601c2c0f00001c0e039080f80d80c40c50b51280312100d041000515402000b2001c10b14901200c0c2c03040045001c403160700c60711140c0051000000390414401178000904080000543c14000d208885500300081c0400c1046030900d14410b43e50341c00400c40d1a00a91708110610121b034180e0090411104c01c54080c0015502d10f000040c021f0010750400782168010042100020b500040c900054103c000408100f65641d40025401007010f40d2240100d0740c20a4074200c0704072010352203 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 114799451 1250 114798201 114798217
    0x40f060609080f0c061c020a0c06060f03051b120d0e030105011d04060b01021612020a050612040326040501090c1e0909020301061a030115020a0818030f060903 70
    0x303140d05807a40e56050a6643d044280004142c2c0c101540041450904500428402d0b80d14424000410220510310040b80e010309141d600113001c4141d09020003a881c02007200030051420b1507030000b411911003e0b01e407012012a80c0e403d42d03189400c00c0d600e4440201005a18174080159917400e0300f00203000e842040e940350054440d5103448000f1420740904140302e0500604400c01c180c15a44a580e140020b00308200b003103042d40315209a42004d40403e02c64207002e03000d0540c18600c440300c14070600c0b504100d29000584038407010701841406003880301c0259407041c0c061406050242c845040042c03464405594030840b140d50a0412041c407005400c0a483c5a00c281c241c1801c0c141e448494440021040302800610207403900c1c00c01c00000190480509140002c000042e00c070380c0c5400031f12811858000c101501203010004002d01403101054444400b4a030000d000ea120882d075448040b4419007510040b03a09030b8a080c4c8429883c108085944000203030129581d40c101040480e6994000300b41c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 114800701 1250 114799451 114799457
    0x3110607020a1101050c0f16080c1002030702010c0812010303030c020d021203190f020307030c0f03020a1b03170702010b0f0105070209070f02030d0c0c020901050d0b06040c0c02040f0606 82
    0x440c200500c002501c0c40425007150b03d000760184401d0045034254401200341000d4130840c0c01c0903441140a01090150748c04404440d007010745403605450400c050f4001292003600d101c11044041900802101c03a410b03824640740c0c0c45404240783c03080d441d003c0c69041c9030314504030100120426416500500703683c6442e03002c80d2800d000648040fa03450341c05172403609010b81d041c404039440c600c3d82c00c0c0c001c005804421001c2010031188030502e040742c000b100c1440009445543e60420030f81c000380c805c980121280707020361030010742c902c024102c4005062200c0281d170340710b041c060502d0701c52824052140070289030100c050401582c000d0281101850791031082491070a160f80a600480c111180503902614949069603002d07001d07611001ea4644442c1940020004841100004d2184c517001d2900368403402c210980e9801405079181d01608028020b0f1302240355000807490701c0043e5540300701c0c21103011508229440c412034140211410003500181031800d010140442ea800503010b56030701e82e07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 114801951 1250 114800701 114800713
    0x70507030b041103210c0106090e07150810050d03030e1005041506030b04061503080a02071d04050c22060b09040b030d05120c12010602010203090717071e030501090311 74
    0x50030141c984c0c082e00c05041c0c01031701a03101d03810078404000c0500320340103580d8000038456584922a07001e982440ca14402c8139004080c0510801c21220456900c042d5a8981040341c0d28280100340c003005d1050242d18841d00c0d1a1326400101482500081000c0304400107480703c0e000f01c031250308098074084d01c04449405261b16134254105030f40c822081140d8102554280340d45030368480030003e19014449400c801c804a40100c04107003804010280c1c003506a000704040c1d841d140c170040380410002c540c6100281070720113220100344001a0040404801c03100b002e00d00100504e05501650300c6440e40e200b080c20410009003040b5168080c1c50070038000d40b0140444508001019203d45400e010580401d200b40005120407204d034104a5200001001c800d240c0401c0b051440304441c426802400145c1d000400c0191902c0107114850007815080b4804c0003417245150390307580352a0107000744900201a83e5486000c0000701007514002d43c1c1190082010211074200142070f000c16106000c85403080c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 114803201 1250 114801951 114801983
    0x6090614071e051506030a1b0e01030506100f1206240b0a020601050f1f05040306090b0610020a080315010203040b0708071b05090c030606070213051005040908030105060708070507030b04 82
    0x141310301842084028090103a0341801d990341610440901f9107600391508140000c692a1a15030700d85001e580900c0041a00d4540800e007030a0b400f003682c100050b0b444102c00f040000982c24a820780c071180d400513000c901020034440f4a420101c0c1201108101090000d00180380c0c160341d401003100c50900c1c0e003525001e03030b00e90041c864036088103c62213402900100c0b40400100660795030000031549031405516007540c98858005070740c59403400ba02c0d0780c022075003407080ca0303e00a1041500e0750000e0000c0c2000d003169032900e001a000041582c104008203103d84640c2c0c0e0310901c216000740041800064456580b81000c2d13050b0740122004a5040044003030a012501c104000c0408030b5030024124811659207044000b044e41018008941101052240d50016034509480141c80c41c400d0030001041d213000d001c00c1310200752940c0882d00507480c001d43e03c07000c264128116415030700103550f059074400540c41c100285103e04280035009000e40d036000300400184e0029a40900e0003502850340a00301 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 114804451 1250 114803201 114803233
    0xb1008011802040b0a051b072c0708040206030703060f030501020d0c180909060b0424150206011e0305030705030c011a0d0f060f020f030a0c0906090614071e05 70
    0x6501450103040350a11111020600c20401401c0c51f0503d00c3c5994594121041c0c104d19101e0341c2d030000a07109c0a40c0251032090322190800c49040c1800c1a1802c4a904010340d01901352503020f030010f03004074800000920380c41d0082d00100014200500828031055984c20a14000e4005803501e414290814280c0e19850b482001c2803c140c005910308400d04916040c01c80004000380c00c003c651464540f110081c1e159030368461401c41200082c154901400c0c0000500040046500301400c041c5d8000c00d1041440d80c0092017030706440d04511290000400c0000308260308600740d10090881c031000801c402000004409864070500100c02841403501c41007100c6110315000c03e2103a00138041118090105081180c3e5022550007410300148046241c14500241e9010710850a42000008184418950300e0701c1101103140030362601c1180386045c240001c01ca00716500c00c1208018641c03010001c2801c08a044884080d131100a0924802840003018210405400162824043d655100c0c1000741 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 114805701 1250 114804451 114804457
    0xc020a05220c020c09190e0102040f030f1a04080a08060306060d030e040902060406020a0302070e0c0f0a02010b04090f020102150f060105070f0203060f040213021309020d0b1008011802 81
    0x141424000d0901078150303400c008110140c8010704520841c1e02c0342186131500344000c3d000d85a81b42030300040085884c0d442d07080c5c44001c1a01406a881003000304105607814106605403070f440000c2400400490820b20a034450f880c2402295541d07500034001006494001842c0c111803544603010035039902410941c690070220f0f032450300850190401d00000348600213616520400810004000c1d45513004030310503401a80003c2c015a1210805c4401e142c2c0400c0008010310b4014509243e900d0051654542405500300b1003026141c00300d044100d0900039000101420b401030b004001c0350b1380350305040d10401078125050380540140b5200030b0703034421200041846040000c0960a05854203001110709505ca00001c0e1444070104a00d04016a0103004540c003e600c1000c0f00c0b0900d040500400c803c100080034002d00321441040050340e209065003140085486550300142c0702c03442c4003683c10242c00c01c420710b00c0d8004503000c001c0c503040340c010308000d050f101e2014075080b8400303c040101040388 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 114806951 1250 114805701 114805729
    0xc03010305191509061506020607021515010c030507060e03032508060f060409060e0a05010807030b1b0405030105040f0605060307051c0212030412030e0108160305250c020a05 77
    0x30b50008440300200c0312a030070007101d0354450b08000448000e8443c00040e01e1901f0380000c40140c01c5002032041141d8100078000d000c0e18003943c0d950607810800065042404004403c606000504c12254180760150007550321300c40e040903050000f03040144015441c3c1d0b10407a04c01c108000f0303104441c510401111480c94a021035a2900c00300c980b03541e410000d0007009001555403000c402c010100d0117848501512005240c40440a6084e0801a0780726055a2058005001a0b40100010000700b440c006405410098041c4000b03214150311541c20300c980b049421107034040d17080909000411502d00070860206010721000c0000ea10303200100360700c903006441543d40c81720301009445200c0b00505403404005200400e55424031000b080c410307003140c001d54811004551000071000905400c40340303890102009103003050441c64084107840185004e2103d590030903954a00055091501004402d01ca801c00c000d00034141030751aa000f881101000822400380c0c900e6000041c45003060913007205a2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 114808201 1250 114806951 114806963
    0xd1404020d061e020706060503010c05090a0306020901031d0309190f050103050603010e071d1e13060b03120915071212060f1d0f010e0a1d060c0301030519 68
    0x411160340b580009070407104030750021180302c41000f4072480320610040440501c1410b000c9100b5181c54201401c540c3d0201051003405010000c004803036441661070707019640d00110050311682c0c5400102c00030040c80b4441c0544030305c920b0311701d010745600102500103110304489290880c0821550030081c00424405c0e5800080010001c7c0050b40c0070b17401583d4403203009400055004440714006140030416409124201c0440d445035010700c00b02c025680d4041c000c6c0740b03c100003200d446140140d04600030720703c5045042028051040001d282c000e0441002c00404a8200305200303e003100e215801031401901c03600e10b209001c2d0083d1300c80e00998621f650403c0e02e084000f0000101030310410b400c1c581140586541d1000460150049120b880140c00c1c02d0f9207145e002002008505842d44010300402001e10140b001000300348010007880e0ba0044d0403444c08154113003901d400780c901d00b25588030212580208020000340413040f5000c1d50480307000b0b00440d0220642410001181c0c50b01400103000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 114809451 1250 114808201 114808219
    0x501020304060c0812010e180102071110050d0501090c090801110712052503110a0b06060a0201020f03090a0c0b070305070b15130b100906080a0c020f0607050d140402 73
    0x1d528011005280340f40d0140c80e43d603250040d0035030703e010000002d8204051490380320092140c00011140d14480d0399941c00b000714500700e003a8803030380c01402c044001140b141d9840c01a40c8011840750056030b0052400e2401840596181c90300704020300740b21a4100000703001d58400082680c814010129200411860300b860301e0310945603403031900f100500326030a000c03080001c1d1175400c0d0781c2c440c1907224021076169030f58003181500c4d000300714000f0415405021b6001c484990013185014490700d42041023151030a590b1040818240c0c06402943d0054500402c040104540b5a10100c1d00e0604a40300302080382c1550340791405100103005444000c0c000420a00c941000074810344000c9410081d0380c24240d10390307076401c0c00050382e0007940d1400f4050309803212400c401905203121401400700f0b050a0196a42d41081320080c44c005c0010485482d003a2980c0b120600b441c002d104014a209203142036804915180001800a074862141e100c041131600d07400301d03201c0ba051441c041c020341d4018070040c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 114810701 1250 114809451 114809459
    0x101e050f12100807060f090909151a03010e07050a08120a03020306010c1718030105010b0a030f0603060e030325052a0303070909110c031204050a05060a061e0501020304 74
    0x140c0407401040903030315455101c40400e54500403c80480104155602e0b40b58008140c0c2000b0413140580d8082c0040508202201000400514141144603410340b400074a50380c24a001d5580314200b10510745e059480d02640074802d0310042005420345005581c440802551340e44950b42d1000c000600e0064903609005c000301c07540c8a030700156008041451b140902001d2510340380f184100c00d48a03038218a06c0010012620141482158a484401c82c000c0103103616012201d500b80c4140035028041542d11124107280c0c1895600c00005190170002c20000b0102a15106580e0344c030907030b803a00c00f450760300415000701d114004110310000083d540791420f00c007601070107403080802d502449003501c001c03c40d000e0aa0b0340800145105000d10b58400131054505441d0100300e5150341c20070300381005e0030400ca040ca80000400c51703084c1982411f0f120344035070316410000d051040ca41c100410500482d0103005240601d500f010301503514501c03c842d10500b40b130511404d8842e06214260241c1c02c00d000800c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 114811951 1250 114810701 114810727
    0xe070603060506120103140f0d090612060513020f040b03040f20030c10031d1b0409020901050d0f1e0c0909020916090b0408030408010e060103111e101e050f 69
    0x1c40011f00d00e0403515421210200b090170580c0040000001030601041004660b43c40f42c000300b03008007040f43c10002c0c1d60800010800311800300c1d054024042d0005010341404000c201258001e0000f948219124141482c04046000d40c1e1541074610000303000c0e50b0b0580b41c1d1400c0b41d049820000078028000c2c20740f003e040c8602c40c4a080750780710601d50b5a4400887c0082400c569158030000400546100824151440d00703418104c80000d01451030720124000580710350411340e0640b03608440040c00a5110f181c1105c151602e510020480111896400001c01008209a03051441040000c545507200c0744030701d0445030041c0d8040d42c0040800b0209000c070500c26050b2044071210715102c44640d40b980c0402e8450380c002c0d402540564030008013041262028840c1650120601d80500403551440c0c03591a2213401003103005109034112202710103084980400323400d015802603c0305015000c01d84002d00142405a80c29001e800007034103782040f4454001c44160623141282d00d070070580c06032040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 114813201 1250 114811951 114811973
    0x50a0e0601030903140a020a0c060f120b0a050a08010501091b0f0c0201020102130b030402130612031409040f05041101113003040f050c0d0218040f02040e070603060506120103 77
    0x43d000e009050540e054004610b00c002c25000d81c551f00180b00311042d500c0c09101070801a440041000103c0000c140d0065000c0c09103140d50300c0c01039000c41c90910307450000b4002e4107554000c9038000311004001400c924190451412541c0f01c403020401030707000c41c082180300d0a5000c2101c0000d0394490540a010f4000c81ca00c81380d00d401840018100101c5400c4100b00d02500d810420f840039021082200b10301d0441c00254030445000c8007444101d180001c140031402c25004000d090003c4c9000103803c0740d0842d010784010030320003030080c00159030318030582c0020802603405582420381d2400c0360400e54040c80619a0681d41c102c000c1846044c0070514020f07800c4002d1000102c100168541510641b03440c01850007607003c0c111001c0c0c090701900c1c04500d07000c6444081c42c0114005999200503944918034030b240001021000c4d42d4a0381d07103260600d007600315030500940c001e03e0b194024104040001e010000d0b03d1047d103041192503110400c00400b40030321400020a1200200148001341501a403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 114814451 1250 114813201 114813203
    0x2040506040509071142010b0a050d0c0c02040c02011505010302070602040e1e070c05030d09060b1909060501022b05071e0b0601051c0e1e031201050a0e06010309 71
    0x401121095416a03403070a0151900365040143c01e1b22803542ca0740e026116009a60740150b00400d81700016802d003184942d841403040f1003013442e02040e42c18105002e80b048034144008003200700a040c030580c401905003004060180c0c05149445265086640144244085811142000703880c5520344001100a948200000c48900e41c00748400205101150000b50246070050282c0380000c4021a0b462030014000701414204801d048180c40800c101000311030f03413119005408101c000c2c507070a0010240601070074041d04130200300c2016032141040d10000080d5050780c00709009449c0e80e0f500480c0d440350703c2c1d80c240322800390748054000c440d2001c1c0081c40c2d07030f02c8031400c0c200d0030107643d45c4445181c400210051880c0c0c4805065402c00c018de14240316038030800c2401e10a0404801c0a0314201e040d401c0349041d207403035a0f640d000c00481107040100c4105000d41c0b4650003c14141d49084a4a130780103080541610740500001190724500040e04000f90703070031400152410ba40b0134004401803d0040300c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 114815701 1250 114814451 114814457
    0xc0807242a021009050c15030408040b09060403021e090a0608120702190905060405010902040e04060507112406040b030307060209011404170c060a09030605041e050d020708010204050604050907 85
    0x7000d0960503c80c2e001da4041d50f40100c01400540301d603d0148000c41c54502412400f9000801c10000001c00c5c480a450980d090b401034a42c4403112600400e2031840313141c00103580203403481a6203180c0460b0341d8a2024004c000d5403005c00c03a4540410340d5083d520240541505500100700312000c1001e036034081c00c030140c0000d01d2a0422861410106000c16082d049210001e440d6010000542401d0242c80e00604d001642185841d1070050200c14000001c0e01c010a4940c5407008034003950300c01d203500c03041881003200351580d000b54201c4d9007001c4120080c00410400540001405030f29051240d03451082002d070140d403810781c007642c1c3c0034004d512030390500c1d0600070501d204c25060300300b09000c4c2c03018001e040300329010444407140713444c030f0718080800b820701c01c1c00304000312850319900240c80c01c101c90780114082040d40380c5180c07419906605049004030146011150400d001000500c41929000f42d001d0720005e41d1200c410070700703074499800b0b440e412a0003003004112500704140c459611401c146 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 114816951 1250 114815701 114815713
    0x308040503040b030c190503040b06010503190e0a0507050f0a0b03070302120406061d040206090613080a12170103080a0f11010c030507030b0a0503100b010c0807242a02 74
    0x1c5140f000740c0045d100c0c4003400c000810301d003006a084000c2d00d0060304050a20b9811441d055035500409000108040c1c100030000c0046001940c100301c2da07030302d2815101d1082c4604003100300714039660350418805441521500b1000038190800c10b00300101190f020340080c1000d0b04155484031958005020310003010b85c200700f5881d20700c400b094000d008034450840802c0b003615101003c401140010f5454003410761a134284070069a485088a101038400d6642e1600c440184507406145180c1384e014401324003031a10900104900302d00b00080c0c40c081c644078030500e4041c402d00006501000d000092151004208001e0603600561004103410060320300000c00c40328105503542510800610f40f40803d8554080c0720141e5007500940d10684011348e90581d0480c68040060b80e6074810344001304071031350788441c2340503a640b04020404080703401200b00b550328030840c50700480230500d8842482c20000600c030310840b503540c3c6004503c41d590031010b41d440e0355401b0b100d041c50f21000305604030301544942 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 114818201 1250 114816951 114816959
    0x705100207020a09050408091302090d142103090d080403210908070c030302120702180403180b0901080609070206070305151207050a0501090503030f0a120203010803030a0b0f030a030804050304 85
    0x1c1c09054070a6224241c5035856662080c03d100120102003118027402d4014000a00316440e40c5510f5810030750821148600d610001681c5401c001c000450307208108004402448081080c4008500420440088412450810b60203d80150094400500040300c074981038501070010100c103111030155400014064142d6031b83c1c1e00c0681d01c040000c035031915248400300b05240d01440150030605c0b81e070890300d160075815030009510418840b4005c035042d80e2140810f051500c00c0607140c00c03004034840a4810345403642c0d01ca020f03a0b0083d000c018005070340307400041c2103401d003081d610340101829001041180c5070108140c0c06441c0040c00c3d044c041456849081075075030341c01158003001d80400040d041c60350425060140300e10303041c1c0100781409041d01d010002d40c0c8000040340c0000d0386400300700d80c80344070484044604001c08020481c511b40040b0020404510200c021070041507070030740070042e03081d00c20144540144403001142d4140c01603407001300030034000d10100740d009118900b503a00e4036881d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 114819451 1250 114818201 114818219
    0x30a111801020609060610080408160305120108010c08040f1a0c1810080c0c07050619022e0f021b01060e01061814030c0301060e15060705100207020a 66
    0x204404800a00d14000c105440c50350701400241d4015908001500749403030181d01052007141e00360262010021031400003424010b900050f1014a00316180341507c1c3e24540c20020803a0704101005540c41a610303000041a0805101d03580f603081240d01d0b00020381d0780e107407180850303000320090a56040d00e1300e20000e4502280300c50018840c216407500c007621617001c40f9584003001140003503640100000c020003440c640d003000600d40e0180e6103500c0700360340d090010707500c0e4144482a400645c11280c0880c00700b00044c2030803403100f8103041d103a08445080405200381740140d01030992428200040c800192030740506900031040440030305002502c1c1080c204625007422003540000030007039544c0d01c014004100d040c241180142217624058102282e1a00b151a0030071046c800d881c901c0d0700161411400707441c01e000104200200400810001d56500c013400c213202d10441c1c02c003500c0c2d050302c04206807c5c43d000782034601c00d60300030f002082e080a20700070003402907000c514181da01c040f00010004403406 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 114820701 1250 114819451 114819457
    0x6010b0f0c060c040f0605090303220b030a05010315091106030601020115091406120607031505030a0303050601030b010525060603050a0c090f0c020a030c14250611070902030a11 78
    0x18a003251540d2581780c90811410f40020f90000c10030002d00700030b0300c5403d640002c150740c1000705a00780301600055401da024982c0285900c103c81e802008420424030f16020390006040320300803012500d4013140007000c10209c3e01c60f658020414001c1115265007810013502569204006000003c0c819850141203000304600c1d03400014295203034410606607111641c08903800807400d40e42d0b01c940c030822014080d107c0d003000b021101050341c0d983c000c0b0058140c0030103540c010031011b0107446e080203440c01c0090103030104854080c00720782048200001544580202d5a544260084548a880700194580400c03400300000352451610344802101144007030240720860b5206d80307284021345152100090030755003445000c03454140380c1620040e006401140a1a00b17a82c14075020a00080c2d900d8420203d0804c0c2d40074108510415400c908540828241e00c0441d81e0401d0190054540d03c000851340280c244001c80945d4200030350810040c82c44c1d8006e16000341001401003981c5241c14a81c0c04560 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 114821951 1250 114820701 114820711
    0x102040f1413050106050d0905010b1201150605040f031104090503040602150c090906060307170106260c1210320306060306060d0204021312030807050c06010b0f0c06 73
    0x9107010103500c1d24100c6200b801c10350058505101c25072401d10040c1c41c0d801442d042e8020700f500d507070076041000b90a601c81c401e9210001d14401035050007d0200d80240324049400c902200009001301d44540a003080e00c040742d045024901c01c5a09551f150170a40002d0b001542c1c00030f44407402d120000381c040c006400546040d5000b0700e880604004182003e010142c03401142c00010014070600e9290500d1840c0e0001043d82c84903681e4640b008203c544000589171000d5240c1001d0010503070036482103040100da511800e41580c1b45000400200020f941600c0545103070350304102340c00310103d08400c0690b004c082c05058800b42c40d51080001c01d0780030030322444a02c001c013002c0300c45881d5001c560000104003040e002061513190440205e5074070003020707000500c02c0d80748260070421980c86404032504007540c0b0481c1d6180d40d50b203d102c0e01403168814401c80124840100148181c0d01c198182d4003030000c07200040100d40d00e07100b103270000c0da4080111600c0040c0200b01c20f0914401c00c2005074012 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 114823201 1250 114821951 114821969
    0x303040603020a080112020a27060803031005060310030303110409020406020d0f0315061b02190503060f130201080a090b18070b07020f0603060616082101061b050102040f 75
    0x1c2c3c80381c51005158050503000346a1818484500314007680314640d64400b40c404018082005e500408890210803041510040441e0b040400114000c0c0c030100245000d0203007c403420001075281c20400c8424002140d00100c0c20400c0d200400100703100c0c4d009100040ea0007000207180076129501101a079200350450300c0503034014524a0040b5074420031144404040d40b42c10041080308134a42902003c50f840b400041054044808080701d2001c0c1315955460740c0180241024411901c5c901080280380c0f040034400e0217035900082e40c4101c5c0450a5202d036001ca05015a281c0b00c1d580190b0b05000054840150300f84d0314400d180000f40c4140e061070040c40c04200f0312281c40041b080062a007510f079003210300710030814011900161169003400d480c0380021120300751a9540c40000c15001d00405a1428850b100c030010301c000c3c001c400c00206840382000305c600901001d1074080c508504001e2054000060f0020707801c000301c0c1030b9a810103030124810400945403540d80c0d00b03851290681a0001212 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 114824451 1250 114823201 114823207
    0x120506010312050906031603060b0c160e0402061b1005090a02121204060302030604140c04030c090b1c0201180810140f0c0c0f01020a030f1802030d050a020c030304060302 75
    0x500ca0604011120b100c000c1c0b800500d03110003080402e80601026120040c892401c50758099414040d8100d4070152074895001512a01c3c07681c0100c0d51501403101c0c1d028203034116070740842d94072001e40619200700c1d0013601d254986005650046503043c0280341d00b103200d010311480c2c020918010b01816004191080041049030024010801040c501c084c8524459000b01c0c0703c0010b0001040c1941e04840d182d090050b12503444101090141c8078111138640030161400411010f1404030028005690140e08800c030000d454400e2402164484400c00c1e500c04604103e0b588082c3d00e84040b181e000e403041c5000c08135117140c11401281510a600118110340003041d07840e1007000f56100e00800000c00c1c3e9040000c1d41001c1c0500e400c80100540203c802c620001008483d14004000350119400038800866558002c603c00a00400c0006a03021070541025980401501c0508030003d0b0182c0050291040d4105160180c9a41d130001800e8015401403009940040c1d0301400038000071301203504e016903 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 114825701 1250 114824451 114824453
    0x609020f01030b0a06030b060c030a082205030316050702090405030d0e0c0f010e03070b0c0105060f0111062406040e0402011b17030c19090f050604120209060a1205060103 75
    0x10380100c408441410540340030740000840e80c0ea0050002265414140000d030140305401040c4188101120f503a01071100003072201c0d0480e40074014511a00c0e6203000309003144040100c0320749064842001402c2c951090000c201060909511201c103018a401d28501c0e1603c2039000c1003401c18200c03000c0e00d0343c0c1c001207103499100d000360085d04454000d4070043c14100c0c140f00000790b40d480c0d4912200b4100b081d010715941c01c1d034508102c8003000d0701000318030350b4a40d1000701380329001e0042101c249006110030003000e07105501450940c06010707200030241c4082d9403014000e071801c0c150002442803040400000100329200d07800100040d0a101204840c1458030f400054800400a52810300c111503400503903011031680a6425a0054045480da689495005140d10b49009500768000740d58030b00c02501c80b08940100d0444111026140740c035000c140c0e202c0030003d03a40140d01c507200a45240600d60340051070880800d9500c00d1009016100035929108005400c0103401000c541c16484540148 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 114826951 1250 114825701 114825709
    0x302121b0a0b04110d021c0515040b09070e0405060a0b130f0902040e03070206030a02030910140702070611070b1b0601031a0a06030201051204050a02120307031b080a0810030c03060902 81
    0x1540602c0c15262110074840d281d0201d40d07482030110b403640c101fa104031140410801c0500882581500c818455001410103040a0040d80c2c5c2c02c0e5003c901910078001e00140c100220700005114540000240200341e03500c0d00c400700600301a860503607000351070f040d0707158450069100e9401e13102520708001485841c1231060000319903100800203207950040c0300382d6005036515811250f02131100c000260b02c135111460001d25001820380e9207844241000349803a000d01c0c4207102c5d00c3c421140da42c2182c000e10741c1c400d01a00c18041d060395100711034001c03010a020001055004119000c14008052950030040c4503c40c2004c8003a0011100220000160f414642c0c150450300c1c1c0040c214481080510f21390b50028010344a119020f001c800106400070701440b034240020400d203500506890405d01c4100601c41d12944000000c070701140c13200129038401103614068042c03c3c0c2d846030b403241c40c2050b5440306480140e4003d2440b06000c0b20b06602100003600303400c04100840c441c0001203441e26081c8100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 114828201 1250 114826951 114826973
    0x801060b04030f03050703090302040f1a0405060102060c09180a0204060f031104060c050a05010e060601030c08042a12050106050f0102011e02030a0209031609050c070302121b0a0b04 80
    0x140e0100c0c03605000601c003150556601c1c00c40141d00d403c106681d04190f01d41a100d50300e1a5002940c8146401020150307601550050140440d040448110324400101000200c403019920703240140e000308002904061503800512101000802c1039142d07a043d041c031415051011144a20300c560007203810002903410002241c080da1581c02d061141c002c01803d01a1540103500c100382c10080401101001d015080c4040090741e60010000c1c8640c1900d024400c1d40d86500341c45103070000e443c240c4002d400922580d105070081da440034003184901a0541c48034170400a89d5180c80300c10040284c0024103580c00940d0002003072059002180003031501d010007000341c01c071a041c54156410000c000c0c0d20f006550a0681d01c0440b403020040e00da854807182c0900900030000c140da018440c0305800f4503440082c030701b0b100c1294400d0005100560311406484d1541c080d2200050140e4440d0790008400d101a030f01406610401340428481400b040d07000321b06c0d01c00c0b0503600740c0e0303050540700502081c482d5072454 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 114829451 1250 114828201 114828209
    0xf05070f050102070b031f170d080105120309090c04080706090801050a11070609060219030b030712120f020c0a0b070606080c01020c0405060a05090f070e01031b03091a0709080106 79
    0x103090418507049240c4240d20000b0407040075004209500580c10800c004a140940a41c01c4078603101045d40d04866030721038030200e02c9d00119051600007c0c0764034201810800484000b4055801c018240050141989000d03050402540342400b003c19204410003030303c802001e4503581c00c3c44042c0381907031305400c59002410001d50241803160b03202c50703070440c4801c580034541e01410002c1c03544080e0400300000d000b010400f4461880040300b90503000d600d9001404413040807000d03512070950720300d01d00d20301400d850001801d483c070f400c1408406d07a0092400303810501c410700543d240000e50400059169265400c070f40d455180c042003520030302039170780700e4600542240342c000c0c5504048000040d544000b2100039a104540356000515151a1003110700020000a000310b0710030b0605003e1041448130441e540c00001d840842040c07180c0d072103809000e40a649a100086100043d0300045002d003842010598100b0f0900006c1043d0307002d036a10311485543c0720354a8801007400e201e00c07103007560303a940c0c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 114830701 1250 114829451 114829453
    0x50d0e0402070b06130f1e1103040f080d060515030403020105070c030e15130603020a08160801030f061806020c0f030c06070810120501060303030f150501080a090f05070f050102 78
    0x40b00250810f40420b421060841d054401c42c0c440d21030b6000a02a54003c596546003420135400742e2290035201a003000c1c00d4280c0500c880441c01001011601080fa00500280c0b00c40b0ba800f004108480002c0c043d110804101140c45a10b55010499000d100602e03840600c00002c10441419420310038160080040d281019065649440c000c1000090520b00c900c15070540c01e0555560b42c00000711010729041480303803d20a60785080c060000d4102c002602c000c01c1d00c0c0000900605400640c1101e10440c5840f09501c0e6400c0d40c4610188187c20711044138035655905030000805e0348030446203c0f040c440d80300581d481080c1c041490814030f00c4c080b00000c2e9030003404800301046000c00c146a01442d1403408110a40e0396400042000c606580040d214456035207808003401410340010302901e002e902c01f80f1400d030300c203032500040300c4419a5400c03d00840394800e205640c442c003c2e040d04403a601d0004603c4020589421031121a400d40440340d50740090010010081114158001018240 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 114831951 1250 114830701 114830707
    0x18281d06030706110109020d050a0201031409120906040e040c090e011e0917040f0e160e040c030b0402130e092d070b0c031c0c020304090207110d050d0e0402 69
    0x402d80d6220640100000d002e800c1005042d0044254813212079a074000740001c8141c0c07010300302242c9074002c000090f400079040c08032194821181002840c0121203d038001c09110100c45115001a040341e40010b5004004202c001201124240002e002d01e00401c000094940761183c1c002c01c941b410002003103140d0410b0940d600042c4018401c0130b200c03111140100308803010b45000e00c0c0a1102404403800243c02003400b00380001c0c8101403400740e6040744242e4200c0d441e100c0d9904081d1406d41e40c0c600c00212180c00b489060b00f40b503004a9102110350801051b4081002c00044c02d82e040059210711070a15a6810032000020a4200f030308120101d014007840306c2c1c980d101ca064503198a000251050106650078a10b01c0100131000003010a5003007a61034105401030140c0302ea003c0940000c03c0712019664049110341403140000c00c086640085242c140b401c00d034400030707420a000542d40c4100210301c0310b0940d01c4140e41c8076040d51250000d0440c0403450365020304118074000c4858040ca1041c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 114833201 1250 114831951 114831961
    0x31e0501080a0f0804030204050f040c0602070302060a03020a031e0b1801060c0f0c080303040b0402090f0105060409150b1912020906030403080a09060c0320070818281d 74
    0x8201c4030a6683c028000d1091a6a0380c2006046032060742d00081d001351402e81008094190041003a01031407103040d4040c49242d8600040760b071201e0074040a94841d90410100b92914083c0e0b0080641071103504020590b51503110300d04d40d0105035060201c000e12744494480c0d456150402a0103180307510011000b110b5410418010324070b401003100103003c91a04100f10083c4030301d858000009110001c2100d81d2860b1502c0c24542c4568150f070201e000c0c240c64800301e200004120319860580780050482801c003441c094902001e1705400440c0716020311007010106084440000600c9541d5402d164002071a80032100100000b5803640111035461050148008581d924401c803074101d9014904407800340c07a14a0124010452042e009000714034241001507030f190140c00c507001548030500a2a42c0c045100e07012000d601c0354101c024003418040160607c410060b00f02035148003406084001200039100e108000103c10315140c002080744031508001c003d045003031204e030001c2152503103e10381c108 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 114834451 1250 114833201 114833203
    0x60c0e030f010e03030a0207020a0305030d0f06090902100305070e0d081e07150f0b060c06070906020a110409110a0828020603040308042103060e060102030403050601060f05040f06031e050108 84
    0x41c6c0206011034001030314100b0b640d280300c040800f440c0c000c4142c0307a0b03440852402c9002040d5400703801c100903040503c0010003c1c85480b541c0c0e800b41d00035140719404c0071195000c03802000014034132002c0c40f00c040301904207a160403a41d100c1142c842c907119507654010b00103803950018040444c0d01231403002c01c6460001614182104501c00c1806408100b4103076824916000d807692800090f000030011442500e202400207100f4055040b540300c01e40c4a80d107c1304102d881d2a6010805803c0c40f20b10700140020341460390003c411240108102410403540d440020490744a940c0004c6503035200414028103848000825841e4040d15500d81c0c451070029808103490340070085c4003a06200d4000c00142c18840b0100000281c9c0e004842224604c800d128409001807016015a80302a00243d0004101794000401c603400e598002c0d00600c40e41c0e2a1640441710200404040e204125042c0070000301da901a0814030041c08580d1408109080d005902c11681900300b0042d10350141070400410009030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 114835701 1250 114834451 114834457
    0x5100903121e050711040b061605240a0c020616180308040b04030b13052d0d080708060915010e040209030307050a03090803280c060c0e030f010e03 65
    0xd442501c10510658010081e2084000402c1c1006040140b0200602d01980f041c02042024443c219241d00b094144081c80101c42e40400c1003a0003610410400001c000a101c00c403400921503030494120070110480195500e01d402c1c1c9900b80405d100003848010300c0a40108200700300d40348000c2040b898030046005107081d0b42c04c860300600001841c12180b132202480010003039078000d0b070203561b40c56640441003c4c0d5403107071200f43d5034070710200045107a0301c10f1101120a1b00303070030800410020410741c0c2d1220000a4141d40d1503441c000494480002640c188002c0c02d030160140c503001046d20b02074001078121800100703440d00c40d00803101040b00c01c056030310800c5882d200038a024074181e800745c4003060082c0304130005a54188008190001085000074a808a19100c2c1e41d8240e005660b8070b45076a500c1c02100018a58041d0000e44200c1400403124040503014007494520f403403a0f410b0300c540c0212000742c000390700012034080b010006414200060110408582c0c000c0014800500c10b07180c80b80 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 114836951 1250 114835701 114835703
    0x503030c090d0c03030807120504050703031103040e01081614030d0f05040803030405010c020c100206010501080604020405090907140d0c05120a05150a0c030501060c0b0604060b0f031005100903 85
    0x8400300741505981c540840c181ca00302d40c001d03080e4610980b41d08000e042400101c3d841800500c07603491140001c0c0050042901075544032004061380b50869506680bd5408596212800d1105000010b084141102d07294000c040c80405050748829454000600d00c0050b000340c4540c15200c0d6803907905440014041c2c0c1e20800303528250b041450540e1044405100ea030340708a40912002c020b0006101c010f52110503c452243c0031101c644290070300b0b00c88030a9004034000f002d0b130004001009254000c08166501820043c80113180a840e1400a40749080c15202c02d00c080d0b20501c0180086455a4205000c01c0c0c0111030244405132603950b0b0740410101c1d8081c50380144034503162600c04180405c18140342d40c0e48002904d02c1c08064101000100c0300465100c60070f20704141c1c0803500a0b029105a034140d459613a0780720f2001c081c90700d4461540d90044c08140c3c010350764000c0040c020307015a01510ba5401c8051182e6942c1c1007000d024a8100855000b8601c50310300054805941500700040e4001c40e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 114838201 1250 114836951 114836971
    0x10c05042102030f010e030c010b0a05090a2703030b0a09020f040902070503092115070e0f13110703031406100c03110a1a150f0609061e070519050303 66
    0x441c0c03144042030a2140e1903004058960078006a249170003000310103018030281c02c0d0003c001216802d010072410201c0c601c1016000b0040304040340b090304058114104050900484100310b04c0450280d007140e00010300c040d800250360b519071480500e0081c0021009240b0820294241341c201848040d80703101d107210303403010710307030700044003010044244103403202e8000080c503402c00340e0744e0600141003040309000c041c025400b2710a40e01050540b020803180c02002d81d80c0d103107100700c841c54060103100d9483c00442c2d5800b803042500d841d10749030240640d190f440d0341c600324a07842d0f5a6620b03015064a190340201400c0d0350f408020050651525511086c044c505880c2851310030209040603586c641403145c42034101c0c081c0030814400d2101010002e00c2d210390142ca04161a62491409505507c60742c1000303500510160503000c407407504502415101d600103240e14640b88901001c900103510301195041400c10208a0609200341841204030800f0703106a00100c20360550303500c41e12840020003038100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 114839451 1250 114838201 114838259
    0x1704020a05060c102423150d110c12040b0a050714030307021f020307020d050a260105101b08070f0501020c0f100b09040f080f030a06050102010c0504 66
    0x4007004000500384d4002d4402c0400061400141c5203860512440c05241c20031030640f0006048040ba05404850144000f4242c02c036039001c0e0300b00070b031580745600c0712032804000384003040c10f68660344501d50510f94441805962100701d038050b1230402c2500c80280c51405001e10041004040030412100c43c800d940c41c01e550f1f91441480d21a007038141800c0015540e1201000300400710303070000340120410181c0c098800c01a00851000c00903407004442600040e0800400c50380070b02d0280016003480c0b543c1c1e08007a4002911160100d0003030503426100c00909002c0001000142844500341c00c410302e00d858040384510740071800c500b00142c0088020209600065031400340012450b100c0d0b50279510100070f550f110040c450f90ba684007030403003031402203001d01625041c01e103001d4461084038001c0078000c41c15581c0e440d1150000c046000400340c64000c01001130000c2510034000035441040402e10000398141400700090031240040c7c03001e0f042c828100400d00080021500207102c2440740c0c042e1882c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 114840701 1250 114839451 114839467
    0xf030309030b0c041205070504110c0c040b012601030b0609091506030703020a1509080708100e0708010c05040f090c050405040e10050703200702060a080406060e0103080301061704020a0506 83
    0x464031480e4040700c0d05c108040000e0080000114100c0112002104c0c1485607500e11844510706200d400500c20056000169840b40e1741800c1e0480d02c1192414104a100c0d80b00700e03d19200c110034208001d08600303584d00c005104004900d03a10301c2d0001825100b615007403074003141e065a0f50140e01ca0002d51203103841c0000e03080fa134007009508003035980540515072540d40c0b48041c03070703840b1050000c507800b2500d4554041051782d030020380344c0204d0368010f00400212142103e15070042c5031401e049141d80c0075911340461401424040c00c0c680000c80e546050340c9234502080d580b00c0359590740125010034142248080ca02c1d03030040903201038903401c880002da003150710f4000900c3d109021300700302c00080c00c00003040710050b01a03010311020701807410300b01d1503003810307000c0c46002e803048400003940100f060010040142c0b140c4000c41d441441403100051141e125803900da0b2070b01090b0b10480b0400000001030007039591080b801d1039015694061007181f0306103640015044c040a0292900400c8082504a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 114841951 1250 114840701 114840721
    0x6060b0f1209030d091101020d0c0b0a0f09050313060210020a1d010c1a0105010e010804080d0e0304030b01090902100c1110030f15030204140106080c0d0212100509010f030309030b 79
    0x881804e6500e608000300329507860700d40810000c0312484c034054025031101c0e800f01ca00076454405e1465000220056a554040c6640014205c0600a01c419a03403035050400052082009281d080445240010080d161920081c5403c00080714000b0342d0f8010301a07440b00a40103005000003100d0400d00382e9008500380e0048800d401880e05c05814181d5540e001c1280c03e00040c074840c161a02039071031040751104500107503800c450642d07000f0318845040103040d020040c1503000c03558642c881c01c180ca02e4540c0e03d45846801d40000c1e0880d00c80c02d540c6490b030004500c3c1c49041d5030000c02403800d04104c0c00314203460324a4100c4400b2120390280c002504e0480c4424482d501901840c94103003010410102c0d415440461250b81e800200e000c0e9182c81041c0300300c0d2165a9285040300d44580c4c038800f0a69400110b44c14540040c03203403801d0305800b40700860480c600540c605101e001e843e11000b4400e071418080010381e0f01d040c0c0c008000708544100500c086076002100c82c050382d4101705205003a48941d4180 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 114843201 1250 114841951 114841957
    0x130207050d0801080607050c1507020c090403050d050f04050a12090f0303020606040e1c03270b0a05070801050d0209061503040503040e0105060a05090d0f0b0a0906060b0f120903 78
    0xc0c103501807011107140ca5900900c109040c0d034600702c100c0d20b4030703524040c3c10f60325403050b20140c025541c4080411030721a801d0540d01c0e9800105807041c5d9031200c520300042103001e202514100c003c60341c04500c1540c0340c0060303c906035205016040f140000d003055191107490b5041d25101801c4440700c000258801c500a841c05c0f8024074026240c3c041190b0b803414002e40340c100560320284224203028440c521414002400c414904640c201400e107141080c070107400414582103070b440c81c0701d14814142c025030100410440c0843c0140e41100c41031400c20503420403664020604800c2c41492001031200381c90b10b1009000780d82e0306031410f42d903d8580c02c0c0020501e01800c4000c002e41c10f000803c0104000d000702c06002100c00044104a0607603c441c100041400391840882c00240180444003540c5414142410b0403400781c0d442216800d6a5190031440d42c0003143c2a0703013802d884040a40820545100e9940101801d07010582407100305d00810700d440c030640143e10384075420b41020540e6000c0078011 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 114844451 1250 114843201 114843203
    0x908010c1b060c0c080a0e03010506030c0f01180f09020403050c0306013203070605090118061202210403090f060504050f19090c08070905190306020d09020303070507090b060c070302130207 83
    0x700d030f01d41100e030701b008041301140c07046a402542040045001402c0000d10031aa00030001e051100354000c0c0d00c01100c98080031002087d03040798914000078021107540b100000b804503070401594450850401600c0c10740804d00c1e50303010b0b92004004110a0700c5000390300b101c0c3c001e51070400d01400c041c00d904480d40095074030000c0c2d0500803c44000b41ea250844001d240d064001c0e2500440701c00c0c808454440385500e072240c9004a8005050146156550b80c000c1c8040c3e40c07181d0307041008002018800302c4081080314208d002c11043c010034403034210100e4900d0300921a0b172400510341800c00020400c45d0100c502c43c45d0080030000d111003040d521001708000034040710b030b00400299400702d5000700800d806131000703408034404807404600d07420306041001c851031302624403170029803540c0c0d5010000d62100720401c040c82ea0b201c03500e000683e0300740000c0036558060b0000702651800d2600b24011102d5808d4400d20481e8100020b2007080000b00d04030f41100d404a071800c50307025020328950046c3c403407000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 114845701 1250 114844451 114844463
    0x90501120605100f060f050d050f1812040312050c1b09060411071b15210b0319021c121e0e19090207030908010c1b060c0c 54
    0x10440500558034190340d54054001404903898440889026182e140209082841010400d00542d8040c0300080c0d040b001c646419850048400d41c40e008540c400d545041000c0703001400d00c880f80034034040c03040c00b03049030b0405803501703003440c0c440d05e00d251040d807000400c0e01450000804140f030048041d1038102e20050b0a90300d80c008200052030644691100040c03286a040740807484a06140c0f01e22078600521052083c907200c0240c46030244502e5002c10002d8460007000c0124070013040c03007045c444d503201d00d8440c040030944034584055240c03810f030001c50190717151010006280d900041c034050082d0010000009414103030001c180071140400c00b258202c810079200c80101f080d04c4008015403c2d159940100912000e0b1441c00c0383d01080b0480f00004440880541f044d00d048404042008014890880141e83c1d94080106980040034258040b800380001000024001e01070418412110b20305000c02c80400c4a14400142007001d000e441a56a00301072500c81e801003d400c0c45198100c2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 114846951 1250 114845701 114845711
    0x1050907030b1f06230a080601031a04060603021209010903050403020618090106050901020f01050403230c0109050106060f0c0804060f0309061103090c0901030807030e13050112020909060f01060e040609 89
    0x4e0203000b503a9a0b00b24070b2a4032000c0d10840000b604224252841007000340e64154560700d4040044000d8440c0090511104d1207019619107260755070b00c200c00043ca0341e030320090313212074050703040c4244407200074031a4042d0703418002c6186c002540720007220141d03581100d4141d10750302d2a400620101c086a414240c04c000c20b00d00114000ba00580907000c0550242e00701d80030a0303c888cd0480c240c903c10f86009000c1003a42c806060940380d01a460a2034060b1840140d0801c03c10322020340c20344101a0083e40c259548140c1441103680c08414240e4091240c00d0039541c0c070002e80c2c1c80420710300c51440382c0c400b040000c0505050003442500400a1150844001d014a05805410f4a02540180e4050039175100f02c41d400600341c201001c082d0f04032500442c445080c10346a450594440ba4884a1913a12a0011101d400b2044551007003070302902894040c821400300030301c10f0040070040500300c107003036070f1018040002005440e507006054a0341481d0107415050700c0800308010f481c403600302c0c0945900302 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 114848201 1250 114846951 114846959
    0x1e2003100f0807090c2d030e0102160611040b030f040c080f06010602100e030708090102071e0302030d0806090402040e03040906031103160f0317040f090203160201050907030b1f 78
    0x5214080e035518103000c0110072010b8400350380c1703603202846803607441c00807050300300381b040300b0484500c3c00a096040106810505e11a5542264446405880000107038002c00f02403000911407480c0c0c41c132192242d40c0c83c1505000041c682400300400401c82d1140b4140000c0420400600c808028042081140c4590500c600010f803141d03024081c500040c0b1446841a0441103940910b0900e604140c000e54070b854400e403a132480305d40c0b1201c019415071086c840700040340c410a441e90a46071400702412007a00f8254410513003003114600050b000c002c2c1000a0029aa075034202c41a0000e504480000e84111200c1d4228118082e59011001c8140b40840010502847e4407903480401012026108543c000d10f90a42040200d40501c02d03105000703007002c0c400200024188040d1204ca502d40c1814287e883d200e1561014494100d044169004810f009110001c000001c5400c24513000900c2103141032000c007691110746100150500c090351001c0b4440f014107846292100b0700014803003020307070b4132 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 114849451 1250 114848201 114848203
    0xe0109020d060b09060f21030c030c070e010e0105090604050402041b02070305010b03060103050d080a020d06060f030b09010b0a0c0201140a02070f0806090d030c03020904050103061e2003100f08 85
    0x180060441c0607902c184000740c03540c45c1403507645203000e4008001008047ca5030b44055904011059203410750301c0108a10303d02c4200c200090402c181c11071004269131814910808070314034040e4004503402c101000107004554400300d055900100c1903900140c242e5071030002401400d0500c403421405550a000308008607800f007400010359010b40c00a00c0208074400a00d69210002d100150560704502a01e0921030f1142000d0740d049041c0c444c003d410181e142c400c0a0884510b90f10400c042421031200001d800d8250050300000c13003046035424200d600d0410501564452040901c08200880a02208580c001c0c521540964507c60000391540c600c544003070f41c0e5016900448503600c420700c000148106000580c54450310511000e00080a4201303000e6014003907408464080c15000d006031081500d451085038003c5009800200303ca030000d201c0b003807241040c1700b44500e516040802031868600540c00c1c02c080b4403c40c40c040380e075036a1800d42404840280743c22000c58504600c01c00108014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 114850701 1250 114849451 114849461
    0x51005190905030723060702011103030c030a0c050a0e0112110f0c19030207151b2402070c030f06060b0c030a020c0a081504061b0c05070504050601020604060e0109020d06 75
    0x5000d40480e10103a4550001c0505000030345081400c017003502c4c1d0b80d941c0c20700f040c0002c4c002803031041c103215440c14182d043e02800c6402c100d44c400035200005c810403604600c03500851192201a00b0001d1500031140390080c0640a000307007041c10300c1203542d0184110f02c040c3e441408090b1104903156101d15805041010315405100d412000340702c0e000c1d401410007940d004240d64580e154004140c007514008032080c4c60503c900d00c02c1d06100340380700080841450101420313010380c4241400b4841c0c15581c0840c02c80c9510b0405c06101840c03051007404e000906110703240003501d0f007000300309480c40743d20b14000780038040e581c01c488621440401c80501d2094004044c2440c86826001e644580030b9490521050b85180d01c1000e040d43c0c03217041007009465103101a0340d040340c000c00d40031034002440b1300080b5822020f130100c040050074400c41c0d001888003d00a41e80905801c82e030a100c00d04220000079507400001c0c2c0003604c00342e0780d0b06000b00c81003800d40c49402da41c2c1c1c1c003030702c0046e16986500300200101 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 114851951 1250 114850701 114850709
    0x5030903070618060207050616170a020f0d051c11070c030b09010501050f0a030b040f0501020406020c01142a0a0b04030306031104110f180405130c0803040806010510051909 76
    0x1000c520081130860000c14079606882003c1c150a00700707140425820800c5074085810f03101950f00b007070310f140b103a50390000800000b82c1c5a002000c084081200c490702d41041103805204202c401e000281d441010803a840103045034044020030550398402c1001c8041c441c6120041c1491980c0d04000208000481414420b0640700c00821003a82e0b503505010b480303a049000e81c0ea005214a80600c005a4611040f5420034040c504034040c2040700d0b6103960032644103030002e0300543c1c003000c0700402ca580d02a04010b42500d1609519007031481260703c002006034040074500da034800d081e5204e080c01200b08051408d85401c210718681c581064200503000700303003502040c1c448512032500c84003281885d00030580e5900114000b20701d82544040300300d2507504882262440c0c062252950240c958940c0500341c000c81c0300d2014a208202589000b005411203a030100700150030a020800290102080c41d6044407804d40e0302034109501200c00300c400f07214418a03682802850380b841c00d9002c0c4d12503c110305035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 114853201 1250 114851951 114851987
    0x80a1d030c06010806071e030903020109140304090605010309050c01110a15050a0609020c060105010e04020f0f0309011d1b0103141006030c0203130909080c032205090f040609050309030706 83
    0x91b11040021141c0f0380c030512003c040e807107481d02448203c0c0c1c800e500c103070b0348240248000250303d003080c5c0c0c8801420301c001e4120f44113a480807400740010601c5100311030007800d090a003005840d0590742d40548844032140807905001d002c200c03080d0b0400b0f0501051050a500c02c581d000d0742d4804001400040c4000d03034000e19090b1400c840498044614801c1304c00c00c16504008104980c43c0500440d03888622450700c80d0043c0d020320540340c801003480080c100c0c44400006180c0c4a1a15a03001da08548040c0030f601c040b4a038904a90458040210358030800d10803008800b200c0014007070040c0e0103420000c00d0a40d83c000070504100c1d0014005005809a80030755400307001c207d5513080220382e40e000d00400d01c24040d14180d01040b11105036800022401d1017413802500344848507030740504542011404201c2c000401042d1601a032030740c0440b0000d040d0807109004242405809141d08100090000341802d07270340d410907400e115007001a114a407800800721a009512500d00070150014000b501c416 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 114854451 1250 114853201 114853213
    0x17060d1502073e0402130f0513060e01143c010503010b090927060f0a02030c04030b040c09050112020102010501080606010203070f0f05150412020706080a1d030c060108 74
    0x45081d00d40e01004010f01c030b004801441c502141c1c0302042c242d05100b160350780280e01b0002d403400d44515181810080019045c0c0e04945450101846032070fa00a514081c08180380050038401c920030700110605481626181d02d120505417004030700c0a20740d122040b1038408150b42c4265003c0701301e0803200b01264041032079090005007a80190740d50b010a0044203028401071041d00e160b41000c0a030b09922450508800050550280e0200c00a0078104034841c2160450010001002c0704001804d03001000c0039421480c2d4600a09000c1d000e02035800010881e4080c903001c030b028080c191080d080a040c164400b0009565a8054800c0b120303040801213000d5424a0000a0429000f10300c107481144183c0195103803007220765800a43d035468880840304038038802c0d100400304100300900d400c0809400180603c0d4201404c00c910760442c4041d000301198040700f070600c42c41d0b50109285400c014030300c0001c82d80e00012220142020b40c800000d079540c0c440420101040300001070a14125142c0d50b080e0ba203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 114855701 1250 114854451 114854483
    0x40f021c020105030a1808071b15090e06040e1e010c08010530030f0403140d0906050c1207060203040303180503090618040504060c0311090117060d150207 68
    0x424040d40d000040d0201d40d0600c0080d8520070aa00600e0000100d50b404180b8541a81d40d51034043e00404415120103541000b000309045000780030202400080710513a80c500003c01006045403414007980f04044500c0c00030400c039440d25002040e94000360030544644c041400ea1503001e040750040021040c0d800d02a04101c802d010f815141e0580e6405001d000b8420280000d45018501030440c00046882550f5280d224450170700252007016400c3c200e10f03030740381d02e98103003000421200f04cc0d03500950400300b440495182c01c20151802c5410a0900355200d074817202c04981001ca815020120324500010300d20100406540294810740c883c1d10304100a0703091580080c1440c030310350001081035204021800f0346160180107441140b403d1880d162118154102040c150740090340c040394280e40341c10120f0901900750144004d1070000140c110f0138030341c0c14000201060201442c0c80607850070709000c506141c481c04030307459a00390841109000d0a8040310448001c0d44052030a85942601c042c8000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 114856951 1250 114855701 114855739
    0xc120c02030606040c0c120c0201120c020607080a060f0306050118020a05040911090a0e09010c030506012307020306102309151917120f0f030a14040f02 67
    0x4001960064020b105542d26501070100400d500070008041c040e00020641c005140301d014031000c000c0d01d50301c03445480090300c00508424820308020402d1410448414032840e4001101c40d40044c0d00e01c5c1050083e02d8410031140140000e40150a5103592990088144a200c0d00028104d074250040c40405c8000c400804040f805401114000110704000070031542030250040d0040103070400d4102c0c030b004400c100050350b40009510113201c456520040240b410804c0c800c80710525041e0400b4480c1e480c040c0002001050303030104112000300d070703800b13514800c20045066030310841d4007404481c22820443c1800321310105900c06d03011165410a04024504400c02a03000c403280b028241705002d4652000751420b0310a0000c0454012a00301d0110300b1410780740c44e020001309040c401121741c1460480c000c0742800b802c01c0030000400c00800410700041d451074119800030894100903038036038507001d00c403d01a2040c0700c040f01c6405c01c04000e0006103d03400764075004d804e200711007007202e00c14161100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 114858201 1250 114856951 114856967
    0x1091802181e09040c15030905101b050d020f0a03020403021e06030403030207140604081309060503030426010606020d030516140a023307020304030f1e120c12 70
    0x10522001d2000420102400c01c0d01ca001c4c0c00612070203a020324540c03149520b40140c20701901750000079448802d00301c2440700c01e0007001c0c014501880103002d0b07042e203043c581c03012421840034442000b07000a906034107101c2c0c66044e02c0c041da100d20b40040c3c0c1c405420000802035045400141d106910992510401084d03201c0a00c000303d201400303044c1156201d03101940203402092050310f0800c3c00d101e82100b43c1c030302444000d114a21802c0075545401d00c18419582c89500b5400101040c1d2402409210944c1e00109840440d03602200101302c002846a000d901e40044c404802c1003036003803c80c00702d0507580100780c20400e02030361b07581004607a5035104000401c0170395074410300c041041e0904a41c008440c1c2e800802c8058041d00440d95a58591592001d2070704a80d00e0300340d107160708082d0402c00c0c0886503009075007000702c500c0114181401c40c0c407020040107035924000c0c074001e1031800600804039913005c090140394000e40d03101da02500c0d200010b030055200040440e1908801d4007820040782c050710365 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 114859451 1250 114858201 114858229
    0x90c05090903130e0403030b03100c080c12060d080c062a0f07030c0507051c0b0c040303020d121107030f080f0c040306020304060603020a0b0a081e070e0109180218 72
    0x880c512184c80c001d0342c4050600003520a0b0201929140000010b07201005903100c07520207a080040d540b00040801010380300054011074041c94208181c41d0301d0b21502c442c10741c01c11000c0350500c41d00142858101e01c1c9115084200f6103038050282000100201d10450507020340305104c5000c040281f019290743c580c400c4020b11410400c090040340d0202c0c0c03246546030341c0d0910a10866200a844900181818040103441d404546448031440100901840c40d0354028103440080d5042c41e045640113902c4540740c0c0c5c2d030320042011900075000e900c011307a00b14103105071070300084942da40801d00b0010050b00083d07a11340046016003010640360445204910322888503050702030f082c02c0c00c5580f1035020f0b500282c020b44007030752035182c00302c05a034903241c4040060014130201e070754440c41018040d1800760b000b03191040c0c1c021640c104410f00c2c400d44500c5540001c440c45e2400d0018410001a184036103070b40c200900e001b500461000c075010722640185160f0305100b0a018084203103908000703440c610100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 114860701 1250 114859451 114859477
    0x909030f0206062d040e100207050c04050105012001090b0f0a0e07140402071104060f03200108130305190f02070819120c0602070b0a0b01050712110a06090c05090903 73
    0x244c4c40401d40b184440340d82c03100e0401403000c103500108034140741c40c1ca103c01d04207241e069030004082d42000010086195040410b031400c1c0040d6141c480080d056039200d980494814406404240c155202944001001039015500302c00c00c1c01e1a2108202c0e00208032112040680341c5001c41380c84034400180e01049034101a5103041c1413222405001c065008803a088590a00246c008a05903940b8010440500b0009001415480c95030405980d0003421146903060300d1524242c3c110343c2d03680442c1459008135041003100036149185811555031060800000030005400c240f96a440e600002240d50300115900303e0384829180c00d0601d8a03244c02a000030082060a52107900141d99024007080c464003a0504440d1000161a503409a83c400c01049840704e9400007040030441f89441085100350081c606507043c03250b01e9558180b00d420441480081c803d40a410304816007042005540d0154800401e02586a5034030f440c1444000c940141071142d0a40d400040300c03081c0000540e025501a44 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 114861951 1250 114860701 114860749
    0x10b030f011e05120c030d110309010c08040b030a060e06010504080c040b04180803011805010522150306020d0609020304200105040b040e0610092d0909030f020606 72
    0x900402030b00180000260341405025000251691405000032418801c28064000765600c40201400e007a11034042d070041c403442c2c01c180041c6110010035501120710030300300442108820700300100540210b0f403100c01380c3d04000040001200c10340d0480070407220002a16650f648419006694501450103040010b42c442e0805540c5880c1c6900100c022703100103030000821180d514400c003140300000c001038940b086c000004024400d008070b040424408100c90810955041a00041c009410030740b8a034000c602c0c1c54403001c0c08004661001c942402c80901c0800611794034070341040a074014160541103103141440c001030007103950085a02c103540c406180d420003a041d201c44c50004e0003042c103080c10054284400300f2000381d202c00500141c514002c402015283c4882040188500c1100940801c000c904081010f100312140d400812103030b03071420f98070b0744441200d80c81c090041c542c05106007504009298040c51340081410302590300d59800e540265403450140310340c071290401c00006072200e807 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 114863201 1250 114861951 114861959
    0x606031806110909040f0308010f0e01121a070314011d16030f0f020903010506010212191803030306050907080f0103030e01050c06040506071211040603020708040906080105040b010b030f01 83
    0x340e407000d00002c18218a40d810a08401d010070b403681d404883c1100da4010307200c203a5041c150003080f050f0050980c040d5540d01d81c0e0500010340c0340c407a018400c903509003840304682d1040094800181c2030541e8172210452451900b0000140506182000c8400030041c100007c00e480750b40c003c64408001e1030100b8140981c40300301480c00684c5808807000c0405a6821150400c200c140c0184603080410716030142e150700e910f004041c211140a00018150750200400c940545449010b68450034080b407000d40300d2115120056035040600010340004501c041c80104c205a003541c4000107560064030307211180c3d0780b00c0b101a5401d480c01c0d2a80710201d06c200c0010800288203034458541c1d4981850320078200300480051924116050741d080711550000750410215079802022522412102c03202031000103455044038210b481980071b00e00800d600001d404040c801c2d0001160020501d40c40200682030740c903c1094020300301601c0840340c0a034084000126a0328074402e40b405080e0031014003025900e4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 114864451 1250 114863201 114863213
    0x1801060b07021207031a0411030606030604060c030908070b010801110a05040e07030908030f04060f0216060e070506030a0507080105010903030f0c031416120201020403051f0609110d06060318 84
    0x2401d0354403120b208611011001900740b1084509003c6c0c0c8080c0070b002c900302490310849510700354a1440c060790101c010044181e038002005504540c100100080704c04003804110702400b08100013804072100000c1010070401147d110f00d040310326410082200407400381c05482248200d800910004a0620040c0040c010303245036035070000f0f0389050008070312840780d03141c000036042222486071a1040310100701c203109c0d02c1d000301c51454051031400c625181b03100302da04a01a151140282012f55a0b440c0204005810080e141c003420000300b200d500c030700e0440407035400341604071030907070024500b8000018254040c90036003081e603074140c44a554610398481d04591445038490141c08102400045000820f00314005046620002880e034800c100755003803851400342c85450346400c580c03040004002103a00858201003404074402003000f90000500d01102810640d0844d040051820402201900060700100254107a04500348940d950703400041d02190011041c4401d10046003034a8400150 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 114865701 1250 114864451 114864469
    0x50d030327061b050a120902030c030f07060e06030106050a23040909020102061005060909090a0c0e060907021c03090201181d010f030309030308060607060509061801060b0702 77
    0x90100c105620100315240c0701070304081010180d500a98a211005040300c00d4078210482c10410300b040741c50514022802000b913086555042c0308181c0d81c90022085642c01d2000ca541c03034200a04076003000302e0407620261951464803a400c0441c945150f52481d030b0400c041503e04071469a120f041c1009502d40080ea501d0010150000c0c046d00d0036208010090075520240021304501c0d036001880740c400d40b00292814401a044001020a6200c03c20451790341d202103502d1030380180c50207aa19283c103000709140c0210564000c100d41c50040e004180076020b9240d02d441980111861101c0342c545050990b1550750300100d0714805501540180764960207504034600d0300f481850151088000e1848035045461207411403a40d02c401044034401130300c154102140507218190140e0140b51455070041c008014921008050225180004103142c4c1c030b034001e9071422508112306222610384110b10790b48400301101c00e07020210600b419882400d0381480340d00203a0721041242464000c064007040301c00c0c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 114866951 1250 114865701 114865721
    0x608190206070b1e070305010906090605060927010b0702090c13061d090916080f060402040b01260103020909030901020c0d020a0f0605070507270e0f120c0f07050d0303 74
    0x901d503880c900d401c1c1305200f800c9600c503080581d40003030654140300308101503441c42d82c4205642c5042c02c80900039992004211b982d20002100c1c8080e80080c0d11941090301d0008041b002c1e907441444c000010b01455110041510900c2140c110000713548105004425004d09041c0c01e401c003c40714003e008440c0540c081c1a0021080900500700d041208000346d0301400803141c13103020382c10070546100341407144582c0070064141c1402400045c000e021005540700c40061000e84034a4136045d44161a034080e40c02191001000c007854100ba00c05030392455101c902c01c0c40100e026080410000303011080100a890300c4620590140c24030f41940002c100c21700d09140c0301607134000400bc1d400075002106820790402050651030741034582c0074600300700f03061040a81c07105400c8804004c024820890520840704d000440060000f01c00304c4c4c04408510b8902d13a180c0642d04d510a0750200241d002c08080031b0060042c445040b50900660044202e49480c081c2c4556508000c10b402c400c00000e020303030004c900380 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 114868201 1250 114866951 114866971
    0x17040608060420070312110306010f0509040b04060608070f110703060f0b280b130513060e0c070c0506090f09090307020414010611010e0d050a02030405030304090608190206070b 78
    0x212405541d043c110750300041c0100e02141c405031b1040411021405180600c200c409122411031801c0c000190420040300011002c03c0b50003d01c60304555140e5105a45515016108012840e1901b40181c1b005200791100004a055507000d0f01c2090304c505d945088142480000e05403070781c07641c0c0c0c1c0c14003e001314a5082500c103844409010701c0303031180e01601c40210a12002074030f001c03200f04205500c86600ba00300c81964002044460300c02e50424404004607402a914a040101c4598011004007216001200e8112504050010000103000580142d07405004030000407036844d03081001e00e201e202d005582004a250103036042d40b0f044101c156100141c80203482c984040303940000e0454040d080010844030041004ac0501c0d0751001402e400c01ca0034038000c100c09501d00600b0350382c685982c01c00d00104580020780c500904c1c800d005075002424040c044039150358603004080060020f40c0240a0709201d20070b64103520702c13020900c41e01c0b00768018048038504505900c2d10042000d00401013910 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 114869451 1250 114868201 114868241
    0x3020c010e0402300a020702010504032d0b10080102040f03020d1406090109060506030c03061506120c030105040b0a03030f050d0e1b0906030c03030f0307090f080a170406080604 78
    0x10314400c00c01a407000d468069011310f505240200d8048401d40050300b0300403018814011040140d80050894003903d03000120f07030028000c404245603085d50400e001500300d8014100704410800c16035440e6014006212002c010a5100c54a030f500b01c3c011441000b0050300700c00e804101600341800601c80c0c0ba805194510911072560b894680751200aa504e00802d80d034807420b030030902c900c0f0303c6010f0708130508802900349086860b002a95804024081d0000c6220360040c0ca00a80c0c1c502d0112208010100c120380300902c0d14124001654000340316890050303040a059080c540340190400003500d40c15242c0310000c0c018400112000d401004010503020754030380b1b078405111810400301079005c002c44952620080d0510030f100b20000c010704038600960000c5034070303080c60b0b40201c10354840c6005e00d65855169620307807104486050095101c1c07400580d51410100d09004003003503111109000b05184c03240c00803045101e1150340304c1c5115030310006403100082040707403a01e6000420030720700c24071180c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 114870701 1250 114869451 114869467
    0xc02030903070609260c130209030a03030e07170304090905100204091d210327060901050f0c040519080102030a0204080601080d0c03200703060f0b0a0303020c010e0402 74
    0x442c0801c26080100400da840004010003070749000c20038000080480c1007401211000f44040e600c20750612901c0c42241441c40c00301024025505a40000000400700c404405440c140540142401c0040b28001c2c01a070b1008208410400384103400840c078440190314103440e0000c4980240140c0400719098050715141d44003029041c000742c800b501c05004009a03120750031022816000b080441950035400680c2041403170404000442408000c2c2e00303040b5500d540f43d8030307020314a6461105007400c00012581c00d120143d8001455482052100c00030840c6072100c414503035202008440902284004100c1071000d800d10a21040190460a01c405152034941d02c1c0c0d9400d90300202d846101da81d5010400b0005020b041040703c0c010304e540b1000e4546206100b070000d00350702c51508040d040c080942070070b41caa03074481015001c8070701030102900d0040f41c4900e0800e015110044103c40a80d00340030796122103140020b02d10044a506400505503400000011f4580016104050340c4c40796090118034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 114871951 1250 114870701 114870703
    0x109120516030606081b01020309010f09050303030414150f0c07020102100c02030307020d0e0a03110d0c090b010e010806131508070f090612030507080711040905060601110d02100c02030903 83
    0x14055449000c0104446003459102490b1020103440310400c1c91506c0a0101c00d0390700401202c3c1c21502c28600340c01d0719044124151035013080f540c403044e014440002004140308010501040fa100e082c0c042d41e811250508084070414025940d03000c00e0f02400000c0380c82440000e00030802035106006950040e100f0700004000c41d460720a40c4800350f04000308004c0c5c035a60520101d81210030600b09001c010088030003007060071849020003042c04030401960340361076070303070500034a90258080001469a07450780c0040000c0c1a42d207481501080c80c11400f52020342c01030744032910480000e49091035220381d42c18020302410591f4241c6441900c8010042580302050103000098150f15000d40342161a2004007000c40d4151340c4800700b440010100c00340001d50003400c44040070340019005454020a0401050841041d43c5c0c05030712601d4180d0b00700030000d01140151042c1403d07201d010142d42890700564960083c1a100030058104c00c0300045000369903070000002e01c000c2d20444e41403054100c042 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 114873201 1250 114871951 114871993
    0x24030e0f0a020307050d1a040302030c030a030225021305070909060b03090d0f08130201020309040f0b0907050301060e0909011506020f01150302060904020a0212040b0705190201091205 81
    0xc000301d4010340405015400e00300006070080c034098400050301c0030035480b044904240e101c2c82d07031000e81e010030120b01818800c005584400e462601a2030b40c4200e1a6400b030f0095000e410852002a11130010410450408880340c0c81103801a0103903c00004000c1043e00421004001d80c0600842c4000451810b180307100b0900602040e40759a03643e42841600c107803600500b40951003c0160040d03207400a0f0740d1140190780c120b0120a00c100c1c00e85004c0c801030341503000300b0104136005803800c0b010303000510b1684c0212812500507600a920740d01d034040112640d00c000d01a18010800305099008079003000103015034483c0f1414000035025a00c4994441008940d502000c01031340b050440032002e000c04c4c451168103015440b40c6a140030b1850f404a501c80c00f6005c4040d214550201d81c514201c0d000f4000160050690066665550b807180c1c0c0150141d0441c103415113041c03184012260490709182a50b00d51250146c40d9001d1051600007602c15110410400b03e80c280540c12009841d0701d03e81590b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 114874451 1250 114873201 114873223
    0x8070c08041514090a0b0d06031b0303030e0f0316020a030f0506070f0201051b0f0d09030221090d0b061c030e010e0d020d03080601020f150a05010e0124030e 69
    0x5102c0000450500200800b5040340030f950b001e2810002c031442991044500c00441381c401c030025450f0842c0f103494070300a0015a101030f0840220040710003500000300901c8082c3ca200e614200801604058082ea0320790381c000c400d04865008105440241d4107405590f100b9502c02070070200c4203030322591141409400054221010b034002c405010440b40c00c030340030b10341304550341c030017002a880d01c424641c0041c5540710b505044410300003400e42c600d4100300c00303c03080358850035001d20071402285402541ea9a60400c194440720001c0d154003081c50800e0102c52240b68010408c0c0426815601c414034400780c09000300e948503110030003000c5404070b400c10503202a8003d8a403003203440c4482002400b038404407401e02e441075844448840042e9154820510170700c0c0c240c5002640b40c2e54548c0180d00d01b030154800d83c80b45101380320780c1c00f0b0408030742107026100e4503005200f8402c59a0300c040e5919030650078088c880203101e5501c244210354184800c44010074130b051402007540780072071000c681400b0b44200707 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 114875701 1250 114874451 114874469
    0x305030d02070b18030307080a090f050a060f0e1e160e0f0c2106030f07170f0606060d18060501030f03020f0c011b050304050603070513060309030c0308070c0804 71
    0xc0a60500c0303480b80e0030940c0309114007444c8003101018552641c991100905110a001d401008070702c04400c183d01400c40103600440c0c101103410217003450395840c200e440d03040b2400750405420484481c0b2a000305903030348900070010460710414020311780415081003008480f5100304035213840400c07400d140c01c100410a075100d000140c01e0400c005604001d00a2000c22151420055081d4800c8800c3c1142802c02000d224040140c40e481c0000b0300309512410800224482c1010114100041911504007803180d5811508080c50300d654070340d05c41504589403a48807109000c1983c10940b02c0e04100b0038433100c1c88400e642c080083ea101011107c0030f0b081a91500b00d45a440300400d07404000c80307850703074144600030009000c0743e00c0002c18945001202868940706c2190b04c0b0100042003040c0c5020300002441c0544a00c0c141c0d00081c810b40020841101000c000800005c1090107407041c442203c0e050341e100c00300900d464030140c62000020b0031050801c40c2400104011801c1c01c0042c20150940c01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 114876951 1250 114875701 114875707
    0x31502070b01180b040504030f0815090702010c02060906130b04060b030102070606140d02060405040c030f09050109051e060f09030d060314010b01080f0a0e030d09030305040c15080708060a0305030d02 88
    0x106502c000c4695600740140174514100500021a0304580c448084a00340e1401c0841990b079082040041e84068051940000084081c0009950190005000c0d1500c0d1f031300719241540d59005040e034804051343c080035038500381c00f0b510003c00c1c0c98415243d031050281300c0c081aa094205e011a089030700c41001501c0f01030b547c9030148008080076600064600d4116807021403913075035070001340e610b02c11441010b200d296143da4181e581d90194100d108544001c007070421080c1002d06206010f4030103414101c505000b400b00300064488000c1030201a1041c140040031550313103610060001d80f07070160070082c0310310050041100c2031030f060107034001075846800181902d4171111002401c2d00d003001080742c1801a07040c100075400700b010f0344c910f40c40700c00608041240d0181864450651249a49441000e070500c14a202456055004030380258862840c4402c55613560040243d40e030305d4a007007040001d00d08000301d84618810300f4100d8100c0c00050410910995036603034540b46a100240301003840c1c0e004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 114878201 1250 114876951 114876989
    0xc031104051501020c270a14060306010608040609021206070207030c050402210c1c090c060e030a061d0706020c0a060908061603021306020c040c1107031502070b01 72
    0x74010503400107a030407103042c0c18041c200d0000c3d46803907480000d13078020040d031905040f07000521011074240e480812103104050611151400181c5080303a038030070f02400d404020503114100050214103c0d040c96643d2542601e0755a514000740200c0c41c0181e0740080c851040c50b5070354406000b943c1c003c5a15400522080c1d246260140181010381d00c0300d44264414800d102030840300c7d4401d03512290041030384035266030ba00c008a8210703008440302e203150568030a102c0f0039a01c510764002150f090064040140c000d640c1c032000c0b10002440c85a00e501038002c6849000098401e030004102c42440040410f500c0082e0403601c2e00d00b0103190712404c0141c2c8811320014140c102500d00d070006d8002482d00c4034400342892039003940c541014081710f80184403034060800e1a80700b44e05803400200e1480030b0951003030341c42000070350300c080c1c07983c0d040d205030300d0150301c07072172007402048440c0e031540c40e940182c0a0301d45542c680034187d0006100700a03240f070b020032034140010345401505021300b90b56007048440200c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 114879451 1250 114878201 114878209
    0xb0304060615111c090b030a02040b0708040e010f050d02130b03120d05010e090d0f090302030106030c081005010f0b0a0e210609030705070b220303020303010501030f05040b0604180c0311 82
    0x21a01184c0329001c4000c1d0030b41c840d500840e40b20680741c1d07911340316649480b00c101450080c440d0794001c1e08110b0012a42104101c00340d0010801c0303400b425250207580e40c0724102009400644d03c115644036124001210042c01d00070720400803415044800110000d019020900300842006203201303011000a40d811059082d04c207040c05000030600005c810b103000500c203507540215090f440c00340a00c0e261100d40d410b1181c0c044102859026009001c0d80c2d13030342d18000b840c000b182e010b145d13090301038035100500c45d00c06071141a0403143c0712980f50216525064490403d80c3c000c841d03480411004510110303090300e6040d42801c007051030200d400c18110303100c050181000e6016100e044141c02c20840d900109000207104000d07a094000042e80d03400e407161184000345600040040f140749003da000051507008001340d4101c5900380c8040c000d942e441d040f524110f134001c035001085141801e001c5240740c1819840700c0c81c1c084101d11180c3c411960341e11002d07001c00a03603100b1900e41c10049004105420 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 114880701 1250 114879451 114879463
    0x6072d14010c080f0f180a06021309050405071e0b041203110a031d010522080105090c01121a0307030c050f040e0604350306040b01080603070b030406061511 69
    0x80d0b524082e001070400b0603401c1e1403100040d00c1d1084103454400400d0b040b2180700501c00c4034011040803226075001603d80315010b500645038020311505042c0000549485a000300d03445240c0c404042d1048505088108861040124840e145482c0c64940490001d10000060010b400860b20b81c0c100c216082c60002c004144200340120786400500003c80001d4000b000101d2008506408041804007100100ca00d4024101c040380d030710110714110202040c040c0400d0007a18404e00082c09030350740c1e030140a940e5941d040301e41030000b00940c7d112010040594412101b8801000d024a0f40040b4580008d1a1028640080c0e03150950b04004024034036254510007200c10b400c1c3c900307201c0a20401015605c0d0035008201600e80e4800411300c5000e60810242a00c03640110a10001e001c2500c3d030080c1c1c49504201c55060045280072040912580220f1000d031140000800901d601c030b081c14803100795500090022101d081d242c02000c50681961346807082c241e441d59940c22452040c00102c1e600e094 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 114881951 1250 114880701 114880721
    0x90204060602210307020a0b0408070c0b092101061208120f160e150301060c14030301141302040b0a0305150a2301050702090c1c0b06072d1401 63
    0x15205000301c0303143c8012071020640c00030101c2c80142d22030f07507078850a900f090001080100180580008c00c0304200c0880080c00340b00340107000416030107417614a2070380148a07680c905507016224000c0c0000b510340003040301001e0881a000807900c203940d46c0d08035802c50740b504801c40313401201103140c5e908c03c1100071440c1e500082541c0086140d080c0241011000c00d9410750820030452640500101c1c0c0d140c2e20301ca1402140498030441e500e40e1b45100080070400240340488419907413411024a030300380003054078141ea11450701840c00ea610315007081107004001800e034034107039028400002e40000b204050a11a175198a0208003403910a090540c0c4180d00d18125100301c442c0c100078800039240b0707460304030760714252b10303556824800400050314540503004000f5809031094040200310003c00002e031503200c4951440300000c546098540017500e04230740030241c00c68000c1c000c0a0200e000c480c0801103200064503080ca03000d08092080c102202001c201380c41411740d20040c041084004d1261226403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 114883201 1250 114881951 114881953
    0xa050a0308040816030c0302060d0b130608010e0328020f0a08091f0905060d1404050a05010b060a1b14030a2304060212030411060706050a0506010c11091f030501090204060602 77
    0x2c94217582c0c2e00005c0c4010b6000c003030b0042c42c0200b203074900a0126030002d403080e50020045022a0808010140030b4442030048000c15400e20380001d0050380d00100b95030000f6003407400340c1540650240803691151104c190041148145140c0c1048045d040c000c00342c005018044955844a5181c00e128018220490200303c82100c0654248190742c0013000e20309a4008403a0140d4886030841c07140054040707a4400c2c50800420014442003000c006a0404024441c0e0004d008000d03101c2d041010074080e119071000801c0740b02500c1020b4a0384040984112403080d00324542c0d040c90814110f25603004081c504010801d44480c43c1410f81924140c070b201041c00111051502d03090050013522403640071410b10340118003001203410042c039408004044074000d84607a459403401d0420202528044d11004020341c0390401213042544104000c2889642015405280000d900c0c140300115100604510b480f90285241608000c000030260005502039800030030b6403035a070700403c02100c10790751210f415 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 114884451 1250 114883201 114883243
    0xa0e070510051803010213080a0204051e010b030402130903030e060603061e040503190203030a0b03030a0e0907020c040c0507030314070f0c030c060204180506150f07020a050a03080408 81
    0xd0302c0c0d001086401201c0452424105a8403c1012a0290003404c1840340d11a400d04130204041000044a0000320f00071a41407089480300d40d0310000b50181e10b06c2042940c01c2c3c0034018040c650040000799005880a400d00d000510001001021180c5030300e0110002903e0f1364811126040402600d80c04c080308074050301f41c80c242500c1c11040c1c000581606140c1c50900c0c0f0020702480703000c2c02581e100c9a904406502c55556200c8025101d910880b883e00d4a146044105480c2e420000f06035403099902d502d60070840900d800400c850880005d00e080114460008142d103251244d004003481c030100b9858050321144286000740a0b51200009112000d96940420800350b500030100030181c1104d0604001003151800c0464062a1031017001e0451800040c000480e4a03404035120410105060104815168401001608240d88149400a1500f40015000f0115680042c10444c0c4020110b0801a035207001040b08005550310503039a042e404601000740c00801e0001c074010b04400c06800c44 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 114885701 1250 114884451 114884479
    0x31707200105250204020c0d020d0201020903030901081f0b04090c031404030f020f031804110c0703030315050411071202070e0403080403120207050c030111040e0c0a050f030a0e0705 80
    0x800d002d100c60000da028001c1c01c007540340f0904452149101c40d0083c1c01950750354001c0411a5650400804110042c440ea80d08014a103106200340d03480d030ba4008028501d030400900045800c9503000c0c02810800c48000154403444810803243d10040143c205080c2d01c071882d2100040488a45110350f81c24507050440c011402e401c41c50764a98030551504101e821240c040301d08a05e0203058210001c0c543c44000b50401094203240c0707500410030004c84050101e04604101c641e030301c0c015664150895401150180000780c081d4010510b070281010950120310356460001d81511034545c4c6131089103000003011014070070b42c410101c840c1b40040c0010b01000e8601720801c0c0d03031400c0040026041141c02008941010302c82d100443c082460300d8401d5403203000da402e1942d00c810000001900ca03628041c3c0d0010140841c42c140c0701210321040700a1038590307903400c01d503203e079000071070300d90800104210500d017621041c0d000d14007034103401c1000241c800509040a19203402600321512900e6042c1041e4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 114886951 1250 114885701 114885707
    0x12090308010e0601090f03060c02160e01050f0a0e0a0b06190302090f030c010207030b130c03050c09010609050a1e03020303040b0d050a0b130209030a0c1701050a0203010f05060c070317072001 84
    0x1002c87c1c2d840702c00000e02d4070303080c10200c1c11710800000100504180e00c00004550f140c01d0151030585508880050050828508024082c1400d20850101d24a200c000964a280d00e51001801c030b88050402d0345005a00c183d010740c44a45d84402d08040303079010900c031025080010019000140941c0185090001640007079a02c2000d0b100081c0702e440c2032400918820810100a04101d0340140c0050300705440b881e203030b619100c1c0099028007600944000044003881500700c10100ca1029100040c29400c001c950041041401409240b40300c03120000001a2001c0000300004c09404600365120015444800d058503009000c0b6004175043c8140349800759280102144508051100141c0e0303080120301023800c0c00c0c1180c102400400a416000441b0f10070003150540102c40c45008120039641d20407041304a0001f80603074240c075080c0351414095400c052005210f02c01d0411304030f0340c3c013030b5683e600c00c81a0a218451a0072408011610b8010418420400800d1082c407108011260388140002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 114888201 1250 114886951 114886979
    0x30601120f05070b1b060f0718172b050a3c02070e01030804050402030711010c05090a0e13080d111306020609191212090308010e060109 60
    0x88000c4031a60904904100c0c404a040ca030095000b400d45100035912114030005802441d40000000c120307601074002c0c1c10700820590700c91070361800c100083d0380301d00f40115414405500301c81201d030428840802c0071041c2c580c44401d55600f0f040200a41d1a84c5080d1078022140344001d9a4400c0302c4100e52414542c00101741c41c20a2100c3c640081e61040810405e10b803d1008000094000024002e40c480f80d006180c00f00c44405a5800700c8114565500c0480803016091201a00e00041403000340501e00e080c1e0020741d081107013841d264800540c4818800c1c21071328004452004144001032035015400c0c4900c01c0c1e0014501c810814207245400b0441100d415403586008041c203c00040c058000341e241d62004444403100c2942680394540b01804580b090028020400544913950004400d40d50001d0090145e0702001d00714800c40d411640c80100e1304551501810501c1203880d25440c1c244854818040e0b024069590030005514116058203811805810107040005025090086000341005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 114889451 1250 114888201 114888209
    0x224070e01200d03110c0a0b0a14070801051302030c2b020a05090405150d0311010b22060501092105010f021b060105010203070c15120e010e060a020405030601 70
    0x360461203441001200d05024144000c1d04070242d1031544110200d000400000da684641c42c00c0081d0b25950403042120f026088215400da4000c1e101000012803c03440e240c2c2000f82d101022a00055000c0c001154500840d880c5c00000c44801c01003100f8034060074108002d4001040451460800000c003125922408101c0f101241c1e65000720315036001a6000c480510070126021920380d07000c9240100701382c2c0003102d15441b590425000c50350a41100d4403034080100002d10342082d148160303500b82c51040d9002c064074095503031107488010584884039001c44542c0c0282410b03481104401034801100c2c0e26402850400c0a8580144900d01030641c40c0c01d207905d116250348900c80c101c0c1c9000da0141c03070140c0100340020700110303690002910810300304c00b144600b00c00396041e0f0b03030725a801241e40f0f00a0450181643d0720030740e42000095200d0350682540540ca26040481c018106200d00580c0e01c00d41d9004126076484800110101e070a012040d08903503070300710540c507061500e40001d42e62401806 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 114890701 1250 114889451 114889457
    0xc07020108070c050f0709020903071a0406080c0c0d0809010c03110a12061214061506040e0702030d1a2701031b180b09012c091005010f0501022407 65
    0x10003804401c00400c44a41502d20456062030340f110b00d40e10194004680090080c03069200201e2403415406d039401c800166180c114dc00c00c0d252041c100d81c1c407200541a442d03090403c0026411201d818040700803107074250740350b020460604120081c00c541e054070480c0300b090310302101182c203041d00c1d4044420f1032030545442c00c90301e01d0303207000f1100402d401d40c403110301076441d01d0310b80ac10001c017040310000b803c0303040e407d451483d0b41c0e046080340d2075440003c0e820782c0210208410b0042a408001403904103040e881102e0070076128880d840111114494085040041e0740e42c445614a4040868911480c400d081100058211110340d2890f0006020041080d1100b408000c04103000895040c01802d2054000020441460244000f40720700c0c11900e005080000001c161030744201d1861101c046030060440e00340000c550103140700407015203804510b000d50700359540298418000c86018004200c408110507103044c001900c3c10244d801c1c0c01c49040707500449841c00c034003070080d030b2540650319003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 114891951 1250 114890701 114890717
    0xb071208060a0806040c09060e01080a030315050d0f050c0a05010507060b030f0a0b0103060c050a17060103230a050114100e010203041505121f03030e061303080a03050c0702010807 79
    0x150025003a07010701d0700210844c0c410001080180603449040e40202d5070007100803c03d07543c4030503181101000074091070003540e00c115030490000c1e120f980420007030000443c20a100a840d1000195041101441500c103001d04100c40c1e0107011050003018507102c0100c03441e500a40c600750029007039015504d809024240d071204108810f460a00112001001c3d41d1b068851640c554549101c0681e002e000a40310585441000160b082c05007089aa00c564180c4902c400e08200c0089400345100081c2030904050b201c40d005200c400e4104190283d480711406624800d142c840d0441c0d040b6003050b0b00c070300703503c1004218400850b20341180f042441d0f985840c0c072210f0904903000507403440c0b2840d030000e2150442008081d004a50081c0030341440d60210464200b00d0b201e0507903265015054240c819604840540200006401507510070746503c40a021705041501c00b40f0f1003180c2207445d03441138503800c2002030802c503a90b6040c422503600021011016040403803a4000805410004001c0d10a100c030403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 114893201 1250 114891951 114891961
    0x203040809030703030203030910090c0b030709050a0b0901080a1404020904111c02120a23010b030f24090d030c03020c0109050c150f22170601030c0b071208 69
    0x400e04807201698080e0031a103c096132071400035600d902c00c4039502411f018003d503080d00e010450080d44000764014204142540c200803e80e01184d001408007030134040c16100000b0366880e1804c07803e004042e1940c80039110807500700054400c8800a141ca8000e91524011000c00d003600b048040d0040d8041d1020091036649290500d9007602d043c038203940c03040042d09150280794a4094030b00c0c5403482954100000c02c4001e0300241e6651543c50003c000d204611000701c0c805010501103880b401c070940002c1403007100314010030300300300d401d0081c010700390040d2340c0c80310405d211001405400b070650010782e25680703895a00c0d103072282c2138000403104250f2a0049015802d2207030301039071850a100340003082002681c1c5000740d03841c0040303890369024210314100c50042604c10f5054901820f6141034952502c58403149482d004650800000501c2c1e0482c0380100750403030a240d085d41001e004c1b000070301695040d0708100c0e013442d0841c0d02c118106182004281d0000d081440c00540000c880e0424010b01c0e158 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 114894451 1250 114893201 114893213
    0x30905120f062a04030b01051e0f040509120d0c0906050a02120703051c0902030c0409020a050405060a0e09060108120930030708190305460b181009020304 68
    0x3a02040f198020049400f00c02d020a20561a040300c00c1102c0e25286041650090010719a290130b9140d0300c214020f55101c0181004d8018a5101903000103403003108184544c02447d503000310013420001c540e104007203880a90412000000f406207410301500386070401100a543c1c0c5020348502c6042d42c0e001c65408201030241e003d503800000200400b5018201442203000202180402071b40320780b1855200303844030705041c4200004180c010307001688450400b81408007425001d8440e603005101e040c4000380c0010203594503405400c0071000380c08107500d001401031400d01e80740307030031100090100a100326a0382c400a104031082d1760002e03243c03c170301c0d009088002034483c0002c1e03034655404006440404c000007000140001d54040c105d0000450b1501c10480c101c1e4800c44010322a41c050760114031168003400d800d1700d200b1515911907262a10545c550201e5520200948802c440d12041c000401e4942201628503108004000307407280c3c6803002014107001500e20542400b030358004003050600c02 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 114895701 1250 114894451 114894511
    0x503010605132a03020705010c031e11190f0305060604120b0a06050a0f0608010e010e01030f050109020a090e10051911040803030f060109090e030a030b1c030905120f06 74
    0x500140d001d45907092801011380603500ca07420440d02d5501e01302d50b400030760f40039201d1050b2809503d1418801902041400001480c5200030184441b0342032000b01e528480500c02502542215a079003009030031030310310140907100d0150400b84119001d00c0b0a0200b200e00b03030484040c642e046954000d00307403200d5000000410030364003c9900005090400f00d0600340840c800b41c111940ca6807011111b0780d0329590013000020038000c61501002100040000c54201d0b0400d205950054000207140025580010080b414650021143d02d89034141f856502e002488124260130b9129010b004514200701d10100d00800107007856202075461440d40c1f40104d6280c00c0d54003510403c800c0700d9485c1010410080040c6088074258001201c2e41004a0140494001c4562000680300203500b0820200c0e000d5002d00b251411594200150080228401c0502c01c102d401c0b280c040d45410010505000510058004d900d500c0a43d5070b05c1902e10304090b00b00040c030280e000900c08482003081c210354601a4101e4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 114896951 1250 114895701 114895751
    0x4020405041a010b041509080a030509060f0705010507030c080709051903051212010b0a2114040b060102190c05091b03090303091e0a020103090204020c0f06040c050301060513 77
    0x840400004202d2001c014000d1040d1501c80e030785d0042480241208446500f2113004054040c9c0040c010000020300030030240c00940310050020b414510101d00c0c4080c507030440141510603030745600038441203a4061242041d002400d28020b00b1501d44080054840882071003510b015014500d001828500044070003c05164454142c581551002c0000d1070b041d0851001c0b10000c1214034000201d50384802c1c00c03545000e500e0303210082c0008041e5610140d046030f014082e03140302c4c1c4405c5450b45040f21034840c144104e11034500080c460501e4400240360506d640c850354401c2607100386180c0419030481810b03089600c200c0d000c4040c2e9440e5964440a01c100c280300101490010007444607082c4080081c5104001880032a1010207200900388042d1003105680140358001c100700b140036521a400c220351190025001514000001440c6481d01d8004510240180c015005010070014420170500092601300c00911281d4142000207520101c1e405800340300e80e40d1410480d01c54400b4203900070781c403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 114898201 1250 114896951 114896993
    0x605031002070b011d0106080c07020d03050309010501140a0509040203010908281d040203090f060702010b0108090708060f190908040303030507020d0e101b14060703050408030402040504 82
    0x105190100d40c0001c0e42080608a4405140b0400400e4040080d6a5502c800100c2410601980d01e000d40603141c290018044004003001086000003588850658101d8144245e072001d03900d00e81684860300312081a00640500310b0000385846041e5100c0401c003054030380841d000c0d0804c0e10b8901c0064014818008010055040491300c56804c00c011208140440c0355a50b070100905406074044a4040414440309652024002d200ca940d04240c0e01035984410404115502c0c80b00210846e4a84482200d0400c0180e440d910000b40302d5a0040700f003500070b02c1e40c0d0004d001140c10a0404ca0f224078000345800100d92520000581c01e0380028021904c02200650801001501d81085025035010380016004642040d0101d0b104034400944080b140100fa0b0314042808031400c200f002c06c106040743c1c1c80c2003080c602d0864107403000c208003a00c0940d101d0300760711000410541d40d1900f0460018114420326150108010200d1000400c8030760144d81200c0c00600d41d03441c0d2419001c1c1014401c040d01d41c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 114899451 1250 114898201 114898213
    0x1a0d020d050f0105130c02030301030618050f03040915051003270804140306061005030c0c0f07060e06160f020a12050a0b011a0409090c0e0408120c032404060503 71
    0x1d041144240c59041c0c480903221804070403005c2104105684c03e044208005a00800040000c103017a40d01c01001c108210852421503401da49400e852b100c1c0d8050320110706d400c0080e04120000380c9210f0300211101804040d4626031030400010071055100c4403031001d241e101d01c009078402ea0400200c2e003a1810480c50320030901214200844a0382140c0038400441180c245081c015140004401c1d100d000b00515040064529240440701a00040d150901e0b8140134010700c4450841444107000c0c0100e624014020240340c80001040c0740f801c0381400340510030820881c030445800300490b440e0960040c00400f05a030f05440131480c0c1640617400b0041c0d400007440f42404006010800f24030f81d07805020856220303601d883c0c0d0030910061196211100d001d0400c41081121016040700b41242e0040002056007582e564103035910100444003211b50040001c0c400d080c400c0311620072608410428245421803410704800843e815200c54101a103180075100044a6a202d8000d50043c260180075a21 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 114900701 1250 114899451 114899461
    0x3011b020106060207060c0f020d030323160801080304090c0c0b1513020a0203040e04020d0506070215071d0402090d080406031a0906030303070f2616091a0d020d05 72
    0x1000788a80d0143e040140a100c40c00110a841004039590940c2c00241e000c4200c040b0743d08100c440c0807191011400e254480841e100b001256a941d240901c2c08a0410f22003450f02450702c2e120324032250180b5042c0218000140000480001a9815101c0c042c10006400d0840c0400381c40c19801b003030004045044a00400c1850070301031741030246802c000c0d10784451208a01c84940700b41d00a13140b00ca00107a1047c8030401800c03038051341090f04940041d1510070182c0d5292a81c0342000b41c203c98210240c1c4c4642c01e0943c056542c18010b0364002003528052410400010442705400c40c0c80180511858010401085a50f203162403540030551101e1015030f100d94458003d809010341806030094950844420f60302418440031079440384000a01852841c7d41c2c0100c15160490902c018404124200c4140400b5500e0740081151203042980200381c10f191450030345070703000e00c0c043d203000802055800800c030415511100f09042038000c0d2105403614060b1515100902070f651069401d1414541408 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 114901951 1250 114900701 114900703
    0x1811031b1e090405070c1205071704060509010215070f050306120106080c01020f03070b0103020928020d27060c021609060e07020304030f02130603080a0e010f0c0302061503011b02 79
    0x28001070540c3c05120a98903030a0607100c0c040140000f901c0d6801d00c80100090300d108000410810748a0350078040c19403114080019182c1250300200046800052007001560301084075207400e00d1412002001484d020400509011182c9401001d100000c008240c1c10f035180785031000341114180080000e02e81d15030020742e5802c01803245c6409802002c1c48030148030030120840312125000302c450000c44e403843d070038401ca406c4000c1c00c40c030021a4100c00800b14064429041003a00f507100c02c0542c44480361040c14040b01c0b10783c0c64104070108224a1884400d9100000e40f00306a002900001c10300c1181304240c0c2089003070040510510500c96010490701501d1f4001c005442c8144c02030419595500810b9917a1b204a010140c5048040c0e00c20f44014601f40c614860303004d20803880070418603581d50b91000c0700d410020741c03103010541000610034030396071200400e074008100c0d280402d140f000780d0318040d407035500c040c2c49924101844000346000e0f4409400000c0c218980e401e002500104c10f807802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 114903201 1250 114901951 114901957
    0x31b0b1c0207080c1b03010c080c030405030408030d020307080c040303120e0705180f0a020307050315030118150506011407020d140f07030b010f061e020c0603010f1811031b1e 77
    0x8443e040003081e05c0d15440c24144a031425030285d03515000155151095160059080200200e0301403100700004901d0150500c00382805c00b214400140e1030b4204894042c2004000800f6201000c1e03003030004202103030b84400e200c2c80d1019400d10026402c84045a52414024550040c0c0c1e0080c454858580f407082050424600c1280200d006404680740c0314248005d80c88141c5044001a20910119650950110f8000e1005000a00001e1801d03010340a9007110403a22905641c58182894140c8080f07a80780980e0303921450074600203000c034540c000810282d0140101c043e000d000f1240600c410010023003030203d000d910000c1110030742d00c0c003a1640b550b1070035540001c9031040307a248000540c3c1c4013503145200c141c0300f040c4ca6850010114000071000d1203408a0310b41c0840c401ca4524038466251000214007030034170350348451006814040740b4020385120381d0340b60900c0340c94254042012081a010340b034101c0c070383e103142d0341c65081070780f5000e81640100360321005088820003400303c00e03401d200c0c01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 114904451 1250 114903201 114903223
    0x90603250c02041107020a150504080105010e06010e090403080c0c0a060e0f0d0e010206040f050c150a02010c0203030c1206012d0e010804051005070302040306060f031b0b1c0207080c 80
    0x4244100b01c028200082140903450000790040707500d00c03050040c090380107403030708d030002c0b040c41e010303003020303902d511083c00d640c000e0f448003030111000e60600101d568080305a00c071700c00c015074204c1d240382080d6400905400380100203441e0410041041ca500040c140b18504402c0e07000350f42032052082e001403051316000700c0428149284103090178080e115000d003141d420481c2050b0040c003000c3d42c80d0b0715220106001c01808813118060078442003003030303035034041e56900d80c1d5080107101d0f4640d0610342c0060700b101d44600940096600901c1003040030f1345090200c078a40c542d82c01e240c0d086502d91a0050fa000c107105292042e0074801107068480329003040d0200300c01c0301401d03602c07034904207050001520303482e4094074050040e8010380101d0441c443c25030006900403001e89001071402c0d0f503a445031022282e043d00f00c26030344400440100103100d000741c4a1481096026131a0341e0440c544005030780c291040c010701d4045428504503900c10006241e0564001a4100b0b100a6640465040d40c1d6211410519 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 114905701 1250 114904451 114904459
    0x506071208180c06030a02070b16081f050d060e07030b060f06160b041103030f040914100905101d07080f0c0a0c02030703170a03050912090603250c02 66
    0x21a5071800030200b080c0c1d04004400343c00e01410401c1408842d0780010020504130307400b0824100001d004045a510a13841c042d803a902c1913824900082440c00c0103813892035407140c00301400c181e04840c9521802100e000f1540d0749061841841c041014092940002040b4018400c0010520915103601c80c071a8600720307640c0070050006c0d01003000d203015010599030701e00801c1084c400043c0e6035112107a0082c0c0201c40c003030302e111b5600300041c0c6564000c3d401090500b1011070208205141405907000f840340a10303941989281403400e02400c1c92300e511880c003d2a80300c0010461101c05151150094444d941c04000029503500d40c501301e41000b502c0d0323540010308110008030307918031602c0c0003801003d030524000d04d0040024000c03640045280c1003a41e041c0614940000021100e00081000c030489100b12030300d0307081d0060040d00721030f4003c0c41a101364100566600b00e84503040c00700c070b4041c0e030101d40180d100c3d240ca4914031150b1a0a10503c0980c404030000380310141c2c1c00c40200101d0a100311 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 114906951 1250 114905701 114905717
    0x302010b0108010e010e10030501052d0f0408070804050607060603140a0b0105040906060504050709030b07090302090103061a1210110c0c04020c0a12170604141b0405060712 76
    0x40d00442d01030409200b50b0b000014002c00500066082d0a962038000c028035004100243e04c0380c803400c2c211742e410b507603a0740d12410b01c0b1640c580c0502006004495102e8a842642c0307103240c00c070b40700c400780b02000784010200303480050400300300701c051002d54001d03184c007a020540b28045481e00300e005002e1400180c800c00481c000d03580c5410b00028001c540e0507800140004541d182c1001e10020780141e10003260031985803500852243c881d0702c40c4034820821951440223141ca1400c040c50480b00c09020700c010481c6029052025031200c240c41d0381140e50150001071030301494001c650f02c2c04c280c0c1d40b4081e40444110342194610100003910346050f00002c01c2045540c6a01e032200d0024031030190949030326000000c26142c1d500c1c1960107040000702480581e40640c40540c2e550080030400c40300718000c03600001c001c480c60328501050b03940c001016582040402030a20740380c403c140c00107103044ca941f140b04180140c07803040d840a40b8004c0c48050020380d00c83c055440c10949845a0300d460000140c901 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 114908201 1250 114906951 114906971
    0x12080f0c0c070315060509100905061c0803070c080d090c06031a040902010207030b180706080f13020112020a020705090c04030b040b0a2019020304050312091201020a0c030201 77
    0x5401103850520400700142031492465555021920b9402191264159a000b001a107a100c60303a4041c8169000c040328040e107410b128440003150800740c0481d006900100040304854007201d8900034a40c0c01852040c0c403581d800404030391141e01850300400d034070008940c0c1c011205194101e4000d1510505407100003a466142c114104c6403482c0c500002801180e0401030709042c5075001d2200170f80188180c44542e0f869031038555940f001038a81e0541200708001c1980c44032418403000020340b0141c40c005542c3d00f407058085005075400340100e09068141e41d14032046a005800c0092400082c00d015901c505243c10040d40302c24080c8100d0340660759101c00102040c1804044078241d9a0051103503e580e00d49480c4c6a441e03200c01400000840c2e1794855092158442400c500440110b000548e5607600300f580c1005955000e02104c41c0540d4014170061210b5580810844da941d06180b11a5407168816000038005000100b5400030b070394400680c030f0400759400541d15034054000c0d0000c0c4054412 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 114909451 1250 114908201 114908221
    0x810031e0605060f181b03070c0b01060201090b06040203090a0b0c04060201051b0703050a03020c010f05060f120c061806040603050103030908030a05040b0913061e0509090705190312080f 82
    0x1250113031a44502c528a00c440ca809621028a0700030040128406044c5001c04081401d580140c43c41c0d40829503000b081410090043c495502408040c802442144503e584101080001611203032203140c0110000d0ba010300c0412550400076003007450180d403030410004600c007540c814068440117508000000f918014088140404180b00041c0701d860043c0da030b20704840d075801000b121401c05d50200030855810109002d0240d001c0b074503107000110380c10140200241145111001030003102c1d16054050362440206903a0028103003680d010743e8503080c207112161001c1950307a566a0190020030045601603051340400c1c140c912a40324200100d4858071a15503a0164607000000284d0800060100100c1c0c0701c05440041000340490006c40c41c0300c1c0071201541d240703400508005c0351410403c050490207007994001481c0a0355020715034203001c1c0a10741c85648030700900c0c0c09a4036002c8903000c42c1c120039204c0801940c0000d01c14aa503892041d004020300d100b5280014552001004641c199039 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 114910701 1250 114909451 114909469
    0x4090209060f01110f0106170610090f020405040204030c0303081e0720011e060f03020102030313020105090a1503150501210e0f010501080f03030108030a0810031e060506 75
    0x1400600611450780c4030000c00000c2d4500d204400e0412403280c0e081140c001c401c00550380340d00304110001c03a819080c081c0c1c0010b01e490b03004950000380c0c0024188682900c00e04800000d0f03c00c0c035400402c40320f541c10700101c040c2c482c1e68030903030f045440050000103000f01d80f1270800540c1d1180da03500d2965210f002140301c0c07040051400254141d40400440c1d4451300842c00c40c40120645c4030105c4146003081d040034210b940b9954800b40160181109100c14441486550054099034420480150541d00001e68900006010214007040100014290382c0168281d0728000d100401c8501d00503218030000851995406d080e001003410044050489203021450742c2c15500180e40d50b91590317902046010000b110001140c201c2c907562100c01c08112403d000044244481c400080782551402c841c15292411032109500c060b0014401405032880210481d0000c545c5450300d08030030f44030a08540361801700c03a84003c01c03400458200000d40556110b45044030380c0661800c2080359510824020464 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 114911951 1250 114910701 114910703
    0x12060b01090f092a030207050f0f0a060e070b0c0f12180907030e160305160f1205070f030605011d060f01050f090a0e180705010801061115010603020c0c0409 69
    0x8081000c18003d840580c0e100922845602d4120b0845118101402442c0d04050341007500103900001c6042c00d0010810011141d00005402402c0b60740380081150b0329511543c000805650701c41700094a071003000c10444010f42084040c1075555500054466a986400c0405041e640115800b0a049107580810ba40c28030302e88048000a40c0b04860400c58403c000400400030300d6036030b0000054428041100c0c16801d40000f198580040c21418414640264050070003919080c1d06414000d09485e20300402c116000010340d02051f6a9520b07200741040b242e030700021040418254008103021079500100e040b900364111182c0e4040c10303403140c221811030881d4400c1d081552030b00000b40551140000703105080d15064624201480803000600346202076003e01c0c0800c04840c00d1107600f40e100c0c0340e26401c2040c1c1d54000c0c140c0501e0040060040700c014456041403068003121296520030030310001140d41d03107084082d043c540e140c2c0300c090025007024111041070302c9a10800081c50629204145000f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 114913201 1250 114911951 114911969
    0x1404050a0302060c0a0b0405010c1202130e10080f07050112090201020604023a030206090f0a12050c0d1d0102030418020c190501090510060b070303090302011512060b0109 75
    0x24505540070311541d0344c0b141580c102e0760301c2000142008602246040c5004522a0002003050340c19000000c14100d000400c4014040c410803041428100c3d0308a00d20860308030f007880302000d583d00c0180305841e550a900c515680c0c0034120940342c1d01c80c004140e0b0f00c2030300c0003621148441601c0710306120454070f509d440240564005000300b0003503d8400c1c00d07081134881e0f0344043e00070311405010f00748941c14145145883c800d1206000020550103100307190380a1403990090074141031201f1407036603030030700c00c1d102401c903c1000c80c500017198410003c440d010030441089030302d449081500100480e0300d0692010403001d5480b000a817641c03020003120112154288864108010348075070380d0082d40304000600c000d104214881e59040b00310a00701c441c10303000d400006403050303003410b00b0f6042403070b0303001c050071228980041480100005429607000740e03090b00d80000e5450103868264010f004454800100e98026000041c0110351040d0b0425024480d010610545240340015125a03a00340108151 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 114914451 1250 114913201 114913219
    0x509041a0d11040e01020a0513060315030b07050f0301081606141e070b0108030d05060d080307030903020114010807060909020c07210b0709080c0d050d030b0301110a030507140405 79
    0x80780040c070760300b007028600810004282e40c84014890032a44000080d001043e804142c80990031650802170b801014a81002c0c0404410b10010342e0004c0c505001c0108640401c001003409039100c1c1d016640e0340162200056525615418456a00d07050200708404040350114081910780c4503a403402c1440c04100741d218208000c0281d00000340e401034500b06d5100d0014440d81340410001302078a0b0080440c00041d40c0d403130b0104000b800c2078600c0202032501840e80c901d4680d0000721a02d00f203a6004c115441c00140000c900d1074202c0c050300400384002203d50750f540010a0700a0b020680d1411901ca80e00c170a0f030880ea1f038142c1c441c00c0e40602540030b006034000032001c01400e1090381d102149a8035060b001d5540043c03d03690a511820291111b0000403103243c011711040303c042051521f0a00103c03440b28141e042581c465980d011044442810591640c00d20185520250032030034888072200c5109455544441008008081c11149140010080100b0748088245a02214151280a044400707 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 114915701 1250 114914451 114914453
    0x32a03060d0314070b06150a0207050d02060d1119021914031b0105010906091404060e0708070914011a070b1504020a0201150f060c0204090303110a0509041a0d 70
    0x18050207804240d0a0150b08407108900742d100700020144503110350100d03a8181040d00c03d0015099101c6102c140030201040307080c40c500d400064102c00c40341b0840305014074138410700c0422001c0c060707a070715000c1c100d0034108441031141c82d1401600c2e0304400072006c03120394407030100201e07501c01c2d0b032402060400c0c0740c407168403012684030701031095205e0305441164134000f4000000030314190131581e40000e0380d66070001442401c0a40c02404005c0001d500203205440050700310003401000540000e01859841121400c40ca0043c490341c00103041984c15501c0c455524041c880c0640580c00c804650410404004100f1680107080c91900c919051f2440c1c0c10140c440d80d845d2400710018069030740b030810a4020301e010303a40d40e00040074000226030003c22645007100d20350009016a07040300c0000084004280f202c01d51142800c142c954044401160a0401c0d060590003000444404030740070758000b03003408000c0e400c2801011400d1007030300c04219030b001c054500c90314a1019004141c0c41f6480c1c040f884 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 114916951 1250 114915701 114915709
    0xf0c070b0f0402030c061602030706080c03070c050c04020d0204170d1407020d0209090f0706020102090d11040605090f01030b0f07051204030905060a020a050c0901050d0201080c070206030c032a0306 87
    0x9601c14400b84c100c0d15050302c1a400620590000c050000e01c0e98007002c4090114181030040100401c042d05040341c04e810400d041003c07070b000c01031600c0d0407c018000004107002007003050182c010343c00f400c00c6680742025032854006c0d6015015000c0c1d801000606040f0007407000030303503030381c540455600e000094995038001082544418010fa0f8011007540706007004d0303030700d0710246030107440041c008001c07182030b4000302d0303050002540c00502564410701003a1400e03180c0d120035114103a404038800308100304060018004101c65003110780c02501003c01c1110250024170510b05883c0509103a100d01e554003103c0c085058030440343c06001860034020240c06034a00c4080702d800038881d003010803441c3e4a81000c101d443d0064910711006074003441d00c8070b060100034484c01d402d489041d10003811641c18040840c0d082d0210030402030400c85c4540002d0603480714031055800c3d0650003414141e590404c42ca4402550f04150350314036080c584400600301c490106d0024103401e514151030307141103903903100802c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 114918201 1250 114916951 114916981
    0xb040509071b06111b0109020a0506071401050c0307110604080702270c0a090f08061b0c0604030f030f0203060d12020a05030d020703110d0c06020a090314060f0c070b 73
    0x150328802c0d004540c242c0000c906020b845034031800d202400d9210f00201140c44040d01e104c007610241a403500c503200780075840da0103091007030390000d440c021341d182d0251a081003c1c02501a80140a51809050242ca4a040c0c00110f000ea800d81c2e0f50282c2c038203400c119084c2c58030340c2610004c1920400300161801820714540e0007031044501d010b0617840c850ba012805010307110450b100903d0210000700740d11915000b407080b00c05407000300b0505003503074101100c0b25138408001d0a4460070940390b401c0c0d405581441c0044480b50b021003030a4a800342001d20313001d005000350342c00340c1c1c0219080003108103010810b4800e0360305c9003400500c04100032482d1346600c0760941011a9020840c0240d4101c0008070740100014519100300f4400141e0356102400c0041c429424444c0c04451a000021114851644488210100c54010300d005a54024498041d43c1e414200c0d84004d10140b170319801000d035041c0201c0d0a600c2201c242c1b00500660340c48000d9400703103104400300109910612804141016644401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 114919451 1250 114918201 114918227
    0x140c0d030b011b121404060801030215091806102a05070906030c150207151b020d050a03020f0316030302131703040f0e040b040b1e1905010b04050907 66
    0x89490030f40480101443c070701c51460698030040c100104520380c90b40040c4244107480010151410503080002c000c01c0c1903418440a031166500c0208240c610400e002200c2040d14018890b510404039026200729a25040b510644a883c4504107100f105004602c0762080b05800382840d022661030854460b626803002c02c00383c3d40351140d0070011408600c54032910001e5801030301d194000f41d10b802800403a4516810070032085411005081202c03000d41d21440c8100700607414a50740c0c00710303101140c0700710b0142c480c0c0c043d6006202c0018017092000220b200a86280203600345c4450a8400789510390381e00c10010428020310703402c902d8030046403080d4090024000e50000c1000501e036076800e983c25404648031003007a42d40001800b0000c003642048520f000313050781c044404044c41c15403919a1021002040903000107601c0d8000b549504503a4410909099881c0c1d02081504011004000220780540e212503214902000824801c0142c01a10110303000105103e2940d034030a80100c0da01e48100355 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 114920701 1250 114919451 114919457
    0x30d0e060a030603080a0507110607050604031d041d0f0604050c150903030307020d080906010b0d020c0102070b0a0c030e0a0203070b09030a0c1e140a03080a120f0b01140c0d030b01 79
    0x440440040e2881000301146c1c400d03690703100d41762405414a00c0f101b02d141d0600d1841244100414000244081074444c4d0050b010b00b0076440b4010b2061410010711038002405034030919000d1040204400f07c86001994401030b0122030700c1c0c0702121800c42d5111000d440c0901550301c03581001e4145d18010350b500c10000400e040c07480c1455208404289990030a44510001d40c02c6042010072190f441104141e00c1800440140025407402448108601c00c1d0b00c8891410360b00081c0d8070301541001d404403965541e00011241c40c1e45000203100c0001c151401c103400c00241046a50f8200c600c3c00a5071003c031640040103060410321344813440c82d07980e110411540e01350141c00d0604e0040382a4400d1400201182044074061090700043e603402500355030405021500407041c916150b498070b84695041d0303580040703015a10040f030f00054038201303c2281d0f151092030500000d42101d05031500410310242c4283c0b0703500000d482480d218602400b82c40c0c900c1030035038006c12031400c01d030348a40c1002c0e5031008181 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 114921951 1250 114920701 114920711
    0x1311120619090506041a07050301060e010e01090803070b0105190605030f04050715020f061605070f0201050d090503070210082208090a06050a0905060f070303050a022b0506030d0e060a03 82
    0x83e03141801d014084406135103d0741701140002e030341035030b64410660209880c940307a440d66051a80c0a041e2028104107281000030b0080380b252a40d000b01700b220081d10804c81181c3d1580842e1030603400d501d409010701406100444001644107102550420989000d902c50b5070940c3d641080f124170b222002001600d0900c640a00018018010b12040384660080c1d40501000c04800c5140c1c0e103400800f90515079000d882a4003010542e51200507281004d0744102d01e20b404000b503000403240360151401e59007886140c071105400708000003008140c018426104c3c640e034650150015502c0f19001c4070311200c0c0250398110064242031000301220103500c01c5170003038103008241000c200c541645410120200c1e40000300c105202c0e4200c01c2010040200311040d6260401032a0054010700030700000038203060f100c0c00891214040343d010364000c10803030742d020711159902c0c11800080e4418100d030069014901404988103090104100e4107401054641ea070200801506200d800d0f4000849802056520 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 114923201 1250 114921951 114921953
    0x114090919080d18030906030f0e070f050102010605092707032306090f1c0e03010f091a04020a0e040f060c0e0109060c1505090a0605131112061909 65
    0x1e05007045400d0300484a00307480c0c400044500d000c542d07850f64683c030000e144003d20070000707a0061414098400314580070981d5800200010301400c0360252802440c0503602e008581d0640c002462812140260300900150341d03100240461400c0c240d500302c2c3c504000d641c415020502d0031020751718103040d010444150503540d454441d5103451038840903910348902d070310406090200b0018907400400b480c0240a40c00e564030070f81aa00c1d03011000300c209048054600814460050007980a06000036000348030000c5e07601d0402e001402200300071224030b00038136056070140c400241c42c0b5125a0340906481e01d0b85050003245200c6800042c411100c5450710341d00c5400088040c040c00300b2041e895200ca5200c64501000901101e1013a00248100b029801501c0c010541011203a0945000104009043c2e1a09084c041c01c29264000281040b401d0400340a032110485550664880c000c0d10b4201e84907018204019102e041c0c03003d0b0940750b90025001c18503102043c00314005000c14018006140126 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 114924451 1250 114923201 114923233
    0x60c0102040306050f0a020c0a060b010201090812010303080708010305190804030213061703090a030f020303130b0a02010c0302040806070f031d0601050f010503130807020d0602180102010e010501140909 89
    0x9508102c85150311350041c40300f0b03801c8203502260080c000c03400c15403c1c140304180d204e58407420b62710050071440d100c3c0100d5116134005c3d8803011185030084c80e159646d03402c4001d41401c12400b0703c000c0b400200d840d4002024944210500c9040e40c0e4010040c3c039414203002d20380c1d4207003900e0000c281e83d42c0d4420000040140d8903600036900f13108c0e44490204901d8680401203844000c1075003c400150410099005a40c1e2a078030950142c0f80d0090311802c010a030341c00820314501951a40c55594080900045441600c28000d4001e1001580c000c3c010741e0584041203013a4082c80c4200d0300280d0014010404007401010780352a126082d180000d01c02d080d00c208072082c00551007041800c0d0308114011300c0340e81007211298031039241c00c3c00c00906c1d504000b00c1c2184201a407020180002e000440e42a04540d41d2503142d0825581182d401c0d904d481380880c0f4440c0d180c208004443c00f5628150401030380c0f400c1070103824125150803070000c444004040034081c3c840c0c8010840000b50140d01d45076204040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 114925701 1250 114924451 114924457
    0x4050306070c2f0f0103110d020d110c010c08060f0127030203010e1c05090a031520040f090203040807030c030c050d0806091807140d0204060905041509080d0c200f0d03050c18060c0102 81
    0x3a6100040ee243e01c030280f001c0c04858000d8002c1d40900300e076182c00c03121a40c00843c1c0007114041d440c210305001c900304c2c0904130b0503003241e0002581b5500380303642c16120020000311f000c4503050191380001c00d9607640c1b030240c80780c0c802c000b401904074000d0002040400d80b15030f0700c00d03440c011410b40864040803800d601c0340410943e03030102d821030a02050903c042d4002112a9028003180e210441c80c40c04e00e510b0301d0006000345d40b002030410070000a12010948a4414003505690083c216000c0145a0381d0190080000b00c8400f40510404000a000c0c4070031000b00004a0b40f0883c0030305101d60900d060b4200011420445035000002c00d51200300581745c5115840040840000000b000d0034146048103081c100760313044001c07031401d211450000c03503031050459a003001140000102100c50500948219000301045076060f1102d802046448001044070107902d020102a21900e00040100f40c088039000e80d0300c40000d21090014031100221010329140d9444d00900301410030214950203820790b8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 114926951 1250 114925701 114925717
    0xf030801061b0c0e06011701090b0103050606030420010e0607110f220b01030b03190302010e01090c03080a18080c041104050306070c2f0f0103110d020d11 68
    0x94254401000701651101c400032866200060307000c101c0c21642c80d440d41200f001c4c041d042ea26601d920206140742e0066200724010a8140c0d11029950f03911542c000c0103044ca01e8030940440e0034100014444c2c80c040d4112407040354028564000c9140e00700030303242c02006400316103042c464034080b680c4003603407144054040d5034407030ba990510320000c5c031040c03020f026201003032036008400c9600e5802ca00303501c1c818681c1c01200ca400c400240207a11900482c09860743d00d000075003501400e80c1d0080700180c88146440018040e4000788071010080c80c050307081301c00c00f500c040c1181d4080a024000503403d03800815090740146040a03001c10840882451644035600c80d0b20660701411031040c9600701401404070312a46174009504045c50800482c0d110b1034000c1060b0104402c0080807002c003c4d031141c80d56001c160410260703030300e507110303078005088101002503c610603210f12008426a6110303000c0e6269981c840c00b0881e044c4000000c2c01c4020f5008042c400340d040b611001524501c05980003d82008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 114928057 1106 114926951 114926957
    0x30103050d0305060f0d2603061011010e011401060207050a0605040501030b0114031f090203060d03080a06091107060e0c03060c0a09151e030207050a0204020904090f03 74
    0x400c54040705c15070049030110320505000d1b2071b003510aa0743c507540140c0e0402880311601c1904030b002c22a11198098030411202c0314840c03090250901715200740d4000300302d4001203a00320b401d44000b03410066500300f400e401001726950400c10b00000b0101518283c01301402c8c20001846841103004a034141503c1381529002d5910400d491909000407100b4540c5a06050140003511180c00742d40c0c031b1000000b0700d00401c2c1c01c8814030880b1302a0300001c000305003120199500356503000004042444069a0f1140020880514001c840303400a40310a0107a5901440c50081c04694840d003040c1c241f54005c0703207440c0884c0c40024075181c2111529104640f900611081101e90905c82d800400d00c0d103c8048800d604180c2208800b092510801640070004004540c110201d002d442000b6020354080359030a005070600d0780c002d000c2060f000c1d0010440042540b620316452803040307800c40c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 114748201 114928057 := by
  have h0 := BRFrame.cov_init 114748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 114748201 ≤ n) (h2 : n < 114928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
