-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3253
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:06:55.80273+00:00
-- url     : https://prove2.me/submissions/25890323-bb62-4320-bf50-2e54017f66be

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 584892086 ≤ n < 585071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 584893336 1250 584892086 584892131
    0x6060e0603011e1a0a020105010f03031b030504050d060501150219030f02030d06090c1d1003110f0c2a010909051009060609060207080307030915052703160302090a 72
    0x401c500c1808808402260130358070140428006518090000c19003a03280b120840c180d81e050f80c0c8049101050750304a091046000c81c050342440000e0000041c980d1740c50740c0d00c200080c400e2901054a500d0114807444401d002c4280d001503421800b10507201c0f2001c0610303013120304e402d86460701c0100e1200005030305610030b400d00410982d04000300400c544100d80c12100840001d5504c403d500780d20100f820207010041d12020b030b841188001c06046042c401d401a05000b030f21589101c3c07402d914031102441076400300d15090882e0f04030f011188100401250f03040d060500e840200807050380f400e13000821180140c000c00440795581e074081440d04003084083c001520707403c07034104245515454003030507616140c4100303001480351101c08a030001c004400d441e1500e9140d21003031207843c24403c074092880075001d06a0108041481201c010500c9200090001d856018121940c028000d0a050502c640c00c0ea50580000d65204100010389030681c507294003500942c000a488100c8004005084480 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 584894586 1250 584893336 584893349
    0x7030806120c0d1e03260c040605090402040e090105011706060a05120a0b0106052a0c040b0d0b0a020d060806280b030f0f070f1a070807210306060e0603011e 69
    0x1d48601420146c108000d0740752440c00200004044151180700140c0a0b0b044030040c40391031050008001441c002c202400000000920160901c0e8032100710407000700c021a09102103a44440040160388514540066205580406000c1510703110003c28460801842031500030800c0001c102c240341818004d1442e0154450b84001c05965540001051908a070101c49001212540d4440e030304060030300707140c1004840c0e501034650032408504000081046003001f42e004201c10300042c00042d03814059603c0317000308041c016110f601d8500d0540450707407103421010003980010140200c0d284070140b411401c3e030410803540511080543c0402c0070b040b0125010703802d4820710600c4004c0e003002041c5003c44c01002c004031046640e0320148007418680d030f0701ca401d80e1707601400d400411014400008048050252000e54030380b902c40d0b0343d41c01000c02a480e4000810308511101d07070005516010b440000d20303840c07030000d060704041000a00544010300c2000c2701c071042d000c180c0718034401d20340d802801041c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 584895836 1250 584894586 584894633
    0x20a0f030c030905090f040b150a361a0f061e0c0a0b0f0604140f04050312042402091e03011d0a050c100f030b030109120507030806120c0d 61
    0x60014244040c6c02090714121500c2d004071000840c200d0206410b201d00b060001c0441001e81d280034046030b19203c0d0010601e494411054000001d24400d8a02c02c94020070140005100344005081c0c900040921544034441c0c01017140c40c2c1c0e092341d12001034840c0a01c000c034400b100649900e120101c148110300b101c90817401049058018440000152889182c0300d8541d8a010380d1420b0400040b02d140040c0060341c4007885001c40d042001e00c501003035110744281d0480b4500314581041a2030301000700e0701120104c2c1c805200060a6041c3c00491302d4a6055540950406100d6170000e900c0440106400c02c2e0000700700d610840b00d80c1c09402c80c20451615000e10810352500100498884566600c155414410040b66498900b0304460b91007580e401036480b4400c40409600882c090070314012000e03810340d207c02c2ca0070f0120b034286442c0304045000d6100c440d5900418640600058402050305110341810315001000c45000300c0ca070810b0b13040031280c034418010245404010041d603517510452422 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 584897086 1250 584895836 584895841
    0x302132c010806090307080a0e150a18080619060506030406020c0708030702030a0204092307080d0302030105060f030705120a0c14090a1e08060a0c080601020a0f030c03090509 77
    0x92400d04080320080a4140c00c22680c88500c6107a03100c000380c4203030103d6482001038002140020000d4946800d03549415811014088002046400c00030215541d01c2000079800e8070241d0803d0424190400c550040d1204a10746440c040c2c0325080140360120105030202c2d0b0f12480302e2554001c5018050043c80c182c1c503810207091080080d080480c0e9020b15214000010680709000420b07181041e9008005224407040b603401e01001d400220310884031481102d4000d055903884508600c800348110005000461030030702501d240c818408500380130325104100600094884804480c0c48400035010160780307440b0140d040341e81e84030307003185400602d0903072091086c44003180d041543c80d0542595001e428410768440094617104d4020079070b50104221000308007054108641090b050090301c0c50041d03941d902c2d80c0d0107080c100101c4200c82002d69400541c1b680f19000071045070400400e20090418003610f42c0d40320b030705560608000d070500c00104020b100300352050045d203018013000307001c122090 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 584898336 1250 584897086 584897129
    0x40e0a030f12020d0e0f15090a02010c0c09050403031413080304020d1106030403110706080f3403090c1205031c09080f0901020d051c05090118030914030a1101030213 73
    0x6036812007025205008502116441003042400c5234068201003003e130480b0b114550054030080c1101d1000c90b4218a104030001d845281845610700c294005d8601044072024070b0100034120100600b00480341c03070b20040c401c0106542d801035aa1147d4162424004c0e090b403030400c00280d0081e16159907001100204010805502500030140380c41058103c60110b80c407044d094030825022a441100c5142d031000140720512200b406a6038010203810700c200348464440000101003503020360b540440c0e120b4040004000843c50f407a17004100441840450400b195221500ca204036580c200b5400f00b04501080b81d00034542c04840000d500c2040d80b40c3c1d940303c100036401c0581115080d90301500a42d140c1c2c0403000d01070800ca40d1441c24111881880544031140c42004000190200c801d9650f41c4c0340d0520100c0840b0800348215019846400d2140c2c90105038039034004011050601030b4000c401c45c0070000744840440c074001c2c2c20074200940c50f0711030440c12409a04003540008201d11450700c014a10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 584899586 1250 584898336 584898343
    0x203192a050a0f020c011e0e04060609140603040203120703031812030f05062b1704050a0801090b040b0601020a0606030b0601020d050f0f031f14040e0a030f12020d0e 73
    0xb5400703407500a05005024010f98445540f2041c450118564418000040f2010452507a0312102e90821504154108002c1421501070743c001f0004103400314828815010000c18070000044101c40070b51461815501003500c5081300e00348910f0300f40380441c141c0308040c001c0c5c100468101c50f09162084059103810300482c21145c0c0c000c16404280b0302503242011b881280285441580e02504500c402083c0340003005c0b4061202c200000070000300318448000030004043c0102000f88007e0f095100d501349002c0204045c52680f00940c5689000100030000340300c0b420b416802074022a1240c081e0750341100507801d10003880c0c4010040e5182220110400015843d814000c2d142070b400c562414207503007403c0e64184510600c0d04031000b01030201c0b640d410040c00c000d5600241c052503215411106100046c2d149480f500314040c03000b401c038554180c90400d032080f006060701c0e00b001440171898a0710702410f078030760114442040116008820500804540440b900644071720380070080c400031010020744 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 584900836 1250 584899586 584899597
    0x807030908010902150f1e040f080a2d05010c030603060501060509010206190207170a0e0402070b06040f0e071202030d030204061d0f06030f060f040203192a05 70
    0x11440c081004503840c00144107407480e03240c1c00307007a1400c00150b00103a041a9000b6005420165000b046045800f40e000741b44039041c0012901c009854074206a0304c2004820540c11074500d5a200401c0d00011512003c1030018a0108003260b620010000c0050300343c08210b00c0005e4503c0d800d000c1d0110703030309600d5848034003168002c0008002c66600c85100301ca2070f00c03c0f800c00342d006a018a022071200c02c021003102d428004210b03001231030408107a80381200c905003141084251000418003030b050355005880b4003c818002c480441c070700b4982c0c4c1c0c3c0700c100203103001d85840d000345c2d030351203030b01420241692045200909204c100c640c84d598440380341590426014040340a07001e148038101e480c0d0700a000355802c0d2210754131a640969109182d40382c144140b0203203da0310540743ca0f01c810603511088010750050400d141c00f564507260a400f40500306030074000d5a800b40e403042040001c1c1c011b4010768403188c010440340c0403400745403051b2541c003240c8000042c0c100307060170000c10b614445e401000604 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 584902086 1250 584900836 584900843
    0x120906020412050f0319030510120b19060b0703030c090e0907030c05060a05030105100203070c17010510030c0519080f010c02061008060606030c0706050f24181e040807 74
    0x790921803070003504e9217038014000691140200c220588001038082d40190b40c0c071038034040c45000a180d5484202c014030100300000c1c0c0703001500d841441160449080d1030150510103200030b004003481c003401c41410384207014000e42090354400d503a02d03281d4861a141e038001c00507005005d43d182001e2920540f076440500c1b0480d003d04200400040609181e010f43d208656181c4805055a10740001d10148001210003001140401c100780400500920240005070005141c5400c10400c5500fa00d401c4a00c05815419081d64000081002954004008003a06d030280c5600458001c004800e46581301e55400c24001c2d4000d58212202e200015800b0b4000c2c044598210366035501c0310107051160100f140503042141c0c2000e00092028100031b4003d40d00000040c15040c94003030203455034421200240c811410b001c0307402080c00f0034059044a1a00865519182c0080d5900042c0003d49038510036054a12115140000141035070400036001130483c0c8507004c3c40c0040d207050302d00341d0602c0d480030070100c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 584903336 1250 584902086 584902093
    0x507050406080a080d0c05040e10030b060603041203111b01020c19051b0f060d0605120d080f0603010b1c061103160e0a09140105040e03030603030a12090602041205 72
    0x40c603500000d0001107481d001132a05107821071810b015800342841043d801c0030700104001c0003901614612403540304d0410714610304600350952030030700d08104010308003d01c1024280244000300d80c2a030f142d101c030300300c8505001440b000c01c030300c00140a005050460007125042e40400e1841101900208500001c12003501d860001c0304012078680000004040d11680c4850003100502042c0b11261f60201c078020040040208040e000410381d520000d0200c4800e5100c01042009050000c04d81d0344101d100c10107002c0d055a1402d005104c1040200707142c5040003044040ba07419202944140c3c034a4001602d000c00941e041540110780518550b01121036514106d142c5051a01c11015607029020f4441880c1200081c0d09003160603801e60300382c169110581000c00a071507030447c45610403032600240810001e62500040000b03c40c2955440c80c0c0c160020404c00c807031070343e01000f02e41c4628020708000121980c0207001d100104583d10005001c184002404155400745250000c0c030355104000f03e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 584904586 1250 584903336 584903339
    0x601150804050d03111e070323220302180f010b0405300105270105070e010c0f0515161806110109060218100e01020d0f1701030507050406 61
    0x2194510800c80c1c01410a4001000c003045091003a000507005902080702c0a041c00c84098000c040c2074408140c0d00552040050b1a00806820490b5520a03121114009214100c01480c00c0303170030b1141007503016182103050088004000c801c0f0f08400915009031000100c00b5200003c903800c4501030b210019145010000010007130040d1045400356400506a120800030301e8003000d00441c4101885404c80a60b03090403c0003600074402d6078841c81402da140d4030191281c0c1d464a8516030305401e90f5542d81d06003010400b4058002c4c03c0044001020328004c1143c0f2044d0030986045e40500744010170700e00644406400525480080358003d540111f05224518040c910903100064000002d5400304508503040145038042c1d0860550482188004103000e00561f0320082260b2200008600031911022101c03210305065942d80000c5000b424124488441e80300081d40e00e03845070004100304821949010300c91442405c0000340c2d80000107100c81345586070310301661155510f010301401a03150140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 584905836 1250 584904586 584904629
    0x203100e210306010c0311010b0d03030203070306050618060a0c080a1805041a060309031e1806030103050a0b060d0506040b0f09011523030a06090203120301140d230601 74
    0x440f8010314050311007165010443d5010340d80100b01003103507c49550b81c2c0014139225114420140c1c44184280d07130060750381c5000507026044500d2034119500856040c170208084151440d03078561802401c46010f503c0750070090044505001c691402480c10002045d4a6200381d00400c84d0f1451000c1f420101c806a511082480200c1741c444142c4031002542105c01f01440c01c08000031034020034801c0c00d40e860074502c44600031181c07114022074008550001a903101241c80045001d481d0501181c0391440d5514549a9541c0e0301caa8a01c003400d46080c24010920310b42d1454000c4a01c5a0f001098482e00d00c0c240c1809001200b04803800c6008002c880d0002e40c00c15818418104024104505618528244801c5800b1307030b0914000480224051361011805030b038204000020584560800303d005400ba10615042c1400740d4400441040244014440100c4805180a0030a005d0b5080461074107282008400e5000d600383e640c9814250300740000c1140004a4024140c680b055208203104403443d4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 584907086 1250 584905836 584905903
    0x409020d09170405033f1902070504180302120922020d05103b010e100806072a08190806031b011818090b130b010902070203100e 57
    0x1100070000711400c2080c1c031b086c9000c4210310005110916090341c207002888800201c8941c00342d401101584c02000c00b0409403070513008114411603502d02494441e8107a0703070060366034803041c1d4801100b0500070602c6c00303054503900d0fa09000d50314018403140314840034000e00c0000303602c1407000c81c9a05080400050506a049103807808646030910a25100001062036040e030108404903030026031588148010301c2c016190006029050000f950384660901c05200c400105041d4801101600b1010402000d00d402c8100c0c00000360800d42900c1810002c0307500210212801500100043c0021030740c0c5058003000c4042d03540403125030320b40c24801e03140c01301050ba03503403420040409509402d600f80c0b0801d503c1107000c2007080501450f95480315484100e48190156030003144502603a83d154031070301740006500d003140c000780813050a5042000319200e00c8210501401030f00340454002801c08215202007002c030000c180001030402814a10801c00f9440c1c03040010026a42407400c070981406013000e8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 584908336 1250 584907086 584907133
    0xf03050a0603080f070f02060c0c0112091703040f0218071d130c09090509060403080106030c0c03051605030f0403050114070509090a1d0d081008030409020d0917040503 74
    0x1009090060b080400713441c50b4400e00701101c02044081c4450016240e51003d07107600e106030740151170083c045d64001400368100a036042d84150510b5210004100e8140c0d0703490407500302d4040e00703540c0c0d500da041076941030340381c004020342003048900480507200540340050701130001a9100350b515040407410100300200c000505d40d0044030170043c01d81c0000d0036480808402802c1c1440b503080d603a142104421241d0444400040fa04102c0400c410194030860351400f401c41402c003008940c0210f80b005017207070311042d002401d200001038a60b428103403d90b03c61103281e5001c01180e5460b0780903106409107400c244400c071400c0d82060101e90ba48242c08204511646071541d42c04e0400200e00c04120341c4c0f49014220044c0c0d166601743d2001c1000c0e1080402c1a600060f0005010240e02e180005118000c010815140c02e044e01c101400103070000310444007154058000940c0b50342c0d1101e2448001d00782c1100040019554400703a0100810600c00303070044520450989400d040500074a58106031036 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 584909586 1250 584908336 584908343
    0x4212102040602150429071b0b2a0406030204080f010e120904112701030c0c080c0304050402220f1230020f0f030f030103030f0309060204060f03050a0603 68
    0x403c44c911011051094019070140c00340190410742500c1c40840302c1c03802e040c4100030700c4080c0c5240401145031740003424203121201403c5a01105015034540044500016100d5010000040e4a804a180d40045c3c40205288040d019999031a6110700240c000c3d4040d100d030545900a182ca080380e0700b80c0600c20368041d00704400103868560006180070000c2c4e40503081a50b48141e40f000c0440409611001410941342d209610a9400340c007444920345c0c3c0700d059040d1604140c1020f00014030740742e101010540149d4007009068999108845207802c5005541040d03070010b00c0850341130381d24504540d00010265040b401d100c80725131550054035015190f80640c02000503107010142c00a280d04c0b03800240100d20f4204a06544070118a1071060424040e0040c0180d01c0181010ba80e0340d0240007400d003190000000751314004041c242c00360079010501c005030611032011301034000c86001e03410104145911030300441d9140c1e11504041d101c2c00c18000c42c0b0780042e20704000600805010710994040d81e41 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 584910836 1250 584909586 584909593
    0xa0302061806070c0521120a0c1d010e1c0c090c050f0c0c10080a0b2706190303031406100c020f010e0406230303031e04212102040602 59
    0x240d19a0980d82042d51302c03401c03601c0f803181100401481d244552015200381452614654441c40c109080c54800c50142481160524006460340ca051300045000c0c100070040c1c0701780078046252001600c85c80072000d01e0070b03004001c0104035034000c0d881103100c080003441002c1000d8000e445103071920460310020b0404011400030440c0c4148030b03c0d501e000e0440044080f0442d07152441c1200815450515060b501c80410410b409100704148079024020300030b40d080c2d5050405a03551100c100311005910141e014001100c0042861074035561081c0424009850380f601802c2d0382c0b85002401884400d044a900c209510086040b80c903094150040c85900d03a642d860b04044690204504100d491000c941400410340d0801c1241e212401080002c0800e0116065154228101d918506210501c0c0521039002081000380d00c071800c0b0110a6052f4210101640382d50300d40c41c00504241d0603a922807641d90b03000f0350280213158443d03c5540c087e070000074810540079074400c1d40c10a80c007d07070040e04050380 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 584912086 1250 584910836 584910841
    0x50c07060804020d140a05010f090b0103061808070b091e030901031e060b070b06040b060d090f140102031b032e050a061106011a18030c040e0a0302061806 68
    0x81c4075980694200d80002c00c0e071a42020141e4070b01c03566204039102c08202d80c00c003948540910000784629550104052004d00c14a452035940c1d280403481400010310540d40c80080010640c00544040c40a80d4402040c0f50764020310f08081040c0c00c000c50301d0022512612400c4000565504047c0c3c0d983c0032140021401c10411800540241c6110051081a03900c50115400d080c0800d000b144001d1400100042e505c42c0181044c4581c1c060060000303019a0410501c0c0c946a142d01d821903551107880a400100c00c0050300e801038403149400006010034011074101c2000e040c2c1980214007400190184c8030800c11081044903c501045880d02030709040304804189246021050103882a0080002000740b501d41c80003401c50764890700000d0000303903d4400d2034103440041082c0d40c00352a134000440202891101d000500384144000c22070195407148102c101502c2c10807000c4408400180148840b000400d551075445c6c42d004001d1b00140301c0c410125103808800d00300d0a21540c0a0b130050015607 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 584913336 1250 584912086 584912099
    0xa05010e040b032a010305090318100507060f020405030c0a03200a0314060106120204030c03060221151809030d0c110604060b131e0c0302160602040e07050c07 70
    0x303140e80c0c070718160140502101c21461080182060101071308192109014404410006046840040240c00154003c10410048111101c0c040880b203a00700c5462503c00900001101c40d4010100002c1c510747c2004000d011004e0f00390058801c1d55002c0d0212a00380c10800100311002c0b03080d200140854450a21443d480700c04400300b90141c000c05800c129250b5501d550b40110203603202c0071230301c064016000500559501c25022502904030f008250f0174141140c8074074a500700c40b880000c0a49900249010301d4010f14502003440c0550b0346800855441e101c510204214a00403540c3e1261600104000c3d0488130000300c60f001d803000d0001103040a401d07202c500c0080c0a50381c811814000caa00d28100a08010401648034602c200800f240340710704041480380c460014016515110305000b05112007148015020121074803c0001089011a070b84041d0b00a20880070107002e505003c641c058180701d03170358001300100c038801d2903090015900d000e001c4581c0d0059181014260300181c904001d00d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 584914586 1250 584913336 584913341
    0xa0c0509090102070f06150503070311010315050d060605040507020706050409090303020408100c0206060105090303030a1e0f091101090f030303020717070b09060106090f0b030a020c0601030803040606050a05010e04 94
    0x1072605000514044464840c500d80c0001035a0480741130317440d5840b511b1445076154447c00180b000360010b241d03ca003103076291101c003005808802e04250342c2d10304541c1c405000e410f10100800025004454198190a040f405010316005a5001c2c604082c0410b00c1d051000801e03404844a03581c0d09403c0c41d081c5800e03000503191041099041503024032001c42c1c0a1001d2010b01b03540e079003c0300002102220310700b01a003403860081846040c81010301001c0c2c001d031004002c60754401c002e1440018600581480c64014864407000c00d50300500e407a451500100c529448810031038010602d81d074184203904d0045030200f00e140210464006002c400708002030081e0042d01e0818401c0196980d00003001d864050780d43c0062030b0075101c603c00c2100340680e01105110141c0900058900310303400c1401c0c0710780b1f20764001c00384c41290900c0400100040502c2c6269040e00c239100f00c07040a4804c0d950f568180075105800a44040d0b80d22898242c0000b802d14109000d0700441c0c40c10384a81d801001d40c013081000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 584915836 1250 584914586 584914591
    0x10b120f0d140d0b0607120513090501060516020d0b071d030105010b0702090a020d05042409050616090305031801020f010614060a050c100516021504080c150109050412020a0c0509 79
    0x10454000d010707003400208044002034200010340da503a912109d0b211410381d080381499000c1078800c4c2c5002c0040c4001c0d0b60103421265180141a00400c580300a0300c045103584a03801070103044d40e100501441600c9500200b0182610b0070000504440c14030b40040608981081c440d03419a800100f081c10014145840c1041d0310810120303005046c03191011000b8140c0d2400c407001c8400c3c0030385800a00303a1024103a690500f1740c1942c070b01004040019074070035994840207170042c0b60760020320300c41d48031071841002d401e0050359000003600c3d1076800e1144c0c15032400045c00007260250154408144040605101d820111803102100c6080c1041c01020310100b40d200703000c07184c1004000c100131801c448042082c181c4c0d902030f0110009480c542243c004070700041c0d95501d5021500071110121030300e8013554165401540060201d952442c90030645444e1440c04010414040c0c1120b00000d00c6c4e0740c041d4481841140a41500d46150021080403604c0f60006a8024420f00da04002400300d414841c01d05035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 584917086 1250 584915836 584915839
    0x1201060b31030f05100204120204050a140103260c010608010b0d080315060c010e070905070e09012c04051501062607021009060b130903020717010b120f0d140d0b 71
    0xb80813600258405c41a40d000750009020700308122207080450030f00b44074007507101c0c0000d5810000d16045040c4100c0814042c031000c0c0107100320a20302001c0c41840c00caa00705501c400031429035580244400c040c0070308100e22980b0703191351070900101c5543c140103c0c0b070040706500c07586442c516070b03808000d002142010b40507560040000d0210480e81c0200344136807540b0305895002803185520f8241c445042c1e4030010111000c212505844c80d02580b180401181580c00000d03101511022183e00e0034841c40e04001520f498028910a02050000c007003410f24404c2e01ea103041414503038072030109507000c54520f5425070042102da0b40581200404815054200e8418030540b03c012801603014001d5132510310742600d000d555003201c904a89050b103907060000005400500c4100b1403503c0c069103954942c840d440d20f04992661500742000298003094081c480284075a4681204c500c41d5641c5040d1200340d0312080c480c1410541d0480d01030b0106449102c10320310900d142c2400f0b00c0178480039022100c800c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 584918336 1250 584917086 584917093
    0xd03030e0c100c1506270b04150e061806210d020d11160e100803070b040303051e19020d14100f031e021201060b31030f05 54
    0x1040d030740d840c24039202c981c0d4240e8510314101d11600b40402540c44420014480d00d24195081104000c00702c00901480c1075900e5450260000c0710050010380181924140d2140c82c0401d04404440f00000b071030195202c0309aa10110703550b010905c51a41750314400952000110000582e852401100400700c2205100da0300c048112071003e00c500c0d208030500301201580080c0d10810500390720143c00f94603c01e0441c01803002004c004a002a00441405001c030000c06550009420011200a0200402e01c2e081181e44d20206400d00769060b0005403002c40000e41490701155183e5000c032603404030703118140d1140c01c044d204c4090721407415007a8821030f9a8140c0074401f040803034410380701c0c44c2482c2c03640b90a0082d2501d80b468201e0303418400380e0488000a8069801840460010342d60240552503130490890f0f0740c104c600003c0d14007809090821042d60034000c01145980407000a8014041d0082101c4a9111103141402c50409041c802c05400d40c0b1115040010444117116080f40b64020f1060703 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 584919586 1250 584918336 584918353
    0x201080c03091c0e040b06040f0306270c05040f051b0307020a0203070801050f09160b0304020a050306190605030c091b071205041802040e1612020d060905150d03030e 73
    0x404490700c0301c0e241e503400300d0903a442d0340c442810b160080d504286c90032030b0450315150030064420114a480d000c05030001e80e494611149180242c10b0005400000c21b500300380c175035010728140f03000e00d6031070007070b01d0040741001c01103041a4800e000d00c43c01028100d090251010301e1003042c143d1504000c140708110301c502d0880a001d42c4003805900043c000035400031401e40303040408420304200141c4003900c55030002800380c0700d2140010801041d281c040c082c0d90b9880e210750000805500c900d800060381400b5103000e00200503072081074a8407107640e5060901039555102c04064a56101c02c8070031780c0041d070b004000361407032850160b14015034440e5000d043c105242604c421300c81c1886080400c0100d88001814032698954103141d0107056402e24003076151905011810980cc40042c0c00514090406000c04c1e40c010b005121041420a666008640321624000000c0140407240700780c0d2585031520f40031640d1001e03080140d594103500074080340c0e18081c031036408400600800c2e41c2e04100c0c2c00741204 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 584920836 1250 584919586 584919613
    0x11a0117150d0501060509061804110315070e0a080318060d0e010c020604050609011503020906011119031e09060518100302090306070c11121f1b0305040201080c0309 73
    0xc8011441d405003000050460a00082c000740740d9014103038500c03816140c1c1406271385c4010080c1c0c103640300398040700100310f8081c0c040100780b030000441240b14503103d924040200d03c0e540a2004140c54408840030740f90700b40da98001c540c5a200e0081d120001150f400c61100543c2050780060103e40d00c8607600003007907841944140c2c00c44d01c3e50f000000050300050b0901007485030400140f178110200c00001c200d0350741a02c401c00c0d900009488020300550b00c060018180340e000f0036010303085082d00410b4528402c6540c5001c41215002107046021800144515130340c0d01518441d101c0b91030490b00e460340031600700f89060f91240c00c480c01900000fa0500522400b0340c695110b543d1141c482c548001d42c50b12031031000c1500b8018000c041400f00304144103070001040c465070741080002030565410700d042d5003103401103041642c1c81c078500300740100107014602d05240590120385c0050310502c00ba0840060b05070120140e031420b0302c7c003a0010f503204001c00c050620349801150000c000500700c0d81464402003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 584922086 1250 584920836 584920849
    0x209030705120129090103030c05010b0301060f060f020303091e2505092505030601090305070305030a020708070b1c0605030a060b030118020112050403210e011a011715 74
    0x204960751280c2903035198044809130380380010369038650030151082e020089820804144405800c104041ca00310b0240a400e601001e06008003800904c40307152112240240300038240315000000d06030350302e104a41403003c0180c1c0d005012002c0600203895500304480010791114441c01d005014054015200546c0e8408190b40e4103450f920490b141071803d01085074100004011801042c3c10941032620030074000b409010207515400d209880780c45a00c0100da58501c6604010a107116420703002c401e014000000e8500040e00d42c2c210b5003440c1d00d8560894881d1500e01c0360410b5400203001052111174000001c421180103002d0006200f5543d800103442c0045000081d941195119540c1c142ca0801780074800030345000c0031140c80c4904940c0d0008003150701c07807020700071500d581c0e0020a007094400d401288208500c90303c000603441041524100410f0f1696200c4035561030619009640403115840d0031903484141c6400c1d0030341a0708140e0aa098a00074800ca80d049500300d800300c40c5940300c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 584923336 1250 584922086 584922109
    0x906030f0c13091a041b0c0c08070806090105070936110a030606140909090726100501030314031905090708010b030705240c061321050d0209030705 65
    0x5800c04140c0c013954115903410485400d01d624021401c00d940c0c005040c1c00e0f5800c2d140c4034507252800559a07445420001c0e0304c01499000301c0d8940c02410304c009a1103100040080c01100303014020012a2240d81c81543d00051901c90042610500c8072280744031440c141860080c0c04088004c11030b52065036204000700c40190341100800c1d000030520701c0ea61681482400d0140815060403160a00c62078031181030750050f1910f03a413040d005240001c1081314103000c1c4500030a0050316100b1540003100d240348243c0c1c140540a011032145801e010b020b00300750302400741240e402d61558511401450b096041581c0010443c5808689401c1002440904c40c4070305803213900f00001800c4070300c0c00c0c510303010700b17440301b40d07803414429440004244480e540d0841c100340001c40615405070030785240e0541d0401030290050700c24043c081d000401c0b62000520154081032449002c0c6a80702e40380c03290ba8900c040e01035401d600000749003072100340041c2c800c43d4020500d5900003011602401d54403c0022590b40d1403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 584924586 1250 584923336 584923349
    0x10020415080a0c0e060904023f0105010f05030402120703050d022104090b03210711040507170907030b0c07030f1e0503041a09010c080703020906030f0c13 68
    0x50420401a40000c40e079401c030805a00038000c40c2200c20300140403280c1c3d59005031007003100041c02d6401d56220b40c11102580307400074801d80340d520b0350000510307902c080700b04040500d030f050102c1c46100071103c1c1c001c5050710016114694651007594003110260001441240c10200c0d40001c02e00300c131810484080154843c00c02402d0000070034800a04000302740000d810240e4001004006030120320064800b901c40380140001c1520f072103000a40307041c50b500c0a24180c0102c411441c007440c0341d204000c0c401c150107a000390310030f940c07010103010072a0801c0b102c04000490048051b04406580c820468009030301c1d1045400140c0c0380d031200c1d00b5603842610842c04107a00000ca0108043e00600c0c01c08980d900e9043c0400810494038403000c100038075080020801038004002420010480b00e06504004090605207981c41c003415054000d2000e00490300100355213000203112944640225250031201424150031038464000710102d071480504454480c801c148451000d062030111400000d001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 584925836 1250 584924586 584924609
    0xc0302100201060e06061e030a090c0e160c080408030f1b01091a190e01020a0801091a0402070203010b100518030705090f131e0203100b0306010501050705100204 71
    0x55481000040454044030318103690510408000140400e200281c0c413140541d4070554811444140c040700f40b41c2e074501c9040c070a4000c03080c0103c00111f41e10502c2e146204402c440100d603100e03800a0100c1c10111000005602d091404000080c4a82032031012540300c0c85425007843d850f00a0a405c54004281c0d0704001040401c020058440002031243c00f00b14144c001c02401e102e1b80c681510b40d00d00d00042c449000e003181c01150600d41005045c9100a45808003040720050300e03010035000c2e501c410500000154408004030301030342c2d503124400b103011a200504503848503003000d12019402014099905568540300ca1005488000d400305c0c45140e01d69481c4c1d601c645202c3e4070514041482800341c002c4d8403c0c0d030240066141e14051907003082c1c1c1c104c10b00c41c1c5917960021030300c0b40c82c26180e00209039101c008070303811443c00032840381516203108031309440031401850f16003021107181101d69075041c0d10890040250b54010001415850300803001e17501c1806000200344181d9209502184a661 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 584927086 1250 584925836 584925839
    0x9030414190512031305062a0a0c0609150306050f0d0501060308030a14071e110a050a03110d08040809100210090b04120c020d0b130204060803030a0b1002070e040311010203040c 78
    0x30b17580c00102c1c09841300b1201c3c40d05160700000c59120069041100b8070091800d1030a8158820f400c00c09d0000d61503101880d0341240f61a440010032400044c4517104d40340f0380c800081c1c0c1e8414000d01070042900c0f00501000e01c10004e100030010303034041001080d1019540c1e048080046072021000f5840703600f102d0004100001c1c0c818455120113801032050040180508801080030100300c0e0240981c5000c0c6080d0030000101d0b41110700f882030900b001882442a0800d01d403c060700030040c80a5490984141c582100c44107038280c0d000c03581200c00609099080140103628500462100315006280c030445640b400c2440c1c8920440ba030242d401d6449000b440104800c22039804441c0000140d1072a10342044842d0381d01090447c28800401450100b0f10000120441210f2013900d00058008006214041e51624510745a9006503070019100d4200f000c403861038207150910441322150f60f8000c0900a181c1042103420701d601400803410001b11180005280209002541c0039900070100040e909 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 584928336 1250 584927086 584927107
    0x103240302030f2a060918090606030106180203151002010e0106210b040501020c15010806010803030705030c0f0912030a092403050402360903041419051203 69
    0x2880469070300c0d04644c010031442079100340d02e5100001104480041d1850500d68100003800b5006111a482c2c1203822601180c0c034005070324000341d0081d4071040603103a080d1100010716099074900c0c000c2080ca251002404814180740794002c6511103030354200c6c0ea4195000c000000c01c007107614000d03900181e44542c042c1040320820f104070300c0140581441c0c41d46a82da0405c0d03203201c8590b0400041c09541c050310000f4203100c0c003901103800000114042c0c501c03c030001c03c9071069407030080c041e103c0b040c4250f40020400150005c122401032400303840d00e85c00e559500ca110707000c41d4414003454960040600c0900700c0e980300c0200c1444030b001324201450322061007400c014820f0030075900042c01a5004108a40344500c0303c0d0100a44120740e1a010035140e80d5070000c1981da0446403414208840328003040207040c00d00d229800c0c010041400741f00c0150302c5a401c803e030385e8000d5014928078800048034030600c0b898004c440010402e03081c081c4021040e507072400503090007410003030051550000103485046 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 584929586 1250 584928336 584928343
    0xa081906060b0a0905040c0c0b010b0c070f1d0702070810060603050708010311060c210703020f030a09060f1115101a09060a140a05073e010324030203 66
    0x1d4019401110f05195030704038001d029812070301c580b80c013440e5102c00024103548248040f0201c6500141c0070380700355a4030381c550182940300400b940701c28029035401041911000d20908200d460240100c5054014140c000245680292a010551089850001c0d100b941480415200341c1c40e42d43c001070107481c3c01c0e03001d020740d00020420000c00c03800400500000d443e001c5601c92011054034440d49038800500f0007031034800c480852103200e9100c90030350105201084010541c161080c0d00307a81e0b01c00700c0c0c03a0a00303580740240c0c00780d4408141200c1003442a1440b400e110b0345865001c0c44d2a00f81c4030300c0078005600300640c3d10800e51680020100b000b0750404865001001051508078024075010400305600c0180100340425105000000b410b40f0818450340c001c40f1131110956140d69100108080a4225801140100c4151001c24009801c0f280042d600310492401240320a01039214640e070b0345d940b4a1542500c3d4181981c0b902d420044000380208004241d40340d4030341c01061800c50041615 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 584930836 1250 584929586 584929589
    0xb13050f06040f0e060703050a06090501090b03070503032d04030602130519030f0b100b0a02150c270301020c07030311060c130608070c12020102130e090c0f0a08190606 74
    0x482801c1621810a0484c005240d80d4412194940040c051b1100030361800544843c3d4000c10071a82020700104030a902640f2102610f10100c0859a0a613910000d05440b030041e46101038100b0b2608446803031041160905000d940015458286415142d03a03070001207802040340b0f00c070342d4110381c0c100740541d00340720045660304003070b000d00c07980000e10396a1582d0340c050440c0e20042010b840080402c00f84403610b03030504041c1808820a5847c0c01c1d00b548001c0d43d410b01c803c0440d585101d0310740416580b1122000300da6400400040200160900d0340202c0d00071407058000c2609594200501c200b480014054400654440e03502c0810001c002070045151030703c094200380925004014104801d075126044104654460500050300d0790390f9a81500c0480303101e500641030880100085000079819402810303039030300ca0140168015159100c0c12810b10044803100d0041e03002240803041d514107440c5940d21844000c0800106986900c600d5044c2502102d60303015260304c02c2440010000309014110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 584932086 1250 584930836 584930861
    0x80f07020901030f0c17030d0e0f1e19020616020d0803100311030102031501080c0904060603020405030105101818083f0f0403020a0c150306090203010e01030201030b13050f0604 78
    0x260b44082c2c0c6c9001602c038400c1e500002956503858511418101c0140714031080c08281d030090f03841d54500444403205051040440c00c13101c1c0150080c041c0a1000003000e0b940103600a42014280600300a03900c80291180e0000d9920940d03c41c205000224a01300542c4030f40107101e90072888134130318502801441c4807082a04d200f40d0051040000d2680d00140700d1803403a01c01d10381540c060b110b903c4804a00d1045078100c503001800c084012402e1a050b4005008480003036008214981e50030209050586490094500e2107050070a0201c815440da0894a020410520743c8200d018569580840944c02468507107901404020503c40e20401c0640344c0d4845135000d10341c00d20a500b0b10440010f810700c0103181e4802081d00f81c0c00b080506100308032400c1c90aa002d8407090180392a001944640c0a003401100d002130b003081c0c0f002c20301141c80d0080d2412541a00a00b045036401c0d980150094680d0303400e81c0d500500c00304007401c070010041c020940603c41c4008090000c1c200710b070070311096901011194 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 584933336 1250 584932086 584932109
    0x5031905240102070b090d2108070f0c020307090c020c031b0405011d04032604050c0f06040305060a0f0e06010f0303090b03040308160e03010c080a051b0304080f07020901030f0c 78
    0x400030080c4801c00c0300c1c90004105c40d12554440d59280c0342039252082081c03c0e0080d00010071446c2351982003400c15014044a4895404441080c0c004440203403908038002e4050b0000b07181085034943c1c68205848007100c50040d40c00ea04c0499000c2490410001c50310b0f030715402503560140b010b0500344540750150144841e1900d6140900c50450b41c1c002002c0c00040c01c100050803170300440c0b400b65031103030b0204000c041c1c401035908050505540e2400d040f0440e501c11078001038042c4070752070034000f11401c03a98000050141982c44161220042c110248980840e945030355162050540c1404401d000e003c9641c0080626401c6080044c62080d40360450140c0d4042002448046504a41d120394040e40061000e81c01f00308064007110403a5845000540640c2040c83e40d013065504100090b01c00c4207148010001941c815080140008005185c0402c0303040c03c00124020071081001849002200d007840e514140c02c0354042021520264415501d01c404285941d00300090707440400028110044507 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 584934586 1250 584933336 584933339
    0xa030f18030207030f03020a0209010803030f0606030925240806041107060b150f040608090615100302043c060503060f150a170a1104060503190524010207 68
    0x2e5503801e00380c0405040803010080d4681091300c20044d80b00000e41c050702074401ca59591800c81d503285c100ba5001d044050720403000640c141402c1d02940e1141100000900c070080c1d104500e40b04080c1039100785060746400020110720068801a02c401c0d01110304070095504412500003480020003403d00e07441142408503488580c0c0340d00c0c2c1030b5203907203801c54000200c0a5062000400c5601048072001101c00d01107451a00850003002a004462032500c600680d562603810681e220032003200d040c900540c0000d500e00d018207100e444e421209985040061900e52514154492509008005e80828140d5030011211142c0802d05401628040e070b441d024603414110003401c540001821107015902d24440d10425554218440e94444031503c5065a10f038a01c3c1c00041018407841c54407468600207001040c07803050a84101100003a032031084c641081c0c1010000c0702c7e6a44090b00d0340032509080d8403898460802840340380d001d0700e00c092080300740590702100090580c448000840c150b40282c0c0c0c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 584935836 1250 584934586 584934593
    0x702070e04030e030a0c090c020c0105090a0608041e120e090f18011e05010614072105041e09060807080a150e031308070906030f0204050a110a030f18 66
    0x310250825410706000860300d400300003180c9041d01e00d00d80501543c1c0040e00001e5841665442546010f503a9400c2c1c82e030b0717001400c0054580384121418a60002c402d404104400c1f0f109030070302500a2f100c1c0c0464807142806243d8481d400320098800e985003407940c0059020580c100c8510389402000740d4204645181c40107010030908402000c4840380d1f072484c0c0d400c1002610a40c0811380f400349113100300200303009075664000205000d01504c0045502c42c621034000d48065002d85000d0355001c61402c0460806019224481c007a500d041424401c00340030200d860801c00c51000c1011704030889104040b4984400102564244e038062020f9030860b43c0d0a22007040c000c1540c0e44000d8009464032003044c01c02c10001c0040c080861200032a0002203590b400d140c4151403000211415442121180d54071489140101c1d08039100003002591440c40000c01410143c014540c000320071400064050002842500c15a0201c546d02001903504e00c9228001002c51107035554403554040b08038402c0400760f8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 584937086 1250 584935836 584935859
    0x70609091802091008010c050309010f02071e0206130b0d1b0f0c0c080f07030501060b180108040f020312070303050f090307020112062114011422051506010206070207 73
    0xc0010f405004200000f503c3e041c940700301c0000528200d4000c2011580300c0030014200e030001c1d20500015401c2108002c0111a68001d50380031300e0b00801700414840104e00103070489000710304101e820031428003d09104074409218400180341d02c2c081c0c03135902c501c02d09800040b2080300c0c140c0f0b0b80703803142c030000040c400341d03c40200f00e100801030400803e0003845060850b252920b030f61082c5998132070108050404140819082d04486c400c00007445030980300c91071412540211000400741c07041e1110406182c0d840f4400c040e401a000e14144c245042c40e0b5000b0030704012912041455a41000801808040c0c3c948140c5600226002c50298203007818890700c0d840340701c0c810b40641081040029110380c0d0070035511213801811a68080d040b03c0d070441e44600c40080303011006a60203000600300884d2800c040c018100d0f1004401013400d8981c0e607000c42007101e00000c0100b2001c2e1200a000a0b00291080084103901d141c0c41c40c0c44021031400400091902e080100325104540001000b00f01100154 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 584938336 1250 584937086 584937131
    0xd050903100603211b0606030b0c0c030d051801090c06180305070302060f0d0509070f1520071e0e18120a03110a08010311011b201207060909 62
    0x4402d8041e5044c92a80c101c030b904991080e03507150220031304c64403420020540c0c4082c0c1140c0c441c50391400507a40d2401722520b01c4c0074500200c82daa420802042d0401d850b0380d4003035039202c60b00d903001485841840d168030b4211103030000201c42c01004c050082c401207401c014032000480e03060145104c018159958070380ca440381c03840700a026603008618180301d103075440181e481c00800440200801d181040845a5400141c482c0785907044107054041203290745620240d040c140d0303030b8840485403401c0030301c064121501508000c1c6e840c0217601020840803c200005444903013034407460502c02e0304210220f000d0100c00340c041101140e18a01d002d81c1204081190005520190900c82e295055207600740e01410300a07405141000700040c0c810060b03a0001c4290703040e00e019141c1d04240343d03014070046d150110910405c0c141895244c26010024100144501012108104050140c40c4110202d02c54840210b240c841c1d5400c0a48203016040c1d001c002c1d1001400f81900a00500035202060700c98170313004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 584939586 1250 584938336 584938373
    0x705031f0b0609030a0c0e0a09021011030d0c020c04060801051b030901110c0d0f141e04050a170c032107031e050909010806040515070c050d050903100603 68
    0x1c0d145001d509a461034261140280b0140c1924491490b51909003411565409075002104104010a00104242c4540000994040d1210604801986043d2400b500f050306460f183c0c401000384a0000c0e540d801841000d11a0340c00a102c0e2480b00c10030003081e69802e40002000d80e15100400c502c2c0f501d042e0b0142d01c0351640b502c00350742d6a00c503500800d000d09803c00300c0440c940400610303200444000245490001c00c40d60f6140c03507400030304104840340ca800c4088202c0c103407010b01040241c412154540640c2c400621540e601e802d42c0c49004c84c0b45201c065014215294156418612160007401204500a021406407104807040141c500c5c2d0b80d030707128840307400001d0003094080415008080408c0000a0604106c3c2d80070804c88000341b282d400241085d000e0390034007000158140c030000b5038900690340300300504220f9003044640722891030002c3c9024104203881c1e6080c00858014000b00403000055614035a031b46146201380341c5041000c0f048000007615112040011840649504044450 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 584940836 1250 584939586 584939591
    0x1006031d0142060507030212190318030e1002011b0c0c0b13032a0e10060c080306011b08030c070b060f010e04051e0a020d0b090c070201030c0c06020310080705031f 72
    0x7801c00701d10306600c0c420441500d0a000440d510f10b030109d180c0414840d8455502403040c0d460000040409884000c401408201c07007001500c0d075880c103101e4900c4040890301c000981e2502000c0813082c0d100742c5107600070114282d0300c04e15041c003108000000c05408170b410a84d1802d14907100000a5402c03a12026045000e02e200d1440c800c0d882020082c00302c131405040165040d20307501840d402140a0360400003186087d04c0c0024058010700c0e060b0311040e004079070582036a840d04015a0a055030203103a01040650110303520011707521601440c02071a5101c090b0792240401c0c60b03d440034030301c05020540700e01d1214500b4107542c0e911802c0d03460228800e980208094981c51101c5100014050142d50304107684030401c6045032181c1d0240050b940142e40c107001c504950001d1254400c41a100800e81d101d0811070640594000d42000622289600d000303d020426915104101e800030b030741d10140400d94140c02c014203101002004040c11045016001301071041c4404c1038882d0413034414200c4180c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 584942086 1250 584940836 584940847
    0x6031e06040f050f0709050f15090307030f03020606040f18141929060a030b0606040e040f05010608030c0a060f020c2b081006031d01420605 62
    0x444a8100c14482e01555005002c141031a10004a41102c2200c03ca0300180c0681d100061a1030019069080402c0240540345681010801c400c2a540a4414150140310752540000020440104200c0b0f95000340c2c060f00c51802d0484c01c1005559840300c101e0201410002e09054032001c21464010155018050300301c81c1040c886820309007011100440c034005101603003034081c4400100d038034100305c144404120001c1d1340d03051941c030115019508140c000c11341040c10301c0010881d0040c103401c010001c01c0743c0e052954842510021090072a0202e80481d680350700e807000c002c001d00a07803001c1c22280300518207100038007140998903042048060015601c500c540c44021101354100c95811444a0036907141060300070703040c0503640c82c4c0300c4c03000140c1a480c0d030b04c888601e209041080c0503003039410004802130326245040b0080d0030610000100b894520022642108091250003501c100007445000016030020075004030320701107240b00201c5a448007003030800001c400d24800c1039420301e040c056141c0c0b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 584943336 1250 584942086 584942089
    0xf0f0a0806040c091214061e0907080d0c06020c1219020606030d0302280302040303021509030a050f13080714011b1209030614060a060c0c0302040b13090c1406031e06 73
    0x41121044004417801180140580c8c2806562000444a9000810b404a440c4c0c150b905654040314441d10300d007a00500385004c0024818441d00c80003900603000541040107500885040c2020b13101030302c548440c0017516168402c1c68a103034482e905c6143c0007500c441e20b051000b003030b00c0b04020034000040581c0012410341c0b1015460901089442444114a581c0c0301b04c00050000c0d407050000340c016114240140c620403e040c00f180b03201c1c104c444051070510b0b00e900c40544003a00300086658000d40144100c0322146c0a0304805c0c001080840020a1174510300300c0d07002d140001d0541064100240302d201440e00c2d4203d130340e425000c160311034104010942c920500f110764440c141c10042a0504140742459462032021010780101030465100e540e20740d84403070030f1300c43e80312207000109003188681d002c10141c60150b00c080305601002e400c6480720f039881d01c2c01d802100c91a00c4e00303c1d1003100c409414042c0c82d00041178050081ca00351078962031410042d45a80c04018503d5015030009401c2002414a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 584944586 1250 584943336 584943353
    0x150c03040806010306020c010b1002070927060b010816200c060d0b01140c100c110d23090a0909050319080403081b0901140f0f0a0806040c0912 63
    0x2041901c0c16160315507160300c1d00001030b5100350ba14607125030030711490321030714034000c007180703044514640040130454507040307115000e00510b403a28140101d05654211841c3c41c90f03000614041e11407030700000c00030001e40c00501891005019266204003000070041d10036008200c100305a98501110203680140303944040c81c0c580c503825040c0d04400c02281d401e10010a41e002403400301002d0f2100740d680c0184202000c5035006051440c0200da000071007180d80c1000c036520290b018681c074079040c40c0c00e001c002d44d101d1400500d002d40c4400201185106000c0540c000031002c00c440c121040a40b030308064500040810f13031680600056907917180c4805040250030022107030449a80144080381000c10304000d02a9003040310203a0104d03001500041001503031020f80641c010081c506941040d0703d510045507004842d054288040310100b1020030401900d0028144d15102020710759504d48100d00020300030007001d4001c5005a082c4900030200b56001480001a2107244011a81400305400d0043c003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 584945836 1250 584944586 584944589
    0x30709020f19111507080a020306010c02210c090606041806120b0610020a2a12060c021b0904020f04090b0408250f0b0702030c0303090304030309050906150c0304 71
    0x1d070340079030b18082c8203081c3d003241e080780914a034030043c1c448a07900114104181c060885074003000418545c00510107580c2c0e603020310f0308500306141000c0f0301d80056000c144080e411a400300c0a00c02d501403800083c241c03c010481305603106a0340e0709601d090050120f45a40a14060810b240350402d241010010f480d600200051024400d036400d00c1420341071a299035107064401502404d90130140f4031442d0300000b4800483c03544000f80e40b01c10360301c100140207400140c580219528801007000644d40303907007818012080e8056440050417a0200307102a181481c8400480a1031407003c40a03c480d564022205038000d070103441907007400e08450000b80040034400d0004115000710300521007801113910140040c0c52103c10300b5401c69049040d40e400d00701c402c0340d00404400202032954006003200300c2654001c0720740c2c0100c030300340880040c00a0843d0170469004181ea8070225003081819445500000108002e641140c40c60600302d0100c0d83c4a048030309524078040700003070b070309074020800c004580 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 584947086 1250 584945836 584945857
    0x241a060a140f0a0e180a021c110c010608070303051903020708160203060105040e030306060f0c030a0c121e030c05090a14180906130f02040501240905030709020f 71
    0x340e90307410744482d095240d000481007a000038841e0300b4803542410300301080403107521301d0b8100c0c1d0a42c1e611120007102070f40c4140c000d1945542402880c1107001b000780a000c0d0080251858203869000074040282129070380d0307200030b070542c0c00340c0820008290030100329460f4405600c1e40380d03ca9420301c44198042d10683c00000c200050003c0c4010104011002c00b40c5042d10031426174a0590b610310400060701ca40140d0000c1d503030410004a035051500600070400d120142c2a407504001540b55181e065400404c01000810341da06101c01c101302000582d0822000d0a0070415040b04002c134008141180f400e000c075080c99a64100382a059014038142c50b4003030401040a00c40343d803540c11580f084803440c020709000e54002c509007500301001f1a80a403140c96004014800c0c1d80d00c42285880c90244000103859031070340c41c20740f440541c41c1d0380202d40c0a0201c001c124080b02d0000b14409016510b245000400c00200d18014091980c020070400110707a040c2c40d01586601c04c031030b06035031244229000384 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 584948336 1250 584947086 584947127
    0xc09011d04060b1b0f010605010207051e1206010e01061d0103090201090807170f010b060304121404031406160e0d1403030115110105010b0a080901021204241a060a 72
    0x82c13150040b2082504c15180e22a4240c4030b040c1802c07504c00342a6107080c0119405600009000d114509000e90b54900000311184004c106803102c0011030054001306482c022242c010340010320001500075100341c01402140303408181070382c51040c2084880706149401d810107460700861029680301c0c141c81c10241800d50203480010f980d810026003e4000c030441c1e0f6410740204005a81408e1040c07040801c455006020140755a449588410404075006641414042d150a81c2503a01d00000044c0001d0351040080c3c1c420002450380e03031442d0200080810f6816205603121120700383d840082c0a00249042c0c41d90700d4186142d1400c00752844002e10700081ca8800131000080841407031020b104a4110707074035401e0000000c5010942600c00c2401a15100b950400a0440c0580f08400056004010100050400314140c0c040d40e204c031340c1070b6401e032a000303400e003680c488200701c803544039441c5001cac1c0004019664034007012024942044608511852001c203e43d10700902943c4052600310009040c3d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 584949586 1250 584948336 584948347
    0x902010c0b0a06081e0a03052a0303060f060309120306040e0f071a130608060103020408030a080114300316030807140c101a0a0609030b0c09011d04060b 67
    0x42000030481840384c03407014032402440a480420000001562101e030320064540038070647c9050340c0c941d00c04101108017020700c10541c004104090b000d034910008040203150789040440c00c110106822401a45c842c410030014050050000544a07403001001207005450740e9500300000c00501f24000b2140503030185080c8008451000320f082010b0f00c181d001c0500d840c1c04407a071142014081e940740b80380340b454003c8003072082c20701503800a513100300e051401518007034441060906540013642c562010409440041c06001c619000e0015481020b4682544640100900320f0b0180101000700b0b40d601c071011428541040d0a004a920382c0490039491005040c603440c4c010540d0100301c03038140c0000d02480300819501e003007108903240041003a0041241000d11040480106800580e5414402802c0c0d0900101d8a4403445080100b032503442d409056440c5040122101c2c80040191501c0e01e400c01100460f681c12869400103042e0300491a10003404046c0860000c101a0b081001c0311a0701140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 584950836 1250 584949586 584949601
    0x5030c041a120a1214122a090405011a0f0f0702121b0402190818061623070f05150a23010b1902070f0f03031e120902010c0b 55
    0x14010055880b03040550130108000b20304603006400541e1400c000c40c010054110761040b0f8510f41c0e60480c941c010503006d00c20001002c17102a640081c8610313181100810046a14940b81c440c4600402210404010f0410290b600300d0107845400d8075010101781c049034500614a03d071050300c0400741d0242010a0f4401c42400ca00d81c0c0e19100195210008140200b43c0428140740c004d03a002c0c5103500d071150804041c3c90318240c40040008011004100c01203405400d0108100040c600ae42203102c0300d0012480c6814005180000807140030f60f10124440103070180609070002c43d400c05030042c170a282841c64918019041035140b9003110202c2c00d0500034000b42d06410340c031089120101000c0c5540d038104020034010040800d02c542010500f040c088800c003005114040d00e27405000f8030550340c80d140c5072910314503022004e0704107041c031031400c002c148200b50300442d89805011401d517015036410111500100b00f132040310700e4950348a8403400180704590290030171105150703100540402c5490042c6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 584952086 1250 584950836 584950843
    0xf030d0e03220510090b120c0d050106030b0102070e1e0c1c060509220204020f120c220806070c020f1305060906040c0206130c0f03080301060207050a05030c041a12 72
    0x20540300d0f601a0104c104590b002d50303d580100d444041000d420b01e89502c600007841100200940d0480c1c0041160619a008030311409000e0301103600c0001c0c0e0282030200081c9005d00c0380d0480380d0840380510a00c40581810501c442004800308404040ca54440300c01c0c1805d405110780b000d069407c84820b048071500c054001009460098411b5181da58a004c00d18890012014100c0c0d000c0c0824000c0d500503080c82d80007403841150900305103140540700e403d42540064212110b9443c1e850201e00902001003808a80c0c1c20038000644082e40c10f420950416141c0300007411900500005a202a0841d214034507040e01d03c3d60020300410140d40290f403040050320046441c41e100d02c40800005201713141910607001c03c00c9040d402407246a0350070b05c000108069516040d80c4a640180c1c000885001e040501c1014510031146d168407545030101c00380c1390101c00e42041c1c0c410030340400d060000b5140056540c8031248211000320307051170202c1401007181070300428190002580d1140680c3c0301c0c00017 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 584953336 1250 584952086 584952089
    0x3130e07080c0f030f04140d08010510020304031a06041401090203100b0c071a0c010207150608070b07120e1005070b010504090b0621060a0903020f0f030d0e0322 71
    0x1a15001001d0307440502d048401d10455000c0040d01200348040f500b118504038445502c14400d0f182884c110310658103e0f85007003641129000007880d40700040c41f441c144880c4141036048503000444c1040e0642e5640c543e0b12411003148241d982c0302c000000e03200e030340b01d07001500700822564941000d940c4421486010350303c1120080c6033400c0e05c0340c00107150240c0c482103c502090392000ba00c040d5080055110610100e0000030750414010300600400e400d080c4003c00c3c00d540b16800e0003503003085445e540e0041e81d6003070b8021000c030341101c0000c1061900080449a00a6120040707584807410140252044541940c4550304151081c0489030385c95000b02c02008428022080b0105580e6608204019170b1103104006103002c0b03090000c80d076141050142c00e420150201a00d189a03031052407140d146c503004a8541c5031598486c2c0c850000d054040c888a65040489400b90400b000c100610a54900c101c500750016169942d040f6070307030010180300b515403680c1c040000c0e4200c1c00e20f0917000f0003e00301c035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 584954586 1250 584953336 584953351
    0x818061204110108010609051c05010c090e090a0809041d1c1403011503091511030a0b010e03151806090102180108010f03020103151710050109020a0c0b040503130e 72
    0xa450b1146035a40c0a0300d4140e048400300e0b51880101e500300408c0c800b113050034001940d841410440d030200011028000d0100343e120384e50b50507000380d1508405e5020071001038100307070694205404510200f8250002c8030210320301640c1c040f480c0040c180142c0c1d550720201010765050300403180300125940015003844010b002944d41c0d59120300c8a2030f004903503031000384a4881212001202608030500a0b0014980a8002c013055041e021451030f20b842914051a05044116000010807000c0b240728458648281420701c1c00a00541c00c2c9400f0030365584c55000302d407026420407000100c81c0c1c0803003408040304100c4401904c80d181804141c40c0d000c2c1d0401c3c00d160780c2401c490140b000c01544100c0d580c0341225000c6d00075400240c61900194000c1440304000e50382c00220100c0030499924680081c000f1901e40c0c1c0080022003102c641050840740e068105520090040012b02e01090b8808901d44080780c020001100c00d85403854030038514030034800d10301d00300d08202c000021070700000c0b80390703070302c01e1a8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 584955836 1250 584954586 584954603
    0x905060f070203310e0109060f120503030403030b040612050a140a0b0a0e030d0e0a152f07021807090605030421090b042d03050a0818061204 62
    0x110144240e8403400b500e25982c00070703ca9110500e40801c03880824012502c1312240141c422a01d41a2400500e1402d1b00246040b5444010822290861100e10300040441e17090328001d8408075503416071a8070029202404150b1500791006655560391b010100602041035015030400321480c0036901c48915030000e44040107881815500d03004081403d0f5202940007007410703d180c1c1c41d42035800c01030401c1e051000043c80240301c1c07400c400c600c610400301041c1c0304400030048010940307007040000700d1b208000b00340182001d42d0300c4255010401810031190801c0c45560400d1240c00130740d4000d01481d500030354000054041d11407044507040d80030b0b004e5000c40e0303500040030f6100c1206880714441034500a15100c1e40f0f1043c0240b40190b070684002c4103c4514000c0404c03980c50980742c129030030a40001c0100c0e86840c00041e006d5060109444d603100c240289940c0051541c1c403119240e4a44400141c40d03454001280100790482c036045e0010413800034030140d02c840403090030800c5e0640450b000c0701c0206 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 584957086 1250 584955836 584955841
    0xc060a0e0a0b0405031908040e041406160503010b0a17040308040b0108010c0f050d1b020706020c1c0b191518090f2d0501020a0929090f040905060f 65
    0x403042c0d0119000d40350041d00500100c440b20494400038092030100344c1b0021003c2c0001b080da003058140d10340c001c60140d8444490304440703031500741c02c21030040c0400751f00e00e0101284140e500c3c0c0080940341124614a40a03441d0404001c00350740002c0700381220004034940a041104041e0011a490b0069024100500c0c00740c1c0c0b0383c0460341c22201c4014044000c2a074403855260040c1c40f0340010085806240300215030008110242c4500e03500b91140c040150f00b100c142840440da04222050710a40200c504d0b9000c1044500300041541e45000080c20004680001804010350402582c80d50712400008201c2903032900d1012110b4184ae006180080d945060306600c10480b901684c0f4419030840c810302440c0c0a01d66545240300785040914485030440b81040040304d5082044e401040c0c001d40003d03a4902044800504244468000b084490700120034440d01e084c951000d00c0034020b43e8482c569031000b0b2440010019510b0b1031110364414142400e8400300030f0003140842c0038064040743c604954 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 584958336 1250 584957086 584957099
    0xf0f02130e10050609060d051602010b0301060509010e150603010b0c1c2717160f0b0706021608161a01050315190212090d020303041703090c060a0e0a 66
    0xc1042e20001000350124106018a01e40b410040885400061400340b4150300300750b4807001c0d0382c0c08072400105050381c9120354101030f4081c0100141d000c0102c008210711818a0000f071a444018044d501c41c05960000203445000d41c49503c0d840308000900280c2c4a680d1094040c42c0385c2c0c00b400e08070102c0c0c0610f10070b0010101044204c0d0400b20170b0f503202c100c84600c01c949044542201442d00c116010f04041000a400c003c070b0042c01c01d01d0302078401030040d603c2c10901c41c1024045a80c84a8001000c02c0000c0180c002c1c401d054601c074030f90024000da50342d0030090761801c0c1024150000343c81e117100010704000d00ca43c00c40302e040c0369900c24000300c0e00300d154030b008000700300b0424810340d900741c0c0207144500c442d060502000f0340c1c07000503100600e000d12900c84040c030032600541c4642568002803000d002e200c00c82009500d04090052000354070794942692104246401c24884600c40c0d0008808035000742d03028480c08825035400703800903444600701d440050062202e844242e000309200c04011581 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 584959586 1250 584958336 584958359
    0x6050f070507080604030207152c0406060c06050c090f010c0f022d01110c060a0318080306031b030c010e030f10020319110f03040206190207210b0c09040f0f0213 71
    0x1641031303215800400ac5200c000701541303090594503d00951b0014480920307580700c2c41a080540160b40e58140702c02035600d884401c580c4064915503040ba414801031000b603550661041c2074040a01c0c10000f009580c3c40c00705900f109040300290301c4542c0114a0b0f010107040d504042100e0000c070400c1d44c410045100544c1d200c5440008161550041e4182e08010b04111004014504152a00050708100c8100c10120541040400c0391f07241d000204fc0000c03441c04129010741800700c1c80da9408001c00d040d0000ea90b40014407100703414414500ea421009039000d00407134011480c1310060b101001003035030100000b580100c810791030002c45e862113142c1524403407084060300400c074aa81c1d85005151251105590030050040381e0161080210011038403400c1034110035640250001d0070040d0070030000c041e21141003142403402c4d200307025040007c40d03c01240180c003c2c1040b81816a21060742010601410950b400d0424507410040f001d0f0420545a00600c0903c00448004c0d00da940c031210320307002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 584960836 1250 584959586 584959619
    0x150f17060904060e0c041a030111030709091104080d020f011d06010b2203060905060703020306061903180506040203060c190806010c0605090307020a08010605060406050f070507080604030207 84
    0x10071001c0140000c0014281d6070100600620480840b0684200c10740050117444025000708050b10205286012030b00b0240a440040341401601a065260420004103251214425110080d4072804d02050300410380d02183d000d40040c030207271540303005c1048000e584d500d103000120110390b1a24145000b08520321100c40a408607278000b5140c0359180c02e02c0d035051900f00c840c810001000004807965050400c205050007103208840105405035982021b40c2044c8000b40094141401007013080341a64074403084600c202d240188481034146195002c40c024103161080c01e40854500e800403062101c0052041d100d40e100300c0c2195059a140e038010613280c0101080500446a54414142c440e800f0740c0da420750005041c0362080c10880242c5032007040d43c8042d12420b80315000001d0000039401c085c1070a0380600980c1d4002d0000a14280c007180080c4994481c100400c9404105c6100841000007180c60081d00441150211030310f440c14680c84d108243c504401501c144030001032180c49094131f205 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 584962086 1250 584960836 584960839
    0x409240605070b0a1506020607021b010504090c0c0c08010902030c1009051c02090f010519050603070e04091a0601080f04020f060903030c01110d06050301050f010303030e07150f1706 80
    0xb814040c0c10350703c42c200c0c40e0001d4461107407691162141400003c0e0124803400a068542c02442c0342d0528010280c1442803011034a48640310303125800426076041021102241c8181600107110b49401e002100c0295240c18004c14030a02c150700003401d400c05410081c05203008500359201001024208210014000d60308000720341c408200300050301c1c00c202e03050b050800c107607001107505c602a03000401d5804211050010f82d0600c4006200740e00b010203a0003d0613030ba080c6020f41140c00c0c070740040c0032404000d00302010004003610b6034031300380c8907504003000307040d4050404800010107940149281d40200c498030b0024900c000002d5201d44880710607805281c01138020000b4070340d4003060103480e40c8001e070f601d6003510080088044484003441a219010b45c3c1d05103d603103840207407000000780d0381150310079440b85c0c0c104000d000841c125078410a046035411700300003d000110a540761f06129190307020074800c003071058461030019000544400c0403007051740c56040709035904000011154003560000d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 584963336 1250 584962086 584962097
    0x40c0503010b032a0102030f0705030a03052d1003050f1b0915060325020a030809010c211104030302011a1c170d1a04050a0b03100c05070804092406 65
    0x22603804c18440a9220041010302c150b91030121034210000d503c1c0d002d1081102e5a030700000b402c03030b0090b501d0302c189500000d05082d1951103c10700406074a4070801c3c1680a07100e0b41ca110f000c04e040d0600b16072110005c640c844199011302c9a282c40c445d480d407100609502c42c207100c100881c501c6240a07003289100e1100d48540240d03008121040c02025000100002441c00c60046008140704c1c2c1000303545021802540180800601480c00800100000e0a0307401d0f60381c1040100c110858221800c4480b9811070ba80010340300119107101006040241c402440ea48000980401030640c10340203030010b001d03025142800c15201e0f1082c80307182c0e030048000c540e1002e98280c28a0004030642450329940911001880c1080d416104000450f62902a00040384044003650301e01030900703002d01507001d954018100200303020392010907200c0415000c4400d0040d680e4080300da100e0301400c203031400da641110400762100c1c2c40712190801000c0c80100620300341c0000103d04460009601c0c500241c030002d1b51031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 584964586 1250 584963336 584963383
    0xc090507050a030b0102100e0a020102072102040513060501061101061a0a0302180310060e060d032723011d0609040f0e06070509010915020c010c050f06040c0503010b03 74
    0x1c60082c00c1000c4c0440c11805a000c0c0d01980c4407d0380613005542e410030001e011103504c2072001a151000c1503000e010300529001148842030300c5c0580880c1c20903010f40d008201a030311001444c422110401d4020042807500c4001308040341e0192030314481d150301d50020489251550301d01c40000c40c0c0a240320600360420030803090301300d01c82c0c2c01030102d420700041e010403c0840400024141030013035215052441e942d0504010074030241135095082003041d43d10704410201d5440c0203005001d01074110303a1000c1070a0ba22222040c261b0303900001041c64900071110428400c404401446201c3c600d80c2c0094081e0b50045644c969056199a942c0c00c010f0070b1910f001000d03800e203c003800c1d4940840c0070043d6500c44034141440240314251056103103582d4a40d8032445440050304080040d00801520394003410344014585d00002c01d0b100140302400c01211012032071508618000805044400a000e0f1300b052100300700484400c042075410880091084009107014180d490300c0c024140c141810304580c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 584965836 1250 584964586 584964607
    0x40206030103080c101b0201061d010b03091507031b17010e1b07050607140304150236030d0e09040609030302090d0c0315020f07030e01200303040c09050705 69
    0x20010018400159220070300c0c003085c0c0004a07404030645002441720319851160450303080c482e140203019247c64a050071101c04120440a20b41400303158980e000010118507103034401c102d0040c060b81074040000b0b40340307803482000300689142029044244011103041e44d005010381c0c13941c80c0b101e144400d120039503032030907080780b40c0d81e9000303003000b05841d4140400d40030403101e200042159078050001495141059040104104000116281480400d0003403000042000d50b502c206803802684c00750325004452880400011194418120082c07480c00480944c6500c4118840410048003074030550300c40c0c1d0728141c07010310354041c10b40da00240c4030000400081103a800030100070701034903005003040180c202181e08da207400c82041c1c0700340da2041e008004111801d1000118044039200c1035092014112401840d0300a138040181400340380b419950450348a680d04200c0e608982802040ca50707258100a900c9520658054401c9107095501141034486401220f02942d642e0b66454a4041000d1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 584967086 1250 584965836 584965853
    0x11011b030f200a06061802120a0903091d0405150106020a0f0812070537110c100e0f0d0f080c030408030d060e0609010f1a09030102070b100608040206030103 69
    0x10400c90b0100c0ca44a80c489014004101181000b48210070002d0582d080214010b00c400c200c4510745034160040100407401900c81a00923000040d0080210700c92500d8a0251110a42501701490138142c3c0901000b10f80482c46145000c3e0303000f40d01340c402e2800307580c00200d0804804d009540159201c110000c00240d40d0340299001d544c0030380303980ea08150250000e0284d4206c107443c0c08000500104400702c0c0c8400d0311100d0500741d011500c002e13180d0514070030307a5007500004264108c01e00550843d8184201428010403030380802c002c207020018240b01780c003e071420a000003801c3c01a4000c4200c8086400c14004005020b90030075940140b990083e070702c1c01c9951740055110400c5e8001480300040c1074500b007001d040e208200807008a041424403550199524008008622841c0c01c1801040322499040600d401e03118804403400d100c98800c501c0601c0d42c0f203200807007501907100141804c140002c501c0c0041c0540c0814142c01c506030354412040b00c0d050707400d48002e5440305040004000280454 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 584968336 1250 584967086 584967107
    0x10807080c0316171e09061e06040f050f0a111309020c07090e1f200a0309020306040b060f060711091305060a0c02010b0d030203090904020102160311011b030f 70
    0x2481c0007010190013406001e503c41c41500c9100301c19110794042c003560f03a40c1c00342c02544125500d005160360320b4541d001c1140d280e5070301588001c005541001c03610359203940d0448510410f83c124140314604242d0070b800b190f188115844030b0381602e01070071242e2031850503084a00100d40c985440b0350113418009068000c0d407003040401214419003200144821403402415520200300029051264140001d92911080300f045034166071700d0700480b907421181904c810324003003070840d00c95901e62000e501c080c5c0080841d00c034040d505105200c100010402c0141c6c20317a1040c981621220a01315102c42400303014000c00c100100316105c240111001424001546548800700b1071040481e5800394444500703050050311888001500c44150001458090043c1d00346501d05580b00e410712401610029240e000b1855414403403002000854296842001302e40c50b41c0ca81412144403407681c070b01c0d208120341e50301400342e808945011410701c1d1140b1180514815141c0688581e0726402c0c2c00041150080c000c3c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 584969586 1250 584968336 584968381
    0xa060203180d020d060509011503030c0b0402240319020f040b0c010906020a02010c090e060f1306090c110705030304050603010b07030908031b0115030807080a14070c0302010807080c03 81
    0x46410b94025945090300c3c0d15400c0d0140d60f0000d11410701400040c00c0d0b41a071030180310000c00030f907820000264000003005e4a00c1c3c100c014503500d82c03554400034069a0203161a02d01c9400404001c030340c4604098001e5001d04440710000d0100d01e03800c00c0c03400031380c040c2103406140741505100400000e21103400414070100d904d000010500115910101240c0211aa9400503035481250410140e00607a184001d40703003840e141507892800078002030400da050755030075004e190441c3d005046c4010941102001e0019104107104c40402100018001c0e2102d6004c80790300c4c859a0343c0000e05040c04011541034402c05070206107940e0800c0e0031621240c1c04980c08408200ea550000190310034248040e1020300c1600a0341596504859401804d484c0071007005040c20100342005c1000075190f204480f842d40d0f00c130042c01e4031090000d50603240403402441d0700b0900d000c001000401c101007490140196071003602d41ea0310a4a4500301280c00e4441203407890205038080001c204044034102d01c080c00000d8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 584970836 1250 584969586 584969599
    0xd0b0a11180a05041a0607081c0204090e0c10030c0201090204060b07051218010f21051602061618080604030c0b090606010906030e03070218160f0c2613080c0a06020318 74
    0x422048002c62030201c100d00100c11034ac08038050201d80e085000e002c003c1c880c4080209084099140000c10001e40d04406400b4195101e4030988400c0c001c1d0030244206400400c1008442e5491811103601d9105100450b03040c01107513600800030038aa4280c540c6d10355000a04d6050182880064034a00c2056a2242c10b101e500c0c41c0003104002460400c9015103080c48000c602410043c803003100610201d41d1a0080d0740110081001010740074004070b02c0c0c040c80740340c078603410035000f265203030140d10f10f812500030381c09100100000d0540080d80810198400c007421041e41e9200700e44280c6901c419980310740029200c1d9001c1068038800d40081035810615015246004d5913036002403400e00d11141801914a1300c00108402c01001050740c04e17060440c6e042805440c4030345c4500418004980c20300802c3c0090510000340c000308182844411031000c18007440d03032110b003024038844e11103081c8940d045034850f90f045420107041403ca02022108603400440c01c00101400d2050340d00c59540d00c5036000320 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 584972086 1250 584970836 584970847
    0x1b04020705250b040e2d0f070f030504030503070f020309100e100c020a0306091110020a0203010c050901051215101d0904020d0b0a11180a05041a060708 67
    0x103005000480300a40c0c00c4800030b0360308589001c03900d0031210030780c480118050140301c100000244401c1040e448180003001541d188240d641050b40040d8201c40c0c0d00084c2030342010030004d04629202c42e0302071065900d80c50307a21981900202d05803a81120f008000403401d002140c040f43c003402c00d2442d0424240150f030300300640100070400c052410307042000000e00f1640411100d0800c2c1c0d180100700301c40c518000c0b90424003a00440c0b9049094400200015907950b85141401210002548200001005280310038a4040002c0d42c42d035080c00c05034401c1d440c09003076282c0640158111030040f841170319040c2c00e00800000000502d00010018544111001180111a941d081d000d90020348103845184180303140010300000600d101c005c13a40150308501c14400540d0302e4143d564245030b805405201c9540e501840c03840034065984000c41c0d160004141e01c0b200703009480d0300c6d80c0d983c40e0980307004507419074400c00c0105540200c10080103030706251041101604103d80180700d001e018400d42da2415 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 584973336 1250 584972086 584972093
    0x61212031802060913091415010e0906161e030b091515070c1a041a091509010c020a030b090f03091e06040b030c04170f0c090a060f0e0601020610081b040207 69
    0x441e843e036080c1d00542114444480769082a188030b4090030a03805c1d02b034ac1520700881075503a1588058810300c81c49079254030480101c2e00c00d1a0216040003500a44c81c5040031524000c1c016101c1250303001e224050440c0040c005100403201544c0100c4000e02402d1052604614483c065110180c1558600308003c8003241d504011040182c03d1038450600ca552907292120181c40340b54904040e1580318800c0203c420300780d4039030807003040c0e2001c03983d04a035444103407a005031440e04003244020b41100420600206002d81c00443c0340c45804020142c0300311640320500d080e200c0c0301d243c000580c405450000c0c004080390079201440c007070402070040c030f140a4441400d90b042c2c1d0805c8a00078a05240010180f103a2007a02c1450b9130030386462401000d05240303034040a920f9100d1100514041c0681c0b20001e079202c074140e0400d900828507181d50800f49a12158070a404100440d102c2c0e01605c50b80010900303616a8920b8181290203030380142640d001d440500854a0544c02030203640b16409000e1000032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 584974586 1250 584973336 584973353
    0x607060203040b04030306080706090302130e300a120c0215040b06040b100c060b030705131b090b031b211905010b041806121203180206091309 63
    0xd0b80c000d2070000001e140a103801030590b0f045806c120a55005a60100451030b00b111195040e2507048415a0603403885004d88030041404481c401c25034852040103a40216003d02c4c85a8076400140f0210000d14007441200064400e5a1480b80001c1e0864560301e90082c043c1d01c419002e154606c1952120548820a42c0d0021030030b40c0c040d12604600c1050000320720b028890f00e070083c038041d15426003101d48841c1c0942080c0403500702a040640700d03010727440c9135541400440040c0c171009103203680010032203400000801c03000000c5200ca490f01100030300d5090289088904880d00c400f003552a541d114000c00121000040c0c0f030510100007403211561000304060030b0683c40112032003243c41440d214204000e401c00040340d29000d20315010062103401c8107002114181c4411052040c11030640c18544030080c5503d80c002d52048072205c0303030241004442143e252120340c0650b003d0081841c1105c80c0c510b448005d2500950080c4100300b00d01c0141440c450740c0c4000000b03030000048005c42610307101803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 584975836 1250 584974586 584974591
    0x414190f020c190c05181501020a020906010503040201140c0d080a0e070b0d0212010b12130503041203020a0605151512040209180607021c05120708040203030403140604141b09060607060203 83
    0x455031b100c030200259100e040300a5011030708248001c00c48101d554011803080f40c8058400d40c1040f400200140c01d5901811140c1a03542e8204201a5192a41c604003600c030340441ca080c0b4005a5803a010658551940c080d40102030704082c05041d656180c030043d0071069101c0e00c0d01428690f02844042d01080b5034000545c020b00019150355520781c4026100902108010140000031112900c1c0c9000324a001090710300340d807440034820071002c0203030400383d01c2c083c074140e40100503a060004104000c944040200d94503881500d40b400705440c0060241414021000f0700c00a6a40440000d405450944074068102c8005219040340c40c19060300305040a00407143d00000d6071080314192202c100381b9641c83e1079403c0300d181c40c0f4107245400800c9589542c001c0d10302c0e400c02a0f1600440d05550b001c0c000c880c01994403486c0c01700c0b40340c00c0d03400840c0c6681c030445082c0c4500b05221b141900c165804a115626040305450442c0f075a00c0720010450000c0d805003100b50030003000e114090000e09144010350 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 584977086 1250 584975836 584975869
    0x120c090c02010609180b0105060a02010207061107030801080a080307030c0c02030a0f1b080303270a031148031225080f07020414190f020c190c05 64
    0x34601d4101000c4a00761001c1c540d030140c1400c0c84200c1c80011401841b42e06055480403034000350354241c1040200d000e4059818040c000030b14101d2103d00c0b03103918600425640d80700e519130590302ea985010740c90b143c41da0309070081d150b00c808000090010384240d1294480d02e880b402e2401b005000c3c1d401091406400400403116548450300d19802d11074045041b595100d0105132400245082c0711500d6101e00006d420a42c0e610004c22507911945240344807a8043c22940040728a41c82180c28001c0c0501e50359503022445019085040c18415602007880303403440001b5440380c849890046044042a4052241004200340120307070702240d070740511401404a00c0514240e4540c0301e0b14040502e403111a5190746081940c018035017001910201c1070b20740c0c100c0941c00ca80d4441e18580085406850071602c08200c0140c0341e0100044030484080c0e0b20a00300c04200c007080010440f140e00001c0b07106101e80100c1d29442403203283c622595880c58600c1c2c80303114084001d1a00da9400204402c0000035202c80c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 584978336 1250 584977086 584977091
    0x13051509010e060a05060f040e071d070f08070c2006040b0409110415140c010c0302071527030201110a080412030501141c0506010b03150f0a120c090c0201 68
    0x41c46005400c222035034026044d00e104002d98103140c00083e90880640d40380d03a00030703515a2a0b204130804144020b1008103401c010758190074900180c2c18821560844081c00441c40344030788650031603c030b040c41c544200901c1d10b82c00d60301c41e52510b4061545582401540a00c40c2c0181c500d0210345840000c1d10040000c0c1c0c00003601c4a0500d00420b090300c202002504101c00d051008120b04002d800000c40070301c0081c241040d00c0641d01c1c031002064815107014030070960800c1100700d009581035004180041c011000c484650303503070360340040584a20520200110780d041418211448039410554083c0e03100b400002241950600c0f0401039030070070680310010652041c01c0205000880c20703240c003035000c0391500700059814010320a94040e0507c82880c000c151100000150313a0015914580c2a5001800c0750010340c0d40d00042c0600b940b04a440f010302c1030802c0380350340c1e02d800c00007055001001c00405106000c0c0c180701c0c540b02011542003098903c001d210400060141441c4200000709069a002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 584979586 1250 584978336 584978351
    0x20402090d0305042102032508030403080403031d090a0f02131409161b030e032a0a0509010e060402120c04060201050f0f04030f230d05090d081305150901 68
    0xb4440607000743d00c3d01202807121258440c5c01a81c010400034164440c1400604101080d00d02483c124043da03000308407688400107010050140300e8029004580c801d0365a88050700105a06007416500b060341c440e0095559808a0200d102c20342100b0341032142c4050040c1400545009021000460f501c140080729042c00358110605001a40d82c4d80015540b1324500107000d09000104143d2240c0b603080c030018120342c00002014400d4021414810780181103c1c001440101d904400007205a4207007903845a100c452035160a08201080031160001c2449139960300c2c0c01d15100d489130000302601e03880781c1c0c204054071030380c0f0107490a54001d03c0c121301c5d0706031980c0c2420006421104040c01c46000585020100601c460300c1d01040799105500d89001000c1c4200c2c50030640d11400c0b800c4c0e00068009412520b501385440d00700c054101c035903015905110640703074903611030b4903000700c151110000741207400061045162403190709080381c0b0030400c4809030317a42c0b4242c04070144d6084d0340b44003480c1d454502 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 584980836 1250 584979586 584979599
    0x903090d0f0210081e130b01030b06011e050706020f0c0106080a11030613080901140409091e050721050105011409090c03060105121f0b01110c1309020402090d030504 73
    0x2540c4800555410480b410382400848603400b01c0012601c5e280e0308860700c0008060003900c00b5200c4c1190350004010149584a24000325051002c54403940005c2c2607444071000c03031141d80107202102c002a01c8013441d14105860380f40203544141005c0f40718400c10001d40300c992a09118481c01402c5010140c40e80c0042441d1025420150054240c400e50012040c84016040710340184030240e400306041740d6500d110001601c05844404840304224404200040c0205c419042407011030710178a81c0102d122203500d01c0712813041034404098021303804404107201c488000140607030100b290341c0c0c00c05c40401c1d9035690a400e45100360800910081c64140b8400c5608288001c140c1001145c4050134030a414900442d81daa40705101d02c52041c881614040c48009d0f0511090300c492040c00c0c070b03a07400050240401c402a201c3c031004c89000611903241d01182ca20041901e1405100007044040b0790360651011201030018100c090b6405a42040503040507510180c01c0c0003403622139200d16855a1400c42c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 584982086 1250 584980836 584980849
    0x507020301140103020a230d0c1a0903030a050c0f10050108240c0304080c01020a090f141e37061d040f0e0a0c0f08010207030c0605090a0c1701050a1803080903090d0f02 74
    0x520351402202880052a01ccd42d021040d101308808610381644c03560302a103586443c000500a400d141c0b40521a0450108103481c0c0106060380c0407c07044170784604007151a003610f158000c10120581240f071010803090b5002c1001190010f000d25001030504a907c111282280e010703484690208050b00d02c10401c03078140c50084001002c4c03081901c0e8005403c00007044240c034034038004011401200300c41c1c1c84070341c3d0380e140851010b815401146040c090400c985810b05c910f20b107540441c40c001c10350001002441552042d0242c0035080c0804804185003007480301928a48070090740d880d484484910031031600300008404117010358000c02c002c03450400107111480807030300170048a900400808001c81d8100c10341c1d070302d00c5500030800620342d40d82d2404a0305001e10030130002d007244030040c4005042500075020b42013085080c4000c00c00c0d038507000801811036514031100022201c20b0f180b0350300400d004980c059441b40320581036a281c4640900003c144e082e2100c03003190f441e20366290744e105504015 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 584983336 1250 584982086 584982119
    0x3150a0f091a060414091f06050904111e07031707020c010f03020309190512040b220e060105070501061701090506011d19060504020a0507020301140103020a230d0c 72
    0x141c95a44c5490308011500c0d00d20144c412241d0700451420780803a800b06940c44541410903d51105a55265141c000052103036104034001d5114500f000c00c00c1c4407000078213084174030004610007070300c203100000b03038003900030360000801a001c0c0030581151004000d1014846031080306d140d4081c10741400804005081d103020003614404052040c0204407507040000b4890080390080841000182c600e80340c000c0c5081240b42c2030b401020404140001e50131a088041e01c9524001203030841d0304040e1680010300324160348100d210103540b81c00440d04550280004180241c0140004a111038880501c04952600e110780c40d40c0c1c6a555024001c180b110500602e40035018501018001500a076007450f14403401620b901002c151002c1c42c640441007c4d4411802080060015034507058640300241094200840590003542401c000c5c80c4682c4d42004001c0c1a40e40c01800d1030304042c2000c1001c0d80345141c0000c82400d880c6103030360400036030780e4481c44411014440e52100e00c92a003000149080c0c080d06 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 584984586 1250 584983336 584983339
    0x114012105031b1009030305040308160e09190510320f0a03050a0c030c170607050a030b0a080102070c050603150f04060b0d0507110307020603150a0f091a 68
    0x103244040c030020358044211902094a00c404550740300c0c401c500542450b028600942d9400e01c2c0c50b250307608154142e00704a00c00c034002e441d00101c5507a038466044c01421000a210000b4056880040da07034079141a000303410280c0380703018100c50070312400210101c070000da64240488184100c20440c880e443c0c8142c21443e181080d09d031811040c529201017928003080c01d00342c410000e020001c0c1c3e039611070383c00c0340004542100485101c000d803410586c0b02c1c403034513010907191000c02c0c1c400800d4a18100c207004003182e0707400700202140ea039000360880361500800c00d14401c040c0c560400c00f01960b1b8464450000e04400000160f5828851400b0354101d1015448070f0300556080c000c0029021141c82c204a524606a40004001c044400044c0040881e5003003100c070000d003c150b4070750042082e881144a81c103261107080c201c090143c1616a24001c50400a40c42101003000900085d500c0c03038107486095014050b0a10545c848403201503880c000d400a00019a80e0840401d0b081403102e00742c00981350 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 584985836 1250 584984586 584984639
    0x9080705150a0b06122a1308011a03031206150c01051009110403080c03041a0703030e070f050f0402041d0a0c0c0b0103060218041e05011a0723011401 66
    0x10740e42c03489240d00f80d000f44260f003803484510701c65403030401546c4560080070100d0001d596031491070880c449282e1281c000c0c5000c035031070140218011240c82c60b40d00f5002d1b000400560070401103009203000341f400100b01c00d811034000d02011005904d14800b803d10118840c001080320302d0319048090540302d16522410480f41003c284519190842003201e0030b50b0b421064807a59800038140951030740c403455000d0051465400480008031030000050200103110b0360342403083d120314500680e40c40805000d021074201c0d08500c10421440d0420120501d004e0191000d41840d03610000c0800c0302000b2904c40181900003010044805d5644c4100c10040600381404c44940d4101d0304c91a190080c14040104040d0340004d451001d80d000c400c9841c40e014000b001406441081d4a0000f11800c0000741d264849051500100d1004241e220401940b110050740d0303801c0851a4917103c080c00141c0042281000392402c0d1908240070030b028940c0300220407038860985508d48095400304031760041c0004210720 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 584987086 1250 584985836 584985847
    0x3091302090a030b070e0a031101030f050910020a09030501020f07050d0305040b0606030703150f0612020c120a201c02010c090501030b060c0f0706020d021605010309080705150a0b06 80
    0x15910102c1405498200c08900d81d190742d1380c8000d4444e46d0f40121890340c42140d03182c0000c10051070f17000f607040d408802c2c0d03418080d11b2200f28010040d0380c030503034404507290400050b0580f030001c0b960103402500b20340d1524042c13007070741c075100c80d800c80e401820511005500000c21600784034003000090341d0804e046c03904021500e440d4484040364400640303d1441b58800001150b8007500c40e400410403116425a03900d1195611102e517401c40e6042e1042c2c2004c1068105202c58140d064801d0b01d9007001c1041c050620401d5050f0383c9409035000d40c480d07205208140000b00b100780540d8400404a92048001f020711000c403108024030600c842220104685c10103a0038071420f42c2c088440703411101c00f800c000c034110f800c19000500c0c500481125030445d225800c201c600421000440d10300311242038003540c903107010f080c00890701da00040740c60b003410802191302085294400d600c60742545c0d00424150781130240c1c958440381012a040f00e1844070310000c0e018820188018402d80642c1502190800c1c54030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 584988336 1250 584987086 584987089
    0xb01020c031c120204090f240f0b0a09170a061107030e091504090f0c0b0405060a3002030708061905090a1107290f2202060c0309130209 60
    0x15040ea882c0b000420280f110360742c0c8911819010390307000d4582c12500740a15440010b08600802004240e040407032001030400040f540080c29071400c0d150741a412483e03450070007811444942c003c1035104104004951b00007030702c031180901c00c000c50754071002500702a201401d1640a0381c100b103080c141002d20410140e0002030308020300d2000034a0650b490301080d80c0304a101d120848031002e07a40c1d0443d0400884000b080b0f40c040712800c406120740d105c0c0c0c0030651201c00c000781c1405140280754111384200001640540200507014100f40100a0700300e89070486248440383d0b141e0103404002c25a00401401026900184295480482641e01101c10f5040b41d010000502d040e21400380101050000728010080340d03042513884030270030040181c3c0c0d440d40740350403005401d4100810400780285c040407200324600c02c242d00c1c0101c150350311300300990310380c01c070040c090030081601114031090351560300c40142c0f41e02c0c0140800350700c241d014548540f107040903c0b0f901d402001110040510401000781c0d103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 584989586 1250 584988336 584988373
    0x1606090f05061c09120c0209010b030103050303070c06150b040306050601030c140705010204050618090705090915030a020d0602090f0303070503041e0f0305030901110604050c0609220b01020c03 85
    0x72a00c8207400303165043c061401c50001020541000750510001020b02005103410000d0043c1e913620030b444001c40d983ea61148003589000a01004095800030000309d0400f5119503000c4a0303040c0100000a5004480b025560305484140c2c4500c102000106040081c071901384a0300b42d110400382001e0003000380c0400014031b42c6040c4c150f614515480455802c0910000754140c901502d00a062160f40324800c0d0440007070100142c01440c4190b9044002901d01440b90701a06c01180b000380c4402c1c807940b00c110082504505514201d9014404c01009001503614112100030481c040c1000680d1801001c0503ca0303d4640f0b1b9041c0c1c1c1c000c1e44204800f0b0009180002150120b07280b0502401010010018a000ea6141580a0510078000c454041309011000c4000d040c891400d03228028180c0c02c1c496050b03113a8004883c0030b000c0f07402140705090b031400d001c401407034108001818144180c800120320154140f01000841916561700440d01c0f1658040043c040e100c0c0c0214014900401c403035110340e00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 584990836 1250 584989586 584989597
    0x8010515090f04120e0a08010b03061b0304020618040504061512240b030f031801090b0a031d2d0105160c030203120103050105070801050a12030318051606090f0506 72
    0x804000404c0c081c00d050310440041401d40c0f8010040f0710b03035a9030b502d00c85000e865010465403090007400f001c6401c4010540d100f445d560b0040c0c0d086815a6a42c1c0c081001507044020b03c007603082c40030f001c00c1150380d45074414075102e076100f00000185d420005002d074801920070781101e2501e003e4243d80a020a0340f01c4059030f080301c50700940306804c5002400d01c4000d042d080d070601e9010300c07802c42d00790415a8040017400007192110440d40051054500455000b00302d4415040c10840402c029039400d0f01c2a0050980792030780f40d0380304800704102c8504500d04445030380b00306100348102c3c106181c0703640d2864a240512587e1802400a414907030310340c84003c9401c01110b000d0012121001041600a1003035400300d5000074140e003007640e52400c0940c040c08049418800180001002203110701d818040b02c01504c14039841ea692245081c0d13415001071480180d00700402c08052000e50008200b0002d1080d90840102610342c19440d0502c040e0000200350415102c980d0352500c240070a8480c03006488 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 584992086 1250 584990836 584990843
    0x1807140312090d020a0807030605060607120c020a030c15020f030a08070c0507030204050709060807020a050d0309020a0504020a0309030f0e0f22050106081603060510141308010515090f04 82
    0xd581c0c0740c07840000380f0300c0140050700075001241c803440081c1240c40410f81c18101c900891003071000399100d03000c0108a2245007002030210100801d007180c5a441100744a00c01807014101006881d00e0b40c0f203843c40040240d001c1240c00802036046a2810741c1130144800714106040110b0805002d4403010300751680c014814030410a950480e2410b004040240100840d0040c00802c210305004400174100b040c0c9000e114003240c0000c01003081c8510014030030700d54540101c0900007401e0710b9a030460140501340b0742a60b202c203035107101140a6823148000d0482c1c20300d43e100000c0c3d44185103405448161202e00c184203115840f20081003a440c2c0900f050b02d5404d080317604003002a40c204484094266030410100880c7c035103400880c01c190004842405500c2c000111400700741100c0049080e20b406008071074124055180c42180a8020b0704040c0410f40d920f1441d40c1840d80d80101c0481c80c908580c0000f695a443d001030140e4000c03481c0d5884e0301d030740c0d0550340f0b0a02850040082c04c038100c0e0141c4001c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 584993336 1250 584992086 584992123
    0x302180f01090306020c030304060b0f0d11060919080105010b130e0403051c09050601080328020a05060a06051512280612060e0d0207030303110405040518071403 71
    0x410940c0e00c0340d0381800196030700400441d2a000326011b003076602c0d00308076000c49410b8034102c24040b840c0381015200d010144014202c4007005d20079030722a07210b50180011540c01900c18022025071307039642e42c55070801c2050560054100c61415085c1420340c7d07030680c0010f030441c1080000700308a203114204802a0340d0021301d51000c40d112803a0480b030901c10248010189050306405a250301404e421142c8002d000343e04991043c1d0b290480e140e141d12a00a055068002100000503000d103070960414a0342203074019540032000310740b030707550402d1011121860060341da010140418540410084c44100300b510f40c090500b03240341c00d110f5602d40b015200c2440c207003911003845000f40c0e03903500e000e54011032032005002c499512103c007040c0c4000303a181200d070b050074552502058000080d030849040200c0d4001e100c5545903071026001800d10301000a02c940342080080b84c1600c9a005d514007800f500c00550000d2141010100e06050190b0406150b1071094030140e402643c00150720903000c21041c084 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 584994586 1250 584993336 584993359
    0xc090c05070618060e0f0132150301060b0310080106030807030e0d05030c0d0e0d0c0e0c0f03190e060405071701060317070c0e0c030a0e010b040e0705040c030218 71
    0xd0f580080c605600030011800c02584020456000c5111502c1d00e40020080c00b00e01c0340d00003218100010100400c3c150080e40d0003000c1aa0542e54a2642104850319134514204003d0082800c5d15059044138186007800014402591a44c08500e0000c0101d00c2c02041810b085a468146521519001404203c0b21046030611a51070700302c1908503030350004c21255180c1484995a4a8106610441020443d0f8032031610040c10100509601603030301480b8910803508121f2039060007000600140c541c0f6106210303aa01c202a00d40045004241001d0707800e85000580b007000050b80d0720300d42e50703c545030004000d000025030300040c0c450594100c0d030303801864030382e1130102c0311300502c026400a84610b084001c4003146861410080c40303020300803041504c0326030b1100350107024914140c03141e140d0400d080000440031b14281d4400c0e000007031200000700f03000042100180075588841b09503540c80c0c1041404118518140c424082882ea481c00c0079410b2000c029901711110780c0910000c0d01860120f0720 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 584995836 1250 584994586 584994611
    0xe060d0c0924031109041e060506040e0a021e030103030e0906062115040f0f15030302070302010e18090c270c0705030f2206030204240201270c090c050706 68
    0x5e44007008405007080220548511304440090a4000034940462a100c4003040904144088500782c40d060707041c40c20962504415800290b0028540d1071000b9418505040204001c800640c000d501036510389290300e095800300900b152005c1d01032807149000300507803001c1d050411001f0103080410081c5103441c0d9a810207550907480c442a035154440d10300014008a501c056000c04550b0f04029820415910f086071100070003007640c00050090390102008100641c8a135140089a003800780c03207a0305c0c0511318802d401101a00380c03141c1100341c010703503100300d602d090800e44000804900c410901080c1c90050402c14412005132240f81000d00014282d014480100100c80216140c42c1c1c070b240c1c4c0d5103072400710344000e9020341c0205246012403d0000407414800d0003650165007414414250203d00c400220721b0b0f065155440c0001d65403181441407800e0000981647c544141503601203881903246071010794102c1580140b9280c600c0c10b00d914010300e902400f030341d0480d6403100d40040c14113680300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 584997086 1250 584995836 584995871
    0xb030c15090301060305070f0504060501021f0b040c080403020d260417030f0a1103060f190504060b0705070e0f01030b070e060315040c080c0d09030e060d0c092403 72
    0x30700c50b007560030420004100080041c0703031021103081c0012203890580300c00402054810a1040c1c4e80180e0000a124030205146a901c02c804d010000001039060954404101980c50380038241c80480c40030000c01043c580c052000001c661080e162051048038170001c8020703020b040032481500200c424002a0401c01c0c640b4018050720035441741d042c0c491800c3c2a00018100c02210410509400c081441510a0440083d00c1c042d000080c240c003c0c0c040005c09000101403006504440216640380c0010301b500d07a4420400a400c400e10802c0d951840c0d801c16501d4104541d011040e80041a07003081082c4c2d402e01e4403541946da0003c0c1e0041117869107030b0111032a1901c1461240d02010000602c51620b46c901d0074200e8850056070140502d2000080681d41201d049610100d1240c1c2040702c412481e040d5030004041610034105a41c1c09021030000c0754441c1c010040444680d42e99202010545811410740c40c0244040300000600010002030b01042e88208a100f100789626000709840809800c1c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 584998336 1250 584997086 584997097
    0x3030f090c0b1b03030a0b120a03090b0d1805010b180121081219140906010510021018111c0f0c0e0f1501030b01090510092403050a0b030c15 62
    0x3c1100e469082825803076000341106940386101c1c0c034400c0600e035090400402c82d11080c81c1c05032600e1135032074940030f203202d495400380007480c2d650369455521041d001c1d400f43c8913520641c041c0e000091f402c1404001d01c0b000400000c0e0701300866005400400607800c0600121070040c8c5110350b0511800f8851809841500580c005508481c100c9010000103a90000074500e41182152007031003092829900c100c0c45180c255200d40342030308910f005009030b0038410b8079036040202610454284890308140d000803103000c0d0032080058000700006205101c2048492114810122500c56002440410111174103809075030080122440481030418400040c1c9508010700482ca00f0380d01a14040007084d078002e41c202c0d86d407003404803a031090045035482407050b03080140060b110074004c80c1c1402d04028030700c40f41941a05c02c112140034045110040c00c5481400c2d2000c0c4428096011440040a000c0d2407008010301005894030b4444200c3c0e550006078120500740c151000b1940b04400204134409104a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 584999586 1250 584998336 584998387
    0x705090f040914030a05090f0904050c01140f0408010e010e070513110f030109020a180f060c080c0a0305041a0f190909050c0909100e34080403030f090c0b 68
    0x855417050040d0010002d001b0b2140807104503250a0406080110001c42502c000c0e0195001000c00c55155000d40542c2c0c05400010011a05015800c00f15032455401908405c003d65100c3c031607600c242900340590103001c4004e038040c000342d038105004600e28140c07580244031703520749400b02d04503410402c43c00c507800220301840c101c0c0c2d29038460041030080c1d40900c7e40d00c40015400440d28054085191003a0247c40c0c20310120025189000d0007102c0d444001c3c10705031803804082000c001c0b205802c01400690030711070b480790381d01c50f803601d00d06040e901114013104e82400f90030004504501d01c0c05048a80d100e0104044060160012204403108a20b540146101d1480d00c428031040060490181003414030407102202c1d03070307650a001e9000d0380c60944682480c41e2200804120503841b007240d01c80360484001c0c0c1d0a0100388121381411510150481264040361088080c04245030f030601070b40400307003002e003410f1081e1191380d03803140c04402480c8680c08150304007096100c2100300380703400c107000c0144 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 585000836 1250 584999586 584999593
    0x4080d050c0301050f12100b06271f0804060c05120c04090c021b1011030a031508030306150930011b0912080714060f0705090f040914 59
    0x1c0800700842254000e01490744543c50700700070100745103480e1001402640b0702502600100113003014501c041c0c04003109459106000340312100c1000f241d5000d140322202c00304d04601540c00d0480034002030404404000f03a88100d1890f2421034642c0200034241c0159000c1c0c00001c0d08050200c088503540034219801014900c60000e110082d05680e0242045c0c58452000b0001022480f000360380d500b0010541d2441c0b0400c0103e051020700e080d46000c2101c0089050044104d0724600180c1d00350f1740706426540c0402d030356003000c0d4640c040d0104080c0107007010100031442c50600f2000150340c0e12603004612681440020824840c0c3c80b41144c01d40c1c1881e07003080e424160480362080102054075140313070111030340c43c00e40c0c20315404e8410141100d145015844500e1000d050624600405404003000e50b8010810401d010000302c207280d419005841003005044241080c0008461505000e018102044000e005480581d40c60184010020004a41c001901007062401000410010022406501 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 585002086 1250 585000836 585000841
    0x10b120a03021f020d0f0614040917032203030c0e180f040312020a02010f0b010f05070807030912030201050906011502030f2d070b010e0f1909060e0f0f060103051504080d05 76
    0x300701d401c60400d80380c603810071004818541c01400100e4ac8040c0018010325050800c3e66070002c1c1242c021a009681c0346d00c1150500e8030454690061104000300b10000380d96015101a42603008005103080d10007100d19004800c0390303404064803100c01409105401003080089400c040c014501981142000341d000d5468068043c00a8028035288040c0b1503c10300349400c0ca84258401c80c3c002c5c002c040c440c1c4403507041030015110a602608103c10440900c03040e43c5001c05c41014a041c0c00d411700b8801d600118582c42c00b00c1c0b0304c0742400010b92203808603501c0740b03600b8141640c000c01500d4207e503002003100d0b00c0b04062002e0719070341c004061200010b81002000c0c0c1d44801000c0c0c0003046418001d142c0e41e03816982c0d0f40c40c5401440360445400100301c040f080803a1031840c1c48071111080b800581008034252000d40c8034002240c90a810444103688500d81c4081b10017800c0c0540c0c103d041729140944415851610740035100d05c0060342500c0649403100004081211640170390b150500842010041407 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 585003336 1250 585002086 585002111
    0x102120a0f0627050a0c020a0f080d11031509040206091207120b0714030108150402030a0b0f01050310111b030d1a09090d0e010e010905030609010b120a03021f020d 72
    0xc403820a041405810040007504407242c03801b03903040c4400240d00905410003191905440d0000b4680100c80007003080041d44d0345514140520400d10701080506a643d041140311220102c0400c1520f0340030303003420002c0001680d640d00c1038940300f50040da9041c0300c0c001c5040965003401b64a0b0080b0003a40c04c168410001d0000404032a44154415280c100410303001169985140c082449400190351000c00701c69168811003140030b40003440502114412034003a5500d010b0360504172100500769891100400c910310741001a072502c41003800e4202701c0c00041e40101a40c620811000a940e02c404180c41294880c04008503101240058010403044540c41810400c1c0c0000c5c450140c8a5098500440d0303854401081148141004e600c038589041c000d000156400b9516101127030521040d050000340c291000c3c40f10354441d00382c40d0000650000e60004000008040358030081807a4401d420f03140003c0e8000950340c000b00e1072800d0341c4900880b940c0e030001c080c0c412019038410103401d1090b80d501d40d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 585004586 1250 585003336 585003389
    0x2030a0b04050f061006031e0c1206090b060904180b092104060c0303111e03040611040509070804020d060c0e01121104050105071103010c050a110102120a0f06 70
    0x5944220300351811080c1e070f40c200c155a024190b5152403009200d0740c00708012400380d4000116140301000310741c01454468110402c030b601401c0c1050108280d54000300407450340b4802c08020380076000d002c00c071b805828804590540115901240529959034400e50880320305290104081d42c000030100d06403402040c0d96480da400c0c0c0201900340c044040d1508086585542980c098906ca9503480c5500081500d0440181c0b55208040110311400c0028103803c0c004004c48555090700c0310b0180340d880c20a0300d0300d842111030403d009000c54000380014000342d079555201d036406c000c45143c0000141c0315400010604200c12000420782e17850a000c00c810740d0340082c5402c1d080b000c00d896040c01810080d40c01416204c0045461102c443c04000511080d8000e00142084901528200d02c0030340d43e010200e8210f828078020b41003c98004104041c601d981f203290101d418910000070b60030114281c102c14545040600340d2003603591110008041c074015644038038000c0c507400079042d1210101100a000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 585005836 1250 585004586 585004591
    0x5160c030818180f100510020106081c090501051c09140c0d0201020d0c0c0f08030c1006180b06370302161103070b0d050a0b10090911040302030a0b 65
    0x82e00300d001c0c02900510310384010507102c00750400800e20b400d96a809542280103400418a5910402e0030b10b0106a0740c42d0881c0000002c1c0541d00001030f01810b00a600e8130b421000c070a9450100c5241440300480b0b5800700001040f640b0a0a080f921604c1d0056100e0310613403503d05200d50300d480c0486100078024002c00d6064091401010350741d9101c510300c02c0c0060a0001e1401038096401017440e03100c0e0522032a00c09010901812400d8074154030740c10342d03001101d044c2d80024120b07031022a07450412903051004d07500d4401505000c000251800c8103022410f2034410662084650300e096031030040d11840e0444626a040e0b65000d1100c0114200c1a8032400e082844004204014003c50819900902c222030300c05d0a0040601030940310f591364003001c4070300c0c540b010f5058047c520b000070f0722400d003030068640a1011200031810b881d0151128003214004540d2521600c004505036440d282c2240e000000c1c3c0310f09202c0840c00214040501245104950009415200d800f0b4960203100d40901e0050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 585007086 1250 585005836 585005857
    0x10905010209040507030525030216050f060106080906010317190804060f0605130e01180309080c060a08150103021c0204140402090619180e0604050c0a0c020105160c0308 75
    0x105491700c4008800b140c0007100c0313407446040074059020003110454815a9218020320f409031a081c4511486420105040002c50f0719601203403443c012600240a180e026203403a01d0404220f19240340020340d03032801840054086010503681c0002e9034014011034150b91040020b24402c143c0d41701004162034002c45003a90268581910680440c07000e0241c0c0003110350060501d00240300040c5060b00900c05406038421543d40d450900e01041c03d0410304540c01d40c040d07110302d221149411095030421b601c83e64031a201d840100640b5032086e0b08007800c150445030401c80181e5101c0d4600069000748640c894580c0d07882030311100c4200c0b0b44800d800820559003580c000c0040f0400325400d00c0241e0140c4280164450401c5c41188200800300404021801d01490100240c1504946010140c010342d08103000780300881d070400c00182014001d8640007419140200c1c07414421120003000d618036100300a041200001e00d01c00c8454070440c0c8000015084005031102555030318040450381d00000c0c11a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 585008336 1250 585007086 585007091
    0x11203021002090105040308033607080a150c021e0c040f06030b06101b0b0609060f0916090803040605030103170304080403031202270f0d020d020d05030c01090501020904 75
    0x81c89810540c000d0b50076074201a100d050030142181e555100031340008040b06044078903880d40350b9040c080304409868010310f81c0940c4201c0060904a07500b04603107504001c48941c0100c0c001c100087c4035603800b40b110300b101c0b040082c2c24510110228107004480646c006500b0400100c5045544080b410000d070800c103c40402042403815548410303103505102c040c1c4480101f20009241d800c140440c045c0341d0082d40350265010003140042c0e0701c5a0200704d41603c0c0c0b40306c080c1c204174080c1091640d640c1c10000854124241d030516000092120b00010100c482e0380f80345a01c0d104001e806100301d2005049e01c80140ca4032903482c0e080007042a0000d20041d80c910f034075010509042e6107034000f128002d64012885070b02e002e04644003500c10a501d82080302e01d443d130030413911406011250302203459041c6010300d20304d0102302c68104644040c004141c584036061015004005a40700b07598074014544c15240c00815501506006046014401c400d00055080c410024108072065004241360441250704 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 585009586 1250 585008336 585008353
    0x110a02070509011d07022536180602030f27060a15090f060f0f051c110a0f05030601090e030a031a04090809090a02121306060e01120302 60
    0x10050319910a21030004c0788501251140909003020720110b034805942e004035880a500002000701c801107808200c9030160056400303202013150008102d8803280000110a5000041003c0c8401c000d52035011904040d50361885d05242c002e4951000c2c200f80d00513008540f240381c0400e07826440ba400312a5011a09481c13034a01c5c0c52002c110b9901c80c07051488800424560b034443d0340c9400100410100003130401d01740c1100040602e168050350364110041741002c04d40c40c1c5020340b40d10260703860b50001000b00c011140e0600c51074680800a94000180400a01030706c1040d0610075032503444a001103400150070325000ca0300044140d1044213740c800d80031100140c0c4e80d9a02d407800c445001d542070750940c10030088110380610981003d8440e6803820130b0407001d49030700c80001c0e04484008408503070003100482d900315135103061911558040d004150551505400442c4003520510092807902e5503404070038550140b12890340300c10060000c43c02e102c01203584600c1151500c02c9541c00442c0184a10b400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 585010836 1250 585009586 585009589
    0x50a0b010512030a0807020312160e01090605071b0e0f04150507081503070e070c020a15050901050f19030902120a030210020c010f110c060f0f011a0904110a020705 72
    0x1044003030ba40b1080c010f18144284030400710340440001c0c0125045110501120910007407003250140200405900100c041d0214800540450f5010107224180700000104001d59900403080b00c0315190b10039080440c5080030045c0b0a02000250000c00141d42001c0410070a106840f405d64021805014842ca104804480c2d070001c2c1c407030407100749000801003004280442100c5481c079404120050a60342c02c141c444900d03501c0510b045070644002000520020300354100108850050a6049a001c042501d0710802034098450700700003604020300003503015100150102521003448003003941c00220014940000d001c3e00e08408240c0c0b090000c1341c0112003080b40003502442e086e1b41b5030060301c4017040e07001c03c40c002900206980c80703d03952a545808920305061003500940840d041302280c840355482d03084c81c94040c0080c00320110f07134400018411007010b00c0461504507a44100e40c000d03085200c1c140080180585015241c000b030070460350305a501d842c00040c085000280d03003221289584d40c3c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 585012086 1250 585010836 585010849
    0x615020f1b0f0609030a0212011e02040b03011a040e070201050430050c010b150c1204140f060403060f060510090302060304121107091505060906092b050a0b0105 71
    0x40c01c0d01e50000141c8072584040c1060406414645001419590402d0300358001c509011402d400402c40c2d65941d4200703400d00c104160441080e4108180c0c2103041c00d0420500c000f8600c4180502d0000720000c2400088504c40b440445010b0308400722840050300b003507c0042c2c047c00342524201d4003143e807060320b003500010a0303410100c0c114500700800690702c010303542901d155104440c40c3c0314a54031041003a0b0145c4542041540041c1014002651400091240c1703051525800e041312020601700400c221900c1402d03024420504c04864421080400c43c0010b41e89205941c00200038900b00750b08110005010f61210040383d106942c44484039900782021500350f10b050000a40c000414804140440c4405001b4095401c003400c003580203070040740d0f0503450407060350320010150361511003103200d60fa030107000f0100400084da2130600b04203800700007520a01a02d0100380c01550b40b680c007042c0814810b41c42200707043d41c0c5408002420300d00e083ca242c59102e41c04080d983c076003010f800000c1030f00300032 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 585013336 1250 585012086 585012133
    0x18150c120b0f0d020619020a0b071b080a020a240f0213090902060f070807030e0301060e16090b0316080f0c04170f060a020309010b0f0307180615020f 66
    0x2c000c40c0311005404100b10314a04501016600200180008200040d03e4001c0000303001c0c19400600c00c1004520704200400d00081404040008404149a031022210540ca01645d03100d2175090710b50030080c80403881e200e0124005001c2c4040c51008916045000b6041c28804804800c140213000d60144020181c1c0b0a560105400b440c1010003003015244a07405800704c5031004050510308003c0c90803041c0c80340c0206001303a420b00c80c00100c00c0c0405030007400405085800760000d2020520b00b80c10401c09120003041c514070111411850220184908514006040440d03116a01c070308040e07081c0e102083c100d010041c041400720000c034601e1605002200d201e5441100c00a1a103818941d04600c55100700b25080f0441c42140305003c9503a43c103101552107040c14000040e01e03842e29400c00c1c0e0a582c0071050700740c01900c00301007c0301142ca001c42c549054441c140e00000c00074603142075240050481ea407121103141c40d50480712140641c0418103441c0d00b043c1c2001c5030003980c41600c0b032114040700c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 585014586 1250 585013336 585013339
    0x30905030d0606170415090201030609050c09090901091109040212010c05090315092d0316060c0f080a0b01020f030313050d050a0f0806130513050d0512060418150c120b 74
    0x189041246180c1b40ea08107080c01c500c1031401080840d920b8907030300c007075078001e550b1441989000314094041d0304201600a03402100e19009000c1c2e180a0b460780400900c0c0e400d090b500402c0d01c0c42c00141075440b40c035a00da0809540e10001c102650b11048010150342000c44041d11a02582c3c402101095450582c917000340c400e000a400500040e1a00520342050070303114401080401d01e8031580010180702600c0c1e4030b0b0f944517085024038094035106040703a01040d03030182400012620040c3c82039101d4400c40d405442d0f1030b0001039110708000142d14018030030081410b28400081000100700601c1c0d09980c10302d210b202200c2807001d501009903081e010f04042c200006417042c0a454100b807141065580107440641000c10a0010b03501c124155001125030a01c0400c6d00c20b01402044002c0001c035801101600c1d1490030006942919030b00707103101925a600c03803070b19010b035404051841040c0950700da030700568190034850311125020103019212422800300d1150b030031510500340140100e041d01e400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 585015836 1250 585014586 585014603
    0x1030b09160c0b09030913022a010e1b03060105090f0a0f0f060b0a02070b040b0d0e010e0114041106070b19060b040902090901050a12030c03030905030d06061704 71
    0x1c6400101c0030440030203030460200402028120003244101c48a1030107049507070061075440099500303103e012103130810407940407441000400b5441414070b08200524059000c46010490b07005040380c003600841710580054018241441c0400440000300e8038544425410396045030381c2c0d0410803500500031161a40c000c0316240004407651410b91020300310b036141000000ba61490a940138040f185113070813104000b400020041c0d4807030b4042000030010300d00640094502420300d1480010382c000c100310b03054207584a400c800e0319140e0079004031381200d103003000801002040c101c0d1501c10810a54081d42ca2800c901120341e4641001400c554a0340c0c4c00c107442c82100c0e150a8440d078200c00c00780f1140011640d6030030011600308110801000200200500542c4030030140040041030300040e48803500c100900b040c200314500d00c20144500c0542c04d401c19080d42c9a46080035805840f070700b607000384140000194821b07080f14992009050300c141d50ba420250a5848000d90080e0106880c09442c000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 585017086 1250 585015836 585015841
    0x3070e091e100501110705030a080a020a0c030b0a0f05070909021e0708030105100207080a1e020a080601061106150d05030f0304050a140d020709150b070503031f0b040b0a2007030203060601030b09 86
    0x1440705009010126281c3304807144210607440311090a440e540040b500340e20080140403c01c031a601032680e002404103801c1203181010078000c2d0801d03103544035034214603402181c2d0030f8800d142c05c01c1100381d05116800550303656529140c43c8500364024003c840c42031039003e01d0f911402d03100103a80b005071525200200b0030324081d62100719401a00d06400c100c1c03100507040e20310042e100e81c00300c40b0007044039600034003542d410543d000e0704030780034550420714982c01803080109150390007612850280e4107903642c0c01c17140f1150502e07604511540c0d202c00f0358240c00005000070041c000411481d4640901200c90310001c210340e99540740e500c00c44504005a10040c02445146980e0f482402142d241940d01700c074040d070312a8400c43e00d03000303820140d68681010080014125041032a1404191204400b240a40c1400800b003124082c3d809528901400070404151042c01207400070302900e110b20100e248641d000300301965960250000700e019005200115910b0350083c0611040300c8001421754000360b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 585018336 1250 585017086 585017093
    0x121f060c1e080c100e0c01020109031e020c060c070303020610051f020322030b0f16030b040902130b0102010b01050906070b040f0605040f031403070e091e100501110705030a 76
    0x41c01580c5003540c441d0070411002100000c01c01c6034505800e401030000c900d0b500d1001c0072074100245220000d040d6414900d050740040c5c1d200c1000c203410300840050507004090040300300c1c40c04488a1031070350441c2c000030360b42c03800c0c010000d04001142d1113942180c0140c0e543c012200700984040c0303c2d0700d8001002615201d5100c1800d060307004109031a20460b801c01e1aa5607210a10b854020b4444442500d0b200042c81400710340f48400d6400000480000e80600345000003032600c440e103030502030406940d805691226501e503007000c80d006400400001d01400c0b0510700c0001014844840c1d0b01642c41e1018002c1d09500a0b81074402c06000141100d04001550715020460700b0b005208940e40d003241055440020b0031441642d0103280280203445040c00c642c40c0140201c9081d607202c9201400c00c1c400c000c10a64003400c661161a003e03a49640356480701452000040082c440035407440034110100601c280c800c41d1b5a40c02c89409903603200180058151007a100c9141c0e010700768140c0c10580449020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 585019586 1250 585018336 585018383
    0x803040b09070b03061003291c050a021201180311010509060108030a0c020d02040e0c09090307080d0c170a1a151e1b060f060108060f0f01020102121f060c 68
    0x1143d0040c140803400e03900d0f401700c0002305000f500c0e10b440060031580060b082800c144005400d00fa08000b203003000300c509070b215542d40d4010140300030b200350302410a01108040030341001c40c10101003500c00c41c584980d40b6016050f080c0005085486619020004505100001b0024101d074440b501841c9450303041c1100311116000580c00340e0704888020611001a2a01d102c4d251030524008040d03c0d00854840c20480340e440c1c0235003074103950b070f10501c041d101203124141201c0400a0403080060407440c44101950190701015401540c0c00c3c0e040100a120780e40741e04120840118030041d5a50850329608016036042e03d95140e401d5a00d0600041010043c1110440d94000302c08004606000510b600da01e00c40400f0003003560780d9000801805034040f000318809030000350034201480c092800c400401ca0700d1403041041403260720919120070041e4002c0d0f0403a25002d440310564805441c000380d14290003115450003c5000b00c084c0030001e4424402c1681b8001c0035800007503030301c10100039800c500b02c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 585020836 1250 585019586 585019609
    0x3140403120510081e1603032f0303090a061b0c061d03040801150918020108180a0b0103140601030302120c010609061d011502100e07120803040b09070b0306 69
    0x70040000c14012134002d03001c00412414510345004c040600700c042959504100e040020034405d016201c00520002c1c5d0400c004103074120444070711000b064107203002c10050b4a24500c1c00c111500000050000c00c01001c038185008a020308070503c02240000030071100d2000c00d10920000803145401a000180f1541210300c00d8000240c02850000701c2003202d0f41903a100d5030061160740c0d92500d90044800c41c0c818260001c00240204015100f520f01580d450a0200b91009040110410000369040085041221040810011982481018070380f000701d0103c00e010542d902c01d1480700d0b0480880b030000e0040d040c1d9a0650181c18000301c4c803810745007290000114441c070740d52500004180c4124600c5003a005000c0e10b1102c103011070303c1030400062240b06820440020340c2d10415199580d030001071070b90300d81c003d60400044040b02c04a89506080c03151700400010700744030711640180030f6000046c6010ba40a400d43c9069510344920319903076070104d88150354009809100041052500c4c1400d0792 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 585022086 1250 585020836 585020851
    0x1602270603031812070b03090a060c0c031e030609060906032f09041109070f0e01090b0301051c020607060204060f08010602060c0a0216170c1c06020f1c0b01031404031205 75
    0x1409603481e041c1d1240180c000308d40d2070000303511055401d0180403042c003685181078070728101075040100c69200200004c4600200d00c0500d10781c0036044038001c7c400c0c2c0c0028000c001d00c8804010b841e071603c800c2c00207800300e480141d405141e500c400d01e080080c000400e8000782d100c030523206140d0f070316201807100c102c0d0001c20503101200c0a03281c1c2221601c40420b140d02c21140ba41d906015901070440240001d208122480d0410461a505204c1100c3c410300712419108111030000d02d03200241145c942c40c40b04044000c2d001403020034080c007000f000c1d4018200f510090f4541c00d00000045c1c804075610802407061800507844200403404e19018040180b01505030f80c415241c90030398411014419001d9031f0b000da10351260b01c40f030a00c2a90414001240c54000c21940700016442c00c02d2214202020034901800f071640c001004010714003804100ca00f5818099a50841d0b41d0703400400d08000d04107400640d02207802c00c81011210552802003501c201d40c10789942038202200d049410052034001c0606 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 585023336 1250 585022086 585022093
    0x150301140d0611040e07020d1709010f06090b10140306040f09050313050108071404210b07030f0f0e060a0506061b03031f0602121602270603031812 65
    0x20340100d042e5000e00d02d4a80c1d00320903107507641c81c0380c21902000510001c21040031508444001c81003039034050b07854104000c000390b480006899a1110328014511148058007151078075900007084502c642103104001d0084442e00b010005088060b80e01c000d200400c1001420108006050781c5060f520103012156004000150441c07036554162865121080c1820701a140000030010f43da032016035180c2c4840343e0318000106c0340c0000b6090358903001700d00400940603100200e02c1342c00d40310141c0080e040d5411415205040c1810341d80030f001001c10703c0782c2602003800c26000d2140c2c1c01c80c600402046440050080c0071030780d9092181d000800001c1d190f0781e03000c40101b00c8003016402441c1e44004081051020350b90300d05020701582a01c1c00010300b1000400d4034000200003c40e00407a0180141d1040f07000b850352071800c50428049020f001b44000c1d4003070100d1035001e0b0310901038003000c4000d40311804140025120304007015568010000c4181d04103c95450342810740c204888907500120409045 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 585024586 1250 585023336 585023359
    0x3460302150c040902030a0e0106050328082206030614010f050d0f0c2a020a05061303080d091101020a080d020c030712210c0f080405190302010e070515030114 70
    0x900c01179078403c1c0c43c1104400e4440680404002082c8948401400110018107501c0e4a03652040c00681ca40801c844245070200305034010304c034418003100c440c040103001610034418011003810140d105030042000081c9480004646011100b450010524050311821a442c0490030b0448042c1d01061141c800a038551010300c90b590050b018074100b00c03602d80c6481d400c940142072001c03d209070300e2202c1e21404440c1c130150001343c2c032240b0a01b03050381c9003690416950608031080c0c1c1280315081d03000800340040040c22402100c1903a20218005210b00b50b145a4880907000499070342048010240000e1800c10400702e110360180d00401e941d4013100c0c240c4e03061088944502c84500c244201d2000400d01184440c00300c1e0308045c80440315904128410009404881130042218910700c6040d014032135060003090612008200000c008006100c019072201054500203020f0441421030141034445c0440108480c0b40401e0b40c0741d1010310228080382168642002079026402001080345c20030443c480 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 585025836 1250 585024586 585024599
    0x7110a1505072f1501030b0f060607201305070207090e010b03060c04060e06070f0f021c110102011116080a1107030804050a090b03190203460302150c04 67
    0x79a508210124040d1144405524200c07070600909081005013400607400500000d64180d005d00d4029554a100304144e9980030f000c15028804c03a0340c040c080d200742c01030201044c00c0504501161180503110b41c00341e801c0074a1a03e05581d42503920317801503002000c050008003555800340304120704280004c074142200d0004a414140288e641002c50301e800a0180000c0e070304860483c000203001e80c3c480e4a410140d4541501c00c00d102e0703030014a810700b545000e10555480c01140104d01d03032150746028000751145085200088030484050142d4200304070308100816020513914410303443c2c5131900d88402c0d113030742e4008260300c60548001840f03038225111084a108201d100085c0d0311484907aa070311401c10080040880301640052281d0b0b0900c016210f607520301003203003000d22007407140b031075054481403001a04028504100000d41810003881d0300011a41d5a0700343d070017a440c003140c1c00040f40c125074080022442c41c03d024002d43d01010780c02c0d980c1c0858800c0190b212086122660a0948420 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 585027086 1250 585025836 585025877
    0x907030b0f061c0501050a050a1a12070206060907020106050d020603180303010e0406200714010b040507120e01050705030612070503120d1b141602030a050607110a150507 75
    0x480c9507000c00354810350a42c1d06410f81c0300e0360340900022581d031040c0b546403200140d1900d6490055402e090940c10208a00e81c81e03010641c4c00446941d02d08141920b05004002e40c1d5400454901e4807822410000ca903440c0e006101300c806903a006000c000c0c071001d4507000d004055102514640301c02c5100e04541507480b000b400514064004030100549a0406040010942d900c0c4240c44421406444148249020072070895054580c040101c0c14082251021140100820440107030068201810000001e501034580e220f100c05c0b1010400c001030012140300e00303c400c00c44240c0003265040000c01d56514001d245800e040e10182c0454076601e45920129041040c402c0c5440710134040440d00b1011441c5600400c08e500e104840b400d6901e44001c50014450414036454403152038001414074044109151251502e070340103070882e402e10600703160044e0b68100c00c0ba518400074126040302c0b40c0c9a10041003000c0350700d400401582070850030718404d000400018003000f05206610790010055401c4330f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 585028336 1250 585027086 585027097
    0x112051212010608070206100504090204020903060c030a0612050a080f130f0509160207141c0809040b090403050a030c110d08010305070504060609030602160c03200402090907030b0f06 81
    0x300701491555243c48809440042e01402420546d01302604200340b1001501c0c41a04480c07044801041002084c00810000d06c207115070146c06010b00b008114080c000d40c0b0066005a070451001c0101c00d990f240704c110074240c030181c000e156411082c0c804000c03c1e90400a0704d510840101c0b00c2e0b00d8040c400641910516941c1d101084d40611810108490724250b1212544409080c0c9012000c1c484941e00a4942d1514055003060070701c1c03110150b1aa40325120882c42e051341c0500264950f01c214145408140c0002d19600e12079401c04040c50107904083e0328880c0120762644032142422a900001c0c6c0c0580300520602007040041d01d0044038502080240702c0c2c4070031003905c1c0d20b41d840d41141040343c2041040d40020740200c1c2404402c00c10154050303441b008490b007040c001a182d0300072615440300c80240f02341c041c1c040c000c0c0480c04001e0040c80a8852400001b406c000c801c82d00b12003045c002a80034a0300050f0381300404200040b41c1c43d009402c4010641c80040003403002c551000300090701a04003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 585029586 1250 585028336 585028357
    0x4050904111003020901020c10020f010c1d120604060504060f06140f04060614070c170706020606010e0a05041d030d0608010b30030c0a03051812030301120512 70
    0xc0c00791995403800c0c204030400c406041c9107401e616082400c030000c1c5d0b030f40c9545030b11680104011001c00e041c1502c00c0c0000162414084000c0c0401e0007105001007030484800e4034101d07a0b591446002c003052800348259080a410310000d0710316691142c46860091400400170f4030303000d8071081400c5520ba44c9100b032902402d03498010540b003150020a00840340e540340000c2d4011032600e0000c2c441d041d00012040303440341c02c80315500da55908034a400b04031082c0030b038403046c800b900c0c40c401c070900c0c4803010803910242c801c59800c8403015035030040119000183c1801031034000c0c951715400d10807400c03e5007103100c000c00301406401c1280c400010083c44c5601c00c0c40c03c966425078034581801840d1017030048800d1104200c1d42c1020038101c0310310800e0f6130103981c2065490044600c07600301004606105071140c903030a520030348081c0700d201e0038050416030007070241c42d071456299070402145182507420b0880c0b440310309009500316807c01a04240d2540f0f54103080e60140709980d04c7c4d01542201c0c00050440c0082c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 585030836 1250 585029586 585029603
    0x515010b0409050912031b091005091003111e070c1e0e090303070804030c0c0803030114040e10050a14160314160804020d080706050f13030206010509060604050904 72
    0x5400500b00440e0001340040210390000542c04040d40701d2581903940200b16841042440c401c9500b802000c3e2041b100c006400c0340818980505640d00400946001c40080d100c141c41c04134401c1048046070415040e280340b81c0c01c1032020002106070030303da081e04000c0742030b80e451410b03096032200301c80c240b1298840c8072261800d4019500c0500181d811400400603040c0e50860741c2040c803800390b2a030000401c070904015201c0e0004080c18410028003105a40000d00380c14002e803a044080d840746c4c001d0040062140070110220054140b910410510f042a040a0700003140c80da0002070181c54041c00e184561601c03441d90500c0d43c00c501c400c40d40695211000f10354140107401002d01920710145c2d0507030308140c41408001300d26061700b5014800345094504801140da440c800940356504a0178060148400480d4110400000d42d02090140705102d0401100e07668203200700c01100c172034100050040c3c02c000010000341c03c0c2202d036160010300040146003011b49a00102d1102101100c00b82c69680 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 585032086 1250 585030836 585030839
    0x1003030f11030c1011040f030615030803040f0618031e2a0b07030624051b010905060105031917070501151d040816020f1f080901020c0d05070515010b04 67
    0x48440c400c0760000a4017000042c242803800c65040494a01444094040703902d900c10707442042e00c010f9500c0041e527406401ca64036401c0c94240f40345090010303a800c40e0311615282884203a4103461144050b15a85581c90031010441c4400c980c020081c000503150a006c9841d201d050f10700401c00e04e01c2c04200e03e440004860b50300c58245100c9542000c1c0840d03043c186003d8041c02000001e00750840e0380000c2c0f9010360964008000c0c200c0b40c6104000c800a95110300340c0701504100d5040d001002114042d104460365a602d4004040d05c0b11244804500c0396502c1e400d5203000142c050401200d405580f1700aa03041800035250542910701c0d000e40c1c0b141d00c0c0512070301170042d9004842800c054a004c001041050f1820b940d622155104142e6281125091004100e0440d6074038218802d061303802901e555200c0100d0300100300514680402c00000c22035a80004030103400520070b0350340350103982000f80200740340014107942a07400f80740c069800d401521040107000003d20401d50003000e00c100c0700d942d100d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 585033336 1250 585032086 585032113
    0x1509080d0e04060905130224040609090b090f24030d050a09090911060309010902190518060303070311070e010f0e01080f060103060c11011401090b06031003030f11030c 74
    0x441c800d13000a40d0007454101440084003620b00c800d501558180c1e0081054900308041c8462000c0c0110003100c41400020013061195000c440c82c42199007505080c0500d440207010480710303920454100f030f00e564601c000140c1d0240c150a124581509504000443c50100320210341011400023900c070100d4800900b00c20341c1c0d1390204508004000c42c1104001c8480a5525049580c1d0240841c51040401001150010b4002c0d40040302d8030f6402010014103c880410b4a2a01d035581c1c81882e00c0340c0c506190070103035040d80c140700c9449000e0080165127082141c7c0e509503403504408010038881d12850202241f0164070300c1045019004455210301030615000c20518091300580240e015a00804001c0000e030200241480c107603984800c0201e9500020a000c80c0c007000e42e00d031a0350156007040d0302e40403907013259580141030f182c011001340030307985003207081c00510b1006a94402640300c0300081000442d00c1400000300d80901c2d45848200e600e24048824611340050049200a40200e00c000401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 585034586 1250 585033336 585033341
    0x1902040f0b0307090504030f140f071a040507051201060e0615070f05010e0606010f021f020f1204150e06040b0910090b150a0b041a3c04050a1509080d0e04 68
    0x2c0d00d00d00c1e00080c501005819860727203001c0c60075172520402d804031746942040901c0c0c03540c001c241016401118540b0b400c6c02d00a07920b40c0d4502c910f5000e507a21100c105060841030094000f59040c00306800c0c4941c40e070000b44a00000410000c28074048144480700c00190b00340041d03050f082c01000042140080c01c20218244280a421281031001c4000c80481c1a500440c402c96541c210884070f100450000010754068419000340d03444403000000c01c844c110301c048140d02d0140303004190b24040c1035444c4d60700d0000c49000c0c0503041d889034001400200021011041d169008a0441c00c3d280840100c28500003942c43c045422030b1150501d500708002800c0d0f000d81c1e130001c82c4040354418076803883c0030203102e403600c00c50040c43c4100d030300d81d0801042c2d0300c16841150b82c140b03418100068480c0c1d005012001c2c4103080c16000003070404601486800c1941078054030305a80e00200281c024501c0c00e5400c0701e001220300c0c1c81009210790180e00083c03c040078064103401010b03944480301c040350f0a4042104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 585035836 1250 585034586 585034607
    0xa0c0204063503120a0504030c02030601120512030606040b031506041403100507270b0a0f080c0406020c040b1c080d0b1c0206070302120408011a031902040f0b030709050403 76
    0x34194801d0010744ca41d118a1440142c001c5051310b000035690700c0d6030a00b1a8850819000690140300341000011540004c205071102c56005000340c504441c116125208140300650b06640e12040601003401900d60307900040d500824910a00c0039001c080c1c030003058030360300258407500403100e0303032065503810b0705040c4800890104044020002481d000c0b0020740440100000300074508412200d42000140302000700001d80004c1781d031b141d210102c01d40004c09441050005100068203403011174184920035060350241c40540c0c0160243c000740000380002000c2c0316008a0740038403904411180d00c900e005500c0345090181341c803d540c1e00d50810550040d2030a48642900401260304100d280c030b01d0107202144095811212a5514905400d0407480c141e9160b08005921000040c0001d080c1c00540c0110303220780d0059401106003680d0001c06884a12048010301c00e00c070090f4003400180740940c042d04489240c1000000d0308601d0b6004645820419044000d180c3d68400c00c0c08103143d0418031064 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 585037086 1250 585035836 585035939
    0xf0d05070e0a0801090308040b10090e010203070e0d050604080a0c020612010f0501091802070305092d0a150f050f040e0402040612020a09021804050c190203090102030a0c020406 78
    0x40d020781b690005d055100c010000f8000f2500075012500b81d040c4203201d0001480c1600707041c00010b03010404203000b075000740d5402000c0f603e4140c002d0390034142082c0e10700005170808050189551261501c2c051a88008052000c122840c1d00c5880180d9032030001d00311404507c6042c0d5030319810040d9180c21158150462414800742c52410003464080805a095070100880c001d80c40340294030b0103456a028411486034400c85509000e850355203030031612514010000a0860542c00b00018400200d6660152000705000001d0a55181d401031110140759065071801c10319100e01005440e005400c640c001121900c5010203000039460140980c2003cac054106e49402020b00d9070f80040d118010a2103002100354020030048810280740d02413410303007500680103000d40d241008072505940c2c0046a0b1b508003882c0c101c02c2d0850640b000060328050130040e0011481e01080c4101521900e40045049901507101c01d0046000d03e2282c0d0110840d0708078048003241e4050601802c55002c41820750300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 585038336 1250 585037086 585037091
    0x10e0613030c060b120f060609150f01020709052701232a0a0323010512161721030402060304020f0411030a0612020d080f0d05070e0a0801 61
    0x84500314140d96100315585424421500c8106180080c0a00b81c0400165406041c800800c3e01c3c5500203e003003500c034485102514403179551407041009284042d02c207058050032200502405091058112280003014011074240c6503071a050201901c1e407c4840c0301d0003c141d410440e80342100e00d501050880b00d900001e021034085900707021980c40c1e100740000c841e80303c841c010418401385e542c5425400c1b035940d00b41440940e0110700c4480207600c041c0c0c0e8100003900d4603075080d10002000015800e0100034032400034440e40703040104440c4a401c08465130280c041e0401c072955800c494110f250003003503040071034101d10b2802c1c45020306000300b035200b20a240d41200c00440300b600380801281d07805581180d0058803902c2d640042003509441c00503444d04940340c140d82c41074407a00580a0b5116041102003885055190545035100300703400300b0000d4008441300700c00c00002d03a07810040c0c01403030800c0c41d07840d042000c0089100d058410940c1c0b030744007040990074543c03954180160b601005d003203442c1c001d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 585039586 1250 585038336 585038341
    0x20d020706020303060d11060409090f02090a0209210f0304030c030209060102120d2a03051005040b0603040b09010207020d0f020415121103071503050105030d0804030f030207050c0a0b0705010e06 86
    0x114040b1003011b03c0080c148501c58140900301c0d540c1e5016180605082c07003007042a0382c12468041d106100303080c021703442035440da0700244403010140220740c3c044201800c211710400800307915101003211403012009500402d00311071445001000030f080107500500011408d0707441c6005220307007100301420240c11500011115403025442c5411100020112040041c0c074004452444001015049d0390841d00c11801da540c100855054203e280500c100c0b900b102d504c1a515020041140c181105494004000744000381c00b0402a0643c1940301c80000000741c03915074154001400c08034100e00071260041c1ea440c080e001d41c10b09201c0c0c000c005401d014000c4004d410b024050300f0f10b40e41e4450042c4914070410080c1c010f0344060040f00c00505030680c00f1074813040c01103405005080240195802441f40001030101e0902c07801d0442d0103903406803559028010035083c00c402950240c00d080e5954407030001401240d4507a4105e240040003030803d00750701c40010340780ca82d00352140d600300c0e94080d0340318005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 585040836 1250 585039586 585039589
    0x405061206181e040201090308071a0a0236090115030e0105040c181b021e06042a03081606180203100926041a280c12020d02070602030306 61
    0x52128244264901d00f040681d40c610040703c454116401c003c2c0300b0140421030208000603000402c401c1c08010403810010390b507100c0c8107002c078090060019007007604060b80e00743c54600c020402030000e000c0c01e01220720707500c07550202d0b00b94203080e8407041402104800b0f0284055243c0300380f48404003044000c1c0403030f0420b43c030344c10700c86201e0380034040a622611480e000d0120380c540c05103103409c40c9500440c0c032200071058040d4445980040310b8058854412103600d03585404510700c0d11680d88084600c5102d91070141002062500c00d030448480628000c010020600070300203401c1141c0d022141d40c081c08168601178042d0b84005910b03400c40003880c008100140d802251a640d0310941031000a9800001d0134a000103018100000040da00b68503464100342d101c1c40010001d0390603d2080714440010724041c2c0b01c640c0b04510b80c2e9080c203c05031000044103008800f080b02c11241e2031410840540d0b480c0c64480303e02c0d540c003420501503403003015400744103501842031100810190000e10f04602e003010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 585042086 1250 585040836 585040861
    0xe01050a0303050c0a0605010303020c033007020a090f0504030908060f04030f09030f0b04030216080a08090a09020d0b0301050c0a02030702040b0d05030a050403031209110f0303040506120618 84
    0x90034001c0208402007818000c008080e480c941086c030501195075a800c020703440d040b08031110b07170180c0141c0008154089246002c5002407980c100b44980d10407084003c0f5000d90000355040342d021208000005440381c007401460341804140c0e10015050030a1b140240c0394100c59808008943c00c42005c101c80c04451001440e8800e40500303003000e199881d02c5044900160a40000740300c40078046040c1c040c0031aa540030351280f44a5002c0315400255417500c4659510184102d800d03039400031008200090100c409007148410141c00d01c04a0f580741c030f4811040c0e82040c0c006006065664006500518090080f660032000d045440c07403901215407402501c0e44500100603020f141c55048004964950f18070040401c0c0d000415607840e481d41c104000c001d80d04c1407000743c0000d08151540c001e1061180319860450358021459482584c074401070001c10000c0140581e490f00090000080380c0e2030702002045103060002c004495441c111041040303155400040924805d11441045694220340 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 585043336 1250 585042086 585042089
    0x50d0b0f180a0609061113080f0613030c05030d020307081509061c110d050d1107050901030b0a1b02010b040e010b0105070803041104020d0905060f090304060f090b0c06010f0e01050a 80
    0x214049610501c1d82011400f40c6506c014141480d000024481b0a840384504980f060310b0007442600c2c00d41c1d901c1e010280c0d446078161100400c0715010300e12000083d00424901180c1403041042e241403d000321809412600200c3c3c10101045405042000c2c1526021070301151100440324200b250401001140401d50000c1d40301c0d050716412504041448440d40300b40c0200040100f03031100213101482d050340ca5041101454000c220390080d030219440c03011440e2815128003401c4403042c0e0f07196803036409070320001070049889550f84442c1c0700c1c200c9a1300d516076014030341e0075000494055580d0043c0821100908910400e50345058680b489a0f82d005084076051900703d40380a459841d03070300b450004001400f00490b0301910002e00016645c125400c80c8214900510035501240d44165440b80009401c035000c090507041004203000c5240143c20492000c031203450030b141e90355100c100b01c250343e9100c1038074904245d019000400406078028406400f811003540a111594502004618007141c076 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 585044586 1250 585043336 585043343
    0x181006031109041509020a0f03050106030c090c0807030207020112090803070f0215270d08040b0106020a05060610140f0301140114090103020f160f11060a0e120304050d0b0f180a 78
    0x45d0b5261005566a12141c100503141c9603411241c015541d25040e03000341200d2004480a5200003400101c0d07074000d00c10f101e601c1174143c0700e82c103440c0d4a00200f107000b503025900490600c0400b08894501d040144100308180e4825506c0700c6e501c0c2400c0c44042c040101d50006031046511654503020102842c010f402e8000e101e00056141c01c250380082c1d10400c0e40e0240c1c400040c3c1c450003800d5030b07a1550281c2c20b140240d0246407141020398803000c04036201c28207090050302a9103e5000700b401824850410210048140380200140200c4d1095030784d540d2100c00341a1040c40040018004070400012001c0040024288a03841c0b9030711001840e0355014044909040c95800310740790b00040b01c8541244d05692106114001c8a001441e01204100c030001c02615640100c8401000d6804d014086030b4402d441529400400741c408000c005c4050304860582400b8001440001020f884da600c000c12040d1041032000300034a400800c0c804e0301c2a000b409003114a40c180003e414454001c507100100d11340 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 585045836 1250 585044586 585044591
    0xb2202060d1409010903030b10020d200307060902041a090a0911060712030b1507140a050111041406030415051b0f0406020601121205031810060311090415 68
    0x6110115000b803209125084004100b1010845442010b602000c01e0b10b10a417403c000850016040c04158010010b030000507a01540d11890a03500880150b8112207000e4448450341203405007150440e00840750840d01151507010b448218909801100041101034007408011440c42000600001c400744c803251b03000d50750f14944414401c42618885074420701402c4140c3d0f40340f0610307204102c403d040804100083c47c0c01500140c921b003e80e2a4101300807240e040342d08000c013b03222118001c4d64240c0d14000345c440e4400d60400200207024610040c5c2d0b0143c0084d07100c602d0700c604058041400c0304030600c121002c0040100117164441d0030340301003104040028903556041c8130035818803024070140480800c042980364450704400024401c4d50700d41da00343e607004e0342c1c1c5014001e80304104007030052000406540c00200c45118002840c3c0c0132402110031051016410b0100b402d140400b2004104a070322018140180050010004d000d0801a00c0203602403600342c59145041c1c0d2505000403d464 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 585047086 1250 585045836 585045847
    0x20909030304031704030e0d0b0f0a050708061c0c0e040b07090e044206050306090d140d02040308041a0339040f05040b0303070507030303050a0603120c0b220206 71
    0x14491f070820f117005140500300e400c07014007605184829000c22640070100380c642c84001a5040a640500780c003405041e00c41d00c0701616844c080001000c56405103864020b0442c1d0044082040d042c00790740245141090300c02035090609003c5e0400a0042c080424084081e40030031072864100003555002c3e4002d6030003840a903442420903003280100c441140c07000100c111484000d80c100307410b101800100402000002c1d51002810b440381000ca400c841107410620b01c600c5124054003403654444d00b81d9a00d98607080d42440d40504a0708150001c4d29044000315080c400e0448254440c0b502c400205051400c510b00602002c000c08818800031100c1464010343c40b02c683d000c050103070061064564440d40300c0340c5a45805140c8a818840c10744901c0c181464120039040200c12600c1c01a0414090a40b80d8210b8401707602901c005003150384202c0d42c84000201041d4454041c500118443d42d400d11051250b00304040c0112000d007409070b803108041e065003902c200e511215540c041d41038030900e8994 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 585048336 1250 585047086 585047093
    0x706023f0604231e090c03121803062a091c0501020c03071406070f0f0e0a051c0201080114060913090503163503130804060507020909030304031704 65
    0x10091000c0c0f28140d00c589809000342c0d0501c0d0702d0104207038200d84208007200c3e6902e00b181307955070381415030964041e0004030f032290f140810304004000c58040c1d07040c80307030682c2003d00101c3e18104046810b01021201166005214481010500608618450b03020300f801c2c804400505408444c0c4a0351001d0719203a0f07111001c11500307406a4005464440a69484074400d040c0202c0c1d441901c140d1a109024400000c0c204500428280c056000c3d140e0740c50500f00d41d0820300341d8801d4140c91550360300208124001403035039181d8030824545442514982c203550303960702c0058107030081a0410304052041200c66400b6441d081c05903040c40b00e00300d40c0f400c0b4039203071140607200410f8191b10103441c0340000200408080306801c910241c1c1403062016050709000e445a06014ad10b48040c409015400011903802820701c240255800c40c03001c41007080141d0700340e955810039903c194024004680e0100d105415131500088195000408a01852441c500340d40c000300728580c0e81100003482c14041c000b0a081c0b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 585049586 1250 585048336 585048371
    0x4231606140a030f1b0c0204060504270309081606170106120b180f0702070e0403051b10090501050108010f140f071b030c02120c0108010b0c030706023f0604 69
    0x1034502521172020f400d0360301c036005201c14500641a40900e080c82400140c600782482461280707006903190f914650201d01c1c60480c0d0300c2d101502581005910710010403a0700c003d102c00c1c200d603140b4107910311800346080c0001d084003520341c80e4107014031381c004c004011841e0029400c404c45811404009554100000010a0302d010075103000b981b11901300821400b0395032402c0c454010003554003150519507440d440242c0c0203a0846005000883c00c4c011421540941540458142c0c0d01c8006d4400d000820b0388401c044910041056034560344401c01004048800c3c820322000c440400418011340b50803000c105c0400c60007404541a000452000840c00c500c5290701c940c2d110051840203100c2c0e821424001c01035540700100780c1c495044840c0034428402e0000d03941a291406031039021050f03107481035200c4250001404558140810040e5800054185c40108a06201071030f0803800c0039041d1303000d02039656100c00c3c04a40c100151401205040207182d00a9011204403000719010007408900c800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 585050836 1250 585049586 585049601
    0x309120c010e040c050f07120905060304080f030402150d1a0d0206030c161e0501060f150c0201020f01090501060f0603020c1e010207150902130b0d080304231606140a030f 75
    0x45198010928404100c07088c40c080c40108038555503540c5603910391003001424030084d600101001e1040000c070000383d050034042c55210b80002e2003265240340c84480030342c050b4000c035a92641c80750358411869841045007001c5003116410760390035000001a078040b0b505448080c001d407440c20800302d4103040315115910032880b081e40c000a0004104184000640d02c03c0821208035401d509104000c00c1130307400d00c403450341198094603580d0802005024260b5800ea101d140c1607046008500310000951801d0141d20b46040c410f00000030072924250400e0000c480581016003090b00402c0b100c0320509000440100180d1401d01584610307141013040d9009110304280103241d481c640d51a8011362500707500080c3d2013070003540c85014030807a0014010494401c618035950144240718140c2c0031070b030120091940030344a18094203940300c500303030181c6100c85400c1c05100903500c09041d940c1d05218004054000f0308181c1000f29424520800410350780c040c1e6000c0004042d92190104c01c01101c5400c43d01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 585052086 1250 585050836 585050857
    0x9072c1504032d2118080a0302190506011a041a03160c080d09150516021504050a030c1a09010e070b070b0406051f080309120c010e040c05 61
    0x140d8071981d07840c0c411040105800e58029040d4075501c103076603042508030660301480e84801014407948010841c3c1d0300400ba8130500ca010130002e05d802001d007040e07084040b00605607190080c505082d5034540249005030a40484514854101003080018000503045054039a4140ba45540025042c1d1800355801168090a180d441c18142c020102c034481300114085d00303640e0394003d58049201010346500c5240b50000b01081d40400410764030141a074010b2138107900c9401d00c90440c90030703082402c05845040d02d00721042e03c003106400001d590100308089a601e2503224400481c07410383c40311510340e550b400014050200389400c0e0001c010664141c140300d10040208003d003424110180360003040c030840f20444620465a020a1558007941036910b00381d84031070712010079904e0f9a501e030050040a020310300e4030f10011042c8030b404882c0031443c1015100882c01952118098820004100310402c007006481d000100c02c0ca0580c0d91260045c01c00c8641950701103a90712418504a441d4440c259055 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 585053336 1250 585052086 585052129
    0x304050f031206040507080405070905180a0812010608131511220609140d0501020c0d030c030501050604031211030903010e0606040608030f04090b01120606030b09072c 74
    0x5041000c40c4040079004403c1954108080d56920400b641da0000a440180580e07200100410000259030452540510b0030003004828801c01098649801070800085131820400f1a080c2c1c0031030f10428000c2e00400c0a8070b01101c260402c140070815402c4812406481d000303114031071408603e07154228884200405100c5a52841150320780c070200c0f25410790101000c1320300350001400511900c030046c1683c00b6204084e2190f5082c100b00700c0091a640001c0720075540034440949014400d0041c0000300c5240c0d10041860015a44000d044400503003015100382018001800800c1d204502000c0350440c50800401d12811108090b2171402141803551b810342c20050312045808012a410f03008280586040c8042500e40c044982ca902401030b400f20540c02c180010803568101d6000010080410b0600c0446031074014940010303100190095008603451301e04c0382d406410880060b5621400314030b488540320f104c0101442d561020003e40589802c035041594081d40d03508488a00507280c1d2100c403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 585054586 1250 585053336 585053347
    0x70f112209060b09060f22050f150303041508130204020c0309040b060a0c080d06090c110f0c0f0d020a0b030406140708040206070b09030c0d02010e07080705150304050f03 75
    0x445001d4031045500b00d4002d41803000d081c00b1820f124140a0181030700405006044951406020400040d000010104a4184904c0040200720b00c40c540c01030091081d50150351420441c5005c0c11100740c44a24043d5004201c104040d440c4039010110524140c0741090030f940725401d449208440c0d04d18041d41c0b0500c00101c0325480c000000040c28040001c0d1002d029a03500c000411150340035250001010903000c0c41d610700050041001814803104040000071507548480340c1c04221000d9030707039940c0801c181c00c1410005580c1013101006544580005121031100e00010400140b41404a5401b43d0220041582150303544400240980307148102c581e100d04d03080c20510003904000e61021214590b010100d4102441064031621443c4c003d03010614040701592001000341008103009042e01040c400d05543c10014011f031620905142e0022a2569441034294104201c3d507024212581c40f4406c10019a01d44114181811001c08502502c950340d40c1000790810780c5a002c98481303800001031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 585055836 1250 585054586 585054649
    0x905070c05010e100c0c170903031903051009020a120506060f0f090117130f02040204050301091416210303020708030a05100b030106021c030e030c0a05060606070f11 73
    0x8400c500864450000d02c10744121701819030354101c0301c3c04050a100c1c0510000c5040085d8040104815400502200c0c0350464a0700320640b1007000344200c0c0006522101031009450764000741d40041d0064000440c507000740300c80043d01c1e41c1c0030459480040c0da19031002031301559442040c1c5601702514100c040e5280880c440d19440380c1e0005060300c1c0800c8641251034400030300404101d10400c00d80b10400000d881c10b882e400761784150190100d0348503400f0400403034036880a0180c6880640700d140c49003078601000204901300213540c0e0703500f401d4a40c040001c00042a42c1440d445a002c90341616170f4038100340e42800c0b0f000e032007404806005c1e01d2001081c000791a01c5036003c030340b00308520420032524949070304804c509413000784640c000680c4180307040f40c078040a039030490905080d14200050b4008103d588141540c00010301705001e45c1108424506119041c030903644c2c000c0c412141c0340d00c1e0442aa94000d480c00941001803c071030403841d00d01c00192035401d401205407200c00700070386c03410380c031b610 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 585057086 1250 585055836 585055843
    0x1e0509100e160605040803030f1f031a070e15090d0512041502162303010c020d0318120f050d02040f0503010e011116020f040e010c08011505040905070c05010e 70
    0x5030410500c00e111070000030260310a03016603007070301e0500c8051465509c50640785200040c000d0051001c4542c019510109002c0016100c4001c510070081c100c1e14220a0110000180c0f00810361000d202c1d45400b0b0036100d64512208140f650200911191181403480101c1c3c01242401c800400760700ca421000c0f1034600591020300115042031038200100b02901c40c08903200d10400c524002400c10680e0b040c0300b248064403110441803103540c1c10740103082400001a00391542c9040000241c0c200b040303002429903041c0649407504130140300c0c2140e41e078404d6503052018860310240b041004014031601140c54426011507041524100b815034860362215001c5920415520a4a10961900858041c0220180980076404105104481c01c249030318119551505c00814126840041c030926021143d83d180314148080d05550000598454080d401410483e018dc20079192110850f08140915900c00d0884058a958880102e140c2e164464240c556141295004010754203104285403a2007000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 585058336 1250 585057086 585057103
    0x29090c1c0624050a140d020706060303210203100603021b01140117010b012106031b03060c11120706060302030f0d02010b040c120b0a17010c121e0509100e 68
    0x2c680364403140c000303650300f542c5601c030b080b602c1800324000d00c50300080f52035500080c11405c5046003015223081c40c00c0d0380c0c41084984c00e80080b0b001c58848603818000100c011503012203070040020441c03441c1000115420521000e02c1500304060700020300720a1421820000308800028000030b0045a000041c40b0041d05024001c00c1281000800c1860019405000d20355030b5910603110305a150701188003800c4d2075401010480c02054940e040000002e0340d180c040001c81514800310005242586070201c142e400700200e103001c0190300d02424043c800c020844070103c819117841660b5554041c0f804201601469001035454020000c24850303115000c21525224001070317000300040c844040400088801c54228100010034042c0021a20606d41d4800590900c0051034450a141d4880158811155500500640347d44840e210340c01c664003c998984d1129480c4d00c1400496500b171600c05e00e56500350b000c7d900d20b030344030700206030095024807480d410469050f005000e070402200d04580d654010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 585059586 1250 585058336 585058379
    0xf080a0203120a0e09042301021c020301050109230904050a060608120d0f240303080a05070e0904060605030615090c04030b070809010b03030d29090c1c06 68
    0x10a19908281080b95046a50424254031000b5081c5400824031001c4031009204641e25071209810741c80b590420500368400001120001d0b0b030700e405045044440303030700f0700400440090040c0010300403607030085514425254540585a1914a000500c003200780281d41010b8000361600c1c144800d1200100358545420300412041c00368540d6142c0350f83d61441241140480c030f0500340084000303400c8036000407040c1085807102192007586200c0280c01c240128071903d00c5084500f804204041e04100d0032684450701007005c001620b00200c014100030450031078180f01e07110143c0050200300c5035600010140c030018044421515060703c0c29a0728060100c002c0384581002000150645002c00403541503903401120f490080e15685c1c41525081400307800600325548403480014542c900f00040d080c0c1045011005c1022049481101740d4981c1e820303480c050251201d0090a482d4a42001503508032101300941c903a01c074041c0b03000c3d4030328a0300ba01800201d5070400d81c0010740c41d0101600e02c143c0300c50 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 585060836 1250 585059586 585059593
    0x14150d02070308420402040e010611060c19050a0c0f03090503010b0303070525150c0c091a1e0409060b0a080d0206010302010c17030a2405280f080a0203 67
    0x2a4440d44c0c07075918403000400d14034800704406482c081050302c01550442040600058142901e40000300001102608140e0000301460b0210400d8034042143c55089451070000a15100300e84050301c200030310069250081c000009650103c0a1086000000c038641104648910754040e2030010110b4030303144035944c843d60800c031036003185140110848400590100007028001c42e1844d01c0c1c0d110307400b131032513030854100d100300c2c002541e04071642c14420f605480d03900d810000c000791410807c2c00441e0f4101000003880d0404200000307004001c0c038413004c90106d5514031015007231442400648038100c0c0769038000c1d052802c2c0d0360400215070061030f14088112801c0101c0c5441d13941e4079a503040340b131040a0050744444010805075002c1c81001107940d001d43c82581c201d8000d41c0200c04c6541c01641d42c05002c2d40e40d40c5005804484643d1405041e0001c000e414180601d01000141030407810403000840952a0f00f0031291250015000c000800c1d07140c0711200c000d65902106038840148490030ba001e0302 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 585062086 1250 585060836 585060871
    0xf170402010c0b07020705041506171b18031b0306040b040813060504090b06070804090f0b06030705090a08031c0e0c04090804060e0411070602090d0b100f050a14150d02070308 77
    0xa192203040140c8060780d865482c075090b80031440c04101c0300036041c1c1c7c0b001052420b41d0030316000000e009044048801c1b500cdc4403c054074805151030030240d00741d0521001c106124010581c4d0b4040740c2c00340c009401000110141e03c442c01c06010503c6000c0d04182011107401d00081d000790404040d000301d50110708104803075000c400c03d0044030f114860005000c0513040005200c419050b9000d90203810344c91800003000c2d002d800c04501c01c2d42c010303076103080804d002155024181c40c22400c181c000d4502c64000d5424181504031500c01d071103000131081d8610352a00c00c6942243e40030002c2502d40000140709210008480c141152250b129004900c002108039200300c05504290180200d450001e8400c6803034401c00d62111070080d0030261501c0e034016100f25040001c11201029240240e040c028140c003001d00d81000d1200d0400c50358006030049014040800111490f60811143d0b1001901c1c0c00007441d8103c1460849845110600122140b0215950701803582c4164054031420b001c040840c2c610 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 585063336 1250 585062086 585062111
    0x12c010f08160b040611030409061d100806070e011b0807170304030207030213150e101706041121010501230907030b0a030812160f170402010c0b0702070504 69
    0x610309010f01500c403901003004102d00c1d48a603413508442d141c2441940d00f42520b54035920161200366200c1c03d082e2600d0035410044030980c1580716081004060000866880c00039201e0301e070718006144409000007410214400c2e40240300318072a98810001d1a07921115170b1500c0240c1c1d0300080000c1d00e1402079403038451180380f909030481c1d02070743e0150020111107155500b0041c600341c415412409440e241d80700041c5428210f149580034196101c0c15420503e00444040c40540080d440304902e11204141114174681c089411a005504002040d02884c018008100c0301035404c2c0258a1100c503d03c0b6041c1c040c9410341c04a4142c0c0d0300900740301300c5001c001646070f40a4500600381d80d402820400030038a402c2c0640d2010f010040064907010109540c0d8a540030303035400030410042d91861030760400425000c000741d00c00f551951410b081d2148055140010210031035060742001d81301004010800350380c082c401200d0001d504c40310525032442c000310001c5d00c0d4a0780340324207401a810302d02528240d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 585064586 1250 585063336 585063373
    0x180309061b1905030d0903091707030203011505090103061a1002070311060901020d0f180306050108071208070b0c0d0906091104021c050c13030308041103060f012c010f08 75
    0x2ca07800c03070015810038a0500d03800d402030030009400c13818454260300005d0350403100f40080c441d99031903002900c1103a01c0e44c0185425108031082005442030b001900f0301031507807250000b41c152508048001440c81119100b0510305d40004005036100e6601900c20020307a50000764041500e01c1000b0a848044408090042c01d0040c3e4080c14007580102400c000807a218840c03400d0100f1180c5400c0b80c0c8402505a1001c3d101d4040d0016101c2988500060105540402c4403000600400300b2400303581107243c0345c000c111301400900070700d01110390380401c0450590106a0b100403400c400b00300403a0816180c400000c0206090440d082e41c1107504000c01c0380340500c2520811001a40d803403450480a000d100010200245003021040080c081040361036001810140910b109480314007075400c241c10500c1b0080c0031401303480c1c400d0b8098020042e1041054440c18111148038441141034030310fa542c0e20034000c0c0e02c4003402d040b800030000001030354035010402408507034510302a501c41c0b00151048050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 585065836 1250 585064586 585064633
    0x16170306010c0b060d08030702031201150c03180308030a090203011a130b0d0f05061f050a0501050d020c0d021011090321041802041401080906180309061b 68
    0xb140c0314141010210714907942c0c82d94058002455902031a140f41e468a41980060721031800680c0f000c03c200d400281482449409813040810000350720303000030f01c0100026500f440040403c180382840000c0c800d224074298010355440351071140c40c1c2ca410301280001b000107c01c00c1c0e100b5800c04e65408085003a0211000f000e08010f000f42c1285420404008042c140c0307110740341c0c1c20403111103400010076130341822180d180d842880174068a040103a5406403100c2590210b00043e61103900400c0705651303030b88008003110020700349591100e420960074002030040310703004000b0b4010410b07885c1c1031540c00318a0302c6803100c4520081040300244213000506002e0605a2905a0300c07003020b80f4440c0300b00c0203440c1c00507400044a94a050340b0b48210b02ca86d5000b84410b149920b80206d0207108640040130096407d078000c4ca005809440d203011403e50341d40018220555078180c820301c0c120b1411007030040310701c0b00701e01501050350b80510141002c03198110030402c1c0560700910402d2011060150b05031407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 585067086 1250 585065836 585065839
    0xd0e0f01091a07050303100504051b04031704120f02030105010b0f09040e0a15050f062b0203010f020403030c111008010308250506091005070f0e0a080316170306 71
    0x203160800402c240030510041c07442d50340309418028940095001c100440c4540e08012901159070300d000d06101c2541c00142c0000d111703c58200d00c07214070190300340a0f00c04a9420510090000c2c2c00f4020454103445542c0000c0d0440e9440c2c4801d500b40700c1400c4050180a00c280c1c006c0020741c0e654141d500171805101e40060b540c90041102400520741034000c0d0340000304540503507a41c8071050303a41d0581e10011a9602c00f101d5120b40401801c1090880b4460780b040c2c040d070f000c9e240c8098040000b00785101c1c1c55820103004a18818410554400354400013003040212011580d0300e8803418090080280800222070814243d0003040c20741c200410340300d07502e100d10b458203486c0e6421540c0d8000946c10203004582d00c402602120022186513070720103030b911400359024015900b403101056040182c0c4400d0007400d54104003d11a903180d10000c446a28659841c00c01454000c3c1e40002d0192003030360f4001d808501c00880c2c40e9407100545070441e0881840751035200ca4220480d5200355150200b210f50301d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 585068336 1250 585067086 585067097
    0x71104050106051b030405090f090c06190804170a020f06010902040e070c060b03010603080702040f0b0a1203031b0216080a020612040519030e0a0608011401030e070801020c0d0e0f01 80
    0xd5801518a001844d03405480c901034a05060b00c07400803c2c40c00720100e429150250345102404281401404400c0c0e141806a40c1c00745014400f4054085a4803d11105410080da07a40020701f03100050000307226640b20314a15980c2d070144404025074404032401c0b400b000d0b00030b4200001d4840703864400c0701c0c00c440803901c111200da518208180da5401007a007054504640701d03000c44c166130340d080c401c040103984114101600c0340302c00e0050104607107496079540d6419141201a100690311080044200c45040b10300ca03c0e10010780c41c0071800390124407034098040c55410b40c403250194010540500e507841c144e400666460b51800c2d00d40d41c507007050030301a400c40c1e802c000e4521440100c16440354040c1c025000c644c02e200c4000b1148949039100310007507000070f2510407020a01e24100c03c2013002403007985061080e03541008810524012140b10081c1895501c40e11a812184188000802424410001c540341d800c000c208540300e541408000c40010304900c08141301c0e00d0807070280184120180c1d02c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 585069586 1250 585068336 585068347
    0x90d021504121b211b02060915131523071707030f031107030806040513021008010815090618070504060f0f0b04050108040b150d060207110405010605 66
    0x60254900c01010b00a04105800001850000325260781c0f041c4540304200791240c041014040f180118600e04181c010002212991104218140d9410f5400783d01154000c0c0e0343c0203514001074860310034210454042d0400f041061070001082c010740121508904500705081c0d07008800c8070004e55200304490340c1610103045101c03c1c50300f0005017005030b210b140d14521542801c503507034099401540b01200000d020b41d4101000725414014240d10300d100e00f50a505047c46a64003030065800101040c2c0030b56138901c00a2000b02507a8185410705402400310705030801c8d880d600520242c400d0003040e03400d106005000340f01c15010a0071a228200ca9000342280e903c0d41034200c104400c1c0d8211540c1540b142040200d130079174440c0300c0c501c010800355056408881c81c00010741101c040ca03038403040e001e003000c1c4130400c5aa60000f00a50748181e000c1103441199840c1c80c034841e0401000341903035400c03051482c801d004218807980201100c0b4040d2404081c1d59802e00d0802003503d8003401044000344040c401f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 585070836 1250 585069586 585069593
    0x4051503150403050405150315060910031a040203160305090a030c121206170c09100611030c0106180f06290d090f0314090d0b0a0e01050708090d021504 67
    0x5007150403030322a10b4050710742070740c407000208003c1e40c25808116038400041844080c481822040064a00c107582c55820000040300090700c03100a44188018942c030751211407014034000e158110b118100800464030307030408210820400308103e040402207898840404d03c41480010182d1a090340755890b0310150100c0c0ea1418026039074145000c0c28400451110104807915000d4030307000e080c04850351480280e400c0c2d0a00d21b49091030040a009202c000241304c100d049840010094030b283d82007114000030000d016070310b10310a1405e41100ca520703100000c03602d680c0101c1e43d084004052002400400440c2d1410340c110f400d01d11400b1002c000e2032980201c1082c4001c2c041070540740c0c00c5181c5082800000200d07054541ca200c0c12602542c480c07598004041c0c21038103070070358aa000d814150820340c1d00000b1807050110400040d10b00010180003c6550026810408080b0407510003400282030803031001e050a2400d03103498146014400d51040501d1000a0b540c3e2a2140c0240030081a220703901d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 585071942 1106 585070836 585070873
    0x1b05071e06050f040b0702030f010612060e0c100e0d021806031515040b0d06020a0309021002010b150304060e0d0f031a0d240609050604051503 63
    0x41c540f5404081020340d400e0b078400404d015a06d031a0b40c00024602994030078001c00c19070901c480818041c41890944505900c10744042c0600c0302d200d0f49040d103503803200040d650401c4000e01001c03441c0d0301c2003c0c421500b40c0054847d1082114580209000100107100009468000e1080c00080d090421001e94011607400481400d400d0a9003c00d9001c0c0c2c1000c80c80f440f403038841000b1103130307580d80781c108844055000030304555811032201c003d409012000400e900c109070344440040180e006000385003001600070002c2c0c09103000d0015100e09604040c005842c1301c0e545116000381c05000300300f01c0c03400c403059440f00d41084840300300c010203840e0000e01c0424201803006d0141c40580f203c4c00c454880e182c0c1b061011648209004020a80c0e803501c8a0034210942070010000300a902c07a844903010320000d8606000070f582ea0f0f0891500d0031a1020400c0c0c060b80aa81c04002d00800b12 = true := by decide +kernel

theorem cover : BRFrame.Cov 584892086 585071942 := by
  have h0 := BRFrame.cov_init 584892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 584892086 ≤ n) (h2 : n < 585071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
