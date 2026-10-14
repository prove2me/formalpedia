-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3066
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:33:43.507974+00:00
-- url     : https://prove2.me/submissions/731e5a95-e783-41bd-a9e6-bd4922a2ae77

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 551258992 ≤ n < 551438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 551260242 1250 551258992 551259029
    0x70b010501020a0b1906030b090a1a0c0703050706020d0504061b05160f0f080c0c041b120507050910080a0e07080a0f0203160e1807050f0103020c011404050303070801 73
    0x40400c443c1e449803052035030b90301e1145d802144100034559980050000c080c2642404031501000c605c0501e901d01071005001c980519000102616070f0a5840c0009032404001c0031f0000781c02107028000003030281d030005040689c0c4ca00c612003541c2c4105d408840150351410b214040b0b228141040300802c05a1400500b480103444015900902d105006002008a000d4103000c20001105101c0025070281205031074091202c406507440c1072000c1407500c214200406940f0082c41c10200845c215101c5d61100d003100b0b00030100c1401441c1c06822881006800c220103009616003a201050303508250391011818a40810460202d6013242004103554105030410020380c81d00080300107455030083c0d059607a80f0058400246071000080c41c402e00305038601000100d03e2940302c2c40511400c1482815002c4200d0075130095101c031614001c66501280081c0c20503202c0d44240c0c05800c0341c250b444000030f4055000c1c2110030094208941c1102c0507803000003040070352a0f10501c040e00401d40c240c00408115207 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 551261492 1250 551260242 551260253
    0x7031d21090f191d100e060109060f120c120b060705060412170a050610030c08011806030b04050a150606140706180b0126070902070201090f0605070b010501020a 71
    0x42c0a2803c0c450398a48600420201d418402e440042007140021400b101003612441d0a80e00119001d000442407044001558110900c070188190b4051f940c4540d0030f410001c045c1e881900d40c540080c00c100e01d400400f199508240308650904140d5103070202450b0495245005803400000710300d00400f4180030240c000b40740010700c03d41040d0303c00580d030300d03038400d0200448902c84a0241e0030128000a82030116001296001d540113002c10398500704400d0000350264207aa102c03c00e04000038021f00010402001450002e13481d02c400c2c14400303d040c41eaa511400e9181c03000340e07401c2d81c003500424a00810030072500c94a044260a507581070140c1464402d0260102d00c2184525680304000076165040000a50205041792412a084406c101d007504080b0564507007401800300b1940c00102030007440425a0f445410111050300402d4118204806140a900146070481c10300c02201c8001c2500c1c812041d068001c2c08480c1d80e0325491382003a0400404550040c0e105070b056400c0840d03000040344 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 551262742 1250 551261492 551261509
    0x20301210c030611130906090f0b10030b1302040306020a0e030a0f0b04030915030c120b03190609080f07020123030f0606160506100503010b0901030b07031d2109 71
    0x20303000040080c40800c03100e44042c0d80d10820341045000c03070444038041140d41b40c0b913000070165240c85208108880c942d8040c9000c13900e04041482d8091072082801c88424400e4006d858801c6e00034010341200b007180c2d19900103a070086d030400c494098010542508095101902520b203240443c020018041c903a00c51001a014000c406000703030b1081d030001010315029940c0140100308440c81e03408050b0001c01d0080c0102200056031000840c2c11a02440f01c0d5100e000e808a0204020090f20640201c0340c030414814200440071100c46803144040004948540c0161811081050041e503403407610b4400141000ca5103c040d40b40c125107108841e05442d480c200b1307680c0c4600c0741c0012040c00e44510700000d01c0f50003640807031201c101c200703420b0404211012400c94002c0709400460500c0d107403210304240c26180c12144d0990080340840042000c903200750207583c0c114965040c0001e480e602420701d850134070740e400c1c0201c4080c0c1c440b60428001c4040c6050f00e41410718412210343c01c05400000050700003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 551263992 1250 551262742 551262749
    0x903041d0615270402040302150a08010e151c0203060f1806041101030203040501060f060914060906120a0e0d0f020607020f0d0c0201120c2d0f0c2103020301210c 71
    0x880303c002000d09844541c1110044c54008090200e0301c160403403a41c40a50051880c0d90015a0100001450300380e85d444041c000c140140300b101d44070b0041002d11100241c01c0c5415242c445a03840f5440150b1000d02119024180d1880c2115003843c1034030704101c541c003220003016100e41c003100070000070407100c880c00c1d032400a0134a00981d9988890400e98017501281c2c000c2c0c0540003040c0d500040c200d800c8030030300c400c4070085d013055681000718004101d40c60241112240d0071140400649031101074231031449511901d0118001020000401d00910b01040f41e0403035004151806a044841c0b0380420001e80d00c42454401401201d0b2200d211a0700c68090040c3c3d001800002400481168085d002d1002c10460315542001a1551081c0c0140030058140820258001c02c1d2517a09811051285c1c08050092613158440c0e55034041404882c050211070090b031395500d001c1080d10320b11540c80c0040a108005a60250321303035040003080300820070380d41400ca01000300d05500754006402e01005070b04a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 551265242 1250 551263992 551264047
    0xc03010909141608190f060914030c061801050702150601030f1407030621020d0804180504111008060402030915090f0d0e010c0b0903041d0615 63
    0x103641c0c41e440c080702c0071910b01c504503155000d1200c109440200920014048400500448400c8000c2c910341c2c191120151002030081084520042d011581e640c000c110740c0c0d4411036800340c0d840310000c103150854200304464a49500305c6824804048440b2601c0d1a0300240a8020015070900190213983e030705268003144180440c0700009042a8040e0340300d1080003040c18402e003e545424100c0503c40001100c00030007003480d0400204050001c00b00d0411050400c500040b5280901d8080000340d403120081156845001c00011074500000a4140d071540c0030300c4404641800c0c03070310703080400001d52000c00d4003d405c07141055500380e512400540d04102c040c0c60050382ca8640740c1c030369402c182440c5d1070420924001800c1c040c000317400043c4806460440829103071100d0f044442154032660204034240003480c0b4188400c0440d4a000426400408960840e49016a940d01c0321044400c00031a5240c034030000400c0040500305420300702c44441e96010801d1405550304c03400c010128501030b96520 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 551266492 1250 551265242 551265251
    0x50c03130b09030f2208060121170c06060a050f010c110a03020d05210f090103021b06240423091908030a0e07080c060903070f0e100e0c030109 63
    0x650b040700b0310480f0301808400d8145a80c402e03995074101c44441c0c0080c1c00c07254043d80c1040004a01a011907001c2c1a00c11030311000c041c091805c808106a0000e90005031665500d808020040b640710070010400d954000c400b41c18140b928500700300021003d179110a010360712400042550f40e9000342d0007111213501c0a11580350005081c04141000701a400c000d4029100421071014440b0024650b41c050001003040f426400025035008102e00845003602c06000c024069417140d92b02a801800040d41c4000c00585545460b9540c42c0c500b8800756007032500e050040c40c405009680c0c2d042002000c20b0199010300039040040c1010940d13032030070b107514180003849401103403c20a0900c02019241c80000214901595500300400280d01c1615106202d510f8181c8617611984041419000ca42c000800b900d03d0042076401e00c006540641401a40350040541c0400d80d00c01100e80c01000c2d01100b00303101e00c545004d10700000121a60303088031042102d00001c0002c440d80c000202e074150f07807250b080400c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 551267742 1250 551266492 551266501
    0x6021e0d031109030109080405120309030601030305071b0f080f061e1b0d0c030c1704080c190809090f0c030115050909070221071a151012050c03130b 66
    0x91003800b50302c060710351550034941c6d05001c1c42640c00c050030a4460031148142900b000c5c02d51075603a8440c01c1c0209403d50003503001040403a004202400702d0324090f400942d03d4200c4050014020a000e4002500151140074140210101004542082c1001e1001410107040c004035041003c19803200c0c0d121007004640c0000c041c80d901c0c01e0740c01a4503500310941900c0e96024040403001d0151000b20303500080ca402004070019129031000e101c40d290a0740c03400ea99840e9503c032001b05034007450404200788a4030009081c040c0316001d40103813883c090114141c41e1580d104c104441c901c0050158441c04541d1814071113050b03d201d0440f8110f0300e80302c0740c03a03010503281c01d01a511401903080c01c40d400704442d8100314119030003103401080c0d1400312240701c04d60080101c8044140c01100c1c4058220020074480e001c501d11003120540e004041181c0c04103803040c4840c002450701d406070300044000740c4c241543c44050a490301030140c101c070540049504515010188010a410f84400900b40c940700c2c01c00714 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 551268992 1250 551267742 551267771
    0x1150915030501031104092103020c0d0504030203070605091518040207061b050a051b010e0a051510060c0209100509090102042619140a030906021e0d03 67
    0x250014500046038000d40900008040c0003030809200c15265904c00880b5000f2602d094414500113a07440581803000580e01c81007803420000a000003811700d682044040d4258404101400001c0750a0362103656a9046105240c00d00b070381c580c44441030100038004590240e440c42c0c1d01c00b04605084080a07190450030f0200e80200c410144565049840010a0400d0020302e80201c08501480003102c160014001022603071442120402c01c0060010301030210569041880c409041403108004914813180c070607041c1c00c200e00400111821f6100c0c2122030200901420016400b591041941d00e1076454060080c0041e071441e200284540c03000000508801e119045013800343c41c01408000891900d9080d0a0003075005026204820010740b030030046a608100c000050100640c0c054840001c045115240440c1d103501c0c11120142c0406c4803900c0c1410800000c0c1c40280203985607106c242c90701001030704081c440e00140000c01101058010120070020f40002842018a0001240c00743c50115 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 551270242 1250 551268992 551269007
    0x30b07031d0a3c0309150302210c090409110301021603090608100b0f0d111e030c040302040507021e101b0c0809010e180601080601080103120c020d1a0403090b040e0115 74
    0x11540051100781c2d44030302e6055006d030420020010011b0034942803030310b2805418500303d0781c181074183c04001d404cbc043d0078250805080584036130464407528030620000fa007a81c124410b01c41d0961342103c45901030643c428820340041815003480486400c000301c0204c01c0007000c0c040c080a1038000280007110f605440110b0392490302883c0304010316002d49402001551001c030082c2c03114180b80c90003140141140c01164080d00c010a11145014619424003000e01802007100040d0302400b01002c01c4035108200d450060025080a0940464a03401a004580804031171382440c5801e1100141702c01d07004143c0c00c074295000701617035858140c0e940040b101c041c2400e07075103a04040d079000c502d15607551103541e003070042e03900740c980315a940e0750140111040c1e02c00748005050300070f142c9104071400340070b02d11000c0080d0014080c0d0701d028200c0e4845500b882c0703039030406102000f5500100418035510110f035602034011591100c0c40d0034580349034801804018040c00b042c038100d074441c1a0225015a48 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 551271492 1250 551270242 551270249
    0x6020325020315061207080c040903030e06010e01050436062304060606020610120203030f0c06060906041e0519050907060809010213030b07031d0a3c0309 68
    0x319040c03e603408004492205003a00c000c0d001d040e40c21500c3d00607100105100056a40e020003c00c0480c100c60100000340208120650515646440c06a0568400e004c07842c06050141e2100040d540742c1801c1c003045417015013992881070f02c120002d00d03a0101d83c455458124032141c08000340c018881c2440c00040c10030002c5030702c40501d0b40d605286030045506c0c0301031003640030b200200021031340c2e18001d81e11010304862224615122290a000202d0040c1c041004140090704132070801906480c4030301c6591103040c00ba00240c2c850001c0200915112002c41d034010416501030054000d012101320b4083c40309441010640d0310307580010b0040407903040d52611440030110920240c02c110705405d8440d00c080c0640c8002441001c00510261b07014002c48100650300114181d0462441d10792192541000d0026001c00d43c40d500c0b50580300c01304402040d03a0186c00c1d405881d401c030682c900840b05040c1d420f52010302840286014940120000d200d00b44101c00503c83d480303004052400f15280071a581 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 551272742 1250 551271492 551271499
    0x90a0501210c020a0b010f0806010e090f0601030f121404090c0c0512030405120301060816020f01060b0301080d0c020f0d020d0b070e09060d05211b01240602032502 72
    0x6882d2240e660f00240d03500400b4000c40d0045080d98841002602c02405805402d0b01030303005500400c803d10100745501d6000010100780c072640030310050080c5c14600e0a03803059030499a107042c03000034404064481002e40c021401c080100c07a141521000301d90003079100d01c0c402e555a4901e5941c10a004021032071a40d54024140c1704900700c52103901d03045400030750b000d41b5203114078907081c0040d100c0d40c01107a040e592aa00c2d021050313603885110505100c160003102d0218021100001c040e04805d0107000044c00b02054181c0e120760500703510a14110b540a488001c1003023017200310000d6120468043d101c0202644d45807083c0c0340600100340c09007090003006002c0c1601808020555a0001d0510300480d001c0380e13402c0c21900c9003002c20451030158031001c0c05540084401e6040700c1009a601c10313030b41e1348072440c4504112049440740c1c05004101c88804160351503a141c0c546460840031a0380c0c480c69540d2150002e54148031000f5940e024440c6c07510080d075640c0117010030501c140c07500300c807460350b005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 551273992 1250 551272742 551272751
    0x1140a08060a150b030c09091b1303171e0309010617010b01090509092a040c030f2703030c05190201090302010b0301020c0a1b090501171002090a050121 67
    0xd0420000c2c80c410031803c0001e05240008500c0c0140f00c01200e00a05445079002c1c185880a02003100d42d98014288104001c0151a402d01014000d0064015480d103401c07011410b0b803660601151506a0308003200a1300002c000382d00121203426102407803103403020b003015269500d40c01094010411508494410301203101e500310000300c150425548404280c0c0d5100205a8507000c3c8142040c1c103498070000c94100d54042d030b01002c03140e2824105c031481c51000c01140c0d048000400e00302d40e43c400c04900065280d1419000c1e03081503028203c0c11042612806640b841c044001c407442803000400241003544850700c0b03405c06031048059940da205000c1c242c5001081048000c0e0080104080072400740d424212610341a28043c400d40f400c1c01004406841582099034a200401c94081c601c2541411030a0b004280011680310703640c080c144d544421201900340070782d69031600d84200c040a940c81c1c010850600d19461300021481221403e08090700800c244140e44503c172104000350601d801d04e0f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 551275242 1250 551273992 551274001
    0x6021305120703060b010807080a050703141005030606060a0206071b0203070f090b040b031e01020f03070906140304081204060f0f0f111201060e060415020d030e0c030601140a0806 79
    0x810424210f80c8144400c20070f4071100401941d400c2c5086440c0c0000c030340e0070800980c0a14541d04400c0d8041c6161400080e00c01c190b60014480c1401039806805d010060082403113603050030818260048411035045013400c40b480d00080d9140401000c500c10001d024003003103031481c1180b206440060340281584c41c010344400d540c0080004030f100d40b004440c14460008141e0401c0c0c828000340700d102070003804107036140300042c01c1e4420b40c482c044c0d01c1640d401c206a070b49403940000614020303c2207544044400d881d0400c005e00c140c11400d0754000803c0100180400196030100716502c264100744611019900c41c18104011b0070302d12089103845042c4080c030101e000269000c03c0e034805500404200c03481000303400f8089401000c1021039000e032950010302c102809643c054802035002091380e0310305170300c2d1040d041004401c80180c50250348030040407440c0c0b51b014081d01070703900c0c1c2d16001000000c20301c0c0d000a680383c1c01803241c100c001031039000019090700c42c22912000352200d48200e6156080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 551276492 1250 551275242 551275279
    0x90b0a0f1b0605240f090c04030611070605010b12010302042a110d0c0b0103060b0a0b040909200915060f040b1902010606080403180302130903020609160306021305 72
    0x1c22905135964802400c480d8509842d4240000680480035100000e096221024003004500c06003550324000018040003000420354002c0c11007a109403042c00d916501c10740f410005071030381a002910a048217004400c03040100695a504581c0c040b02d010a10815845103802c1551300100e00d100d5040c0300820b800e9049170070082000b41200c82e00100c5480d035190540440315034408120040ca84510000108085903994200303200d01e100c01040d0400082e55104074001c03d5004e03501600d0110344405c03001d01030001c4000b00710348071400c0304036401801c09001d0028003103100007000d003204080d6040d451600d549601c021307601d0b200d0341c005440780d0b9036499451880d00c1f600031212103080000c468403000201d0344180580e07000c03103090340c0b00c0d407a2a4480741d07820340740240c152804d030485014044000000da96011000c4002d980f0b46440040c1d04401414000d003030000051060042c0d82c0040a200000e9160301c0c0b0410880c1d40024005031914400008a0400b83e4142d10a980c0001100201d130310000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 551277742 1250 551276492 551276501
    0x201050f032505161403040f082107020f06030406090b07031d010207050d260a0203070305100f05060901052a070e10140d020307060801090606090b0a0f1b06 69
    0xa240300b1410115071400c02084900e0301ca0b03c0c0b0400e6200d043c586424001074502080060100024005e4a0a00d500c509005540c0449684601d0113039010410300c0341d40c00450031071600b0801d10803000300e2800385c540d004518410449070314039001300d4000002505000e00b40c2d01984034a076000c007207a0b015007400c020060182440805180881403a040700240b04041442241d41c140e80c02009011040c66108040d9441000a602c4100c1c3c9035607000c40b080e50140a104952143c0440d620058803420010401002c80710010070092108840301c40c18800e03645004240011150102d8405a54565079401291035010b10700b0004a81d000b681c210007001002c1c0c05c1c900a480ea80d41080b12403160381c503000204954400d41c0c51481842500c9400d12030000c451032000300c805c40180c04240d00000c55800702c1e01d80ba016a11840000f0b000c64014481c0b6540c500400c00180340781d182c020760302402d1030400c20940c8170b00000da006103e21039158480c01c5001e510308411020040b4850680399032030382803040191 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 551278992 1250 551277742 551277781
    0x1081f0b091c0c03020904080d09030206160e03070e0705040518090f070617101805040c060906020c040207050705100c050c010305090d080405100c020102071109040209040f0201050f03 81
    0x1404914a1004060708000d465010b054001442c00406484c540038420904400f4000303035041a400c001e2002540607074000c40081500c40e6000300607a1902021810a0b2600030400d04c082052050418000350360004144040d07841944071003240c0e449a4a003a20340388125480550003116483e0b402e40e60b12014840d541c80b42c6c5104d8203407aa9004142d5410391500d61502541c0301098150400c00c40150401940590020071442c0817045640c0b181249580402c0012aaa451b66210400c000c10000c40c044234100400ca20f04107000c030b150400070302a440f6080c0055841c0182c1e4040707801e03400e01c80200034400c000c1c14041d1280c0d0901a0705074000b40301c0c0b20503200070341e914820022031420652080c41800e00c509045c1d07010b03014451241c401110410300241c4161214450141030207074150b4a40306040b60860307036400060341c0d01d43d58034100b945079282117000c2c3e215102e440c0030003015850b2a5078565226a008040c544110030920040e00c8501485c034802d01550000f00801500d07403060800e11104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 551280242 1250 551278992 551278999
    0x206040c0506030c16050307020406140315071409030c150703030e0a030504150c0c0f0518070f050d2007020301050f0402060a120b030607021c0207060e01081f0b09 72
    0x507a1150140300143c031060302c007400281c42c1005030000c60900c00d0003420034079101e078082c0da1800e030032900050305580d13494100241841203101d00411621301041000c48000c860000c440540c644140301404045195003000d5007914001200f00142d50203210003480c62078000c01380c00b900c10211561074680d41040c1c0f01200420b02d0205801072001001400101043c0d06a6a02d8030f018280251020342040c1260700c2c01c1804000c0740210001018650010040c0c040c080040058511b000c00f040560308260b180c940c070303041e0154140482d140d444000c40340410828180f0f6079451a5400c0d0480045c9022107402078034012030142ca55815005d0340040101c280200c000340410b8556a85c21403610340c046d00c00950014080000c504100d0242200622500403138400141004c1c03000003003820118216000d90050f00000442181109403100c00c0318174440750320060030054200400540404102000c01c0d051014403c0000c600203c28842040156a8024801c43c140e6032004207500c690084c0402c14031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 551281492 1250 551280242 551280263
    0x604090911010f020c0d021c050616030b06040e040b07090e10050a09050f1f180e15130f140102071a0919060e1e0a06060f0b0a08150a0303020604 64
    0x50544001405900176100030020300c2d6800c821b60800136035800708140884641c0e010807507100859002c2c49524400c4c0114110b40311015200e02f0014115518040c0f66031080a0a02c4140291014410040d500c981d2040001034592504603051f07418903406e40c0074a61038842c840c10091002ca401000000321034094400804580c3c480760400103458003203c0c03c08212440320300050101c90480c8200811591007a0040d9015031121412004d514041446d05040c40d00c0d07216010700740c1810042008054000c0f8601d04003070400c1c05440e803038081c1440300500b000074000c5244041c04012000d00380f5043c0010b008640d1038a052030554850004c01c00d941d0656180240003c4500c180800c940e41d0394a9246d500d55410b28096035507a0081c0040d00003030740b051088043c1c46541100c03c0d5180010609001c0003080c425140e45807940030345100750054417600e120a0400c016062462080d580c040c1314505004446a88403c070001c40d000f4446000c42d440f480028002041c507401052a5001c1c5006001564 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 551282742 1250 551281492 551281517
    0x18040206220303030e2112100503071d0c0c0615010306241106090706141e030414010c0c060504020d0227100302061b160b0301080d0e0f040b060409091101 68
    0x601b0202c5180790446a0780700304601090031041c0300145502003264080041085d4451010924000041d040124034180e801c0c00d035903035221104074130b552228940020394a880e400c203409030307101c6c1c074050080c4d803004d40031110004084e170080d00548050040401030784880c441c103018070202038483c01154804607d500714400e0281c40302142151007955020700070407829107881011580c2c000c4c7c034042902420420f1014042d40c0d090300003080c20844203c0c906036100d090505112640c00704906103251070340e1504901c82c00442e00868081c0540e40c2100e00001c05650f1800498100082088000e5002000b000703900c40b191200d61308529001000c91000c42240d6800008482d100b03410300000c0c0d44540e0074424407600c60382c940c45c41094070004038159101c40316903284212200311680c0056405a00101c014891480100706860918080c0d00e0700f401d49520ba0008543e03c41c1e1455078050203a512030000410030348076101280c0c010f019580081184180ea0308150f6980d42071030641c0c5000072140da84c002d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 551283992 1250 551282742 551282773
    0xb1818010c082217070213051003061d0105090d030c020714090c13032d111201140903030103050613240906090b04020a0518040206220303030e 63
    0x40181d1622a20001c0d140d04101100034503209a0900030045a000703034a0010311354401000c0c0c58402c5411041e102c940ca4410011101041030750380c041e9030301c0c1c4410000601e413021052021070f82c0185000504061843d1034034070314009505081043d40c02d041c02d0126484d00001c00642445c0e19a07001c001c51a4501c034204c1e100c9189200b5030b0912200022560128900300101e160400c9024994502d0410049112a843c81b42a03005607035100441414090030006200f5158181c140380100d0350f0804101d135116000309000891145c004d0b10500c00003094003101354007807074417080904011540c038502201001e0750f03644240402c8a1b103005000109480f15201164a4030041e4401041003100d50a000c00210ba0002900351480c0c4586400a65010604074403070703200a40d010340020396661400b1b00500200c00115481203001c1d4610001803000d2003028548240c100f541203e1942d0f9410400403900b10224594503c0400e50102841c0001015010f034032508903c2c0c103003c1603480101c11203000d0b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 551285242 1250 551283992 551284001
    0x140708130f090e0304090513050d020303040615080a0609020f04020d0603060606050901020303070c020a03150e01061a09061303080f0301030303050a0c051206011e0e1219150b181801 80
    0x140341c1130b84144818031080000740c00041d80300c00c2c2520010000e035056221030746407415100007a409a00000180400d1190500030540000e004000203200d191511a240781e030b9281030000508000c0e56503081004564410000309a4032000030803d54507105880c400c4401402603200480d003061070114006502400384095802c02e80050300031310302755502e200c01074400c50802401242d000c9c9003290701000003400040c2445211203805400566804100032550854445e60429018823400c00c2c40c400180790f5001c00c0380c8034150213884c441e4544640b03001c00c1d424407100e81c0005180d100003140c2900c40c040c060015504907406030b9001e000c15102c4240365401c5919100c00c0c000050b00802c000020310005e500ba17603030054018034140c802d90611910700c80721903c41070580c1c4001007580851009a00c2c20b072111b0b4001b08299000381050358031000603291101c0c0076000050000904038001d008034912980041f00c260800b40410701c00c02c47c03c07501e84103410421110544079403000102e290320258148138 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 551286492 1250 551285242 551285261
    0xa11340506040303180503031b190203030406210906020a090609050a030f2102010203090c0a050303030720071e060c1a09190c0510110d140708130f09 66
    0x31880c80d19043d910102c42d1603400d180209030401c001a0005840c2d00c0410092094280480c4110304a40c003288105091a03007d058801029050745070450160340c001c0100c074101e030082e09152100c0001041000c006145003421008814a81000081802460b400502202449a560340e42c05030b1201410345880b9814060160400340c00310381403002906035000c00341c90307600a0700c110480c5640388a03002042d5001c2c040100041c0d4000c014400035080030013159844100440300005014142008281e40c0d0100600e4541001945a50346150140040543c41c010f03005106880a0a440794441e00440d0400035644212614000f40058058803c130b1a610900c2d82c041c018009075012608441101c1c2d4000d0809501401000350040a06c2130a107505c507442441001d014610600d444100f040c0c00071110618401c0c4601c900ba403902104000c2504200790a041c00c1c9030b060711600881e018a40c0c0107051008041000000c0c0514104803407100400c212a0380c0d000240c0c40a0f01e40e0180816201080c6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 551287742 1250 551286492 551286499
    0x100e0d0212031306090201030f2d02040605160c210c0b0304050d0c0203030921060702010c0203070b1015180501030c0f0e06070506011205060a0b0a0501050a113405 72
    0xd81030f4001a185030080100c02e0300500d03003c910030200c4422642160710a4030842112003a2007100c0c03988040c84032007040d40b00c030054007c40c2090300c0c01c9009810b500c200d90030042c20800d01100d03002007103000b00051003d0107098a8011040c2c00a2000100304203080300207550701046408001420000071044911981d0301001824000e030340c2c40003c0e117206a004404a81c140418890ba117102d484841812a80d012041415201e500300420541c1c20507501030a20f00c00c59040521000210750000200c4607181e502c0f5030b45600e2a0303038010120038001c985810041209180c071800da1042d40d800414024001c42d94009207007050707038403401581252241e401510214045c0c41c4c03169071720b42c06134400f0003100401411003480c20146030f846c10304004098104012001203e98a031003444000c0004a5115080c02c0c0208803505510340014644882481003d04000c40012000401d500ca40c500c034506030381803821644200400c1c4442602420b41082140301c025060450414041c40c502c8002c04442026 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 551288992 1250 551287742 551287771
    0x1060905040218031212090a02012a0204020a271a160804030c0806010f0b0301150e0904051e0a08180607050a12080c0a021e100e0d021203 61
    0x3090101039040040a10361401c602c840b00c0c070140d1000d000031424042807034140703070f030710000ca0060000b01100500380701d00d00d17803281c405400141d0708170502890481c015031f6404e4402030800f010400700c05801c04000e41190022404400c15a0040c50007480304214980e14000007004e120f07003600005052294034208581c5400016100d04120000d00e45e80b400c01064156039200c039101c04841d42d00a0380104c400203450801001039a90078450180500841404914180d1806001140d03070700040c0104800450620280500c81d0b00607420110000d00203880694070385070508000b070b226801c90900d25034510030007404181c01040814003041c9143d02c403110714205107904000e400503599490740e90f900303c20b00b0881480850030811240c204103220354140c1603005825000242180000b6020180b0a0001d01c040a07840d50003160440c7c0100300441e00000c50003600b81268544001c0d5409c4804551030034800c110f01c081c020405c402401415008c881a0041600d40442c0500c000c0f00e1a03021031044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 551290242 1250 551288992 551288999
    0x1603110a050a1a06031f0f0b0603010f03121b0809010e1e0103110705060f040c031403030a06050a0b1c0b0402041403010b030c0312161e110405092d07150e0405010609 73
    0x45511450102d070400300005230076125040400c04607802038221000044100204004201944040303000c031003024030f8040c1a2503d500c5250031050312142000300601c00224130403000e64815080c000d044c500c010404800540040c003800300315400d841105001134204030841c0350040600f412141c00c06e5110b8024455580c0c1c01c0c1a150b004c90014004540e00c41c094003000004c1010002c440304140d454401455590800322011030071116180d0007075000b201109001c0000e0721400c400e0b03610208808081c01284590f12032120010010140c44503031103803010030003213030502c0e0444001044103019030007004882c500c50101030392094004442a0b242e40718510401e40d195a04010704400900045506504003050369200340400301080002034044039080f480040c0b00c61010071380940141620200240d080c104106601c80381c51280002028030160100c1d0003518289150445201080056581d070302e403100300406000380c0903c1d900c800611304e000480d43c1460725201c3c19040b07488640320320008a24 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 551291492 1250 551290242 551290303
    0xc020907052a071502030406030b0d0f03030c020a0203030d0c02061e07050d02071208070807080103050615010215010e06120c010509040519050f0910021603110a050a1a0603 76
    0x800410b00820703800b480d4000200810008800c03000348200380c0145440b242803802c02812075071a0051144510040702207100421100400c058003103426150200d9280710065041c0c0ca0041055402905440002001034030a01c3d075034809400303490342c0d038251001921112603030800101c03550581d03010f615003030011030016801040103240384d1494810240c18213605898020480e01000003460200c1d1900c0304010380a5404108164044134a06000303502c0d50640e2a13603581d41400404080841600900050403613000f009a030550310495540c5041c10343c0c43d0b504503c0d0030300041c0c444070b01400d884050790150084c04140c1840c1d41034107949850410000070108406084080c00d081801005044a0714226182c6d0151500c02e04001c40d0541241c14440429444e110315101c46480170b038030600500e034141c1c941c440000060b580600d004151707002c110700c040c2d0a002c0403020003071852142040d079504100e1107140415a1001e0181d21180b140d035000706040d103079800720380c2845030080b040201d0031000c030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 551292742 1250 551291492 551291557
    0x30f0703090906080a060615020c0f06130807090e07060f08040c170c0306060d0f020d03210603110a0617221103010e15040b070e0604060c02090705 65
    0x90007881c00000c030580c2d42c40004100c403020380084245400c00007600c820b00540d801442d0041c20076180384a00d02940c40e200070349404000e140c592041c1d200070b0400540359248000d64401200c0d445003403000b00d90365041280d59881d1480740054290600b0707181200c0420104004003150000d4032002c041c01443c840403524100700078811180c0c0b02e41c0701d50214ad014411000c1403042c20135040100b05403400c2c0e00806181c4100141010311444010a0440000303940343c2da29501e05506603011140c04989190075940c20348005120300202200311284000e4884540004e0201d0f80074034044040c0110b5032082c405000b41038000c00e004241219808208440300d00c44240d403201005c850171404402010808940224181e001c5d50005544492115180b40a111722002444403100034403142c0f0040c100440b01040c002c1c80588400030b2503000a80d0140204121001040010105079a540c3c460b40c0103025040394580036401840c00ba0006442c003030081003210030021001d500b0f40c102c580010701c03121105 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 551293992 1250 551292742 551292757
    0x1e0b18030106090903020606181306020d091202150c0403110f03010e0d030b09090303150108190c1e080c040b070f0503030a0905100204050f0d03110715030b040b03030f 74
    0x150750b80d240c001a183c4482c8103c01c849071096001e405503007000001c000d03500c07000400c4440a04070b001c09001d16508003101c944003e41c2e2200c005600c0300908a48039000f880010320207000b941140262980455000c0764540018900c10252003140e100c15110380f85071301883c0002003654006107400285460039180b00803d00d400140041180240c040c002800d11f014076015101198031180803070b44514040c5a0181c0c440f1030f68000314218540070010383c002e90030902d00340c0c0c1409610b0010590140d40c0d12444624000f1481090015070750f4500010990300020412985994035003074100c2c1400c3c130480c0c0340c03401880041103544c1480d08080c50092590700002c1c00304c981401180d8000b00140e41440514400d030f020700c00c001101030b49803e000e400c18034680c0100c52000d01c10401405142d40300030155078504019141a1102d0415103026611034101864012030352007004e00015107045c10803140216500c2e19501801013490400511003a42d407122000ca078986c20520903c2d054400700405041e64 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 551295242 1250 551293992 551293999
    0xa090e1009020d0f320106143105040503040303200d0e030a14010f201804020405042919230d0f031b11040e011112011e0b18 55
    0x302c0c1c0341007000508200caa01c081280700400300c00306441c4145c2071245800601c42c03208184203901c0c018000400b00036100c81d1600c00702d46130780707982c4c600220b25880c1c030301c0c440c410110304001608007403c0080c0d9035001403100300c001400000d4a2401902c107405a0000380c01e8084c0142510802460143c0344c141003a220660140f052004d2180410f4151940e25200d51000c00002400013401c8d42d40c1041d21400c12400d44800581080701c18910f035540c04884000919a6008042c200c281000802a104940c440750340281041900309502e040400d8004a030019009800304100b001c10510150090320403089449119490040000c42c0c141c0718140040d20041c442444250700c03100c0050100b055283c400c0e208100b611a81c1d50030190090190f2041c012130800504070640d09030b9071058400a8400501c0c02207854450061000c60250030507511902912a10740d00c981420012441c0320000344910325141c0c4804400d904945e04003a049010390362507a6001d07150020315002801004800054141c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 551296492 1250 551295242 551295263
    0x1603021c0e101d06070b16021f0b0102030417010f0e01110403060207080909131407140f03100c03020d0b06030103020f0108041e06020d0f0b0105041a090a090e1009020d0f 75
    0x2500e0b0390704d00c001c0000300e205000c000d03c00d050041e00b0841082460103c0003e42d4480c5e00801304a0a00f1070940c20800c100e0400440c0c0785241000403070960207a40d1190307841d0b400d1940c9000300d120f41900a00980d4100c454104000180840310609071034600b0309803040e0b140c0420050000c12941e03002410b01714003403c541403410218038049071146104684604500000080c80d10030031a04281c01e0340300b44018002001d01509083c5180c00c040003c18070f440c0b0524900000c612107890600616100da00c40f01c8003004507008171a8007074042d5200711180c1154900d042000002c41c680071007a241a00d8001d0140040401103600650344800068000d07202d491311010318040383e181303c030380c80ba8403030348960b50160b10307002800f02c10380a80d01c10424007900f0b0f600300204403023141d0384641942c0840707501000c00452880080d03c0c0400c18402ca24950390000d118240209404810382c0050420020785001c48082c070351404200e00843d032600d50025400740d02114100c0c003044a1090506180340103065104c2e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 551297742 1250 551296492 551296547
    0x12080a0924090b0709050312130b0c1015051318260406050d0f200a050c030301030606050315010b0405060714032703150c0307051603021c0e10 63
    0x121407a0044800c00c0001e051140140072a00742404240a0041520112030900a000401602c2d200a50180f20292b260100700b07401088400c0026404100042c0010001c41d07400c4c8107030301c00e18511030040d60300407640600745100c0c10148e4440e01c08040701ca00691641103c8a40e02c03480c5180c0f4540d0424400040c81c0c022454540301340004100601b00c50f200c040e91885102035601c2680d840318207040f070300c81ca403010b054582005007181c10000600c4903d06d039500c007103000e41540e81e07018514643e83d440c81f000c000882008229442030095440c11011211403212114181c10b64103000d004500198400380803c11603070600341c0140a886201c0c681101003c0b11140c0240c1c5907400240500500050071002c14091030486a04088103480a90190101c98401401841960005420310fa40c441c80000010b032030902c22821b5500075400300700c00c3c1003c0351541c10020b40c0c65605d100b0340d0541400040400301c100c0e0142d0190410f00d4000b070414403038183d032098143c555007c4c455a09058081494054 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 551298992 1250 551297742 551297753
    0x1b0c1e070e0a0e0a1e020906040c0e150c01110d05010e1303030b041e0b090610021207050a02030703050615061c020334090e1510110a12080a092409 65
    0x80800410785c00c074001c100000c600400c1040107001e00040e01036468050f01404450b488060380c4102a42501c00c8503541c214014050300c64450b410008495501c0d00b1010680c10002c3c030014a180b41e41c80d0f000f800980d0302e49096282d23140b0300341e9410044446413104440028040e400400c1c0039140100000742000e2200d004072042c40c9446c5003d0700c11036130b444004140303107080584a030700f22505484640e1042c8003594040d6130380c41404001e41680401103011010040c0802c9402241503028094615903590391400c1541d980c0d05407200ea403440d0005000c911542860000d58684402031a0280400d0512440e080001d50005d8607052010821041003040303402084420480d8213201000044001015200180f500780305810580c190084501801120300d84079191a49045040b10340d41480300101c1d03000d803000700392010005082d00600c1202000d2110400b480c40003141c0741d444020f4070f0b40e03403e80082c084402c1c4041c01030140c08203448040820210380f0920341c1036040b50500255008090311030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 551300242 1250 551298992 551299013
    0x60a151a04210318030305041208040b04080a031e051222050309010f09050a05270f01030b010503030313030f02030408120904110c06040206031b0c1e070e0a0e0a 71
    0x102040c0e49140c10502c04155101c401000e0700c03001558400a84c42c1035580041683c802d81c8204620340324408039800a02000b0800c68005060310b41d20960341d6559500d00e03903243e207004102a004074190001e0b42001900500c0280031001c016078a4501e80881c0304045002c0c15005401202c0c485007200140101c0c1e2044000488070038000c000075912417030b0310400101402840c0d0b000d1810040003140401640d04e0300705160058407022100b410f13100444503041001034045d611580c010340c0c11281030014007550b0003c80fa040e81c0c060070ba0484a84e0303d880c2071550b68801514000f004000f0100840007080c812000d12840b9485441500d2030669124801c51400c03805040071412804002006540307481d0610409582c01c826607042414509030700b5940744c84030001040a80101e10000001d00d6100084118003410241002e51310380711003038a40c01503541c07451b030624080e2030b05548421000071a40007503101c0407584a0050b120b415500c0c01410f80142c00e415452840510803400400f00152001c03d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 551301492 1250 551300242 551300279
    0xa11150918010905070906080615090907050309070609080a030e012723010207090e0304050603010315060e09031e0f071a070c02060306010c020d06050a020a02060a151a04 75
    0x30703a801c0d15410101d8a40442d42d0141c40d050501c8001d00e400c00071113030400000c1e03900090072910000c0c0617646a1a90b26644a0040b00c0383e400800c02e000c0001440c0c229010f180140b0008040ba8461030f220b840a86041109019200440c1e02c60580480001d111300030344600064189000640c080c03801c005a070045900c1041d8007811720303d10005103c4d03904c05507800c2074002074803050590706802200020307450f060b00d800794a20a58541114180c0c400c1e04004640040802030302c52956580e680c10401d90700000c1c00c0b84d030341030b640c1001c0000030b560000c0e00361035009103c005d02442c900038014480b602241c00c4c02900c2c07100040d050040711141c030000005840d07000d006046620700d1554240790111a072034000e080e0701c11300c8543e00b850009a1110300c00c0d294001c4003030074504404003443c000200b07a480c249400800e01410442080030015540d00548505801c0c0c1d0220b03207550703c504250302e00782c80c1b2140e0310031b9040e441e254040162000040c0841d80f140c1450b03201c240360a03118014840008414036 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 551302742 1250 551301492 551301529
    0x50708030f120a110426070f0503010e06100b070201120c111501081209040b030703060b0f010e0310090f05010c0801030b0a0219050903121204030905030a111509 71
    0x622812202d440d4410703664850341c0c0800400c0701c1d84211484800300e008901880300c4000250124503071507240d00c90001041403002e811500016502c1c50240c58040c000c3c045c0501a5003040d0980b0003503c000a211800b404091003200780f04c03420880400c2309904501c2d010380c10843e03484801400e044d500d100b80b424840703c1c0d07951094440040c4581c1c9107040c056141481118900b040104030b0540003050313480700b800440101d9540c40d42101c0000c1e006e01020049640d041c080d0040000030400590702c4080440000e5078015100a4480300640c1d54402421000d07401d40c001c0303008007000c54040d038040498140316001c00310b072800b42070302c900e4210f800341d4081d0808120090300500a00000320503540d403100e80218290b1801c80a102c04e24032030344450454038240315020035008a10f550910080d40c460640301507068468070700581c404421082980d0640105102c0c050204a030305012508401b03268112085480240701401409501102c2c103100030180081404201c3c2e255640d151764600280040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 551303992 1250 551302742 551302747
    0xc020402160b0f1e0406060e100f06030e100f11070b100e090c0405091207060b0405100e04030f0c0602040b070b07030c020c0111070e0f040c0504090b0c07050708030f 73
    0x80c030746480360310805402600303c1c1d0701450400c1110126840703d01d10b41503090308052159140c0b45803e86c0038080c0780e0018178026441e6400c005c0c600182c01401822a02e050742c288422507510300017a0112181d1120355043c5800003041000308041310b4010185185520000182040f240704134091a90840b0f0f42c2114019680018058a192100160b4000d00300881600780c00e8100a260300f981c1d002803020140c0210303120400904400000d00541041d2210480c02c030f9650907440c90301d507000b44001d01809120b21f24280100d0342c078030116050241a18042ea0303060b9295201d503101130301d82d40e4140d0245410002c07407104001c000b4502e40003030802840c0c40c820f1185c4401c084c1c07a10010040c0028041000c062800c0060074890f503001401c584100001e0a10440c51203140b00c03043e040810503040b0800c2036182d02c06121b411910319072103d1085000303071441111540c6800802c000e4510100c40504000b003130102040048c05104010407000d8868400c80360207aa565180e1803d43e000f030240c56400c008003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 551305242 1250 551303992 551304037
    0x406090914010612090f0b09010903021c050406050f090409120305060114030a0b1c03110f0d050409110912011a15030a05040206041d0a060e0f04120c020402 69
    0x58000c0180c9099621401c801540c14000000e0852464030201d02559031120414001d000d6a0710003030244540141c0c01c070800745003241381c0c58080c14440400310300500c2403241c00d1154580e02c408841003c0c07030344d0356464600ba1900504031841c0d00a0102002c03107800c1001640c3d80d0f95503038400d03040120305c1104a5000320074040d80203000c803030000380608d0501ca0301554540c0007403640d4080701c0d848110524001541c50b43d03000400c13511541d5074521400d03a400f5000ba4014140c02a0600880c007080d0000c8800c8100d5084030141c0b80d43d444514640802c10500c414081c054490308804034550031200b20f24180240c8400203031900e2800106660181d43d46c5104402c01c00c41110282d4007040c0955071038400e40622804030f84644002040303408455030f81c2000c102103540366400c0310010719001e03840310b540c600301c424030b00b058420030b59036182c06501d048000101f0391003481030300f88145d892034a1903525903110340f151031540755140302c0b80f82008180100080160b0751880074001c02404990f5240c03c8095 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 551306492 1250 551305242 551305259
    0x18060201050c0a2a0317132a05090103391a0c150a0605100206010905040f23010b1219170a0e0a060215011421030306032e0203100b040609 61
    0x10098010380300c400b011f1031040041131045802c80004850781c40c100030707034001007400c0c440c90f0601d54108640c0406820300000600c10181c16a1111203070449451841086242d1009070314007074802804400d8002d12400c0020310000b000850035903c2881a0300e18000c81881c1c5035041444098181444040000600205082510516000d4201034a440c3c40394403007054040c1d40c40740d0520a1511042c0c8903000141002050030003034440c0e641c092070050b0b0301e09001070740c03000b07922100c0d0981001d9840d000615180303207080d0381d10707400114903c405854110320010801240801c209801c2d615140ea101308103203040c1c41e00008242c2c0900070341c0c91804034480d140c20490328001c95401a000c6600041842111a000141007811501100600090241900081202841010141090012030000d820481349012004601c940030031805e68035080c1c8904030304141c1e0000c1d24030424643c3c0210480c40070015275903000b136030070140c03414002d0881503031101d09054a40c0a034202c90005002c00303030704121800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 551307742 1250 551306492 551306537
    0x20703052701020a2d2018010506160b090a030905060f0909040c0f06051b010603030f030b01030f11090a06020f03070210170718060201050c0a2a03 65
    0x1030321051400c80d0600000000b50303103950480e00038011041c907080c002407000300b00c4411000c8014031240c4402c0d101c0b450520034000c01c6c010040003420003811000603428640300e100c01202102943c80408180d0a00d014415182c00040500c6104415100303070b1808035001400e000d01c1a0040002400c034140e01340740c002c00d400c0c2d81d9413109000c2c85081c080d04640c0901101a00c901d034005460301d0a0a50721401e00c0b40f80f904082d441201c80707900d80c0340040360301e80d0310800a10040c80e5022009a0f0746081d50003075400c0314142c0c800a00010b0310501504906442600310000d0180145400f0444001405400086a08016a6545105d0009030151890138004094401041c060000c0c0c1a5108407007280c50f102e120f1410000c1c481d01d10060b000058034011261034052441002d80a44140342a01025003c80c066984500d0100c4100d8000140c0a1050144911500282065034280540c50340295490310070502102c0e81c080401c55414000c0709070402c901c0c541f41c0a941c1c1e40c44090384070300241c2220b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 551308992 1250 551307742 551307787
    0x302091801230306040b0412120603060501060807021506010f090801061202030d08012904030b100807050d020a0e09010603150b01080a05270c060c0106031203061a0d0204030602070305 81
    0x90b04004c0800010510304040349030301c950040317840c01e08540c840004a604009810100c1e100e80d00e00030000c400d002c043e5000d20305030b035007544610b2156151010141d99a100011181c0c1c0c841241000155265100c0c1a040d84030307607031034100075404c251038114281c25038005411010101004101d480d06620342000b075a50180c20605044000354100340640801580c003903103004a414820501c406400c4e1480e00b124000c0d43c010b81e4003029410400c10756074030507109100e0340d007483c480d90001007240d1511454080c1e10700c1d80140b910b0000c51500e201c1d07070001c0034001c2c2a0f15041d540c0e80701c008040b42d0300c040d00d180500d0a21500050220000c0300141201002070024400c041c50202009074007110b0b52901e40a02ca0741898101c800d01c00c40e1010751520400e1402c29070800008690008403c005400440640b8800e44040d030100c0f100ca4000c90407603a051040744172026040c1811980304a410005100b0b5000d0000d0142c5410344a44643e416a406035100320001400025014100c410440008800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 551310242 1250 551308992 551308999
    0x10021e04080a061109090f150301020f12130209070f26010605280917010e0307080706021911010b220c090e04030507140303010510030209180123 64
    0x400341000c0000b5a200c02c4510014210303580c3c2c1c003c1c400401c84d01400d0700e40c0710034014100000d034542002da0822040041c0d9101c402d03c5030542900700c030f920701802a1100c501112a030785080180080d0001c8842d60082c0c210f64089182e032007150003688a00124602c10040354580c101e041c010300300300511a50b08429140d008003c0c10303410b981c08162007548941190b45520f4081e44070b41c25070707500b10004688155180c41d502c84898043d4070941c4c010008101300c40d0045021958868010b42950070f031000740d560301c0e05640040150304000fa03c2000034141c81802240018109071080c184800d114418450309808a07254401e0000082d4090117400c0664000740c80c01d803440c00ea044840881030400d41d688a03009911242d00aa60720b12901d000001802500c01c0320f41182018207014206074001d0100707a90001c000c11007905038100c00800c50307040381d5002c1c005903203c0302c2da40c03001c40094104c841041e920028003c0e0300390840f90710940060180c200340b071080a00c000c04410420b0800740400c0c140b0300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 551311492 1250 551310242 551310247
    0x102130f060207030b0a0e0607030e0d08060d021c0c0605091002010902130b130f0518120405010c03050f0307090f050a03020d14070803070501050109050c0c0604030f020f10021e 78
    0x80c2c2c041802011030ba8001c40c99a00360b02d84032100c1002c0d001110446000d80b04080800c510585e0580203852940e0200050318803102e250b0a040304c1c00c8508a425170740007080b400d205401400d14402d420414540342100c8005100140e0340c022107044964080d200040b004103001d8070f80e24080030b42d041c0311001c0340000c0000261980c0800c0804200303a0020340c840b55156003000207500c0369418a80c01c80c22032001006202106001000188010742c1c4040c0380214045040180000c00600000540c2e01e508050f4200751400d00116000001c048044041203000d10500c003050500d0310182d0b00800080c0c581400c140d0900c4d03551b2503c079206500c954454010fa01c4200302584480c01c1202c6076582050138044082c5002c41103524100c2c0541c8000c3c7d9034440001c44409000301940b00a05950754010184401e44409034112182c0c040c050f5001c180e50008804078001901642c082400b5444500513142201c805400d0607003004c801c0344c0380c03014164002801d140981c3c40c00105000080340b00b85400d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 551312742 1250 551311492 551311499
    0x905070e100e0f040e0a0501140901020405090c0715060b070201081b040902071a2502061e0901061503270503091c0803100e070c0302030d0b0d02060304050102130f 72
    0x14003102100c60524002d0f486039084100986a90704110652a0300c0d10842c4c46100701803510713a000b010703441000c04038200d8000103e11507410600840b000c80c1c1e001803584480380c5548482640c4ca41c490441119280e40302c1c60807003030051407030013801d000300305511100382c84455a0001500d0450000c10400e0418580c131421180e6007040e03010b07102a1a030140700181c9071710480c984141052000601c903040408500f0400c1508100d1a40402c03100c2d4032562240701000310110260390b20401501c69600720410341c100c80740c0b030381103007120640e11519000007c10744d65590b804141411048100000000c2d482d250404401144524402c141c094400b01d50b1000705925198191640180403240d0312a45944858540b47d0144c80344409a498015000c2941c034281110340d1300d81a0f049100344d4002c500040001503c541c01110752040301d50301034006c0c61070402803114034070080102d00390b40340c5d1010342c0b980d0354005a103400021b144228170407400182d80791040a1904144000da601250b0362205604c0c050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 551313992 1250 551312742 551312747
    0xd0f0311070627090e01050103170712210c050c07140307270e0c09010b0306090a0e19060c03050c07030507030e0a0b070b19020f1b01150905070e10 65
    0x1225000000b1100000c07000703a0b4843c0030000b031495200b400da20341041400040d0a50640c4200d040724440c034800140c2003c00ca007006002d00895a01401d02c41c04481c01c1c903d600d00903011420333030000303864204103e10601e0103080111030940054000050000c1002800694104800c074081c0500548000821a00600003507840741d441c065910381c240c0c1c0ca000f0414580840e001c1820440550340148692004001565550340c00070309043e120700c1c2d0301d40000583c503200790100ca006580c05800d0012075a11082140054038402c1c1941c0c1442c0700342142c10550400d003c41e1069068072a400c08100c90360302410040560351302802b0310900e000300300000000a9040011691180d915007403108034201014001026014180d002c0e0203081f80c001440c02c20020703103c3e0f1b0644a00103401c451101d00502c1d40c0e9200890180004411500c2801c0001c40e24510354140021402c0410400214291510101d9a00c1102407036203c01035082d21802400826074111203009400c100c10f0b10b0404840f080706000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 551315242 1250 551313992 551314007
    0xb0604030206090d02030d0503090105010929030709060e0f0903040e070e040b13020d11030c180d02061201083325120608030a0804200d0f03110706 65
    0x2d00c80d0000040f0040d10303864051100d0b4030780350014265601901e1110024020b50300807141003e465180c5000030a03030f0b00d090f200c0c0750b01b103000345080c0c0b05101142c030b44001c08400c0c1d04c85625078548540880040d91003458016240070b000c1d104c1a413011820450a0344850075030280c034031840350f08180000c1c040a00c21840d0158801c41a03d8104120b030803401c0801c00401000308010303040700d080481030480c00ca99800901d2100c6508004011400d20543e007025140409d50390705010420801c030682c1c08a0504071481340540c0018941c0044206550000c0c0301c0750b2029048810f0f280401e801081041e60500c00103c0e44140600b04a80341c00d15260200e0441c492010f00c400c500d030205011405512081c500411100391040c005480c3c50b2281c14003521007a0181c402c00d001e503090180101c0c00a40100541c1d0828420341c80b0f4440300d8560341c3c0e6600e900c0b041180c0325a044009020074403d0742e0f9400301920000c50103114402016905810700600e510000095069950b0080000300041c1794483d00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 551316492 1250 551315242 551315249
    0xc010f05070e060f1608091e0306060d03170108010905060a02070c0302101209060b033c0f010c0f0e0607020a0644070908070b1312030c150b0604 64
    0x711159105100e5084d25128040c1c1007a4024103a0382440c2c1d1410089a4002030042c2401110000402c0e64a5045220055401a86182c05412650104001d41800c8094003000d522070305200d2030703540f680c0c1d200c4850050240d0090b1201d03911404070105008080c44101c0d00702080ea03100394035266451320341d801c1d224500d04c0000d000310040e8949030a16413040001201c80c900c0c07088240800091410070304090265039840520030701907080a2500062008400c21407101c00e2a40e900300a1011300c0c21b2640c812682000c11124001ca541c204200407003031050301c40460081d2076982880b00036110003409560900b1209009660810400e000342c0e40d0381088104558042c03400014211500404c070036801c8068035a524091110154012040e0715036181420396540f4541d401c1f0141c2c0c8406d0100c4041c08184280c1c4002c0c1c000002c05d00c1405114001080380124030111391804943e500016009c038040c101c019400691308006090800c4008100c1100c55100ca80c070500c00d104040000402e0381c800ca10 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 551317742 1250 551316492 551316499
    0x41e06050a0f0302070812040c0b070f020d0201020f030c060a060504020304021f020118110312070c06031820010e0609011b060b06040806010608090a030c260d020c010f05070e 77
    0x10542d4800d18443d4040311446030b0f1015030a80c0310008810149040082a82d080f0703803c00d59060081a2480f503402900e0000350042d405c004001c06036000c0c0001300c070b00418268114066a4618091203404100404102c170b203903030050109152070a01074003240c8041d00b00d9481580100180000341c0c1e030316180387c21700d00620302e102c004055203c40240d005010720050102003548080074a024402507488480705040d00b03030203031104a007043c0c000c1c182e14070908400509186e0f80308420b00001e81720350301c4181011004014551440c0407a01c13004c03580c40703170017030001040781e404d121034401542e1040602e2120030307058484900705090000042c06514400042c1c000ea0b620f02c1e880d070001e00c955500410101040582280e540301d8480c92041e442d4070003401240c0c049200310000c10782151000545000c13254060b42c0d5882d03d02100d540310400d0307001054007403411001c41488811040164070007004030100c44400180d44440f0741c0348082c02e54034004080b808041c900010840120780010722448154802c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 551318992 1250 551317742 551317757
    0xc120b0a0228030b0310050705031b090303030a02040302100f120c020a080d06080607090b04030b06010e041d0f0a080313020d05070605090a080309030c130b15041e06050a 75
    0xd4650242c0303800805554000040001c03107030080c07640c1551040b6500702040e000d540a41c1060481c04c0c081c1c072010f03075507403000440c10800034254000115070406a03046d003c0b4040d04c2c00714107400192841c1c20130b5074002005580001c081046140c64007002007500d02a007041941000345060242140303a0070200c403603965071505a80d0020034824801e283c42079a200e400d0340d4070b51050412b80d90080609019441803071007501e0108402c14080c40500c01160300e250f4855140900f50b603100d021241c000b0b000c2c1410b108542410040d15995405603541e80b0604850416078012125081f0f481d0140c01e842114181d007040e581d50000c1880c0d0ba00300c90b845000c0120040781e0454520100d15408402d0001501c94007941c01d002c280326a1010091020300c504850740400c4a40301c461443e00c80c8141e0846541c55071000f0745481681c1414021122505042c1000198580d4a42c0c0801c0076a070f03551505041040700001e00380400c41c0c00000104402030000b065600103070030284003604603c1040d00440030300250 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 551320242 1250 551318992 551319007
    0x30b0114040501090c020607050d3207080411010309061404060b1c050c040b0d14010b0f060a0c0b040809030a0804090f05130305070813060c0302280206090307030b130c120b0a02 78
    0x210380011000c55140700615070b20384081501a56020303032031000800360300400be000c42c0603540324007407083c056a0032000030a01001004019401800141c104803011510740c40aa59200c1c0030b108850b11075030103900e01090300681c0b813003045011b8080354181c01850750038100c0440800d40002d811031280e54143c90000c2e88981d00ca00088207150103001c010503031030401d10721500284c019082002c140e4403d88511041007686001c0100306d000d86841080002d14a01d10711011414856800da0882e01801c01c6031f1a00c0c100402183c1011540d503001d4614480014007000299a42c0c401c501840208200410031810a002e1a2400c0980e2800c080e0820030040340000c10b01a407101111a444042c02003038184075900d100182008030210010340c0035015440d00c2e91449240050000400c1071807004180c01a8000c0d0708002c0607801554109030103104101c2c0100004840e01c03c814041d54210060741240c000900d42442c81c0c91700340d000b00300e03070000c511000b6001034920300752150403001c80040562a40d01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 551321492 1250 551320242 551320267
    0x70606050301020f0c0c0901030f11010903150212060603010f03080f1903090b09010608061306060504020d0204031e2111010504080d0c020105010f1707030b0114040501090c02060705 80
    0x2400d4000030307455440000d242c4040610f060040c01000300a00503200d000c2c101c0404c02c581c074402440301900142d403080351500020885881b03005050f10504019407010b860752070300c021034044004011030169000507104543d2847c603100c3d80d4881c2003195100d10719810296000c0044c3c900341b000030100000403659104400c079160980c0d40030100c45404805013000303003200034050031101c6400d0b00c044208d0310100340e44400c180078030404d40d02600010103413074490042001c01c0c13040542d41694415582d1501180ca030340e40e40018444560405070140c0c442d41107081c07802c130169440c0c0c02d0a808281d101c450a00145080854241490003120707041d4011010210548221040d062941030b1035107080c0802c003c221500d005040d04000381c031820484048003110a9088130b20a000d0079004000401c2c0801081d000718805c1c007074131807030101500d2a0603501d9071400817040081c4c021034000c8400da043e05510341003a10450b8010f0140700c1d410f12000c20800b10181d04c0e030401030300c40c204108000807070305040c80 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 551322742 1250 551321492 551321501
    0x16150608251a0d0e0c1005190f022407020f07180b040b0d0f170c120702030111031614030c031918050f0105060a060519180303020a14010606050f0706 66
    0x3e2036034050003401043c404182c0c840c5c0e40c945410b48aa403c0180040141c0c0c0720328140c42c66038403190040c101d024a1202d0503902c400d04215014114401c103c2109982010540c44200b000c01010540038603003048000030707085c007000000058155210b404204806140c00800c029610410007000981407480000302d0050301d00b9000742034011409002140802008082010040340a000b0a2074241aa0408032606102d408501d14642d4006c51021410796200001011494401400001c2c181505400300307000da001204c0b00041802c0440c652003032550840e03105603d400c0d4400100c2d1443c034103406071229900001d86100200584c00c03103460114200c5602c094424510101180305003041443d0040e502c0d84140c8054965500300000b040c40e03400d0420401017a500591111410001218094408066250b05079010400c200c600c00440e0841c0d0a040d00c00385d400303940a0801354245080c0001ca0f4031003500510156031403d4400c004542d0700400703640301d020003403162035070369600c0342000c134041e0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 551323992 1250 551322742 551322757
    0x3100311030c18070e060f0d0203060631060203030c12090c030102042c0709060f0302070f0c1d0c031305030702030115260606040216150608251a 64
    0x1c004410f00c05960f107450250503200d0240ca0b0f0300d95400d414880c0c00e00c062409412001e9828001c240400d81400009130061030703201c41c01a015a040074512406100c1f15403200000d145100b520705001c81c40988202d0140e006482c03035000440c510304080c00d210015209044a150386054418041140c8070070510039803014410080c000d40d1166111203d0000e1096411f0607104104000000d0150341030b000415144520b050b5101c1841c410301d80f04060700e000d01ca0001101c101a0708010060000d5148503c450009000f810010f140034200041015003500d2924001003d012031130070080d56a4114003207951101036150400b40085091070218598010300340000e41c5135082454000c001c1f20320780c401d070341110000507001912285400c04101072814100443d0255040b60000409609068001340206040c9224011808070b00741c8900e1440e88018501c04000c988840042201c044200180105034014889010480403200d02d1450410807d00c81c00100c7da03130700b20364000801c1c1c0301400e84065 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 551325242 1250 551323992 551323999
    0xe0606070b0403031b0903120f050c010903080105090906060904150f050c0702010905060a0903060b0a03060e0a03020105070e030c0d030509060706060302030105132f031b09010b03100311030c 84
    0x340e04043c0b074083c01401445000b200055040f0805100282c85a0300a4080760313080310200c043d0340c450071000c0301e4001101d014502801010400c45404190074441c0c11112400703980d40c0c5d60194100f0381003083ca50710152070b03815191310210030702a195403804840c0341c00a0b406100c1c159803e20500d500005082e50f01da00c440141e00c4c02e0708001303182461400412069200342c3c0c50445480d11803040000501940c031920002800d040710610000382c03031b6803142403040b00050070807494a80d25a98103095030010004504c090304000c0b9200b00f0182c09005280d00000c003410070804104c06000426590701305034920310710602c4404001d50900d40540704450301214090001d6554041d141000c0025001c944002c82c02036181c403001a00082c0000e00c1c0301c00302a40115010a20310203140c10f10b0780e00001c0d5002403511010180d01c02d00300e580c200b24070300d1100180003603a00003810310010041180016880f0040201c01002044240e81e4000b100701e0070b803540004240800e9207400040b03403428030b900f800d1541 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 551326492 1250 551325242 551325263
    0x1d070303030504110105030108100b03030f070302100e0d0f03150e010806040309091401230301020d0b0a09060305060403050a030e03040f091d120a030b0d081902060702070e060607 79
    0x18190716800603803040d0300480d40c0c41d0004c0c9020004541c1440244101400c642180401540081168103e003c6480000301200c2c1810300905034160703643d01c02c480440c0540c0c05000000c20030380c19802980300340c0f06030710041e1451040d4040090000350440e030850042564901441000410000d074501c007501e04401010055a19803115a0351008180d0701500070682c07103600050180d24074001c00000030504030003a01a6460054040107058241448088100e82c2c0300105a141d01c00344043c0c032203100700d1040481c11490072030901c0072400c656001009150b003000001d0001c200001020f80c0c1050381850300d01d954004d00042100240351281101340316010000d40000c16011a14074101a43d2108104000d00e070081403030b02c42603040c908907125003034202c845028200c0a000c8090900c018070b80c1404202e079045030b0000b030303030a0512503012180d000d000f00c0e03082c041180000d0a0200d07a03c4500090003d0301301040301a6680207d446180d84c0c41c0055400078400d40c0303a103401d845a06920181946 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 551327742 1250 551326492 551326499
    0xf013e031612060518040812070e0a090504021503090319210b130510180204060206010501022e090b070305040b0c072006130311240d1d07 61
    0x8114101200020300082c0310741c800b8000d40115031040c003044510040c1303e40c414a40e050440c84e080c900c018006c4d641c00d10140904400315034525000c0388690000d80d03802e0780c0b08800d00200031404080e90044e2950b40d02d000104801038a540e048035282c0d030b4040d90807607280e54607020b08918520400c80091100201403419801e45a000004006881c007034401010341a40411004011192107911450703006180225030040d890696002c581c0240c2c4070701d44200c0181d100c40d80510000014000c480d0318660018003005280c0e07040c8030090143c4001d101409481105502110401c1851948454481440000c2e040000c01d980d01c030a03110fa40c00800381c0b0540ca05080c020340103000c00c03182074a042d248040002c0b10082d1040860320120382c88160702400d4a05514800c2d07108400c43c0380030f41c001c0810001c5002e40f1905800090046120300c01c0b54802800340303024011041c3c0b101003005402000010803410003008003080d00c80030030744130b0741c0080d0b40000146a5640c4c3d04c0741a901c12114020030300c1c0070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 551328992 1250 551327742 551327761
    0xf020d030c0209011d0a0b0f0d05101109150d02210402041d0307080304052e15060f0c05100501180b0609090f0405030d050c030601020f013e03 63
    0x1140040d0007221840301aaa07908140d00040c145c2c41901c0c0080246480080d41240465211000144c0c010f0070301130007490300030040781884a180f203090b00d042e070050700055204401406a110100c000035542404c1140d145c0100f5481c5002c1440c141c01c0d81e801203035080080500e41d0507201c00b04821018040e812001118114034480d0944099000b64100b400781c48184150707102ea90540610240114581203580d1600c0420343c00c06030085503140902c0880c0c840745405045c0c1500c44a64145007aa40f010440a1001c07c4803d2030358402c01e000401d82c000c2140a0308040803104000281c1071800d0b0310701c4246803003070510380c805610014862a000c004a034140a0381038040c0c00850450003041140a580100549800380c0d050b41540000c00f0070004100900b10400715811522071012642803012581080341a201e00f00c8809000c1040441009469070f8100400428004154002c01c2240184c95a07212031034002c203140f08010b484543d04240c0324040c44075013102c440c011032a01c0c3d203904000c00907 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 551330242 1250 551328992 551329007
    0x120a080a0c0c050d110a140f1b0d02011d04090525141c140313050f031e0a0f0515010b1201060c030e041a190303080c070f020d03 57
    0x3a44502850840c86851460140300d202d44426000741c0140b4110b21803041c1102d0391302c100495030f0078031b01900241a00045100102a910440c09170150040c0000c0600a030b15240742c415220300244464400d074002034a451803004003003502844c0855041c440c512103842c0403070314903c80c550880e00d401400b8050103408a0200c0c460300820380c5040c0140085588090b43c030b103544c0100052549440e0f8040294544078a48940304403441c034103881d0311342d2280c45280020940700034903140d03a000050070705554000c0784000703006800101c80ea8526122030a000c25036504c92030920b40708215004a14011825082005000c0d42c5c0e4803c21070645c00b48286030141c0c8455a0041100201180304000300d418000c8105030380021800800d170b07442c10380c03a0050468050b03203481000e83c288034003120140c00c00e4a5034011090360b515481140080310301140e0900c028840495072861260710890424800290b00c2510542c01804541002c1d4031080300e41080071226200480083d1300070220b08600d801c140c1c00c82d40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 551331492 1250 551330242 551330251
    0x1081e0403020a060c020102041a0a1704260f0313060608030a03090b181c030b0a1e060f05040509090c0d05060906092e0b06031905060414010302010809120a08 70
    0x4240301c5e8805c000d07001e034240e009500411203180150701402500040b90006041846001d1401d0302455621204d241c0042c0e0b801d80d000e9490005022805540d01c40d4148030355101d0b00c075041c030380c3d103070011816a0b0095030101400013203084480e0607102050011a0700140c014082040070703a40da1b40941e40001d00208050801102d00103001c00c001800c80e02801c40e104400da0000000e004428040c414551400220100310b0082c0755039010b400126445600804000e0080da0040750110301820315001160050307984241c041084400380c1805907036105050703030201c1c2d406640202d01038880c0c010303127403d01d141050311640100c0412800400d02c00b0026919001c1d120704004d40300340e0b40790128269110254013840282600c403400c68801b540f902c2c501d4030290354000e82d0001515030308000020750258016601c6003200c40b00170500c801c04450700d11902d6006202110704100000c94201c42c9007000405110103818401450000b4800340710900403889440300b446640c5a841500702c03030144c4801000c3c0c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 551332742 1250 551331492 551331503
    0x9060921100f050405060c070c0810140a060b04050f04021c020403200604060525080c0106061707030902011809140601031505040b030304030506011d0f0705030601081e0403020a 78
    0x510b0a0401d403030034030689025582240180070751740d41d00c101e079420340d07070103a6030490340082c0d10f1900042d629002e0018080b0358122100110b82d03000c0c8005c40051580006d002d0881191800c002045460080401c03101201c4082e616121000d8050000500901844840b10458128000e500d840054158010000d680c8110040d050104800111003407024035040c41c030380c01100c02c1009003e001c0c01080540300c072041c24000140111404400d0b0044c0d41e143c404120b0302040d001c18180103031802809a400900418901102480c48118460603054009030004c410b02d9075a80682c02507902c940704a54800c0c8244240040403036503411010010010540317800c01c080d11441c0415076540c400d00655442d01d14411020070f5041c00c01082200500d580344010358507101c02c01000000400074400d080c002e10045070314004400d107001031994641c0c0002c005411001d0a081004425038211742525001182072801e44072542e5100d0b03c2048952100004564000264080108140d40040e8440e8002c2c400d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 551333992 1250 551332742 551332751
    0x9040612020a1a0313020f03030a020d0207050d1509020a1a12060103180204111303031106010f030203100b010903060603080a0e091e040c03170301031106030106050906092110 77
    0x10004480350018903040d0039a0f14400704085180e6503001c01c0012039042c0024896140000360400091455001481032000f50300304075100e584950f01403012000400007940c8400c80e507400d541d540c0f84809503960304045642c0c0d9403c010b1083d0b4548602107030161008203203030415040140c160f0500c0d500000c084a981d150800d0004003654400d005882e480001405595404003c560801014010482d02295615020303c0898032448451a11310000d500a44903803490001304881d007030600030160040000320017091402c10040c0c400069109200754031000c00108801c9040040f98142a641d00c0507054500303041000c130a00181c0310081c10940c485407213a500b503803010300901c2040141202c0c447c240741405500c1320350310741c03c0c044150307442442441c0d047e450903102c1c0e640e60301380c03030a1030012070700d02c803000c401807081114a00b1200d0390351008031100c608540c03400000034054490302c0c404900441012075801c1d0035440e4640c40c00b01400040300c19201485501181c20354170012034042da83d825040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 551335242 1250 551333992 551333999
    0x10518150c0d0203040f0905070e0310021312021503090307020a18050703050c03150d0503070b09071a0d0e2a01031406150903031b1006060216090c020309040612020a 73
    0x701e07170441d0440b0784c80c04000c51505204000828000b0f0203041441107240085e102558140a243da61005801c0010f03150031814000f00581e001540000707080100c49040c48015a40b0301c84410924a51001201e540e41d607032040f000d0840c00b40c01c1c0002d40052034000302084443c00302c650310303e044ada00d0200700003558522400b20141d8405031a001250314003040850443d510644240340c0348403014001e02e40d1000c56688403032440d4000903043c0d8003418041c0074802d00640c14043c50008020090440440605800c02c04000b403141e502d1000c1502d603a070003441c0402d0b00501c60701c0358a139907111030814071684a05009040c22562031410340042d16101540b404600c1d088810380c090712015200305603c55007650680c2c0543c0c084141c1651501c020310402d01e18800114240c48000b0480003c0c0091103d802101416141a40c00000075074100741c1000741006030381502c0908851015402040c040b040d4a404c5e421441007141c0e10b90000d0603c08085803e140030381d400d01d0990b20903607800c121643e5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 551336492 1250 551335242 551335247
    0x30010501092901030b150705030a02121227011a030105130807020409080c0303180d0815211b10020307050a290411040f0e0309010518150c0d 62
    0x150b0000c41c100d481c919450400841d4030982c0412100c200180104441e603002c0300b01401a40c10149040710340750b20010382407001c954148180303041c96100086e468101802032a40b4070102800400c3d4402031400e413031100c000900e4001d69000c103005a80d00030041d0501c10b5000c6800d815020a6540c000d41c203150100380c2c1003000661004103076070403219490801681c2c0c0c0c00c010141c44410029a40d048090080400c2c22034140001c1d030048207200d540e40b24083c84880c1075400d10f034000078003200340030044080100c2d03202c200c0b0307400a00110849600140e090708026825030280340480c2d00045100c2d20784164112400e1510340c000d17240e001c84007441290b024a100726500e1240c00ba0003001500204041d20024600d0b84111100c0e01440413a4000c50750601051500410129400c1d141c20b42a0343c150117803410036102d101441072203668103008440b0040d03007481e500d100708500a410030400190002c0460143c00c0c24002a102c000d180c010044074282c1401007942010400c81600d00800c0a040f00c07160 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 551337742 1250 551336492 551336531
    0x70c05010509031e030c030a17010504020715410604052509050d0c0501120e03160c03020d05030901080919022206030c1805040506063001050109 64
    0x400080041004d4891a00c0104a00005603440300e207a1100f446059541c3e903003400903022801891b0b1341c90b030905d0b101c05020003d04006038045401148100410400726402e101c005802d5400503202051894030714580d09030030481d02d05c480c00c460403a012454181d401e50280d20910070f000000724042174a440c1e0411080780c10a80f900c0728610200081508070354200e88100581004034104800f1465440d070201c0d0704400202000c49a6074800182408a5030300301028a071214045081041450100100c01d42c1d20b11072141c0d944170481c494541702d4104034000c51510086c503400b606e2544c000f6142d191440d80c076000340c20141d0204442c0740005980c19000140f00d10100d00303052000d0041c06861702400095807504000881145000e0103040e0003000c18058900110720444003000540c6c641980680b480d01d21030b0810f4041030404013440045940081c3c2d064000c1d40440e09007640200300c102c030105107041102600d018120001010b4198072040d40294100c6a03100300030321040c0da80c20103805100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 551338992 1250 551337742 551337757
    0x110111090f03070b0c070e01060f0815040905030c0601090506010507110906060705010507020c130c02070b1308060f04110d031b140106121713090203041e08070c050105 74
    0x101003404080c086191035500000720460140a907000280c031041007a0195002203074441065006c4034080004883c02400503004118910b041e11403c3e0304034100500155020300410510002085111860b9585600c0320481c02e601c2411030f9599000c00201c1030701d4200c24419030700384914040c0085d80030f5000e0001c842c0701c0b039031000200f61180078110820080c3c0f68003510a13078101c1c8060000b04000b0300d007440761600031030382a001040c0209802c070801001290380a041801941840d035400f010540010718007066075096070807903850303440202d14908182110303480101144500424400c0007030380045e4030f50045009528100300c82045409111030a012054000c0025080070070705400100c50301d4003080c281c1d1044110310110010244144d09480c40c9030041202071030b18404075010000c2403035030040c441004000c4181061100c07458124000c150b407082068054000000904002c0904460f200b0282410314800340e1044c107040003000e42d00170400485401c2409d090100c1d180d0700480c1900c851 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 551340242 1250 551338992 551339021
    0x1f0f08071509030b180a0c1d010f0b0409020702040e1c140708070b1003200102100b03030405100e1504092f070309080f031905040b120601180e071101 66
    0x5a16601c13114100d845e24541070320410f004245400002810507a8042c00810300d055407244055030a04d0a4076007002c1c180c0c81b03081c40d0789034034004001401401045c0c03004c0b10355041005888401c1400440c01400d240c0b00804554040e110410525001c0c00007010943c0d8400d40c0c841400868169511150780f00c1d41c000940b41000910003000020344240c0201d600600030000341c0c00ca0b0340d81c1d42d5000204c100404004070314407603029200800d940d0400400c4680d40d00d4000c01d200703440000000c42d88030301c10350150f14010070301500c42913034050043c60a01040d41c07001e040d8003172a0b6061004661076402c18001e075118141850041c0802d02c03900d07400320501581134000300d2580d0a0601c0110344550003403100b1014040c1680c0700241c5170b1814080e05004109200107169600c1e00d02c06440450b007001490241844010302040c001800da0101381c412203601c1c181c03003013501d0b218000160785080340b01e003020703850a003850300c04900520030255041c0a0300154503200c1c800f6002100c1103098a40c0710804224 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 551341492 1250 551340242 551340263
    0x70501021f020d0c080105101b020105030714120a0f090b0a240b030604200301091a1e0f03011a060702150c0a021009030201081f0f0807150903 63
    0x3941c0044501c1c01c0745103410301c20700516012108002900380c8501100b01c0c004612140010001c41c01c0003031a64034035181c14508004140c0148003003074040d56aa901c064100100400002e030f045001c0c0c9240e00450102c40009034468202c44101c4402e410200e440603d038504007032040302e402c003080c01008440351f0f010b491001c41e5962120700b5070003021402011030b0400c114200d01041c000040144401422144103017956900d800030511040e204614188201d003103509080c0d404042c00e0a056070b054031903529002c00c0c889401c80481140501c020b402952010b0104900e070003240c02d407072404800c0c00003a04c424080c41040c20425003203c0d00007001c0d0710000380841c4d940340c00e451710f0340007011010301c01001c414142643c54032685050700150705851107540b00c10401025440c240c500a811001c441c0f410109503419540000d21906016006558201c0315900203010701402d81c03010f402410710741c400886116070b150584c582c1c511462060260b4800d8410303a4140b024172403105034090700c3d0099103030003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 551342742 1250 551341492 551341513
    0x30b071b111917071707030503071103030403020a081f020306032e181b03020609040218031614190611010b061902010c0822050a080f04150207050102 66
    0x6942c104010507038241d0081030720040380b540400d042c024081c6003900300038002a41841e606294a40c00406082c0c1c9a5018610400016400004845415034401e81d165034400141e404a46980955000250301c40744a51020075880e100040c94480c090150246542014102140c10300300d00c03041d500103406400141004242c0440000c909030016280329224110309183d4565104858040d6000c154041202e12a07405100984280702100041865000035091a41e80051410300c5074500144c012500428101c01c4140d540c82d0300d41c4455400b07800c0c1c540c07c40b41d00500c00542603e40c060540c490301101c034076100c0d9042c120038400050207051040d4461302e0418000741d5042c80b4000380c0189541d21440f00381031580300c15000d410386607050040f50101c0050000d000e800e44500501c814200401181001803c184100a8040614032180c00c6000d11110707040507070902900140c044c201c12000244905220703480f9004008070b03500bc80c0211354200013004100e858694034814240103a02106050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 551343992 1250 551342742 551342749
    0xb0a03030e060a0c0b150307060f02060601081f06030f060e0f040620040902040905090307030804121403090604060606021f050a020c0d1d010c0213110f04030b071b11 73
    0x1801c40c3c43c03103410885071031021561a044402401c40f0b0f41c8080d1800d001c81c0356400d0604001400291195040070305209140b40402580c1e1000203004504000001d00424860707080e0300c00c0340f044100744d0034a00c101d4036240e44010f000750030001c010b819001d04d0400006000b6000100e103501030010004103880c9510703183c481c800035106804008041c002e00944404c0070b007003d0b60061006041485025817283e18280c907500450b04001c10181240d00b0400c0101c00295210200700e81c410344c8515000b51101c0928000c9680e801c1c0d6500e08030200c3c4000007400a45100050528072030361044600723000b0f03151150800c070385448403080d0fa03060047c0340080021816a035a088554040d0000e900141040c41c031694491a181d90b850002010422000d81d42800c0741540390f66400009007801c04500d80e00c0c1ea540494641014a1a0031903195a240d181a02507100c0700704850305c1403240b201d0561a40c0d220304000452540c15500c400c0482e517807611070080200068000303034200340c010a48000d015a07444c02e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 551345242 1250 551343992 551343997
    0x10f1706180123010e07030b030a17040b040b090406050d0f060e010b0a06050d0e03090a0b0708070f0524040809041503060e0309041d211e0306040b0a03030e06 70
    0x921032039540b510002103c0340c0d0340c55003601032210baa482041c1107516001d5582ca144070050020f40c00c25080007a51181510000341d01c10f075055118085101418949a01c455503000d40e8000706001c1e400001c1c00940c0c81c01a0016040162044a0030842181d440041103102c0c800070100801e40c511100c10300002c100e0366400410b0740d10721000042629210000042c1402c5881d070055004a100450500140b10180c071942544800d40c400035803803c03146400180c0d0b2660307584a00e801c0c0c260f0008840041011480c1510300d4641d009003040000f1140303145c51a15006070a20a0700807501d42818203d0074100895018003580e0041001d61070300c0b074400300744000b9101c00e01140070601d41410000000542c944038942d0703d03074003000180d80c68404080070442658200c090440c10903400800e01d80c0c5880b40418002c0b041d1070102d48020785035003016403070252070180703038076640348003410f002d2030290b84840c1402540304080c00c550030840c800c0d040042207560081030001400044506101c1489401c001d0300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 551346492 1250 551345242 551345281
    0x90501080d05220608090606030a240f0204080307260702040e010914031b03040503060a1e02070602031509040b06040b121b03060105010801180504020a080a0308010f1706 75
    0x9140343c400800c031091850700103030382d0129000071100d40400032000c409102042d046902200503103040446034550060107000c074041000820305400001141b428141d005502c090040913055440340c2d81d1750f0242362a40c0003074800340c690241c00c0c82449240380100b00300304000890490801d0030310751700340c092000034140380e8034409107996142c40e420007142c103044078940d10300e1038500107559850744a948007500e295174580c0c03d0301a40c003d01c4140311a95012803165401141c2d440005103003c600d80c000c0d0419515034900390b05480c4000703046030520803a40c0045100722888000c80c0d0301181c5c540b01344203031242c08a8000d00500c03c00004122980740540080e00502001070103071a0500c0b4500d01c40b030a104040c406c04802c640c44004412040c10140030311801407009092443c85507141032034040c140141491124072044d41c5400140c2150f40f441880c0000d480311004988a1070345500e0060a031741001c2c052244d24050543c00010001040f840c01d0f01050f50340000350140da1900c075002c1000040118 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 551347742 1250 551346492 551346517
    0x10f030201170f010b0d0f2a031a0f011e0323130b041b0e0f012c0606070b150109080c150304170a0507060c051e070c0b0a0315090501080d05 62
    0x1801c074203900881d40504000aa1002e0742035481030a140c4121154007488008c00040c0741c20303c3c81c40680341c0340202c0c12600e280020b0b0307100721300029840d004981e520310000e03044c450000400f101c071400d1589a40280040d1960341c1c0106817140c080004071360f10741012141450000c1c0d8450100001503c10706189402c248034140d002d00082035480e006944080d01e8000d1803c00a0745d104022106c00407550907070062010740f003603458445c00300340185945a0078a4400140003520804911551680d008036422150040300d110b42d14103002070822840d4183c6203105000840420012403048070115548000150042c10341030903150100842441d900028070580302c62450f100081103802d0b540c001800c40002a03603c442c0d070b4402914084003114141c1d45c0c080c08208052181b861109410400c0d1850b281820000c0d41e210303022441c040c1c003146401c0d0000c110680b40071030750500c2c85800da00b01c000c0e42c288081942040c2d6840d00c0044013141d00900c680b610940c480d042c540c41c201c4c002d8008098401441c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 551348992 1250 551347742 551347751
    0xb0c0f0606100c051e0a02090a15030828030203060102011a10030f060b070602040e10050a09020d09050708300406030c020a0606120b09061303050310030b010f030201170f010b0d 78
    0x550003004500301490141c00380c6c0c00c201450004c500c0c20070f4400798000001c150411403480f5004105a2406550100400b014800501011b03000c2e2007040c40c07030036001e40040152400d200010300030041e40041c0c810398003540c20240840c4030340c03400c0c0074201d008800c040e00c061641103040784224080d00302516540d0b0f14503a03c40000c10400f0a050080c4803950080401580e07591809240004c460b5005210100c0c103103000d00d050143e961f800ca580c10403542814000358450704c1c2e8082403070041803044402012486020310020f1061004120f101400e40300740c1000e68100c650b001c000481a15181e4020f1001604210034000b241c004da02034080102e103441111805007499455104441b5a5004503100d11121840c180c100718440c101254050300020182c602418038540f0040740203c810002014043c0200c00a403070700d03908046480c021504604080c0301d65a452034130f64100340550000b68001442400256180c80404074814040c4003400e0910800f6860411140140d81000e0800c0c1582d5484 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 551350242 1250 551348992 551349013
    0x903020604030602071a04170f120f04260910020c0306092d0307030f052b0e0102070308041104060306110a180503150901150b0c0f0606100c05 63
    0x400001d000070314070a10700140c0e500c1e083c2c246030034415940000c0178002140c103010440090107513011114003d05031000d072910750a801001d0b4402e4011080e07107005000071101000300300c0303d8003000c80303010728080c81e104118513048201c6016840840c0d0010900884200203074000d40c2001e20b0f407002c070440684140c840848001d00006d062600a40e0021007a90001c1c0c0d045002c0f00711050340301000e110511010440449210a041e124041e046c00541031052456004603640e000d402114140c3c401d00030303001e40e14020502030100180d0300c0512003240500c0d0207403014040505200b2100c211380c0649030300c01c81c0da07540ea0340c1e41d903024a1b08034000c0d00a40c0ba100000001045030055000750042e0006840d242c85900310018000030390401c094680501080d010081e80d1808100518290352440c2d0301c6507199211100c0e41d000d08160129584032400a6100085402c1c91502505045107176605031100c04140b0015160350700c5003641c400b179201001078041210b1501444450b80d0251081c8140c4002c03100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 551351492 1250 551350242 551350249
    0x5060a0c0f2307091a09041b0510050a1b080f03090f01021206091b0d020901090e042405010b0313060902090906091e0715110307030309020f0306070e060a090302 71
    0x101c03034950031688441404c2c070602440d401030b004070380091100d0000400d45440004c20494000e880030300308112200703070a104070703d4981c0b410014100180410000c403030503030030040665100b100c80d6000500711512010011030761009a0216070742004116052010150280c1401c0d400a06022050f1040024100340d001003030001e4a80e01c0c1d060401c441240c0f4220781071140d901e00c001c0a800314100c0c0030405210781c05030707039050314582c21403041c1c01070303c840b00d160050f552045182c0050180e0916032042004001a01982c04600300d0602c001b420b06144120914058403004c0c0141d1104d0328040c80000d206060700d40480c14480d02610000c1007200c050f8011410008007911114056040300c001c0000b0340300c0400150b201c00d44041d1034040c101e01c40120403512010300d030007400400300703006d040c0c00d400c00d1080300703106110703145030055903900c2d0b0743c41c0307005002031140341c030100d000340d007401c03000c00a518000c90524410100c50f1900440004c4650030010550710461060044c000400c20200242c1c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 551352742 1250 551351492 551351543
    0x106141005040906030614010e070f1803080c07060f1403040f03090504050f04020108060f03070b03040201031409010207061104030f020f061323240309031c0b0a05060a0c0f 76
    0x6001e86c50016000034584408020100140c05c200810542401403120095005040d406007000a02d4201c0c421803100c01c501302a0515a0f01c060600030b00861403a04151000c600d1f50f0444655403190041840600d40603900d20300703d6a100815a1014000103012404001100602e103100c4e140100080d0b84501c0004e0444100f540c1d5602d850441200300300440d40c00805098000100310344000318221403000290759408a80621541000003001017411039001e908078a075087c1c42414016498030304611714034002d420100c03064400c582440201842c642d42c81007210103913900902195880340680e02440550000072585c2a0405010011200e1003048006c807480540744036491401d0781c0c1000c01400a0750f50700c00e0040c0c1d204200001c041c00c1400208000c42d2900950f810f42a5200d5403008509421402180425144807040180d01041514258800b40d10ba01c030854007401030548560500c40d0038000e0500350004100c2d00190310020682e030100d00040d640c45400201901c030041040106641c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 551353992 1250 551352742 551352749
    0xf110d140c0a0504180821040f0c0905040b010501050a121b110705031903051303080a1106060907031119110601080c0102030a0f0e2d030106141005040906 68
    0x26007010201c1e101629203040303000c0081800311010b1191840c441da40b0b508801240400802e9510001003a048500c110502c0c540c41c2e408400c0408a18540350810420038802d00000315803420003200d010a80654a22426004a40090150480303a00781401541c0d151711205501061011400b4480e42840190040c0c41c4a450f02c564030b00200501c844002c0d20300d07001030542c420b840c0c01108080c8050707240020582c24a03501480ca0480c155960b003019a081e00c01c005e2035042081c6d64003030200500c03007800002d0080d03e99a550b0340b01d03002002014540c4a05080d250160320801c0c107004a62800d202c0d4004524072055031840314540004200e1200300000034113041004a03c05501d032002035002481224014111f60003e018142e682c040000e44900c24404440e041c42440101e504031240b20b034030903142009018003040b2590001ca00780d484228001342d10540000080604850341c2d0a044c096082110070300d011420607103685000f000590140360241c00d0812009000028040c5814028000207 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 551355242 1250 551353992 551354033
    0x30618150b010216031e0201050706151d0403020c061e042919120608032a0f0304030803071725090308030a050604061a1909030f110d 59
    0x410801000039042464004e00200f0042002c14204080348501032009010346000c050301c04055040d20040e1541c0c0100400034003900d15009080b0000c80300e608180c0181c3e041c00c440160f881201f026035100da01c004545c0200140c0088400c112582052809410708420381d10102032680c00d03030328030246250865845410840d60360801d030101c40d00c40c1c030006055421710044c020b00d0034600c49060091644c0d500000380030404210051806000c0d160300110241450001b078075924180550442d480b15a114200084400048882401e1410008162030b102555001450900d40781d9104e0440581000b00488213001d031084103151103c6105885521440858080948520313403101c244054407a114004d8042c40f101d8441480441d0641c0d05503036100810180101e12907840f00c020074040c00240d0300a2040780312500c400c82250b5801000362400d045079a04c0490b0142e0344440483c0c8410f03844c80040c00884094442c08e010600004501080e400060440301e40c544a0380d580e11b11050501e0140e40c0f1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 551356492 1250 551355242 551355251
    0x1c02040b030a1b090e06010b0d060b180405010504020a0f0c02060c0a1203110a080a0c0207092306040204051518060316020607022b032a0809010903080103061815 71
    0xf5140310700700b0001d0103803000c10010000201400c1240e80c0e5103406000340d03448800042100003100645811200103845403c16558440e540d0300209d80046032001c0b480da110314201400403445080134030944098030065564050750481200c400d030384104281d0402e030b0f04188200070150a45208200c00c48526120b400e86100803000010000c00701c03900c056111111010801c03404081c5c51f070158604d81c00c074028072400144a401c03540281e00c0d00e40c950348041c226034109000383c1c0b00038800404503034900d81d075822824001d80d140d40400c000ca1080303028840c0c6c13200324401c200c2c041c000c0350006040e91419001c000100c1621003800510b035a00101d48000d42d100100c28081d802d65810300200341c00101e54002042145620030443c01610307100100781d548003800300c410b6a21300740303c0e4200e039119009032400441d10b188000c6124000584058140021518505c0418014141445141d241ca50199205c480c0e603401d541e40c0c8000703801820751854246100341403100205103661030364021010303050710000703 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 551357742 1250 551356492 551356523
    0x11041a030d080103240e010e030c0c0102010204081005100b1207030e062701150f050f01020a0317060d0218010302120a0302100b03030f04080307031d1c02040b030a 72
    0x518003036103422280200701600004100040d1201c0c5c1128401e01400c549521101403020030900400500c00c240e94290308092405000359000300091980c0c45022040d0341c031138070121005900340c3c8154460105030368007240102c45e00b9107290b4816034110328111180030005503900c100c2c410541080c404482c00b02d20450501c24299010311a83c00104c0004010b0070403454104600c07140c1c0c45003820003096034000d0801d028201c00d429800542c803464480150400c0c0ca03101e283c180b072020218000c2502075140070307020807841e43c00040d2408490b81e1503512501200026920541c02c410f010f000560031819000c100310050755160301d140380240816a00c0380496145004004070520802c2c880740e05074001e180f02c400800d50125a01f000d100001c0700100b083c80d0b085020038954440d00c05501003e841c0450042039085000c0001c00419020b6a2100002c09408008112807180c82540d40e41c0081c0f19013001e043d0704d100c800d22584103030000303000095664a542c0403a0500c0410384007160704500c0c010000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 551358992 1250 551357742 551357749
    0xf030d20090103090302031b1608060c1b03040e0c0702190b1b071508040b1b0a11100e010903020f0d0225030501060f080c040b0a05060711041a 63
    0x349044040c0916000308044222250000d44504014507042584641910741814003c004135000c6c0030b0380030a02d00c001d10b6102030035a10703400708201aa420b143c0261000130340c03c0c80052018014030b00c1000c03143c50300400d0940c11184400250042c00180814080050304240d0000010722401036020300998800e9188100948060356044010b200c14855006204910301082907403035001e100050f0b00308501032014800c0c500912944a48582c40c40c09841440b016440541640554814140c0041d070303840e4490341e0115400400d400c1049407034107010140c2c21078402c842a0120b28810829128091420600e02c0143c0d213900c0304020460391968481010954104050140401c8001c00352000003030b4084029101d070440740f4402e02d02c00c640c58401501801600900c002140d00c00c00170481d2941e00c030410305484005214030003490203648a030500380d041500408110f1007006020084040c01c1c181000f00c00d800c425010740361303000380ba10034158644580c450b08608400c44449030303140d80f00340000c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 551360242 1250 551358992 551359001
    0xa020408010c0f0906030e0703140a03021506060304033006080c040b0622080a03090303110607020a03080a0905070b030604051008030d020d0b130501060224010b0306030f0f030d 78
    0x41d00100061070002201055114013480c0940e8064034020507000c0c00780410510340a11908040d00c5002c003005150a01c050014903034885600c240c0980d40d0340b030301c4842400114803041f2401c80d0408000c00006d40060320031050f41c5401100b001c000d0701042e1041d140381d0b0510400c181c448440356520041401003500c100002c14803418119003d003c1c0030019408542d160045c2240c06403850300001002c010951000d19000240c41c104040b240340c0d5486040c0100f900c030003403000380d0102d03210300021440b00202040403446215182c00030000503403150340441d00070300014813030000743d80c2d2500007000184081c08164000c1007079058890301d9040500410080b1440074046007030400c000c40040141007400700a8880c010162030005172a1080c014808000d4240300030301c2c41d030150340b01a007132900105940c07110381a20300d15402c59401d210100064184d10540500f54240310300c2c684010420981084015039020780043c0607035194143e0f411003541b0b451070098000d0b0258002161000075140395108 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 551361492 1250 551360242 551360261
    0xc080402040617070510020102040503030a0305010e1012030f02010b1c05060f1e040804090e061806060307091509021b0d1b0209070903050609010609050c0a0207120303140a02040801 80
    0x103125140300340c0282041d513a01c00500c6118095580200303128800382c002e41c1520f00400e005010380c0d80d682035900c0d0007001002e09009841e01c6c1100b0781d01154003403401404074010740d011400c005a06800544050380d05140c4a6405001c564940d045041c0c1343e20749040c2c510001c404450007842d8090645042410540c0050503126004105020401404981c065040b1440701044e181c10b13060311542407422041c45150050518281400c05070070305544000b407864400c3c0440d0410a2b205038140740080e443c0c0030f00380c5035980d05a1081100b0302480c084c940c00940d1040c0d0b035400c5811043d9803403a00000342c2c0c0000b81e890b04c100815445000e030f000b20600c144a401d01480c5000202c603400e1301080d1102c000340c41b2001c1e00501c4000005103441d4042d0203600050350b00a822151140340050703c0c103010389a02c2c09840b840608103400f0801e031241400c29210b00010a4000c2c00101d428800085081c0c1e015410940405031180e00040004101100c902d015007004940565180d00b0100c420b070135a40c8852 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 551362742 1250 551361492 551361509
    0x5060415081f050108090f030406170a050403050d0209060721081003050601030803070c05070f060320090402070f080706200a02100209030a05010e0304050a120b0a05070903060c0804020406 83
    0x3410410310081c0e4242c898296202400c2c811070544074070054030315240080451707550900c0700080100d402c1c0d4110300031400c4081c85951b400c0459844805140c103403003098400038082080ae002c801c45903030403070300a000c1241000c3c00a5040015036260b0006c54120b001144c1220440721440109466114120035131010740ba0b5200030720305123151b48555603200140b1000c0c1c50000c01001095030300e07200310042c0480d0358125007180d900d19294080303072412421601c15180032a02c3c0000310811000a160741d030400c5403000207c01d0400c0654030500c0040c0d84881400c41d102742d110003030107001444400c054103403a800b0311000244c45c81344236600e0750703010b88101140500034800d021603280164001180c0788000b04441025885809070004a45000e040300d100034500e50070140c8c601280e050020190048940c01c81c2c1003180c0e00d030390354440c00c0c0c19209203030041e0840407030f00300040700791005400160b080320b07451070101100b980e607032035503011074420340c1e5104001a030f400c1c18001541b4050146401910345e04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 551363992 1250 551362742 551362771
    0x40b0603041101051605160806010f0305030d050405030412050304090b0114090f0f040f1407090b041509050604090c080f100e0c04270e011109010302090a0506041508 73
    0x161100400b051510500604001000860010700c1d441e0f0440402e600d0b61280848480c41c0104100140d02481c502031005130344210f9000082000040100c1d40c101c030f801401031031804081ea0031074070103410002d100b40c400384000c01002992818070618010164020b01c00740d600c40c0d0070920000c00b922401010141002030318058000d1600304101180c0e840c4e4000c1f150300c82201c0018002c1003020306102525079002d8540000079900560035089041070644c4801082c0580e40c801000fa202e110280c028802203000510091007144002c1385495001d2041c0d00340940002c8da036030001442540300e904801a1540c81d0b0782030159680d046010650890348840310450b041c81d044102486545940c030074200464800c4000ca082644001c04480203010b02800e0031040c640c02d415988a28400e881c82149641d1619001c2001c4500c10b104410780683c070540c0180c030b844420001103000e90401003003d6030140440f880000e50342d403044c0013803000745141c2d01c60b00300c403001440b005050840700078400944910f00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 551365242 1250 551363992 551364001
    0xf0a02150f010f050d03020c04020a0914330702130f0f090203030313021906080403110a080405040f0f05090c04060b09060a14040e040b0a050a0218040e030d050a0209040b0603 77
    0x1400e0444142c4000355045c109181850a00300e1810520390b10960f000b6100081c1e11000381c1d84000140265100820701601c504004070501075111003040301440841058030b8001110509203540c15480c42c19221820704012031a00060400094405955041a5180c00c61948001075010345220024a2170301002490031640209450344401440c041000400c0441d81c021955141199a200840c409104a03002e0311648041c203013504c207860590200c1c00000b08a400360100041c40407040ea4855403103401c061401d424080a0b1401107c0300400c0b64450303c009409460601c501c1d03106000c0740004001c24042441800308035000ca802c40300c180c0d02c003009010354031b46500080b00c01d801c516291610001a03080001090740c02203421060450801d5401d010030b02041f200f206d40542125401044640c0340c1e0200308040344a02c81c001d0750421501441000713240342c01d50180c0300094224059074030b855460b00280c4100d8a04440081c9030f00c3c0e01081051007410035206020902400f40d51003465030a0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 551366492 1250 551365242 551365259
    0xa0201020d030b040f140a0e0325170c070920090609040e070303020304091d0a0210020709150311040b01050f090a09110703021b0105040306110f0a02150f01 69
    0x5074240c410051680b07620320264a62500d5001040465082c80c041042e8004030800c801e600c072065542d00041030411406c404000c10201c00c0f1103610310300802c0c001c500901c80c0707018100040e9104082ea540e96601c00e1200801c11950010722006800c24040d040d640c0c104091402210316203c0740d84201600c12140ca81d1054200c81103c9020104a074042d445405401c0003401400390192800f03124020000c0001c10140c0000241c03081d6485607006004449114600304140742c2c0202c44040c059000c010b8000c0903003046803018040c80c403148150b0395480e494186500954001e0100d004d0140c47c0104208103021302040450841042218140108800200002d103640100f9101c42d0210781c0c0010381101d80e5881034400c3e00200003905040c4100c94036a1621030054200e0ba40035405402000000c0140c02c13404888001c510005860759070030142107440344c50042000078600d170310900b0100410008840c08c00b001c0d141c041c00d03075402066800107941102c0d0504a0250540b240b2150f010300604c500315 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 551367742 1250 551366492 551366503
    0x5030309070f052404050a1d0708040b0105120a0618030905030601061e020f1207060e06040503040b070515100f0807080616020316030e040c0c0812070207030b010b1206030a020102 79
    0x14030104d4000111000080e40b03c41500c01c907440716038001c4550500180b1403050096a041000708180c0546250780d40c4001031358048402c0b9002070000001c3d40044c04103140c8074005916000810701103c200c0c40c03403951800121611402c00d0510310940ca40c00b00205540701d105080509000e4000e411654902007000e803030380d0310f001110300090034801e00001c2d9030742c0308004500050004c10100e602c1102d40e049a040540c6c8581d900380c4103076040c0100d40d45040000111140901d5200000f986064a010380880780ba4200c244100c0b5203016480044000501c2d02000500940145030b07a214880e14055220108040d550300a500a4107c96800c000c00d58020810640c0010121002e00d01d0300080340c412030440c440c2c141c06082080f04035464605040d800641400d515a040d141001205000b190a480000075140c0090801c0804c00030700c2660380c08a081c098000203a40102c80300c85459603100c90b9641e009800c82c000b0f201c40425201c0d00030401000d5550440002d901800c02c51545400007503d42 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 551368992 1250 551367742 551367769
    0x10b09010608092a0a091a21011a0315040b15150309071a040f180603020312090102010b100e0d1e03030e010c0e1810090905030309070f05 61
    0x106440058410b10007030140410b4404a01c1c82ca1340c140000300d05031080382d411655081e01480d0b200b078011502d0000f42c481d6500304c803441d036045151451301404006c44207a01400e00c2040720212070404010100c03d0084501c100b0440034042c224255010503d8640596480c21101403004c02d014000410b804500c1184c002015000240c0d99105101c041021100000c0d00350328030201c0081000b44401011541b0016528802181100707503818800007001c1e402140240c43c1e125a005504200101441d0080440070709100d801081e645d54076000039046c1220703030a04074608800003071600419a420304c10411201c4046603030404d01501c0c0e5100404204014020030302031024455154140518404c008801c0b1240b401c0700411a402854010058540c4100c0b0340d82c55800c200c1070910240c0074801d0032060030005045101040a83c1c11003404a031405000400c7e0380d04882c1010540c00d005005800020b4001e0004596a00308481c083e89061455408502158607040c0e050041daa1420240d4924 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 551370242 1250 551368992 551368997
    0xb060607120c02060f0318060903040803040608040512070c0306060506212e0905150f0607080c01110909060301050103050c040902010e0a0602060106080a05060d0201141c06090e010b090106 83
    0x200c040c82c4041101c2d0f01c07417031019016246011080150203101544c901c0c4001040c802983d101e0f071100c220300c82d40c03070040c1e015041681e00280002d10040348901507040d80240148102c41402c00c82c00b441d0056a0300c401815910034007840801e10070701c61980554030003058261030451414003101140009400030001d40481010b200307010642400e990710040171102c40004071110f550f14914003085041c0702d1441015242c0d424540022800390031646500700c08040500b900b11b02844803020040d11781d1015204482d54401400400460b103402d100781c95010001c0342400b99903110708410400c081c40001c2100c0d00c01d03030401005100003840410200c41c1200c086d070700070408001c20b02c016a80e20340d090720450f41040d0707180c1c0c0020300c1d140e0014285040300c07402c0e190020a034843c000c10b00143c440488600d13420006203441a801548290003d442022004809078146041005031051076684890b030580300e0f5480754000c1c00b8004d103601c5069a2003039680300803c0039001760300104250700390500c00c0f41c06 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 551371492 1250 551370242 551370257
    0xf21031306020c0607051801030209100f02030f0310030201110a051f090b1608090a03081b0415020a0201020105010506040e041736010e06070611090a030308040b06060712 75
    0x708150354065803107802c68281030b03a90034908000020b00f40d030080d148400c0d1086c90340440c280b4550107482114140c0d031000c0c203900c400684441c0187e550480304803200045110401150086070080f50203940607a40420380018201e00d94000101038005075607594203280c10034540c040006c2c4000950445041d0f41e01c1c100e628240c54030384264000c0010300710103000351240008000394104182010702000c41161101c0d010cd8a6041140e41d4403a0102c10040c0410010b0000c200c1c076000a10804e0782c4c40a80042d0385103845d4030b544540c5168201c6140500140e801402107904568080c0074081c00750000f035698070b0809251400782004c003a0058005031141d0000c0c060400c0043d000c3d01101d0900811b007111800400042208410046000751000d0402101c0c1203072000645c400d055480b0740b43d44c01450141007410702d80b103040c020a441c0b1030000d00c00404101d00710b019140d050b480c9000350301a4030350300300c145000d041c9000280002040e41d840744a04204000001c0e4400108001190355880c2004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 551372742 1250 551371492 551371531
    0x13060c03141c1a0d03051b0c0112110403061d101b1101020d1112060103060b030f06010309050708100f0603020a0b070501091703180109050318060d020a020f2103 71
    0x40034900c00c1035103d07802040c0e011104042c036400500900e003c1038900742513407101c90316040c426260402412000d0000740e200008004000346c03500002c2c1c0306a441c0c03c071a41341c10303035a96980c4200c07848946c104500790700b01140d00c0d40d1444103210030b11545103c0305042c400c2840080b001d19aa004080000d8240f00e09034400c8400c00c4025030648565102d4007008105078081701c04e0303480c0c080e003000c6400290719014900141c0c0c42e522a000e80c40c112500300030302c04d055031035880c001517002500900d00b60405a49000310b50205000b000f1010040c0300103c09018942104400c600c2070b502c40c000015440c9003003120400c01a00c0d1b03600c0d80411165043c000c680c03202402d25101340503005030754002c0c150201050000119000e0b0340b00460007101d407072188030340d80020fa20845080c0d6401e800f014140f0307003051140d007603240500c40e04c07400c003100000c10103407800c0030000c8200203c0c0c004000080059025079040e40c44907030100185079000070416041010070700c218101c0c108503c07000b811107402d4000a04140d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 551373992 1250 551372742 551372771
    0x512010303032a0816020304031208040213180807050114070e01090603112b050709051e01090b0a020f01090510061d04060b060904020d0f05060406031e050313060c03141c 75
    0x560281d0f40c082b110010300055618024040401603409a12603034100c2d0442c98100e4840c1700c2c00440310281c54408030030074a152070300c0d580d0750017103001650503548030301491000d4850001c00503c43c0c541038407603ca03507900080c0018078450a03500f040e41414503100304900c03c4c010540607110003849a0b4014140e580d0444000040c0c0001e2808603a243c42c00d040c10721000c0364120030f100702559401d94030802d42520248176498a904484003203408114030742810b00041c1001001086030480a00459450000328022142100d034062020f0b104c1e500b0020441e032403801b4034090300c00180010004c1455011141945a140c1d00c009400240a1a595822080143c86801c00c1d201d000c0001003003151251506001e0b4030150801c12800e500403840c000001e2454a001d100701c8007500e4005020710030542e1081c0c00058007036070200050712030784014011500300c0440c0380100000b4210b6a90b400704005000d15024003402040000c2030710040003400b00390045031000c41c0e07598808058030004036101e210f2489a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 551375242 1250 551373992 551373997
    0x1d030c030a120e031b180c0d15080d080610020601050312090d0b09100e03190e030106050603010b19020307030e0103051003080a17060402160b04030512010303032a08160203 76
    0x103d9030940582c0d03076041c8a8442e00c80740565440b50668100c4004600c0e6016952503038012102015400e401740308481102a52354040f816a10700042c078001902d441e1041c4901e400310116031a000281000c081211500b031080c6554034428180c002030655504140c0043c1d107840011909400e10000031900780401d5817041902c04100b44c1003c41500e040c1002032803140c440c1080d0260f21896418800041c454010010480c1c070300001c05056500030103207940e4102c40281c80720a00c03540c55900d403240400c860740e8080086000b04040c0c510705070703a11308110500004020302c20321030702550028801c03180884d8010f0184400901d0034680001d041d516448210008020f542016011000100d2940c16050b00011f007503c110b02d54000d0304244c2da542e0410230007644603003200e0004450b541c1c440e000c00610b002c800203801920a09119081642030110300d041d80000341e00c02d400003900c4040000054018200038000c4150000410003046050704000d805001c3c003800040d42135000c80e00051955100344107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 551376492 1250 551375242 551375267
    0x5040302031e2712070308032406040902042d0e1306051501090f180209030709020703170a050907050f030a050109052506023304031d030c030a12 64
    0x601e140c1080b0604001410306042070f8200f4020459021810700c481c500282c0d920450f50704c00042032965851048401e04c03621298100c544407114102c0c1c002031a580c00c1c1c058000380c15213910040c1ca99240c40490121403000b00881159a80e0700b00c003000c401040d51620105945002c2c1503c001c580b50178840e40f984062042010748a14544400d03c0200380318043c19103006c00c0c09036511848292190480e2a0b201d84130710500d500103103600c2200c1061220380e0040c2c000c805d4001e0075985002d41d9242c04100f42d0344050703000c900190340401000440c0124603030307581d040b402e51001008070b03140a0020710f0741c8040f03e0090038071480c07000001981c2640c1c00c02100950302d501ca00240651540ad141c49d0382e4820f04240c0010050f142e558007480c40040c03c46003041143c0e030070b0b0300801d200c914010303841d12110845110040761851510b00e034903081ca1002d110f83d0244d4420b550b500d10510f0f11074503800c0c046a4100546110380c001c064a19590f079400541c2c101003030b0300f00032610005250510152030349001101c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 551377742 1250 551376492 551376517
    0x2042405100c050109260a0503130611030103050d1d010203070b09120d06050406090e070e070203040b032a0924090901030302070305010b0303120129270405040302031e 74
    0x9251000c0003900c5c506070b106c07000007211003414922480c0b101b1071035028081e511800a4030900014840c82c0480111007a903030701410001501c94500c0501a03050b0b8400d81069510f9030101070201c21250380071108001c80e502c001c40c3c4107691400b07000000c3d01ea12482c1400744c5124904030210716450b9090100001025594070a503982c2d810070074814020b0000ba1007450300c200e140020000f039006103070140325401c032601809420003e0520b100e40030800001f070950801c42c40240008580204c1e00c038029801110003100510b00d014070340311100d50400c7c4021040401c8002440450480c0d124240341e40c0b650503030309032058204010041003c40500400c0d0701d6942c42400c0740c000000345900400c0c9001524052002031200e410741005242d135a20445401e4100300c139518004014850800305299107440480c446c2514001c031001440140e0b070865400c000002902a04c0410b02441000ca0300c00c9810f4255414080e510385600c2c06900d03401280c416462811001a48420301c010500071580c9191003c1d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 551378992 1250 551377742 551377751
    0x50d2703260f01180b040c020d0e03070e0c1606050c04031101020a170a0c020307060e09010e090a02060c01090b0a0c0e01090803041710060603020a080112050c041a0d0f02042405100c0501 82
    0x1f840300075a1246a4400207011a0003809503060a040c0442d03060140d80d017481d01500c16031030f1405500f10f160700c01c002c00103400c401c841005000403040d00401380a145542c00c543d40743e50640c18240900e480f90442c40e4155484560680300244501004040c0e40403003500080c1c641103040340941d2a12200480254140224034001c940c058002d4603540032910280ca02c030b040f03681c8580840304824415984e0760440d521807c594801440c1140080c6510201d81001194010269550700d04106054070312204450300c0300b2040003010b0f40082c00c13104103a400d01e44114014a0460156100c0c4954002c0d006000d0240360195851035082000c40441c059040d0308104490395928010008e40200710040d000400490000401403401c0c242e41940540040190941e03000080401006080240c0c0c0340c41d03225210b801c51071003580e880e440c100313070303140101c1400710113441520401040b11041740c96007690b00001203402d1191900b109008040d00c02c1556200c890040320b04050318141da42c89070003402d541c02c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 551380242 1250 551378992 551379011
    0x1d070806040c11100c0e030d020705041104090e06090d0302072d120503150a2d080106030c0e0901090309270513150606050d2703260f01180b04 63
    0x350b014180c06003840e5503046e00f0820180c10151a50406004440164420707001800bc0d46020f500030445610403036141407401d0394495195040d0b8041c2540c010b03a5820171003c1100500c01480880010011840c04501c2c3c0030040e95062440c240c80319280030b141003841c1002004078070b994000703101642c21100703076001030495200040030b03503204031030388142181940383e000c0303507130800a40d00303000d03220040d400015003801d047d6810b000340c5c1c080c002080e0b00005560000b44044082c07246a01850207000301040140c00e10300303007030800c580140c0f00d00034aa24080400c40425030000b0107900741c40024010724101e003064207462044610500803000c08524010a1082c1554544125200c0c28400c94039203e4100300c1c0b4480b0003c8075814850340010582c100b0860380b00c50040c0c0e00603a5413554211039964401401d4907100c00c1d5065035041103021038141490220080054102c0700c0b60400c0e440c04405682c40d01c4413000310071802c18400d1441940000c4050f940c00031458001c444100070181080155044 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 551381492 1250 551380242 551380273
    0x60e191202010e0a0c090510050a08030a08150a03030c051204090504030f0c0b0112210305040b0f0c0702120309030d080105040e0303100317070506010f1d070806040c11 74
    0x100d1200000240d0300e41030740725240b800c010070740c0c40030b60303400c951002c120500c2d0218000150030020424042c1041e82c940201d0140d6071480004050801c0500441d00ca0300c580801820158000d014990340860651110100382da4102c00718003501c0c1c0c1440c00ea04203414500c1c041e49031456408c3c103c0074500001c1408516500c03240e204500c11402030307980507440307048106e0940d01030620b004098078428610006129841244044459540c17040c040020f442c10040e403001c80018400050000207500c036801d0000f0302802e00c9820b904085c1070810801c05040100700140580716602c00203014001040e02d140c200c0200740241ca204804c06004d03110001a0260000c2c0020424080c19104030f10705040111a5030002040d24456420401c1c1c000c421401c6860f0070303800700c0c45900e2802010340c04000e4200000d2040c0709060081041c41d1081303000710f0910120304408001050400c402d001001e0030000140d0b441411a5041f20045d100050740103000b0341300b21792500041d6101d80b010b10079400a20345006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 551382742 1250 551381492 551381513
    0x30901050601120e0c120c06030406051b0a0e1c06020304031e020703020f063007030b12030702041e0e03030a060e09030304080d0f0e0109120318060e19 67
    0x210709980380c1a916626901502c1140c499000805440d41321001d2803100e418004444082c0c800c0580440e00d03d140150b001802692040764200c40c40ba449030300b0311a4000d00c60403051980004e0b03652880c1441031b40400284207588004510784a050300a00100c5251991000300341000e030070080541d074a14282c2005001403036014441c0c8441d1014014030b0701d030b143c401310f180b50640340c0c018000c0daa511000400c0040c41e81000f902603200aa581480c601d402800280383c0c10001541d4100085600e42144003a00321600490b0260084500d000c039280502c201008481c0841d5041303d0008030b0398116040c0344100001c951100b07440d80d00d442c0104003031010010180d44108100c0030284400e94840c800b0401d5030f2019905c00085038070501c0424002020f44002c0c0c40b65115149000a40c505070450f008141d035000440d480c610f9540b42600c00500820814003503800c09141814480b000b58224254200304100101400c81e650f5034110700c1d085e0302e06001079102ca518480401c0c102c00c0c1c0c02c0c103200740405d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 551383992 1250 551382742 551382751
    0x30f030207090b06040528080d0e090705040b160c0602101b020303040b040816031e0e010207090c03020f120603060a29010c0c0b1c1a190b03090105 65
    0x107104044000400d000d59010780031540502525050a02d1318200910007000b01001c14000400c088918080c1f16819143c20a8000c26a4000a00301ca4150510283c20f00600394000c03070080c141d007001c00030b8158001c4101c608442e6520002c40d43e51038554800241a0003948000340380400d00000061f52030740c00140c800104202e400104038441c010345aa0f40240542000340c00940c00c2440000c0214041c01c2d162a40b041c060503007249009404840c0c00140b42d1103400440102d001c02c03650008100c1306e01c0040c54220418180804848240c0c40040c1d51001c581c403c0000e007a480d5601142070320300c6030301901c000d4a01215241e0300c4a240c0407944d500b1210032902c99002c1e10440001074880d010034010410700114000400c000703290002c2e91042101513460750b4a0501103801054000079a070380e000c040044c8103820501ba160100340076041d000e82d000104030a5080d09100815010819a1800c0c4404810444030b1031b4500140300c92006041d00c0c294800c11000b0004010410111019000684179 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 551385242 1250 551383992 551383997
    0x81c0501170c0906011809090602070303110c06150d0803090102041a03100308070804051e0405010812090613050918190f0f0311100615020304060807050f0d06030f03 73
    0x1541042507070603621206008100d5204003c00c0214415501422080800c2d0344c0060150002d5601c0d0365410301600e141d07920859000e40e00190701c005041e17241c81200c0e02000408002454980615205a60f90b0f20181c14282c41030307150081113081c2e641e480034002c01140d000302c05580340d18190039594001e40291086c540318030302d2484004803003480700b0122407181045207840c003009400c54039034042c1030b00221403c0b13981c00d038104800b142507598030b5000d2000400d0040301030510b10741d600500060360410b034001038055000e0300c5a1140007144005564072178400b03941d1652246003080540782901c5da940d000d250400584414410704047c1b400c100905075440400325600c1c130305e50800100100404401c09045c49010070081c03000103803502c503000c40417802803408229182c030005100341022010b0704007a00031035503044200104050b01602d204c900040e03001541c24185041005003030407000600030f40c200800098803481004405c415580b500111a6007044242e40328034040b00c60741c0b24404240c01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 551386492 1250 551385242 551385269
    0x80103020a1e0e06060403060203042915011d10080a06060905011d0d06020f040f0902030105030d0809070e0705031e0105310e062d040f081c0501 64
    0x4400008400c03001c102e181c1440540405450b0241c0e06180e641c010749101d0748010100400008140d00e4006580105d0051000144d010444001500280c00502c40002c0240c0e2807010448241c1001c00c0c030301c07103261080c20402500c02e0150004180e51801106559200313102030002c0100b15403052540348540128102000901d0b01ca501c1a15400903038864140003c01c103400c09000054010552080c1d00b001030005c0da0a18000e0741d407501070360807190805440b01008a81000b104091102c24002414401ca0461555040c4004a900c4d4425500b0710800e00950b0008a0468403007040304900804404401c01d1450411a000030242e500580e11800040c0380740f00059803481c45128a54101c0300c0080c07034000071f002e09610080002800410f40c1c284c0380d042c014400007550884c02200560080c08021300384918120395200221804660507414100800c41807000440d40c06010582007038009029066280c200e2911034040c2c450070900400803007a82d407000c208003080b03402460580b1840c1c1c1e601032 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 551387742 1250 551386492 551386499
    0x912030301030c150e0a0b0f1b01020904060f0b0a0e0d1217010501030e07090e0304080a060204150c08030f0606041e0602060601020c091807030f1407120b040b0c09040c080103020a 79
    0x1714940c204d0010142d0108645100700280c01d83c00f002810003000b051095410b0910b4122004510420b1540d0b4166507500041c1403049480c1c40d00c681405026030042c030488880c00c00410107650f00800360b551080c80903003c803081031580d03203101c0ca62401d940a10b984041c021140780003040140200c04200c4c1c62020180045203540c0240202002c007580940200380c014613040f000000350029144085160204104c081030509050042c440d41720b0080e900569501d1500043c0254000866111410050296007010000b04141c0407030b500040308464802e182e482d01000a00303c2d101c0d40d8481122040305016204130703d10415a81c03000c0300c1c269001e941c41903407840e00680c0c9500c00c017039241c1e62107400440000c100d0081064080c1d0b4181c028030484440f0760300e0360703680c6008160004e410348441c07280710202117180380c041004401500851140c8403600d1a00d50300c0d1722000b240a0030042c0035420010001d02c100702d0070301c07e440041c60002c00034440d4815032071026200b0042800140e00611901ca00030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 551388992 1250 551387742 551387747
    0xa0614090402060d0c0e030d2001060f1703161a071412041103030307020f07090c050d1802061b12072118060806090907050112020912030301030c15 65
    0x1500c582c0d0007615051a014118401e0002810355442070014051742c03941c00344642d00d04101c1441c00e02c406450718551100644a000c0504402e80c070b00c21032682c1040c00510100c8008807055084484405413400c0d0982c290340f840e0700314041d100d070301030380002101010001d00c8001c1d00c0c08a000e4034140001780d07140c0c40d010411202407060a0250808042c100302036544903201e140400d070321a0050729488840342400300080e056030b100381c032001c005078402040c1c0d43e9819814072959004100c1e003201045000c2c0c540801a05030b0140d0403c2421090340d038071111004017071300051844041d80c001d04299440a0f126480020607801e8400c1407960301c11000d0000920055404a444254000d00041168800440e030004180301b94180c0f4410480038020220440114000382c101508040c3c48400b801d00e40f9a00b800541e0314002d02e15041303940804810000359070808000084803068240c05607503801464041100700c1c04150341d03070311988400000003003030002c1c4003d0b034010b42d110459410303960180403504 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 551390242 1250 551388992 551389009
    0x70c05010c1e0806010504060509041517191a0c0c120d06082d0703050a030201050a1a150a1b110a0b0c06010b1b0d080709080109051e01020405090a0614 67
    0x10f0303e012440410043c03102e907000b000075080d62b01d00104085805a805851081554030075030247c01c00d008145002004104180003e62650140344400350b0340c18140e440702c1c48a00700e40c13035280062034002800b095414844108071600c40d40d854003183d00080ba50186428581e22000030f1000d214a454404245098041850801c0d03500141c1800755440a5444c1c0c4006a07003a060101c0303403071190820010004a042c014040070f280640c00002d540e00e005460b0a040c0d985042c40c000e4800c214842e801081e030313070340340c504401d89182042c200c0d1160022402070300d0a10380d250400c0d040d0342c055501c00041104900d0f0700f11409200340d840480a0340d89a850341d03024000c020140c607151f04000f0040c032590307108901801c0c03003150603045205054444210103081850388507400c00024042c000300300303c03203030803000304801040d00d60000c00120311a030300da050b22400c031039410005042c80102490300d0700e03400b501910042d0038010680e4826007007118062004001c184183c410529802c04690968508002c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 551391492 1250 551390242 551390251
    0xa0f020a0b13050423151908100903030b0a0807031104051308030402210105092802090c070c08030301080105160c020108040f080a0504090b0423070c05010c1e08 71
    0x220765141810703d400c11016109003174503019011302610310220b1501d1800c0306139010b010044e214912280b103c50501c100e071841c07080003000b459051801080b500100244145e5140f40014000881a1551604401600c400000b840d4407014034a40404e2080010441404492050100828640001d0305100c20344074101da1900049003885011000725501c03a008643c800e10082c000031341d142e07040c82c0c2954407814004119003903a66500070007051600c200101c0e200078102034602c0d5401c0c6a24042d4643c024008c58009000d10422070214442ca01c10b0410349140c55071206021503007507111141e0a559030003d1094860315800d20010900800f0003881500b000d1146541e01e402c900400e80055031120009002140c8240d680c0300b200b40841c8801c009096680000ea031240d540740d1500f8204401c4d40c800005c4141318034900517114158625a0102c92200152580c11240030750b1100b81c10350b04950403a0700a8803550030880b000038056440300403c0030046c0010042c010b0b815065108842845045a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 551392742 1250 551391492 551391517
    0x105010f060c030f0e0301061212030515100e06030f090d0c080d0b03030912010204060201110910080408070b041a090d09140409020604030b04031b0b010302010c0c080a0f020a0b 78
    0x12100400d00c00d1480071302c0180c85041031500e0903c00c0000c02d08684040c0c2c4046200c5070b01342107400c00c10015424010a4503068502440036040440e401000e40303c01000440c45410006620620140a0130b01c038401604000d01d029128a000c205a00e00c0c0901180c616a190081d08207403005c0f18002c0e0090040300340c12184c01401c224052039071500601e010711610b035042c0300a115220080da50f190469640c190728200260302e41d07207070400182c00d40c0c1e070810860240b1441070043d49155110180000c0340c0d81202c3c81c2c03510658032035040802c00ea224521001d801015034104001c01d000305000c03000045851590140784541e40c0300003d0392180c00d04c8010b003002500d640020400307a00018144c0403c40801403000072915040c0d8001207240d030040d40300320f4902d4002001c2105054101d16003800700348d1410001609100c050b0340d20b2188000c140002410300520408807824821081514405000200215004c0700040d09103c6800c2540c0d8000300e10541c901c0e40d0126074030b400b0009640010500c0e5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 551393992 1250 551392742 551392757
    0x21b07080708030f090406030f0f1101260622091e05030d0e16030c1e050109120618150506061314040f05010b070302010e010c1413260105010f06 64
    0x303c50740d0036645e02c0584400d50041d1a0103010012440c901040c42080744180010b400001080c03503d42d4544109802c000e050092101000c0b100b070302d140911300031554048810301c0c4169102c60000e00c0345a940d129080010803e54101d00e10140e256100c080c0181c04303054010160b481544003400403c080c01002030042e0401d011103041198550400461201014155502c2c0d0080410100aa040540c03042d144d01d401840c0030452405182020300107003500c2c007101e5419a040030b00190050b1114414542004040c0c581802403201a91003141080980016444103600500b4001070542021010036981c0d8030301030210b00fa0385821400c03262110802e05807684103034a8440e4170031040700c16a801541103030710703160708581407150b9110b80c6000e01018201c50f41c4072945410020f00b191109101c080d0107030315244941c070030103402102d4200c40903c1060050f03559070700a002e4103036803c580c1d402000c0c150305418841c1c100c03480500021718411041c2d0000c00407a0b9039009450390100d41d1344112008911300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 551395242 1250 551393992 551394007
    0x80a02010c0f031e0e0405060916050309070b041d060906030c01050c100f150b0f1b0c13020301052b060507020304120b0115030b090a0209040906021b0708070803 71
    0x14000b64500070b00030304100d40c0e4218030341010078401d10003024800010350b1095803552107290902c180c0750052010340d48400700f442d0500c440c0e10720070301945100c02444000f0002070b182186c200320060107882a00d42c3c4503255079a442c02409498050135907034082121120000303006050060040c2c2c82a840180106070036004803006440a501c1440407070602d01842c61006180206802a0001600070220000c0c081741d490741d001078140040d0f007140c4180c270804c022980d0b040110000361117030156424980d02c10302041213071241c80c1c90f0b44505a103800c40300621517060400e240c0d41c09035048500550b101d039100d1082003d000b0803005003003040c4490252031170000f0040754040e0321241c1d02820342e0040368a49038075440c0060700c814200200b00d45c255207440060046e10480015546071841600307061181040c62030000b0b0b6110b50080c01501c54076804540c0701c019076a142c0001c40b04c260044c9046582d03860760b00903000301d41e8801410940d58400c05600041c1c030a80001e13018200c50f4154007441c00c0500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 551396492 1250 551395242 551395253
    0x108100905130b01151b0809011b050f07060905030705010212090409140102280804030806031c020309030f0a02060f0c070306020c0c04060e1303121103090a0c080a02010c 75
    0x180ca0b4500034030a9202c5000040c4544441d18041e100c802080c05410b400c0300302c014503602c540124528003580c841c05400010705d8110680b000c000007401d041000411550340750500c1158120090594803c1c20640780620b00c0205003181641c065a030351103841b07610b917824165260b0113803241d6801603105400b01064040001c0c090007002c8070052000c40c03020304a4894162004110b2908100342c0d43c0000c00c900400c010f007417241c9007451510014982201070780310140541c04020009418000348400050103030398103001c0407821a20587c0000015450f1000c02513aa17080041803034000d04c00e050b6414800880003510381c06069000300f071546404280b03c807083da10b802103402c4030082e1164507130100c00640280050100c0003c00c000800b44903000204002c01d84030030742d03c848021000e54040c0805100b1881a159101d40c040c184a0183c80310703950f0f82c00c02000c04524010003040302105014101d140840c1d4514040d00030282c4200480c0c42e414071944403080c100c130013404180b00e17040000008170b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 551397742 1250 551396492 551396501
    0x3020c040f0531240e1f061202060c010f1503051908160302030d06030305031e07021e07030203060103080c1c020604030f12050106050318030304050a0204090c08030c07031101081009 80
    0x15140070303210040005a2120f130295480c000d22181c0d2500801c42c501041d9a003c0780c08090007000c40c4007486610f00d0b041c00e00003401c9843d1000383c010b001c0040d080010003030035081940b004408bd68104030b05040c0380b221850b4820580000c80312070240303844d000c00403400450720442c0190040001d40c607103c0e4040c0f03125422950150101c0550100340f0100c43d540d4864803e030b4000f140240c59980c2d40c1c0ca4142e248400011481c0030100c1c54207900014000c60716030018441d52685810f00a80402480d540600d03440c1c40ca15600095041c03241000100401c2446806404441070341c400300c0f5002405251032180301c21005600400603800040042c0c0400e1080f058110b0007000c2d0f0400540d26541d000c8200150f42c0c00340c101c4804a28000188009e500c2c4c081d00c40d000d00100307800030303509508003070352a00c0c0c0754119440040d00c1540c40d483c2d40001e1150503203800e0002c014100840741d40e000c00c00c103590f444020510080e116000c8d515041c0e0707210750281c44e1442c0b040c0c9030050f0b403081c0c182c20221280d0092 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 551398992 1250 551397742 551397773
    0x509090d18030c0f140d0b040803060a0e0103260313030c0201120e1e0712020f03150106030507121406041d01060303091406040b0301030f03020c040f0531 68
    0x1a01c044000020504102a440c00341c000d00510311210342c02d1601c0c05026010041200c0c0c040d03210a076142000c603005401180d0880d034000c030195075a440e40c4002559141c51500000e01003000c0301c00000400c5040303401c04910724a41ca0480a00300105041070301d0b0740c00111450424810b00d0205180000d00c01c4514a08852050509024010244c0100070480e80f4030013012803258001407044009a84d202c1d25240d00302c80480003400c505040c02c44000310070240c1240240107440c0d0101800c01c0da9424010440401d048102811041d81d69034401070140406079a0340000c590071105c00095110301d4010b00d00c6000c0500401e40c0c10f501d41006010040c00240b0a10400414200802e40f02210a000f200001c0d8026a10340d50220b09081c10702c00d102c9008141e4500c03810041008019200e04001903a04603600078802a01c090000d04003a41040c1165a0302a031051800e0b003d502c108a240e0f00450050450b1465a101ca4041c2102a80e401550034102465410000082000a2003100c0d656415 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 551400242 1250 551398992 551399027
    0x8060a0312050d020d0911031b0105030a0b0d080706050a0204030305070201080405070302120a0b0108070503060106051305220e0a03052d0c010501060809070518090a0b04080c070509090d 82
    0x24521408020000c98000280848015072190603207005d110304111f100341610720842c0503151b04510414240240c400c1803d490341801030100c0000d0706841698488844907401a110324600c0c01c092409a103607a00105080b12030034500f2002c42e80c0450944241c4d0b0a49501d0340381c5901d804090307001518850750080003164903105d4804007200503240c40382c05816030303070003980104005401031404000303900058011107107a500c540ca00700499980050510b04649250600f01e54500800300311041d140026086150030066006541e4050355090a01952000020030200281054040d480b130305c1d10410103001e8000b85003030009019628561914051122400c2c8650440846102c107059054000c01c040d030146940da0300c010400190030982036030344550180e0103000c4090801e00082d80207210820700e100c2d40c1c0c180c4400110744040410440385903a41051100009103050724014070700354400c540140b0913014030300000601c0c5c10654405401041404003516001480e201d08687c0c0c24803603940d2849 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 551401492 1250 551400242 551400247
    0x506060c16090c02150c0708040306110a030c02010b03060f090109050a060b09072a11061b070f0303080a1109090702010507080c030702030a180b0a030e070608060a031205 75
    0xa2200700418403281c40310304030500a06107021036030390450300c40003040429900003130b1161821356204180785511000c034a6075185c0398455400c0c0180c2501503a00b0080c03603103180c44410b00e5060340200103000c0c9481d503079030140800e40c9482d00482c203a500512080f41c044e489900812415003a0070802588201140f0001403040019242d15180a0880c081558040d6072a40342e0206400c080340001e9001d1128106150500a418802c02c00b42c68a030440c0c2400000005034a0b013000012246401c02d07100043c0540c1d1103008406e0460a044170005401d466442079440002e81217422080d0001101e82545070850907030344420b081000750440341034801d411032003004003891a0b92441030443c0107400b99400051186040d442c05410b0303550203400a210b44a040c402c10112a500000701d46042c466403801b00c02011800c01151030408140d0080041c01c038000c1241001c1c181c0c564405042d80230200d04030b8464a60300c000599840406942454100e9800901800821150019440300c940360f86440384c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 551402742 1250 551401492 551401507
    0x6180708092e050a050c0403080307052a060a0e0c0f0a08070314060c0f07060b01090807060507030921030f05160c17010b101b020d030908100204030b0406050606 71
    0x310345010030110144115102d590724420078160701c240c0d94450030b0f004080000c0d0a1100008055010318400284903010010006030541e1240055030341084011000040c140f02c0120492000c045c1410302c18268443c1c0d800107003070784d0024040c10011400480161a2000050081c040e40307094051030782d41c0100ca03050000a140d18104110343c0154061710080c05010368500300141480030140801d00e0390007007070080e800d5030451101210100e581c400f2002a00204040058400c3c0d504e551040d2480d0003885000280c1f103070080001d080182c86566040038445d298400c400500c00b1844c62405001400c0c1c1d0650000780c09501810138880c4207041207800d0810440d190118121103500c1242c0e4084a0380c41000b561020294040c0750311003c0c00203100003400d0802041111400040c50020450700368800c80012401c00100c0d000700f41c01900c1d188841c2001c0c2000791021040303120f07414041c440c26400c580200000e200f950260307940150f0412258a4a0700c8042c09408041c1c0442e6104804000c0300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 551403992 1250 551402742 551402773
    0x1b011101140106020607090609030b010b090d0c08010b27010e0405160807030308060306062d042c0303010b031f08030c0f070506070b01051507120c0b0618070809 71
    0x1c500030b0506900921342d40c0f404100041001c03a01d94400814402180c00500028040c8185141901ca030514042c0c0c99600e840d000407050704507900081c4c00850602d0001c00d4241c0f040d040518040c009171440150740188113402210300c010001400310003410f4900510101d003c4200c1c50f034001c0c0c00b600c00c94540314224003c07028241074035841112a5800082c00308105500b0420059111070304030013410700d600d4503401040c61019444582c141244151039071150948c0c03030700c3c106a18000c002d001048040291004500c10842d01c001d4411201000b4910180006001080324142d80180b070aa07030841d110002490f007401102008451440300c19080403440300810030141c1012402c000050480b40d214110160508542e40c00090044000704201c60209241e50002570448e50240c5040d070808480e50040044c9001e0385100821690341344c00b9150065078031007403041800740110400480c6455401c101f02c0c595603010401401c10800c403002981d540e000703104007035024601c00103070340b0005002da078007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 551405242 1250 551403992 551404031
    0x510030c06090807230d1511040509090f120c0a0812040b0610020a0809042012060301150302011b080d0e1c14030c09030709020901020f1b011101 64
    0x80c2c441c030b10400c901042000908002c06000c007101c3d030707500600b0f0782000c0991591151345016019290b80e400400c11200001d594568042004120b5000d11182c3d040a43d071051040b603218950b000041079020381c0c00306400b01003000410050007140501240c80740d5070342040308a29014042d108120b008600a400142214002c0701094240b41c6002d1030036910f5000041d100074020030240410124944c2c00240320003115800c6054251102030707034400100607100406041d01082420045081c840404802a0040581035400c0100b55980e40b07092500325801d22940603901c0190500c10800b55000341207214242484100f01c0b0344821300d035111b08025a014506440d01d030303a034901c134102c3c8860742809a2050744820101004110101140040c2001ca0015018100420000205400103480c1e8221500d000024040e40c0402e5030340c0c10128001d41008000c94054000c0380c455440004000c87c2228101c81071500c102d00e038150348001150704003c4040d250481d0b40da070782c0c1e214440c00c1003000b8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 551406492 1250 551405242 551405249
    0xa201005030402030d030603051f0213030302010902090c0a0909050a0b0909280503040e181506011710030821090705010915090909080d020a08070923040510030c 71
    0x1105907507030030b0a20625207000e000d218403004140c60588140b00046012035011003072054840a00c9440c200c18038080000e100d845002405c0601d01c000c0001010b4044d08490b000a008031504141c0b69998000d6000d81d1081050200005142d04414030105d83c00d036200c143c008000420002d201301080e004154465001d13030317604017983e11401c410301824015450340d1290b45040c1880700c050f46d0031aa6610b50700e000d10b000d101c41c0508030300002100941254100d102d203030400030450300043d9003a10810200b0800380c42075400520010034804101c0c1c4240040c03401510b50140c8040340c10300d99120031405402080d08d17403a2070b142440f140402c07010b015400c18000c01c000070240c4465860134001410100060b44500410328202c0209004c854000d05940c04594000a020450b21b500340f504600f5407042c0b019524195101059401030b0540c0506001d2113010503407100110b03141c0740d0004040105202d0310706516807644480d4800c01c0e050035000755810030707012140720083c04d85980e10034482014541 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 551407742 1250 551406492 551406497
    0x140c030c070336140108040209040f080307120501050a05030a0f02013b181303090b180306100b09010302130329150f010e150d2a020a2010 61
    0xd03c4142c00791030789001c0100b652161003107002c2c00760300000e4032500b001040070f84a01030260010b002e0041d10540600404e03485044103030b4030303e0105405003103080103200d0003000c0351a0000100e843c3c18000c0180040e0341006000340300028140d41c80c0a01c40000c1d180490400c40380400c0683c01c0600c40c0070014851512010010180540591801c2141350b03410044e4415803007011038000c00c9501c207070b10300c1c1c01a41d500541c0e00394607440e0509440e102404d40c030803540c241001130207007080242d9000c0300111400450944070b0680f20440140d0408480780114406641c081000c042c1d10360103170340100000078900314a055125625142d1190480201c0c081d0314481c580050600300720409050255842910b0b202c2e41c440401076480450b030031541540c41941400b511b16110a025501c400c1020081d145640d0b1169440359500c189001800c1215400c0d0050000302e491603910321000c001e2120207820319801055175401c2929a01545072001c40c08001c0c2c040fa0700450800c1c0d4460503c1d100a01032241c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 551408992 1250 551407742 551407817
    0xb06030a02210f0408030c09030d03060602240a1a030a080702090717072105090c10050c060604021b1009111002071401090522140c030c0703 62
    0x4000c0c2c150400e0035203801c0205050000304111443c2c1007030351400d0b0456013020600e912a0348a03007072400c503481641c09617a814428045151007039a45a0040d1050340c800c6c0d800c0c0d0b02c44080401c006c2d8050306207080caa43d08842e03500c1c0050b40310078403544040c484440010b603030102c0300d18a40c040307801c0c84100001507c003000f0000b8907405506008200580000281c50f04d81c0751050482da48040301c1c20040d11034010068138007000794003e00030180115881c2c88009017002031307043c0b540010350380e03520140031640940035400c052448140a10240c41210404402030011a902c0b00c040200035404480c00c2c0000108080d601c401040c1308000300c1c52102401d003000140a103103403c1c0340904040d00382c4280d1045004560103001158085414401c59018041d6440703c240d055005807040d40441d001250012170072501081817641d22055444200700c001d404001414030040da00001407001c40b41c00700e140c902080491113035102400280b00383d4bc060b02d0304140c0004440b5015070081c40311580d6408440c0b02 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 551410242 1250 551408992 551409007
    0x1c090e090a0302010507020a03020a060c051c09050601140a1208070c0906090f270c0b0706060302040b04150b070813060f09080606010c020d1509140f071404020d0b06030a02 76
    0x904c105078118006d0700003882041c4903550002d5030355411250091401c4d03282d144243c43c00380107105440c201034011a0800a980404103547c0051503101d07416030b2280f04000001408a032004403100380030001520300c000140c107108400302042c86280c0c04983e65a420040c5801194664003464050503100c3c0b03000ca80e581c0340103c0082594443c40c5038a98161803c4504018030000c07003200502c103100c000c0d0010f82030b800c03418042d081e05465030201c10a2103000030b205082003265402141a64401c4404204048005c07052204440d07202340f4035440c030f50003240180f1843d41c80784094410148241c82403807410140c4150070240c1c610b81d41c000400f0850090100b01c0c0e00740c01001e004040c0640c080100190728004000130b122200640023740100c0468609c0c41c24492038002c5070500d60307415501400300070801d1810600b80e004038818184a03014050319031840c0400401c0703480403036072800190344a02c0d10660030030000354418a1001c010760f90714603601d845510341801840c4070304402c44005844058 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 551411492 1250 551410242 551410247
    0xb2d0306040c1e05011e020c10030b01080c130501051818040201021009051b04060305011a01120c210212010b0c0106080105010b03271218010305091c090e090a03 71
    0x400540740c01c240343d070103102400580da2000000000c05041c030080d040d401d0b0003100c00c2e4189891032510744c2d0410075210b1000307840d64040c1c05c082c4180101303aa5501d0b076075403880c80603503e9004200303070000048500b060410a035841503014084401d4148140407568501c10000f40300c0e1a40d0010140320064040c003000203568042c01204024440c03940d05001006080da20141c60382074441c1211704079041e014081c2e07101e455a510800107180e110703000300861f1036000f00b040c00303c4181d540c4060000d201201030905c0c0f9034050041c10104440c0384c403101c201c000f041109600100114803442070b00c55003403021381d01d00c015054105000b040f580700050740d51262408081d0a540b9540c02080766607041c1001003200c80500e4040300e600400030b109140100a80d20590302000e51030081c1d40403d40305d0480514282140c0758010004010040800018520248015000d0f2030049540b440550414040c2c444808800350441241c00d189140188483ea20341c6001c080c1c60740c06542084441e4400341204d0704054 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 551412742 1250 551411492 551411519
    0x7170a02030d02120f0f0402010804030f05130e06030705030d080412050f070c0303020f16170a05060f090c010e13050405031b0a020a351609020a080a0b2d0306040c 72
    0x704c1c0150140347c107400203480303182c010b00010200304000380d0000d01d09101b001650495280d843c080003400340d0f40d644c1c000c010700c4d058540d288a0b0060200003c0c40c0c2c80c00051054441c2d5468583e80f42903a40c684807405803038003400825080c80f038200412040c8541800003000c0d101d101d40b403001c4065056040003403403c3c1c5e4440b40e40145034003000704842c18001e030740b80510465094011403160121038101c582d007850001040100944030364010310062042003c54644a5079803035040b2402e6901708801140d225258003000c5400c044e01d42e40c081e44903079480e00328651081c01070781100e1030f140c50b000048a894a9803413024149401ca0240c035021490115408070007403003800f00c0c0e0741d0039071040f18101c0c00e41d403480f01e9810803600c92500c1c5074005800502c20200309148000700c0c026010382d5083c800019600c00e1090000148024001811500715846004020b2601500260702107960340d0110a604030b0704001c8501d010030307040c4c0e4802c0035541007140d94480c91188100c19420742c0341c0f120440624 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 551413992 1250 551412742 551412751
    0xa03060509010503191401022805040b030a050403090b19141e0304062c0f070b04090c02010902270106020a0b16110a1407050607170a02030d02120f 65
    0x1e2074901d004100795540040c031035104c1308925402c0103840c1994600500d040c081d001d0003080c5c0d0f50001c2625116a440030094016800554151000300620008215020f100314000d400080c0014000304e50f216100d5804150300c54428105000c2c8292624065020307500090300c4022a18492039014010640c00200842c5030100e4143c50b6040c5910414440541c4042c032842d03403400300c1e010000500f0300c1101d030010003d0007082000801c400750942018036918480321020300b107a1081070783c40d241030b010001d0000c0840c3e4007405041c3c1440d060103407003030140c00100310783d100b15926003640002603524404901e12907400c01e0580a040c1c00811103c54030b4100591081e000e640207141000d0100301c0d42c010003640500140071801c45007c08800503101411181c40050181c461001440104010291802a584108000c6030321b020390f900708020f0140f09120008186080c9415201c041013050b0024124820300f60040d203050021103481e0900700c2e00307c0710700041105a0311061100e400360b0f040885400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 551415242 1250 551413992 551413999
    0x50601111b2106041205130b0706050705161b03050105010e07090e041e150903030c180b0f03181204140406142b0507030614190513080706020a030605 66
    0x454000034030b450b00c44400400c05003c080000e002c0e030307040c1d80c40380046031000303880c00b00410003003600d40700500100d801000c0d04498041c50480441e02150040081d42e010022204601c00a41c11654070700c5001541c90074040940c3c4026203001c400030f4002e0203680d010340f035800408d1291313150415004100c0c070345d0395025500d04039400c07091002040005624006004403010224284101c3d03140c036100c01c1c400c036030500c441c2d5440c0c220300e2002c042e81500074040440c4c0541c0e0b0780c0032082c40803e0400d80ca2101c1d2140300c10fa41400c001101c4902040c1028542c480c001c05141d100074412418040e080c03c003c8a10301000190000f02031000001c0c078000c803500d19101341c81c10411581801d180b80790140b002a140d92050707046800f10f0414550440210070401c2ea050103407001d55070680340c078543c1c500d10350000b101c1c0c1508284803080d4030455145075920540c0042c0c41c00c00c0850603104040001c04c40540741d000a0420000e110012884400003000d075203102e40e02c0140d98080901c03004040b00e645e6088140f0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 551416492 1250 551415242 551415289
    0x1309090506010510021b0a0f060804170405010e2b05031c1e0f060812071401141f05100f0e04090804090b061c02070b0705090a09050601111b 62
    0x413841d03000a100c13104030741c0702084106a031059000118071155540c4514401c42c00498042441c0c0c0d841000365000d50f11402e07001b0b0820b01c412500038614015030103201d00041801c4d80c40d101c4c0b4584021681440407400103c1801c006080740c110b0845081d4080a407125400010000800d9000c00b10280050380e0702503081240d069024030307111031855803106100c0b015803664403180c0f0138502a4400001000142c040340c40441c80007500c0001900080c6040d501143c0108400394050030601502c0084641544d03008407556622680c803071200c085e1004460081c4100c0c4012036030351640800c200d1400003e840341600394200100044c80007106601050180d030408800000142c0164250f40c2075a4141d0350200d4144204000b04009015005151a403100222220300f0300068940c010802140103c00391045540d421400b82c41520410107050f4014240f50010800304189512003074021034145414051038040c07003062486c140448c081c3e5013420030311540c0802d151030142c0d03004030f855094050104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 551417742 1250 551416492 551416519
    0x501110d0e0906221517030409023f07031a101b060e010c0c0f020409060e01020a0e030d181401021903030504030912020607150213090905060105 64
    0x1000c001042564034050a440404500326550740039104e03841c00c00e5000310224221118035000060404502c2040008803080c802141445c580707030b40440254021002075280c5444c3c00c02e24002035103e0355503041c04074180718101c121485000b64800100d064410106c0b80121000040d0072502d00c060281000c3c546040940d00d03400280540202440d281150b02d0822034001c07100c151071101162000903848500ba60094003000740b0ba80c4015801101034000300600d810407030003034820b0795009001410507a4043d034040014a080c4c1c2001408500ca0320300441c10b041d4088202c8c0c00c0ea04040044004540c002c42c42d01401d003010400031107001418542108858840c055018006142e401050001c1c042c7c45682940799000300803410512440c031604290351318141c04e0040c000c10085d0b0b0100c0004000c40e20000702c0d20201052000c0280d0001c1002e8544407803650b81d00613907410220007505964081c8850030b1050740d048007900c001d00da4000081000300003441c01c50304210058001d2442100311901300c5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 551418992 1250 551417742 551417747
    0x9020118080a0b310b0702010501060507080a120609140a0606050906090409050601080601080d14090f032a01171012080c07151806050d0207060b0901030c0501110d 72
    0x90b9042a0400d08001003900d94002c600c549120f071310038000b250704107403502c0d04114504a01090020340590034510113511001d004034242d810038454600018030602400c8040780204008041d100c445003072000d880c460082d660301c240c41241d4400c4600a40d10a2414414071031101c03019480700c5190b008105086c20088040c043c1d0168404d484e008010115509a80340c0322035025450140d0498121052036a40d40b03031895030303940240500040342c040c40e1400c0b80613900070740410311440c20602900d4100000402801524184d04180c0e9500d0f00c10f42c4010500c2038024013049101d00409510038040c4d80c45034002501e043c56510b40207030f0080d0700408000b6509448410700c0e080e0b444640c11550043c0c600c6c145003001e4040c84003018842e001c0c1484c0015484103c0094054011842e00e5401003000c0c070104480a2026a115820108030304100e43d1071050f50b142c0c010140d0070307c00d0100280c1c07408004085020501c00740c00443d1004803054082c002076800a680b080803018000042c070311550440c100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 551420242 1250 551418992 551419003
    0x21c08041a040302040504080306280b0c030904091217040c03020d021518010e0d030c08030a02070f050a0c170703061107060c0e011b080313110907030902011808 71
    0x805490760054100d2a00c0821441d00b11401190020310030b009a050030300b4600c00035030040e41d4940c814103040034000b905025080c5141c58044081050140b454505051641203a211900030b803190b010400580c0c02581d500c0c0314001485010380401e80170380c030110001a110b9103145c0511011818a42c040000060103100b8510690740c2c180c41c1402e112070700b480414402400903568500e28000841e01039401821303000144a012003d98030100012424070501841071145a000340000350601292400310310800000c42d080131460b540140b8184032501d4100001188800494040d00b2002070141401450040b12000c2c01301d00f141500021108071000790707a8151444000c01d1f69407905451000c0e40381d01000d0792181e680210090206003c2600d000f4550380403103030403070302240820440b040400400340540e44025032000c45140b0b16140c01001c1002c03001c01030070480346c01c0702e0f2042c08071907a20b03443c2545009115039140824400002c1c400500080b1002c1c82c075a4612070710b12010464100300040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 551421492 1250 551420242 551420249
    0x901050d030207030506010e0a060b090609120c0d06050a0e010c020703030c0f080f030a0614060a0c0503091f03060803120c0706151511010c0816050c0613021c0804 72
    0x3030085420310280340603400c04000e43e10180c01805400000140781c074603861043d100d42e828010402c210340d1030301030303013a9207008099080d500010305110484c0c0604101f00b180c1d080403100811180800788a100064032183c0c0e860341114026118000c0c801283c4281c0611035800310264024022a90001c0d40255604900d01c03014041058004c03090f001d0000c00450308200700d400202080c1d0b20645149040d41075401691401c10380313845d0030400a441e840c1d101418103e13490060030b0a15111914108941c0710030901025209400100002c1c04265680706070310350f148084080000005140031005400c48400340c0c07100c01c40740c004002e0450704001c40c0340d8481e0b20040b010402521115141001300007401e0400c1049000140c0150214400c0620b0a80a080c589540d03112441c0c1c506a800386401d0300c0340103881c0f0780031842400100708868402240c0500501c0c540c0b0740b040c14800484041480c01c08141c9400700d031002042040410340c24448121101109495071502c5080080d42d90002c1a00c654071 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 551422742 1250 551421492 551421499
    0x408030c0409020a0306080c030106061409040e0109030917060c0406030c020c03100e1605150a020a060204030c061412060f01200d111b060d1d06011a09090105 70
    0x5855000c03420507035002d40920107045403110740c9044090000c02e035600a440032840340740e80098181c0380502441064501c0c84c0c0e9450140850b89a9407040b07030300101d4216520503121000c20300d01d08024411410300c28040e035244081c41d40340169070060303584084400089a007088040020b5050104122000c03154503150010301d01d1420728089040005030950700b07526002d0030700603e50038010380e04640c0d006030041c1c095464148070200c00550a02c640c1c4100c0f0f030000d195032002e03448240924040c02c01c1c4a59401070340c0c0351045941c1c4410499105401c100c4a44015080901c41d003070b0721802200401e2401ea125038640028150291900140207050522441a80c024403100d039104009960100e40d501e13001c0a40880038000b51500c4444802d40e01000510307040c5c60b20400d03400043e80340b21601d0b030000c0c0c1c8020b100706107050082ca82d00544c0404841603e440e80500440602950b1414083c1d181d0082d240d0f550400c0c608511000d6120000175590000b44103c002668504401d00d0441d07a089 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 551423992 1250 551422742 551422747
    0x60e0f0d05090d1202061902210603070506030406020408070504270c080a0503040918020a0303120b090903030708090105062b050d020d03140c0403030c020a0801050108011a0a0503060408 82
    0x80001032a0400f140344020146028000c450261580005030240110102d103045418210b02c94801012070059411100107441c04800d00180080441c682d240c01c4003003d015202d42c642c492011031131550007a6004c50380075600060401808005100d84006498112000d100b089003022160756014070404007400b403001904020403c101442c0301420040c40039074240c61220b5418105680c4907000780c8900c52510381403050301d0b012180c050240d440c605500800440000e8215101100d030459441907048540d0b941710320a01c01e0b43c0d2003484052281000800a542d6850403640c010039480000c4c00920541e8100818010309a48805010601c000540d14107090216800c0f0040f04000101e80c0c06401c500035150705408581d80851244200c0c150b6890034403401380c0345030701d54903490300c12514110381000910083c000648240d0b0641083d6000520310050992151807041c00c403071007a03012410680d50780b0700141c911564080744003c940411120307445810b01c1d0002003900d54800500003032042500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 551425242 1250 551423992 551424007
    0x10510090c120c030b0307080c150f0706060f081603021003020c0c0405010f1d070e06090102210d0b1206060108040807140309131503021201090605040c03060e0f0d05 73
    0x14455a42c00d4000400742408103031003e1101600034521103070710300e000307004458020600314000035071a0204180a8181c4840c0307514103807107185503040340d4030b01208040108a410b002c20000c0c0a034801a0546813403484400d4a4070b50280c0c40d0880d01594907070a141c008100f0000740c0ea560601c0c5e12810050304003d655924108641420403503008003041d489884e000002c0382c1442d0b181016803e8031200e07020601d4155240c0104480c00e40100c4100c80060003100102c411420314030081c04245074180110380c1c03980c6c2c0961030401c030803400301c03809000540702081000c0c0c0b2810501940d480d0324415210054400307214101551244002000f4a05110040010400b00603241040303c280c0380d0001c43da0380031038a4005c586070301c035031040180c80d104914191401c039a80606104800d0001c0d040c641a1744464595402d101501e01e018202c1d070b03980d540e1084d900e0041049401a44e1281d4031900e11120b080d429031800404440000c2d4003441264071184940744d10040000f03102c8545400c60a1290302d0b540e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 551426492 1250 551425242 551425247
    0x10524030c040e0a0504060b0312071106091e21060408090105070f0309030302150f04030c060e1009120302093f032106030a032a030f030509010510090c 67
    0x2281d2103c5129210242040704003456540028015071003000140302d540005000c00d80da42018644801d641041000000300141c2002d903030889a200181c0070342d0805d450b040000e180c152040c0d42070015801010644503031450034a6080000c6113188080b40c00200010401582c0c90074001c200500c4000009110000390b800746017074640fa00e510241c07101e2144010719000384100034501c001c03809441801c1c028000030603807000c1c0c5442000c0244e00c1501541c0d41c0c0c0c808070760380c0351010030a458403561989120a50b0805000203040a1540000071801507820b2a0a1003015000160501014030500103100300b42e5404046003507070f00b5981402e0b100c9001000c60310184440b1321000404c11a00c0c0f00220b6084039000c0084d00010624560680c1218115800d09180090881c0c2c1994035400011420300024003c1041000d510003000b101d041840c10411050841d400c2c40c4402e60102d0550340006005a1b4940142c540c40b40e2808001d000508003020110580c0030b0740d0050f901d600c2d4444854810740c52 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 551427742 1250 551426492 551426497
    0x90e1501060206190209120d17072309150c0d08060303030c120901020f040e0609060d05191b08060103020a1409070f121104090f061a0304020a1a040905010524030c 72
    0x2203d001030b10000926030384003a10310b0003d200c1c403c150441c0440020030640c0101070480c0c1507004159000394040bc00b55190071264442c0c02220307840b084078000305050400d818058655440300c50300900110158a001811140340288024420352081003041040e41031541510741c030380c003d80030344041a141d4100c0305019002d0724400c003050038408a00016080440b07140300d0b002e020b05035100401510f0759811300c600c0001e801c01c0a02158040c1e411001c0503010b080321000c0141c0264003600c4411002d189590b0404ea00344c0c0302a0140e448400140190315000c1d17501c0b0014901d1112119118849402144181c0c0c00240020144001c1964040e900340c0509840e0104003c60b80e0101300c0c0c2b220b040c00203d0603400a00450704460310b044511828181d00c4c0c4100f03800d4038685000040088004449220309a0000303104903002410800001100760762080300b90508400c0034442031701da45c02c01031240203c030380517806a80700300340300041c549092140c0151414009040b243d143d41c0c80d556490380b0b544e5031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 551428992 1250 551427742 551427769
    0x3080613021c0b04090c1401110312010323300328020f120604090803040807030f0e09040f032001060e01060903021f020106090e1501060206190209 65
    0x40c0006030b144402c0752016121500e00c0c56605003088060003400c00d001c1124580c080043c041d1070b0000d0140401150700e0154425030b4014585820490107070000c0c5425900300c00120ba428a200030b005000b0000044d02e80c0c440b4840d050b55880d54503500c20a200e03566541a9800040003031030515881d6002c81206d000880481e000d141c2580e681000b907a01801c1203510400c002c0300d04800303030f03401c04003101c5030080b68400d030741c40d024050504100e8070140c68020740242a60303070300680c0d075002e4078005003540c0080c0d07100314082c00c01c0c83d49134140350130058808840c41c103102d000c00c0703100ba2102e030050740d512050581141d049411000c00071003500e000e40d404a80360812001180440b03500840c551070542201007aa41d00c1c8100c01c1c016682c0d0303101a550294507000003540941c80320b160306500860320080d64446a0140f001107802951004400304071035030100480d001b07401454000c08509000e1010300d0041c0300324401005245001c1d512901201080041c800a0540001e54002e0b5a030300d803007291555 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 551430242 1250 551428992 551429029
    0x8010f150b09010216141f050421020306070207030b0c0f030c07150510030510060b03010b0a120207060e0c0d050c011206151e0801060207050603090123061e030703030806 75
    0xd1940315170700100c002ca01b154035980304620b8001551040890a0846c00e071060060b2161420282003500c50f504804110000d0042d2071405000c850240c0d83c10403041d0301035092500039040389429400c1c4408004401060010104c030200f203e03034900c1c1c02900c110780e884581e9076000da441e0a81842c201131204001200d0f0300089050905004054408102e503c00310ba200c0d02c215511024a05030354019031700c15110b01c0401c61800e20040051840240043c074040040f49413443c4e1610600410f032040381c02c003401c1034640d155110061a00d010081211140207036080396154400368003540c5555584030f940813041d0402401349482d0280c24401d4200d4009030007c00e048920f06511540010205200e20241c1c0740300307040e20324651501501030320555060341c01351343c05071440c01d042c08280700d00c0d030b8000750100444e5907840e041c0c900740d00c00700e83c8006068660509120400e06003001040340043e030000c1c080000c8402c480e02c0c100c090f40c0005000c1d04403941818544103031780c2c52500041c032035007070740015146 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 551431492 1250 551430242 551430283
    0xf030702010c1e060c0e0409120f180b0712030219030f020705100903030605090c0405010302070804050405070c0c060f050d230a05040b0c1615020c030c0708010f150b090102 76
    0x2c01600740c100c2d03600141161b955042c90480c07281000180c0308403100c054a92004240d0b6035005920512a405d281251401c003a004030358080c5030030311070301a0b0390b0101210002c007040c15820400891100d18091080c0c2c46d0540c100304800e480500045441d021942c00d0690b5440da540e00e0b250310b6010b6a150359000380c1a21300841c1c10b0307801c0c00040d2043e4a81240068600b00d800b10741490100031090050b05c25140c201e0070113060100640084d4840c440544429600380400203590740d4a000c0c10b84516130903982c0e4001d545103481d10400940c2c09030081e90901c41040ca010300450b50000541c1e4021040c1c82c0d02141801c09042c0540c582140e440d1003c0c054508502000200040d54200b80c2c000e51040178100c02ca641c6906107003485001d000b00c504009501c56154070f0104407850007607a035020301500c00502d0f00a030b0801581c07071507215240c5c20405030003080c020882c40b142889900c5a24035003802c10720020103000701c0c0a00d800118002d032148000c0200e122807140c2d108014025044c089241c1819 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 551432742 1250 551431492 551431553
    0x3091e0323120108030301080601230d050c0301061721040504020703180609050f0607050c0325090209210a02090a0b09071707110309040c03060e01080f030702010c 72
    0x19a02e0b402031040c40d031100840c000000d0380c5200041103034100c0c1c4814003d461182d0070010100f903122041800c0c56903502c0c0b9060050455a02c040c001d804551165009140c014800e006050039503490b544070000c0d9000a0755100700c10600070030885c0d1447c80c01e1a46007001002184a0a581c0c0203c0d0000c941292010840004242d04200064000585520203101e01603954030100d0346c813842405803d070000b2008215828905040c8060031416203c0c8007528148909400401d19000c880070072101c0300c0b192002111008100710000340090f2010610135880d10305403e01245035000810810760303d0540307516203418401002c2c0090031240e9401448256141008129480500f214411051055003400302094055001d003050308810030741c43e1070100441e0f0f01e07032406540200c403d010407a1b40340000c0201c000195241e109903a02c0144a490019606003821501c1c20310300016003000304903521030b0020b48169840041a58001135091130a9045c2081d03529000b5641e844c81d41104100c110301c0711201 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 551433992 1250 551432742 551432807
    0x5010e03120f0c070b072301020d0e010c030c02070806010302090907080a05010609050f070909050a0914060406050105010906080f070302210601080a0b090610110703060e070603091e03 81
    0x2810b502c0080f004442489440b25100c80403072064080041c606403e41d9011800501d50301001c58510f030b0288001070074402c000b80000b0940d4800c2202e074409954444011207001d803d8414501c1c1244103100910645e070a000d9200d40c0d903001808003900c204031120001c1c010b20010001c0f03502a00010007a60305825903449c0c12800781c90075000300801d203404c1100046240508090f103500c2a0341e140d4900d0b0003140b40540d404c00601c4094602a65561174900b04e60210309504d04041c1011194401080146440e081040132901d0603000309040081200041002d15070182c95950001103034804040e040d02c84820542c02403055440d071802c8140140d075003a0f80c400302c2020a5205080170380702d14180743c1c1c070b02e10b80720b044039100300119074081503200214529040a0b0740b2a500031440341040341c1c18000c6c094103d85010500d600440d081e545521010310f0707041c001c4c80308400800250609000c1964a40d8031000000b40c00d801404181d0781100010051510032400c0307803003150701c400b1020306950108809 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 551435242 1250 551433992 551433997
    0xd060e0f070603050f06010f0c050319050d0b090105030307080c0a1203020a020706020c0607060b0a05120d030c02030313110f092410091e08010f0f05090f0705010e03120f 75
    0x1400b01103031812000625080c01c40003500c3c0b003076030142e5508010410050050b1004030a40c070040d1041e01c400c0c40785e070501003402c94021011400d1616580d403105048030b191000e6400851400c0e000d10783c95001048035807000401c0d03c04840d407100d200c9445034554558030385030801454003e04030200c005140394030150075600900c6030707c80a40c29070304d07440d4881400f682d130781076101143c0350001c00820541001c07a415510242501100800c0041c0c1513541d980018029040f0f0703941501c50b5040451100d601076054440c12121030010f0000d581146000c1c1d150710b4509040e000040c10541080e040d009450303680b1856041d105100604040c03079070030400d181e0a40288101180031a0343c110f00c10001c0c19141c0000d102d5100c0704180c0c0c07030340c4101d401c1401400300030380301020703140d60b2581008012910003030038022892442c510480005030752076100704030020341e00c010744448643d4204440d2451254800f01e266400d4a0f0282001c4c000c1d20503c40109140000007181c4640f418008110284900b021600 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 551436492 1250 551435242 551435249
    0x30403030218040b0609061e040603020a090801060f030209060409020916030c0c0b150a0815041505060a060807050c0106031b0605030c2b0e0a0c1509050d060e0f07 72
    0xe09281c024505002e0000703d1300107422869000d441482000386910748200203000301c01084045058036041031590140e59000342c3c0241001c40d4000c00c0d100302c0707554448109801002d40c10000e1040914040841001807023500020740100200c500003120758403142c1003200300e0307603010345403e042d40342803004100201402d2008100090500003510400791294000c900001d4101c0c0c0c0c20482c41c2c036102002c1c007030b80c1c3c211400c41e40c04c144d41c0c00002800308401e108000002c0c80710b01c045081d03032806240034805842421890f101c11071610703003440030726221107602d0025510b407420b040900b6154580d0550b594010003090b9162982400c0001c01004100c116015003105494101154030307480744020382e0796000458007502d1042050255000c0d05000d000d2512025026144007003032104030030480320544841c10080c03500b1b540200031a40800540d040c01c1e0000b001990265011401c001800400d401e2451080c40c2c40f0352400310b007280a11840d40d1250200000001c1228040c60329201d049031a00d20510 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 551437742 1250 551436492 551436517
    0x1611180f041101052b0b0904050105090c09130303050406060f120b0108030a080f070909090b09120a0e15040509130b0901022a07080d03020408070f0605030c0c030c030304030302 78
    0x101080307640c0d4003c4d402e40e000048904285034803a02d00c5000e440e225009072091240c0f00e521009a40c00680702d4144140c0200c5c001c00000c1001e142800901d031804c0b258124060280d40c030f00042000c034181c0001529041355240ca400704480d1541e0038440301405041d00117111100e00f036400095080301800c1402c0005110340d00313103511a030b65402c0080c2c5038040d00380b0301000f040c54400081c0260040950040d030081c0241014001079803182400000c84085180c2151100849400d20503024020003000740c46400031102d4600d03204150700010080308905207018002c1c40400c417034200b0700309000251005050003800c80c5500d80b41ca617074442449410038030140e0782010640f0105030085410b0023120000d1400120300a52051a041d4050558501c030003a002c00d80640f00000c10003000500c1501d0344414a0707500940c88030705200c28203040c00e246a01850090482040801c02150084c0680e42c1c00904075000ca9110b082244210342503100e142c42701003040c00004204400c264140d0301411840f070b10340d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 551438848 1106 551437742 551437763
    0x105060a0504031a1509250909020a2604050d0c03050c0106230604150f0c08070c06032f3106141611180f04 48
    0xa6102c0c2400b003c00134244084540003080c0d00c01030a40071900d044490500c100500c140c1207202c81c14511118050810307541380c3d07000304c00c100c4c0180306848065589041c101001010369075000040702c0b040010b144116603081100d07000714420381d030060080050ba14804000c1c1c64408010000700c040101c10007160545400a003c0c08008000c035000080708801c4412941f20003c402d42d03800c034010b407010711003044002e0303400070488002205400d15030038021940800720340a180951018000000c0001c2a0040100030a480003c507425076038200700d0054402c180c01c2c009002d180940e80014020b00008400d24900001441d03015402c509211040c080d000d0013600c0c080b0700c203400c08030001184008001c0d481e000001c003d410100301c145240340034104442c032400c0c1d0a1954000e0182c9690f2221400d03607481d81c034040c44203044017003501c008030303c0c2c03030000141000f01c103c4040328507170b444 = true := by decide +kernel

theorem cover : BRFrame.Cov 551258992 551438848 := by
  have h0 := BRFrame.cov_init 551258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 551258992 ≤ n) (h2 : n < 551438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
