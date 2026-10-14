-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2462
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:47:08.214611+00:00
-- url     : https://prove2.me/submissions/77e29aca-2bf0-4f65-a2e5-5674b9af9ae7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 442625899 ≤ n < 442805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 442627149 1250 442625899 442625921
    0x40308040318060e0f0301060501021b0d02040507032901050f03100806010312080915040605070903080a0509150a05040e090123060102011406030606060d1506020606120d02060c03040204 82
    0x82ea41c500002c00c240c010300200c44d1194142c8030a40b40b000010101400c8800511031035016800401c03c0a0f9046419080c1e6290044014070300b0894413202d8000c2400c0701d600321500c0020036561007008010b02c00d10f0900307031108030781050346062070f0340c040300002c0c241c0c0108001d000c02d4807804400316401022000380d031005403541030110382d01c079031352814199079074904034903860017080303014022861100012441c061055030024810580e0b07150351341d0f00001003400801070700400403040000701c0007802c0c00d002400d0641103580c6480d1501c0c461402c1241d0a808516003075034000e4100a8940061b4008064a00729407040c80d03013504c030340d84803c070140c0074110003201400c006010f608030310880e006206005003d0715003a4020014540c2d00105105072017400c1c0c07440c0d13030705030b2100c0005512450f102c402412003004286d4041411607444681149441050700000090303006582000302605110074001821012a001400c80020790b91000e9250200500710006403d0008001400c4d5140c40c1c111001040c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 442628399 1250 442627149 442627187
    0x60409170f0412080a08010b0322050307050d0e1005270316120605070305070905091b040308040303020c06160f0807050312060405060307140d020d021f02100e060403080403 76
    0xc0d0343d0786082c01c400e034002002000030a44643c0003040c042003036000c0e00d02c5130a84544200e003000818461850111b04014125400c2c0310403c00d44000500c10701608060140325100c4084c0d941c1c80c1c40801c1504180c641e8003000b00f020a20035020320b1035440008a00b91858030312440920b01c10300011074100304542380c0e030040d9080ca110300021a51360301c0692000c80c40c00b94a08001c184c480c030604030300351403003030395980b001504a003c184040d160050049400081083c2c0b4400303485a1441c0e4800c194005600075582060701143c200241901801000140d007000c48170303036180440fa4500043c80300130f075170006080c8035503110b203110802503990100c07071040790041c3c203d03600c0d00800d406d1125540c0080f40c03050300440c1010702043c203e040000d54007007511008040102484000c0091080c4888020000c5c0d03802601a4542d0026031102e00e0000303007a44407080c0e44031010115030006071505500d0608030014a1925003403100c010400324406811590510300710a80d074170b0740e040494202181440c040101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 442629649 1250 442628399 442628429
    0xc020c0f0d0206220f0e0f070e040e010914030a09180f050f040201141e090f19062a030e1810060801092d14040305090108060409170f04 60
    0x401111004124082c1c0c82001484545071280740d000440c5c0c090b031180c0d91145001e1030208143c4881d00307100d070754007130080d01d0500d00d8400d5070400102600c000c0f020b012000d0b550781080400f8400402e10280c010040040114685101000002e000b0081803084042c007a0380704410464a10081e008119252900300c0188081e0609514884956006440880c0403550300012901305c44001816a04102d01d00406200301d0942045a00c1a5038030800e5655440000d03120000a151b0701c003005100102140745100d40030a047c08800f92007d030150045000307007000c1d40d0408442004d002c040c03142e220791500e0000100c40d441c80100b24101d4a03900c05100710410201000313005000410303c0360840c1c0396541d0300000c03a6680c401c88030468280c001c803a80c0362035060785210b00340355181c03071640b101500e106800203a050101e0110807442105540c110006000001c10004540c0d000c0121504080c08503010041c0d007440355101c0c102821242e00e03a001070a00030943d005410f461000303590003411403c4402c508 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 442630899 1250 442629649 442629667
    0x10c1e050d0e10110303070f09030f0b0f0709151214150f010302120f06010c0f051623091b040806040204180c0506090402041509090f0c020c0f0d0206 66
    0x140b081e0035540315019010f12001038983c0c0c0e20640c00d103400003030007401651554640b401d0032540e0700b07200d10076030003030042c40180000000c80040a0341060b5000d0840d040a50920400b04001614003407c1402000301aa9050003114080d850f501c0c0181c07000d040c03500030072034014003407000313450040071060030100c0740010042c855001c40484002c521049076400e0407050030200560807805070300050540541098001340448507000f5001d0f40000c414145201c5c03074504c55032203001c40d8090300011a040c4d0400100a1302400801c501500a41b0049604110500c0d140311040d9006403403e01e003d1040010601140c0203c900443c50b100d40c0c5109585d081e9669215000c507a5078003003d90b01240214640090f003401c40561104503820551300903145030f4079520b08010000f05030800c080c4503900035400c100000e090b10b1342c400500080c40070740c0c843c2c926051a10100008450b9442c002d007000c203003454040400c065020400141148040b01c61800b410041408aa44802c1d202c0009400c81000628888 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 442632149 1250 442630899 442630907
    0xc05030a060b040b01090f031e0209130c05010e130c030612060b101403040f020f0402190207092d0f0e0304031106161101020c091e0114010c1e050d 65
    0x21810400f0b4800784002d01e1040011240b01c820ba1240705909045100c0a000044c6c00e040b01210b5203880e4015a06000c0d030a800242d8102000e841810340800c08918940c100402410203800415090078403281c5202240045541070485136545015940c3e01c405a85040b0300039480100035000164800f02110101e10344070f00188040850b040c85210800c090840d650310400022580003120060b160958840f9660070102ca854054100e03400700e6140e8942d99079890714401b401c020158041c58203004110034101038184801034020301e015030b087c098841c1001c074070000a18481a8000115a840041c07140414020100c05c02420340450a0001c0e11006400020151003617a00a48011880058940800c40103200e02120211a440b40700307241c1c0c0206184150001c40d03c034040c0155654241c0d04130000fa4000d10449004400a42d01200e02c4400310f88030321040d000d0301e200c408030a0000e0940b0f0000c0c000c0054007000810308070140821414000d0320210012405078400c0c1160f640c0803080c07802030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 442633399 1250 442632149 442632161
    0xc250503030a0e060a060302060405010f090e1501030e01090b1302010c020301020f04170d02100203040f21201b01020304080709020901030b01020a02100e120609030c070e010e070c0c05030a06 84
    0x503d0500c642d001160b500c031110f100340d0701103960044c1814a031601d010019078a10003454101400d1285c01e440016140800024041c415000034140c112100003030000942242c080e501c1c100401e80c5000d400d04001070025460b640c0140084840c5113542e01d1a00c012a0f07500c101013002500355001281c0c000c40e21500c00c014100b542d4180031090440d503c001456aa5112920300020041c1d10403c04844032516550007560064000c111500104050f0349803504055425401e0031010020010100d0100f584a17104030410140c03900f2003611941e020801075070b2803203084400080e20068a000c511183c0c02002203800525480050360050b55590003003c0003904200c5203d80824104018030582d50300c0854506050741e401011a115180c82103030454401c48040905904106008803101035103a0411100c0d118084035001140d50b413010030707199400d11200380e1180780c14011500c012b0249000328901075500c00542c3c9049403a0481c2d904110f640e0351500c0d07000135014064482d5200070b2107000d42180e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 442634649 1250 442633399 442633421
    0x1309050a06050a06080a030c03050a0e101e1701230904031e030507020d030915090c090b0a12120504170610080c2107050a0e010e010b030c250503030a 66
    0xc00c40c0c9545e9400944c0ca42c241c1d072030300030001003240d16107800103406a4080c08a082986c03030403a4074a08024003042c8040e80d8040b400d80440c0c0f0280b1409000740d901d0319032100c20343e202e2400c0c02c40c01c8410003a00340041418000c1d0680c00c40360180e8901e0204440c3c0f18840c080800410003100c034103007800c01420041e064485050300e0860308407583c00450080c0100d50007040554020000c408200d40f007140100f00c03c80d0200c400e81030305030341200802e18030b000701c10344c00d4015040c160155180c1070009044034100c90281c1d00440d0803103420052a80304607401820180c004e2900c80086d65001b200311194030490300004110510050303112860540040c00d80d100310060210f85031055103a5114a61318404a500d01e03074000480e6044840c0189100700070384840c1280310844070f800f40c643c000600800c91603000745241c1000ca0700104454001e8540840c01820500c001d20b00d5404e12a83d080520310a1041d81604003010f008800d40d03a00300b681c1e181a030a0342101c01c0da82c807814240700d204043e0200041d4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 442635899 1250 442634649 442634651
    0x1c020d1b0e03010b010906031518021201080c060901050a090f090905102f1b1609091e1a15031608030417030d050109091a13021309050a06050a 63
    0x2403000345040501c2070713860b107450585a01e51014604a01240944041d040c0441055502c106c0018100007259000d0141c8034059030150719000080b0308500b020405a01440c0c03c1d512126000b0540d481e41000c8491a66003031a000355144100d81054480c42c1040e8000341c02d00c3c040c0030001800802c1c1e54488420144250306560920500405000a5074100403664900440300040901c3c8040c1001e07904181c0541e141c440c07400d00904255010b4840c0e40d00c4901d8009410140b040c80501c9408184940076000d0154100b1448403e920f495100c050034500d2480030703078101520b030f9040c451180c40000a4504040074013290b0f01d40600d680204039004400d483c068440c070035085075546810302040023518080700055003003a103000c500400d4045c1c0c401da0700750b940c00100802c0c07481c00e0060284078003070851000d01269900c0185056400348845040c000d00d0f0030003040074011070042e02d40100468580454500f11420040034951000303000304e850050003072050038040c404114072900128070401801034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 442637149 1250 442635899 442635917
    0x403110f07060206151909050627010608100308190c0203031903151d041e050319170718080304031b06030e030720090a1a01020102040b1c020d1b 64
    0xd110346c600b41d4207180056031948090501020150b540b0882d84100c2c0280700f0503003040718501c0e401d180783e0b031040c0703292004040000500a49401c030054681000350315200c031484a255440d0341700c2e180902e54076240004007803540819a54441c0e807641100940050a496460040810f4840b01134031038070008000c2800e0590300c111404920315031204075200046107042c0600f001c01d490480401c0180210760303d8690000c0451508070020340114400d10520047d540d8800d00f031446400a640030a200707081200c03a040c511842d51614100c0780d04248103043c0049004100780710f0300c0b20018690410f2807640b001050000038000b0340080031070b00e280510204240307076480303070320132000e68810039140d5105610030400c0748005101c603140122004070104c00364010542000004110602c140d940b00c03000d540b1915420651750a00800c2d0307400240c00d000843c5480c0c070b4103503010140c1c000c002c461100c512107121480d01c02601030f012918064529001007101d01301c02d0344074840400d41c210007040000c41d864 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 442638399 1250 442637149 442637191
    0x90108010b100f0210051806040c030312060f1707031e0c0b0f03010e090304030c09020a02151005010c0503040e041a0702030702010903080f1927030b0403110f07060206 74
    0x501c1c5501105501415004a400e45d1400103000085c0a140041e440041d115158072810300032540503030301c900900b403040c03403540c10000d040f540c44000004e081d0340ba05008011200e45082c00070100c030307038802014503e2101000e4280c00c2a54030b41c0068103010b100c040d40603800c02d21881081c00c9601c140000104251252254040c40c0100d07024424215400c100522003040f42000c99548030160204880c03810361030382d44840311010554008491541c01207206101d554042c080f441e407034005000c0c1c901640c50143e1300c2202c0b00140d4421305051000095015051142c14411030700a030403840c0040c10769080c10702c0c0200c0080d6400b8129111059900d002c21400c52000c030803078030500d805035030381e10f811401d5455148080e845510050340300034081006c90522032030a400940c030212140c885d1400c0144454000800c07031801601e040c1d6448090f0801d10010f07041c41680c6070080d8140c076002048009283c6a40c1c40d021440c10f611200e84a00c40002508681c002100307845021005603e4130584a10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 442639649 1250 442638399 442638407
    0x904050d230f091201020f0a080610021f180c0303080106050c0309191e03150606020a0b100308031006031406010c03180b27090402011704020f090108010b10 69
    0x4110269107110400009141c018018082c26004800070300c104040c42050103500d003260300c03c5a01102288010900801c0c00da0040122540842c003a03407d610040300064000351610a00001c0b1051041d04021050034100d46510000317000d41d001310003200c010940d0400140040701c0703100c210001181c4100100c0c1580c4138105458480a03020020360520035448104808001896200001c40d00301d0b203000121124001840011105802d040000450031400c007100901c545440440b011818a2400c11602e54001040740d403080e00b01d8a120b05944030026000e04110450b84040c5c40c5001c040180440e10118200c41422503290f52000c02503440c044001040f41541100c545020802c1d0444003c0424003540320b50314078081110a8003022600c0341208030050b00540c003203141c101041106412104200500c1401c2190215600041c3d460701c2d600080c051095010054203c100c6400070404644171110140300419000301010b00310b44e145d12549009200210f8074134440c0c0e0034000211000c84c0a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 442640899 1250 442639649 442639697
    0x190201090b09010902031c262e17100903261302010503071205131406010302220e0d0f020d09080d0f0e1207050118120201030c030207020904050d 64
    0x1025001d031007c40204c0c3d200e100810032941900c1e06100c00c1d8184900d05800380c2c241e640c9a900031081032032150034010341d2480209035441100d0980740b0025682041c1c6810b00504030102ca03520310200550880704030f1618103050f11030001d18401820101c0010425400181241e100e000312500c00700f143c0c90540341c441c1a00d0054910b081081410a04d03031015512030001140d00c06010704044012010f5800750404441088517061820a8110f43c0c1800b004000d4811020400c492001081d081d410b40d0001192403002d6008408003040c03014140e4180c11454101c44800d00c81c1c1d10941d688145d0000000d07000764190091070f8010b011f00c541c040040e50007032051500362004a002032603c0e20020b13800303031003c813400b522074030501c40c0e0200720b120241e070b0f40040d0a5801c01c42d100500340c0716141c0b1002600841d0300c2c038a2007480700c00c500002d01801e00e44021050307049409103400700788042102c000303600a21030440041d402122020800c01800000070f5540e50705616951001c842344600d4001c400d074601 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 442642149 1250 442640899 442640903
    0xa170709032109060c03021c08010512060105150c121305040b090f040201030c030b1909060803040810020310090f0b130c020304030f020f0d0c0509060111060417190201090b090109 79
    0x43e204070188605032280d000754640b107200340101d0340482e18000c01c0c4a410700302000210001800300005000c80c0c2030160050805201140050400d035040c2000616080401ea85a00c41c1000204141101c00b00400001d05145820410035a071801035a070300e14000c0c25180541030089040031b0903100282000107015108280702c16101815840d168011009050050b42d180101601c0d94614403090395030801c10b0b541059100c80d4100100c0c94900e40206903880d0341d124107076136081800b04204c952400309004694001e49003006a4030341d01d107070800e00d01401d45e801001c4183e00d0003034440c29007511544401d001603000c540c01c00810000d91212001c3d201080581401a007052004000003016030b400c00300c105100400700d100140b800c9020039400000610207032141c81c101003040004d414801c41c02c0350020f8003841c0ca0803108980d8203425070b5462018100130030700c07144910308841c02c402460a41303005a204242c405100001030300c009020344041d00c001c1d0745030408c01000c01c0d0008414494400e09903 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 442643399 1250 442642149 442642157
    0x304020a060804081804021b06040c050a060c0305210703020c21090411120f0a0b0603010506121302060d0917040e0403050703020a05070f06200705060a1707090321 72
    0xe40780405c03e044440481c402c40d0704582c00f070050321701e0382e01004032200d001541040100302500d094208030000140300ea00580c01000921818080254048604014160942000ca87e200044003076802d403410083d603511080207118061041e02a49a0001c042001d80c000c111002003525501016402d0454400100001000c0224410a0510f90016408940c0c40d0b0444c038181041081c0c0e02040d034000f140c01c84c11490301c032000c10842d034032144141e481103030342511010304540c105400304034248600201c00f03845505240c000b400c08030303038170004101c5e07a075014182c0c90302d030020585004043c1c01401d000f00c66056845d103407404030101101c156000ca070244400150180c40d1030f14250b03001e41c00118141c0841c00380c608598007040e01004030038002e05003040c00c4d50f42c41c5d107000d0000300000801029500c10400d82c2c0c20100600c03000042d42c0b000d03940125071441d5158000300c401c1c1c82311600c8a149480040658042240e25500824072070226401980d042004a4440c4200c1c0c2c480c1091001742d1000c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 442644649 1250 442643399 442643407
    0xf06101409012a0308040b070206060f0906040917042105030d090c03060515090c0a1d120a0501050f070507170a0c081b010c0203040e01120501110f0304020a06080408 73
    0x358840c507010b0b048100c030301d0b06840030719240807081e0f000f010092038168003044000c01880100700c0b0401c0000e5001c102c03031024120034142040060320034000010400e118400c0c002c003040031680c4980c054007141d940881d05000703111411180101c0d507045441400c0c4a02c008812000c82200303034004140305107600c503001e145405280354002c8000e020310001982d141c5440c110200005010b4426207001d0300400010703054403102101001a450780080c0394240c0b645050140701c0400e90410381060501719240346035003d510008001c01c1000d01c1200208045124501c3d42109000065021500581c00a00604a15500e4041c103586920500c0401807401c042c2c0700c03c0d040a2160314002d01030503119032a00031201e03c04d540320400c003600481d03044484e4000c4011002ca00103004d11502d44160000c1c006141042d240c030450f807140110501c28210100010f049450800c0429840003050284481c03100b6101c220400324083c0035003080302c0803805420981000715034540680a582d01c00ca42c891141460 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 442645899 1250 442644649 442644667
    0x10150c0b01121a090f1f0b0d031d01050c030d020705060c07020109150c0204140f0604110403061d01021b0c0103020708040b0a0908071d0c030105030d08041104050f061014 75
    0x3d09401000580a40600c0000508002d01030000355220780d03e404034180920307800c079061000c84001c048158840c0c0c0d07020701d21400003900720b2941180704d9920301140d0031003c00301005036001d115150948166000006503015082e07220340c042c0036014024002c0310407aa40d415a00200341c41282006070200d0070406080207148603204922090301881c0c5424000580564003007016076070b18410380742410341840c0800205550b080c101950064040358148040340e0601c04a00540c4200c0c000038040e280c807405030802c1076000f60070036162880c41c50000c40d520100040b40078003040c2400c01c0075009028240042d04103611034002d440c9481e400c8000f0910303041c50303c400061103034448000034050011106000a06400c188030200082c00741d81c81c0c07401690b110482081110301d00070915200554180014405518001100c2070001c03d81d00305061a902d0314100302104000b5605540d91050400040000300e01a082d0918011401a1240c41c3c041c0c10b41a401e0b107882d00d88002c02240d4800a20800b85 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 442647149 1250 442645899 442645943
    0x142d0d060e010b340c090e0a02061c021314011d090135031308071d060130140f04030e0d1b030c0b0307080c0310150c0b0112 55
    0x283c56445030150030b00c1380400d510020340b19402d1110a0315113400c500d00c100000c0c1a18080d40101ca07032000060030707500d402c07580051102d0040c1032240303100401e02031072540e051039203038100d90a826588404d03083c80c5a440314468030703110441e00e01e1400074a0900a40c6008002081804240d0780300401c1c1c040f450f82420810814810540715410102e0300004901e0540c1d04005089440c10085c2000ba41d80e4a240405040d00417882c0e6006035805d500c40d40c01002248a21204110440800e00423003400d601c1d001c0048810103004086a07008040c10340005200032134240001a822980040030301c0f041409407030030191400c00b195a08a1600c00100040000b845007029a140b03080c02002403845803841e440e15101e07100f041e440e450411360703030007001e01c00d0082c00041b0704018010080441d20f0b5140420300101a090041c0258081d2103002c00403941c1c03820440c4600000d003c0050302016a8045d0a50040c0038841c0b07500e040e52106074000c00401c070104940301400c200d50b00b0141026010f580c2042500c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 442648399 1250 442647149 442647187
    0x3010b07080912280302060408030604200a090f0b0d0f0e03070303050105241e120403022103010b090607050a02090705071a0601142d0d060e010b 64
    0x240d144008100c581c60a95030540c920107a000a04000e000405135001112074100d51031035200506407113401020b00003903000691550099102081320780702e4882134003040c0a4030100c40c0c0e0015281102c222913180d80c007071030b0141032116010342c0c0744820542e998a83c00070304101c9001da00440307641000780ca41c0e8690706402000c61000d05030307000501c03540350082060844d000014103c0000342c42c0c034010402740c0b03080b0303c03050324087c0344140d82404a2848040e502039072003031420b0303401c1619501c007034000070140410903a51400311340e4980740007c0c40c00c1e10380291100544c8040618440301880c43d4100c504014090b2410303500e024160b1441c5c80440001c00459400200301103d6605c2090440b00050301c41903103140c0606900e40310307542c4074070702e0b031404800140480c401012041c2000c010403880b603900c48038030710038080302007000c60355070034210b14800c0042011002d440b041c4d41c070183c40a070781e80c50040040c00f80c0c1e6190301d820080107468451100c00c0000a10589000007000c0c00240c861010004c205 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 442649649 1250 442648399 442648403
    0x7120504020d021c05060f0c0324030d052502220e01020a0c050d1706090705120c0408010f06030f03030b0316031101110114180709050901020a030e0a0803010b07 71
    0x20b214200980d80080c00c01800000843c034240d035900c100c002040070800181d500320b02d000d64107901c0341c600300c0300001460100078103c640051042c00c004800a4509900058490001d015540c900318900da0140080d0300001d010603c03440000000d0311403601302d103249840c00e03030b00074845001004841c443e1a03035040c0e8500368042a903981d04405046071002d200034035500113140c442e06820b00c400d05048e401c1034803a40c001b403b4007024076401d6001c1e0428200d203d82c400e80498902810340c44041c0201c43e00e018008002241141000610040e624014040d00c12205500000e104113100c40c20402e042d28080d200051112101c81c0740f4a00080c0280c0059945a00c0902100e9a802e03040c680e0320300208061707105a41d12494280c556183e564001c140c40c1940c0d01e00340c000c1c4031151426085920300c1500078002d5012400c41072884003810340520201c0005c00c043c00050080e81880c0c0000c0b8000d500500003140420b15248061502200100d107098010f0b801c10300342400d40c0c0c0380084141c01c0e03510403981 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 442650899 1250 442649649 442649659
    0x20909030913020d1e0903030c091503020f120f040c08071a0a05090a0b0301030201030b0f010516050705031f050709060f030b040204150c02030c01020c0d060e0a0804081c080712050402 81
    0x202e0000895082c440c017100818600d008174151213542009801c840d910030a120400a10820501511610780c3e00d10850394814071b401a922064825040006c0c000d00302081012035401003880003080758140d8880c090742c01071803100312441e500c0316010750741c02c4c25100300781c9040b00c1c10301654140881c490107008a038007242030680c9443d000c080011a841c80c140c1280e00a150048014002c0d96031600c0380d41d096481c140c07404050064001c1c0082c0035030041c10b48c40c050003804000755004003c405e1080200400001d801c4500c3d002d0f02c0041500b101001240010f03005160100007440c161003480e291003252025180c4c000c801e004041d00300d002e0311000c170304942c00603020040001c54642e0320301e40d02c01c1500b040d42c41c000c01c00004d104242c06c02032103002c2c4038119440f44031000c510307507a0300b2890307034031aa400b4100140d80305003654a1414070302a9007014003038100c007041c000780360b020100340207a440309244804581c07003110701402d9404100948080000440c1e5402c0b083d00f103503a41c0e0016400c2130004207 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 442652149 1250 442650899 442650911
    0x6090f070621110a020d09050604050915100306180614060309121204121e0c020301090b0a052d0a05250e0a080a170a090819020909030913020d 63
    0x48403020b446030103070040103074440004e8444ca5654144480c4281e0741051522528007894080004c20743d01503401340702d00c620100b0000c81c2d01d005220800308040000603042c00c1401308400c81c0a0001c0c80b1038412080091085224840700402c2481788805443e41040700c03c05e141451002c1c02190f410040482006104500c0141d24802401004d41292a507020741004e1034a8185001c02d081618001250140601403028845500100310443d111515525100a41d00c1281c00060702410348410082c007602825020300040755881e8000da48a864007000103e9118810703508020041c000580465034440c54101003000d03184a40c00198200890000084a040000c1442d107812030381c403209200840e01c24110404181001c10154005040c0310000c0e1017000002d07100e6102c01d010709480d41c4212000001c0c034005060080035890003070040e20702100c9941411450211607000c806c207041c0d00c03580103080020302021340041158000744002d4044000040c000318284081e401030700301b0b4100c19072511 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 442653399 1250 442652149 442652207
    0x61615050411010e06030907060e011b06051e070504030204050703020910090801110c0a11060408060a02040801060b0711090405190f170f040e040206040b04120506090f0706 76
    0x3024a80c0928022001d4184021a280024150000a000450082d8410f00030030514500200d07007202191420b0610f080420840c000403205084d10703142800e92440402000401d02007654015446041c5031480d55180d541c3c514a01e400c0030f04226500710009004000a10040c200794001c2074000c40207090240c100074a00340002d007244000c1d1240d00c0060b403640c201304584402401010242c099500265140480d13004002e80c0311030010801411800c4283c202da03a0743d444283c201c80040400100796102801d000c0c02c1c90b00a9442403140e490990f0030524045148400c41049844155010402a00c0d0314281310920100350b4000b04255240d0041c0b500d5500b16040c00f600c5010300a01c105840e80312011b00d4038080d5604500600300c0e80d2607240174803200c01201041c200311020784401900080469450740700144480c0700380e030040e00c000b150204000074003007070f070300c404103a2179200c1c1c0252180c070341d60b6148142c1e0300d4040c000034a21a41c4103034010041d2601856008440034030b10f0681108040f011 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 442654649 1250 442653399 442653401
    0x30b0123090a020a08070f0e090c0d02030916090506010f180302040c12050f040201080403120f064707060914030c060106111e010e0d080a1109061615 66
    0x32280c0d6403810340c001414134052503105d00644c1c0c2c012860b0030480f4455102e00802400c000003564124025800e80300801c085507000c4056850b40c22086106664038a41a0303182c94881108040300b0b001a0344452011842140c1800741d9403184070180c0d241c10b0301e50380c84041200c007400a2071008500030303421007000c80540c680780600c1c142000c1d10340b45c01000b032800e0181e000445000a00184103140101c00340401030f0b9100c1400ea401941520304241460400c03020000144030402d28040030b540f4111002440c100107602d40d24100d500341c151a01c1007001c42c0e180c00900705d002c900c504044c0382e8a4110742420f101c0c081c05440660702803070000410354203550b103e6080310450a01c0881550010a80681c984030401949003d00741c10724040490014020103241d50740030307620340b800000007007086120001c40254048582903407058105e680045407043e02600720402951200101401c04034140034440440781100c9429901500061030b204540081115550803641d08036a109245101055100e1003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 442655899 1250 442654649 442654651
    0x30b0d020312041409040b0601050f160b040312021617070204050a09063c091515080712021c02060c01020d1404120e01090503010f05010e10030b012309 67
    0x8035900d45641c0f2810811250102120420010b100304a50010000021500e07202150045000e00f800d60720362403080f003038060b64041c0e6045140c51100950600781480790422120340540c0c0a41c50306011034660019400c26441031008403001c88400c0b02c5007000181d0700c41c200c07104071a01c504035982040160ba002a042d10015501c2e4090705444000314414090548100161030004c0410001c0d52855510300a400c950760306200075428900d00c407001022050354000104c0c040d4040c00005030114802e0000e801440b000c0700301004903c07003040221340380d080090580191104020010908505642003105406050740b0022070503004042c40360050321008080c0c12180c240000142c2c99a0b04212245c04540f24030080700b4125200304180404603003014500c0c0c440110720b02e0b109011030807035001640d840c101c5612594040d842c000d03070298506010361056058070400462031070b01c3c5e20307000890382000d20700c1d0001912500e8044010080c144415012000c0c1041c00010030050151000c0044c6881704 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 442657149 1250 442655899 442655923
    0x10e10020c07050609090a090f02040501080a0302010e2d0c120f190c050907090503121806190503091903050a260c09060c03030109090c091b030b0d0203 67
    0x50041104001001c1c1404100701800050b200d050401d0502800a08a004080c3c07000d905035a480c8210b405100c1c061403020f1072590060000d209959407900c05035030b49c46142d0004d9005510b0310551115844010071852032840d42510344c03004c0481001036611448440f55400f0b8030511a00c107500c0c140b9140c098bc0e00f240682007902a008030032140344c0e42070500c0420801c1c9891072104620000000f06000c0b20303c82602c10030740e200c0c09186e444d450281e0705241d8603088280d00d03114008a05840404003002801c5200b800001d0f01c00f525002424000d03a40100c0440001014640036000066442a40916486803268088a03496800c0b58080701c0c00d84408403040c0d0005500103098235180e900402440503e1120070316411080f00c0158051a400740c01910122030110005104401c40c0c0e900c1d41543c2c503481001c0c0c15a0365a594400030000284030850080310328000c0c2c028000381903601489010410400e40c8041d2a16401d00740d0124001d0240c10300c1d6070390100c800f010f25005030301c0420903000104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 442658399 1250 442657149 442657151
    0x2030a050606130507020303041509060f0f0c080f0f130b0108031b0604020f091f140108010503030a0804020906130203040c060806060c0304090c0e061903050a06031112010e10 77
    0x2c100034040c00704042c090080801d02d5410041404249940002140d601507000340e4491801d1400710f034094050104803801814850a1145041212450b90301160341020b07050020805507102d8001968481c00c102ca01d5803d00d15802c00007401d01040224040e03200000c40a2003000e22030325034661480420a8001d0b0300340d0750003ca000002000c0781040f5501310401940144040d10700790340090007000d02c0c850712034010072100c400b003410403a00248420400400703c2c41e600c0a01d40312003942140d002d00d2001140010307108030001403a0300f00402110003403c601d030354600c01550f40e81c0a001941ca0080d05541e0000c3c020740404041b006144051401513225846040d049864000000c0190501400f05480f4440c2081070850301140041154111003c4200114000440d44016140c0c420816481c41e00607100103407144072a00030355103030300c8a640c154804102c0c544a9071220400c40d4001d02000300019441d4000d0403980c03601e030f144403501103c0e100010513509003503c0740604042505d00024465 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 442659649 1250 442658399 442658401
    0x1305010e030414010315120212010f060b070605060d0b0a020a09032019060207030b0604060f03030206041e1212092f0409030206010b0705070305030f041409040b0106031802030a0506 80
    0x2c0e41e4940181340206c0a0800c08000c51820103e10100b00d40c40518002d21440d04032441109a5000b0b4200f0070b40144140781c10480180d541c9600e5000341e220550454030316180100250103490300c41c130320f0008182c11070b0081e1840d40d52118200000e511150089081c08035089001000540d0b00018110343d052411064211103160b600740000d5282428420540d060450824400541d000840d00d08494016240c000261555000302d00140240d400000000e0302c1a180031040c15000522940111301c1450101d84041c00c8180074165440d100c0c10017006c40c541c0750290040c02e8402c0e0113101001c0c40ca07070350004200c42c081c1e890000c0c091404a0f0903a216964a021a18001d48400000010401030b5000d2002d070f0601d9800948800c414065407000f0350001c501402484020031040303000d5544041140da8614010301317000350070780052142c51a01ca8105018136a9400c0107400140681d51213004000700f0703424100250b002d040d501c501609007030000d01c4207030003507501000a50700550243c4060092 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 442660899 1250 442659649 442659689
    0x3130c0e0c0c0613120f2703051902030c01050702040b121e120301031b35030a08150d0507090b030609030304050c0904060f0c18050d05061305010e0304 67
    0x2040801442081c0c005184c400c0f11001c54080c0300305040407240303072400034282c251141d0140c40c0900c4001d801040d07110603036006411540440c11200660340034004495510b962072410310009480000d000307415400100000f0441d5000d030780501425440104082020503001c0b0120b445055440281b00c0300e9403000010b0007022032000e0080c590048100301900c25031907003000c0700e0700f94481888000d019400014210107030151091b210030207071040c5400c4540008410198111420054402c02032501078106642407150340001201d2007201c3c00d03191940c5030b40e100c0c16030308170309001454016045488002c2c2c00001450602c544400b0b044201c1001825041160502d0314140000740b41c0c2d82c09034410000e2201042c00000c1444086c0c1c4100d41310340b031039070701e0745040006461302c030f003800c982107041c14104010030b41c002c1550f240900318541c40844c0c059a030300400c5412000c90101505c544c0140011640c0c504112004242841c040d00000c00c6100a101006280d54030a07403214880504840034199 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 442662149 1250 442660899 442660903
    0x3040c050a060e0607020f0604080a080a0305131a09120c0f07060315030f030c060203040b090c01050301062325060605030102030103081602121c140307020303130c0e0c0c 75
    0x7025101c02e02e450f141480022011a20600c203002019100746d070301149400c910380e100400c9401900e260020760340c400e5a41d10b008000c07074001c46069400300303040c140080d03180d01c40c04d02100442138101c0d01f4590303040302c200c0002c5040c0901a141c0509030281c6d04041003103009460040100130100d500510484e03400890050070520315800c51010141007a516800030395a003000001030b01c2d080f812190780040c561074203403140080500c00906407070011040006114641c40558030503403121080e00d0242807030341e004642c107120034000c110104021440c101102032910001854146401d00c9452825007028101104a500b0080c4402103901c82d043c10000c2000d640920802481c05800960955055030b403001c880b4000c9403202e80e100d211008440c0299a28440911102c2d031404c016251001c10458101002e180c01500c1d401c00b150905201da032480301074030200e902c150fa1980c0034608503151071441c00064521000d0507500003100d020041400040d00c8a00741c081d60102c44103d950380c581141082c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 442663399 1250 442662149 442662169
    0x1512161203021911150d1d01051b190c021e100216060e010c02040507090815060901031103030403080301060f09050d11040e0a0618052a0607060b040203040c05 70
    0x82e00c1c14408000700080c022042c284c810708000c0394004058522600c3e451356500800710440b9a441c00c1c5903010240c60b2110680100158518000340316554239046144040d503402c0c3c07001c610b190400c109007d418a03109070480c0e41d070f8403a03141081950354107030000340601d18980c00d049400c0d40c182d42d45101381d24201035842801c00080c00585150050745c40441c410119510611080c0020882650b002e41e00c03c54042140c540d0041040111f03040000700182125010700810780c0354400d81400c00c4078100e10366442031103006d004001c01441d07800c1d9030351011407642c00742d42c65406100074040800081d0300c08002d580a040c29503a941d014181c06400200604003a600031405041e00d910b4807000300700c411804920308901610041203988060007018504a002000680014501610304101d10341200720082c081c0e01450440710301c0c100b075601a0880504e1308401000d0b2904405031410a070600d0006000c03140d001d000300040149100c008103090340c0c002c440440d1144ca500f00f042c002407901b10b2501c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 442664649 1250 442663399 442663423
    0xb0d0c030c1806120b1003050906010506070f021005090907020109030f05040806240d0c03060f050601020613060216030c0c090e031605010b0607030504030506060306151216120302 79
    0x1080d80c08009404000b144000d019078410003008000074071124003260000e10481e031000c2c1a040c0c20804c1d186c0700034020003050314007217581d01a45c1d00005035450041e0076101072580203106000c03181c00f2a401c00c6001c912501d400b0b428403000f800061111b580b40000e451045610b0303000811000c1041c54024601d007503212600c0f0230303c881444248403105000907442e41c1302c0d10101503107559601150400c1072409803c0e6280e5803100a26180c1c10412406610490840f40310791001e00c001d00c1c0440c0d014082c0d0714115201c07070041e8030210008100802207245802c016005030f60041c500030710102024130f00c14000c601980890768403031a50302049003254220000f020141030802210719100d01c0c0039281d10505404440001c1c1e24040c00e07003448801e40c42107500007030003032640da80c43c105454082c101d50001e12040c1c0b681e0003640300164050402180b040d101e1107130b145c04a6050b0601904000403208144000d107528414003404070085100014407d02500c0c92042c010301a210f1490001d2138822003480c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 442665899 1250 442664649 442664657
    0x905010e010906051e0313121b0b090a02040f0e100b03061311040207110907020d02060705070516060305062103040b0f0c070602030306040f09080a030203190c0504060305010602031c0f060b0d0c030c 87
    0x803000e803401c100c0d00212064ad024544c1c4249803a2030f03c45902d403078940040a5405490003a0303030341c501080c541c00807440e905040240c8812541000590048503112031540d90560811000110f1000198181c04001c40c4a0100807805040ca01c02007800c80e0803074a011200244030700708049003441c2030515a54404128402421506e101c0b01000391210000350441c42805000b2540404010007440740e0080040200501e08000341c0d50030004000c0d0005460071801890401207003144081500442015080b80000035850075203019401a45030788001c010452640307003804915a03040040c4072407002460a07a0045403039083c00740400048070142285010154078200980d03000400b042c0646040480600b001a269641c1d1240900700315010500903440c603203000304c20034402d40c10a010f801a81c0c083d640030410384c3e80380c2100303070399a21580316000304d11034031400103003c08440303500008040744861038003140d1140c0d00c4400c000e054100040300364140f6150054902001d41c1445029210146490 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 442667149 1250 442665899 442665917
    0x30c090216140c03010509010b09010e2401030f02031603050a0216020d03020102041203171b37110c01090e0a0b030c0909030a0905010e010906051e031312 68
    0x4081403001403000070001c0380000750b00019803805001c54503060a000c3d00901a80c540003410038000c040110780d01c2d01c600e4280c0004210315031009801445030440082240712180904599070701c544030f07150118101a00c4d0301e0560002c41c1c00f400a18080d40c000705070403c8000142c0009025120014903040c103240c810700281d00350a03500c0342c00440458055540752582505420101d02a100b583c025608a0000c61090001c1541c41000e40c500c0c486401004429500c41e200007172100304005410326600039003840582c00b00007401e070308802f070315610720211903030503c1c81c2040c5860004008074090100c4c0744001c178050004c005000030328020300c0074070b0280d80090610f01d0012204102400c0c2c810182d0751900d0300484c81e20104086214200001c00307407989450aa0b02e038558980c00080008000341560200040310b5001c0d01c03a01c40c2550050315001c80407400d19201f250150800c1c5d9041c40480207051015250385034200065000d0544000c044000346804d050005c065548031401504001c4429 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 442668399 1250 442667149 442667167
    0x40506030c2202070219210309050f0d0c1e0506040602060106140c0307120f0c020619050f07030c030906050301181805100501050103180807140304120c030c0902 71
    0x81d03400c40c0304450704202c00000c8503803101c0d14000d000b260390080d004080e21229120001e50117082c00c00311600c4240701c070341c00c40f06034220f03080e0b09098801c02070100303216400a110030f213450400348c0007049000c0d10003400c110254441d00031301c002c1940315100f80c012060f4440303410122a0710410162900f40d41180c54179250a00c001d50300c581c144507080421441d03034000b8103010305d49012182501540c40c22280c4034140740c203151741071038662070221011400046000c3c00c0d00d801807284009442e00117002600304000314074002069207081c10300d001003140400180c07529180d020094500c42e80a5a2031408085507480d028141080541000e01800000c3c001004510507221290b1411410352602107800e000c1152840440007040800400030b00809102c12032880880c0d0003107048481c00d80e801c1c00448402c1d0340e000c001441c1e501000e031401100304000004550144060100d01e5100011a850595105200e058002107180b0440b00c29021400400074405002012000b40a00d0030085103421491 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 442669649 1250 442668399 442668409
    0xf090620040305100b060d050109020301050a08010c121d06040b010911040e010303030b010e040507030e06150d110d0b0a0219090501050d150b0f03100b1207080c0405100509040506030c 81
    0x2100900543d4171206030f40321946500081da500000c0b052428880ca58441001c90b000c5d4009025080c06802242c100241c042414022405805100d0300d614150b00507008200010b04a60803040010450419400c3d26103d8200085403049000340210f400d0743d41003900504c16200e50a4680000610500081c001251003d24a9044075450f00b030000300b0390000310069824444002034543e10902c0c0c1000c0060460b09504002e0381080c00800ba00c001d80e46a10720641c8141042c44680e070826038118507000010341c15000d0803642c86000f4412000300960740e651184c0d44a0455024003069000b03c0c0c040e00c0c0084c1d500604c064000755003408080c13a824000020901c4c0580040c00a541d0b40360142e00c80c07040381d052803500181c070004100a0b070324101c194050405a00959414081c0ea0700c120000423160524002ea40d41c48000881c01007003910f41c40e20844580c0006008000c07010020031002610f41d0b50310810294500e05601c0c0d0548504450080104a55001700440e001e601f080b101001030756a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 442670899 1250 442669649 442669663
    0x50402010f080712020a0305070e031902090c0f0a02100510030b070c060f0e071712091003060b0a03060608070c171312050303091006080703080d0f090620040305 71
    0x1c0e440d00c046603680307040084860070480781a2100c041d02c0000c0d2841710700e91540110b03120711225110f0002041ea5401416580c04a2100c1c02034188032203035442d03006261180c0145d42000b4440d220303a0414107201d403040c60035845440488050707485084140b600320018051103500024100c51018294690745038102091001003005081141134181d5204020080e0b00c0b4202540c0307804000c03c48001070203c001e42e942c07500d0091100e42c0b2a4a0b49a80501000040740d1407610740281ca042e090100c0c81d010b00800042d41501c0a06051b00c410010070108000c601926080e400c41d5804104203103410009494050083c0007030303081107000541d54002c520180b464440c0d840103240700d5943d80d021204522040b4015030810142040d10410340c1d018014000040c50158149105a500801074003507c9070031540320303120b00301c2c894201d02c1c8100003254800c4003618410041c3c00c0c0101e400196a2107200464403810b030100c4141d951a6245031508100506020b80e5040281083d842e04d41580c90315540c40e14 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 442672149 1250 442670899 442670927
    0x40212060907121401050702101524020a08360f060a0c05070801020a0305100807030f02060702041506020d020a020607021c0b0405010209030610291c0b030f0105040201 74
    0xf090881440401111140740706a21108200070846400c00c0d081c002d4544428510080403d818013802007841c8c000c0880420440e11081083ca403d00810501d00c581c98a1040c4c5120540c000d04544002003180d03080181044040300242c00070100d48500d072400c0d40c0f1004080c5150304500046000f08580b990429420800c00490306552280003501c0c0449461071070040003042c81c090403100141e030400c1500944200c290a0b01c090140d5a104030211203130600601c51a4180e6101070b904201085006c0e00c00c0a2450000e01640d1501001c0d0300420b003501c80166545440c40203400d01001400e6040c002c01141070014405440d6941241d00054214001d41b68041c0c4540c800003003034140f501e40c1640c0003903140d501542412480c505400c1182c001e401c040c2c4541c0c000d00650b00061901880728890100b65003e840d640790040c4040c0c4200c3c00c0d51668103440c01f0043d002000083c41c032842c0c4080b584c0300c0360b50007140030845102384418581000c3d045124401c3c5a8184000d010060b80c0010040f10008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 442673399 1250 442672149 442672169
    0x507051e070f0801020c0f0d02031b070f060518010315050906060c0f15100b2a120c011a10050d0b0a030f0203060709060e061c060608040212060907 65
    0x4060603a0090600310076502c03512440c10500d50014a480064024090400301d01040c4c3e2070281ca51901c1c5503e0b02032001d210401600208208071030014448109600546d5060456600d0341d159019101003000e66002100071410100d00411440e540d00c0f040000e100342071a0a10a401d001e048103441c100300c03802210320600131500041c0440c0c40301c0301540c02c19040360044409802c08088110740b100400181d44030307016100b00002d9844202d2004071011111849001454500e080300e103410b0807440d501510310181449030301061441c200300305181c5441804103215644040d0380018a0844000740c14031000000010200175081c0d443d0300c00a070003080c19050003036032600c94050440c000c1c0b4070785030340c90340c041943c44d00031040c40500500b466800380300340c04070340060701c1c2c0d014203641e140714901c6940001610b4020826140c104500030b07200e03030004400c0f0401e4074815071600a054030a1a0445c07000100440108004d51a11100859088a915010f0003841c02c1074242d041c0c5a00060140b48099 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 442674649 1250 442673399 442673443
    0x3170702010615051803070303080f010602030f0a050705190606060f03110d091a0a06030204140f0a1d0a1104050c0f04050603040f0f0606080d0302040e15030a0b0106030219050705 79
    0x441e820510091740e00304002d0030380c0d00403601c0c0d24000d040c00409031051400091104004aa0140000102e40c1d20845140c0c0060a1054211040751581d1007180c04481c140590240d039011890401240d04d41d25100321300c082001402e2490080c602032001404404040c104000d00c0c1c000e2540c88201c3d02c0b1503d1803000070a1103220340c145034890082c00c145030710350603002d036041003a1585603038072a40030b4074807c503000e000803078156035210714829040e034501040d441c6c03290204440f1b84a56104040b6981158000140384400440d0281403002c10001511440c07881c1210760240d10342445100c0d444006100440d01b407048400c5001e1642c082c6020f024050080000442c0030f105025002c0207800fa0b002d140b03202c0c0a101446e109016205502c1640d00314070074a2461020035005e4002c2d6000c0d500c4a20103240b2a0780ca810100d0400104c8101d4950540140124000811311120080d030190545480169640c91010b48411035481c058860104111003400b06900041d40440d0402101c19007460703223001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 442675899 1250 442674649 442674667
    0x130e190c09050c0c06070203070201120c120905330112080304080d0207080c0109020f010908030702060708090a08060108330907150c11120a020112180317070201061505 74
    0xb8601c0b604d03411081c00e00c1007a0402952a50000051400303501c00e980d40d055504900e0040f10079218140c0c00c0c4408600b03140c0c829030700d80241d94410340c03506d4024000c0350b40e0b1040e1280540b01042d00d00804003c01c941091000c0320200030042041e00401d0324200204c0c4610032030701c50391881d020181c0010440b800001d0408941041a01550b11041e00716840c0350b030300c1445092150092500200c01c0f070217940d0150005c04a076010b400c50004460b282d102a40c03800c031441e400c00040b5072000a003125045800c1c05441640d803542e240c0c14010744946002410a54104010b46140001c1980d00c400d14206440003480345166510020030603100d40070b1080300940700d100c0083e0404032581c004821907510000034030160b0364040f400300045401002c688007140000c10a11280030f00801c0b01c0100b95001e005804010f5200c0e605010741c80c00e0305800003a4480342150103000708820b6031401c0e00040c2c401401108031602030440a900210580002c04ca6540340040f2070502070100c4001005201d80440c0d102c071 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 442677149 1250 442675899 442675921
    0x1209030203010b060703021c090e0a05090d08060105090d080d050c13090902030c0103051914060f0102070e06010c0206070c091b03090b0f0a02040801020d200c1b0d02130e190c0905 79
    0x82c10b10f86020600c3c0b854140d0502f801444200c03200c0c0c00d14401d071905207040368000c000326409200103030358662500320711005000440c42400c2041b074020760208640b840d1031985d445154081c007041c40e20030f0765940d07282c0b0700d0050581d03140c0c024990031031070440c0000040e0380c0003079407083c1c0102c00c0c2000f241698a40480071007841002840710001420461103a91107500489414440c040403910720300c03001b10440c0126950030240c000ea0f4050b2542c4804039034298040c00395000340c0d51000341003625121031559101c220040c1c9078480440c82c3e880e1080f03032044d10000380b401640045503103400c005480c01d50715406803800303001d0141c680c07010514000c02d0145d0100c0d01100c0103481d030b440095554103155600003008010204950015242001c40c40507006000d808031103505c040c1c00d001300300e0952a0131940c8201036196980d0766003e0150119503005071540c12408400c002c0c0c6500020321103842d035941c1c1d03081080000300d280704c14036080d0900e000980c50004d240140c401c4040001565926241811 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 442678399 1250 442677149 442677167
    0x4060e1c02041a060c010605010f110303150d0816020306070c050c0f12070618080102030103170f130308120f190203040206070203070b0c010e010b100302070f1209030203010b060703021c 82
    0x84e410060005601c100d43d0310540118003210000c1c2d84a01c042c00c10b90382d080300e1460348200d83c12002e800400100d0b00c03451100301c038648400380041c080581050b075543c403110158000521200701030271f030604400c25450203000480d17000c51181400203864410340c0c1c0f0329450301c0c0b0607030580f4031a040c200103450858407820700c1041e80d544a4000c43d10380c16220b040c0540b1008000500410803c04113602064104041c000d8904980e0300c01150b41500006140c2c40d400e039001348641c0c0310311250500400792900025142c0500543c02000d0381962586008404d42c032401005100800d0546140140030305803501600d00a4083e0040a0058403511244000383c000e2044820283d85072141400105001c00e102e401007a5204101008110400080111500342c0304102e141d00d0b4003030307040760380e09058900940060600034440c0c45050083c0d0b6071556150306001510b00001e0000b102c2800610441c2001d100700c280da20003c507411030a0000035a0001d641d0345020710310345802040380036400703281030041c0404c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 442679649 1250 442678399 442678451
    0x1a070528170a020912030f030402091504140603010e0a020105161104061412191101050d110d0e010603050d03111902010f052404110c01020c0304060e1c0204 69
    0x212030603007026400e940203034010b132926502c11400824030310503d100000c2200c04c0984111310380c42c1140d0f1503808011000380001c1c492104041030b0410b00d581fa039036500c0b80344c180540070b0b0352210032802d10409060031503401c9000e182880d03000b99510320260381c10405441c07540c2d05180b0341402041e020301d001098032204014407034110f4240381d0085551008a0f00c0b954492005440d03d0000b21a2030703458036a2510743c400e0303600001543e14510800304044401d01360354114103042080c40c29001c4107010007120038804512110b49004100c088502c46503014200400456100138010f00d030440c1c50395034450302e0200c0700ca4281030b030710001c00348030041007425074410950756100e00031200810500039000c2d0009216060800d441c110001c0e010164414600a81044078111040303114816800e05c030040c222001c0c0345800c1802404030404600f800d00082060503008009103071500d00d019409000403032818031885c4a2413000c00148865001504105009601120081466a0250140003c1d03110003925 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 442680899 1250 442679649 442679687
    0x60f15040908070620070f080f25050606040218060705010b100201090201030605040c0c0210050415020c03060f0108060a1113120506010e090a0311191a070528 70
    0x8460b0600c12070303520085150850f04030b0f0107030ba0417510601c0103182c032038030b60b00510001004004d034010a2042c070140150b072510046651034240c024090325030f02a1201d14010300c00b0b0368417001c142082030900c10141c0001d8191741c15030615608040300c100300044d00c06064000d410124203107092003025040907400040180507403516415000000340a4441284281e01203400c2440008a40c00e00d0300c69860342c01d0b510380d40c100c01d5180035420040078080390324204007003000c203000204040303501044012212506800415a80300044181420101c00a10200100c0605001004130f44404074000350300c103c8a1100217202644640b0924041c09500d8030340c0343c07400b0724090104c2d80c2c03130310750381e00c5844207018800310f0b2010380c0d98a6031101030000c02c0347c1c0882145c0146001e940000e00030142c4490181d9040203548070001c0c0d9603240c00c044102c1400c02d80352250302100c06403000022034009038101d015850828909030034100000580481e50786900d00007044840411355081c8039184c510310794100703480303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 442682149 1250 442680899 442680907
    0x12041a04080d0606090e01090b150a020a0510020c120a05040f0e09011b0e04090614040602120a050709062a060b2b0f030210051608010503060f15040908 67
    0x1080c0030705800c5110000001880c0c4400801c00c50b00480b600e2080b036400c021298001d0b8200450300d0040e0a19040e142c2d04814944071050211554201070144079000d9801029a9059800c100f03151801003408000c600c0c1c0304011942c4800c2d40407480c09004140c0c1081103503a42040d0004481c45e02c44c2e54040c0043d40141080454540000303403074540510f903424000d00034007840751070054500f100d0350114004034a2452a140c0345040c9508000c400034007441000560f140402d1903080329180842d03046401c554005203031100301d5051410260060020701c4104028549120098509003403401040d0500c80c0f414010112621021280a204000d007541080a030307a0071b01d0004080e024526101d44290300c05005a40b402d00046011540651101000c0d0403440642d121800000d170740c00001d40460241821456100a15006850040343d0b0805da2020040007203400070310720001030b0060b61080d0041010f2010748007014101c070b43c001e1b03440c04114505440c15400600201030100004100c104041 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 442683399 1250 442682149 442682153
    0x7030504020d2108091c0f0e040203041b0b03041106070c080a03080103060f111b010603050303040f050d0c08180415080307060b090613020d0617030a0207140612041a04 74
    0x80445921040c61385030001941c44045041d0f4031466866500e03a0049004282403403000c0c4940c00c0c10b0304404417414070008000c80940468181e920031501501c44926111b0381011520100a00302d00800030003214500b1410b10745c1d10b181104603190700c954426800820314034184402010b4080042c41c100c802c40300d0072001454003170942c450034030040d96132524003008082c101c0380302e000c0c11205030708100c0a1031502e010b1280261039080c502c41807600640da100300c0440040c20400003140268001c0325040042069458801c2c54681481780c580100110900207000003030400d0306a0b2144500550f164048840c0b01c1c0c0440c000b0041c0c1200c0208005d000381d03000600001c040700030030406009030001e004410240c0d080c0851240142c45480d0044c03484444070b400d405580d4041e0200e10004400840d60603654001200c8100884002c402603820004d00d031103005404008020090140c9101084d03d210320000050040c0207940714480d9100120303002604022207002d229001d02c0c1520f40f0f51815003494 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 442684649 1250 442683399 442683443
    0x50720060604050903041409190606021c051e0c1f02070b0a0c02030913060e0115122c01090f06020a081305060a0f1514030706030203090607030504020d 67
    0x1941c801c0c0c002c0e0b01d4180428410b910210031902904e2803050800a80c160140c103005030081e0040c201c00c43d002c0d40d0300f0b408058011600407500204086c0d4010300f1080f10700d1864075450031000c020b80c4240101003111000d211424045001c0f4200f20840b07003621000b40444075418200307081404c13104a005a203140210742d10582c042c0c004140225500070b07030780d03440c50550300031903440350904005031307000b40041d500c2460000168038000704080d0300412510b03510010043c5504003a088161034016495810150300d5206100807440d030000070003840508050302c810101050042c075484003440442d44c01c255001000d4000000496100d10038016800003403c1807070082d00704402d07020000c2c3c1c01174049060241c90301e11045842c1c0e0000c01500441d1078108a50005003050300c800c240064a541705240401807524166006081c411800101004614101410081950801018148144184206040005009540520541400203154546000046070410002401090101d00e0034098040d5801 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 442685899 1250 442684649 442684651
    0x70f0b07050d060e01030503040306181a0106141c020f070c0f0e0603060f0a1a090405010e07081911030111030a06051c020303090d03050f04080c0a1706070305072006 73
    0x4442c000304000c54490300624500d00e4284006040e80e4400c0c40148003050250b48018051200440f030056840d4081d942d48000444540d1445040c0001d8401040159086810415903144041c0f0480c038100c510a108e482d52a101594181d4407940440d01707030503900c402d40842e02601d03000400c0b01d55042e5074050821a0005c280500c202e40c0c502e01c8080381550030f000031282d0040021320070511840e940c000030680140301000c50494a0b2082c14030207541610388450a602032070048001088030b655286c0c0007454914603030b000c06a10341c07204264000b541d8201007408244c0e5400300b4443e001000c60b6001a0141480d0440c9010072200001800105092603020340115107007502d4508101004c0114000b02c04403603070020703405800400000131240340031860140c43e60702c2800c0140c184095140045290703000b680103180a03138000c03650084103141c41100700005000310916540d0b501c200d40880c1e0b840d014080e1140701416240c1c001720b0505030003003c0c4a0b00c041c400308107540800051103580780d81c50314 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 442687149 1250 442685899 442685917
    0x110102030d060b0d15060203030106140405090103031205011502030a0810090c1205060105090603060906120618010e0a020604061101020d020a090303030b010305061c03020a050f07210b010605070f0b0705 89
    0x407822111802170391510300c0160031101d803900607601396840c00c0c509840782c1c00700586110194030200030202c2d03242da581000c40d002e107020360b0390b4981c0a80340300e1880d0104c60303045e000307001e480303544c41d00c050911640003040b00c04003545840c0c03e508584405c1d2a064841d6095041001340600f01800a41e041e64070821488070f8106036002406070741c507003100645440c4240900f850700302604000288041c182003c3e029001000940101ea03404588029681004070548000305448150104070311044401d000d50a0710038076502c003030036034202c8c950b001403024840e03441450140104143d50744001c060a40c1561100da0101806640e9951042401002c848071030104902081ca0400c0070846544a48240340c410740e0041c02d404c20862002e00d984d542140c1d1090110300b144100400703000014414405030540710f40d414001c2c02d400b400d011412011b16203840c1c9012404001140090100e0440c074100c82c1107881d82c1c1402c9075074800d40d05000c06099807203c0040c02c54460b02e070620851541c0a401881c81c49 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 442688399 1250 442687149 442687151
    0x120e0111090114040e0402010e030a0b150321070b0405070314010f0617150606090a0e01030317040b220b0403080601030f0b06300a0b030d0801060c110102030d060b0d 73
    0x2c140f41c0a220303501881c02281e4400c400e841c001801035010307952060202030028101d0b110043c00d0f076925040c3c01300c110341c0640c003071030403140304000d5080421011203085840c0100300e03d040c2d0075502a50960280340c001801c04e40b000e4004c50180502030103102c001c0c0d40c10070801d0016400c078009240c040c005da82c80b08815185480800502b80642a034100c0115041c90040e2042c4030414111140914001d00a43d6001c4c2c420000b803000703075842c410007a00500b01e88883c1d1200350316500740580340303032446454070b03115042d81c05c01c100010b4400100180e001c400c000300c541c605410201e81e05003403100100014900c10705401844141a040f0210761701c1203009030b13410f20895504000600945081484c05604100140860030007001a0707022070161070358000c0300020050140e000005810b2064803801c18407640c941c840c44084c1400c1c03201b14a02d500e1810300c92590f51421000400c42110443c000d044c0700c1c203172811040b0b268400c1c000c460f6280346070300040c440981c0350764203008503502240e10800e807e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 442689649 1250 442688399 442688417
    0x60609060d1515170c130e0709140f04020109091a060c030c0708160314101e061d070807110601090b0a230910090203010b0a08090106080706120e01110901 68
    0x14990142d48180e01d000120080c0c4801105e0700d06001c2c107000d061044070100303500c2e5035201949500400c19400141190400403c02c0852044840d4170000d024089166107640300c0100800f43c1d800000060890f00318403000990860000c1c0d4208007c6000078604da40280c001800c030380f540c6070000141c03164503417000a8543d01503564100554805c40d910301c030b2100490102040000c40c0000c0a0410380400850a0799410340101c0109070441304207580b00285200074000c1b000706101d11784108005400c980e801c1a00d81c0104110308051110010326117070403c09031800003151180301d1010014800107040032a000c03561503242c48000350460050141c003038a40c201001504082d000c0d820702e00c14a902c082c607206d02d0210014000001c03001031100b20003111252002802c0681840118000c010403c0541d4071841212401001500007404204c08d42e814090103004241d4003107103d0b0105d03410340c14070f003070070043d00c034031701c5018041d40181600c50b07529140c560070f84906078400070401208241c0c0c4a104c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 442690899 1250 442689649 442689659
    0x715030b090a061a0c010e0703051f0b010903021c0b04060203091513030c170a03020d0e0102130b210f01050f01110d141213050d020c03060609060d1515 67
    0x40f0f07000c2c4c0c440d403d0152208040440509094002890841803450020807030300c080c0b00d00da81c50b01c40f40c5e0f0b02c11146c59000031401006000a41220a06141400000d000202122000038400b0f111804040c1c4140581003d00e40c07801c000b882203580003a4413445240e50b034071782030805000a40040f1500c10103801150403c40b0541541c0f113150303208162086c100540341d07040b600d00300c99581e1090011200c60a01c42c8071690350385601c60150070740e0015079901603074031641b003180300042d200e61b0a03000030706a0051120fa404180030490f58020f179620a8600c41e1240211001141c010540008404848070040c003440703001c0034010301460503140b040d2541004041003c004407101100000c1d001c085800900401c89240d1050301404003200d0907010f00c1d030402200c00071015502000390b48040c200c0164244920400500b0b00c200e1070802a140064620b40c1c007000007203900c4090003890644100d014800041413650382410034110140c1110f00c1c2081100340b40300c0031000301001c030103428003010903540c0010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 442692149 1250 442690899 442690901
    0x9050105090604090b041e09330b0103110a090905011a0d020307030b0604080607120204080712050307061401030308090d05160525030303050c040b03070f020715030b090a 75
    0x220728440030701000c0c6440d24029464000340158000070307510545601070860036a54580c21381e42014503d2000003048803c62424200000003507908407a4210043c0a100201340e0008081e11740403140b0f03c0200e403d0b660200101c009183d083c24031140003101140801207581e01c0030200c0196a454a001c10641e621403000c40640d00e1124107554a40f90200b0a040320340c90b241c4c0245410507203070f00300841e6022950001a0003078010760030802c0151b210000704100c69921185485031802d81600131031a060401c01c00e940c480c06075000b2001c19600040c1c0c60400c0203000c0048465140d00a4010030034250190144903480b0821310003580020881c0000c101030010100c0c40d8244d4101e10344406151904084864014900400b03050b203950140c3d002800080802c0c100502001c0044441666814114500501215005400341c00798800c00c1c030045c0480d5041908403500300310a8204034164810018040b40b5020341900444010403216070040d030b030190181c00c029541c2c2d80c111501d10180e075812466030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 442693399 1250 442692149 442692157
    0x50603011220032a06030114042a0e0f1314010602030a0813060207150204051203040305060c16050f0309100f020607140403020d0b040302010c0246030f09050105 71
    0x195242e00042e105079001e20070305661540810860310050801c0400c100000c0076030701b09070703c00f41c4250b806a519038010700e01886440d0900c1e04c43c04035203020104208180081d20328015900301400541d40c0e481c1c05130390b0360311961075110710007e2075422104030070000b42c0041c1c04201900200b15080307000100f4040e0012085d070f200c4a4080da1109202d40e2403180d048001c551000c400c5d502c66900304855400300318500c40c400394284290f000980d4582c50801070040d2140030703000c0c14105810500013403001900218585401000300140c0325256494960350000540c50040020141c0c422203404103080348011002d03203601032003110304004039a00b507417060714088400101900144c102e1b0002420350350040450100315041c400056080c1900e1f135020801ba070b4030390141540c02203d40e60412040641c24041c2c080f000c002803000d4a0420003a03010140c900030a0f0b041c2c82000349800c9195004585111080076010207684490b1151a8007801c0103841c0350300c05080d460000b003034140049000d500840c215 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 442694649 1250 442693399 442693463
    0x3050f0f15070c140703110f090103080c03120103140d0504060f0c03020f030c060f0c07051c1b03080a0608030a0212071e14070501032706060506030112 67
    0x2525414081c00c0340da2921541c01071180052084109006010810600e4a4a2181c1d1040c000300800360960412202c00c81c05214024414900e0345146025900e4a5003000c3c1144d80c010452611000c444500307a06500440c18120309800403840008140845641c9900c04c803103d074016181e10481743d0400b00c03154072460089002044010f40d41c6c1d40020311030b085002d03010b030007441030703d50036080e00c9055401d542c8101c4c0511001d5015000384101d410402040c250411108a00c046c900f00c281da46844e100c00f44c004e2a604502c981c0c001c400102c80c081e4803000c1041325108044003012800d0300d000307042424151050ba06040c23a044020500502c000111009042e003900101040300000458126590150100f11800d282e07860214049c503910000e1444000d102e501f180c0c210455010070703a40b4213a15071380681e0415040a00b418144400380d000e07154000d035a440e81c014541d00740e06109025013040d520040d00030030008000103054181c103056418082c45480542c0c0c2403106800c4a0f014102007001c8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 442695899 1250 442694649 442694653
    0x20a080403032006071d04180803040303060e0708041a0907210506010b22050906040207081c0209010e0d083001030c15030c0e09060409081303050f0f 66
    0x51002c28040d02c00d183e100c49150700501010b80159102c1414240d05861142c08a40200c010178407100050003030940003201a2400c01007400c03034108403468141c440c10003404480b0004042070a05200360030071800b070004805004018281040f0080414030112021348120010382115040041200c540c140200c042030001c1a845040000213070b50400b540d0740e10210303014040c0800d80001d0040c02100e0090031a11075540e20b4a800c0000301c0b03900d0307400c0c4546508000780040c041c40984d40d40c050b01500510306440c016200c6c42d10345804403851103206030404230004a80c105210030750356900240b621b074200380e0300d490303000711000c2c10310004540810005007098030500c80d0240200303215056040403011030322124039540e0300c0803405015400a070016503820604030824081c05520100b145d0250f0098502006921000302005005181d41c08600b8072451846001c80c2c1559140d0700315441c11500b202043d9510032429000301e441d8043c030710080300c40d800f5801300424003000100d500e00d9049004c0d40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 442697149 1250 442695899 442695907
    0x110c060118180b0403021e0d08100503030c010501091a0d020f03070f0e04030216080613080d110d0c080f0703020904110a0c14070602030703030207050a1b0f06020a08 73
    0x107445295014058101001203540314000c40602c80e121441d00742090180f150300300c141c1400c0c00c0090401440003801814400e00d400c0d03480b4007080025105440c04280d01c2c01c44025120390b8030903a0341c80040c0c0c0c0003a070b00d403001044e200e0f110001076001c181242c0030036200304030034900140707940242000301c0c1e001544841c140e401240503041c0814071049500004094400f81925402e560110211035005580c0d50b10300903041104150f010046a51105d41a100e0f103440e0520f01101c9550ba5440285207144401240c41640e041006d01000e03a110741051110601026800c035140e4060f0ba00000c480009070f41c1007015004101d4000c3c0455400b0310600315219040741d690700015406544a10f110355001946c4189009004000402819601a650707466407400521801e0200c461951560f83c40307210b8102034020410070381c001040f28401903242c2409a220040c0f8100141032601841000e007007040e13800c000101c0c054204a6910030782e80d00c2e208405019840c0c1c18200ea645a55510041c03020100300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 442698399 1250 442697149 442697159
    0x60f01021b060904050906041205040e01170703060203071809050402090f0c040902120a15060e0d1110050a1b0b01030b040620090a050603060a1e081609110c0601 71
    0x65028120074001401031843d1003100030100e002c4440841c1d40403000c2d00180140400c001c003600c07007071100716410b1400754181800c10b000070142400c180324241041101d640c1040f00440b00f404544011a00300108549910b040ca0340a00045004100f80b1140d4002003008100540d00e4400e103030040d03030043c0201d1000e0b0303914044640b40c01c0c806001054400c4040c800050000f00500080200d11594071040d40d80d41460044001a545031680310f081c281001c4800b80f100e5580b100010303141441c1296040f0b071030f102c40e0078007a403c184404519a00210481c0915440c290800c0040513002003c0d81c0780504000b030840802d01511402c00d00034681c411a5004002144a00490941141c011040007540300c40514800000700ca0081c04880741c5a404111506145409440c0d00000d040507101185140b40c82c0f00081d039088554013a0001d01d00ca03070507448041041004c7c40c0700203000c0b914115004228640e440c0303030041e102c074850312100e103051420480039120710605030341d401c0749450010461b030f034248 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 442699649 1250 442698399 442698433
    0xf1a0102031309180f05070501030b04051e0c130f03050f071802070c21060c0507240e030406021513081b0c130603060f0509030711030a060c0f020105060f0102 70
    0x15401c5044c503207440a4241c000c07803024220050b16038458001007801a00d40000901034074030751147d040c4194030f8802081216215041c41d2614081e00000c032070382c5907894001d02003050007140506d025240d244400401c03104003c40b10324044e01c4c01401100c4940c0311003240c00d07946000c503008195603c2c044219001740750740d240d0081d0041034800c1e075031902919195040907110b0700303a0704890711403a10000d0180050201d0b5103e45c841c0360380c2614241d071038550161a803030484103010041c11000040c0c0c40c0c100c0a02400b681c004114040c0d4007090360780d01c5507907190003035988400c848403617024504100032581004140b94400b02c4250301201a609180d001801001c0d015003220344c400040c000c000030108641da612020f0f03015601400c000144c1c003820760034168112030074200710a01c807600e0107041c03182d4850700209a5000300c3d440808100c503890540042428402c00541c000c00d464100f80310524081e4010348684500e0980c1c1e0300030040c80e901d001c00c1104075542541080d001d81c01c1500c00001341951 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 442700899 1250 442699649 442699661
    0x30804140a0309031707060222090209100507060f0603080304060f1e0f0e0613060605180c0a030209100309030f090e07110a1b06260610120f1a0102031309 68
    0xc00720b10b142886d038580c852000f40e0740a0286844038200328a4401c842d12084107507007003d000366403401c5090000c2000490041c103000c40c00781e02489408145a01007003c5074000c2d40340c056181409004071a605c2c40d050900750400c0d9012030701503050804144603650f440c030494203510343c9030524210010300c00381c071030b00107002c119840308a9a4581003850210402002a40c4c000d440078484110003440d1814648116882504110301c203100d000321000000e03950043e0503402180008285581b48803840c1c0c00e800078401c4051603600441100400896180c15130310540d002800790321644080c116641085600442a0258070307419204140401c036040e00c6410301c0300514010030100c61007000c10741c9030044400d0021098810011a540003805120352002c1c001188035910242c5050b480d45941c00040c1840c001021240101d8140360f05e450340d80c2c03003201c2e0100f522a0010f801c026401c03010301c002c0b001d0301901c10780d4041100210304410403944000200e41c41702e02d81142d4116450b05142206026000c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 442702149 1250 442700899 442700933
    0xa020304060818160503251710090b18010b13020a090305030403080301240f08040c09021c0b010f0c0b1503121e04080303041b0f03030804140a030903 66
    0xd64100f0708110354020841029440c03803c103d402c102e285010100761411031202210308500500f050f804038101d0b00c8403000003d60f140c40183c03c0414070401d800714901000140f0001d0f007981071000c0303036040c044a440c0f91405065040348404d40000240040c6003a1101071a1154121222036508080345105a02408101300246415000b0756983c1d154149582c006406c02da503803400000042140f072080500b00708031100c40f2446288074415000004c0c14121049020070240404280003c0c100f229290200002c0c2520781000c5481e03074010307014401c2c0e0f420400d4080c8030951400102c12010f60040e168080006c1ca25070b1a0002604075039200c015441c1e01a11070700c1c06203618245050556028004210b20030140940c2c1500c2e04008020091042005c1000f5900d488003044140712090001c42102e40c4990400e000e221980361580844120840700d03441108400241d59000c401c00d036000c1d115502941c0942e10341a145600b401080391141440340c1e008002c00e805680c04c00000c1d1401c2d101c1d8140070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 442703399 1250 442702149 442702171
    0x902010f031a0d24020d1505010804140c100210050609390a0503100e06060d05070908010606030c14090f0d030216031416060f030209030304050a0602210a0203040608 73
    0x45526110300d862040310130410101281c0204158414410a20a85001c1c00400d04515442468640064040c6c0000303031014026500302c3d050311a20300810000180f9210300034204c903141a804900003511100d03410b0b8901d58150918020560600d002c446035030040c8042138a10b01650910b88402c03010b26050f070703090020501c054074032030032000c112400b4200c040620b44a41d581c0307190141c02d000c3c6440c3d90703400c4420501c0e02c0c0001c3c07204039264401580c0d11642c14040000c1c1549074a50305580000345a0b01442e035660034120081107099054000f08200504c0740c0341c6010746080484880d125009840129400104000001d0360034542062003025243c060300690781e8504000300001e03c0c8207074030f4009642080340850340702080c0104100f00c8002c10700450a1004081c2400001083c1801d4030685000700340d00810340d40c0c0b156800340200c0e4000c04c4001c151844155650001940700c0d228036042400a0102c07100c003410055603d070882c1e40001c11580511714103400d08009a8001101404180c040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 442704649 1250 442703399 442703423
    0xc1c020f03070308090a06030903020c04091407150e09152b08041706090a0201111603050106050a0503190201031a0303210c04080618030f0d0902010f031a0d 69
    0x5a01c0c01d10003030020710700503402c0b6555420140b007400040388031075112000705860440341c803010a502103000036880c0011500801c48a04c60309088259242046aa101e039005104001a524150400c25184410103840b50b1207a040403200b0042e50038000c070b0300742075420450240c0d0003161800c070b020210740e092010301c003010f8440c11040c0d40c0c010000070007088558100000301070102c02022000c486881008034010210b5140c504042500c401555070000d0600220b041a141d03000000e00419002100c241c11000741a03940f810b14901820052080038001c0955000100380c80c2004101c3d5a0041e01882d005110101d0560046008001c4000a1519900c0c03da805604070340e0207000030710074281c020404422844041001e150002d0001d08080d2202c00f007008100158007020803015481990002401802c040200071141517100e080c1501d94041c0c0c4c00101102e60100ea0340c8000c81d0386000b0707681c03110f0303490700550140d040325150300041c03086142e0401a03400d5450301d10b200410481c0b00d41c1c1c044070701c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 442705899 1250 442704649 442704679
    0xa0207080a0c0504112d041a0d0c0908070b25080c0d180614071a070806040c09050f040f02040801021e0702010801300305030a0507020c1c02 62
    0x300320441c2801c03200300014500810103440d0500071661400081c016161818044218429003002d00141503400444140c50301d441c604032840558004114200322004a14031164800c480341d0b104209480b1114600ba00034807625100350380350300c04d131103c900c01848554100020411603400000480050b1902004035001d0490803c1d103240c082c500c01c2006545501510b84190b051600c00c07140041000060a01840580f080d00358000c1280d840e400c100c000050041c407030307101d9407182a1020304080c1c0e6155107950541c204001c40d80c4a640707240d0f50010940c6510701004242c8104244100009414201c14043c5d45044459000d06550090002030038103012802141a070b003169024032002d950100f1405801c0d4229203c0d081291000144640b070314100d0f50001e0070204044c002c015507030503000d00340807130021004240c000003070aa00003003a018210303241c0100950b104550a01e526030400c3d02050245000041c1503001a40c0203080503942c1e0942807890140b035a03c55004c0e1780c04504140c00a02c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 442707149 1250 442705899 442705903
    0x6060b0a0305070201051f060f020a080c070e0f090715020c0a03060605010e01050c030301060c020a09060b0711061303080915030108030301030203071e0303050319050a0c0210090312020a020708 85
    0x42011095280402c0d18504034102030b00710f80006202001c0c032850758100c40c3d41780c8401c0c541070080e40c205040c022502e403204001249030058080c401000c0010014042401c10300016800080743c2da84100a4035540d107542400514900075214820079501100e424072801c2e03d40110540c0503529072040b1148d45001d0743c00201c1d88001c070380c400e60b88030b650380d80280700559200800c152890700070b00708949800c20003441da65581c441446001e08114814039280215594105101c0040c105802d05010b80c0b40c8901400d455680840000c0b54003d0040041c4900c9052030703c103840400551030f508920300352851304c481849034407020410b50700811000d450014603ca0340051406042c200e40116141c3d81180306044c07801c50b50382c002205501c410750486210681c0c844030b50342541c2d0315203407042d2280c030384492280111401c8440d884419080000300449054541d10a280018481d42143c840c404030745c2c80b5804503840e03074001034002020a48a2000794600750010421a056881202c10655480020034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 442708399 1250 442707149 442707157
    0xc010f0606140f0d0e0d08180a17090111031809070306120221010c03061a03040803160309020607050a030815030a03110a020d12030f02090603041101030b060a0c050f01061202090406060b 82
    0x101207061a42803100900c10212342c44107035000d00c0f00170011410b035901c920309100c0d02c7c911511a445c0c8001f86400c03072070b4412100400505c6040b000c480c0c0701d01c840e0604402e96001c191b1103e000d54580390020741050300c00d005000446084410507140c8480580034045525011380c207002a42c42084140006140248901050380d10b0640c0d0000d8100d00b419584d02e84071031507114a0002440500500001c18000001c6035080094581c4c4102d00400b810002d40140c440154040c1d4030410115014090241c0461148040b038440c2d41c070081c2c0344d6a100360003508001c4811520360154030480385000040d000d10016004080c0349422544488800c0e4002034404441845c201c680385405d0407000103464060062002ca602400400e41c1010790010104420303020080018004613440903007403c40d40d000c1e5000c20710400019044d203a40c1c1030b0142001d04504a00032080b1440c0c861107003c0c0d050020180b04020989000c810001d40d20306068080000000c8080c0042e130760f5540c0d404000641000f000c0c010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 442709649 1250 442708399 442708423
    0x9070c1721060109061803061104060201181203110c0d030626190822080f011407081b0414090f070801030201030f020904020c010f0606140f0d0e 64
    0x45655010104103125610310407030030701903144990418000140c1c0c1250b001000d4071980d25001560315000c07050380c2c0c80e07407000da44050309103881c00210b0104074916500600c252442600203005c24240d08429000e1398402080c0a0540d070401c01d0302c0051300c1d00c00d40240d4070341c4904103e00b0b1308000f4100040e43c24003032240c1100012954501c0200321003280038003510f01d0f82032001910f03441c0d042c4103942d403070300c4010105003041a103c0441c000f60800c00c001c000c3ea401c006201408081d050702d440003038603040d40540076110441c41510b1642c0f05200050191408a051624091410351603100c020740b0b04071409410a45460070001c4050810504000504010700754072000e645443e586605020050102401441079551101e04200c41c00d504800b250381181d40c280380c0025961202c81c0007100034001d80680640c414000540c0c040c01c11015040074000b0303400c0d000700704a440d50350902034070403400900e0102014801880075460343c2c0c2a900107004156542d2602180141d41012124101283c1d82c0304 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 442710899 1250 442709649 442709693
    0x1b0d02040b0d060918120e1318020f0607051903020f030715060b0421080405032506020d0f110c0940082811010506010c0f0209070c 58
    0x1c02003400d40d4020440c171522040803001000e0000d03203c500782a42c6250a030000c0c040099500b0a0b280c56803000340340803400f944401c00c440c0e0b002036400380d0300b580e140100384d10a1800a54204651034420121040e4a0340a002081070300d90314000741c00303070fa10180310a80960150001c154081d520504c0280b0721f40380325490b0921001380c0b450f400703400c440094001c0b1503200420300060040640040e8820340c8011040c84008281c8243e00c0d0840302c51103250000d039050300a00622003000c058000310040602c09020b06640e5003501d842c401c90741c0340d40704444400044c4d2030221003104c01d40250f048514401109064401241880b404150b400b50144d48042e550030b80e004108804030903039014001e6040c0f5101c6041d1015001c50b001806100c072540340076141000005855510390142d00b00c08011000070302004180b0070f249a8080c01d449000001a8070550030320340000d10540c410540c00300110f03805240301000070916000c1c040043c000801240600500c49861008070300400040070074076800c403407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 442712149 1250 442710899 442710911
    0xb240309120901080609040c03140708100b01020c1003090c0b1b0d051c140103032a0b0a1a03061906090b060313050304090504050303040b010e1b0d02040b0d 69
    0x1464540682071000a20050041c880341c032043e070f80726041c1504030301c0448003881e030750310789007010003100d100ba40c002043c40c01d40254504010a01040440c102c03600201610341c2200e8008001d8240c90421400300d00680102c000030046150541c01c40d01074001038503001440005556804005200c0c80e00700341103103e400f0034140101c401d040e0f544d68085210b600584118610108081c0407130141071b088242100703562080390079030300c0d071f40c2c0c407944010144049450780b41d6903a0402801244140202070030401c111003190f0301501517841c0c0040d01c140c1c0712410070740554411501d88004d050070b0280e454401207d141180e15942e0030000d16000e038140d03422580080000004020840b200395200e08481c5040c03046101c0340396144001e8960003984020691030041045ca0518214821078100b000030500c0c250600003407000000141d0302c110f100e402e032503240d6600c4070000c8061070004c60721100b103003081d01c40070b00d0f500c1c00c1540030b40b0b85078080b98405400e0903101c1450f01d05980000030140b255a42d900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 442713399 1250 442712149 442712161
    0x50f0a030b0a06020a1a060f03030d060608010b0a050a050f160302060601091d0105060a0c0c0905040203010f02090f01121523100203040e06032b020f010c120b2403 72
    0x32a40c02d0043c5804c0c002020010700582d614200d001c07004c044440d81e1041c0d0f0b800580c0c43d0715070840842c2d9a110090130340313640c0c60310b05038124010222402504001055000003040c4c0542e0a412105c0440d4283c45150804000c000d04642d50f60001400414000c5d00344030210710703640300215400a041c403a030090700e03076460020001405048168044880742020080542c40f40012802603810365100341c0e1041c0c4c2e2500142419525040c070003000411030540da090020300c41c0e186a0040d801140308038000d02014443d0b03a40705040e40070b22100709520504a001201c050740c003c0003082c2c0030049540000c284c074112545030f02c08080303d69002d078504c080c4e10115045030500d2964002040c140889840306682e1102000070740d01d000d0f1b07000702013410401d0404038410380d90420030351700c05411904021a82901c08080c00701c81001c1040e0040142c411341c4402c1c03601d210180502d0a0960003a500c441c0c0200c24642c11001078403a181c0d20907080b60884218401d07815600540d104050035084100c0c3d9030381000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 442714649 1250 442713399 442713409
    0xd05100f0905041a010f05150705060f01031202030703082403010c020c030c0405010b0307050c0c15071b1a0d06030803040f0b0117060a0c021009110f091b0703050f0a030b 75
    0x20b00c0001004c00100720042c02200e07000c2e20520b0035581c081e55621b40310056030703040d0811846000c0f0040d110f880740b0401c1108581992a400d4180c912a030b51081d006606241e06030381d2030141c0f4074001c02254500c800103285900300c514500c10b4403030802030b0002c480315280229013150b19040381c1c100145c11800000c111802e00308000e601d040070946040003150714045d8065000d020250410301013107000200c0900000d002c00402014800040145c0c040480c04803251a003540400d204540707080e0240c03220610414030b4183d0404440d08140400101c01503004c2240141c0e002111030411181c0d0b421010001c11104d0b809140700340c6c811305000c8000d50b41030500302c1101d80705a0161480031060785880060700d001246558100e000d5800100c0c203000400020f0b81000075100001c24050710300381280003480506141d2b00c1083c401991001c5c402c400c41024400d50328000c5410000e804481c1050842c240c0920f8010001c05000b0300d0854205022010b800801764812405500041e4892000750614609 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 442715899 1250 442714649 442714673
    0x5040303020a1d03060f04020d051902150a0903140321100e0408071211060f160c0503071121030c070b03270c030a080c010c0507080d05100f090504 65
    0x81c04074090740f034421000207694050003403070b0805d03d100c61004241152600103207000c48070340c0030094500100410404019801d284c45003a4464006103041e00940c441078401c5601c0401c482e906d003114507056450301881c4055008104c1890301c801c002607440300113074a09403900c04815244005c102d083c030220f203c642c040242c2010150030b201000b0b00c03002415000464082941c4445101e0401220940594103d0a0700102009030300076002000340002c01075182a120b042c0312142805c407621b40d2401241c0301031075008000c1065108120b0100403c000b500c0180348120b0050190071104c038500900c0a0414614a04600d2a8000300708040d10401c28480d080c0a800341d402000d040d8038001c0c0102000d0340719010302c0055414501482c00024100313221001c00d40c140038003115550200c0307281808a5a204a1107030645502c2d06c4a070b0385015200380c0c11108140c0d0003000450411100d074002900819018050301010315a4402c001001547c8650020041c081e50000080914041c1001903080300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 442717149 1250 442715899 442715927
    0x121103010506010219020a0911030906070e0109091e0219080a1e0207020a230411040e0f07090302030d1e0e0901180209060301080604020a24030e010f05040303020a 72
    0x4100740400c00681d90000d2451501407281207900b40c02c0640e4000b10f803a4100541202480030300b401c0500e4940240e000044d40100c0d2190215983da079565002120540b0f212200c00b0700040c00b1810400061031a80c100e98840014070a10720f100c2c02c2892100d500300e0744000346031503609080b02401c80883c0d401015695110b120200705008000c0d0303140840c1521400c1d0584801d265a000ca400381c15512074100c44800350603500080c1100c00780c528804d0140c03400e0010b03801c0c450707401c0820f0841404110390079178045070080d0003501c006860354180b06030040e000904040c20081252000005607070104235141208216171122584a001c502c80c080c2c4446841e0809420b1100911103500c55445002055044460f2494807540302690f40c81c800000c1d00c42c250025a0100021001140d00d1a0110320310340190310880b210146103513900d4517075a20040c8003008811950301c1d450b04005443c0260040124100030784000200444482501421204281d07400d8001960114610700c905411000b0034003145 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 442718399 1250 442717149 442717151
    0x20706080105010804060e0a0b0c0d0f0b1f020f031603032405010e01050706020708030a0c021b0906010905040e0705011119081602031515040203061c02030304080712110301 76
    0x160401d00081c160102c040c0000304030940e502013031f60080c2d20a000301c0410319400501e003141810401800d0075503800c5100380b20b90780c034034009850740013584170300c40c0068072040038103401d489000001d64040044468002103080d40201c03948103195a500740010000000e014049000641481c1030050481d03075040a81d507500c694410b204250385903e0700700c400480b142441d1401820f081d02004030317458011b00784010701c1680042800f0040001d4203010f140b080e245082d0400444c040d01d40100c1e03131b5031010341c3d00f00011502100300103007070304051621950052060400c0500ca9982c0d40115013111449400d070a01a004040184419a88280a4100c0228070001491003113014800c14415003050380d001000c0c004009400c0440c40c84503803510040300c3c0c0007420b581030111241c48180e040c0804460300090a0350b07400b0401d085207414426607000d15405059410280d441d0842d1800246100c54181d0b0f240c0701c107002c00079420030f041040c1c002604c591081c00c180840507241c60a5140c1e14044054482c0e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 442719649 1250 442718399 442718401
    0x18010e07120e0c0415181a0a05180406110c010506041b2c0409121413062f011a091e0703060b03040b18010603080a0c0615030506040302070608 63
    0x39000000e008010710740441d00007406903840441071714010b00c81d60001009007040421100030040302c4d4000195030020000190099200c44104014604107000e2150300220301c66030007514140d0110200c2d07009225031000514641440e4010065400014102200e6910b400404c105400c0c18090006040d040300c0d40341401c491080c1000d40b00031400c81401003640158203010042d8103480c0300000080c503000e0f004000794456800c2c08a0071254801c10741c004607504061ba811003483c3c040490340005c420001000035542003150454800c4d66062000c4c0c2201140001e20b035035684034090f443d4040e138265000162144450404d12508040701c1d06140c41b40c034001d4100701d00710709440412044501401da6100407903660700000c0e4010f11198005902c641c50210802c41001341c13038000d032805404031002005070341d02c2d191601e9081c0c40e504d020042c03070f41c030040c01003030500d900a036441889288503910214012841210200c1545460380c02510039500c108140024960180f01a40280c40249400c3c0f0395 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 442720899 1250 442719649 442719671
    0x503161401020c011d27040b07050a0e0f01051b030405032a01030c0c0c060302310e0a06180203150307030506040f081b07031506050d0f0218010e0712 66
    0x111641c5003040c400703200480612041c2e903c0b003c0700c2d2458a9445640c8450740c84071b01000017615002c8030101c1c1d0f1420400c0104034080e002e00b050b10000c14459480c448001c0c0c40e40c092002a180e81030782641880f1040c080f45180d1600007040801c4220004000c41e1034034a88801c00d49012a00070b029003500d51003814004014201030350070000c0000a080106222031102c208a4441d100c20303002801d460101c20010400682c15001402202c503c1e54981012540c82c0c0c840004400d86000b45504c120a20002008101c1c82c0300c0c01c00f0b9012000a10010300b17281c3c2c07803e010035a4442d9001c3e84c03900301c1d400030401803813022404118401050540003480c1c401c1c15a40ca00340d4445000d40f0190180d00000b04000030800039a00311201c40d4401c84007114034134000d900700e0b52f0758620360008480c0b00220380090401c0c0c1c0307182e2241c0000c80d10003c10300c42249042c0c1e1a40031005804040a07a045804001c03aa08a0891629124020000050700c0f507500d140c84600203102503907444800208a0400b100d600c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 442722149 1250 442720899 442720907
    0x906060f06051b1c0905040c08010e04120201020d11190309021309060b0a0e0714130e0c040e0c12011410030209030f07060c020301050114090412090503161401020c01 73
    0x82c50b003c05991070002c5030000310b40d900c2d10b080035840e0000b00d03001000c44019aa0310030103e504807203066805000032014000c0560702e42c4400d005211054001900240203d1f800941d0108505014000146040e10f14080241a20700c6920140080c81307001036905450300e203105a00c0c00b62607146c60100520754196002501c04190410140051030b20307007124800b440700c01d030300500c844400280801d1459903649880030800404a5041c408510080f6514070540180d1080b1001d000b1140d08110400e800c1842d1a5000040605100c460340400e110214044d070100c40458040c4003d000403a444a00c5021007010642050300032a00e40002b84003200c101e512610385010005400713080140e221000b00e00801e1400401c1e501c0c6040c030707100703a58002880580144001c1d0403107001798001d1040d03a0300c9000f4240f4101e0103000702c6d0340060000d0b000401107880c04508890800c01c6162408066949400180c80c08a201d044220b225004032003c0009151300c640c5113801001c2800540180401600040c2c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 442723399 1250 442722149 442722157
    0x120501121b0504020d0e010b010c030f0f020313030b090613050601050609010509090c04080c0a03020a140a080607080a0c0c0512031005120114010e090c1005040803030403030906060f0605 82
    0x101164081c402110a9801c004103110240602070300c21900c0e11716004078100903007488144030f000c43d441e0101c12003071540318501000d880f90305502c03440807000e0092422500c50848624280440c041400034045540b100c0c180314000f107004444c0d452481c102109440c0c01c107070019040c28030300796550045c0300002d80085062411a00c007110000e0701e800d0040010b940c03d109281003142e0048104c420080c1c030380c00101c06001603c00540850f00c00c1c2c074808042c006422081c0c00040d5201000102c2000798103104840c50f0460314010300710400d40c5569030803452600e0340a543d40b2002ca0311400c01c001921566100d1143e8800051a018000041984038030782c46e1424115000c64540c0e002001448030f0000380030b440c005000103003142400e1039003001902d00070440031131101040241040002608010144846d005008550203084140b002c441080004808049500705004041c4800100e410081c0082d5110380c1c001e0301e0105d64036100b85014001c641c00760308042c09000701c41c0010711056034400151 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 442724649 1250 442723399 442723403
    0x5040f14012001060806070302070206092803030c02030d0807050904090602040b180a080606090c0c01141306050c190c17070309150c080901180510030c12050112 71
    0x10a400090000040b0391061041d52a411102c5145601d208034070815407100f42200d20b400240c80e5541c071404802c41c142d202e6a68040d511020902c200421403400c4603284c0d1507418a44004902c01d20038076071040c02c114440d401039001c294130080c0303c02541010300a20503100f0107480d02040515005801401c05d008103402e1a000341e64070182c00d020400e8560484014001c11401c20383c481200c142e41c020340c886906d010340e0040c8014200050a03060004200c1e0007010018207420440e500e070309078181d140d00070840b46d103000d41d25001c282d9600404404480c2c0240b80c000301c0d18000d510707a401c020041d40e4000d010420001c0342040446880910660520900d1040d480d00c04215800d40c1404040000600107440d004035002901000b00b6400c80c1010040b10b121300b00e075040d0440ca10400384c603099a00c42c00a131943d0350420002e02c0b950720611003001100420500e81d0046611400864040642c60701c03c0301c00b184d581c90741126069044500002e0601c0c0c810b001344038640c108040140c21801003040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 442725899 1250 442724649 442724669
    0x40b070210090b1501090e010803090a080f0c1003200a030e0d0f050702011214100b03010b03070e060d050711010605030604020303071b1203050901030501080606090114010c0605040f1205040f 84
    0x4013154a038410b241100084c22840b901084a58480070b00300e450358800d40ca17a600c100215400005c8204002c64007041c2c0b5070100d0041c000d0380c0014024800f041682401e41000c040e81c407c980349440400d03501107400c103404042c000d0344600701208050304031004804800241da1060030440303003699214403683e4800032145440760b16101c0600c01a544412902c07408220b6505112540714092100c010f003620801d101c01c0407101c040c3d40c6000720350252100303000d01c1919010410010700d4050003102c8004510078081c03c10340c03400c12105202c0e41240c1c1d05440240026540da806582102024060000548000c9019203020304296002035034074401c103c002000c01d095074042a001560b0500301c40c2c000c3c45500240548142c561400a20f280c1c006460580031038070b0301c1c001182000001918911410020b80444800d034240101c140c1c0e00507207521030301c1c100074911a00030000f503072500682d0b0041d0f10172a92008220524580303a60340d403100d40c0c940c00c1040002d100420031550300d290500211070000503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 442727149 1250 442725899 442725931
    0x516030b0d0b090f1903050f09060702040507090e0901061211030f06090c1f200f0a03030603200306070c020a15020f010c0206070225050405040b070210090b 69
    0x1001c1205002244009058690503004001c54210b011030b0316010031a40304141c50120010103500341c80c808402d0300c051700040f0300344055078034a134400001303021070540246424103203180d035400103064403030407102000007850890003004480d800242d9141c00c8107004000348072580c10a05940c036070700408a0090840f200719807032920326840a01084040700140700982d4224640581ca455035007007843c1c01e8600407051003140092060940030084090002c0c1e65845202040280c0a4002c0e5001180090254081e0080c2c0c10f0b0348810400481c400ca0f40704e5200807482074a107080401d21860007603401e81082602e400c0d01c20041c6e6000c134105501c002e0500b800340042d0124008151000c2094000c604014802201324010540014806440d4103882009200b19060b1034002c0782c44a5080e0342c0035003d039022041800d211f0708149880441c18041c01c401c807888980d140c00090a552041e01c040c1c6024a0b5501032010040d4140b10b0b9400403100d4000501045c00eaa40c1c4c3c4120750074004010010240c2122 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 442728399 1250 442727149 442727171
    0x901030b04090606121104020a0f050d150f17010903082403012c0a020a05150f040b1b06040b0a05071e0e030c09010e04061e0f02070c0504051603 64
    0x1902807010b0300d8005504000c0c0517100d07040a403113454900d0094401c40c540c400d00070480e29290007102c540104c03036501d032911106040400d0382c10350018a81084c01036143c3d49030824804500c042c2c40f004113111484103a04a140184810021300c102c2904034060f41040d41031004250043c00403070700800d0341402240d541c640c80c02ca4503030714004540c040da899401d0480b9503034010380ca46100242a100c0d101100c10750326143c44040ea5035108010002d4102c645071f4010440383c9020000c2c001c5002c14082409e180001342d000504075076100c1d801241c0b00b24000f2601074a41c901004025540a002c180103151505003512019440b0000505c1072203c2c41e100d0001515a612428042030306156494412a4171134048102070002d20174011600d010384038480c07003580c0500d8030a10090413106103049a810503102c03500d4003006040101301182c07800c0307048001d440e603100042c4500305007020103500040c0c031200c0f18900101564103a502031803041c0d00300018040030250f0440461400301180c00d0004500c4002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 442729649 1250 442728399 442728401
    0xc051003271704090b010909020711061c060f0305011b093b04060f14130c0e0f010306181e0303110f0c2803180302090c12010504110901030b04 63
    0x1800151142404103000480d62030726001305c9048402602c404600b00d071624000e904034065031001034280e440d01181c500c2c4a080c0080141507000003c811801180baa9498040c25140540d2000f080510f20302c400300140002885442c84402490345a11049085540000c0c408162030140d0700641b04001d84003100d11441691a604400c0fa1407000700c0b01c40a6813481511f240001c50f03080d12a141000c00441e00c0d04042d108003415115090700d00304242c0c0b40c0040821b030a10301e455003100c4440740c00c4030104600c05002d0750389104415008088000e0360641c50034106030341e1742c0318011400408844a00b80054462403141000203c1c8120729603042c1401e09040b8094455503005001d00500002d1010f105c2604000500b5910000c20440301103a00400a582c0c04003603507100200b4803250040f0020019110300400400000000d02000c1000d84070340019403900e4041c2c5250504510010712840201d00c000031981c0180b4049800300882417000707020020380d100c0c600030a030405585104540e126500c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 442730899 1250 442729649 442729673
    0xb0d12080901060f0e04020a09180b0613090f03030e01060b070b09070902030a0c020601050616020603070c050d030c020f0f1f09170c100203010b070206030a0e0a0c05100327 76
    0xf401385406000d9540d40700c254050341d01501c0580c003d46001c00701080341c82243c051504003100d445170307800040c02d00b40c80700c4210240140060b50301c50118842c4040d420310710300403d12814014403204844080c1443c010b8112460074036000c00da0703410f0100c03c000450300c08098415481c5c1042d041c3d10746603250000e207801d10186030002c02e002880803090160009407540001c0700200940c00b00c038902d988030300070000d039401840030511440000c010f04400500b010800f031900410a410071308820001d0380e07602803d1100c1000e140c00040c1c0d40d010034500207a410000782c060480f01401501c10291b00700c1e0341584808081c03000780c2070360020b40380c4080d070410240c1c08a40c115810400011042101e1064002e160f0300081102d803851240c5010303807030309220354400c5030704a90071300f00154a0080c0c20b50034003045410090180c00161f030707259074100182509100d40c2c6c1005100d101001c209609020420800460156aa80c20503280801d8041212074103401d0b94030100c1d02c0b9050f100010784914000c404250 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 442732149 1250 442730899 442730909
    0x3020603010608060d0b0c0408100b0a090209060d1e050f090d23070b0103140d05091c1a06010206010803091804050c10050a0206070e030a261305040b0d1208090106 72
    0x1b00c00702001340300c8078503401600580f038816003606c0da2800421400c0b0151070221001a0b4881c0c803000d130410134001158014515030707101a011508240040034480210340400c00d03005420302d800c01e040c00340e440142c40b030f20340d200e60b540c2491140c50601107844d940c0c411051441d0310900c0041081121038100c21500aa0110741e0b4042d117581c4c0346460f180003001072000388070494078281a801d01226022000c036079403c02206a035141400c1c41c0b520420803d810b5000301003440b400380000741c51070100780c0b4082c82e2030b80c00400d00744114041c20001d00082c0340110507031200d041750300b0a00000e001130307444203070141506040100c0d4840b5501c0ea81440d9017822100011603038840c4007100035161050708040070384010301c400d03001d0383e00d42d9503800700640d8100b04800c110769254008526800004125180f41d8001000c8417010802540c606824011103912180b40f03902c41d912401020021841c00d030180c8d0745018825140342d410201e01c1d41d40c1d56100c0d18094407180502003000001150b42070f00b548181c000304 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 442733399 1250 442732149 442732163
    0x2060a0f06051513080606010512070909090303090b0c090616020402090904050a050705010f050a12150b090405100e0c0f0c030301240903031b030908010608060f1003020603010608060d 81
    0xc0070129a645164001a1343d600343c503030004000100d520020818610815040e10350502e02140e071170700e070014604000c00d05ca042c0700c0350040100c1c50480c039220311803d0603c03075207000a2000d15801c1c0081d50850003003650094500401401541c1d407554825580e00c0211005002c000c891a4800a00a400303001003080e0000181c100704424400c00040066080e80900c0030740d80c21032b894400454140011011060224404210005034103109084482450802d45d0000401240301e100c0c07811321070450361206554002c0840e01c0303600c92400d0301c40c9a130440c032210b2810318114905904000c1c0304200a004100882b0046000e00b0a810840c046817444411179041c1c0c5e58943e110b0f020000070011580b01c0414111804803c0886a40104244010b5907015201c0d03060341100e22407002e4844818000132402c1000101c000543d10742c09000300c41c041c00c4040003400440c0f500002c42e1044075402800740e00b40e040c40b95410005030304d0f480308480c15a0064038200d042c59546401141c00940765402c0107000e1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 442734649 1250 442733399 442733419
    0xc040e010b03241b03070f0e0a03030206090c030613030804050a0c030b1501020607020c220f0606020d05040617100b07140f01200a0201150803091f02060a0f0605 71
    0x1461440041d00714121000c80f000c8083d40b1801e816030240600103202130369050003000441c80307081c042d50b44900012181c0c90030014040e58075003c143c0d48044d680c003c8015038000c6007484510741e8144003451300e0300c130305400610b13981c9030007400c90303404095031080941802450b00104041c0241448480107013508209400c0101d9628035040c1000c2e00c080350264030201c1c54400d00c018039031012442c03a00400c010b44c01855a642c941c0708102d401400843e04180c000500404c4020f82c02081c081c0a188640903400080d401e450714902a040100c150109070400070200310601c603468000440340014510141c0750180b541c4c4081100c4410030f00ca421030341c10940041803900800a800084100350b246003030650f600403414440c010b0903540b1034294212030390ba00200924910300454083c2450940e28400401c0300d00051040c0d20602c44103400c041010307040001d580d4242c0c2014074031852031a12068001d2109003019500949526014015000302901c0d0340040039036116580203240074010080211040c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 442735899 1250 442734649 442734673
    0x9120304030309060e060d05270309040513080a0503090109140a0317010803040b0d02090a0f0611060c0a030c020c0a090606080f0912030c04150509030114090c040e010b03 75
    0x1994105110440000e4030902d000b0070b13668482c45c3c81d00004800a04002e0816241480200141c42c0092605010040d5002a0001c3c220703054a18540100d1a102a6a43c0e507184810f220549600034804400c400110b001400011805022103619980c02e01e4065102d442e01c41d00d5901502c8444000703400f00e000c9043c94448130300040760076413003248a07448060710401c080550f0341c02d5110921401d58641c1050004100d031f00321242c018160300f0000c00005141050307080c00914100c0c030640061202c02c1400c0b8080c00ba83e0340010010b860049424014181494010310010552184080c00810141c46041e40035105000300504c20300030070020a8200000d4030380300303010002c0c5101d11071200024074202c0821201400c1c80300180c0218004005810480115050034071035900c0a8900e0071640800c010008a00c4d006d001c1e800c5d05003a807aa20340790760b43c030320204040c00e441810016542c1400b140041c8100d02c4800500042425029034000c140030046c0d0048074010540c5010840c0c041c050141e0205e5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 442737149 1250 442735899 442735903
    0xe1e0913170d05011d070e0f0a2402070b18010c03110f060a1104050d061112010321050909160207030b090d030e0303011a070c03081204030f020c03070306090501020912 74
    0x705980c41882c405e41c080015059640c9443c0c825198000828030000108000d4103214143c1c02c0907a9000c0c140940c402d644581c1807564900d05a03076002400c0e81658400e604035410305c8954001c008082b4041d0400d00403840541044c2c4001c40344505008401c98040c0815002c2c1c442c80030000c070300100303451800504141190b1540c204949103d080c0b40342c200f500c0002184401079405655000d082042d44d003800e0768580005245c0c1d521618500b00b002d0021607800440d41c0b243c14040c500c601008905e17542182420170420b5804d00c0d600c0c003800f0040c0020107641d00c030614881d82c4007515a00904081019401c26800c00860b600042d04000001c010030041c407800040d1202c0e000702540d010807505206140107522400300780241452061416000d040000b28000600329860007201c1171081c041c1e480d640e1658035480254400381052440342000b05041d0801a0990700c1d40c0d85001910b8045980c2c40000d44903120f500006100c9541e509805007441425030644070781c410042c01e4a0000100700a0340e0f6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 442738399 1250 442737149 442737151
    0x806040f030e0d0c2904121109010e0a0515030a03020718020301030507090903090e150f0613030209040813080f07060509010903031b06020a0e1e0913170d05 69
    0x140100710b10500407815403c010030311600d465081004c00320080d0512050001502c003034000180541001c800a580b01c540c480c000300300800b1507070811081c80c2c5052600c0803440728440000c80c800e11002c00108400491142d0b441d0307010707844030300001301941c900c0703c50303510640b500c290b00782c05104680c104000c140d00020390340142d8842001c42c00c25241c000c0e030444268402404010301c242c0060902300300c03e101e6500940c941520a05103494000d1f00d8129180040004540034068010500d801d080c1d54240050301d801c56038025240b4502d440500888003643e02d00d50300c0028040e5401d140020240491201a80c110000010381c00c00580d9951711070075654000481046510b0055450014400340120704842c1d8030704068480e40101d52968400352803011280402080002006060b840084c09501c01828403203001c2e11031108503d070f90014003500c00d0701034a800c0441c88000f031b92941c0c241e0b04c240010354400050b040c0300c0c00c1e4000c0d501e44084190010700306076040b8040800c4610001c420f41d0011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 442739649 1250 442738399 442738403
    0x1902180108010b0a05090d0507080d030f050a27060f0c0305040210021504150f0c02100b0402130e04021f030f0b09040210030c020f0a110108070f0e04020a090806040f 73
    0x1507041a6210910390006102d09120400810000c020441301810510480b220450056003517500c651703642c0f41c000f401c00078030035060f2000079515203000880748401e00c20180c10500446040103c08180100554606400340c42041c81c014200c080d54100301054020220300c010704007040c070280b041040c0181c050f000c156000ca2068507070010208040d80b0016142c2891400014486040e07152034507809101d00e01e01c80301200c4651110180c89003034038203010750f5a00700c01c650300500f49211020741190807a0300030980140b18900401000c1100c2c9410848003060300c42004c96090b40c0d0311180b00181c03424a003480300c0d90706250440d40d2203000340d030945e109890550040c281401b82142d49c1080100d421030807600258405880c54031500e240c1d200354408900c00102d070044400b00c0102c0752889103043e0042c4400c0360285801c81d0040c0007075900c2440706030840c125003001c0d090300020a0307000e0100d0003e407460502999000c51030240c212b00c500b000e000148483c00a40c0c240f400c041c01c1416401110200c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 442740899 1250 442739649 442739657
    0x120f030708012102040203070c0f050604051903090e061215060109120b191d0c041407090306090c230a05090c0f0d060b04080a0b09010504021819021801 67
    0x43d20403080d81044891900701d1100a280801030f82040001d400240905c810041c0f511640000540711000301c03050180030b1001800149400d00e030240ca00f01101c01c4910114003c07045450000b6000b4002e8001d54404400841250346c81c1c102264051245a1800006210703420080c480c9041e001d00080c000c0c4000c1e070390f0062140d01c981050003038103840303000282414900d00c00240c01d450341e00807400480c00e0780070012a01c213080c00f45021504c402000d0350a0260000c0351140344600d01031003008111360000b4172142c018500220007070690b2a5520016014a85900c4a2410019805603120151401e01504000c2150944888400303034a06200c040c040d60b44004049114030744840181d01c9000164805486c0015460080c0400c1c1c202c1894950341549410b404102440603502600150030084014810562a4240703002d42e10405071400c0304a9140000f48805622200c04c00c5d84280140004c0c0003003516250715095450800176801e041c030300e202084148000079041d465845031a401d0342d07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 442742149 1250 442740899 442740901
    0x616030504171b0904060b1005040603050f01150f110d0c0303150b04230301060602032221110a15020c0f060414030307060c08070306150207090b03120f030708 70
    0xc03599680119102c40310840e003c4046805452501000702170740680305007004500301d000c0401044045003441c00d07200c0414400f1030306000d0f82e60715220b403030b5209294900c032188952410151608507085071034000200310000540c2d0b00c40c2c50080290241d03281c13910303040750a4088200d02c02480d40c601e034401203001904280c80c840c841c007440d240f03d0055903212a5014036003460300002d155120440b40407402c4c10510b0f812082000d0f0707420710540c4001d04864015640c1c1c5d01c000480d4505101000280035640d2894900612402001242c00e108204e00c00646520302c115904141080b0890b2210042d484041c00b2000300703580300d02d521031500e04801c940031114403c240c6000c120a030901c001001d07401c80c41c1844100a0b90754000e540303900915003d0196854001a03131129415251807a0303080300030400103030038480210307418407403d00208550145070115241513100291240104c4c41180c4005448040c41c4985a5040c032074281036003048000283d54018508022410307400484500d004140c4880c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 442743399 1250 442742149 442742189
    0x31015020105190c0e1201021b060f04030507020109090518010507050f1c0e03180306060406180c020f0d230c120c0304120b0f0115090905060616030504 67
    0x1000d00707802007014100c8800c01161501a4030018a804801c1d0000c02805c2c1c0d00d101d00036110705010180c00d40e01e4000142e514500d401418100b15210304070780b02c040d4048020095a080d0004401d0b41040d030520780300340c3c2d4900a000403a03240d583c0781c104031021031901092081680050900d00e101e220f100c4020b100a54802c0070130f483d14050810746100c001e00c20400314105c0059040c2c603a100606c055030000719428003c01c014a19003118008040d41007401080b115149020820a50300000c111001c0c040f05043c09003041440c0c15401c0351044c585d80720291788480c0da000303000d000740c089000c03c11241b03400841c1c41d0040840b04030700c062035964a202c1c40000c1c04800e01c0e07011110380d01c0e000c4009008440320310418005076480340344120711a00092002081041c2c10714149000d550040c03c00031414100412007801032001a03201a010245155200e5160ba4021103800210b607810f29001801d80d42d0580401e940c0e1081101d0444004200c1c2c6d0540209500800988103451a08500d80304000d244 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 442744649 1250 442743399 442743401
    0x903100b030a080d020c06090f0c0f06040501030911033702060703050c0c0904060b01180302010801181d030c0d050a091815060305010501030c050304020a050d170310150201 76
    0x3400306030141c10084104000c03640c40c100034260070651138801440d05541003212400c0007400c0d01c01e04540d030032034410103910b6501000010094041152508660b07001c060006600c0e01c01c0d8483d0a06060f1200d246100788503030018245644c140280a55030401e2800c03000800c16130280e480b15980800030511149442e121401e030319041d56015048910b0904a41c90584a903000803009400c64414403d0707039020f94481a8005008034410030020907941070250000d020990074503071045120002000410150780d01040c1103046881e1031038801c0d644051402c05e440500007490070070304070420368010b40000e500000000c2611207040341c20b50b800101c20b05d1088900d0300c5421490000901030300e0080c000c01c0e46122000318102d11210300041c07420242d142070215010207a2002010076a1440108000d580501402c990681203240085c82c514103640000e00c0707080a8082e460241c8000d4040000700f05410400700c9001003134450b625182c1c500f8150424020300640200401c80e80f9680500d100320f801 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 442745899 1250 442744649 442744661
    0x30616140c0604030305100f0b19051c0f060909141507080f070c021009240504090207020a17010609180506130c0f080106090c020d050304030507150f02090310 70
    0x100d9020b45800e4689480c120003030400a00b40004502202e0000030303814042520040080402a0703d451301d03000d00d420801401c44082ca0a40148801002134004480140c40c0c03c00341e204030f0240c000358050040400300c0081c1115000501503500d0800004180600c07168030350001400c01c000c485070280d40c0706140560400a8488401241083c008079440740708040f0305551154891a100e006054182c0005d20044441c0c41000042003d0040c14030102140318001d13501680b00242464000001c644014100d00c141d110300741000da408680c072000c542d664401c5c90001c240d00149560501c040c0310100c1d00a00c0544640ca0040f0704d05041000c545a45074a4403001642000240c00c40342d17201480000042c40301d1000300c40c4000d0030800840c00070a0041c1e000090322000c3c1c0001103c3d03041c100840704442c0f040c50158213640c0804500f04030343c0c1d8404203c0b0b40c401c3d0701d0300e0025220300c0c0c249013070f000c0c07001c1c614290f180890509202550400d019400f5000707001003202211604000e6001400031504 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 442747149 1250 442745899 442745917
    0xf0f0303023708180901060e010809010b03241005010c0212010b04020c0d02010534020304180c0e1207060309110a06020c1005190e0f03061614 63
    0xc001102e444000c0d40b00340040c401829004807030401d40e003003400c0d690420040c2e03070215101000440d00c1c0e0b0206901024099400c0d400341d5942c1c040d9410070340b014107a4405108442d04000c591030014007481d000390000070704424040c045400808102e06824141c0400b0103420708002d8040740042d07501d03450400c4110403a40c06840d4010415515000d000503155a0680c030000c2d50340f9400050007640301c52008104c1461100081c221075010f07800002e09640000c1c05400c2d201250a40c1613a01064200002060182c0e00c8105c984540d2901026401e500481e800ba40f2003000d20000080343c81e800f504091102209a41d03003030040e0340c1e1760007003100011000c4295074169104950a00c00c0e070780207a102e5101302c1e000d0000c00301840b00301000218454100d0304a500160024015000c003802c0000700d01c00c80300b03558105103040049111441c000140025650f000300030361010707890007035210004007000010000d0700303139070303162a15903401002c000c89064000002032416802110044000f070a50764010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 442748399 1250 442747149 442747153
    0x7021204060c050c0d08091002030405060a030b030f0604050303040b0105010804120e0a18090b010509070203070201032a0905190503070b071406182404170d060603060f0f030302 78
    0x3410004100ca289001d902e04031500d22610b4040da000d5520440324010180c031038403050350741d42030003020b004600d52154121000c0d5401448107000d2030359403405590403550b0354600007844154982c0000d182c00d00e034200208440c0075500134441808404001180301d50700540508a15981c1c5600450b00c825089038058003114101c0c0342d0f003101d20720403003024601c10401000082d41c2929504140c04078240d04402c1c550560761810030200f00300f01d41d042903004020848aa61309481e00c1c0c9070180d02d902c91a80300034101540c0e490682c0c85118601805005c1a11440b000b00e0000400c0c8005052075503203001d80c6100c0c002a580080e0011030045e11032080d53390180140106030325040c3c101040da00801000c803041e42900b8020b08401d18100305040c4a1442580c10f5030b00d81c09200400303420420344d003445590881c02c450b143c0180703035003000d02c094001c2e40c04040300c0c840038100d01410415004210244103c0740c1081030005001c0c5c0e15070410000d40304c0c800d0304d000d5402e56801512400341c0b001c0c44000e0150f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 442749649 1250 442748399 442748407
    0x80609010501083601150815010905040f08030a02090a0e0903070627051b0a05100509040b04022a03250c050411030f0a14060f1309080c06070212 64
    0x4800d05441000840c6071a4065201d80352084c065101209113400315002c540c0d958140100180d610a8564004121202c06003120850030a002103002c00140110b248c04c9480308080307010461041c0ca0f041c6220740140e226034481c01c00d542c41f08045d511a81c8854854540c401d004501821500c00b214044c0000c1c03002035141241c0b955800c0054008010400082c1c03003080d001d000850420900d500e070041c0310340f01420100d031903804034101540c0d0400919001d80402c103000d014a888600660717014803041e0409503191010000040c020b0a11404201e801500100f40740055003076119120f00e2960340303445d60001d4010481039041d9030340503500690300c10745030011440d0688270415070100c0308203004d03c1c0d00c400c1d01921200800d00b903542c02d0398a055042c00000421260780c03498071000e41c01c4010300c7c20500c580d0b501100000f00300c40d4050400752044454100c01501035980642942101c0c100820078003102c41d850601103001d80194141c60b00d540101c000181c440d40c0302044c00010301c6d02c1a4062810 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 442750899 1250 442749649 442749661
    0x7110a080c0d031709010e15011a0c030904062304050f16050f041d090a02010801150c05062d09070e13081308010b06180603060d140a0308060901050108 67
    0x24202c400c0203605001c00f5241049200c07484030921407090300c04d040007250b5022103960781c42c9004144009108a00f41007801405a940700350704080705d6074000324140f42c84850a08286082d80b00d0007540d40d5205203071a00010740700e180f03140d044040d61614880d036001070700354400b0320081c0c400c204c80200c050461240003804030590003d08400c503081c140340072801c110b22300f0f620801e40d90140e006031000d5a49034030f060054200025102d603000d0030110140c20207000c0d0340d00203040303d1010f0154100703480360a5400c0305414440c081d0f0030103454000c01140d00600700010b0240c50802d50000d01c500881c1c810314101c02c41c040d244241802002000d00416500c0e10301100c244003140041c1c456043e00b901d00c082d24001c9515107000d840044851300001d8225803901400da421a1500e01405009100c103014401c1c0c18454800301600c41d0009490003656941c8070400102e8054260382d00800440200502000c036142c00030340d5001c0f1500c01d4644c0ea0b03054840004212070403000b48035090003c1d2071000000c0d8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 442752149 1250 442750899 442750909
    0x30f080c130e15120307021009030803070e0f0613050a05040e0303011701110c011b08070e120708030c03070b130c05040207030c06061e0e0c03070c1505010b07110a080c 74
    0x81e200d4091944031464042c3d24000a00c40c0002642d01031445d400400c10301d0951801170b4600841103000d091003106546150f50728003150000501c080c0510001c860001041e844498200a120744014101c90382d45501c0c06400074001810301485014141ca07800200d40d40c02c140c400c1e0790b00f01700301e800103500f503038031b04030545000030804050b17071205540350340c1e80034140c03200c5e000601210110038001141c648040501b800300285054007041c10008000148001c098010707030300d22501501510795194210390f02c840d00389402800d5014000510000482c0f803e030500100c090720b000340c4200402c8242e07854017061480d501d220060041c01e91079144d003007001185091350080800501c0381c10500702c00000c503126401210b5180d40140d603218500d54026000501c9203031802c0c00f604100048076103e0400100c41140c03404000e0281d0140312100d54000c0a001087c8503039601419210003e04c0950b844516000303842d00304000859043d078003100c60048a1612140d01030a90321a04010411003540c042081 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 442753399 1250 442752149 442752151
    0xf0a02030c060c07260c0102012705030708070506190c0509011214010b04060e06160201080621071d040b070e0d02150702030f1623030a030f080c130e 66
    0x1000512503100c00103501c1104040d0b8044d10f0000c83c5e800d07041e00e403110001509260b101d0b00d203941107914281c040501e030041e5540b00b221210715490f1000303028a10b40342075031441c42030000140003100049201d400b040000a00b85224148080000a01440d2502c3d05401d4441e4810440301041040c06842d00e20751040d0401000021010008039520700740c4500741c0900c802c2070b0008207404800040c2881b81541002211035191400e03612686011b80c3c0394089803080c042c3c004003c0c1000300c504e0202d43c8035610000c500400d0700c40f4031140f5a92200071700c001a580d04841c810450200121442e540512204122591145030130100c40007407070750b5501d8102da607002a089a507510142c04400380c4056110002c01c0074281c2041465142d41d090940101407400441804140f402e81c4125071200755a032030643c580040f903d100030441801840810f0300061074039040e03480364041c45002c000c0410305074002000304d61019a0b449103045503c82092002181c45030811001170200350100400c50460410449 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 442754649 1250 442753399 442753417
    0x6050f040b28030504110a0b0301150e030d08090c0604081c0207090612020f0f06070803060103060e090a0309141e03120f030412080f06040905010624020f0a02030c06 73
    0x507070200b59242200180d0259070003540000360b81d00100010086110312000d550f030421207048042e91300d8400e203408036100500422024040f201c0d8100001c03030051a02c01450a4014255807030410b031034500800d0803004490072121841100369a030242c0c1032010488007562440c07405810070215130031005590504000d2610118420050001882c0001d449440050a03801c440011914441c5c0104035042000115207417007aa808540081c042da60002201c070311640c420780b90f503201c1d40da8000680c0101180d83c1700020104501042081c490000f19201802611039110040200c3d00d5107450200400c149444a0300154400070100040034030312105083d00c0301c0102200d24074244d0301c810100139001601446040f000210a2004000d00204880650305091a000c8007902e0450220920200081c1c00f2074007942e030790791540f000c0c80002e40041003c2c1251907458640040084c120202e10703964140c00400501509884000c1402d000c036550542940045c02050b1032020704040000c568842c801c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 442755899 1250 442754649 442754677
    0x8070b090a020406090b01020610120f1a011203080a050609221e020307060e06040b0306040f0c0503071209260d0606051201120b0c0901020a230706050f040b 69
    0x207a00c00595a500580010307040885000c83c07200820380000e441c00101501c0041041107105052120f012010f000c0b0100070b401c101040b41c052614101030ba0082c45201c80d011110794401d0012400a0060310720f03c03400761003079440c4101603640201800848409988040e800900000882c5042c2c184003600e000302d86010800414580c8580e9503424400b0030544003075461070070942d030a03083d840c2c103216200050510b41084040981c1000016030144900d01441d04400400302c04143d05840d40d43c00384000300030540f0200407601841e000a4001d800496545000030180c0754403001c80000c80c01171924159000c030750010900c1042541060110f039415025030410024002503080b17880134001e0f140280748545520303036181d903111228900181c058120b800c0401500810700c00150411440c1544454084291603c6400c1ca40040742440301c50f51010709881034240c0200f144100500b90a0100c0507860111501e251f600e82013a1924000e0b4420205003402c1807104200301c182c040e0003401e0401d2702200c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 442757149 1250 442755899 442755913
    0xf05040905210903060f06150408030405060d140702010603150c1707030209030613030f0302090310090321060503010501050a060f050327030a020d081909020d06020705030a170408070b09 82
    0x2002c24030f02002211a03012206c407072018440207003824103038810f2030b80b5203803c40ca14090421043c03995a10a5106940c0503200c0080d003501d0f030a036654052032805269810384010b50402800080c0030303000c1400151140000221012003440c524450001d600d0f05e03a860b40f04440501541410f420a0300808801c24903800f000000c030035030342c1841080d00c035242c40c9516003c04880d600380140070810510007003080c14410041c1d904160340c0001c0b43015002c0c00308840030035000d42601d8201c070305641c42c144004440b00810b54a094141158000c074040c1e65041e0000c011980c0e0b034031b081098064641c410513005c55041c120f0003046d83c1c4a48000e60303010b0804480c00d103c0b90186000d0141e00103c140b450501c641000c119000d989034140241038581035641b4105000d800d008420501e003000c40011894070543d508101c2086490380310034000d1460308500210741701c1d050b60802a490303500c440c40010000754031000840300c014004c1f9040d0b00a40d00007005900307008103583c0d0390300d2111018040440905c1240c2d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 442758399 1250 442757149 442757167
    0x60207020d050d140301050d02060318060c0a120b010c020904060e030a0e0f0108010503060105060a091703070c0807061704030c02040e0c04060e0f1b0c070e010f0504090521 76
    0xa03140d00000d41c412001420f50708403692000300f42c484030340f8080340315141c10001002140d40b02c030700e0f18081c0f42c0c0440340c01c0e6803600c81500c00c41403086041641042402517000b001500082c00f40a40088400e9440d51402c008000081000b2a20006091070114030704102c0d032800750030300320101544288225030000d078003d064080c07949160080d08080000401111401c4d01c40d09284084032202034082c20250001d50400000079100d0005003d8a40181004120700c58040d00c00e070a0301c0020701a90562010060b6480b40342c6d81c80303901510701a1200c81d00003800007a10340e40012100200c42040c4d499030b60035003401c1c0c40c00301c448270054415400c0041001c600c0c005603a5500c210050110540300800040e00907400b40300543e502980100c40d0203082400700b00e045030410714800c1d401000c401c030910b101440510b00c03d01e2809400c803404840d00c01d1240c003060120002d150349040c2c4070b198a9034130000ea5a00704210035201c1d03100000308590403c140030380c40c0c6110001104960920700144a0609802c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 442759649 1250 442758399 442758409
    0x1d07080d0c14010f0c14280207031b050102070b0309060106030c0c051b03011503030c0204021303080a08012603070b06010207090905070f1a2b0204060e030105060f0d0f06020702 78
    0x1c40140380002d6817061a8248650844000c98143d080a05414100401c501d090600080c80c00040308200310200031481a0910a201c4000916400009610049203000d11180f05613424000c00d405807049030000b04211400005591103040407000522180c1e013404002c8018292002881c3e060269070242d00d000150700b88200d640c10443d050070503250391000d8007007509445000145c00150310944800b400480c0c0d0051040b01b0380c540541d40907984d850304801210020301c440e4009400044041402948103038448121812075084400202c0c031804054082c0c840c10043c41c80d80c0e440f80d4001c01c01c000001e06000140b55201c1c070705005403034100ba6070303400d524265240520100c4403500001030a101c0d5254080000d0007801d0700d002248601d0031082480d000354031510074089100e80002820000183d90f51019a5016624030307400c0d9201d80c2d40e02c1000d092515070404aa2183d42030400242c102c2c00c0c54a030741c9442c1d520081c2100004e42c8203803039000001020709003d07a40d1075000c10180340941c42da = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 442760899 1250 442759649 442759661
    0xc07020a242703020423070f030e07180e01060e010f06030509010221040804030f0f0204050906040c060e010207080d0e011d031515131d07080d0c1401 66
    0x108a1180c0501d68105400402c40b000c2510010142811503012108a0304610121000c1c0c0307a0654001500060b00e07030031a8100c2c1160b80c2901040042c00303003044142a4000c0340007101c00e0031601c082c001c1c15a641040c0c0d0701c03014540140600f07a43c00c1a2041c501d480380b9003100d0200c2c5891030000503060345407864069540c0c030982290300610f5191034100080d0780e05115040d48410024000c5003085100c540304003089000d1400804030380b40a901003404d1120400c1120011a40b0030040c144415a510340b2040341207401e03000b64411403811001500c0110b003c03980c5480703031b58840c802d442c20504210707003640c3c2841628603041c1113101d110004148002e003000000c2001d1440e03101d030038508c402c900c001410780c01505941000a116200b121440c0c2d10f0014035501c1c80c041000e40070a40e903803600c521140c80403642d035501ea44a00300f090161b40f40c09940d071083c07030900880c040003042d0f061103050305580d40c4020b21540125501c002e03402190309204806c6001a035104e1070800406400350000c450030340d10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 442762149 1250 442760899 442760939
    0x50a050601051017070f021002030a29010c0b1f12050f0f0c100302070609150b030a0b0609070203040e0403050d1a0105030f06011209080403020f06030603060c07020a 73
    0x2026030014001071500d50007048802e40a450300301001c1a00329070010210102030411428440000fa84c12034031802400344204020011604544034680404000b002d00074081c186d00204260031402c0c42d0a503c0030310095000e01c0103864442c000d4030959241400342d0300c0207003641c0043e29040000c00e45e030b00090601c0790052002500b600c44203039160420300d00742054049101c1d0580d005030550151844013141052072103808403007109850b242d15070180c1c060f1251101c01000c2503d4102a60104480d0744111040c1d00c01080c030402c040014441030658a84e6420700140035000b0300070000f54585880e600c426400701162050701d040c50380da800e60714120342c01a10100c011030004160280165034911601041c9040b141501c00c603030359180c0001e062440090b003c1030018030804002070f1241d001d4100041c260722400800c2001e00c01d58140080e00f80c00c140000c0f4810f03d108151010f451520101b0b482c011035004029025a40320b1148404407503002c5802240c0103030040d500000d25854404c11640002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 442763399 1250 442762149 442762153
    0x90210140a081513020309060106020a1502030a20070b060f010e0d08160f03110a0f03111608030403020f040504050d1b081209100608061807090f06062303150607050a05 74
    0x81400050307d4200310050708010115400740d4801004100300d0000c1294a081d41000189d0340c0e201c2c100300b0400b5010703084144440d11441003007103c0c0005000010210305000d010344503915202c1c00200640c012145c0c1c442c0b030001d100100031030b038640b50186251012900c11340b401c03890640c9188100711040220740c0e065a1501d01c8103000b00515401c081c51f0b2480c000d4000141206804559600b003030882d01080c046d04000f00d4400d0501da100007045041d41c901d10b80b1070302480d940d41c3e580140c3c1d5268000d010403030241d402d81c641d41145061a020b80350080394010f014102a4150301c00c219203902c0c0303079500341e10f0032840d1a49000101743d22070b0003000384140005898066107041480790749031071186d21041c0040341c54007104122110780440c02ca90814281740160000410f01d00b8258031301041508291b0b041c51500403000c17100e948541c41007040712a01c4d00c1d6200000040c03281440032000220040314008400c00000ba441100c2d11403480040c00010180b81c10400f0f141c480c50300c0c00040341c0d4110b07542c1d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 442764649 1250 442763399 442763401
    0x7021f20071a0f16020109170c070807150804030c060509100e1f1e060f1403030a050706050612030a020a03030b030313030b07021c03090210140a0815130203 69
    0x84042e400540c1c0c44011104154480c2e4180051600800b00000b400940480c107502e00c8210594070039080048503982240c6044041d818110341e815859010b4443c8009078850030100050ba04070104440b4121109182c40b220842182082610411801842101000034044440000a01e9032141074051600b041c024090f0700410b0314080211443e0b600e40201c40e40c8086600c49003d00810180355840788803080100300300200c0c4080c4100e81c80f4141003440b2690a19030b0124003070700d104065104960030b404d409100340e2000402e060300c80c030a0750040b0303000070700802034580480d00d0f0b0341000d07800440c043c1151404004a90440c0d04640007005020016044250507006043d45800b079611901e6080b0f014500e00824504c450f91594628403004004800d54400529900c1c000d02414052540099000c1d000150100008004110121040340718000c101104019240f190300507000d10041c03445c0c010701d800048070090320a44001001d007005044003100400341a1a80550003d0003c0340305409a16 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 442765899 1250 442764649 442764653
    0x8062b0302070e060405010b1902070b07050a0203150705180d06090803060307090e0c09060310180c0911030c0304170c0a110d05060613230108060a0507021f2007 71
    0x20043c003600507441130741410014861040100111050110107040e41d1410001d0508168104442d540c0a01200c540114401c01802070100d4800e16061003203050f54002c00d1464810040c042d41610f01030005902030201802c80d0400b08003040c140440203001100401c1c1030341d145002e4031212103046900c40c0300807007405614181044400003170b11034140c061054407a01550180e494132400081c601c142612004030f01c0d1501c041c8052152118120001c1c09072404002c3d0b14100742018000450310620104000222508944034490a9800c03002c0301070b00c3c588035004a40e100c3e800c044d03c01d07140b0300c290440c280e550034507100080c01c0d4a85284044e001c0c00201d41030100b0b1121071183c50038007c03a100c0d02c541d80029000314040d9441502107c14041c9081e2205911000341452852100d800c4000703940b46261400d60340c1c1c01d0381200d50741d9080b10401e43d1081180d0042d102e0a64026015901032419949030f03903080d0029410403041ca035400244503212411420280407224611080680d0009007042 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 442767149 1250 442765899 442765919
    0x40b0408060601081b18040204030602040f0e1e06120708011a0301061206020307051605010915020703020c010e061e03150a0e010603050606071208071d0108062b030207 74
    0x20740120242072160142ca4942d0340411000000c440650786603600040b1b98502c000440d4840c1000034014008640f070316281c2c0b9220000390300c9406625424003008000103501e00c0400c076068400d4003800950148008044000c0382103040141900740d0101c011550a003440d4070402500c030090200310000704000c001518080030144c4048012802641090820302910505003001c12150758040b00042e1b480d40c9071281284d09018180900b100b041c100080c50f01480415082503191714000c0741d02d2034006480360109001ca1191510040c0540c00050940c1c403558007c0344002a4030300040c0c1640d11344820129206500c01c49101c242c01c842c01701006124000d04885540f5505c01d50695403581414103117803405a80040c1403003510105a00c40b000200a61a010141c41c4116808004020303124400743c0e0107443c1803421640c000014040c0c103400e00c42842c100e002011000b506848030003a54032480c00f4010407000e9003c8840c80740746a0007081403101c1091040040c228001d40c0600345690415107552 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 442768399 1250 442767149 442767151
    0x120c030f0e1b1002150603011d0109060c050301140f0402130e01080607050c06011202060405091501080f0112140313030309091401060807030c14160204050915071d06040b040806 78
    0x16000341c600b6103048202c00d0300005c1d103200007500c1c13038200d5820340e459800103805801e40030720b810000c03003401d11500c100507415008000c4a0380b04000900c42c406030079a080703515010912030300310342280341901006203041c03114204d40c0900c80984090b140c440400c14a07040240719901000300d00416500410842d00c00b8880690841880c1c43c00701c0c9850040340c201503403513506000f002c1503412206006011075a68104a400814000c1d065035031500e0b02c1900107800b41c600c54421408075404c0700001d12401030080f5500c3c1603d00545600300361160a480b420b1003200c0084404516200030489802480c28441d002001180b003075407101780c0c3c01d040904000030b80d06049c9000240c200008018000150410400c0707034010101d2400298210446504441c2c141048a0110004000190004011054030500d4407058026101404030361140820166585032800103040b40f07401d4800442c142600c01c040003082030441ea00c601640314501000923009900550140704e5030080020f0410120000307020007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 442769649 1250 442768399 442768453
    0x1e0f0d0e1204031b03050a061e1b050f04031b0315051006080601050d0f0209030106080a080f0c100e16170c090718030501020403020102011803120c030f0e 68
    0xa071449915615007141d9a0041d4040140b01c0700c07540711320401d10000b803c407000065030080d080b90a0181a400c200d0014880c103200c5100b0081a6900c465081449014a1103441c0d00e0100c80c0101d0080d6040440b01c540026818141c582e004001c00408500c806070340c00b880e50003022400c20304614601e4000030703601000d4045000103003060100005080418a4001142c025050054141c0c0d540c0c8012105841090080d524080c134000446981540503800b400c1c1d0107405034000c220070b0783c0b200d11031a0f40c0c41c3c016034000e04403042009181039402540004e401e4034905030301101c074958440003441c81a01e41246000c201c0764003c441d002c1c641050b40510500a00c415100c003082c40025a4000b9103d03400e600d042c0d4018a03050010a40c100d00c0760800764401e00c0c0440c5c8a0a4294070f91520f0f9000c0d600030f02c81070340190300301030b0043c04948240304207041b190350503121384150390350218042000c1d0002c4a003000c24513a68007400d010720b11250240300340ca0001440a40022070022403201d4040d4184240 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 442770899 1250 442769649 442769653
    0x1020102090a1403210f0304020d151a0a0803041811040303022103010501171f0305101b09140402090a03060f0c0207140105032e1a03040312021e0f0d0e 67
    0xe09000c2c00284400c86e4843d00c510b0341e21541d642c6d00d50001c11003001016100805140940d440b000c030f80c9165900211300c089c0c400c01c010207090002410804c40142c1030090740d5854104100c200710716002442d10b4039081c442d10401180c016000c4004800640041e401500580c12202c0507090060002410807180481446124119414040000c2080c010000060001c2003e1000300c0c1f021350518030151000b4a6003036040310442c0c0c880c03810036102e08a00808412881c105803d0b4141c01011110394102c881169079030201d40c1d8a03025580b0881000780007807a8001c0c1d420400c0220b183c95020501000c1c502820001c03982d071803039200e00001c903660342282c0b001310740103040e003400800e00b6143c1e0081a0002440c1c03841c4c4946418014400da1401c0005c011010314034200d40000464188194204594220b05c00018051140142010a01c000c0341d009000488042050b208804140d01070004085203c400f09980c0c850007001c0c3c100d41d0720524540c0301600d804981e07240512030a0059828007515400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 442772149 1250 442770899 442770943
    0x108030d0e010603080313150203090a02120102030105102304090b010e09070f0c061b0206040b070e010206040b040809100e0f04090c0e04021813060501211101020102090a1403 77
    0x20f0b407517441d00001e00882141c41007e921181400f0007015904089103000c18110355a04040c0c050031368466003000100d00030400500015514041882628101e60000d0308016000c481c40d80103e850100c403d001000c03840c0c02256902c14640d03d400980064256220b00007203090b000b41c00581504008106644901e00c02810400140c1c2c2c0101c030341e51080501c0c20301c0d45491220b840d01a0142c003480f00d902c4804019200c4092943d41c1c009021805140105d6282c182a281e10340202c0d04d80d02015813441c00341c0e110390701040c0041c160301e9809502500566615003002c039510009824a144455402c000030106400746480317103800401ea001c800ca00b21801c101100d003a0b942d05030341c9242d61042d41111a41c420004040d922500f01d0020442c89001d5503205c10300e4280300c032840e0180e01502c10703140145024000f01d810f0714120811944443c00714102c050070f800d566136180e0344500d441030b5241155000d10141d1102e41351081410082c0c03800940d20104a10b03c44e050514208424814241c444a400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 442773399 1250 442772149 442772153
    0x6080d121a0402030603070902030c0304030912080a05090a030605040b0402010909060501120e190308150f01021902011b03030f0e0601050a29040b0a0e0f0f040b0f03060108030d0e010603 82
    0x808401c0204060340c0140c0c036030303844600083c00c20307100340d2080c038509000008000d01d106111004611070b030b1194940c020895191014001d00c800b04040c01482b85c0c80801c05001410b000e40c024105501c0018036081c442601ca41d9210280d40050314112981354241090004540c3c101a496000e0844a48100141c40c50240001c060300800c0c107001960603a80d20075800c41100c140318184422800d04541c00c108001441c000780100003c481400c00394480102894903444c28034400010050140e0007041c0072000b0219020f034184200c00704a050040c40d201d03001410713840d281c1a0032030f6030107034070005a4070741c1034034510081d06e00309802c11100b0f402c80e0005006980d00d050101c8142e803440b03400505031801800840014044240314441e0340100401c00081e410000c000425900c0ac090b07940356242000c190501c031180c031b00c1d0806140d1040c94010201511f0501d1f0744164030000c8020b0070341307142c2007048011904081082c1c000007910780000644500860080c002e103151692404020401e251841d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 442774649 1250 442773399 442773431
    0x301140610050d06080708100c0c0b0406050907050306070c050c0a031a0712050412030e0c0f0607050109020409060917040b190c38012301110106080d12 67
    0x41e076010018403001064210404000d9448030011388480001c0758059a00d03203403800e98407102440c2c1d4100315410680d105403264030541d100a803650340440394a64603207503580d1791405860014021045880354800004a0396004c000850003a001034680403200d10050070a0340c104518103c1d1580150340d1150108001025030b0680c0703c0f00c0001d044080b8031511018401c82d04801a42d1000c403182d8208420f200a02c20908101e040b8140140c40420607280e4402d0150781300d22040d08101d07440007a4107101801803c0c45d40040c00e15522070000080c0310b9a1503400102140c0010b141030b5102e0780e0311900701c020010750106002d8403240d00c3c04101d0800b0300e026800d5070244184070403042002c0000c405801c03440d024254604140b5800750421041c0c01c0b103d007580c0141c00882d031a03076849000d08880d001c1c0c0036140d815502e05071011015200c41e0005440c640700d5024010060080c100a0100b01c0000094000c0c490035002c4d01d0803001810401d004000007d100910503d1054003003443c1248440c0c2c81c030b801d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 442775899 1250 442774649 442774669
    0x6030b062d0402070f0609121d030c10030212040b06150301080a021e1804030801170703020409020303121008010501090c020618030d0e0606030106080304080703080315040606020c03011406 83
    0x2c80b0056560110740c0343c940482c00390954000c01c22400d01200030b00300441c41c810b089000b04150340d18001840042819015907035400c0c2c06d203406070419800e01da8036051a0320750204c458082c1c18051b00d441cac5400345151030410201c905460001d44001400400d20345007412030328041a2211090855061510003521000030b0140244100038248101e1114600826a01080d850040868038603040f21120507408100c01c0700d08500041c80b12002041c49451808080c030000041c0c4000e1807940d040d582404018080070a003641d242c8014001c01f0300300d140f60510603210342c181d0058214180e2610118500756041a00300700c0c0030340d081030304502c102a40000d682e540a010045561003020340411300c1410343c42040180001a4108031b0b88000c4042c000030000d001d25002d60080241c907545080403030f140d00460154804980081c00701b00042821a00030310381008008800d0500d0b003a08a00141c11180c0c25440800541c2110414070101d00e82841103030a00c0c00700c0c00490050b450000001003075030750 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 442777149 1250 442775899 442775989
    0x4031103030c121602041103370e0c060c070f06021f050a110d06061701030201080c0c030f04270b06090d03020f0105070816141602031006030b06 64
    0x440400c0413807403504c050032107602d80c0d60050802c00907030401000340c0030954000c070b8421303006122640345d2055030300d00f9001c2400340110702800c01c2810041c80d400100030b00308480380e40304580700c3c41c01c07010015624a40205201d5401500400c41d10f46890b2900c003d0504551102c0107540001c0c00d19010680b0a681809501c01c02880c00a15a601d0343d80d043c000f00b9404204440e00074bc0801d031450610141c1d400701003618603039141c98400070030384100050780d102c0c01d000003400a021040400d904141070b0014110003441c020650341084602c2c0c0301030040703030417560010b8480c1c1c65403c190000f6a0074201031504860400700700344403151424000c943c04c0d00c030b03032111140035103140c0616205143c428002c0f2400802c002c40203101c0d60405100003480b001050f40c5680700c540c510f00090441501a4401c1011061b113019060f0410148500031030039500c080000740c2c0c06001d00001b00e00080140d20585001c0c601c9014814000d003401f8090003100c4520821040080300700050320803900d44013800e11004c0d05 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 442778399 1250 442777149 442777183
    0x103020f0117041b050a08030d180f05060415020a0f08091018020405060d030e150d020a09060306050f0306160e1801060206060f0d02010c0303110a0504031103030c 72
    0xd644034004031691020019036032080c1541109100400c07102020507114041c4035003403110038944480130009550201d11600381103900420041040d1b10940d0808071071a8001c0e030800c0c419080381d031104d0700d482d050903d0031140c1e1f0b00300c03200f00405c0010038440c10f40c401c98418811800c00511800203007016007900b000b41c0c10f001c640000510821000c00c040040c5502c10344083c4011455040c84584802a00c6400c0784980d00304000541a8104120640704240c0c04d0b40c0c400d160214114107204000802c0c00007440c10820030041814441c4035400108441c1341175039142c400c0d0a192080040c11181c95802040c8188000c10039100f0aa03000603a40b500101c01c1c484a900b2510108426520b80000c1c021031b5401220345285050120000d01a507812610540c099903995500c02d0f00300011900809000c942c0640e96441800141d4490150104070510a00b00050b9445e07640428440c66000a1140c20005000003401d00410181c0e140000c44c040302500103508040b51000c80f952150f078010b1a11000c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 442779649 1250 442778399 442778419
    0x30d0309111e040f0902040e0c2407080c0f07060809070e090c03011104080c0a0e16120f0c09050406060e190e010b0d29040c1707020a020306100e010302 67
    0xa000103050382c00342c1d0400800c208402d0250103c080040c10070b07100b060344a103151541c214051800401d080d00480b4008151160b080c50501c4001a1354805404041320010240040c0c0005007a140080c01c041b110000103001c4030b2070444441e442c000c0c880d0400d1042200d414280144440c00192600607600310b500c40751210750300c10304032914121610014030b5040d800e142580103107100d078074010800d4079074007010780c2c03000170207041030000020701886504400c0084100141c07a0603401722005102003100e02d81160700109122550f019921402c070300c0041107a0781c00c02c40380700d40d4021a0420041c60251000e02c0b080746480800740954804c0070b2950b000780c0300303040f00d64024040600e0000c0a0a404501103040f56160f030178985940d00564209499203107403180814120340980c4520f0b40d00c4202c0402c0388100303900d40302880080c091a0150703500340465005480e494a96160420b8442d40301540142010141c40c0109441c0003409031100b07000290004017072000510400340b0505494040e00c01c4405 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 442780899 1250 442779649 442779679
    0xb0a1101113c1806220b07050d08040f0b0f011503140604050415020316090b07020a0b0a0309140a290106050a050706181b14040504050708030c0c030d030911 69
    0x140402d06003031254025130010740442407445900032080c0b03100c00000a002c209450f85030b0304c055031240d04005003881c0d100080e10000c4600c00c68403558001d106095030700c051140d565620255200c20303036888072403099401c01840030900100040703800c1402d074034082c030a024a42d1304a0341500c401501c041c0c0150703240d000190030720010314080b4041400070741e811035803450941c440d0500c01e40c254038484001904d541002403c4000300094409682d001020351500360700c1d246042059501c80003048060540380c1101e0804250750507650301c2c5c1c040c0454040c060000d040d2410001176240080401c0072003d641140402495100f07000c1c074150350160030103c0d520640f800301959940240007004015904055000040f01090140042e00c3c41c4078034941d0400000002e11701c00d00030280d00409810f89907404074080740f881c098000c150468042d109451078280c880340c45605581c8220990120f5500508040500303050030070064868150310301d001c00443c8069500e82c080c618030000260b08c500394420728980 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 442782149 1250 442780899 442780927
    0x30a0507090308120907050609030d0f020709021824030703020a0c0c06020c09010e090c210d05030f090c1e01020c0319061112010b0a1101113c 63
    0x1c05980c100c000d9544400311803141660080040701c0b0400f150148207000201400e00d542951146200100905003516044200301c1c0c0c001c801d203009104502c21620002042003c5100410b030600300030416202d55040602800289829031421404220030941c040c490343e482042520b8000c0064500540d460300314000450b0060f80303050300940411429040015081d4000400b248150000d554000041c2ea840300c0c00b07610b24804803030341d0986400c0340403058024581a6404a100d107000a66018a444210f404615240d40c0700c00d0000403540010174015242d5000e00406c0e440114175004025140c02c00c400310b03149248035036000c000d090040c1c400c00d02d0f03a0300a0100410940000d01202c404c0034181c40e4083c006020340c0e909a072820314008444600300c016008a500202560000030226440c00801c0582644410140310402c405018860074244003809841608054500b0041e02c407000c0740300f80d15840030050145a144c41b03880b0340074640342c00044582c0d02c0020790003160680b01d80c00840044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 442783399 1250 442782149 442782167
    0x140102090a0f081504120e01020f030c0c01111207020603060d0f05011e050121140708071409070e040f06030f2108040c0302060a09150f0e0a0506030a0507 68
    0x1c0d405588a0000715908502e1080309048602030421101c1980911000804807081901c0282c0090001d00031250a40d000e10100801c2d40418030480344c00c0707050240c6103804c50300f1030104000d642c0c0100c2800341981d81e000ca16442c00ba00d80d07401800c1a00350b490000d00d0144a0000001e010351008000103085a544c00400d0728125000310102449843c94038003913000381800c0c411083e0504285050048507109445480c0c143c07507015171880141c0b003410340058119200180c04031501040700102444004091020100510b016001025403500f4503070688010341102a15038060b859810030041d00c99404000314100000684000402c008107264507009000150400f41c000090701561a08201081d610301011090b0020101d031289900342081f9040402914003074000c8000303a206201501d0a64010152445581400c0120715030703400900c1e040c004804201c4d00400e000c1810066100e81045002050507811220043c03024140000240e0030f00014001144150396000050140d030b02603c030761 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 442784649 1250 442783399 442783417
    0x703032d0f0b0d0c06020610050603011403030f1207091a03130c090603150f050c0409110706050103030203031603110d020d020f0310140103061203030f0b09090a060b0a06020a140102 80
    0x85160f0300410b061000d0b407107610340305940c01031055400080f0410010424441541c0c0003c0c402c03465a46011503600c060101e24010641c0750000b003042200001c103000003402ca0301d0303221b03032000100d24200201070075511907540a43c1965544a40300706000d001d14003105ea00003001c4140035410300180c00c1c1401c680e07840350090403a0920342007011091000d142c0c80d43e2040004544c1c2400940f600802c00c070190340c800c0d80d1108011000388028400003c25400454049113407203944c03030030710607603881d18401d03140d0a90044d00960800800e110300c1c1166048444500e1003181018088101142120745192156440010010740d01041c4400b400086804503102010f03001c07612501c0781000364140c85003540d04c2c0300e0306181e04c0d005804031303800b0350090040c001156140030603081d000889407000e8010303111908000c0134403076552801100b56a500d6002d580070300311400c0148802071861518204980501004501c100b041c140c0030400c041d400140d80f1483c50b408010924440280c0b40c200f80640116030f40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 442785899 1250 442784649 442784659
    0x723120d150b041208070609080c060a090b0117031902010e1c0c030302160b01030b0601031a060d020f04091a2b17090303030c0703032d0f0b 62
    0x1010946104020203040ea10059520801844032690980000c0c09468498450100030610003084050b249610f01c0d0310b0325010300c44a520b403240a43d01d4408542c04402e084030f00d060040f40f1341440e170b00100505540f10220f110100f00d4100c031030329000038401f414401d00800e00c0200000541102050090741c241c81500c0d0103010084400c0d100c085d0203407141e02100600f41c460f1b001c0100e0506a14000708e02486900e84a0542d403c5c0380d40c508030065446505d4000b0040000c9401c800090710f0246154000c41c0645481c40d5507082101c001070540b260303000d10702c8503061092901e129954480003103846c00900d8500040c0e5807140075840f80348038010ba81c800c80d00649442080e90002c1180302000103c41e00880380c000380070700600d030041d05108601c580086811404c4031100005180001c034038102c41c91494145080c4120a0300092035580120b4076000346290100e40f03c010141c040c05402000c0820000b0115042c0228000c03036001310b411110320b4105034844021452140b6550310441c40c0c2107001e08 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 442787149 1250 442785899 442785913
    0x60507050c0f070e16080c03060a0b0a02010c030f141609170f011b0507150605031b150f030705031e130b060a05030d180b0301230105030c0723 63
    0x10b040c584484052241c1c20700c5010340d00001c1e200d0110041c001074002c00c0c07070301d4401060b1201403140280750002040ca135000700400d400403a55041c00c60142c00301c00300307036070010409080c0c00341c005050751004006500010709241d95504940011420f0f19401848840300c1507036410141802c841c43c174036a41c800b0010a10350310007012001408101c04948030454402441008034440501440907c3d552282001400074803002000401c8a00080c52425405401252070f5442d8800a4105001ca51207803e4807840c84407101601c0c1888541a0300440354071900b0b5090803007204440c0a1480014170300810480c0000000f40c5c1c1d8440b45640e5140031034191000c0170070b40303005005940e036215403030425103840100c0000034400c0e1410f1900c480560740c014026082c00107060302d00303039800540340f14003241c0c01c0391441c804a071050741100554024143c0d40d85289120106042511514041c0030174541000010400c0044500c003020032a16801d40c4155641c840007820b60b42007a2450142c40f0282c02401000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 442788399 1250 442787149 442787173
    0xf020d05071b0e150f15030402042904140601090605030a060f030602030f060307060e01051c0c02030913050f011202030a0605070302030a06080705090109021608070c0609050f030a060507050c 84
    0x40d00052050340900c09520a010040c001c00c113428002e0034280346e0240010040c2c0700c2050089000e190010320140010030054003541c0589200908140d998040000f000c44050544c9028020403d0805000c01c0f524900d0419100080c194a65805078000f0f004000001c141d1010079980100001c2c0180540031108946919021019500554140c44200d404c00041502c0e13140214090b02110340544550380c0403140f07140152190f0308041480c0700a001c922074125050f4040c0c4c003680f48075803c00d601a650703504100c0c041280d112140f1111540c41d81c502410060005001c002d0070b81541c00074455824000813501c0041e2411000201c001d20f103600348400e200c10550507801840c005e078500e0b00140001d980740c484040c1e503050b59110321a4040e065030010071111a45500404003520090090301201082d0b444410213588440303022615011500410400141d0018102001d070070100c8000b00990b2031100000c0d910030340b0742000741040351340384080381c20076000300100e03903480c2c1c15007040d01c40319680b003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 442789649 1250 442788399 442788419
    0xb01050906120604120903021906080c0a1d0604050301020703030f06060302270102070e090a0b060a06120e01020405180f0609070c0f030c0b250f020d05071b 69
    0x2882828058804031010440c140740001044005212000c020903a581d00e54580c0001614807400140c00d2044010002c130260b251400300c0c80844507031754500c0055a26014004007000760040028141c0710040c80041e8116900104084255001d074000d1f0700c82d5010080010514440c3d540415455032000403100e04040d01600319178449001100f0810105903508002d0b401d9104a41d208104007002c00c4004001e4034001207030356480d58040c81140c45a0340c503070200001034102a181103900b580b00c00041d000700312084141c2c4d54008401c1e17a841201d140780c4080078002003400c10144140e1230305d0703400300c4910036000d42c10340d001020020000c3c1d014840c03c0305080742091b01590405880c52a280c0040c545040810714a405000d050f030300c0d44600861604c0f4101d946800380720403000c2106800c1404c002c2204108117500a80005403440144011031080115045c0300b00a50340500c1030300f210141c0351070340104002401160a0805c036680780180c1c900348800f0401034410304468031a40d84049420720074 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 442790899 1250 442789649 442789651
    0xc120a0903020c03070602030f0304050c09190605011b02061b070924050f09190c03020c010c0e06030c0a1115091002090906010c0f0203011a01090f03050c040b030312040b 75
    0xd40079a444a0244428144c90705c425003e4035003d0383c01002440c01210b500c00003541d10a0080342910f1441c04904000f5400380410344202c9004052108059031720031b203d124004c0200f0003401c2500146c4001c81180866111b1400e029200d40004906143c0d185030504015642e8050701080c3c03201c0907100c000690040c450f14094560203204501c1200f0100d8065101c2e0080e1380004058880c1b840c0790000b0003c151074001e00a1a00c065610382c03200759030906025202c541911902c0241e12841202d0090f802c4a9030920f00303804004071060311a00688412044980200000b0316030703595200f58001c29075010000d201c4107900c610400306149010040c0e085402d005903800ca040c0c0b8142040c643c8100180d0007030b07008040d07000f041707800482d84c00e40c05000060240f51080c410100010701940000742103501002e802650004c0c102115a115a480003100d4058034030300d500700d505142140c81d41d6550311030368185107004590715140d40005503420010b641c180010200003603203130303d458a444000d21030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 442792149 1250 442790899 442790903
    0x1406060705010f0c3933050610050702010806041a150a030510180f1d0d09050301090308011e12080c240402040b04060b0a0206041203060e0f0c120a09 66
    0x10300b80d031200500d6640365001101c100703024825041c494401e0303281e03020800d02031180b24503146e0107440c4000740300200101d0a00e0201c22510f000501d854603105200c02c805a0b0803619007000410000c00e00184c1c0c001d141d05d0b4000800366000154034030703002c0c9510181114075030403036841840c0a415003000d100c05401003c24804a03901480545ca68082c2c5513280340c114011140306d0221640004072101e0741d0b03400310012a407480030126541c1c1c0c0d03142c09070944105400210b1516040680009681c0d03030001c020100508045c0c001b00000486a1801800030006014020384086020f0082c1c10701007904c0b0320100505103150b0361000540781442c201d880c0d030b440f128070400c440c0141d030940f03206c072010001032815203410200043c000b66910307800c1000034001d48044a42c4076540703d03000306070529183e000d041c01440b0754008181c076042c94207100e851442c0155044007050f080040a1103820f4551802c0768010560888407213064868104046050103550780d03034200340030303e07100700311340032101e600100301d030314 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 442793399 1250 442792149 442792187
    0x12090c150d0f0902280504110d0e070b2b02030f04031403040206030114010909240905061c030e060a0c03122009031219121406060705010f0c 62
    0xc81180390b80c150b4046950103540300142e0071864000c5c800d0755940f00341e060344200c2c030015025120700000302112544040b83c40d2030320700840c80f10220f840b0340c441d404003800d58a000b001140d00d0148400382c18072a0101e541c3e04040500400810a040302c00c48078203011448034155205e1500c5009c00886000c22a015400030b0381d41a6400454640740040383d002e81d4001e01841d182d42e007006e0540c1c403890280c07d00700f0b04120011070006101c490070710071303d440c401107421810203c101d91854120900c1d402e4100703a007240d03e00018811705da42d40b0f02941501c01c074250500c00a0001608050754400c031104042da801030750000e050300c1d16941c03000c2000881032280c0c9503240c18410040c0304004454038044000410100c1e43d04c00c10000e071440d0042d02c3d01c0c40e8024111040040200e942d8001c640080c2440a03e007001044203110181d0030054191180310749070b0007041908840420700455141c0500164010385000955400b48602904005991410002e0034010910040030007441810030201d0030050b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 442794649 1250 442793399 442793411
    0x9010b0c071205151f080609100605060a140403060204181803020c01030b12010906020a0201110f030c07061b27081203060105040e0c040906050109050612090c150d 72
    0x302d6900072000c0d1040b90401c1c01000b001903400343c5042c10301e0028000d0b0032200b000501d48081468000031030006000f484000c0c00031800e00400720303481c050b42441d1400815052100c02d10180d140c400c01da8180b11014504003489100140c00038849101c0e64102810750b900008000c0b40001000304400115041030f9410480c2e100c400d21501c0081600c000018010780007208a0310f1558481d810408068130024000a000098200b8075400c41c1c094070800c5903565004540511407940a00c644a214400052014175040144800060500c4000c00707108200d0340114034101403000d90341c0014052a1411010041c0340e0183c800a0011040d030500300300c04a00240105085105140650f4100c1d12130704001c2040c01c001143c1000707a81c1004222504015041c030001a000b000e480d02c0038010b1030303600c5042c0c2d0313039500b0302e10720b079082c2c8204d500804e05010306410200126190751040700c400300101261410940c4521511504040300d0a42d0554803400100341001000c03d068020141140050001c0000e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 442795899 1250 442794649 442794659
    0x6150f0f030b091807080d0903110906030a03030c050912010f050106050918090a05070e0f1311010503040201020a02151b0601120308040302151602061b0f0d0b09010b0c07 75
    0x2070300c2d030391420140c002e4003080c007090341d0b181c0c001c070388280030075404082e245440d40340c1d00c1e400d1800720101e0a02c000140a00010418007001c011502100e02082d42c2c800c12500d030020100fa507980c01400020101561958401030003842003050b01d21401004010700c07420110488018003800c000c2147c106818502000040d9140c054022075803000009003010545003117402c2115802c00e030080c03410b9264012100c0880c00501c00344503020280c00000030414560500081c64060341000500d801c126408144810700824182c3c80391345030035182441c1c2142c0d240c0e0740d440103d01701111500020f4000501040c031040a100c00f0001c0c00030030b030f801440804a9411035510f0b0f40d5902086c418501a8102220001c0100e1300c9404c1050780240240111035840c2d190724090004100c0441d5406801500b1500785001654140421900301c02d00140302d1044040011408045104400c81105902030014035402605a41d4209005000d401001d4005940c1c0d102e440c842c25602c4020251128040ca07000411 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 442797149 1250 442795899 442795901
    0x302010b09160c030203070f0b0f09280302030c0a060614010e0d02100903290c0315190b0c16050303071a0c090913021e0105071506150f0f03 62
    0x449501403816420b8250b03907025041e01c003511000b005908501080000c04003213840c0f42003ca15a0303205074a80450741ca098180c0721440c0d0341c0641039221301e400000c0103501c002202070604007040c103034803005011400c00d80f4080c1d145100d0348020110034003034212803806100e0b4a0748440d044545a07852003a5000d410340044070380c030150352041c9921071525541e02025080001e42c00f446c0481070308011007003944907107407000d4242c0305e40050800e1482509142856400e0340f2560340d0081c0007842d42a055040001080700311070106c14005015580c007072a0381001d1610900e0800090010402c55540d0f140c07180b04003a1210300c11003000382400f010050000346410000101c039142a0001c00004083c8407081059015101c05480d8800c1c000040c00020f00781d5580b052014040c06001c007681410b174442c0d2050044600003101c050480800c8040b0303c0c58540d0b0010200c032903e0b0303130145a1003055402071750884006e002d03d0b049030526508502d03a00302101d80100380300841703090648906075503985442e4220 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 442798399 1250 442797149 442797151
    0x150919030201110a02030a2019032021010f020a0207030507060f050417070b030901020d0b040c09050103090204020408010903022103060604050d0f201305091c0c08040b04030302010b09 81
    0x207401d54407c854440c08540480054000300722505284012052920001f80b07031490014400e0010152080041081250b0000b2030701185940c254040e4810045600042200700c01e071207601d201c2480c20701594400e03e829030211983d1001c1c1d2030111b4940b004060f00941c2c8907039074007080b9903d21400c500850014020071151110600e01d64800e4681030505a0b44840280c43c60403945680c400e0b044003003540520900614816200d5000058a940c0001c080e582520481400180194900320440b00c0d07040d4000b00341d0302500c200303080114080c049071021800a228680c0080000d5203090016020198007007000700b086507032405202001c0f00c00c90101f1341d0130f100644606500c440c081100304031904001d0042c0000c203025035180d400e000c00c1c2d92284820508030b06100819558201b146000500d0302d40c10540c040965400200b040d0714101c14010b85c1c4884184008000c102106c552110345071181802d100c0b800d60002c0b003da2030307907502c2a03402040e401600046003d075003850700044440c24007010203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 442799649 1250 442798399 442798403
    0x105150307140c0607121b08010501031116030e03160f0e070302120f0703060e040b040602030402031f02091201180206030705040816051815150919030201110a 70
    0x918038603122500261110490074408010030310052003031a942080501807141300754026190402000d2400d07402400b00c40440391f100302200000c140300c40703045900000c1941513a0702800c0014601440c20100c1c0d54070f00407001601c1903140d8100d41c849c1003543c00105541104000d80480e41034a010040c000c4140c2da05005017081c605e045401040890231203030800f601f00c0410f04005103040d070050040784102070102c0750341e01020414014814590b80c580705540040100d0030450060b8107107652000c5c0e40390400307807004d40515004008142555424083c1003600058140e00c80e039040042a00c820107500040b0344144507130141805544140303010700071000e50a400980c030003001c1e001d1f5420850b0f286c1024248408002c0140030104050710108981c0d0810201b402d001200140f401c020850101d01ca618840c0c40c581ea1034007404021000650044010b5404030b500780b20148088185842a014142d003030303a48000c0000b4510440e000e00305891055a00030307a1000651400007035400d0740d4003070407140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 442800899 1250 442799649 442799689
    0x2030606060f0d0b150d090c09020c06010509040c0b040609210f020d03030204050a030b04060c051215040912081515120901090512030906060405040c0b0309150a0609050105 76
    0x207000d0000f001580084d11140d030050070140322070012041c1c19103d4112000142210f55944929001d000360303808010010a50304605616103d00c01d41c2d1107031101010711800e801360000c48041010040461018005003035502c218544442c0e48180040100703001e44520369170014503c4c3c0d8002e00460f003195856281c2c1c0c20041554179a0307841d900b40300390145050381c19000c140d0b00f400b0115031a50b46001c2c541c021030040e00441090304090611304100c0e58030016030418404208100003c4600550640c1d43c0442c030300b691810489072810102e806000401e40041400010303c003501003031500301000030b00400c05041c50f1070105103500c0601c101034100340c45809940e14240042414003a01010182d88865290000315131021203546491400201d80071080008402004100210008000c101d90244040b5420310032800c2580f10101030b692f940c0600143d10304000001038420000b081804411030108180154038981890400c1c01003955000b002c19003410900001224a00807141c90141101002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 442802149 1250 442800899 442800907
    0x1205130203010c0f0e010c080a0e0109030501050112020114031302091015050c010f0b06030c090a0b04030b1e1005120f07180c03050402090c0306122d061e100302030f0a02030606060f 80
    0x50a0391032b00c0710801c031303141003000540300071000460070f00a081c000d120180c903580c0c0190103440050b040c10034100c03803060506428010003526150750301c05100100d4040d1020b281d25100c0400407000200560003480d80668070740c080043c2c5a921000a2035180b24102c000c201160006800000751500d204020350f0001c001c4c000325018013000d030000e02d00244c0c01460314102558502c241c405a4209500503104034003030008000d21102c1d180c180411207c0007e01d0004240307490314400100440707a00031640100700c4001d80d60880d0b4020402c2c030000800c0d01c411212031030340d103150740003403910041c201d00c0000c1d080602542880c1d0090003814000d5500804070b0712580d4482c40d0741d02041d080102016408183c0b11080851044148042c408640e000c4034180658903900702a610300c00c0c0150300c2600c440c0c0c4138200f0000c0d8502d400390250b00c4108040301c030340c61a80b80d94109012610190704043d41c0350150061440442000080d01d414051080d001e0754050358034001004120b004007100110135032402c02c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 442803399 1250 442802149 442802167
    0x1006020a0507150302070f0501020d0b1203030a0c0905030f1f0b130f0b060a090509070c03020312150a1d0c04030c0303030b03031309050a0f020a1205130203010c0f0e010c08 76
    0x1020072458500c0d884c00505044854403003850b407201c1d042c01640c0b00c0c0d41c00030b00c414940352a0b00a541c2d03510740580c0c0074864001000c00650b520b2000030083c040240e03581007034104461240081c0001002c0040446286000403c586902c1d1002111840461107003080c0420f40144a4007400e120048018111569021001c040788080d000d10b4000000555507049040078654441d40501018072941d696841440d05140c00c1c0300f0740c1c8601610300c10070b0044c00c1801000080d800411600050442d0051074004e440c2e0a10110b9a0354003080060fa0001404d01c0c04201d11400800c7c00c205084990a003111989882039031785054495400043c2106030030b20818800b04e4000c1d0044504d81d500502101d142c00f4201e016510700a045411201c1d1194540701808110401401500548050020210700e00102c212011304140940d00401c68202d45650004100f00440700b024414681c0180003400b0080030414000c1440c0c02e0040d1100202d1400a02121070f5449100c40300724a0768030131101880c254400d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 442804649 1250 442803399 442803419
    0x1706010212070c03080c0a0c0602060c03043201020a03060f0308030c1c0504080904050703060e13020a030212031e070b010311030f0f0304090c0507050703030807020a0b0403081006020a0507 83
    0x701d80c2074031107400783d42000000641c000014410400520081c142c14101e51a00c07642210300b640c0004210760000d024040360f50314110449402942c010104541c034101580c2801c50310f40705920b80c0c00203a41d0016000b01110064000b0015032150360750802c105611014000301117011400090700004040c400100300a09100052022510344000da400302d0000410650541d4400c880c1152b800b0300c082018a5079040c00d0140c030ba0018150b00341405081e003081302c2d5120007131005090400c26a51000300c0342c2551242d0b407041c406140c0140c40c040c001c154003090640e480d884461070703800c2012124070300c490481c4e29805a030107080c3e0008404210764a1030710340c42004110300d007001c3c1e0b150041c4940c851812204020280b2005d01034406540c4451810021200b02d07061141340c141803100400207400090030208125065981c542055101910b640c0c004900c0c0c1543c50314010103800035081408213150704030b0b0089201d0402d01041d0601652a10822602c079882d004000340f00b5400740310140f000d6452 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 442805755 1106 442804649 442804657
    0x50706060e0f0a0b011215080c091e15100206010f090606091a071e11100203030414030f0a030b0307050f0607081305060309010c1706010212 62
    0xc2200d250080b00000c03d80c000142e40c0300f2189200c0ea000741c1c090801c1208009081140c00405000808412201d0262a800d031048011078a96468101d0600e4030640301409480e2400e800012445d038800c401030301b081e6058440c621300b504103844440c10800c2c1240346a000780744e41e51600b038500c20400e9203600840303a0f0354104070f014007090b40c1041211045603500d10b0032550007600c403204030101e406291030090550604444442c0c1c0e0041d019920b2100c140904c05808400202004000b400001c407444030015810500000d40800c4110072120087d00c04c9c0020341e45000010103c0c0c5180d68464028040072a40d560f9010016080c20894900604026034914220b8401c0b04001600d5026948000703003003180000342d400009109540304d9000b00384c0680800c3d10ba041071625280179104c00c086120001d990103185455142e5107803241130003040c0c10380207003810800300740942c0f0301d41e48 = true := by decide +kernel

theorem cover : BRFrame.Cov 442625899 442805755 := by
  have h0 := BRFrame.cov_init 442625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 442625899 ≤ n) (h2 : n < 442805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
