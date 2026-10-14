-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2469
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:48:07.155555+00:00
-- url     : https://prove2.me/submissions/c5e7fc6a-e900-4721-a51d-11ac9789c2d7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 443884892 ≤ n < 444064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 443886142 1250 443884892 443884927
    0x203030a0c0509030a0c1a09130903140406020a1506050f120115150e0105120117010e07080a030e0301050103020603160509100903150501050604120501020c0102071b0f0605 76
    0x410b410210b040a60a00c0000d1900306001c008903046084102c0030060300607000c2e24403001c00d182210807800c06d0701e050080f500d902405010000030907181c0c03004009044c000c14240c00c110406954440e942c0762100780283d80d030038013034008403a0032a01d50300d5582c0404042c442c0702c1c1560002420b485035841d10108000d018180e40b485200503540e520085d80341101010b0840000b888000001028a8403d03040641303008030582009040c06400c01802011808203000503054070883e5440055000350b2000701c80c010415108284aa40304d840d20109070407500140102101d8425a0b81800705500c1c0c3c0709143c01d0300c40070f00c80250099030500c0803640340310320341140c040c1c11003a80c40c00d00d04000032a00003e402290544105010511112041c42841104042d000500c0b0141600b40517175450407021a82038484c078842d004865014400000c01c0017030a4048911503441c00f4001e40d1a03064904040702100c14901d1140320152001c0000241000d104428004440b982d898690600908892040c0e80d103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 443887392 1250 443886142 443886161
    0x30c0f08040b01051002250303020f07150503090a240f09110108090a1209060f0e0109090e01292b0303090c050303030709060801140a1e050d06020c010605100203030a 73
    0x103005042c8221b4141102c4130300c40e00c1fa8084651662586490340c14080e0801805000345c101c250004a030502c032120004200e4540300c0310600d803055690303450f030040c0c43c282800c1100c000d04c4034080d41d403100c140204840410000360310000c410850102d071b0f07051400445401c49002024600d802a22040700e60040d02c0480e4003101d482c0985410703013002d0b52003403a22121180b2010215101c40800d0143c0369111204610720449400d00700300c130b445d0280020b4440300d03151089a00080e101d080310b6403110000c0d000351100c0d0400d1414001e800b903c0501e8a404c0160784d41c88c1c1d5005812001040c1030030000000d510910807002240720800b005070ba04e007103000e400c010388241c441d11003800e00080c560310f040000f14441e201c240d407000246400c19200030081181030784030041d00c1110084812541da186100c6d00104c40b007440d02001941600100803040c8030407903101c01d42c8601115695014803507141c0061400000c240001c03c1960b450f4400c2024444d040201d84006900900016401c910a5441190348 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 443888642 1250 443887392 443887397
    0x30a08030c0903061612180f0804150c121b030c1110050307020606150a1107050a080f0705010203181c06020a030e160b0703140d060303030c0f08040b010510 69
    0x50400c1c0c50003080c80c0c101c041d1010f40a500c14083c0380350401d139102c1340141c001810800141f150742291000790b03229404040c0040c040c101180342c82010803254108440c01429501d44104009030180000f800541007850141c0d40c0f20401140a42da0600c641c0e0f0348890408846800d40381c00d07186440840e5104101c4030202d8603141200c50855442e035960350846600320180c0e0b11640e40340b8009000030304101c0d010f8551400740710840e85805c10455240140d888a2038186001881c0d0617102c20310ba803130111540d01168119034003d4021400100100301a14608241c6040f030b40240e07540c0004a9503031080c1144c40000514040065002d86403120034400034000b89800044c000340c164503141c003280d0101d050240465580d480c0c10f40f52000038050b005d07418443c1482001d1445c0b411105d80305274410380d0350003000c001020207c080c8140001c010385600303140c113103000c02c2401c2e220300c0d0140090400128044c00f01e914075051020a0b481400b44034880e0b9440103040403e0391030001030022801c1449070b030324103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 443889892 1250 443888642 443888647
    0x80106080f06092e05010b0a1205071d0f04050c0a02120c061308190e0f010c080901052b0518010b1005130302150a0806030609060f070507082a030702030a08030c 71
    0x213000080780201c0e4043d00f4201c10296039074a007290050700f81c5160002200c2a5410641081030241d00702c1d07141e01601d8458480d442c0c100110728001940001e004070703040e230310626200a1000907034020b8060b03c0e910141c1d40031100802e08081541c0064010159141900d40c82107000407014106542c1e40c2486512505200f030601c4100c5541c3c0442c00c4c055854000041d140c00c940002e41d19003016100700301403007800d0644003a00c0790340719a8030a1151011980c140301002a203824985001c1d15220b6134000022035020142041c8054503000e0701082e184006803100503240d248480704184151506805c00510000b03006079000c01c01d46443c1c202c000000f403542c614010000142c8c844a1040540704d81261010f0381d586000903015110b40070251095000b64040803c12060202c002812034011040c00302d40072040c0d0f1a01b00c2100e0070300c2581001000c009002c207055a40c2045080d02020b00600803400d51075030300107801d400b40d80c0e002d000e0010791300d6817200a0903004103407010b00854001e40c2c89141c2c1c51 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 443891142 1250 443889892 443889973
    0x13110a08010e060403091a090d0c030b04050307380901151e360f0f1517030f130504060303050c011104050a03110102010e07080106080f0609 62
    0x80c21522a074280c1e00154203c0d1003084101580500901e001e000d140400d04041409660210306500402c50a02d005030b0304030120310144152150a0401903a0015400e521880c4c645030540e181d411042045038590060400d24a600e0342171102d409201030009941b09c291204089042c1207254007a0103441955078a6001003c1c01d03185894240240c85034000500006207a462401e90b4100203a100298640c0c4001008290543c01c03420802c034104044110311441201c0c240e10801090328001c200e03401c1d41b6091000900c0744003504814622000c107402d000110340d42c1d028007401c040300c00903118034a0308200044040704101d54003500b080c40b0000c8881c209039403a10046001c071907403034100b82c0100c0c00215a5017000310b403d00600e9030039055801c0b03c0d0304091400c40402c032484054080201a020010102001c3e40d101350f102003d080b9440c41252001942d400500740240310a000e0344075a809564604041100001841401500c000c80202041e5050f200101d03804588030b0410b41c0c05005024644 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 443892392 1250 443891142 443891159
    0xb03010c0905010908060606030610091203031b020106270e060103030801031509050a02220504060507020c0105031015050c0102030f0a0c0215060103021606050103050c1813110a 78
    0x2002458aa140c481d9400e0030900094080002d0f54080c2c1d03071a902c04020040f20380c4032803007640c0e0800c50583d002c5814030781c1e6001c02d6030010b003113070003800d00810180790103070525604d60001c070410315040322480100d10b00c000c4100d090350094060010301000540d00400c03102ca91390030245028580c2e010006013001441d2209081010a17481600007610304401031060100c10200c154490151010420405201d591104d442c0d408190010740700b0318030b1281d6840740e4075210700d840507504600d000c204440e2405142080060005070f0300d4000602c14030100940950190702100c4c0103407024a81c4092940c5000d403040307a410704030101c3c2d4003040014070010382600c100740041c50017125030601d07502180c681b01d840c882c1104c00d12150441154401044c0080000002d880560012801e1030f0150303807030040c80181c0c90900900180104002d261500020521001007110490404111208107030208102d0091400c050140c928654440403c070b440000102007021000000358013601c0b0710441990344018 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 443893642 1250 443892392 443892401
    0x13050303030c13081b060a09090f1e0b060f0a03060308070c05010e0d03051b031608040320090f13020a03050d1e020327060316030501080304051309060b0301 69
    0x1d03100b0640307000ca80c41c40c0b548481003c100103402c0300001030482c08600d000418604e61428075490051900250001c0224400c00b607200141c10b550000b8005100810880401019a031840c0b048020b10007200d40b0b541d500500032880d18040c024083c074180a1100c030920301a41c009a4540241070341c5110000000d401c61015103507680c010f010005c0c0c0b180c90b040015023145445d011403031182c003000402000290300001a555440f0961480412007005841c06d0303451441a0f030030020910404d41c4400e401c1041c1d44000700240d1f407040e030342013060720754900180302d00004004403190b014607144e000840c0c059070143c4855102e003c9120940c3c90040c1c98010070200040c41e001911aa0003170b02c09603441d95000300c60342000c0203900f51001c40d500031441e00251607008403a4040b032015010704070001c0442100600300c0c08010004e00700c82d5241054031103420b02440d03905551000c00e06001c0001520344c070110030381d8112840503103441600060552024001d145c404012101d840d0344802c0044661000d109 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 443894892 1250 443893642 443893651
    0x50c07181803081e071b020d0c0f0f0b070309150504050a090204030201031a030709091b06030507140c0714300c0d0f0305070f050f0a0c06030203040210051305030303 73
    0x3500681403c01901c00c984d50b20070b01e07024011284600c0c0520620551007882c0d01b0080d03c07420000088041e03244005030340340c0484040a003411013480c0d00450107401182c3c41c40121451100500302107581c443c3e0303000060090050260203c1d000d03010030032440380030740070703001c0318903510b1074614542a250800181d40010540044d449944c0c042014030455800d03214580b6907070111441d100c4590310f03280020fa80c3d0520f50080f0110241c8480c1c00400b00248803110a40800000c00d08100c44c540301d240c0100100b004580307543c001802894484803c400305c40803a1250f0715110301a0401d14200620715109180c1c04a1698004a000b0500c0900701c0c4500350b1a1481200d2107010340c0d0031003062040c0342c902003041034054403404050074194000f070403000d9043c022960505105807a200103090250055a02d064060003500441d4200007a81c0c00101d40c1401192041021180e11603c90780114203e00003100d0094004071600ba0014030329006030080c1a484403164095602e03151918046401c40e0030581d03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 443896142 1250 443894892 443894897
    0xb030a061703070c05131d0312010b07080406030b0607020d0f110f13050405010216060615080403021b060903010603060f0f02030702030d021c05040b09010507050c07181803 76
    0x1405200140c6119580100740d641e0600071400e200481e01c0e11101c02d80b19101e00c51140901602150003146650030001d0192141e40a04c1c50030b0b04030040107500c90703122081c03840710b0450000021a800d00c4400658030b04a421682d0a810641022400d5000340303900c40780f280e0300290a0004d00c00698500b814042c0c214461301c1460030134120b80c07070b00101d6000c13030044150ac540c80c270350142c0c5140c0c3c603000c4500c4080e002c10040440e694503603052050080c03181d0902c40002100c60315810301401055007140089401050701d078014000c2d50181266119005c1d90020010707000020030341c0140d6500d080e40401c1d501d005003c0e0b8a407d41c100c0020f030841f10306520442e80c03981c4801d088120b80d001403240c48000501c0040941c950310701320f8002503da105441110481d01e40c04a0b5015202c610328900310043c81908508109a003440c0c2050340c18038500f200e121000d5820800003071101e43c811030941c0c407041301110007400b041e810100c200c0e000e105040001c0030003e54885084c2d80049134044410f0140e4040d8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 443897392 1250 443896142 443896151
    0x80a0309021f0507210c06090602040302040501080f1c0e010e0a09020301090b0a1502060f04060212010e01141813030201090503130303170103080f0c010b03011b0f0e0312130b030a 79
    0x510300a07464038001184a4801d0000d405d4000b045900900b01181d1035610440001e003201c030a03d003840c001d001e140c1019400a180c4000420f0390980010b000100100d524101c907440c0b518801e07400051840d408040700094428150a417255005c3c1d54281c41e50703007000b00400c441c55220b00d01003040342c000f640305e4034209071210190324070340c14064450b0000c0c0c21011030031700030a00004006580c946026188071095103c0d9000142402413a6040e20b007441205500c8140c81d507035600452074150380a010700e64844415040c0c1801610300302c0403c0984084600103a40140d9070004881040d0310600002c1c0c0565407101500f000280d81400100480e003503040c0c10003010785c00c604004086480b400c120f60448041400180081404101615540304540c0001e40c2d607000c1c0c0100305800341410444c01c83e0598248441c0008216040421110500b26a40c48032000d902d0385500f181c862494031411601908480141040c00e802d1100a10002841046e0807000c00c0d59400d504181d58000ca580d51110b60380c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 443898642 1250 443897392 443897407
    0x1031b1a040b0903190c15050301030b07050306010210020f0901080121140a080c010903080105060423010504090903020a020405060d0b0a051e0c030a06090b1e0102010e0307080c19080a0309021f05 86
    0xc01f9880c1000c006181950071581165103107648c2d40401f40c12201402004000195684e1003006140503407811110159118a05424814040c3d00042c98a90101b5000e20010461140d01d510b0a40e81c04444007018220341c02c03545a120009200400f80905806040d96080202c0d1081005066030f480c6c0000020740300c085414010458034060300a54402c01d02007104000501c0c820744148500100854100c120071031510041c2c809101d01d80c0084482c500700915642456004200d0592041c001e071028070480d41e8002c2007014280c841c42000381051440c10103c1c2c40c0c400550300c044d90014065801c0750f900c2d803100d8100d04088408030b40c140c0500d8030002c20440811000c0c02040010803500300103000580f520800907004441c09052a41c00602406212180368800d4000b1240c200c1802c041e40e69860007800c0c4044190f0000c4200c0c400d0307115102c00d480d08071400440e0b0b2217016404c40700b074a05004488000310090300c2d1140c1e050b40d005950f4441000426240c82607400484d00940742c883d5030f48039 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 443899892 1250 443898642 443898659
    0x411120106020c0a03060b0a030b0a2406051e04080a080c0d08011a0d0f0c030204030614010b1b0705031902090f0f010504020c07080601031b1a040b0903190c 69
    0x105800c03810454000880700f1409844444060301584e6109070045800318913030000c20350b24001a88042c14028181081c00340035032140d4443d0740700321a010303d110075141d01c4442c0a61700082610a08000a00410800b4003d4840c0c40f141224000c05514031880c10b0b60750940300d0f1a164801c681990303500350003d4401407810080041815030401420562019071400d07501c1c2c4081440d0314042005400d00080911042c020390b03004511403426004104600350301200000d00075003017400100c0d00b00d440c003000c208030208404900c504854034035001e5894211010f890300b000100c03910944019101d02d8034086495901840701549000865544c51210100c5004010420401501c0c3c5408030340520b01b8054200d070b15510480c19220213036409039640c070fa04240329292002550060500c0d001e04e100100410101000b0400940c84000c4003a0362661613441c4402000301100006c2903103003080100f0400042c4a6000e48105c0700300406544030769500086800703207450b5120f0103c40845500e0018070040e80d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 443901142 1250 443899892 443899927
    0x40e010f03020306010603020304050309191e030804060e060f0a020d080a0b1008090a0f1209080316151b080414010e030306091f1203020d2d05090411 66
    0x1809035080c0d000c503403454000c2070300c442c030601680c410150000001814820100200d401000e8068540b4149041e19150707044e24402d20701403901d8007072034001c0104a0b0b2881400350016a80c000c03800c185040d10b450030070b0303407040c1900303642d40c2c4c00041c18410703a00c0c994154409002c40203104c0c0c011f445081c90410000b001e4482c000d254032a0b85140801c100615150000f01444003200c9050080b0b094540760003040c0782480202c001090307903010240d078804000618002881c084201d07201d2844840c1c94280701522800b414180c2c11007d070104c0d450502241e484400e84221504508000131039181d4214585083c8a40509a502145000c8144010081d104e55541c05035076a000c000c100300441420701a032079100c040e100c584560302c89008520120026031401c5001d205004038102c2040c0e903051070f00303500c0140309015005401030302c12098440d0b00660840069440b2801d1020000c4807182c038121608818452070b20402109000c070745401d44851041c0c0c44001403503000705880d6440c0341c00c424a45e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 443902392 1250 443901142 443901149
    0xd0810060504150e1207060c022b0807030315060305061f09050d02060c030c24010e0109090302210705060a09030e06030c09090403050c0105090c0a06050a091a040e01 73
    0x80030802c0200f00080060354031580c1107415162403c51030700070000064207858402c1880402d8043c01c03000142a030740025030001014030a5507514202412084550100b440d02540c0c003014460201c90140058460402068034074402e08002605034098a841c1008411035000304010a41c2ca40c14848145131000544640c80b1260000b03e0100710070f0000204a4203880c440c40d4020040552801e04564030700e0161007204000302c2c1220744070142c200c0000e80d02e09094841240b19081c46118048070300134030021505070b80d2210100c440f6a4079011205000340001e903426021170040360f40c0040032842144010407221070a001468075070126040c034a0403e030000e40300518107840c0070000c600003504100f61141149040798070130b8076991400c0c0d101c043c40c840d05428a90056400042004054004018003118030075400200a103681c0c99061982e64121a001158418603403501044014400e000030802c0d4841480c05100d13450355240307445107c83c4001101c0f0b00c0124045000d1080e400c6403128103004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 443903642 1250 443902392 443902397
    0x1c02070f0302190302030904150816031b0308090d080d2d06050a2105010908040e07030525020f061e060a0f0b0306150c0708060c07030207050f010c050d081006 70
    0xa5040c2c07a94040c1d5244a5202c0b034600a80d2100381d0488a400451181401040b44ae015076000e00105662080c0800d000e00080b1000001500b0908410342d40d000c40100b5254030040962412611404004c0c5840c1800000c40c1da102c0c04010018400c01c2c540030321040c440c00c000e01401e220f009400f0a0202d5511400200702c0285090010481e940c1e0fa020310a0498091000103030101c000e407800385003200307903c402c0a0b18a6003004541800c03c01d0420083c42141c07d002c8484c041502c0c1c41400b01d0a40b10151036503100701c414071841405016095100c1102048140112060992207103600d030b040080071100640e6004248500f201242e44000103075078081030880344e000380b20782000940a03803140c0c50301a000b04094044009010358032004801c08910516450098840e00c00d41075140d23403420310740202d0a8074040c02c0041102014030405032003606030b042e0003600034141000706104400300501d55540c1040307058500d40005c140300b40100c078030031105550740035070914001e0200b102200d00380d44043c04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 443904892 1250 443903642 443903683
    0xd0b06130e130f021c080a02030405180411040f06050a060201091e0503030103140705060c0c0103140114060306151c0506010f0503011806090204120c170d051c02070f0302 75
    0x301c8011010707001e02d82c116400242c80c140c0d240c0c3d441c1d01701c942c041c00030109240001c03040e10040d0008050f10482c0c004860700d10584268070607170210f0b50f1090700c0040c01440103424408640c54103810401c00b0340204100025010340d5580002e4058a6550010015035034a81c503090074032200d002c060103814000703450101c02107595075500d5564441484060031078003400c88140c580c04414030285009200007029280c803007800340c40791031701c0e0b0740707280c0c5141d021a140071000c031a0500900c855030b049a4561100032008601681071240da584020710b110350007041000c0012036840c0304405001c03140701c41205012000d289403032400480354050229410f1080b42b00500b600c2e10351181c102c9064500c410481c183c280352410042001e00196000001190300104010502881007581c007100c1c14002c159003504230395608050900e4240d20b440c00021904501c00065100e0b010b14020700443c155000b40c0e4540105502d1588220782001c1c2c000c4881410104482c002d05504110310790801c00040240c04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 443906142 1250 443904892 443904931
    0x81e012426071403071d0418022b0305030601020f120a03020a11030703112a04090311060f0a150b1605160e072a120e0d0501051f0e0105060d0b06130e 66
    0x90030208c1c1400000d02c64003050312845048081c501c0c1e0b86a446142010035503001c285840c0c0a0915001105e40c14018031542404030b41222000510860300c0b0346001e4140d150a007111001c402a5100700c80c1c4209000031110100e070380000130001020b066019644000310011a40b140324248076004c54105008005043c40d284003201010f5051800001242c000480404602e815a00562404800c550034050b040c1084440144003070010b2080100c10802c0041c5040050f0540c481c000750702404d542c0789014011700f0700c075000e0400241401402070f070444021990815000b01e5179003d64200e84005500321080c042041d800103076041d218142503000003002c04000442c2d41c404158020090300913031070501c0b162400c0d4029150070003500b801a203456003070116414900c3c044c0c4820389030110400450241850100c825801c5102541e51030844444581d1070f00040140d25000b480306c0e4040e40c1d075207079400010355031418010100c04412860110f402481c051405031034079001044a42000b903100e0750b19 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 443907392 1250 443906142 443906171
    0x20403061103090d031a030307050f370303061e050a0b03191d010c0903050705010813260a030e010c09050d03081e012426071403071d04 60
    0x4e911341803d45000241190030094005118540309480d03038160100150080600501041229104d00750070100c410724a4001411400302100040300d0b00c20341e014001444401c40514610500c0724000d20780401d080f40c0361662842ca05002d2a41103400855030501004a4201003010000a09040740e125042d4502440c035032035100ca180a0740010a03594180d680a8071a000c03034210000001c007402001000e10805011f41040c041c0e00041d1410b200b8450300281d1503114007050f0384070700c0300420080001d9805556080c44240080d1040285403085d10b00303175901b00201c401424a52200d070768040360401440c14020300b101d8014104804010040d5010300040d150799212195031607161900040554480c0310002080035134860784008083c80000000c0d001c280f00b41004155091980440d89549240314203460441c420380c07a98281c0600500c100d4052490740b032440e0b0740502c0e00e0600007550142490a20800d920464500d80490348100707c148000300c03000034014003250165005c000040c0c480140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 443908642 1250 443907392 443907403
    0x209060d0f20070203010b0d050d05030711030f1b0a0302121806030a0905060106051204021c02090a1d010b150901110a0f0201080901020a0804020613081002040306110309 75
    0x1500d10280c5071007162660034001d07804601480045440e0090110403501041050351050400768072039801e00d254240c40c1e00d018510207002c603a11000400b0300880c01c1e041038900d42c02c000d0a00c824000b800384140701d00003003400100304c1c3d003456021141e84ca01443c10389104000c0103054010a0b0f90080b144007000a80005481000511074614280c0300d51072000c4c0c244105e41c10a004a4015001000b03002c0c1131901a0415507441d80b240f800c0d42c036103070f8950708103e0300c1340110400d1b4032602900f0400b040150403d131140e409400d0b8440d03142d03402c070300e40c58011442c0c0d24016076000c24416511290600c04400c034000e121010308030b038402071029000c2c02c400540f41850b001001c94805d000064810380a80c02101001d04084030b95080c0c42c00341c0802c0c104000c540c80304400583c003003014400002c0c2c0c2004103100703da08a000689840d4081e880d190240a04c0d9084140f82d81412a0420070200c5d0f0074000704a445c1d40c0388000c840151b81da5040d8074048080e2440c951441c2c07501340b014800c1c4968420007094 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 443909892 1250 443908642 443908657
    0x100c02161a040816050108280c030b18040302010608030a0504150302130320010804020d03080a0b0406030f0c080304031707020f100201141f0302040b030a0c06090303080a020906 78
    0x2150002000c00c150440e403030321481d800342c1114840c10505401c1c08a100c4c1c0744074102e55007602d40046603a250550100b050b62110340c0d454240035002e5420000e040298018803009203a0702d0b00041c00c031141e00100b0b049550386080c40d48082480000c02040590900a60000c0c081e464047c0d0f0801d2610840600a800395000310f1904010140f882e0032001e1003541170f80c124040254040f0905566030605028030704004040e10040e00520340802000d50049002600035540900a043c034a600303520110b070542c001174040704426460341440042661103001c1d0801550141400c100c16100c2445c0c6410f215030030f944400f0040c0c10a21082002c207480c0402c1803101806180c0055541000c0e10010b246d6041440c1c0c403a40c4031100c07558654501ba41584903124102079100300310804e486050301c0c076501c250082ca003001c011554107810b0006007419005101010f00180c100c50407011540e0b101079000c40b45800c07120020780d21400c00c000b410f9010515076040101071030114603180f21340000c074849106915 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 443911142 1250 443909892 443909909
    0x203041103100e03430303060509040c0501050c2a01020105060405040503030f1003020a03080a030b01030e10090f0203070b0703080705030f01030f0f0b07020601060e12100902150705100c0216 84
    0x141058041c07032022000e001c205c0d1101a49020028a03118011100601c0c548141c0c0000e207820408038a80c202000d00c2d6000ba6008068000b40b585408011180b5138803103a075151036030150b40390a042c40c0e0030800c6100d0901c15070344100c51071581860002800c45000408061180d8200418880880d0001c800c5a80102071407051080c02c0e0703a401524020954140e00081d00300380358103000002c0c0700d500406006a080e8655051000c56010750044042d915400311046850300800e440c0c0c01c002985510040e1003e116504021175000d80b900081d08110455024041038040081c0050400d40d2140205520140c1d40c20a107040d4180310190903614401404001c04e500d030140409414060b071042d1102c4000d902c24035558440c40e022100944031300c401c0c820072003c41e10f001c001c96150f162580c0d50502c141e01d2100106581c038070342d01034140500007007181a60401004480c45607030800740310041035528024001480b0740d00c09480790341e0071036114000d614211340100540441200100c1610001c0303a0501 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 443912392 1250 443911142 443911177
    0x20a020c090c041e080607021b010c0b0f060324010e0718140d060207030c050601090c050f0325091d09060703050603010f0603030809010e070521010b040203041103100e03 75
    0x4204c0c0010b681515040041140b04241c100190150300081041c092048124030f80404105103005441030400304d18001c104100304800039290301800d41c05641c1c440d500a04413002191405205206000001b505101e40002c40e0018020008900e258a821541d1894007240751542c0c40c1d10044291881d00480d500e044801d298618259030311020b503054113410510443d03464004c4d19015240d0107155400311414001c503400010b108045129030501800d43c0d44035546400f00780d548044041e44000c01e84940c0c81c1420181c2c0145e840c80da80c24000094072602c42c8210ba60400600f00d00c1442c40800301d401c0304081d07400300b0140c0b40000c00c000b40c20445605002c220b9850380000280075001070721035052141d00d00003000040c19884034180307021f807c48100070441058141d80d203d441d43c030580680c07138000044840a4003078030014092030030289440b000000705001840001003e990060740e05892040701e2000c00066450140f124007085030400008108101c0d1300307040c4076140c8c01004142d841c0281c18 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 443913642 1250 443912392 443912429
    0x241e1b0c0c1e050a180b0f0102030d0509031b0d0201050a090c0302040513021c0317070c0201140f1b1c1b080f0706090b0f0c030604050718030303020a020c090c04 71
    0x400c642d14081c01006002c4890f00b5140d1003c13507400c41405845000460401d0703070006087c1001c5d402c1c28a9540c1c181e006d545081110910034000d010302608c0110144010040072248056401c0c01c2d075424541e500140c03403810240d100080c01e444001d1b10901c42c2c1403428101c140080c5074140144100d035810798000c03986643e144652094900107200c0179400c50004080900b001100040201010388291650190b001044000140441c8101c0b90440414440c440b400c2c095805078841103241506004003901e0708107107064513619604640f08880d00601030160018980e2000e205240154424104001e0030a030522001000900517510f101a030b80c0c92040140280900300341120114007000440e15030f80c0301d042c07510700d008080403070050b42c9035011034010424401002c81c0203030043c02c4031a000d0342541c841004010050601030200d400f840580d48056401d00c03800303212807000314001e4800686446405030302900f4a009a40c0c850f100305a40f02c20010603100d1001a60140d0710190090640000c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 443914892 1250 443913642 443913689
    0x915020109060c0e0a060c080702041d0f2b021c0504081204051504030b040314040e090706030615200f03280c241e1b0c0c 54
    0x1800344060402c50800d6410151039410001404c4d080000b61000c0e40155524401283c0b1540c4e035410080510307000b00440c5000d0718198211100079241e41c0c1003455503d032500e018a03e800079400702c061260b00b248000d078070800102c042412500d10500d441c485c0404040f10025103624407010000140d80180300440c40d8107100f0300980e0094050002140c0c0381d132410081030215130b001485401e01c0742288001012048a00c00c0a403000c8952082e01113595465507601540e840340588038510000a040c807000a4080c80c5000d03441c000e01d0380102401d9000c0c10030300700070252a01500650303000c564042550124a80c403003c0b54009071070300f46222084000cac0880f01414039419108617070b82844041807000c0d0001e91b07085040d07220710800c01c154841e4101800d05442c03a1001100c080e107044c800000b2603001d002041c41c03070000410950800180d8000c0768010038810051402c01c044035560320b41d8a01d0320a1507440f2064034007896810107461400c0359a035100c085403254010080c02c40200c5100018a04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 443916142 1250 443914892 443914901
    0xf18032304060201051503010903091a12010e0604050a0204060c020f0406090204170d0e09041121160f030b011a040f090912031a0609031009030201290109150201 71
    0x218224030303a644582e00d030710090180c1025500c6040913008025890700f10f190510400003496495100d00d66000c2c80c01200712408a00c1080e4240b2000d000c01120f0303040710754054610b000e089018220342d000c0c1454014070044843c014124401148100400d009031504000d9503604150704680d0300701c03004004c0000c40d0280c01e0980c417a0050768004a008540c24840c04050b000b01e42c000c40c02c4600b121242e600445a500501541c2ca0300810210702080c0803411940c1c0b13451040801030000100c100c0723a0640061542003c0c280c2c0f20703558208401035010ba001c2402e45a000780b8040c04099482400d60300d0341c211168061103205c060f035507000c2d00041c5808590b0151001044c1e1460b01b0074003da035441d00e030406008401021150f05210000c011707805400ba100781c0e0f4002c9e00030b9801226006c400030501400794408064254503101c0d088650b6007090f0b040c0500e420040c03280d4008107609810a14003660a04040322240340c201050b001000540d900184403c01c56035141d82d02000c0260115080e401007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 443917392 1250 443916142 443916197
    0x5071103042c0a0509101104050f01050c0601090b0a090212010b161b0e011d160c020402030a020405040506010c050a03030903090e0a06030c06022107020612090705040f1803 76
    0x86001c0700f04561908a0303440340e032046003c1020369015082c402d01d480211003484806400002c0140301c1403150307041041000c42c100303006043c16031424a1145d24a854040240d1102c20741c961106100c82640c00e0011810008141c00e80040d410f00d070b00c0f0b0324260840681405407038441540450084401d118840748080216081601007810400b0140d005490101768081e074082080b50340000121000344103600040c56101c0005d4100d540c82c0c5030748503044075800c3c0c84603e007007140005840c000340c2d4443c401180506d8038401e005968514100c240000e03200001c01d060306000c1c0a440210102d01c02040f100000e580c14940010300351960b01d0140c90720041c0790442c11540301c03000c08209600200b035203c602520301526580c2c803200e03560b2108136590a00307d544440c884011010303d07404400c404000c0c2503d00c0c0300030505428004a420740d40c4105404030b5002c00350b03a200120800450400b440307001d403202e242600500041225030500e0010030354000004042180090790740a10200154503a90034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 443918642 1250 443917392 443917469
    0xd030302070206071401050c031e090f01141902120109050c120708101a040b0705120304081207030b222702010305010b042909030304120302010507110304 68
    0x11404c1a08110007514044000d10980f90710340700c08a04040540d40176284201122280750b1060724003c4d0320356943c150b0140c1105018490b10648000c60042805121000c10544604901c28a044c07150a1001d00312441002c0304c1910401101c1140101c4000d1181501c446a80100b01030301d91071f540d040c00b440356650041c0d851285000b800005503010b10014000c8203401c08040392540c940c11841d1000700081400600014100310800880420343c001c0e03c0c5d5103020b41e09884840c01d044a86115960007180c04171058600000c0a14160300c190b008180c00c40302520301040505942404150308440d000e94140c1c0b040d88500d6100d0032080c20341c0050b0b03080e40b1911a0303400315410298a8601d034410014049020a00f4100041203004100d0140c07004c891284525002e24102d860072409210480201040118803c002c2410552001c0000300018015003c032042d4140190400900b1101c0181c942020800e9869000c411070000100307031015241950141c40c200c11540010036004040700b0303440c030389 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 443919892 1250 443918642 443918647
    0x90f0a03050301051e060418020408010c0e21030304080c1f1d120a0c0f0b0408030a0b01030c0f21091a01060f0503010e0c07080c16050a030206090d030302070206 71
    0x1050750280c007a5040710000c0d02c07201000860141c40c500c0c0c1140c44c0b13010541004007808204420028440d02c0c80900340030010040c5403d407110f0704242590240e02005000c501c00a00c0b20700c0301c0c105031810b401030018040f58041c0ea0a42c0702262912480301420240031480302040f07034003501d10244500f103419488052580034141c051107212000d080140c98490b0320001d40d120003a1a0b00011134201c04000390b40440602d010305034001901c81621008090f20780c81120107210740015002d02c0514043c90240058075224545040c0400c16200d020b44954100341c00d2001c128011034020b001c58040b401c1c9400d00744004200c00303014800c69001441402000d5040410000522249000c980000380d40d44180c1c5846a0721480140c5090003003211510008074200010400c2c0a9101019030b00701c041e000c64035241c915680c803000c48913006106008503070703005041c00180e4005941c49243c024041a12500c40c201c1c4bc5070006803641c0504003005c0e0007800c1d0041000304240c4241c1c102c40c1a030b03a00414054 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 443921142 1250 443919892 443919913
    0x111302040918050706021f0905011b02100501060c02031504240212010518010905040305040509042003062806080114010303230d0b03010f0c0e1914010503090f 70
    0xb07281c401c000c0d41a40c6500a001010070b445102042142200380315030002c040254604c04100020014108151559503071901d044403400c1501440d007100320300701e5000f0f181e5030030b210320003604031074041e401781d814005184040b100585000c42c2d4030b0184411011144200c0ea500d003030884000c0444803003122001e48850b0110ba0301006a070103884094414030321900540e0321078091280303d00c00b040d07001d0070404010340100200a401d402880e8403600c01d00e000c1c0e0a166550700800c40c18034080d81c085445140700b206101c10b101c0f01240b040540b11040700100483d04100c0042070388042600c4ca250451100002510001c5100344c00410040250300020010265113011480580001b800200c5c0081c105681202034441e040c21010700300c1020b800c8080c54410302d02d000d040240359205c02c0d182c01d5500da0030404608003582c8503016071000b0300d48402c0c1c40003100c9010451040c44041d5140700d9000c502109010224100d0030308a0250300a0805c00e55030f8546d424008d140180007400903686108500902 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 443922392 1250 443921142 443921171
    0x10912050c15061f050d060e01230f0f0307050a0303020a0b090307110d06090b010305010c11160e0903041e0e0a0b1e060c1002120f041113020409 64
    0x200140540d1805940c1c00c2c81c02c095141816580540364154800e80948502c4030400c0d04c50030b10340c4524520306004e031422200d080b1000030303038a203603103c00d5440d108100100070b503003803e034007501855285020710782103041c0f0403001401250032100180d001d01c40c03030000c00115803420020080600f400420030078031581d90303142c0255201d040c80811039980c00309101040d1048000002e41d41c62692161008551082002c00d01c02101607081054403d6a2600c02d81400300f03149a0340903011f140250000700d494003080d80702606080d807640e8200c01a034450098001c0c3c183d480000b00d070a440d101e055030f40c1c00703460b400d02c400d10b14002c1e40c20008030480b080320302e03810280d01d4a0b2642e00312698805240c1d03040e6110301a81d804c66944624654122241130303103c407c0d0710302c215510b00c1007410003401141049030302c0c074080349069520400200e085600168002d01d4004010030903130310641e807040c101c465117040d50303400c10495050f0b4175040c0203a140d003003c40410340b0607405850140103c40b02c200310004070610301303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 443923642 1250 443922392 443922397
    0xc0e1005240d0b12010912110c0925031505180a0e0f03120105010f0813061d0f0705180115080c0d020a080709060f02032b06030309170a0c051201091205 67
    0x122601fa409640e50b01c0c1140c0999061128001d2803009091043c441c40f0603c010780c8401001d12042a00c603034081d103022032030200e000c82260070550700041d081513400301191b1450f0349504031070300c1a46180041c1c0340c0c0d4515001d040d0782c45104424003181d25990400541c0c40d104140500f000c40340004a000c1c10050f1100307480a040780c200740c0c2d80c1e50b102c0c036a511040d41c40b648141c8001100c140d050a80602080b0640c1010700c9030300c42035690100e1030740400c00322030a240000302c10040c00d400060040043e49404050141c220780403160100095152492801103184003030010024444001d0000d1032003002081038682c00a0061410356550603142001800e0a0b4202c1c0e100b0045400b001020580e1031045520105000854009600c2c03d4072011014088801c000b201110481e8000011544130069008103401503109840e030395000d906205d6800322401030b0303807400308a40d440411200007291074100340c001280e2096404012101105a00901408482101511090303002d0217603010b0f00d034002d00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 443924892 1250 443923642 443923661
    0xf0904020d020313060b04050402060a4d060105060405010c030903150b03100905030d0b0d0203030a0e1f02030706092a0503010b01050309070b090d0c0e1005240d0b1201 74
    0x1810061b0250714010007049a0702520007940210040c07190180007800382a8903035594040620a144950001810002a810411000740704200011380c807620601040800c018030107480d4080c00b2690304040100301980550321a09040041b01001030f0107050003100a880a9a00070f2540910b40c8e100401c901c000e800c0d0207040e58082c0c89441c0005a00600d1489078968440d0701c00059481c1100c00d050280250804d040042c0c1c1c0030ba00b081a903001680c04100400c1072082c59125013252802c0c1d20100703c411798540038100c14a65090310256029070f800300854100650241c00043d101c0f00906181e00c01600d9180c6450903240051b0450707004840041030764007120b1080700207102e0580d842c001100c2a02050750210352603400300d401804170750710f41c401801c03501c1000b825420061405455006070074046070700800c10021400140001d440030001c8440c042c04068441d40c1059000701c040340041100c828001c5000c072004151034134001d855400161140380000c0ca0148040500c00003180200007044 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 443926142 1250 443924892 443924903
    0xc13090207021c0c0302150c0f060604051305061f0305010f050603280f022d010206130305160c051806040b100f0c11091302010206010b0c030f0904020d020313 70
    0x3654105402c3c1070340700304803a40c4e0340401c650280504d5036003444101c8020000c07007035003801c2c14080710400c2441001081000c85505004015074201002444100d44d4042c000909212101002001107140002c6180d08a1498200031701c11614104c8041080782168000510360350030310b414141981c80036086180190b40071000d42e450402d0b0800900c8074600400880c981c00e82c040103c1d20081210354010143c501c0c0080e240e08825480c840081d0702c4a40300803038507080108440848051075030304111066000310402c61031240300f402914090100d02484004403a0240700c14404010007080840e56801001d0103498508400460f6548034070f800000c448080c0101d18000c0a4a000d10b4402204107601540e9200d01d8902d080400c012180b501c4251410344076221283c232441b0107503e45c1d103081d070712072060110861281000392000904019041c0d0004140000512200101090100c01c540404461380c10b01c130b55130989034000c40d02030702a800900e141e8a1022080081c408540050b0106951145 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 443927392 1250 443926142 443926159
    0x40302070513023a090204060905090d032d0e100f061a12011e031e0b0609010819020118240503090714060913020c0c0a050d0602030c1309020702 64
    0x10f41c0390111900c0c0354889148030340c0c501203141304811000d40c051002507001800216075551a84421820b90381c041c0d4501d200c5901641e984280268580303e0700d00d02400d040601040b0242240c01420705201c4c3c0c1c8080c10801da0342d80540f02c2070103004c010b00c110240354a402400301c410b0752410f0740020520362040c0d002548541e05030000c401c240104a960800200034205c02c0c40e42000321150b030074508803181e81114442200040081180000140c407040444000c448404a4a141440301c070900589018040c061035801030100c03a10201c2c4c0100030b41120280c0301d40d80c801c2c40c00100e50005040e00c070340440d1324040c8000314002c030034609103000c5020342800803107001141c480d04492070700c4200c69000030b03034211316028050200340c2030300c2400d00c44ac01445036042c401c1007800200014035a104644451742d00080c1003201036000e02c442d004018040700c003505080d02e0103001ca0401e606541004080030340c000000b0300300454a1069405040d9884001c0c448070741c0305c4d00341070000c0d4403541c0140e00c6944d16 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 443928642 1250 443927392 443927437
    0x201090609051e070e041205130806040210170601051e041d07140901030c2d030e010204080a0209040507030b04030e13020309031c022512020a02060a0804030207051302 74
    0x2541c40c00c64610350020b0783c40c0e42c1d03031f13403200e24184a13004450380c20408100410a40031140c0640540503015800107060581071505c10030100da00d00035141c1d000e0003451024000c9240e00c00d0f562540c058800c0c20803580d00c00300032840d8071807498101411805001c000c075010500c000041c440d1003a1079001c15007502d107070302c41080c140c070311500d0074031190f282c90341c204030802280d44032303812551000780e042c1080610070200a4008554080da44442d0010a00903880051840c0c1c0c58003401101407445002140303418180381e2102c1d1140c1880e0006030083d071070391001c00c081040c1002400000c580240d5641046d05051600070590146040658820068076402051214061085038007540701d2070002c1d481d141160542c1c0001c203800208424150340e0a0107521842c0514200f5114040002800c800c1451000d2030003103244a0246030000465201140b26001a16044101c548803a900c6c10001e56031307591464100e1a2108540020f40c2005002d5101411308083e500909041071450003000c112160 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 443929892 1250 443928642 443928703
    0x207050307121b060b190801050601180b0901050306120f1b042a110f16080d0912210302070506070c2f03030c0c0307060302090901090c020109060905 66
    0x14100031103074072003c1d01c82c5581d0010305a13622075407004d44003410f280d81d4079250000c09900000241d000d100f099445004105266a1141600c031080007141195925581403541031030341c600541410030306028002002c1450341d81e408100c0d0301c2c0c00203c0812100d00d0070340c4085c07483e02c1d142640c030706450b00d03600f4049161091a15000c0d224002c07070f420030130700680d02c01c09030481c281d25034104100c010301020380303014910007805005801a40d182c4c03e00405115409031080000c040c40e541c00b1542e1a04451500b0302001d034490010b0044516081c00c285401000d801c19004425461010321000200c41140040c115016005071621500400980340c040e940c0d504140c50140112500a010101054990000f036008540e030b039000c143c00c1c17058501c040c202c40012a1440c0c0c002c1442c1c0ca070035409090102c1280c0707002c020010281c65946411f6017003202c884003080c400c14042c0034158096848440c0780061610035442140030b02e410003800e00004003242030107501d4030480c0c80241403c40c0740340742c81c03031072201c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 443931142 1250 443929892 443929907
    0x807090203060f13090f0c060e01210e100903020c040501140906041e06140a081906180f03080406061715090c0d03030204140d11040e030d020705030712 67
    0x2016028900d0440c1d0396013040b403112640c3c2207042850340e48590980204082c0207070210800e105810501c4440c0c181140601142980d05030141000300c80c543d2030b03200325054400c61401c80104034011407080d00c00340b44c1c20308104544220201c41e915003100380c1c0505500090f01c62100301d09641c100150b03621a048514407001202c2a00c0e04440d080300400c0e4a414507511100f05114910445400c0c0c0c060400e121090310429480b10000714418011003a082c50034403049402041c201000702038021003041c44135015020610b024144581e42c54801040301d10140d50202c41c1c41c0d011021461010310f5240c064440341040d50290399540c6012400704110f500c6958a0001c407010000230643c0c00c10010131040450300040c40b420b07842c041c0203d080c4d015181d151a09040e6403080d1409a00ca6082c81c0d102040040428100c2c0e01c40d411007000302e40070030176008181ca001802a603001c44c40c0700325120020702c1d6100741c02c10383c210244001005010701c10080060326525104204820b02220010380850310030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 443932392 1250 443931142 443931151
    0x140c01021309090b191524081b0a0207032f101d0a030816050c040902010c030807020f1c03140f010e09120d020703170f0106030b150c070807090203 65
    0x200044e502107094112074a03150741179510411000300d0000070117072034400c4080c1158003003007034501c501ca80325a190b00c1d075880c0c01120b00994940041185400000f40100708054200001c1b5070350000b071132044461081c1300f8a005107400c400302e8640250340003200030004800710040030044c0302c0891640c0042c80e01c007040910303121190751401c003000c900e1040000c50b1000b00d003501380c2c01080b030680000065070b0040a4045441c4041641744802c2290420034184852814683d1080c2d00e410066001070b0b0b005004815216014a40f540f025607400b40d09a15146800300b007640b4a106001604000210811000304200701541e0140070348101221071075001e05054882d0b10b0b440f5000700041c4100340022641d50780c0a1212822244001010308001d45964020760200407440c0d0001001c00a054100c03a507080075500d145003c2105142556075001034010600510341010346032800c4501076502c81c00c2d0306006040140c0169981c0c9091103c6981d65201ca100322000b5000705040000ca6207014803e0b64441c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 443933642 1250 443932392 443932403
    0x703090804050402090303040302120601050a080c010207090221010b191d04110f0d02120c03060102100b0a0e1f0806010f030f06090b0f0f0105030102070c090507140c0102130909 78
    0x910b410036041101039000003841c0383d00351106020000c09070780c8003609036a00019650241ca01941000103100c81c5174aa60480304441d4481000c0740d1450f40c0c00a4620126141c1c0140161030b0184510b40440e00c1543c081c29801e040030010000c11104801303401062540480c05501030825000c58083d039040f1004000c0d000742594140240c0900d0615810405e02160001c0003c1d1400110f6011890140c00002e4114141e6a02058210b4400250303010103400260b450340c01d904520b0090300003507845c18100401c25040b0f403075010700f0703030280c64180f2180090312038005102d41c5840e2580045180428042c4092054a014080058819000f240c242d042e00c2e00e2994080265095881d1017490403403019080301c07c1940c608240300861207401c00140100860480001e0b02d080410b0428182e12040c0c000900c0703640f041016900003014980103608071220708c04082825555101e0a5601078a1030002007000800000c1c2604002c5043d40242141c160220018210b551510744010031100482c000030607 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 443934892 1250 443933642 443933647
    0x507030614012a02060705070807060e1c1103010f140604150602070b07050c040507050d050f3102120307030305150121060b0a020d0905060711011d040513020907030908 74
    0x44410b20f41201e00c26940040d040d2494074450340c0e01c0510740040c5038401c071241d410000003402415800a08109102030844840c070103110b2003940c1108510001200400301e000c0240c1e0200e01d500c00b134004511240c80c0440800c003200e4030300ca8050541c441114160f00c110f04d0007480104888195148205a0703010f40c1c01043c54038141882d0300007a40c004003056030984680360b0b450422380d445000d8284100d28a94800c0e890b81c0300204680f05980000e040c082000707003500c0400400e05005084c4019840c86511004030440741c85078a06041c103904d55002c0d41003000e9000600482c00008010980c3c0c600ca81d40070072090b07441b4000c101411080030790040c000340da404000d086580340409510003803001a640010482e681304400c030441c1c0d22620401c0d000d03800c610040c030030300b68000340c011000308000d69945240c410b0940d2b810300016141c040e454181b040321a110410124031002c02c0c00402d2016204004504080104c03007201c0c40e4074203080340704800040004d090302d03100303004040c45664060321590 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 443936142 1250 443934892 443934947
    0x60f040213090b18101103062106042102030c10050a0e0a0c090f050624070b010906091802030d0305220c090e0f030f030a0e01050703061401 62
    0x20508400400104201e40c80d40079200200d21500800d03405481003000c1c10042d4942070111500700485d050040e000c5510704121810702e0150002101e03806070044403004c0b036586a083c3c100308003100a0410144078415030003040308114400426280d00411600d4500740d003400004100d95a01c104544406c0319040868210132030007850b045590030101540c80440c994148810280c540782030100c00b910b40b442c1080c2c040016001602c0760900c101c101c00382c24007040c6480b2020411070030b07500340d004034a00500422907090b9000841a69070060380101c2024195950385068005401580598031070540340c0811040c2401030586004901036018001c0c3c82100c0307450303409900406004149152031a032701e85a51a40c00c1023010740000c242d22506400844078240003803182281d200c8610700a8980c010050702151210000990f0900c03611540c0712507890756990a110040e100ca001d540e12a0341c20b002c2808509901500040b09079904803002d038940000e00c1004544280c00802ca50820307000291009 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 443937392 1250 443936142 443936149
    0x21218010c0f1505070f090f180b090109060509060418061e090f1109010e0103120201022506050a1a0105032212020d020319081305070909020909060f0402 68
    0xd0380014080c001d0b40e00150315584480400b80a40c5456010040c0d0b20710410a0190304440d00110684a0703103000190300d81081c0841031480114064840303855060001035062000710f401415208001501000495070354401820152030035001e003902ca880140000792407414076100b0a06e1803524500070928488840d15031800801492800592507040540101009211409043e400510035024521002101d00b0046100510012060300c0b84000a00400ca0450890501c0e41980d8020507405c2100d0003d0030141c1c020710403070001c1c41248085c0441680c0e4505a40c41c04403115006042c20700a039070320700d10100219001c0c41d11200301e6013400c8018044c40d51103200070303651001c8514015412103405600390310500c424003800700c840000174916001c10310381c181b200201d00d014600046041c0301102440d4042904009645800c000c004000560310700c3c0c0c1d841748441b40d20380020545e80055210f00d0b240e0003608825030300307034003925036800130422284000609a00c1344606240c0e0171084c0e116a403c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 443938642 1250 443937392 443937407
    0x32070b07020127050f0706200c0d39080c04051b0901020316110a090213140f091609170604060203060d06050108150c030f0105010f02100e0d02121801 66
    0x70b0340c10340705c1c151803000211020480c840c05010240c030b800ba54807000074030444041c001400c20711303180e420400620300e0540380c00e41000c56007984002058043e080d240c0013104654041a161121043c15480d102c4a031400e0070b19440550700000151640c40d1100001c2c0020f582c0181d41c5000f161002440c040000c0300b8490207003030011b0052055030700c0c080b6281d80700382c2c400d002400d0036a0318441c241000300d080c2c5082c030102030050408200a5003011010380703216044465034402c501c0da03200700c1d10249003d66a041000b0140c1580145151001d00707049504041054a0500d03250206d15003c03000700b2142d00c01c8019203102c0003c480201640c3ea1903989582c0a03420241c0095000f0540014000014440380500c1e806800124001c2c40601c00da109007503044ca4018007201003002c010400d00002161a900040c1500c81c2804e04440880094004070324100e5a0645244d0042c90061288a852004505822002500c0c1d08887c402d035100310140206100c2c2c3c15000a4101c040e5454800c43d5000302d46 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 443939892 1250 443938642 443938721
    0x80115060809120c031815070204020313060207150c0c0c0b0d0204080f030c0c06030408180f060d05100905010f15021509012c0a0332070b070201 64
    0x103070383c00d14001000350300d85030b04103a030450080d80020414006030308040d10000307800340080358000c8840c000304070000001e10030034001038043e64000000130940800080c8401046034061400c66807590181092249000d601d01500361f80340c1480b11b58001c0074425410920a0398100c2030b5018814540584080290b000c5402e1130303e001e400744030020302a43d0901c000407682004101656441201c981c1d81d60400d100458400d103e400c0500510011440110070b03110400a20100f001080f076401e000100040f810001c007580c4000d001400b550070120907003009014080ca0224501500d40310f4104e001680c509001c0d55103051456081003011204081c00b101e404042c600685400781c000200219a03501e0444280601ea91240842c403125100100d00c0c15102e000e10107850761440d4010300d8035403203141013000942001600030010840110440c51900c0400b0008104500c95040c0d10b039202d0070b82c02c9800c0550316005190006000e0b00c4c0180a10401d159440b10001c0c051040c860804031a05507170341 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 443941142 1250 443939892 443939911
    0x117040c08150115020102070312151e18020a080f221208071403161403010e0915010305060711030d0e06150d08180310050403050a03060801150608 65
    0x40005000101440341412490352000c942d8602d42c100f0440d8040003410407451411a8810059040481c1d84100540c040703002066004c40c07110244030390071005010980240c0b40b9481610034580707865554800c0403088a400b03d00b10320900b651004400224003400c02d1045c0032480340400664070417101c8410030f07030214011003411130800c142482c0c50807207509084126100d43c60010405980d51300003400a6100070355283c01003030556640c0701610715000160404540740001c0c8108508a809005044020000b08a1040d100c1d070352000310109009042e10401030a004590130b0307800301d0b02d8024049050340c0e000401000e498403021402c44207070722100488015030006000844c00d542070307030040240c4440c140004002506200b00c40c0c10401d5807038041640b0640340700c822140055007a00c19142050541901402c2101c02c4801290624481d503985000c95890b10080008154024010f80b40c81c9255a900b001176907103841c3d039142219040c000c83c4010380b40390507041285070312848400b80c0c0300c60b440 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 443942392 1250 443941142 443941163
    0xb01090903120c050918061e0109120c0603060b03090a030e0105091e1005070c0b03060406050a0306020301030620160206041a0405090705040612020c0102120103030c0c05040209011704 81
    0x28040c0441d46070507840c500080e130020702c4001a1500030100c507076030007000107554020b00b400c000080d80d0083ca0042490030280d01c07440d184540c0c0c01091120002d0003403050390010303407050303103840c02685040f40124000b00380741c820040b64116100c41a240300740150002401071081603242601d07201d0f17004070ba481c1000000c000211494a8004d103071500c200f01040300c43c503004448070800c60280e0744156460100101480444003042d4035540980440d903902c8805030396030702c5540105018241c0c50b048580c000041d24000000c0102c0c590003181243c0c0030325000c02880e4007240040c100c40640c0035a4004500042c049a0310b100d10f0f108400381c0072840100480d16155465442c7c8401003c20220ba0f000d40c04007040402c1706040003a01a60f0140071441d000d45080c0c103055000e02045c1c0d5a0030000c2000c0e5020900f241c0aa100350304903000d244407101214100d40e502d207002081001c03500380489402d8030040c400101d5080c2802542c0100805031510407066200d01c000f40030500c0c00420a0700c00d410300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 443943642 1250 443942392 443942417
    0x1b05030c1c0b0310150302010e0316080f1207020f0f0a03060c02031e04050307061101090b1005040f0506010f0c051011070b010f0e0402060f0c0f010f1104030b01090903 74
    0x1180d00300c0300c84496007840071882d2501502050b08011444010703855490410080014002d0500000401d5a81c2424a45086805400460f280000704506041107074145007010409840000d000a1824921011181d415480c0ba602d445c186c000d01c02c000350006960203400096140c8000100c034260405440c101c103140c8da0761a1601038034400e19480b0056040094010b200c185640300c0c10101c1d4070010345940c505454113010a55030302c8140308070b0040220584a103a00b02d0b000707401100502e0b030009041c1009007004021a04a0000c1d449500d20440c81e1042819003116540a030f10710808050f10f48041038000003106540d00e844001044429000c0da002e0070b0010f203031070300c980d4000f40480b5034101d807031700b260380f80502d20311606800441400210a0b8200b00030304120f00d03490350045d419a895500e5100c0c0c50307035007090760240c00c0b88400180034803090304c182c401c4154401c1c05251070200050295036601c0d401c42003644214080501044560001884203000c0383c0c005180141c880e1824a1001d00d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 443944892 1250 443943642 443943667
    0x6140702130204090f02040b12180115060906030e0709181b1d09030406120204170c0a090c0e10140406050705070905010605070f051e100501091b05030c 67
    0x1611072114400941c042014414021070303104d040c85409110204514290400f22003c2c0ca82c0240c1003802c244007403590010342004021090b000f01030805600034009030503103940c42c00ea121200e000e8800015081440021107502c07070b0242031800302503800a0400780c0e0412120303c020b842c0c4200301441c405c000031041d50000b0800d4603254080c0c0640000300c1e0300d07181840300c0e50301204080c59a2180e0844590280480d14030040206e0b400c03900d05080c4100842c0d030514121020380501e900100150315513000c850311541c408100302a0b000740c21584954007507115101141103805c641010b00c0041d240580d69200c60511407151614414581880d1094400c000c140e49501d900c580c11400000728007003980760801404005207409800f0614051115605184c1e00501500803544c000d0300071840b50220f40c00340b20b0188010104107400c52492920b01c900f5000543c5d542d128102c080c1d409a01d00400011464800e124014105200d5000348188501e0311000711540d0b080948068890101000301d10403000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 443946142 1250 443944892 443944909
    0x2091c170d060f0f050303041202010314040f0b07230d02070506090f0d02010b1e0406050603151c02100804030e0a03060902100201150b0c0f01020d05180d0906140702 73
    0x260300300c808254a8200142d083d200103081d4001d1590208028080c850741e90040241c0b015241d81000b25081c0d11103d000407405452800f00c1d80151050746820302081c85907900c01e160283d40a82c00190a5494a590403034030790031000ca14a090035080c1c2407662038007030050000c00c0003028040000d070820800341c69040c10b0007020b41c0d560003607074400081180503010600001c942915113000820400901c03c01103450707010100503400791600722418403a0320760380d030317070302160250901070025511303480c01180c20015035074510350fa50f20400d603030400030008408440170b814180d5070250280000b071040d0503054454910180048007804500e00c00e4150940b54400000c00071400f130780c8089070101081c0180241c5000036401001164103007402649031160200070036088810080e6040d5407829030030002403c1c880038a540c01034950000500448a00082c1c0100c0d00581d80b6141d461007203485002c4803555408448180c40200fa100e060030043d2500078058900043c8a4060030b41c50000164001100f12 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 443947392 1250 443946142 443946157
    0x204050a06080d050a0806040504030201090c0b03190b0d030c050703050a03020604020108010605090a0b0d14010e090d050a121a1008010603050c04080c09100f0b07110402091c17 78
    0xa0340d8aa80c108242c15040103003140403003284c181a440d058600a0041040b680240071030300940c0c49801003800c15100754040c800841c0c1201c1859101626014a41c982e42e000381e80c0440d070610200c0030110803088034429441540001040d40c14000c1a030f0b94143d60300b0b1480d403410b88042c00341500001c04564188203058443e840b9501a000a160610016040e050103070070440402800b40040f40c10341d16010280015189a1182c40351184140748040028080e180280c1240322540c0c0c00015542c280b1201850159008801780c58910308221000c4940380104510b540016009040018041036103510200070120070001002c1c00c9d060000210742c20507142c064250000b0494001002015458070405420450b00e8560a00e018600552103a44207219610741d440f5072281d20101d041c2d0a18044014018032070076042015040c3d43d809000700540142da820b840d6a00e41c2445070103607140a04c2103070202d0a004150001180d818510164a005000340441d0350354607030780504420702880006082d10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 443948642 1250 443947392 443947411
    0xa060c180824010302030a020904140d031e020306090408130b04080c030105090f030912100e28030c080304020a051908250303050313080a09151821020405 68
    0x100140003182c02c05229112a401041090030005100517940814610061a0120750107211900c45d401c1000c803200041c41c98000302d100c0c0079144c0c1c0d0308980541100c0900cac080d10b00d400441358070780c071342c283c00f81d00c01151000d612a05040006002940000c081e02d0030042189230201265265509024a5441604605041c0d8001e40c144c0e1010300d024028103900000f290302422a6503d055001d039680d0003401c600601c950b0202c001030850100c05c00003a0a0380800000c24040318044203a4651510110340c10f805040200000100002c9022007035200e40340d034196161143c03c055070f00d4a241581014004990008104400003403e90b684c0003140442e510010415000364a400d5101d440d0440211441599403810344d46040e102d44142c41c01c404480d09410003907569541e414100401003a100030003070000001058440b0002d502c540c00c0703020740d03400c040c0318a504565154141c901e030800d64020011944844010310480c840d80304158290b00b40d0f2a0122004410b541c0050103441086511010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 443949892 1250 443948642 443948653
    0x6060905060f030d050702270412050405030a0f11221d0d08250215061903120203040b160b0c0a020706030504021201050411040c02030a020a060c1808 66
    0x52000148602904090101c03070400419107500046a103414500711140c040c070070b011131100e0940d00d504481c0c6803400f528180c1c0b4140c8d010481002d2151500596059880e00d83c1034003a0701005000b0002c0310150390300180101000754141d500c0807001c070f030103000c200c2d002c1c45030304010901d549514a840102c40385107070031501070700c036480409822901c8004998a0403402c01200c22200c150202c1c40b5a040c3d9110725100d109036490740c0c5844001c515100c4030b0780030580c403007005120a90340440c00440040303001e492035a950303c600041004242d80c60f01c000c0c0c1c1d4100342c4c14080001414280074451516403c4c01940e0525985030a03203440381e004400082d2040f550360070800204000d00c44032980c011941240d60b824014501e0000b0b640340c0d61802036506055440b0085000d541c0c0d200b04481b550034402c8001d21651a00346098401c103603c0f200c02c64050707410240700700040d50012054a68000d95a0300614400e40562600d40c003400190484100b030040420550302d0400c0300003040006814290001d01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 443951142 1250 443949892 443949899
    0x5060702011b0207050105030103060b0f0d06050405061003080d090510150e09030325140705030c07050a05131d30090a0e07170711070503030307050319060807030606 73
    0x12812682d245034045400000c002c0c07140c0d81e00102541e06403a00004002184041c1d400800c0c008911210203681c0801000058010403c1c2500803030710440c401d00c1a50081d84a000010b1141e4040e804020101a820702c00e259104840307510060866010b075084400b240e40898440048030345641c000b4020440c9000184040400400100c0c0c01440d1580214034510300001e486408407c031715951298820b41030126401d545c401d005444044515018496681d17155141c015030301da000300c0303045140b8081c90b0300000300d51415201d4102107410140c401e100751208d0010903001002c0c1307000450060840c40f05031081a03a001c0100800c080e083d1001440c0ea5000070701004411315103840c41807800f0341c0800c5a003881d600e4190300d1808540141c2c01000050b15000c0b0241e404000c13250b031400010050800f0000019804060040c00d10441d000765050345813203105242c0c50348000c84458011420400104500d035080880054903c001d503000040c00380c3d2510042c50915409500685001c0e481d0300013070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 443952392 1250 443951142 443951171
    0x501030501080303090a030c060605060f1b0606031b0102010908030106020d09080d0f050a051b060a0c0c0c050909030c0105040302010f0b1221040b160302190b040213090506070201 79
    0x440c09801800000d40c25485c0c0b500c121680c403000c00038014200003006101c0400c10400360001c4000e4000100340399160454100001020303000305041c0356007404080502e1500140101d102800b03401e0160103800d49180c1454a0b41e0000ca414081314119962603030144049020280618040c0105a01a11808040c181300801c501702c2030300829201c0c0c00800c01280c2e041d80001c0c504451540a0034100d840700e0160130b080d10702d401802c04061402e80022900d0180b642d005c00c0e40c5100b01c405640421182030041000c0300d6180380f02c81d00030300104035003030240603a181800135103031301c042003100301c9162507904060242034078001d89041340940e4440744032081d500580c1c0602e00c4c40400c2a106c039184000d45900c4140e841440300304120300e00e000050f00300c0481c00900c0031203002c1d00809020f10781d500d20f400c0d42d0812600c0351002c1640103008260f01c0180c03000041d00482c064507002414046030303032140d4003007100f110040101c04904964524452001610521605110f46030070340002541051b05880c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 443953642 1250 443952392 443952401
    0xf0909010b07031e0e0904080f030a0b040507091a0904061a030906070f050315011e02030301050a05040203060a060e06090a1502070509240301020c0303010e010611120307260709050103 81
    0x4c1400040d40318200c280141e40704444071440350301221018100c4c0c60b03a06000649100d8146c2c012a811400400c10142414580000c8000682907070104156503442200300d4022082d8020f40442c4050404070b80b03400c000c0031014040d2040002e2000070200d139201c011001440c0ca80c5452a00008007000304489000c00f80700300c690260042c00c190000c075001140050403480000c158128240c4e808000c0315059205000c0111000c88229401d0740c103025035135000e5070ba50001d119a510aa128071804a1541000e0080c1c1e03010300c40140c1040c2405062007800d4a040c60502d070301036004207040c4901840c0790780d200512001807907400d154504264000d5802030901d0216007003940501c22903410300407414842c048440c1917907445014000030903100f40009000e40b1a5515902d854480400045a40041011128103c81054403032a2900c410340100c076894440c0d13105448407001c000c1c40020102c41c0078121241194021052100400c4200d80801a0b4040b054401c000020366110042c050781d601344c802c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 443954892 1250 443953642 443953667
    0x2a0b040b060411030402060d150f030c0927030c06140a0c11061506040b0a030501081c0f0e0f030a050102030601120501050d080a090b03091b100905060f0909010b0703 73
    0x24103000d03081030511880703074078480031700000c1c003a510006071002d14074019404600c0001c0ea50045131413030b6940701c000310305807052804148c596526036880019200c0e020300c0b17035003035940810500c0d9040c04900e159488400d00f550200354140b03c0c86a90400010320244200060704003103d103038a2290a01c820004202e40c00300340400300307000d810260b0414072140010203580c8946803a1a800ea4981c010b40800c00318011540030700d0300d00e000420b000d515540c16411140c10b0f100510110f5180300114000d00b10a200100030101c0840c202c51034400d034036807048040401b00321019280304c500002c09d402003480d0000031101074890742d50110605c1070542c1d000e184501010207000f0b05005650508002580401041a0086c070894000941e41407135409001044010718080c4005601ea151100300261a9010080902c0d04c201802210902600d0109140c0419050640e074400303d0301e0070881440350b194010840c5082464081c030001445641d001c180d540a04030161245031500218500039048510280 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 443956142 1250 443954892 443954899
    0x108010504170f1204060c230403080a0504080f012007020a0e0a1b0914090f131b030c14060708030f10030f0503030402010f0201020a020a02012a0b040b06 68
    0x406110100381e007081c1c0c480d900c2c0e914665183e51029140480d903490310810360040c6900726180100301c1400700710fa100f050010030135100c1c0c04000d440c0410880101c14900003d007170f1041e00703200c1400840c98000c0540342012190a281c0c0c9020b45403103010340f418066505040e4942e4441da000b81000201403040e001c001d00c03600b44241418410f50010300e03501c6250082503652091040010b0361000340e41c0049440c40000c050901c01c03d424403c008200050034041c603006104942c1c1441c041e030170315800765032043d544003428501540324140e5640a440d046542511520155200d150052800e11080c00044d0320852800b00064034003204007a200c5003858045214400078002003000c51600700807a40e00200c0400040041e80c0e1705110b03900301c86400d400c05841009600b06000c1007120000065001e54001d80b181110f450f29440c003207090b84a07031404980141c1007509800b0065003c2c01041c2c1882544400c030034902010710050094200c013144081c3c0d203001660052006211603420150740156003903 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 443957392 1250 443956142 443956151
    0x8160e060f0c0c0a0602071211181b0703050306040b030a060f021b1501030305280504060206060f01091202030f010e03070210180611010213030302010b041505030712080c0d03090605010801 83
    0x18806916401c441c41078211002280c01d0038010031000303139030803080d01030f002b42407074541061180c100841c0c20040741d403910350a070384001003480f13100070409403140030340c0c9661400e00d10703031301c0c2c40501015120b4400c1c91905071182e080d4035070001e07210313024074000007604d0540161120300c80034941d1002d800700c821020054004221100380743c05c0200b10030f030650b501810050b6544441c0d603041424011100000030380312412a6120403079640c048018030884010ba03003143e1300c0703441d5001000160450b4580342401710350200001c100810100038100c040c0c600007010741e01c221000001c42d82c2540c149402c0d00449070400191a0218500540c4420300840030303150588100c0010091554400181e0098909001001010403900c040c25012244140c28210341d00c481680d9a06d40070b400f80296203015841b403824035421074500c580c02107401007240c80041c000d19546203000354040469503510825120000c0411002003000c0c010002c6010343c1c1039607500060030340d1700360829104443d03041e005148180d052 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 443958642 1250 443957392 443957399
    0x1c0903050304030b060607061406040506042901030e010204120203160b030f0411040903090f050d03090312031d0327030c01120605040c030e0610050108160e060f0c0c0a 74
    0x2d440a0301c0d400f00c40040e9540f40c030800036026015a0310003c080509107080030900c200c400c51018002c1105540c1404030343c5801081005807581203036100c40280310009951a404001d1084804052041c100014002c00740002c043c02c1e64081d07000040c1514001018a08608040151402c3c0c0d1180580341c44c035041c101006039500b440040c3c92240500c2000c1d020505208425207080d400c44c0000380708100d6204949005040d554030342c46005210181210001584d080480c20106002e9040c0c0c0d170141c60500316603030080e5825207401080c0030180d550101c0d8036810b95050010b40101c6103040216111030001c0180c0d00c7c4104104404108202c41d842e030800c141c2c8002540e0210401c003400e010300c0503800c000e2000e0090038a0f60040c0e03809800e240182011039010340c007072140340ca040c80545d401070340c07001c00480e0010b40b070388505400540c001c000100c84040c0c41074020340315222858003540203a5501d002840d541c0040c10b00c1d04007504001840d0b010f24004100d10203c0800549610340036500c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 443959892 1250 443958642 443958653
    0x1d010806090a0b07090b0a0206150402090d0305030a06050d0311010b0406050f012316050106080303040b190f060e090c03070608130c080115031e0804092c1c0903 71
    0x41ea01000f812900b00c100030400c00350080c110700e0060162440015281c05429600a503244026142808038024036a1f100324181014001c0300c804503005800707980000a2603800315100d03407000707021140082e035400d0007103925aa4005004540c60181d84e40ca00300e000034912540c2145c074041e01040c0b0861611078100425220030201a4000c042402d00080082d10301c010400796680007410500004000201c074462641080384494000d401030b00200045078440740203076524031080c1c07005040c00d0100d03400130700b2095000042c1c0c0581605400c005c60b404140ca4626400e4074040d80001c22400184070130000280c000704000103111104400412400745444406441d911001d40000886c05141c800d00041c0002c21070100e000b40b801038001c110319408210019003076050f6000c2286c9201154915603c0e20f03e281000000c000c1e04221014a8146450301210051444a20360782900031a06465840078003100e40000911040002900c154801c071048502e0584100e500f40b0244440c4440c14004904d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 443961142 1250 443959892 443959903
    0x110c0d033609021c06030303052a09060c07120c03110418060b03030c120912030f040b070314030703060e01090e06040b090a051204150908151f1d01080609 68
    0x115a0b120040e9100c040c0185222800d4000c42c100248034141480081091b52652019201d1444c1d00036102100b044d50010001c0c00c264100203c2c0140f405000c0040145000c00003400034000701d504540c1665074986111b1080e1403581c0040d25518620742c020400d114410010001c1c0070000c903020003501d58440501040d0045c6400080d0110355164007800300c9403010811500c0c1002140304940c0d6126503038540c0140d036401035801e940581e4050a42c804c40301000020380e6501044a035078542014280301601c0c00300d4220507425010400c1d08518607440d0000000114040c08c2c241c0e13004242c0030b0500e030b107449901070186d0188205e9841c109003104550f1011480d25002607000c5e032034010380c6d2036032440c540c9402140032001c0c0c141c0c0aa000549400003a04000b84102c0d000030070300386c600200802081e12143c4051180540302c0d04100003a0501c420395038002507110306070702038240011803030803020500a00c40790402400f4a41c0307400224507441071020320500600707180c40100b1007807404940241c0c80e032 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 443962392 1250 443961142 443961149
    0x3010506100c0f140a11030c0301020c060c160602030108060a15050604060e120d0206191103042402040f091b090b0705030702060f0a1b05060106110c0d0336 69
    0xc05032203601c2c000300111603000d1134a44e002813007140d0b101d07151800c01e0720500041c0b1243c4ca1092041440078000f500b41030094581032007134071010340303040d94600b13000c80b81c0f540c0300442d0200c2c1a50300c9052140014460f1020718080c00c00d00004200500d803103240030301107501c6040c040311595656003040000e1b558060407242911000d1a0840400042c0c0011980c0749403101040ea103540a1056081104c80e0700180a920841d0031004c500c00401048100ca400c484a250001804190800008001c10194500c400c0c5110f418809101800800c140d080101c8e00550450740b010700381c0d8202008040041e0080340402001108440a030510b032a0010b042c81185104410003030380046148814803005005841c0e0094015180d035580b2404400c2441c0903034825100c81b80826944409918060802d0311300700c004130351040041080307909010302519a5006148484003500ca024100d000c243c40343d0880c040307514444e03143e9405104d00c03408001a40c04040072481e1020490300000c500008440e1140000c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 443963642 1250 443962392 443962403
    0x60108030901180305030d140f06060a0309020f0909070f0b0f07030f05190c02150c100b0301060b130e161b15091a010902160b06010c0f050c03010506100c 68
    0xf40000038003068060b29a4800b0700180000314501e080ca00103500405011902d50340725408980d82c0786601041c580d0151303250b070703000f0109000084140d4080d2b0b00c1018118001005007040115203400558402d4003184c4209150300b005200b000681c0341540b01501518000c1490380c241020485c99039002c1c00313142070203420021540005e496407800307981107641032000c458804442500111003d0300d5056a40c0c4128021490300e4550312503148840144d81d41c540c09403002d0401d480d01c610340c0402501e072500390b0503415540d034030002804205100c01840c412054609540445207400980c800251005060782d11104802c00c41c00304040d0301840034002186c0c41e0105606400d05810301c04045190060f92603d89480d200f010030921102c415100309440f041c1000341c2d4a03a0300c03004000240e004044d03902001503006084035000400c2650155484501850424071006413070b2110180c0350320421007580c143e000382c4001012402c1c00c1c00b50650022098444403001c11030260020f2181040000c003a01d07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 443964892 1250 443963642 443963657
    0x9020a020c010f230310080d051c0c2f01140a150e0f0406140414101a040b030c03060f07080105030d0507150902280e0907030210030b0402070b010302030f060108030901 74
    0x1c446c404440c8500a009030360704039090b1542004002d8020343c48207914009044135500414100b04050161002810071035669070481280752101148602c80084052000b206800c40156188400d00c5503200e80c6150915490850814848000403548808503a400c405152402404031002c40074041d60450640c448041041d555828901c00401000f840b40c0911240c04082c002403000c05086400002c1c0c080082d1050300150500900c220361f5220405012421100324101e0b0310700d01580512611000a020b448514103060002400c00f00c003101c11b20b80b4148500c06104402c2e41c4503d4842c00351a00350002d2401300796030f0030040c180b80607145009190180702401072041400940011403c2d035405424552410035540b0320000c3e640c0700883d4011440c00b8502d0014640c5c613990038041c02002d40c4800782086601b9070b000e201c001c022160700a41415101d01d0f007048075440c0d0384020b1901c2c07805a40510407a504620400d030070040c640c203104841d0740c4641d005222070140803003200d4800c42c3c00d007404e00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 443966142 1250 443964892 443964901
    0x180906100f18050d0804050117010e010603020a1704030512071103030402131e0609110f0901030e0a0c03050a021309020f19030203250b070b04030804020a09020a020c010f2303 77
    0xb19901450b04001d40241403042d101c010050020040e000341c0701c090306d86078040f03d0100b040d0920390f8024416403822030303c80c4004001e00c50283e4018540d040f16880d100501414420006580c0b81007650200c0005400084455500010040080d00030705a842c21804e42c5000340c400035602c0c040540064402d009003a030300100692300b40d000305804d48202011a0005c58800d0000004050a12542380d200d82480040030070264a80300b00d03a4044540503004d401c1c00181001100100b000300101812840b4100501c000304242d07180e45001584114020100300c005407042c8600b901d441000d40781103d040000110069a8030003801c214040c0941d014020a0315114030001c0d042c0d400c0c3d01c080e40500401c580820105201450304069100c00c440030944269034a221400c81d204040000d0448001d5101007030019100702c1c0880c2d0050300003410300c130280d921006404102d901c296804405648500306040841d6040880300c000b0501500304190320070728080b11640314481c504405001c01c00d0010004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 443967392 1250 443966142 443966177
    0xe030309060a111216020601080a080712030608070314010f18060903091203030509070509040201140307020304031709010f0e06070809191d0c03011401050d0b06180906100f 76
    0x6a913142500491104541014400704241080d40c1501e4030040c010130001044400b40010042c10f0030303034440406490b0220580b81c007603480310244141020162680c1d00081c182004200070405140988d907508500c40900003880d084a00c941c0050401ea1700301030030800c403aa100f100c03d0340341c10380041e00450328004a240450381c07800c49400404078054110000d5040c594594000d900c5502c14030708490003203880d2820412041421140240000c0c1409130704403000c171441003d540c22031094011207013003985070b907945c8452607a040800400707440c0110b00f03d8903c0da88640c0003003d0781d0003803d20320418191100466a80c1c85150b4000d03000e004005503410740c41c0c88000305900c1401481500c00788040c2c540c0a00806a98480d1400007003040c240d01191f140c05d084422641200c500e104031440500d40e420054910390403c80240040695502c9081d80c01c0e00c0d050020680e180c2e000c003589a4002030b02040114042024150602a2480b4aa08036026402c010741c9a080c100b1801c01c001d401010b02540c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 443968642 1250 443967392 443967397
    0x60307030c1806030221010e0402010f140406080f060a030c12261b0609031b1e060712090803070e0a0b04080715020a0203070302060a090e010e04060e030309060a11 72
    0x550304403082c92030b000a00304d82c164007502d841290304016010708100d44080c500c400c03000780180c484805814001c00d00560244d2101c8141300440d040c12010302682d851000b01c103420680c4608082500c0344c00b00301520038101c2c00c465102e001140e00082c22400e40d10750881d0b41c4c0d05030240d00c507954942d4401d0800d22001c03c00c4c15040d41d81d09a014124120961000d1445821510340c1d0386070b80c14100140518400d01260192243d51218015805e0042c040b0026440c0b101880b000e442c0c0c0d01500110a10303e518444003002203a0201c8000d00041c181218003d08040d040034080c403c1718549030b81c1c0c2001411210032071303400c0311084c6410391416046200140310120303141c0c080307006030713100040c00100c0d00008507811040794800581c0706000c90b46d41c5400d0340c59004e149002540760308141c0301480140340c6040a09807110640c034044500070307254201c1150602082e0410082d400360f460420082180a01481e040d101c904800f0b0b40c21400d000ca051030707a44601030030715070043d0348a0964040b080b150605 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 443969892 1250 443968642 443968667
    0x15132d080a030209040e0a020103201204031e020d09080304080327130507020115030803060d150608010b131b03050912040b1324050306030f0d050d050f0105060307030c 74
    0x100020f0b016130101c1c0e40e1f91000c21004901090401008520200f0403c1d0818003800054400f0703458503498544140030030320001d00c00c80600c4201d00c0004100640c0800c80003154419400510780c95075164809002e1409a5003e44210b90003040705000398100441940c4070701040b0b0300e01804602c10900e801000c041000f6069030006c103410040f00c0c40c00e11940006000b07a106800030410009902e95070320101410780005000450300b000800c98034280150b15055260150f0741011401191600350020303a4100d03806020160b4440420f0485854a40c61000074a40c80040402044c04902140140c0f1414070024209166030b40c0d0004107461024072482c6203101e070440550360341c5d42e110f0b00401c0c1e0f690400c0a400c40c8a2400103c04201400400603c401d511608116031030182216142201c0d194001044079406014500f0b900d482c0c0d800c10806411a00007a444013074444404900c1c0c4030031120010051000071314014010070081d25244d0450340c03c04020314000c500e07040840402d40c2c40596880 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 443971142 1250 443969892 443969899
    0x3220c0503030a0203181f121e15051c022206060917070612150b0703030b01170f01060e032b021203010b0f0c15132d080a030209 57
    0x6a8141900d6010008103c94100612803848003075151040c0541300f00f2100c1f40e111454a02d40858900301e000b215900d00a03420700001141101803182c4130310994681c44501e00360141c403081d89041a114107100100541400c0c0e0340f081e403103040c00d03072400028090030001a00407100000e081081034170300252451507031445070047c01003a550b104010104809445440444110410340380840c440201d40101114010740e51020310300c0b980d0001c007008102c030068002c0c0d803c0d1a0383c030003c1d001c14804007030000b41d07000c3d13140015103480400000d000040400c00d10502c901c429401c01c80306036640141c41e13043d5655441c1158400c2e0300900442e1810380400d00350641c1004d240001c1c031301d030102651045040702255003541e50908800030842224042030280691038034050000c0c078440362103900544941c0018008030b0b210b0005041080d03442c1c000940d5031741141c0d0740c80d400c98001d2040700702c0c444101004160544600a04200c040f40c2d10400c004002844044006100d48a443c800d0301036603088034009 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 443972392 1250 443971142 443971147
    0x5040804120b0f070e0a0b090a050a0e090d090b180120060402130c0918060513051f060e040f06090e062403190302100f090b090303220c050303 63
    0x341000b40c0600300440d40d0080b0900500c00041a1510840c001240c09601038071b041613003428036000071155048682d205401c0000c0701c4000506039201103010300100b05032441888541045d54802d03051091081c41c40c02440210701040080b02003c07001c46031020340a950f2000000007001c0100c0d034500c4690494a182c10780d94a0025a51703401140342c0b40168401c890401100c0c441c500c101d01a90410b10075000428005181000000c900f040d51801e425001c400004403180c81b500050640580030003108005582c41c001c104d068940c0e215031500b1304620500700002d803881d2100040900011a50403070090342c0380c0696070941c5107140c2004000d0111003074148031282407803a500f541c1c1c11048034603929280c0d0002c2d00301000d010105c01c1800d80c0ca0003901030030120261001301c940342c00100d1402c4085108a01410010703c1961007202d0520052100100d440009070404c201d1000018068003599001002030190322030402c8802c3c00b000341c407a0440d82201c0c4032818195070f41070465002e180c050100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 443973642 1250 443972392 443972429
    0xd060312030c021b09040f05070b0d18020f0105180307080c040f060609050d1a0f0915070206180a0807060209010917100f020d0603061b140301050405040804 69
    0x41004045904241d07010440d10110341812a82c454640512011042c514190f400b40340c10a489515480f0b03000d82c0540b01040d42583c7c410b0b1910145903c448102c004c007150350070500686001e540f03124850280494000c06181c1c0014a0f00fa564800070380c140302d00021025000a0400e280c0c00c86920001d0a46205a03981d03111240c036030750000017541c4500d26201510444110522860080e00c4159940074942d908240c18400604248041601c03e0890200045c01c40040c2020042c80745030340c051100d90900b0f10031045440d0008031680c000c6000e41d01000c1020050340060800d40c03100200158054104a0420090400c81c1012010f0540b8400090341801c2c003000340c00402c40e5840a80e2040f800e280d4030101e01460142854a02d0450340010789a0242d150454004000040c050000145003c003110135210441d0000e5108540d00303a103454940300c0640d104e94a004000500e400c108140c0c0400144e41c011a01c014020b061050303540f4004078081c40b80d03001c10385004e001440e41c540e80e03081e003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 443974892 1250 443973642 443973653
    0x60f0f27050a0b0412060e03070b07091401260a09021203030727060f0908011e060b090a1e180b0406090c021e120a0309060e01020313030c080d0603 65
    0xc4a014041c0110801c003400034250b101c1c60102c0d01101d124903256540001603650f428083c10400d12141c02c20b10041c880c0101248520f4021341c0180604c0d154440706905d0320803d0960354071a048610b05220302c076122040198485011060b0410425104084075501c40041100800340c0540181d04102481c00c0f541c40d0a4000004501550381070b12030490203102042803070401500c1810039001d02241e010100000381c000c0391b00b0340c0c4124a40c201100401c1c2c4078010b9608403040032a082d901c08003481410010b0307022038410130b0090503074007000c01d203004039500115403ca50b69205242c8a00c0103040d603a108242001100c1010b0440b0303034640503980d104510714030058001069079503c241e140c048002a40750007481022022000c0c1d80281c0032010503504160511380300f00e1031183d0940a982240951108040d0041125030700e140c50024840446081c00d03001c84c6c11200354001660710410038007001c0c807641e10808010301d525207842042d900c414a002c0501d405100454400305040080100030000d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 443976142 1250 443974892 443974967
    0x80304080712030203120c16050303041209120b0901090516150c200d05030c0f01050610080606130509070c050d14030118020c06150307060504060f0f 66
    0x5403031004840080382c851081c1d001c014040b802c0140035034410002e40c240d0340d4265403140d9002900381b0744a800d00700b01101108009500d010b04544030380001007080f0810211301c01030107211081d0710309212114140030300c039510107803014409059000e41800060600c42c0942041081c154400d05aa4420394180100101c004444c02500f8660080c80d011130340d05445003203001050390300005c840c0c82800710300c1c0004029a4003400000d40040d0002c03c0d50010410400c01032025120000040c0160054540c1803421034001410203071003a208440c1e1050702651001c0c8d074907000f02003169420f41d00c50500010714403814040e0701c0720360001c0c0800b08100341035802088a00034607005500b902c50703a60940300102c0d5000106030035403241110500042c4424040d07046908110741d86203900500e400152030072685051f00c200c0300c0d055410084a1250400d081c2408010000c11540c18601e04180c1007a40281444004800b42c3c0100042ca50392594160b10448903519107510015800c002c0d00e060403e09031182 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 443977392 1250 443976142 443976149
    0xe0a0b100801022104110306010602030307090b1303020405090f01060308030106080a02120a0e0106030606030606050f01170430120c050903030d091115130b09091501050c07080304 79
    0x29111810002008007040c022100303806070580c07186648524030130380c09041800103002684d0140b5001d50801294a0030014103002e400305030000c68403498104402040071a40342c000c00c14805043c0401c0072000c05034060b810a80c4d5044174042085c0d42c0c1c12850314907141800e80540000e41c01c05500100340300c1040e000710b059a5003650b504085640b08180032013a4816022270f940f000e40b8500004804000326400a0342110351000042a0706580b038039403205803110307508191020307513645c0c6c000c0289260441c0c540703141540a0800c030915100780c103004600c0340001080504200c15036041c00314210700c4500c0c504419050400304582c40040c0c403c0c0140300c617440c00c101d101070340c0c9042e811000f101d002d842070300c42003000140214600300301212004d01521030306008031011403040c40803405541d15071040b0b00388140002c1700c00d610341c524001840c1c000f02d16544400402d0404002c51145a20b1b0342212940c05015039110720801c901c0b00380122120712800740c2c41440b502504c40041444c110200081013103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 443978642 1250 443977392 443977411
    0x30503060f0901081b1311030105041505011b020312040603050a0b0f0a06031d0607051e07080304061a09130c0e0c1e09030d08090613050601090902040e0a0b 69
    0x1402448000e22600d52420300504103d40e108460b05d610658817030004040d4031002604213480208502c09520983e02a2550020384101c003200500541c281441100d10f072100040c4c0484004d031038500003812154100e80e80304104c003901340200040d520200b0804141303019541501e9522a620140140144829200100303000d041030540541850081488030411f5402802c2241d504c0ca03080c0c05400410b0864606c85050403060701007503c3c00e0060000610034465511455660904026a24015103482c0c079101d4040b241031044102048040e81505d038042e40c05031000070307200b42c01640c01403100e062045150703000070b0110070001c001d1500700c1d49121451007503001028180d12003400f01a000c4085403241c204039814488107022120f00503001005081c0040c06030300e05540030307010a050205002009000c507a884050100c9402d080141f5540090451441d01c0010744a541d40d903115071042c45200c00c0580c42e040404255600e59100e01a48001802154022000340c90030000e003040c1140c52824 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 443979892 1250 443978642 443978659
    0x3080a050915011814091f1b110f0d030605030d0302121303090e01080624030d0809010b090901090320060604150510090906060e030709050403050f0703050306 70
    0x754100000340741c80d1522001080d03050540e0a1208a11a0804103e8240d0740030740c40351021000d0080b954001c502502c0e181c40607000d45854407000d10b5031100c00300c1c2d18419640c5420865482c982d000325242c4030100300362601002800c80d83c0c081910b80340c0100395000d103c0c01507040c041d0021307415501403002c94209500b0741b03d024184103825422400f4655070b10041e90740d180300080509510201c1240740610070b0400704142600c8144001c24003100340c001e504246d00c60410b0200c241c0a04040740008001098603009480340d51012a40300c07501d2020030414402c080d404101100b03030a407c41e00f9400d034060401106403600304031060192000c58016004611040d0380300c040b907010991019400d403040b5004105c607480c1c3c0b9003440010a8800c1071040c03d00c0c0b410340040740540e80c9604003105000c190356071a01650507d40042c040354540c0e03000344240541519400c403640c402180b01c0044480b00040000c495480f07080a55203485010a90084400b001401004060b04203002c0c6000d050152170640 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 443981142 1250 443979892 443979901
    0x4020406270e122508160c0510052b0c0207090c09031a040f02090a021e04121e0218090105011d01050405090a05010e0733050c03130303080a05 63
    0xd8540580d52895540000108107255a1203104e000b003640c84c11500314140707456602610f489039590072500703034841e0b108040794501007400004051407000e00b5003101d50f034000f201c0d8000060030910840b00c000514940c51b50405400100000c1c110261803a030b080e06010102030b00740001e40b110740750300a02204034544601400494883c6051a040d66403005903130b110070070642800d40d24004010f00495084424003030300300058840c0c40c103042c0140a0080050f86800240d1030300c080c1402c0c4400003041e40340050100b00901140a0b22980380f05400c52601c0444030b40b1000c0340402c0798909940690042c1c0c149036001031440316208070f20700c1003241d100204240c3e43ca5407555000411401ca58081200c140350040c4080d2525034409030708902c000c422642d00c900c103660b4490944564107a202c04030703000b42030200a05508d00304c0c0400e6100d6201c6601444010200b43c8100e0719008440c40700070010003140c8200815020400c48501140c419040308a0603640e150040c000082280c000740900c0c140701c040ba = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 443982392 1250 443981142 443981171
    0x12050a02070e01050108060111030403051603140a02010f2616080c0c0703030e0102030d0f050106020c010203030c0703081009020f0d0c0c050c0114091c050f0f0706080402040627 78
    0x140c3c162581607444c1840703501d4240045134614040c04413440c1a01081000000040c000c00020415545414942c1c404500e541003000c62228801d139114020740000c40d00b400141c0e40820101644116400e0040fa80d5050005076905d0000c805101550560f03d0f1040c03081c0c00c014404006105d411070b0b40c944000b036031036804444903402400200c074055071140b4000c0c0300190052401305400c1906104072030400060a41c0a4180d80d401503224400740d94420043c03004a034140035543c1038020a0001f5031850403c00d40300030862054070400340403c035050b00070403040d5024403030200042500c6041591038a0f0340d550702d4140d51f804107580e4400d5a14005400040f2030050456411560f080300280c1010815030006444c46e00c0b070000b00154880b0104803c1c41031f65100305140041c80040004881c4a440074034141d881e11146408140310b030f0b44003488a2036211800a0000c0903100c10b13152511481e100c1d807003c20043c1500b60420710748110320005002c402c50309006150b40415800905110310074114484 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 443983642 1250 443982392 443982419
    0xd050c1905031810050d0f0b0613081204060e12030f0f12060d200411040b070606090e120a0311073518120105130b011a030604090f12050a0207 63
    0x2d40c4c0200b10180540a051b0000e03503c0002d6129103640049030409a000004085502c9804081003640d0441c2007401090410088000c02104129129140a003400c0019040551172030301c9074401c0991401c4e02c002c0f5041481507800c41e19801c00c4442c1c039180b0f4186840f85503000200186028080540041c10604d4030b2aa0b4842c81604402e40000c8022010014118404128001c58215480710341c01d2000e48101c10040000f03004501c002625504540f030142c080c0d80c0e056115001c40360270080304c0a00703000081035000c0218043c0c464141d0700c03031604405502a1101c9120040c140354042140c40512140680310302011220301c0603864455414259016075408200b078244501c4401d02040c46002a080d2021010840052000d02c02503109007545086d15003c40702c8240c2400608a00401c00c5100d03202540074100c1410200642c1784590341d0800580070050019100304c4c3c50744c00702801d1020070204000c440d80c05c4044102600c19002c030251095000070020790040c414401d00141810502d0007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 443984892 1250 443983642 443983669
    0x602090a1e080c06040e0406020d141611010b0303190c0b0109141305070614040b04090b09010f0510050703050c0d090611070e0f0415140115020307050d050c19050318 73
    0x81d00f03000307510b980d08c07000001d4000744003810b8a140e0306d902d655100d640300901e035803240318034041c0241e40b1011048000d10302d009062011b099030f81041d85864040e80c0c04815111054581e08000c1e04412400c0d4044031026041400a08128100750006c6001d9030503070000700c01103840e80c10054154594111403140d4170310840001d001d40c1c00180b001d0040d244180c5c1440401c0900295440c00c250f01c03400e0326141f039803141c1d01403107a465450b43c4078029401e00300341c003500409500c49150326003403900007c5a01c05c03035a40348880410100140c0c001c10540202e054460340e0001d9005c40e4610400381c440607100d01d100340030380008504040580c2100050018402003520003003c10716159481d0248442548140980110360b0300c1e100750307060114018144201c144007580d000040e011549014018204030b0024000541190801c10820010071400514001d415aa5280c03045e551600c02e00d4003800c00ba003c04002d1443d880e0700c88220240000080500508400441001c2d481d11039107003080a11400200d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 443986142 1250 443984892 443984909
    0x16090b2a16140f030312180703030f181508010f050f0f060a0309140610060305070f0f02030f040810050a0902030706080a020409050f040b070503130602090a1e080c0604 74
    0x606100103207610000b00028403010302038180001c0410002811900141c080c60584051001000400c02d4680001281a4003004c040d155950854400801002000c4118002d0149103007114540214200301c41e030080262110070b00b000c0d04a03080042c03803084203125080c03000e07075245008122850102e020803c14a00104155115550311080c42055000001a074091594840401d00810300030005c0045015030b100140c45107107070600f01841d1050036030700a00101480c1078100609241c12003010f060000103810041d030401d511000c200e20794400d44001031101003000c10300280c03c5000143c1e004400011880c02d2000b0383d10050800c040f00d14444020b9416880880200800e0703014018007500311800b06009072500ba142c90340754090310070a491080d0b0002c060000c0100744840031385899003007581841c125145046c480c120380b00c02810b00001401c065800200600140c0d680c0c80d4142c0280107501c0405030012003204680204031052155042c9401000314046552800c030381200d0030b9882d480c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 443987392 1250 443986142 443986183
    0x1e0609060901020f04091a040e03040e0c0901052b060902130503030f0a0807090e0f09100b0906130905070e01050312030601020709090503090a080102031608060916090b2a 75
    0x300305003007d031003d41012410080c050781c0c240d00c56181c2d400345010603503450b4019541e852411030403014445004080d2581c00030b003480300380756aa0f4040c04940d001c926000c0134030340500346520868403000c0d00c0804060500c0c644500080d800500f90050015030300340e40030401016544200341a20b0307108105031500c0081c01000f2600720a80102d400c0c40c0c00103400d05e41411401c1c1c03190210301d80403405503030048481c07007d0010002c40328030810682100e511140c07070511403c1840b41c007040c00340740040c001c07610075a42c542c120310482e0780603405020440d80020071a15620360780d030956a206d400a01500e406805032100c941020140403003164001c600607401880c581e8906441100101107c1d8001c0b07940e80010486207459688085100002d13283d0341c00011390b2410401d480c0640000101c00b8881130020310000c000c1c085d9a4041d00a6005003442241c42580078502e001322100501e0fa00030070800031001c1261310180c3ca00d03a44680c074000310a1568180c800395011080d0f13442c20054061000c00e0500c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 443988642 1250 443987392 443987399
    0xb03010c0509030319180306020403020a0b12010303050a0512040f0203060c0f040605030406140a1509090f0206030c0412030503011d270c220b0a120308091e0609060901020f04 77
    0x3c3c00c0c04130645c072040d15002c01d080c002445407103048255544280d4240340c01250910a5140c4400b45800520800702e00500c1c241075804564000d0700148000f505000c80480c2c1201c005010380100c5000d40500d11042c00c0910f014a4030854545801000340d010f40708000c009200781007a5421140700340402c61405082602d4040700b00c43d107a02c020000c48941d51607039a00d403010140c1c05c610500480b0840c0011030034142e000201106014540d000c060440e00341618400400c40d0f00c3c004020207a016120315a4945e603003100d8101038030035070780500c02c5510030040c0d0703005065004001c7c505031a2910111007808542e6080036444110540c0c00850300c1c0141883d940b1444040c14408483e86104d00646006120410010b900c56055841e0010b04a80c440005407010540f0f1190b00c000d031504844805406040c481c5a11086c00c0b0044d00500740000d80022910a031400c200b502100d030490300d503041200d00300c44012a119601951b032404c0d24480d0502092000b1018001c0c0e50041001801d070f00d04041c038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 443989892 1250 443988642 443988667
    0x70e0709170c060304030206061005090a0506070f0f032c1f02070803130807050d1106071a13060506040c050a140d0501060c1203020301260309030d030b03010c05090303 74
    0xc400300705040500c240d0190030b60980f14035010b10b01c580c0c000e030041e0040f845e10340240044160122101c0d001c21108000ba00c15560350003405006498050301e4854807124286000c20302c0710a0340d4070103403c0c10044103660301010b038007a1004000d00c039107032001d9040c240e200301d0500072003200011013540240a484034041c074100c20f01c6641c0780091203204880d115603403100c0181c1540c3c4540799001d0310000000c010320a03c01c04201000050000756240f017550a640d0302c1e408580c100440007248995000612174003407000c0491226181140002d10740702c00c0c104800f618040001c11402145c5003410176000655600e01445400c210001c40d407261803a081d90108104d0360348211884018200c901880b18500140d42485294060f0045445001c044c42460900303484018500090b00100760040005100030b6880c6c900c500b41c4074040ca0719058036000a002c5450450091880301078042c030541a26000865150700001302d00700d42580204021880d00380220b03034500c17625143d944c055108100442d22041c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 443991142 1250 443989892 443989919
    0xa050322030b24130c320304020a080f060a0f0203060a060311070b01080604060510060504140402210121240e0706030204090c0504081b220e070e0709 66
    0x103500420185000c94400044c0040710301074204094560f8070303034410250710b030000d400a08104602e02484032102ca5811038801c1c82a00590f6141e001d13001002040441d2905011200940317038140170303107400040c964440e9550719811901d80181c0c80c10500c45c449030446510031680140805000021140d04056050707000d81440046e054204404125400100d0442109503001c2c3c1031080140403141450b00f0a42d0580b90f02501d80c0c3d000c5110081e0410801c0d400004440460b120b50348606900c0704180c0002e8024044c031044503030b2000700b01500f0100740746072000301da060751408510800000025002c2c1e884100f86000000e0000480c0302c044030f40f05a244000021a64119070b012900840c1d0086003803d210315980501e02083d00410240010709460003109200082071901a041500d0310200981e81d299840466203e0409595009034544407000e82d101100600100000d42070f680c980d83e100103140c0c00d484c80700326014810004c240804400c04c41070042205940d80c40c28141071940600210 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 443992392 1250 443991142 443991181
    0x30203060406051b0a020a0219050a0e07050714010903030c1e081302060a08091014060607150c110106080304060504030210030605030a03080403020613021f110a050322030b 76
    0x40c1d20745210000441d140c20000d0a1880541e406040c07c0075251050002840d282880c2117000d5040e020240485d4440b02520402c55607080080110390b2911101500c580c4a0745c80060014418100b400c00c0301001504596022846a9010000b01c00784600445850040403070700400403250409205861b072141078460340219400c01c42083c121140e500090182d4000b1035039001060b4144104490360030244580354045a07145c00038045d0540c2402851000310005180e00c0c4035913004240d44051024020301401404500c5c0020880d0000c1c4540141141c0044100e405a940c02c24001040c0801c011059804a0b6007236200c00c3d0402d41075608110700000b4a107001000c00d0b80d6140300042030b6a04000d0240c41307a0203603d52001e0341c00c003810b000f0304145000301603e02010711100000c0040e19850083c0080600400550040c0040850f044800350b614031542255481180c4485003840b1021000308042e502202001d090441441c8000b03491898511004e40054076400008594040856149159 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 443993642 1250 443992392 443992411
    0x70905040b150c01150b0a02030403021c0c170d090f050f01112b03020306010f1206050306090601060906110c0402070602040e190e030f0d1d070b0307030c0903020306040605 76
    0xb5080d0001e500c055000441030700100e80d107a4005140a4040380e00c100b02400004624910b410419180070b0354074032071880024041d002d0300c3c04500e0708009580c065119a0760000c81c4518007603540103098000300d0151100e0701346015640140c54607a01400100e0120351044800e2007800c0e140c007040106151f04820b80c2030510000c4040b4000c400014405c6d6a004000c1c00c5040c9540d03082c4172200c05101c00e00725034400c2490701c10420b100903680c01c403820031340303154940c80c09450f0504035454101c00b5140641c4080e030140704140074800311050104d46281070710165903407049000e541e480300300c5101d01540724990302e50304000c01035121414140c0051a190b4080d40c005481e0999604060b40a14422a0324100300e0b03160142d10b42c0110b080c2c0c003600c061804c00c90000c0d400e081c26001079a11a10690402c0031b040381c4d403100340511074034108060340c1220003810291002d4a96881e982c04e507961003282d8070400645000580c3c03502c24040d1265809617500540107010741d81e01c130781c0c03044010880039000000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 443994892 1250 443993642 443993659
    0xe19080901140f0d1a0108040b09030408150402120a030c2d05030a030509030405010e090a06052709070303050403110d0606090c1704080304150b030318090f070905040b 74
    0x1005122040240a80d07000ba83c4526541e01c0030750341c4041107842d403020402d004d9219030725101043c3e9007d040d40c2d80103a00300c03406440980b00c20880c5031443c4607907446101c071030264040800540b034021400724400c50080d80c0441d295090f4a00f036648610b40c81400070046040781d216040402c00741401c1000254075803c10900c121015225040c04503101082214941d03c00201980e515601d4051250489225001541410305010010741380b10b408407002401041e9000000708040880c4e0810002049c010b845100880381d003a8074602c0c080d00300e043c900810307202c4c1004980a41400192207049a030180d980c1402c1034203559078111341100841038958000500b4075004007040b000c0c0700d076a001f071904140006464411030000303404c80800c151108403c0080900300008100800c3c205d0341c1c444e92224104064807d82d007000e07801452040103494044c4000b0035000c81500289682c0000700320301319512100c0d50303102840302e04081e01c12070b03901c000285c4800c01040301d410290012481c191004003000d5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 443996142 1250 443994892 443994917
    0x103031d0a0f090c2a0206042c0c07081911060901020c0c0307120303020309120304050625090509090c06030f25050a05091507030e01030e19080901 65
    0x40082419801040303030204154000c10040c3c010744142d80e81c81600c1e003400c0707542d1a8000300300300c4e0811041c20005a20000c0c10382120071562010102c074050304c0c2030b8000c80e080c00461940d814449800501c0c07440602c0010020804400360303c1d0a98a8090340500741d5817070007500141107600c110681030301d40103000d8819410f100c0c0034024801140314000800c001610b6054516185103080780342401c05006c0c2e00060402c2c0003d902c50583c2810041d01404c0169907500c41d0440145045034914441c018a00c011082c801080000300320240203000902040c1d103a03400b100c1000d544680c082c000c400100d200b0850401c1942402c048850380710004400f514412040400442d8050744100e0300c01a204c881c01040004071003105480c4036440548003804408003468000181c010b00c254000001409000300341d1020b1640d40c01d240f1180030801c2c03074245490b0003113803802800030b82071000c416001c03034244154a07100e4600064400314241710303149180c4480b1403603240c00e40264007003041c00c2d04103d060000503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 443997392 1250 443996142 443996149
    0xc0b1308040b0d09020901050f0a09020708130b092412060102070b0a0804050d0e0904110a030206040602030a02100209060a081306020307020717061b0d0902090a1e0902090103031d 79
    0x4044400f081c00001c00d0075100d91040110521050700a10700c0344012001c0d12801c0d0b100c3c0c000d81801d95a00d81001a42d4801d41c0c1480c40d00c13806a16805e12580741500008620701c4071046c060040800c06480e80340c0d030b601401e840750350304c0e51504840d0500b48000384198520a28100b40131038000700180190340d0041c0d2910000d06c182e900c001c0c1d230034011840a00c01c0c401080001c000c3c04280d45d0f610b10f80390441d404401c0000e45a000c0140c405040c540c40c87c0c1c4810380750382e44c2d101c20800441d401000c5c19a16035030790002030b440750080c5003142c0140c05540c2c00c0c4005005503008554002d2001082d66203800c0c0d09030710940310b0f0600506184400c4982c6070750400019582d00c0254002d07900740d0020504180760203280784040c19107901d500401c0d000607080c44400c0c028a00390034500600741c5488c5031150311a0540000401851002951203480c8800340320440e1003a42c81444096080c2074051503000740c4801c250300380d0b00807000094010522800400209104a00528404860700100000701c001e18000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 443998642 1250 443997392 443997397
    0x21621020111030a0914090f0c0307110a03030515030109110402070302100f090209070c0503030f04030215010e091002040e0a110d091a070f1d040603140c0a060c0b1308040b 76
    0x10000851070440c0284901044032241c00030206e000c407a43c6c10f8500d031030a2861038080c0301a04a4140050110214422502412540000c50442c1c02210000c40c00b60900030050b08041d21082d802e405044255041820180180141250440409101c1508401c20301000303501c150416011405450341141c40540d850140141c4107180c8000840c001900340104603a5401c05401681409901040b00c0005103001c0141c950202d0f840524020980d55400c1c00d82c1400000c8841e456424004000030501005020140d80181000780480300d41a21107072500e82240700b607001f05450701c0c00701c60026000301e1842c0c00040002d0f081040311420f16298061305015a1b215440484481c00d0300c50520b0450800c265107035030f100b00d8500d0b0801c4d402c1c40103103010346880409100502032424201481d50a902d0b190844c40c01503501c0440002d250400080107a200c00c000e0325128442c600708080041c11078424003003a5103298014510b0703492611101080c1d4007201595408807101c1d8400d00c0000746c80007a1790302 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 443999892 1250 443998642 443998657
    0x180b09150a060614070b01050607230708060603030a0903060b040b030d021f020f1b010209030712050f1507030c0c021c02011116060e040608011b02162102011103 71
    0x9000c01e0312420301a01500307503c80b0320648182d01d03405002643c045106c55148604451040d03455a41d20030440c2070804800c591100b88403482e2300070008214040ea40091004100c602000030760f403080d1074400800d074a80c4100100c0c0d00005442038400d05c007182ca030ba401400580001400041c5004200000c641048180a4418007681050481e28441c2c0914118801c10f0300d508003085107406035000c1c58100c1ea000d0440b101902c2e00f90503284c2c6440b81400d5040314100c501c0113048036090741e910f07030b0392030445004030004544600031642c40c110070150003d140007a03104000e0982155582e500c4044000345200700e0420100031a90440300096103519900da0178064041200b48071000507800050078181d404500c5c50407075404480d80021032201c0d101d1500a82d100c031715100c05030407a0040001c010303005940000d02507510303015407943d007208100844c000e08161a0250ba14000000c05028104a182c1c4942d50034014000a80c0810501c0a40c205001c2d501c1410440c1490aa0200c102c0c0303107800245 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 444001142 1250 443999892 443999911
    0x4060806070804050d210c0c0212030913050402010503071416060c08161b0f0b010e07110d0905060a18060206010603110f040e091c020303070e0103180b0915 69
    0x14280f100b4403009200b480704000860412018081d401000c00c10306a100d40c0b0202040c2d40c0d904c589240241c4120b0f0906060794008120012900c6008001130316588020030141c170a80b06021a0118000c3e14040c031340c8a1a0142c44883c03d5a541d03160580300001c0e5035440b809243c10410003001c00d001110300c40c0107024012940010400c04500c0c0c058202e51018180e211401010801003010b258090b14140791506040c4581c103e000c5507280550142d0548038004081490140010031040c2000310418410060340e85e88170103040c10320110b00e4031507402402c0301000030b00c000740a1060307040c1800144240951454581d0a24141506900d03200c509600b05e1401600b0031001000748507031501074100c01c003041044c21817034240c88203000400e40c41103124110401502600040c401c10302404008204030072882c510202001d5480020b449510491300a00070507181507261149500c00d1054808014640e054481c040ca0580c0741c0c0c00311940001d2a8640304c0c45010305110403160102d49590040c001c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 444002392 1250 444001142 444001157
    0x1701030c0f0e040b1f080d030c09170a0312061802030603070e010e0708180a050c090619050d020f060a020106033c080d0903020f1507050423060f030405060108030a05180406080607 79
    0x10b1001000c2483d9a40026650003404019880729030bc08140d008089074503003004036501e821903055201038103403030703124800d0072003100158000e042c42c940055100e1007003141600c121310386907001c04611080a000c0c0050f0304901800054949015101190b040025260300c0d000c0c0d44061442c0a1810207403500c00c135503e030042c0c98224202d09208070204d0300301b001110b420401c0500f103410030a040180340300b03041c03060034411000340c10f40d1225102890400005001d25503600680e0101034040c1c441c6100407280c0410f20148101880c50b00c080b651003a1018080000366512a004141142c02c08000192030b0b030b03a800c2000b020b950f10b20348201e55200303110342c024103034001000f00b010381001c01302d07542032480505034810010000d51080c01c84058a070141d40030708507502804035403c094178107402984d41140300020301200e8840301801440c8900e00c51411a21640c0c1c0310001c0580700d00900d07c078000414414000c4100840c40d00140000310740001e0800900c0907620105180303410340584a80011841d032 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 444003642 1250 444002392 444002411
    0x30c0d020d020a020f06090402042907110123210f0f0105150c100f2d020c0a06020f190306060207090c1701030c0f0e040b1f080d03 58
    0x14054200026258009403034164210380d4069251038000f08000d01c101140c00c20b40140d640c580d1309490342c0c910040c20854482c1d886261400865000c4003d9120a9030240c006207010f60700442252840e540c84040612001d05940054a400e401e184140000e020000c8a001c40149127201034804a0203200300c0d4a0710b41044a456961100d02500f1b00040380c3c0c1c2803003040411064580c080781144c0303041c0c40c01c941490400c0350360807842c01049000b241c1c40c0110800d11200c00103a030040a02408914003c002e0560605100001c160002c0c541c10340800411003490311880e51a07003d45101c4602d50141c811a00c03031641c034070041741c0c08a070b2400d41503940450240001a410103400d20300244501301040220709101c0065558020740c0704500c141c1c0c0e1031b21b8414035118810281d410408012401ea41c2240d6102e00d0030165841d0300340030316800c4401d01c1e040000c600c500c0c07903602c9003d150443c2010322070340c44a81c1c183c5000f1041d000b400c02007004001c2c000500318010000010741c84107590300000c0c0400c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 444004892 1250 444003642 444003667
    0x1205090f12071809020303040e19090c060905100906030506210a0615061202030a0e0f0f010c0504050901031202121606060501140313061806090c06050a170411090903 73
    0x520341c1c401d20a2130720b0b00154000503103001041b1030540d41741c0d00018240d56507078000259040841034005035028108500c000420038415107030001e4400036120105402c1d100c90500402002945241d00020103d010400a85000340c0c4455004500548010048403544010301403207400d0894104066019100ca0381c28403101d4441c84001a0445105900940c0b42c039000400400f840c0f0500c00706c2660003c003140c044140c83c0e018003048456032054415a150402005445611070b101c50101542400e4400c0c030bc003071280c0c080b1000d8641c000c200755016400c0d92034643c0d441e042501e06d40107510443c400c00400001c1240036000000007413061a601010610708101511501e42c0140e0600415968003e4035442140c107407903021032404114400075109050240c0940707101505241665064030200c2d0901c20290056400d06003e103400e048000e940380000c4406101d1140d003000003980340843d41079035026002101c1e1300a405602007800f988100c4000403e00c0205907000d048a81c07000620300c800d9403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 444006142 1250 444004892 444004919
    0x31103010b060703080a02031e0406020318070f030318090510080f031306050721020d0813020a03080309030f0409021921020a0207081506011b1205090f1207 69
    0x8002c0e1000382c2000301668000d09488400b8000002050b00400012158482c01c2580c1d070b0551002c0710faa003c141058241034000303503c10307a0840a145640b0740c0ba0040040000303440800c5440c84160001f4652654900b211800d824940e0541e040050042c002529100c034042c4070300a050041d10710350242d1602d001c8514142e01035070400c06030b8105002c08054840401000d42c11103d440c00c00c10b0340c031051403401034040e0f1004480b2400300d000f282c03881880303681c0c0000c3d80316507055951140c4136151508030610340351040c0b980009610a01e120024800202042e020f141c00540c0700b42100e0600ca84400a03905a40007078102d00381440d404030f80b60102ca403107640315940c900c04c0c0781400c0901940445036090200c048140802590740c00041c5603055a100700482c1c00107100507001d480025841d9424807900c120107588050026a506034841d00c0c072801e400030a00300c55440a0000b100e40e008000030340b507a4120080580d0f01618144048280740c5842c0e140a803508804800380008a00b0110261500d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 444007392 1250 444006142 444006161
    0x40807170a080a03050901020d06060513210f02060d14070f0513090b030709020f04080d080708041e05030309060f011a0f07021c0c0e010b090108040b0c0903030403110301 75
    0x60307000901c0c00300402e4074402114242c2c5010b140200c2c107980c0d8420307118064400d5510300d105003031070404005a1940c1c014044d05402c1c1c0040e9000c81746a90300c00403a03030b01402c486d581d244001e4035040e45e58001104024102c190900c050704007030400d01e0305a4400d080f00d0b40326030b40c0b0f140f03204075074100300c9002d03480001000c1081050401d40c2c20300001903414104003055000e0244c5241d82d845819626076420041c0ca00142400f80d025541d9200b01c40c0221440d40191098000c07900c11000c0700d1076402c0c09501c1140c880c00466907103030380c260748507105c142c003e220b078050801c0c060345a0354010000c41c10910066100d0b9081c1c100a100b80d0909190030ba01c1000305a0000d180000009200d0380401e08400442710040d5400d458140c40d100d003400040d00d51750b16502c02c0410200d6554861003000840f6402404650500380010700d16030741c0e882d0b0034501d80314140d0b9071400219610009000a0700c80c7d056182c1101c050090581031810003c0440e145038429002911900e0341c000340e540c8071b0300d000d000e00400d1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 444008642 1250 444007392 444007439
    0xa080618010c08041131060906050a08031c0908040b031008010b0f150c0d120f0b060d02161712090a050601031515120615180b0607020303040807 64
    0x625040e200c0504c0450f8a00d000d600c0307080d1b013034480445500f02c07144012185810018015441103011400c1c0000e281c1071142160a5040a50000300c515200500c04100d602a002452426100650138011007400840590b8050340c0c0301c03507003804120b4400280014090500542d84d80c1d007055510b114a10145170700000365030381096240d45287e122000a07210b88082521074500d02820b00b4140030050055a1100100740700f03407038609000c0b0303601c05804280d40007041410803060300c0610700304042d00c98100c104c1350010f90800415204042580c014420f00d00c0010007014540001d03502c29020141010141d0320010b00400c141d880f200c40e412080350099240030081080d07002e1a5251529070720140f2001d1300c240c404001c940c0c11404190072043e54088050482248c0d02e0303c481c2166007194a024060713580501e00803140004041d0404903a00f6a8100c411041d100b94200e450340014011a0f0000c5802070400c0c450200141c0381000500060030004014081b002d040c5407413242440c1c10011940c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 444009892 1250 444008642 444008657
    0x180907050f0d06080607020a0b24060a051201090608010e06011a0a02121210050303070302070b220b070b091c030b010905130605030c030d0e040207020a080618010c 72
    0x210550400201c1d0940381c001244541c0752603410150030010142903002c055240600030400c0b0800e503020401d081040d12480f03620a003910791a500002e00c001403004044502841e10b10000e2030300c0e040c80688090040d43c501035160a00003610b682186d8400e0740211040c648640007840400b00c00e001e082c5504d000b62008090035894582403032290300e02041c5220707908000140d6015903c0c82031085410b60030365200041d80e140c44004070584080d400720b581103200624481c010403985804400c4514503a095030017094000c1c14406003007000e610035880d032520040c40709003060b00c9a560581940c0200000d0306601d407684100d0400c1c9241100081c01d11902ea08040c2c1d06451640075000d03071000c2500729180000341c0f201040011389441f0a0354101a92040022410140502440c0c01590507900d090b015035004800350010b055071411084071001c0410145040c0c402e180c205a4081c0400c070380018002038060765108072403420070303400b6a82c41301c0c0d43c0d0740c42c4110411954240103240044001d0f280030712 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 444011142 1250 444009892 444009901
    0x6050f0109030206030a0b0907020a020109090b1f02010b0d030e0406050f01080406020a0228020a0503030f07081602060c0706090501090f030f2a06020c15040e1009020a03021809 78
    0xc01150700c1d404000d10550000c070101c0c619030b1190b0710201141d80e0280011440f4180044040e40d50103c0d0ba100f240007070380c04440482c00e6004c070b02030642841c101600520a0301918a1300c03c030100400c1c0e07003103002c565903455441f82035514242000c1002d40241c9070b224509850b1810301c010798034203400060240c01040b0f0004403590b407000e03c907a441900700c500141c48005010040f0b0501d03034150307030040010b00150b02c0b04844c0d0078280140c5680d140300303d400c4401139a0f20424075807607014101b0303070480c00328040c8407a102160346180103020b5105010519204040b00c1d80c0000c409802c0443c2e80c640076441030000788803242d00920900c0c00b404c1c007420408039103842e21419000c2080c1e6070000510a4100b2511307003042042c2c1426103c2e034840c120303002c80e00000da10141c040701071100c0e10034200184104c1940c407031075040442c40200c03040117841040d85020304003041c4440b0010b001d03041600912035004001350790105440030f0000e4011a98000d40d5075942c294901303201c80545180284511419000d00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 444012392 1250 444011142 444011147
    0x618060803030f012318010504050a0b06090f04060f06050703080106020705030a080919090b0f0d0b1303020304030b0901050f070e010e13110309010608240708131505090106050f01 79
    0xb2411104030b80c0d54240092140b440007140707001c1045d08070f42c1100007641c03503c603500000b2010301d0682d842500d08110f26610b0700c00007030a950414a20039081207081004120700e0825051000122402400128850340d4510484901041c01d80c065000240042040380030142d000a0081c0180920b10003841c2c040d040200290302d07070001c408000c042c000d00081d0b03420181c071205107810039503100346440d50030705030340c0d41c0718601030108c2c4c2810a110f11400703841b15031176240c0307510014030250700503000c0f20255640190007210301c02c6120094095100034880080010b00c0d04180c1482400150000300382c908004509056164028003501e0074071000010001e510b903801100c0242005007201c0628510544003040301c01449600078007221036000004000107844150400001c03500400119800182d54034480c51042280030500012001400040381c1e90501c01d0076204c0e0416940c40c59044400200d680783e0360840808017400c1d1b4455103980c10050091404e20500009040590ba004000c40024000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 444013642 1250 444012392 444012421
    0x12062c010608450d03150b1218060907050a0b0901020318010e0307291303030311090d0609031e09180906020f04030b1e01030209060f04061806080303 66
    0x100b00448000d0000070206800e8681140e441000c903103200148400e00140098991844c0ca1035040820306064490458101c540856130460380e543c805207091900104804500c3c00b00680420701c500041c6800c03001152050050794001d0709500014007500c1c2c035180030700100340440d500541065000303010a5103285d03008011505050b01a011101e01480124010394011403640318007038041c400c084010130f0340c82e41104007010031152203d03410b5040c0400810b50307045104c0c5205c0d00401e040200d40800000b03001e90003d441d0b48001114160400b40181c001c10504211340c4001e036202503e410720401030581000100b00602c030030040744a1800002c000140000d070320303486644070344040c02c0d036450002c4109501c00703584140d11080565a90071042155001604107000a40300603411501003076414071448071087c04103114090300d410507880c503000c21018010040201d034000d0032455000d0101d94951050a003d04580c034039900a5124002414003191216000001a90700420900107940d600c41030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 444014892 1250 444013642 444013681
    0x1150e011b05070b1603170106020a0f06090b0c21040201230904060806190218010509010c0f0b19090512070c03060501060203180d0209040312062c010608 68
    0x5460780507490098a411440c2c3d0254808001c08106a04030703034555444601000d0081e907070400c4142c1411200e88000400f8815100564007100c8980c0000c0c0100c03107031710000d500030800000c006803a031301e540d00241e038101e84c101c140ca20700240890306892008107102c000420134807000302e42e140540c0003800709500c1502d60510002141450740c02d8918a50032a215124050414442c19644612850b0340300c0040da0041504245500e281c2d000c0d502c01c0c426100f0940b010803803224940c05510054903698040c0f440c060404c00c03610001c201103034107040b07210840391064203036115600d80010a10440710326541084442410f00405e8408240c0001d807400300d4203400002141e84e050036251180c10304155900c0242000d090100004001d074000c80904582071501c120040d040040f842002216221018025031003000c100110740441d1054001e40c00340c42e80c0d41000900e0640b121f08a8a07000c45c00324480340c0502c15002011a07911501d11028010000c1b8204400c040c10440003040030008180c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 444016142 1250 444014892 444014927
    0x90606030a110d0b042d05071b0f0201020d03060b07080d1d01050f0a060305100c050f070605061201110403121b0f05012714010f060b0301150e01 64
    0x404074040108a9100000706500c21540c540d0b203401d007141c1c0a014000b0a04468070480c90410203040c948000350344144004080c290340798040b100c03510040001e05002e401c050400907540740e06143c2d80c10f03800c100c8071203038080c10a1030101c580701c3c4002072629010383c951004160130a24104450701c1001c040c0c60005a1117094140c81b003ca04a001c0000c00d516412088082503d1101d03d00404065010340d020306050240700205031781d603e110205035109440014840d47c80030b642c50701e40c804076511495601d10300e8038000d80f0b0507415417480312607900700440566446a41b0014426103151140982c20b01003801802440000100d44010085004510000d80080c1d205615505c2c0301c0d00c5140102400001c01c1810701184200d402c01701c15800300403004686c250310f000740442403503066024440c00328400d103288030300ea10a9541c2d84034440c00382402950180d0340321094500006014040e40300a446a442d60307648961404520390400e03542c0840e00030900c00d511032050b0b1980d80c0f0020004142181c1d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 444017392 1250 444016142 444016147
    0xf0108040f021f021002130905070903050d02100614180703020903101b1e210f150f06050927040b0a1a03061605220f0b0306090606 58
    0x142485650000440d00003944440d4200c100c04200c0f2032000700540c10889a03080300e003212802001d00041388101016160781c0c02124000b0030001d9102e41045921015501c3d100b611190380f83c0d41c59180040c0301040001507044515014178a6200c2d02c1000c1c010000d0308100c1c00fa0442042c0811510a15a500500d5843d9800d000a5126000f41c04440507030390040c048034410320140d9141002021180554210ba0a401d002030b40c03102e11030003c030890944d6010804803e40c2d00c2c004252656440484654065801d9917007030700c0c8035030b400d119400e4054410075003c507940202e031701c1c21001156141c000d0501146a0038040c08500d5003d4141e4245200660708410b41c00400b4941140000340000c44810341e880c8101040100208000c0403800303160488401d2107034001c00042800c642c51903035441600341c0d001c400001c0b665141c80b60000b01d610400c0c00c0c618501031243c281c0c03030300708400504583c0d071030000c518003006040da10040c40790080600710000c0b801e50a203c80019840d0002510240c4180b401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 444018642 1250 444017392 444017401
    0x100c1a07050f040f061407020306061e0409061a0a06022e020d0b1903051207030e0910031a0c090409060e0106180507080f0703091b080114090106050f0108 68
    0x1a0700311118074840300461501c840d0f480910b4580c0d00003a0042c1d00000302c10700d01c1141c0d0401004d0980d03650300e6004025000380c4d80c2d840140200e2250441520304101080702d42030301c4640360391007000038841c06144003003400c90401e00742d2401221198440741c01000007071800c11001d580421281d01e0702c28400122714920400c0c20040b91030643c0c90702074040c100c0c40000c01400152095006c0d100401d020340c0c90a06810400060060320030b03051002400301e030404900c0f036005031554002400018400c0c28005490228a00806c4031104d04480d0f030040700580280900074071107403207c0e00c48200e411002600e59450300c41202c0c0c1da00e00840b00c14a00507a1202034900402c1069081240d4411702e90008020955480080c4a9240c00c00344100c0c1c6200d1910000c11901e6101e50b1001d445081d1490320000d868032500c10440081c07290407002d8481e000c045200040b510b00810002004007218400465403042c81a03e015400b000a4a0301c210b50b0715000c410000c503240c0e5400c03080d1204003403c005129564 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 444019892 1250 444018642 444018647
    0x5100c140f0a320d0908161502030709030308090708061003021e150705010603020a090903032316051902031c0510090c02010f050c09100c1a07 63
    0x289880d040c0840105500319020300c41d8000c1c00e002c0325107645120010304881104000c5100c6152964180310140804807000c08201c002040030949454000890a2032912138501c03640064001107102c401c0542c030501800003041d02c20341d200c00014401c41c514289031501034201003080c4401814010498005540c801090051034010b000c0e81d0b081d0340b2a4600620340ca125542ca0b404100c1c480c1c0f8070312821f0449120002c0a0300303040e070006450180804050071150309280c0201a040f2507941d00c0d8100400140c1340d1101280050041e1000418103046606c0c01505603040007400c40d441401c000207442d060981c580ea0300341c00c041009940068012a858110742e90712960520950040100407000040c5500000070144001614903400042ca03000350000d0076900c0944070010410141141444044c1031a405081499100d00000070500145d084071401c1e10f00884902c0313402078020034006143c3c1000010001103d440e0b15282d0280138041e5103035076400000c5403c0364514403241c0c002078030150 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 444021142 1250 444019892 444019907
    0xf230d0507092013060e0d06020a05040302090105030a0f02040f020408120702041116030e0d050d120e030913090f0213050a0b0906030a0f1104020409050108060108060405100c 77
    0xa4001050719001a21141da2002420030400ca03d020340740344900d0440b80204500640c0d00e11300041c02e000008501d0088122400a001d11409030312240d0a060700000910350b100401c000c0c0340c0354032001c2d103607407a500400001c00300c16441b450090300240040c600044607a40d030701c11a907034126000a0003650b1016050300034001e64204034180e00c42c0b003d0044404200700040c080344ea00c2118140704101440751600c11b07a0086800713074080e1116024090000078010007206c0d1840c2c2010300114518466a00c0f5a46060307003910140022904403a841c01000009004505242c10b00000031883c00c0c51480102da0b06a0010b6294000250b41c0c8030505c0c00c00c506141e140004c1c0b5001001c01c400310000e141c07070400030314064407200c204502c2c0550703006240c140400945c1c4075074030050140ca0340240d42e49030000f11400100003110300b2420b81a1100309641c6038800f80016010300807000420b581000c0c0c0c0b2074079140c0c0c181c100a03650790121041000140c000503001d0030603142c001011036002c20a90040d141f41 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 444022392 1250 444021142 444021169
    0x140f0408040f03030203041a09100c170f0913050705041202031207030f09150e04022a010b030114040b010b0f0909070c0605072d02190507030308010f23 67
    0x1c10700c074000061660000140064801e02001d10211400f80640c0d01047e2049c40c0200e5004141072400502e070301d0040380141c032210b005502015003034036000e41400d0998440349000e40d440c0300109403d00e030b40c18095a481d210707442c0d1140810440c284040080c1080c001d034480d5804080f80d000d001e10440d2014011414010000f03007085448013014500505143c0b50714100ca40080c40d621000142a40340202d142e404000584640c182590901d0500010358064082e58900c1c1d03042c4401c114108050b20185840c400501c2c0000640c0c003220020182951594003010414095120a000218440c56490780c11100000c854566074001802c0014550242c400200d80c0f01f0031a41c100400b943e00030030742004907480307548104029962400152000903241d00500050750807030390780c064840c1c0450f8100268030000e004030361024200c24203c15000780d4100c0103c0709034101303050400c00c040c0c0110080d8054188044a210071506182c030240069404841400c2c000290500034030301500e07032130320701d0200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 444023642 1250 444022392 444022409
    0x102090402310609060302031e040506060111010b0f010315030611070c211e05120c01110418021804050405010b150a17060303040806010e06010210140f040804 70
    0x21108120251030b5502c88000d00305035042c4640610030004202941c085094801e00c0c0c44205100f410480100d0007034000404000001e03104400701c4601c090316145091103144200000c1c440e5140c1000010001c2030710303c500301aa80e0422051040c140d03920740410721065000c0c6400030749020055000302c04a20036078009040d00d880d018010401c5101c1100030521980100b036844505503070b402980c8107204d40c028400da907241d00d08202400181c034181108018503440c50404003044050386946040c4420070703513030003944240002e030151120030030700034060303545501400782d81418500703d021110110702c51190074a241d400274400740f04030441ea40780c110141c0054003c104d00d192030714140e4005c048216002d445141d0500300c142e609045e0170122040f9202c00c0c0c1c0c400b600b502c0d00c21015a81c0c908043d1100780d03d40002d010101d02c1010801c44103000305603101c0010b41c14200700002906101d181804220354a06000c451031020701e00310001d03908a507500c01d03a114182e480d801d0a0380e0340e00494110700035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 444024892 1250 444023642 444023647
    0x3040302070f080729031302030c061b15010308191209060c0801140f060d0605060a09030b06011425050d03140a1802010516060212090c01080c0412050102090402 71
    0x10b40d5500061500151101c9072a1440d500c40c174184181c0360b00140326042c1c08000d0701040014598030398001d2078811544003a0071244903440729400030b0420342101074440f2005d4051241800360003400c108140300a0b03540e4285039201e50441e1140d00452058001e180305408202030401c0032144a140b04940c2c01d40c4c0110304002c207041c58948a03001e4000d10007403c0000d00e8001c00400c40c41207000703111184103c002c0030100d4031580481442000c2e0001c50145140790b81e6601d0014141d1a403500402c0c0d1844a0307a95007515504510f0640000b0001401c43e03410804680501c02c480c608280c2250100149100f042701418600c54078480d9801d80104000e2a50081540c02c42c8981d03011382205c400076610004411256a4101280c0c0c1199480561880f0000b60368510311302550151000304000c552940c001400501070fa2109c0041c6c0e0701211030942d01c84502c008111102710248803501d00f52809103002c0c4080e04001070141c855002d00d0003810343c00e4281e0850442004000d41c1198a0224003600954 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 444026142 1250 444024892 444024899
    0x90418032708060f180f071403070504060e10170303040206180a06030615021222030f0b060a06020105330301060906060212040b040e10053114060603040302070f 71
    0x28040940701400064100c002e0300c04004004070780182c006001000825005207410f23250450b5214850030705415014240780400c01d07032214045d040c0a4045010340c020182440340403041c02103000d601c41e00c4002c0000b42e04c020105008401c994005404544140c5c541e89014095080c10420f10b06041c1d200d80c00a40010312035800d90032190032155100c64840140e61941001d071384444940c5410602a074003005503180151030300154001880000c029403141710707141d550307800345111942e00a46a01120310108642450110381c104064086803000303200b9030500050b100d942d10385104101162514100079040a0b071030a2807800e840c140001c0091203070a541d44210001044c4900900c4018040c40100c4001b9010600807641100c00300000145040c1c07034030001c0f80300700c40c002d009040300d02800580041c169960b46001007603003811103541e415000c80660b07488400301c0e6400d1a030300414181520001580c45405405900079420744655540340c0c1c2c3d9280032030800300290440041c9002000010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 444027392 1250 444026142 444026161
    0x6070509060c072907080f09150a17060109080a0f080408030a03090605060f0d0204090204020903011128050301140f1012050a0501080703030809031201030b151503150a150509041803270806 83
    0x106040001075903440d44cc2d107001110020202d0040c51000d52207040c00c00005420b04c2c044032100390217120180c3c01c0c90703103030311080341554400003100f40007948883c500782c1032229a228040c0c00c0300040b218400004090300226100c041d8040c0c0184c801e40d41d07066404150744403501120442c02001b030007000b1880c10a601c201ca41d8002800303d0603811400f501c02c0050600c80c00480758212500c0e292207003140e00e04000400c1d04080f40c2c00e03498000007040e10454842e150307040c2500d003a103450b44550000c0300b655004c060440c1e8004010041c81401d1500400c5600c00114826040c0d81d0185088146030384c03204000b5186124951144107500951000041404215498280120b00032085040e1106410702080319041040b460700131000c05c00c102040440316034100074a050400504484045a03440c12648070251032103c4280101d540000d51414503d0a445510b0000c00c81044006c0c0c000c0303481d10001d1803268051070200d00070309403414404050840146d10b10060401008546440c030344050b20 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 444028642 1250 444027392 444027407
    0x10506131e03051203010305031617030c040314120405060a0207180c0f02011401140f041b02010b12060705070804030f06021b0f06070509060c072907080f09150a 71
    0x1a01d090003400c810205071081138007124105c0341c012000354101581d8494110113140d80340401c81c0c0305140c400c0b0b1048440d202d0000342d0b11890f40c100500e82c41e036145061a0038050030030040c40b0540d8000a1349103044002c4e05040c1c40c151041980c80ba40c85a07841d8070242d10b801d40721340041c0382180500202e94410070941d08a4070241d4955920700340201c400700802d03803d0764400c50303101d80030001d0840148601030329a0501100c0c940010200901c5404980c041000c4030700603200f0054092080b42107942d000d40900461009110a881403518441c098855a88490000d4180b50800034001031006c05c1c01240c03c01c1d02d0156030040c582c000001490b01c0c06030700a41c000c1074011070000f840c1a00c1c0a0400d404a4810005015000540070680d901101214076034401034045a202c2800c0c0140601d80303904101d1400a0600036210403680d1001710300f8403201c1500c44061610321481000b10b0000220f4581c113580038070b00300805040d00c52a01d42c0003c0d01e11030a10030105041c00300400c4158034558000d09 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 444029892 1250 444028642 444028649
    0xb0406152102150f181c0c0501020d0e01050d2a08090d09050303030f0601120e06010509010801020421020406031202161a120a02070210020d090b030f010506131e 71
    0x1c010f003010b0404180f40000340111102c03405504400d100045140520204a00c80e12200a1000540050740c8860407151707490294180d52011003043d00b40150b507010841610029243d0809000340742507800024101d02c245000c0507d00d07034903040e200ca0386024080700721064000c090400c5240381d181f1040200201320440742902e040c407441c031044801c540144509400e4400c094084c0d491569002580c01c05068082d05aa0400000d80d81c1c690401e0064400e40003e0400f001c050289545440200250164107130030480c4240d204001c1003205000c1512f145d0580d40c0300e0201c0302100c0100c0e00011f0014805544081c0035008003004210309036501107500c120300c41482080a015945802d000300381c03c040c10707418048114040000d5294001d00c0e06d041a8048034450300545030234855404181c03000307103c40e46500942d03c00c00000c403285410120f01c8020302030000f05182180b03021184200c8880c011b2140790f00680000501146415030404984090001200044a1a16081c0f00146051540e10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 444031142 1250 444029892 444029899
    0x3070b0702061303050a0e030a06020d062d050d0507051e010f09141507050d020303010e0903090f0906031c081e090a0602090303040f0605090405130b0406152102 71
    0x40c000351a40040f00c0002000540595440d41040b98210040c1c9581c0000c0030855070500c15007203006c0010301d0500040112075044900402d4643c0751240c5481f181f81c0c103400f00c1c215400c90744030301c1130505505c2c81158200d4004885030f6050503000d08065051110307030b80026030002041d64985c0400c8030f80700501200b04200ba0388030300303101800c007604403075940c0a80600301d4000058212030100d031402e0b41c49403203854508041e0351303d4840e03190b42d81444c0043c0c0350b1808000d0382001c001000001c51203414113910000a4019518110508002036148000720742c40b14882d81c080d201040c0b584d1400c02400d4110000b800e4510708501c2c5406014101d40000c440d030001d030400f85648580714420045030316000b4a4448001d14a540003941c541d0081d4001c40c412940611041c00700003800201d0003210b100500d050740f106940c42000703c00307200c140d49004000c40803100f02820031034005605c1004807070b07103d40c015900146003072000400302422401c952240400c1030010300600a8201e00e0280075400c3d52084 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 444032392 1250 444031142 444031153
    0x5220f0501080421030b031516050c120715020c06060f04090308060420040b0d15150e0109121b0609180e070b04090b04050c04050319060e03070b0702 66
    0x2030004464100c41100c0082c13034440c0e01c2c48000016a01ea0b600045075041c05d0401052080e0f010001c01c0c50100340301074a840b0400b2210a0042410180c21956007070b600c1c610b86545800c43c4a101580d551045801921520500060603000d10040049201d0014a01c0130203650b11580d941d10b49959440642d0010311526190108401625240c41070302d00646e815240c0742c3c082c0d0740d020b041000802480245001c828070741c0c8480310081b5800e0005101500080521a49170b2200c0751511049031800d00b2913403580f4401e203205200341d401d1781c6c901410350350107031403d80510310050004072194400c1d58810540f00400d0800740081003a10782c00c5e04004242c0028010600e40e4810085401c0802c41c46070f0503034402c6c501c0b81c000ca090542d40000b40781072040710072207500555403103c0548581c0951b00403050207070f41c1e000042d01d40c030381070090f00d40160303000c00361a04250401c00020f4131342c103203000b4444070300c04100d05050400030260000744c4c58803071180549880340c5803410a203000c03c0003112264014000e4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 444033642 1250 444032392 444032399
    0x1e1b030310030f0807080316020f070f03021009080609010b0913030e1315092414010e180c0912010c140304060e1b01030b0607080d0c05220f 62
    0x1664840c0401d568100c50862464503280030b4144044030958448004000740000f01c2c101000560042c10940700903140c5654002c00281481d009242ca0544c1d82c104007800c2144c080700c101c0003415250111400803444a440400f594540310951200700c040c091103040000c3c0c41810340c40070101800030796a000050340e610044444d00010424010702003101c00c42100101d051203018095501d8030b016001842c0900181c014096100c160f02c45204682c0b102e81c1d8040120f02c00400c54101ea4540703514030031060800210074452076088840078101b15180040c100240c0d1500075880701945014404a00c80c201a0324450469018018803402202003049106803c241442065411100c503030b1101c0080d0791403c032860b981c0c1e20240064a890351110403600107454103010050a810b00c4000c68151000c0560000d01928803210f8094030420003406044003282c0c5a10442e01c080b04016800207695030b51006c291043d011707916005002c0b070391600842c0f039203041d080d000b0419111203110507031303481e0b54 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 444034892 1250 444033642 444033697
    0x706020c0a080a062003040b1b0a020d0503091203010b070b062403040c080d0905010201060611060105100327020301050a09080d1a060a0201020409060503030a0f0c081e 74
    0x80078070030009a54002e0f40000081041a403080e808059511072008034880e003c0c00081054209a0381915028007400034410445081c04d02880c0c00b2203000c900c40c0c100141c01401940f00c4160410b07002c00c0c404000001580903806001d843c1c1902c100001381ca4895850b0388003505160440a4221a0381d0080300208469140494040e80c3c168584050601552000822820b880e000503000b1a68004842404200c0d4074081c042c1409034400d40e80c0d10081c503403515000a0a4481c5a48101c0502809440c0941d8420303000c212f85064810a80d40c0b6021420040f004800801100104c4400f6211151540d15046150848000c00302d008a0080c0300c962202d902d9a000ca6100400040007032008025940d200b100a401c80320709503070a00c00f100c490b10292400320b07020741c1c41100540010703540001c083c00450807522600c0301516054000354107100c1e0000d0040c1200021040ca401070007405d50040d070802203484102c5120504002400c40000808a1817000302d0f00900c0c005c00100c06001c040c10342081 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 444036142 1250 444034892 444034909
    0x50f0318090a090f060c031103091f0b0f1c06020408100c03050106080601080411030601120b010e0c0913022a19022101090605071e080105060d1a10020706020c 70
    0xd030810824a110035095607170724010500c4507506810f240d00d0754408600c1e0746400d40518400e1000c50068800c2d1041c2c11000302c060030a131440440503510704003020740e041c2c032400720705902c60340c082d036414400086000c4988030003c500346005013118000540410210780c00300f01e2030100c650408003400503c0b2311210075001e540b402d00811001801f19000241550700c94048079401c140507801e440303208400c41d80031a0420009030414a1524903000d451402c0211031440c560045c5114040341c022410010700c2d916080c0b1600c480c0c940714014803034400b5401c3c201d0344d040301c01141c644400401d030546400f00c01441503200c802c0842c21401901c1c80020465071050700000916402050710a40000e81c8074041d48002c0020701104542d90b03108100320008409100d024082c00c1262513000d420410440070b2154543c248100f1000c001044004004d1074440c071007910402d0304c50304804105941ca0740d20031041d8003098200c5035400703002c000074600003e801080c1c400554000e50300fa54039001070b030000e000a44 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 444037392 1250 444036142 444036161
    0xb0714030708040f0510051503070b040504050402130614130b21070f0e04050d020d0203090607060e19060c0903021f0e12010b0109060f050313050f0318090a 69
    0x214410400100064810202d180d071092069828400340c0c00141c132050b1400050306c02e20503906a0342d00500c100c03501c00010000c001007080300184506c03821b2006d0001140a648681c6004a4031100814115a10120025810340c8400e9080251503a13650b00240d81c1140e2034051f0780580d0000b14041c806010030b01604458010180100c00e214144030145003030700300d03c007911001034000c00c000850b04042c4500f5010050800488054a605290502c2810490301802000c155031001c600081129008420744983c08400c83e00203440d12503c1c1060005050000d1400000d80184a11241e030140358035800340ca07490050342c0400106050b00710613903081100303005c080d41c8032907840911a01c03503032002c0c03c5810000f800e10b01040440040f17404110308000d07040e03a4411a944500450041d0350340202c4440040a042c581a181c41c035044a01404a20014150034107400c030b8618420180103003080002d2502204504807507513908220640c40e014240c001c0214480c0c0441030204007080e074035015040c0b0340c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 444038642 1250 444037392 444037427
    0xe0a0b160905031b0307091e06060e0112090f0f0b180105100302040f1515021009030c060504050c03120d1a0928060f050f0d080a03020702010c020307060c0b07 70
    0x56000f1000c0c00d40d03041440000d50717850712907500080b9501416005401c4000d0031940c1144482c0c440c91000000c0c0c07952034009074108041e07415902003a86e0300814500c5c2038610150001414211801d20840c01b4490b00d201504d4520000304180400c0510720255106607850345403820390140c81c3d07201c582a2441941c91038003200313095001f440545081c0d0310441021811100000e031881c0000f00095010103180e000c07540303104100c403140c0889a01800301c1d140c1c2480c001002c2011038001c2ea80a08600225140940401d03510400902045410820701444050090480b60032845900c00c161450f80f203456114882400c040340d000c0c418048950041680c1801004c2804d60380e2042e022a496418a02407030644241c60760407000180c140d031140d5030184c40c158401070202030401c02484501c54283d16504d01622251080001240c0110151043c1c40c80500e005680c842e400c1c00101c1e2403200400c000303981405160000a1105c0e08094460b04e290300c21240100941e1f11440103542502174940b84130304 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 444039892 1250 444038642 444038653
    0x30406121a030c100e100503090706090602030708070201050c010603080306040b012d090b0a080a420e010e071106090705010f050c0f100e010605010e04050a0e0a0b16090503 76
    0xb142c41e244650300340d20551460701100754412440018640d007448420400411f0001080c440780032818007441025001c0c500b4000b0a00303103003034030081d41c0344500070380544164400b2070200b0031a0720a038121000c40381a90003d00900b0f44905150000d548181c455500c9180b8040f2079180703e5000c3e040500000680741d4904c01d0303070608014007258040f03402d0f00c6c41c07082045018003c01e1015116002e05180e000315696480709e854403100c5481103402c030011010003d0401300001e011400151400340000b0101680b03807212500c0c0c1050704211420303542054a40138011800440c134400d0744e020b5940320303500300c1d03445d0007080031108009034548d54140c0e450b204c690007d00082c400d079400740d80904c95440709450024508081c82c0d51103400d09102c5810329216800c000e100308940c00d020b001d042c4000032103000030040c1c2454030f000600038000c0540b04500440c0c0712800280da120017a070107076a500380c800040e102c01a00c4c034075051101c8070040b1080000b00412005103410648070b144c001050b527201034020300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 444041142 1250 444039892 444039913
    0x307050a0b0d050907050d03030c0e04050f061009120515060f011b020303040312050d050603030c07090509010905070b0406080a112d0406020a020a0b18010804060b03030406121a03 79
    0x1014203c01010402c0d144259140015503854240225808034041c3d98001403801514000912287c2210b8042c0d104604040601c100140700c184240d1304200111070089c4040c90190f41a0360b5080075900c006a040240360003003052020101d00050444489511340e00d4980c0c0e4502085142c00381d08203910300098403d183d2440c14460310f288112002c0c001800c032800c0956a41e20841400c030201c003c03d0006801040d215540c4182d4042c880d0411002c90203507080c010307510314481d41c4412600c00c0001d41511080440e03400402035201c000b2040c0c100d0242c40c01c1070713207804101c88507501a12684000860b0f200000e07000c410144200c40000e161442c900e4502610358101070b005008802c0c0403000789e40c4054800013048400402000141281d80260000600c0c5004108000049920449811004000950b001d4641421603841c0c00340034249800710352a64248031004001d10702503507801d80b00016011640d1a009180f040000112020902c1180e0603902d0404081603804071264040c0c4c03080001300c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 444042392 1250 444041142 444041167
    0x703053703030b10200114060f040b030d0f0207080d05070602071b091a030303060a091e050a02090a090b030c0103021e030a0203040605090a0b27010203150307050a0b 73
    0xc0d11403602a14000c5070355040c1000041c095214507070903901044d80c001d07036903501240c00c00200c00e09590400007000200c66500c100340f42d018000340002c0c40703400764083c140f1003540c40e0390100c4007407c0050202c0b600a40000000740229210203803c0000d880354070f00c0041c0400300044c001d030118407155070f000c1c1071034080d5031003c01941100d0b80844111110b02056603801a90004520041c08240340100712508001001c081c40b0b00061011406a0010010031440751a0903d80c00115955544000341503410080c038509203e00b042864001c040c00c0400348020040c031600a80f902d0311003150100192903441d031510003107031110341c007250305a00030102108181d8025405494900000c02041641400401c0c01181c103900841d280d00c1019808824401884081d01c54241d11184081c014405d0038000e4030366104540b0001d006040791030310202e103804038444500000c0c0700d074a03101c00250f4580c2040e4001340007441598100c40d009119543c40001c1d00e242010f004807c82d085460102d142c00300e2500b24 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 444043642 1250 444042392 444042493
    0x12050a03050a030204170709050c070818010311070303050f070503040b24030f060912031e0912072010050a0c170708040e15092e0602070305 62
    0x3036820315900f0b22000a1072030380f50180810b446e0a4501515505042c91120011100054200c00c00d2507800d0003000c00182014044480307443c140b000c2c1c038138050b012200480c0a0b2240240042c49804080740c80420560103410413802185080303035a040e00d60f2146402ca840380000c980c081c0144418502083c210020a615040c1000e400d00d0b40c5a0541650004a450040d030303103102c0c81c9039500070820800c00401c00d10119025080543d4000c0ca5818810016200140035180f070240c0010010007140c89504200f204102040071445000d0f2100c4641c1071104114500007070f0915881c3c0101d68181c26072800d000c4074561000745807540ca0401c02d445900702c1d9509080303c0b04032225903003500d0441101c0c5800021b040e003907216609a541d01c03428103170020300c9050f01170814040c00c6805401000a941d801620981c0810b0740801c80c910301d400d1000e03007c00054054008080c00d0744031080401e83da9408242c02040d0b0340a40202d5175030300019501c10b8201103c150110b06134040310400683c41c80c01030b000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 444044892 1250 444043642 444043657
    0xf0c03030e1524150a110a1b05030138010c0c0305060105120a0506041e020901030c051009050a0b09010c120519020a05060403120906020412020a12050a0305 69
    0x315070302c91900d0b051000c0b04010a4591040000c041c1508032030901d12807100c02103480040e40c088141c400000e0120025000707401c210402d1041511000b00203060402840c001540c000c0255010303401000441c40c100c400078020140607508200301204d20000e49240b4904c0320b141180c90000e0401c02000d4010308800194807141040341d98a034101c0440e40c4a507a10024600520150810354504000c00803080381c10090380b481c3d40c201440c1200881d2004c9966a03000d0303004508100c0d800e12004400780c10007040c02c3e0003580145424004001d00c034488003102c00342c0380140d0304020ba8024001c026100010144512917006803003c8040c004070740308002508003014107050201001ea92036450541038420802c01400007400403401e0041981300111545052071540040c0c0b030382420030b40f1029140c042c024030103020300c41100800c0c1002c482c0381d07110b5500c0700d810804c115143d545994558484920b45031050b8800c00b841940410080d040d130041c0e4180c0d9030300600030080c1c0e007190364040d503498000c1c52 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 444046142 1250 444044892 444044921
    0x905130906020f190f0210110d0f05040b010f0513090501110a021506100503070e0105090316032001050a0e0102010f140402030f120406030f0b0a18050105010f0c0303 73
    0x58050300081c0c0c14005072001081414210f80c94484168080e03603542e000c441840100301e98000084641500402c4204108901c0320011641010990180c906486445450b50004e4a030031800e190305140395000c940920305ca4510030365641d9981007a610007943d00c0c003800f40c4c001d100110b4841c1d0280c551744250002d902c20000810952004815201660030800e240030250300202401410000481c14441c2d02000448440802040f144030042181c08010042414007c00700a19207884e802101038034800c4100500301e07004c00f0a420f903c0043c840040c4021500d1041c2d00402480c0f03494000949a83e24806948850800007414001c50b203c0d801d0706500c5066550340da00c004070401c1e060003030840100c161031600c0c14504040c8181031410313003c40d51440d1950055401030180ca05400200c8040352524034000c100924034001810040c141030f061980e0081401c840010004840b00e0043c110b0a1921010425030383d90b040159860f04c2c54107511000941401803480001c1e009030b01c16050316070441c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 444047392 1250 444046142 444046151
    0x150c010b04022106010302030f0f06180703020c1e0604080a090801020a11100c091203140a111005040b0106080a1508061614070b070212071a0106030c090513 69
    0x80e02060407603000321004514244a454034502d81d003075548000c0c3e0814020303c0c04510318a080610a0000c14010b4201c0b801540c1044c04142260741303072440c1e000180c491064030000b42c102540007400070340c00820302c0140b6004003900107601c1c1c2841c4903885241c201c620060540380d80c9039540d4007410b6004c85403000a01500e1480414558400d00c06400460b20a440d01c2c1101481e0690030361031301043c1042c144d4030300d00b460304045249034000603103400c0751390309058003822507654a025584009541c0a80e4013900000ca0450303070b0140e1242414000011020942e070301010030801d144140c0f03100700c50240051060800400505115124030f50b4000c440c000c00040403c0b0303030701c00c80c2c0e1880302e19401340c01d80d58841824425907c224080d85421101c00c1d00305200854486506113440f030143c0007001d40031034010000501e00c64002e002c50481039001080e15540d070a544d28000440c900410000d41c00d01c0e20800001c03980a00070310880a10401c0c0c0d0703d64000d81c9240804000c042c44000d40e80690450b02c9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 444048642 1250 444047392 444047411
    0x30a140f07060c030e0913150f051302090f0709060528030603110301023f100815090303150609040c1d04110a1b170c1b150c01 56
    0x10300142000c1d100b96a590000c00e081800c004050f0f030340000701184246012401e000c00ca08180c154004070760341c00f44510040365140401d1600800040c0c10400c40340e030030301e0200540740464101b642e80c624400c480114207a1901600b00114113001c640b000c01103240200240080b83c001d4014000a4a1f0080718006141c0f500d444081c0c20016034400d60086510340e0403d00802042070078600f90350344103800841c10240030380b21020704140d1640d03e1818076601c0c0002c0d10024441c4a41c5241c09422950a10220741820354050b8101d40c014841e120300e60003865075071000205811000350140e48007500540c01c54851220400d030700c1c00c0e1090762a910080c104102005612240280303000311496446068003090011b40c5003040103031002c00244602d1420b00d1480d026220a019900011018a086148040c10348091140151900000340402a01000880c0c0c054504401856100809000c0c1c071816800105c0e50902250640b050640c40584100d00340c40003c4540081c210b003481d901c00114103c0038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 444049892 1250 444048642 444048673
    0xb0411151804060503031620030f070617070f120609050c2101050d170c10021902010e060a0c0207051e0a060e09061c1a090d0806030a14 60
    0x1c0021003280c420048001c84400349454801c0600404064020394a01402c9490b62004051034010041900581b00440c030403c2c0d82d17110507542040300207000c031116540282c034210f907500c200744100000140d6200c1c4172401d1912440d40b482c010005034440c030a008120307403020f591040a81180b000020350700d140c005580d000c4e6005503402080220780c0305903585040c2e20980d4059141d011401d05c0c0740914001001140c540007244000036030010b60b819032401c1e8041d180c045a125610100320036100300c03030078a205400d40340d009080c04101701c074540565207503003841a4281c807606503001e15242c10000000b1007800c5260480e010005503841030f907004a03141c800080c80f81940030301030401c01700908000b40c2981400c1c00f00b800600b0b49400d0503007840c11498001018050000c20741800303200001c01c404005808403203410707540d90340080440424680002c1014040e40200c0b081d00c0203104980d085003a003030041e080b250007404060040e001903500368458032040485aa40200751380f007241401803e105 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 444051142 1250 444049892 444049897
    0xa0b0d0305160b0a0510060c12030506120312060a090c020d0503060102150c0a03110f0f0a03140426041d060d02150a02011103091c0203090a1206050708040b041115 72
    0x81c80d40c0030005403820025554142e05810360009824232000c15132290100700300210701440314500c1e250104050b5076403000300705403102c07c4509030044d10000c1801c02c280a1045c1003c1d2140c0c205998516000d0380c9c5101d4001071395035a200950158000f5000641610701c543c0041d41e02c980103004585041c040c0f0001038880040446d40415000d0000c00c2c8240c40d1076060040c1d494146082592a0502d5040c0400c148203104100e03003c11003140014080c01180e0103074002542416040c032960805291038202044041741d01800a200b0400c5082514001d07403030303082030300c0035a80c0c0d01c50b900e66510602c0b03191550742d034000f5180c50380c04422410326000613558108d64402540b81d1071605c40d100da103000700103820355150784500c0305a4901402045401180050040700080c0d0300c59155202282681d0140e04611803428000c4c0c100d00b001c0804190440c1080c50145205e114030010030040d914004c0840748684140d030f0040482c54000d01081c08609084981c0358840d00050003034452020310310031600c90b036 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 444052392 1250 444051142 444051151
    0x12040c21151d07120b070c03021207230a060624200304060c0b01080604030e0402070312060f05120102030705040b03091c0314060a03170c120409090b0a0b0d0305160b 73
    0x13420000030000c0001c04081c01c0e40116582c24542000c240356900a074503101034540b0303500e400101143d424240008040b5810400c104079504200041d031500780c00361120301c20441070300c28500f009800070390301a0b005008a0a076100c00c00c8051007001d0940110b03242d0103400701d66103c008403c444080019024001000203010580300c140003c1407502d8401882c0005071b1001c1c1c155004039003080301103508102d81c1603444100300d03001130742d03011a4501610084075038401d013034620303281c1100440d82e00110301b100c0c019075004039215074584210340c41041c02d03844102ca000c00080c0b002e000401000c0c1c50381024680090030241a9005c0350811250b89001a031800070311400030361280051205164a0305446402c0f5005684822849056446140b068104100c3e2191458000500c0c01e90408040c0a2260308848082c0066a40c590700c1284201415001c0010f40d41403554a0124a050103184282c40a685001d02144644040c6440039075071900080c1d102c100c00070407040e0070400600341c0103003a40715 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 444053642 1250 444052392 444052409
    0x5010c06060f140108010914070f0c051b0a0b030105060711130510091a010e011b02120a1e120f0e040e0a0c0b0f0d050c12040c21151d07 60
    0x6403c0d0000408004042c0e005180040c545913401030040000964030361b2041f81c50500310344e80e119404084803a03e00b1504085d1090260b40140b40c91340c40c0c5c1c034000d0240300d04104c610310446a103c40b0b054025100a01c18940e010404002040000e41118409001500024501c456503010380310398000741c07042200c215111290000044c003046a641c402c00c0004520340c0401404201884000f038154141d01c1842d5042c0143d41d0301d00361441a40d01c4040100a030b0160a0350351103425041c2c0c0540e030780521102100c0044a4100c04407105096000041185404c501d280c2003620b020001a540281c0c1c04002e03108001503114400d840340c8641c01031100c10004400107081480c024180095501c03ea60407004401800308182d05a0303009402c00e5490011751a400011a5204ea1818100d1403140000300204d40342c1000800c2b00380659882c403441110b90008200d60306901003448034448211180b0000e003031004600c07480c5035240c819404a51610800089c101c2c080c820712141d286410a0360384108034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 444054892 1250 444053642 444053669
    0x20c0d26030126061f1203020102070c1403100213091109040b1009030b0603071e08010608071a092d0a0f0e0c18100e1207030302030405010c06060f 65
    0x141003c69508401c01c2e940580f594a031034207040b05910380720030000c0c00441071140810703c10030360035460f41c9201c0010919540c1d020704109440c540070f4040d4110314825500c0301c0f12007000062100302c1f448080caa001d0001d01500780440360500b140000e400119070030681071000c000118800f1010b110700c0c10012401c0710801d4030384c1c03032030310800080e940f0404500d4010702d0100c00141c031080d0403d8070b00f4141e0340c0c404050038880d903c400c0407138a80130495100c00c540d03007040d40d21103509008480d0844282e030b20341c10080c800e2540320b40d12680c0c1c43c400c500c2410b10844008042d5120350b400100640711a00d4002e082e085060061207114055403030000403035081940358900b43d00d440c508240180e0051583c08880026145890021802d0070002006d050360141c000031003600bc1310a4205403c42070800500280d80f801200c08018146609400064051154014480b100400001d01881140d5059000f07524081c00c18004440f0361440600880e0603d84a8001042c030070545032010007c0c200d25000200c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 444056142 1250 444054892 444054899
    0x40b031e0126010b0a06030f090204060b041706060f04020327030301170a0f02010c0314180a0902161202031605010c02160b030a020711030105090d0816020c0d260301 73
    0x4600c40c2c0b168002105070b00d0403d07020311548840c04030354112000da050010310700b10320303881c04000360003002802544140303441c0001c920301c002c030030182c0f06070703541c4c480700c4584420f9001e54a9603405095641c00c1d4032152840302c60010b0300c0c09030000d6921810b004440090360440e01b040500050000c1201046a00080010b0201c0405840c0303416554021200902e510a15038440683d070203505003000e4100016110b5150901d03003e1b01840400c842070243d1b040e030b07030900d45490802c00ba252010440c4250014840080e615a05009580c121103d000c2c20316031400c0e40e9951100444500341c5281d0542c0001e000d03107a248240201c101e881e003030183d4004a01c0ca48440320090400b403007942110078400000c07406019001c0b042d021340340c0c010b080190041c2d88800311b0400c5280d030741c01d2000da96810342c2042c04002040070040f070341d0342110613152269500c580741d1200403210ba45051001c180140d0001416400a16040018bc0f4040c1c0c00349070342d80302410300da05100000500036000b142e00d1140010040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 444057392 1250 444056142 444056189
    0xa2316030c12030b0901050909030c06040c0303091202011d0a050310021e040e0c1804060b0a170c0a0e040e01090c060207080724110105070e090f0c040b031e01 70
    0x20b81a04241d103800c1200741c240380c00069005406004080c0586001b000182c070039001081101c02d509050310840b00d15241514106442c00018041240018201400000d41d11810914130410f41d0303050f100c0f5210f4020400d04581030003c8600c003998000b41d40ba400140380e80301444000c0080d07411100c056580e070071601c800710a420340035550a8801d00c04100c10002c4e00d03d01101e06030041c1c0f0080c45259116011901010784c81c2012607410b9201e0314107000090b4030b600001c0201201d60075030b01d81d5246101035010742008410100c40001054030204042c01d4502d110301600794141400510028103492250701d228216065940c003115881040e800900c10541c04101349401040020020329030345003040c500321000c80c050050718100c83c400301518041c407030290016688040202c002000b45e40f0302600300070301e10784005d4200c1d801840143c020400b03503101100e8a038414a155030301c0c41e140a01c0c1000042680c2e10040011400c2d0301d40c0d21a60210745040740a042c001d106108451641a542e050321 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 444058642 1250 444057392 444057413
    0x10f0b161e0204050c0403110603090106030b01061215081213030609050102040e090a051905030705010f060f1221050c01020319110a080711150a020711060a2316030c 73
    0x175200e40d00c0c1d080c003040000070102c0350400c0300001c00f175490030344a440c3c07480c038240035140a400007010b2106c0c07c1c0002c114a40d000c84544400c850202041c0701c241941940e03000886194001c05410303030881c10605100002560040408900007032400340503507500e468120132241031140407a126500001d04204510440d4070301b80d00481a0340142c815100d25580d801e0362505410006055445850b094005100042c82034511041d0030100901046110002040c0209854080c40c40744502503040801c0b2483d01640303c1d480158015801b0003002c0c08580d01e4000a55030006040c20404204200b101032002030003d540558461100c20748914840f40400c01902c813540352100b0048028058000742c998444a01d40c0c00c904242000340007070503402401400d107001140c0f04ca80b031841e182c060100b041441d41c02024014000c145504011011f0400c001c2141301d1543d02000050003411002d59004183e149520004d045070b4a592a11410b146410f2000b08040360942c08076900c03080345024000710600 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 444059892 1250 444058642 444058651
    0xd11040801150e0f0417030a06030c080a0803010b0d060803121b070f020f030139050316050a0c0609032d0512060f0d08030403020106060206010f0b161e020405 70
    0xd800d0100707410f001d14806103c200801c05200703040b0b0769004c01c0501c14182d42d980549000c0e80d00240e90b030324001b02c086000c0c2180e844201c2e80c14448100000c1c00c2c1d640858006c3c20b0b0359010303401603c0c0d6407820180b040140c1041d5000e090081e540d0100103000c210802c02041d4110100c240c00340d0510b003848071031200f0303000c00400500030b14040042000003915410340e820319a504a4a10001c0c8041c03c02107801001200c030b00500d0b03c1000c14030804250300d0002c03103421030040010f26801c40300800e0f0301124503000542c0c814600c41105181402030780d005001034070012030245410b07401907201b43c941c03c056441c40502500130035581c01c000c400008a0304821030f0300ea105c140e40340f00780e5250124000c003244135955100e03a425000902080c3c90307a81708044190301c0038004050280c0c1d81560706000146500644085015620344940001c0041c00420098100c8170110307100000c9a15007501d10301036500140c2000c074041140302c040000075081e03085100101101e83e00d00101028184180400c5980191 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 444061142 1250 444059892 444059921
    0xa08100b1905041e0f0207110d0209010521010507080108061308030a020d0908030a021c050403080103020d0201120c080115020102091318050a030c1211120c030d11040801 75
    0x3800c0142070a400e1034403104480007542c00203a40404605905000805904032141c6113041200340c0c1041702294002d006007501410700021800d050404116010980c10402900404000010012482c1c12500701ca480d50f400c05410442c044440c20260840b17104554040128120b0310050100800070003c66600c0818200c803502c11070800e40301c58480740401445110465000548800d0320031503908141110b590201e02d154980c104108400040d4210840d0b03004d0707040031540603410310510360040601507038240d02d421856900399020310a0310116500164188001800f40044140961141c2c46240b8180e5460352400d505201c110344104500070104421a801403010601c182da8806000ca186103940d01c0c000f541919080c400309603a2040c0c1d00c040c00e0760203400001d5082c141c00c4a40703401e000d031003140d0002031031079105019280c0a00c80420380c209940105d03400130703030281c64900030840c01114a084071f0400190700520001d91310050503c1448010100c0d0800041d5824040ca10070403140c103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 444062392 1250 444061142 444061159
    0x2130e160e040c032d080a08060d12030b04020f030703090c0f030b1f0e01030614160f0e0f0a0305210a120c030902041a030601060201050714090f0a08100b 68
    0x1e84a070b04640030036001c0030b811007107050b1005c09003041c1c1d12100f84081d1156075411081d030741e82d41030440040c0c20120407103022590002c0061110300d004400842420f90241100701600e0f064202200200700880000d60041d5003007040446820640003e54030440190381e010a00c0b10b03146c070f000304081c8442e60010b581c0680500c810f00020700440070a80d4000c0010b8141c0340d0340145100b5000c3c03810281d40c000d28400955a00100c14005503400105140d88080c1540c0d4603501d0700c0c02000400031310321071442d000400b10744503488010b11403403000c3c100600003440c04082c92504000141c0c2d803d49640b080f14658421440c901205041e2002120380781803450310203040c035084040190500c43c42064000f000356844420580072070007648000307411900504100410385500200205901e000080a4464400d84000250841c414041c1c2881451696520030228098400142d020b07040704410b140c0c41042072608140a031601c2845d200200140c0005160210620400d4000c81d00000810f03401031128 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 444063642 1250 444062392 444062401
    0x30e03040b190e190e130602040305030d0509070f0e07032703080906071b05030705010f0501090e0a03090b0c1906020a1106060108040f050c040509010c02010b0a03020d0f02130e160e 80
    0x10340402c0400c031061700107030110f150381c0d4814441e24584c214800908680c8007040120501c840000a081c07110b000703000c20400342d183d001038107903540c10038030580c164040100c400340850740340c60200c60b400494a042c041031210440b8070384003003070901480c0ca40f215840b199800c000d265200c0f80191f000884100034122908011a0040007003100d06a01c81408610150903400c0050820032a2050f5801100802010714542c3c140e40181400384900740301e403400d10180161b0707007101290340080c50794142c440328071941c54000c1829480d0088865003080703010340c600d00380d458082402c00f900c0540c8218001a69102e104002906040e49000c27041280d520800c204041e60b6089200f60360080d8002410402c40015880c01c0b0345070444100803160490306010030f200c0ca0520541100385851001c3c0c0081c0300090204082c42015181c2c0c1c4030107940220805078a9001c542880e2800380140d0029003030b0080401e0140702e01d01a5041c8903441d2141d03a104501c55641e020341c042080001e03205908203107485080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 444064748 1106 444063642 444063679
    0xc0a02010e030105070e040f110415030e070b03220f050c010f02010c080a0905031201031b050103020306030a022e030f0507090503030a030e03040b190e 67
    0x201d542000c1c0c0764581801114814144c42e40d442449081c13001c10071015040c000c45442e44196580c1c080a0703148403102c010b0003e009040b218034800d80b01d1210007412078000195018041c1c112071018825400c040c41140c1d000091b1420040100c00c003210240500101580c1c010500c891300f1903420100b003004202e00f900300303400341c80303484081003d01c2e02a030036030700c100100100144c80c0000256940341194003003107800e40101c08a0b4100303501481807100300202038201359014071210095400c171001440c54080940000e01e02036046041c80c4001c00d0391000b94000003071180c0e000e40c48881d51106410900062101c0c038a540740d240810201c00070f40101b12140450041c24203182c00120341501608160080380c002400540c94088580e80c11801440c07007101003411404104000103c9000304006083d281c1ca80300380000c0c4045107507602401d1202d403074041a000700d0305001e40468410 = true := by decide +kernel

theorem cover : BRFrame.Cov 443884892 444064748 := by
  have h0 := BRFrame.cov_init 443884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 443884892 ≤ n) (h2 : n < 444064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
