-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4548
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:58:38.227494+00:00
-- url     : https://prove2.me/submissions/cac0018f-303e-4fcf-b52a-e2ddbb65cdd3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 817805755 ≤ n < 817985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 817807005 1250 817805755 817805797
    0x3030b091003050a0b07030b030f030903100b45010e070509090403030f0e0604210513060309020f190603061502060112170703050307090504180209040611 68
    0x300140e04541c080c1c1520300c0440410324584859031a030041034001010501304500040d907075030013640508000c01000e0100c8404034080207405699911a540103031281c414050903240c06502c030b001d007510001000c0c0508446408001c0c2c02d0340854071403800c5907845481d02c20b03030312050307111164202c200030048401c6500315490400391032a4141c0c003921890420030100014030a0361500713074003545c0050b070610340055403514400500004195940940a55005500601c0b061100021415440140c203565000800702d00c00000c2e41c03d80702c1c0b14100c1841a030120010002503020b030707000300080c2c0e001800885205242200041e2410b8404c012040070084045081c0802030745841184054041040c9849800d61405806551000144034225107a921484203204005214014044400601e60015101d1415140252640e0400c41d5401c0002c2c124903400110351400e07018401100d00d0200024128800507000d0040102c4018416560389403548405020102100000c1840b03595524a81b00e00003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 817808255 1250 817807005 817807009
    0x102031b030c030403120e030703081e06090a051909060e0d09050a0512120f0304030311041d09070315060504061d160309150905210a1b0f03030b 64
    0x390403450408506010300800441c654207400b1039030400d40600700203150782c9031409030001404402c81148035900000c110182007603008458180658030f01e1400298001491038603480480084903050b5102c5075880101c1e0031007945500c00d54100040240c404101c082d03100f0b0030801e503025440300300c1d082d0351380340c001a00d814000e000c2c11003504105c0c940440900c0c500000901050355034000c0d40c0c8103c08040040348800f504100d01c0c0c0740702c5c43c00602544c40b0142070190718226001100c0a0340401e040c64401801c21881400300e80a58081811003021042c018485141900d0010f03c0540c5600c6440c002001207482051040e50340c20310164045002c078100418003003521500c3c2e0212002c1000e005100003030140160803981c0c060743c108504884042c04540c110050041500d000d08003000e80004104a90785a0300b110b80380364021012500108840004100c46d5010313001485c0c01c0f44018819441860720800b02e58204d10149104c018680d00c80c0d45401100004541007140803075a10848180c0368 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 817809505 1250 817808255 817808281
    0x7170903100c0e060c0313120b010b030f162609010e030310031118010b04050901140a030b061810080d0f08060d0f0618050c040209010e06030406090b0702010203 71
    0x4140000080c884062610b00c007801c18240e062600b803086070b02007420300200004001340c403c2621068292801380d592081c41c0004400300c12000c0d074401d00b5400008c203814040000322030003031114000401587d681e0a10b224150102d040c00c41c07007000015085031642041103840d480030350302503c05040340f0b8280b0900c0350f403c42e401c4402c4004283c005004202d10040320000f10012646c1202c800d0702e040c42044001402880b4584800380103204050000c2040c42075100a40166201a1201155a46c03542100c51020b002001702d1944040c16030070900016440707800c2c0c96000803002d44802220010700b840b40e1810341003112280000085007008008000b0200b0107054030a42d00d09020f0728032501100e0050041c000100303050b009448a074850420484060300040c1c40503000007080002c007064140740990340e621400705903403900c01c02c2015005c80c034091007211100101611051994501c00c41809000d4000070010b5405940d540844400700d07217284822881032105600050b501e01c3c1502d1034001ca = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 817810755 1250 817809505 817809523
    0x20d060b03060928020109090e0c1c05010b01090e1303020c060a1205100f0e090705060d0507020706050903101d03070c0305060a060b16170a0207030c051c020607030507170903 77
    0x1c07803644e51400c030000d41d8002503214140d42c0c041d00701080500f03200381d21a10b410b0550a070213400c840007a14001103501c000f40d401000a1042000f40030b84410013004460074406030041d550b05480002c0440c010780310b21601c03840301c1d512a005075130744450300320005441da401c18410900400d1041d003203003000002c01e2161540c0403180c05d540303107030b8a8141005202030940d07038000d810070319500b000442c89a2000700844001407100030500c950b02c00c0d58605c101e01a040c01d40d03411001d441115004140e40e8011b006442c84408083c0c01002110031a5108401a0400040c40028a0004921000300040900082c00c0045c000c0301e0403c1181c0c0707980390031841c0480041480c04000e01d064000c0c00b0040007403044840c00354840c1421500c0000300cac180290a9500c0c90b40055442c1d10008038141d21980100b54441103900420020308090355510070b02c10b108070329001008440c0c440007070840061811030003824059000f8a040b40c1014440d59886000109207002c4890902c1e000c0342c03c11461804004d2100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 817812005 1250 817810755 817810813
    0x50c06070b0601081b031e0f15010c022719090510050c0c070e070306050402040b0904020708120106200c100e150d320103020d060b030609 61
    0x45001440c0d1910305101c100a00418100000c40e00851040d07081881c2003501000d42c0200240d407070414808180d0410f401d8104440440300c0680007548070016459000d00c40c18000300040c211070b108600441c0c10001801c0e040b680f00080b1001c1c041c510f43d0652070144c800c05659402132160070400000303d075840d5008000c08682e41000200c8000620126143c40341c030200c0131010980c0d0305e5108800c0c100303001d031078502000e511403441c000400b07000f40a01c0394060090b90720200b18440e20b640c140001d91280c1d01030140d4441040002c40f03910b04155004155082c000d91700c0b2030915124450a180b12142a80b1200001d80c55144000f40f134040d91101c80c1000c2d4540004200701114a030209045220101c9280d0511235109030340401611036038901e4096074a00307150f807542e030742070280150300604208402010608042c0038480628000402400e101d80b580c0d400710003a03071f286508214601d104e610040742c4003a160b4003281d01070b850030031260b400741011001070a845102010400916000070007089 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 817813255 1250 817812005 817812007
    0x3080c0601152a0204020304060c14070f1b1206020d0b04050f0403030525030912050c031806041701020702130b0a060e0406031e03020f1b010c020f030303070309050c06 74
    0xd40d280c0e400107401031103054924032030040f04000340740c00800c4059841c00613402a0000042200f0017510f5480a580080c01d52101c540d42c00c95020000c040740111007004007240403c3c20340401080390910603007402481c3d400146001c40d200c0380d481c102c107450b500044030301a0300480c00180c5900c160040c030088903000d560801031072030080710003403071420054009401c0c166590042000c1c3c001105581c080c1c5002030b108400140585040200240f030260310130f40b0410701401403082c0140c812000c0303032b261285c10001142400c009840001c503500e400451a54041000c01c0009070703c0c140302802040c091002000161581e00078018003d068820303c1458030242d2030000784d5a01070340c0380400034054526500e4010030b118005030100f0300800345a000504040f00440072012080e00c803600c250300d40c0f840383d400e840410541e1416980d803a60504481c601c40015107440c150b0310351044160000030f600050076405100842008207003554015280c80c000607445111040c2032180811510301c220506695107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 817814505 1250 817813255 817813289
    0x290d06030218040314160809012d02010b0f0d1707061a120c1003021804020f0a021204050321070c0e0601021905070504051f090219020f07091d0102030103080c0601 72
    0x1b8102c0541040c000b400c48002140b45a02c5901c5160100407440d1004800341c2d103500045504043c1c02030210000b030056013014461079185c10300717500c0b0b0343c0e4048016201401d0000c8903603400201180b84441a42002024001c2501081140c0280940c0715500f40814071180c0490091018000f9203d41603181c50340701c11601d50700d5072960213404c1388040b028680140c440c020825464201c00151b03441560042c00441d17556400d54001d4000e03d0860308030340840701c00b005c0108455245008a2282a515070070132086005685a005844085803082c00e002c249000c1d03403903841403440380090300961603041c60720f8200036a0b96010024440c1803502d000d00701c1c059111940d2001d40d1210a401918020f503103400200d40012800d18159012002c1800c0c40e107801516116070708003c0d0015548600a50b0700401070700308450000c00e88200c40e070190741c05803603024180300c50034001e000300d10018103020171180c6d20000140c0c1e0a101842c0a140f00c1d521055031007582e03803401441c040f01a00311a0120104401d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 817815755 1250 817814505 817814527
    0xa0c02120d080f0601020c040f020414220f021204030f080c12060d0309080f0307110a0302010c0605040804050a032a06020601210b1302030106290d06030218040314 72
    0x4410383c030074a00c650085183c1e035443d00403420541c94042d40ca40040c1040300d0900346504540151060340c0e02c11041141082c0d140d01046910300d803442d00e0030b5500031200505034481019401416150704511005840e0480c3c03401c012400081c100c0301680000c0d402d201c070100c515842000300d078101c000c00315280c0c103040c03000105c6100140040d11061041c1552644c2c0400c160142d008800202403000a40c1e40745861150f03c030761a0ba200710401c4402c0c140840f800307070442c6054000307403084d030390103035200e265040c11980d81000801014109507403030001807000090660355084003c0207580301ea28450300c015481c000c0d0f200c0da0080d1401c1c040f2034074030740c40080c0b10703040d80044c0f05070444008a000c051841d0641525941040d100d1401406552072403040107002e00250700c680210920a07002004841c1e510160510407002204515001c002c2c0107080d01c0700321800d0b5014007a004655500028070301e80e241c3c00555519a9031413030f0104c40700e15500f00000e140e0401080302c100780414541c2454900c030302903 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 817817005 1250 817815755 817815767
    0x504030809120a0e0a050301090b0f070c0b0402060307030e01020307020d080f06010e150d1a010e0301110a030e070f0e06030f0d170408090a030303060f050a120b0910020a0c02120d 79
    0x3c00b0300800c007183c40983c05035622400f18034001d1002800030007005480381450011408110354105008805030b003c075141c54859060640b281d9007080c0c3c50109030700d80d07508111440e800136140b50101620f031001045611401e10040d40211041c0d0000c215042da4108041d1507003030b00414014001c001b640422007144d030044441c203402e040842d04c2001c5031900c410449814081c03894261406803401014508641400c100381e1003418007601d500c4441c07014a000c04d4244c50100b80381c1c08940e1000d22901841c24020b810001014000b00d003a50703046c40d21540021405112a401030f0f145248100502c402c3d07041c10b00032440d0415052001c0c01048151070b4010303082110400c5004200c044040000701031200d44c42c290f460088008101d114600c0c0e81e0f00b402400b0b40060300801c681c2c0c07140300740d0024407407900041d00b200300c1e9502042030b02c92504a07141c10143d20001007402c1010300922903141c7c0070f075186100030503203501c19450703441036845c0900501c815804407220030b5400f076001016050045d40c1000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 817818255 1250 817817005 817817017
    0x211b0f0b121b0c032d031501030b04060b03130606050904051b060c060403020f060709051e0301180c0e0a0501210501180f0b070305071b0c18050403080912 68
    0x22124042e2800e041c079440752a20079010700900d5408081905407492003410354030102041c41c1090140010720462104185e48019140740809404070300010768554060340040c02e41c440024000035281d565005001000c1c0e01c202c400b03a007102c0005024a042001d0b51007018003400b026101c0d040c4902d403aa540d281e4503540f84000780c1807801c150300b140620343d4030841240c0f000240f2800356002818a442e000e559440c0c1c02c40841c80350f0240384005a6401d01c5a0803200c201c030790052400007511000720075010106c1c51040145e802d5500d81e030343c401134091200e40c45d0741c64034800c184411141e4a40002c0d2140488060080450720707050600400480b14402c0007030322180f1216130505c5131482a4640107004100110200804494002c1e6007020f004000c0c1681039801c5c094502d80603241c0e035004e02213045070022140403011031903d0040100001c00e250180e64031500c10003030660710a40311100e240383c030054940d042c0905a1114204401c040e400383c20389800041c0380c4000c0c801a1200c82030882980500c03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 817819505 1250 817818255 817818271
    0xc0201020c07180216080a0f022404060f050117010f0504240b041b0809161e0e3d0b090619080106020d09030309211b0f0b12 55
    0x2014128540c0a161341100c04546444143c3c00c03403401c00c0e01d807104c0c0c5608076113030b0a4041600c401044800c1030001c50070100a220035107004081140b115844a6a000b001e04142d4455940320b26500c02c0031804e11a070360103410242000c29141140c030400b00d0035600c0012100368401d06100610001030f00360440c209680015a80014490342a540d0f030301e000b88003074084194400c0c100904898488542956011480403cbd500e409007907a079030b00ca69650301d400141d420004d8440c20820410070070091a410544002041c20064441d507031704001c021035105076080308500c10342c4940748003050b103000c03031400e004400c11401c140c0d001450b0009002016481c46113201c2000d0002e0700c0c10700740d51381d90300301c2e42d11203002018a0785401e41042c004051398000d005000141c4144020842e43e01d01880200301107035490703555802035a040c20a484112a0720226000c02c03094103a44c010002400300c07040c4110310030f80d5a00400b0072352400011100d454400d034060004000100003080b1558060030301d2a5121042c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 817820755 1250 817819505 817819529
    0x11a0603040812150a080703020d0803070909060e010905090f06061c0b010e0402031203010b031302010924080130050a020d0609030320091e0d030e040c0201020c07 72
    0x1c90900041e0340c861459058402d2a0850411000f015002d280c1a5003c106440c003141d0f0036120200307299182103e0002941c010b0700100036000142000d0015640044540b521822a680d5400322000381d070030940000e80303101c8900c3d006101c2c1d00003d110b019480060480108a6802e1031030035240c813000c0c003500f440c1c0200b43c40301031520302c02d003a03000340404c0d19171008919209603501c14401e08803800c180c1c0c040340301f4092840302c80004941002501d050f285031b1101186141c40300011049200c00c02c81040741442100300c00026880951101507500b040d0014004a40e2840c2d001c0041030341c00b0507006060a902603804031404008845408032030b40410039407450410100d414420710b4003141010003503112041c407070800c042001c250840c01c85580b00340c030140030701c0840404120210503110b106600b5040140103170b200c1d52030400c989020640c20250a0181c5242010110321042e4110f9415808100340340c04a0340103092912406446840304d00c000c50401c0d0a100e240d079207030500b40c881c0720b010742da07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 817822005 1250 817820755 817820761
    0x110117070c050f15040218011a0702210a14062206020408010624020312041506030206030a0c020f030304170a02030d091a10240e030d0804050d02011a0603 68
    0x2e041280801442030641151410703654240b004000340e074200d6040b07019280000030307a180440c14600c20b5058071120100300768502d03980b0007070240c15001481c090364842014111250300c4400c24956081d02a50341d4040c02000c00320307041500800d000700c0c0b61514140d0101d002c200301003510711041c05810b0f0307a208a841c210105814644007a0080e41c22204855103070450001c1c0400c40c1d607401d40c130760900180442d03150b59800601a40c40b40034540c20007001a01003400240040d2403c50000c1d480704079820002000c0d034880e000708010341c10464154801d1507030b60fa0b144c0d9100d601002049051804500218518603080d92240c50b03c0071584450007c50360b002ca18002864001d000740c0c0c040000060080000c80154202401c805c0501000e60541c8104140440d0b0740c240c501000100342c400300888102c80d840c0c015800003004441e003840c0010403003400c0b9080c4441d0340910440e00388640720356440e0000d040ca401c02c142424070050208003568549801400c944010900381050b40304d007200c40310b880359 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 817823255 1250 817822005 817822013
    0x705090117011b0207060f030b06030a0c0309060906050603070f140f0102240109050c09031c05040b04030b0105031e2a130e0c01050f04050402070c08030c0307110117070c 75
    0x300700a804070f8a0035103408480c6100b980082c2020481d41d641d81c41e509240138420056080fa441644010f410490800000704100d406410112a024591600051965031138461001311031121004030307a0705445800f407144c03d10f4104441c001802d00c024520f80c00d00d1606044011405100e0101401124000600300c69603000b8020707403007151007211201519400d050010000329a007402035001803450100801c2100100c101070302e40a11000d4000c02d094841000100a031082c031101000400030108000301d007003004000a040210302c00d0f210f810480d410030341018209140032590500030b250b000308420a031080021910810303c4219600411035201c0301d0307690903600170700703d03519001001641004c031076240c0c40e44280111950307442660162400300d80111646d01c07c62240d00001c2d0401d100c14400c40c40d081d0f000b011a0b61003445185015a5510651425504850781d0310015410116103c4180305000a00c00f06c3c1e0038007480c048800c1c00c4040c114402464010741180c00700065502503030200 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 817824505 1250 817823255 817823261
    0x160506120c16050a0c230103110d0c210207170a261b0c0a061d1603060f1407030c021204082d060f150a031112070509011701 55
    0x6503110000410b085203040c2011036035841400c400716107541642c0e6000030140c1d4008202c0b240082180d40b9194170003524401140504020000e102c0113040c108548108405136208101158000783c4804001b85030001544e1482101c0c1c4884065041c01004100002045000e4050f14050b080b548641c580010034012607111290089e45106507548100d01d15007101c0848800744604101108881d01040301d6440c2c04075401341c0c94280015a00168024000803070700c0e00032481c1441c0a006d4407680074540020b080c5030040342c40c51003401884054080c02440040d0065145604a00c3c3c1c0500c01c03d043d401030740c11030101c02030504c0c082640e101310301d070708061080c48940d82c0d251840c0009902c40361603030041903d80b18900309020206c2544400c03c0c11450313880ca045400d100750000900816a906c1c16440a6070b00d0080c441c4c4000da0013a0740104450751100140f2001c0c41c00784000601070b090100520009107000130340780b00c2e55485880c0c20006617940554641c199003103d8964504191100019405 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 817825755 1250 817824505 817824517
    0x703170408010501030f02040c090602030316140f1b07051003020c0a060525021c0e030a0501021201140415031203020f07060506042304111201050711160506120c 71
    0x29075402e0500000031b11810720541131059000b102c0410000954a90943e15034035107200703682c0035800600c00100e02d030130b00441c040c1843d082c0d81090300308028074001d03510302a07102020041101201003840d101c1c084520400c80140c0b10104001e104141c00d260001e519141040c080808164000a550384441c0081c00080d403140d030700641c06d106a0518940980214200c0b0741c100400080454808030240c0c03000602c0407104d6040050030b8502c0740410f0040f0340404c03440e020240c142c8a007690a10005600b4401026540a460700740b5a80754101288400c44001012000d403040f414a10351e1501040000540001ca83e40312039038041054406070140d02a010310140c0c002e08545c04908034060043d40d410042c0701c0d0794200e0f420803070407190200203a0204100c3c207582d80c10881010000340094140c40201d4040c15009040302c40740c86018600c1400c2d11000c413444070010300002e0316a81140810450352800c01704580150400030304207408a510f03400764800300c0002c1c10341140032540f004000f008440e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 817827005 1250 817825755 817825769
    0x14040b040f0804090e07081c050909060d021903110d05030a0e0103060b040e150d0f0b090a0606030f05060117100f020c030a0203032a031f2606010b04060207031704 72
    0x3003030301040085621b40e0403510845c2010700480920001d001441c00c0006030402c0140ca81ea4208000b4038140440844c4c000e00060f00034513000f81600c00b50343e8404804034951030092225a48508514040010039070200b00c2d98001c24509580d4400a040030041d43d1003011180f80601c03c030140000100c010704016440b07152500070010380811503003506122603104a95200e004050140684144641c10409000141c00805400d8840e000102c60050103900030788486c01320762604040d900ca800403103610b43d0044440400c019141420410300340130050040844545403410109040b00700303926441c0213603c070003600f90b41344002c4210007071940c10345440c108042c0c100d175107410110f04065a65403081e2480008e040d01d03020a501000c05010710407885040b150145070940d1600c0f403c15002440306514491210000780010503080b02400c02100705018407680d03903c880008805090500e20180c00c40d0001c040204814005a50001344900c21284c1c002c80e5816000c2c2c00b040c06070307098081d64000346 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 817828255 1250 817827005 817827011
    0x2120f03070c2414100b0a020106031e050f06040206090411070c060e150f12070509090a061403030909040b041a07020304030309090510090e010207020a1814040b040f080409 76
    0x203002119008054032007943c076114104014414000b00c15005001100c20715036183d1440c5041c002c5011200280c052070006000105401c0e803240e0360484824a611050245c5545031041036003800000c00c00003115811210140c030071800c240c0c001c15a01c0c41082c034458001c42e00c40c2c501c0102c000d00c180c21526100d400031503a01503107481c1d2800074203443d90805054131405e0485d941a001000d4403080b1428240700560551800280c01021501c0070f8004003104284a4180444151921010703141481201582800564036040c1441e88060899485104d4000e81c818091350004c0d03244c02d902181c01981150040c11030799102d2a050f90b11300c03810500e080b030386031000c8240420341c0c0d0000050800d61340309848110189803140c4000e070440d00300301c44910b20000a00d60401a410b5950301c608190402400003621307024454010031001c040d1035000001003892868070f646581d4041c81080c02080d03400c544403070981019143c45400310005007000d0400d106d5805644200310812046030000c003071000040c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 817829505 1250 817828255 817828283
    0x90a140d2003120903121201030b060f060d0618150e04050c0616020102060a0905030912010e030403051005090c10030c030b041103040b070503130f050a02090c0c010c02120f03070c 79
    0x203c1c816800c078a0113980030b88170791080b02c1c0c40000b8000035984607042000c280d0344540c1c41d64454600700c5d8005080c4580184240022400a45404000301000e046040c0c0c040303121441d021301c440c0e003200c10448010308545031024480c035450440114a086a1090051303a42c2034640341405810185800c10460340140b0000e900309483d640c03400700990042c000d80a641c410b40e40d0b0303210350003a00c2c0811401400c42c2c2082004410780c0c0f07040b100b0b00c01c5121a40f0000115148140003040ca0b551082d003058451364085100441c0d154120300035168007400c08005481107129007008141c01c91102441d01d0141500c1c0e0580c1c0e28500d120707a110296070a0018024030040000e440e010042742c0c81a9010303140310182031f00181d01503000740c048902030100e461014610038002d0311044807032494004100d51600030307a007031000582e0b524074086003e04484148140d1304c4200160003801c60717805070304c8103003590080d440d0b0148024244080c2c1d0324055103020b4143c2d036a65820002c466690300c4220080c62146c0b00401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 817830755 1250 817829505 817829533
    0xb03150108150a0e18030f0d0c0c1202010b040f090f0f0f06110a1b02210109050706020d181d090a060c02010e1006050d0320030f090a140d2003 63
    0x400c40c06a80c0c0c00c0400340105000400303c80d02c6c2e11a20002c500ca040041015000704c102641c40503003010514900207032008001d64440303409041082c03002005079114102004541f61500c01c07034072021002e542c00c2100401d05d55409030f0040f030020300981030a800100000912080d0040d5450300c40c4d0001080102d1411400501d60750b4002c0f5a501001409049620900040d0f480701d500905800903c440160784845d00451140c2c0d910300c4d61801d90707540741e100d03d00005a0411a04000d4511a009404400540600180a0303810340407440c060005d0305204000e032409007d04100c2c1d40350403609400840d5107803205d8070728007884540000c229030701e021503602103640d040d40a40c1c11151424103940b14400b1b012240380a650341c070b0040c240e011580c200340100203802a240601048a80140007070609503401c07030103040d600070442e5403a4000e030010f82c1038103a29043c0b0740b010103032028124074041c4140c004085040706003180301c001d001c0001001c91020f00c3c02c0003403a15003008802021111721518041d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 817832005 1250 817830755 817830779
    0x1f0203040311060705150910020409090b1612111c0623060f0a0908070f08060c0c0d210612060605030f0a110f0603041a010b03150108150a 61
    0x700039070340c1001d1182c4200d86403030544111001c5a8101004015183c8800c00911007080003a040e0481c03441000001e01e2090010300150004000070040064505502c0c00c04d4644e00800601000302000d812101042c078642000f46c0b04c07011803800800095544801a4039402d40c030035000140c0840000140c1d03a45184100e41046041c0e50034020b072444402c01200d8500840002240c000307501c140c09104980141c030b042000b40080320190325084006946d900d4500c1d04004894005c1041c0c2c020501041c01404410802c00b90800505132266180901c0c2080694403059620025010082c0740018190101c03c8407002025080011200b003040e15035400c3d00c4242070320007100c1101d4240c02d1240020b6907107000b164000c0d0000c025009880001e800e60b40709070084c0b000b5a00d070344c1e000c19020950741c0640ca0f08009540310f00d204122b40740c82d99040d40301e46440309505a1000d900c40c1810020800702141c800c030301c603600c1403003828001c2468695250042c00d038076203180102c0d086142007100040602c1d41d44 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 817833255 1250 817832005 817832009
    0xe040203070b070b100b0a050708091f0c1703010e0103020d0c080118060605041a01050d0906050414011401150c03021005090d08070c03230d1409190b01141f020304 72
    0x85c00282d100c030b60b039400c400140d008054820002c03403000c0c030645000c130700321400900c04a40020155800c90030b0380c140d01d80602e6100b810041c001039040e840352003000121030003d0741400340049528110761401c9010501030005000007400303214011760580c100100c1c0d0300060040c1515000070b201c04070000c80a030360a00c43c030040640e2258102140001e0364140751155144144000d20350b80c16407a5082c0040d03d42e540844001590030b0365800540020a40354445c003030184d4890a00d14041424510240782902c00301399090040401e40e000401444242c05101caa400d02c240c28143c803008000d0809034100302d41e0480b903980d1581044200052441e01082040c0045547c0e2680c0c031213901c42c50001c807204140c0000007130100d129407045502e8100c0b05040a40d0494018820618042d4102c01003030aa840f89448062103511a405009500406118541c1d41c2e00d29414140159119a06e42c0c00254006103d918098440c0010340d0219840d2009002070b5040d592a84d144540c4019000039920342c000c6c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 817834505 1250 817833255 817833271
    0x115080c0f0d170306011e03020301030605010b1201150c060501080a02041104060c020d020d060f140601170a020306010315030302030a1e0e041104090603060e12090a0e040203070b070b 81
    0x18101204945441c0d0108094107403c8410990165810302007094107078406441141032103e01d5144401000c0750030b41c5c030f0710101040e980c09a1603500d940341034000d586041c2c101303110f000414024550307020410f400481c1140c941103842580140707119030668824001c00c0001e01204c1c10400007103029039000891400140c403e5800b00a01c150346021061107000740d002e49000990210711040252424201401002c5d0000741413602090341130740d4040845a501035403484445e1078041c0880b13440519110254403c00c2820964007140350040551311801e0001d225203c4140d010002c00d101c1e0f480b0703030720100401c181580440d00c0184c0340e0034040c0d42c80d00022220b000142d540c14140f45a40382c4420b034807007850700030384660b00115005010040607007104228140b41081c184400209004107000d02c100541c00741800107604d03030100b64600d04003a5486d0a1650880042080300034580300da041d481e00311507d041119000b0f48551000a003090b6060b4004100036101062a00c24402c0080c4414014601 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 817835755 1250 817834505 817834519
    0x2d0206031f180207150513030804020303190216050109260114130b07031e050703111605190b0c0a1e2708030414041b0206090d18170115080c 62
    0xb005c2185007a204210303001d0656a8040782480002170003840d80542261008066a04200080812010380e822000301100103074082000460110b0744507040340007418003841c1c594416410f0400c0010382c444070520507841250320220046004800b03502c0122010f01c0c100c0c200d500d60804149410391a80050010b80e03603000300502140e1464027910540c9200310f8448600011007010b0301001000f4000144220103040e02d0b0b0200e410403084503401070100d03601448503400100c4030b0b810b00c0d51800785080e03c8200701038000907400b00400c2d200c84032140d00ca150300055555030045140100c925840300554842e409401c014030188058006a40b10b00f101c04180382958080301404010301c00141c148211105034104010600049a440c603507216030000282002c69030000c0704000301c5210050f1446540143c001d04180010503800303000890901e00140391469009200d40000c02101c40103106000c1c81c0c2001c51a0507140020a400021003214001c0c0310040c103942d1038400c681c41e980e182840d2441541 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 817837005 1250 817835755 817835783
    0x20303061503040b010302131b020303070f030e06010b1b010504030e04050a0506010c02100c0c090504030216030507060c032c0301050717160207080a2d0206031f180207 74
    0x300400c1543d00c1290840301d0014540d1031074003803244800079001e020704519101c44c5199140a04040c400100c4107041d4019940ca2030304810003440f0061a030464001c044c102000103408038000910a81521400c0304290780e5181ca0071030311000e960044e1603212065082c40200f01c141608515003403820710080c4c80a00c4640d40703401c0c00030111807049501310b0101c7c0c6070283ca0005820000c511442030b4006080010244161b6100d0000d212201c1d8050048191608100020594188544800308903a58a11141c81d81135a50302611400c05010310b01c1006403200c0c000040c0742c4588840301003104a03204504035003540301c02d9600440d040912060096080074041181688518440c04502842900c4084292581d13894412503095160340e1504502c0707411000b0951032000c0c05040c03840342c8034108e1025140720811710b01c224410110340d40d00c0751352900c0b071f140b40158641c40c007100c1c1e00800000072101c07410900707041c0e1308002c6160380080c49a18608001622408a1a1300600c1e043e07018110302020380d9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 817838255 1250 817837005 817837039
    0x2030415020a1e12030f020903011a03010b04140c031909080706110f07020f0607120801030b061c060506030a0c1d130c0b0a0201020708070b070810030506010b0c0c06070302030306 79
    0x2d0302d020f41c01440900f10400140c041e0b4400c0d4030000140301007090152502d00f031100003d0075603800c6524403801c11a43e180c0012540b60901c40d9003400103054806104010040344c01d42071030b030801020340300741001c0007001482d01c04034004903d2940205000401420545013040d80e16034001ca0030403524989803030040344052001c4d03410f40c1c201c010001d404515140e029802d100c101800070f00010b82180c4184021400074142c00b03519000c0400075601d40b1f24039855410024110517000d800c1d580034600e1b01c0c20f0a106c284001042c44d010716003104010440c0c2d19140b000c41d180c502d5510010700b0a8032115404039804034a4401850001040404000c00b41c4981080344008030103070000404800120b40700b040001d035044058400c40646000042c1048080c0d114004598080e80c2c044a00060319001c001065811042c101d170854240550426140c1c01c540e00e581d9510418015501d4280000c9000c00012104200f0314000200190000741c48203680d18000e0f5984d002030310001e12504c0f1094069840c0c1e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 817839505 1250 817838255 817838303
    0x15020d060f030221060109020a0e090a1512080a030c1106070306080c0405150904022b03080a0e0a0308060a050d061406011115071e0e030d020a0c1502030415020a 71
    0x481340200240001d64a8445884003d5204507143c505024400c81461180d9880d424828400d010150012840c1e014034003444c2a286450740010700018081034140000c10100fa003510a49a40d07800c001619044a200550701c41c4400072199440f0301c01c176402c0080e0207a06800030b004841c40c1c14100c130a01c1c0f03a0f02082006031081182c220741000d05403011001c0910b045402143c00c5400507250118558183d040013050101d059017070540c90300503541034801c0560080d24594071400204040010b45000412141c55a0301610701a04003c581d102180040e6a114001c20003880700130034215601d1403a15101000c0c03c1041c9c0130104e907201e1000001d0315940603000b91654000c180300a44440700c5240d42200045074050708502c20010300403000007000341d0f515095801388080f0b4684c42c2001024108241c80c0020b100f0118046402c21464280050070705040b403000e0341d100c0c01c2c0000d024a80150102c0c5140101d0744085000c0c0a07400d02c4016480e000708902204078043c40d02e43c48912060407000d070726 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 817840755 1250 817839505 817839559
    0xf0902100e091f0b0408010b091501050d05180109050114090a0302071707031211101118060702030109120f0302040605041e1502100b0d0f15020d060f0302 68
    0x40003581c00201c201242015081c0c0f0300f1025000000402e07200e039070741d02c0c845c1c1258004502c26952620030034807501d05850159440003591a0900020711084002030403070007261041d4564503119404515503501402c2e0000c8501881c0000300001c0c40030b810030380c0c0681a4440c0114020110384041111a2000300b40342d003220360107800070500706141101803100896860b0b10740c81c05000305240800012121000c0e44c14541656031140744000300e00312164101600b100550b1309040c13030706070441c1e0303450325100030348080461280311030307a400802130080780742c0d442800d800075415441c0c02d592000b00500340c108500001c107582e543c541e403c0707400142941244582d002e500003113174080c8030400c00c14823900e04581580030382c00c03e8042e91655030721110304040d8072500b007100540c221800310403048640e8400c0801c0d0031011502d8081c03c0303540f900c0d07440703040c40c0c840c1001d41410b210344141603c2a506804854024040b2078041040ca0b81e22141c81203882c04500089118420360380000000070009002010303 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 817842005 1250 817840755 817840759
    0x5040c230c1e010b0d0b0702010b0a1809020d081204051002030f0f040519030801051c11090403050c160302090a0b03060106111501080f0106150210110d0f0902100e 72
    0x400c03034040e8003222038000021102d94141d6485070307094441c0e9290012100401c502c02c02e40b064007818030240107400c0d00c540c210043c0c0507012001041006001851800d9100b0103c1d0b580000c00303858070300110780850142c9001131b103000b00000d140050b6800c10b900c0c06206d140610140c0780880052600d00c03090b44429207003d100c5003181400b02e81a0444c2c0000e140c0c11a218400310381c006581604c000072401c2401c0019008100b0701d60040150741040240c4c540059602e41031a800f03001503543d542800b00d22003100c00d001c1c501840c0080d0405001c0c100b156102c1440d01c0072100780c41512142c85d1416102030004900802c190400f00354200d840340240d02d040030f0000c0203094907a0038210101c0d001410f0800d01d41d000e205881c0e07c25102c00d41c10446c107001e005c200d8040d000e91401c0550381429a94540c0c084002c00400b642000951680400e02c20340906c00800007065803000712540e407065000b000c24104017985800d04085250800d070348800419442681c0125102101d001c2c145d506803001824a5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 817843255 1250 817842005 817842013
    0xc0a0b0106080c0315040209031c1d0102122212030f0302040308091e0d1a0105120d03020f1c0f0b0907090e06030109050607090f150f110705040c230c 66
    0x14000c00816031512160000240c4014280384007230340000d25002e0f604240c401040b403020081012950300c1507004131001c045500310015a441074000035a1000c1d0002a41090000828161200c0c600c50030308641e5460f000411204050b00d54400c0442030102203011400b04809154403400e0718028000d80d011aa00400b4142c100301c004000e101142410014940780154406440c100c03907a55040b102030024095149481c4407005401041e04415041e085140f048190440032340200d140012506000c400614001d61260308846503132000740240780c00305000150902822000914550140100f180f030981c05108000c1001e0900101c80e074191800400070307002c030b80d080c4400c1a0820680e504804040d000003445042505d5243c1081421b9030360100091112000700401c00b0319440032005032400314a04151000341c0c8201034481c503465001d040901800804103114602c09101d0034000b402c018109000d5042c10402c01000c034005004041c1c2d0000c056442e0307001c03100d030310010b9844c4205900010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 817844505 1250 817843255 817843261
    0x108061f0b0c010623130902030616110114091603020604060f0c060507030203011802031003111206010803090414060a05090c0c1c030e011509021e0c0a0b0106080c03 73
    0x305010341d101282c492880c1d920340b200001c80e007904159513000240380d0f11702c0b0800015420100705002d02d202200103040340c2410b01c4a0f0140c1c0d004504160400d62204004c0d0300564011810740d1685031000001c1d00651a280c51085c3c80d070700e40324074540701d401c803d030941741c00c003c004944c1c0700d181049000c003070741119080c01b06001c0d05000da4100e4042407140c0c28100d1000040e41d4420301a20070894403200000e1b0088010405618404025a02095008015400d40c0382010301c443d907211052202070070129060380b00d0138498480001c100c4c220b4103401c05032101980c590340030545d07aa21134604280214600f4410140e060060580d050040d0402407191102c20b141808010004030301520030461008104401407800b001009a00c8824510681c1903051940d0781c1360240071a01282022862a410300c182c44502c0c078101c3e000481940c11561005032501c519040b130740462001040046100c1c0c4001945000807100020820f140c0c9201e044400c0d080c1e0780b180d0044540c59000d640403404883c00b4804 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 817845755 1250 817844505 817844519
    0x120c030804060209131a03073002010519020d09060f091211030a030804020f090105060a0c051903020604021338210114130312150e0108061f 62
    0x10308030054000e020b2064038040c3c0804008580386c0307130746084504480030803200690600740000402045041d02c2960607501004120b00000824980c81e401c0c0d2205c949024116809101030701d5103922180b0030380c40e5040d003030440a581c50800340c0c848000301d1746541000412502c075102003803103110166500b00495180c040d12218407100b01200700c80c900da0501c00c0800c40e450401c0b64140960003540c54080f5400c090041c0503110500c0c20540e40548400001407019884020480d00c00244c140303440c0c05070b00801d003000750608108514902c1e007000010509014541c2c00a0301078000e900803070700c2288441102c0341c8181224404006100107092581e10280725047e42c2d6048091101c1c502d82c1c000e404402d90300020400d101c41280d04c4e0510b40030210804c42c0c86424400d2106108000340c0d0210a0705140b01071441c25605800010200a800301c100e0320404060b400c0034205038101e409004025850710040c80500c607090240d20881c1c840e060001c1d40401a20840c1c0c0181104031040134a29428030315 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 817847005 1250 817845755 817845757
    0x10b0d141618051906030c170c0307030605040203150f03071401051608030709091d03030612030c010e011d0a020a03020d1b140102120f04140a03050a03030504120c0308040602 77
    0x1020704490415030000181a881301c0c40c0d14008551100000c00c0b5982c1840000350845108211010070065039040f0503840c035181c0344805401110f040100e0780c41e9520b2840c210301400c81e5410041d00706001105100d0000c407402c5207100c8540e01141c0851020031250141035582c0c5a41c850340c0300b40d42c8034008444a95000340000c055029000d4060462000c0130740300c00724142e20035a44500000d2915508200900984c0728030021105000041042c800c42c0c504415524000908154460707000c504a22a40e03444c00c00c200c0c3c854681c000000d12840a0342c40200b03000307003d000ca10161800d802441c80100010103d0514110781d4020696110542103400b4403250410141d011030710210240b81c6116904891010304008000c034140e030f03241907007118000a00340100c0a00c0c0d0a8001c4052102c80001c21000080d6401e9848501048441a4250740001c500b602e060340301400307a014840d120b10500d50b00d5040944103500070b10480d08502d0180c0002c5851003400c142c040c0001e0b1101c000b040000341d00390 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 817848255 1250 817847005 817847027
    0x106050c1009050a0b01050301200a020a0506010f050a150804030503040206070209130203100608060114182a030103020d122003031b03101503060905010b0d1416 71
    0xd0441c1e0301c1c0241034403020100c4010700e505581503848020004d0030800d40b0307107406016080950007480701c541040941c120034200d022001407514404940c2c40d00040c070800c1085a681d421500321361081d60754102008452a4a0084900415904030040380c00358000c0c5c6040702d400718540e00c1d5800c80c1ea80b0f8030100c80541000d081243e20890400040015a0301d04018034002c2c80030744901c200c004a01d1042503d003c0c0540c0e0003d01d243e08040c002c0000d01d0003c1041c0b411181e01440b605100e0348a100000e003910541e080016003c0021030a1140c0300d02c000c5410b803203558000c809034110103c00642c44080b8002440000d6003c0040c1c022134000130403203503d0030043d1505040900780010107d5000c28400c0d140b0390640419071020003005060341c0e00e4101081541c036031704040352a60130010410b00401d00c15011303461604454082045003030b13101c2d40c002402410300301c80400083d615421444145d0303000010030f01205051220441c03010b440a9029401020700d40440007605011180c1510b03030752102 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 817849505 1250 817848255 817848277
    0x31d030a23090307090f06051002100b10090303080c070b0c030a0b06032712190e1e060717030c0901020606221d0102070b09070b0c06010902090319080c10020c06010605 74
    0x140c90015260725003927904143d46001341c000d070080b0702e0800040c10488103035510040c820341030012112002500858004180c80e0549010079442d96098400e001d5445040130041c40c00030300a0811014070003200281d40144110a0140411114001085528002500d454150f58400c8620002c2d0b18084603d0850540c00182540c1031250480352400990b089810020180b034508904042031641c800b608190440c0c08450040c43c1c203075450014007820004007407090080b80001a050103001d07107141c041591442491701e444e687e141c120072108958000005960261044001007411450100200300a0300b840c0c4001c0002c41c407031815500003900741c050288000c0340e4400d0010415a07400c0c002010018014a00800c182c2807080d581803410f0350310303406251640810b2058058110021602c6411600ca525016072a403440000080c1480b011040040d602c1d940c8c1200d0004018544010304180990b0394140c0301d10480202c0d40d101a441840d03811342e0950403440041c03092901480251001541d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 817850755 1250 817849505 817849511
    0x1b0525060b1009050f0405090c151303210f0c031b051603120c05060c2b0f0c2d170f060901090209030c01031d030a23090307090f 57
    0x104080b8207504000b40c0318800240384010180854103010b80c400180d01401d4404015a180c0780360401e4407250b80c00c090798455490700218081450082c0c040d200f030b05000784040e4000135901d182103198100d0140c180d8030220014408178020b20300424010110341c030079444000d0440c0296800b100d44403a460400400e05851219090109800300036903d183c03a5100f480c9000503046003884a069441c54441030104010401d096002440108500713030003014500001d40c0ba81c66803240c072070000b45040d81d02c1ca55240c080200c0303030202e00d1640085ea0280d43d81181040480106070084500002d40c10718a0800052007015041d01070166100380c440126900c0c14110b80d040e80b2040450041c03003910050310707030307210103082c01003528200fa2814010003200d6801c500d491600b02c0803d03281c0d41010400d50600d9640d010300b41004040c504c80d18448043d007029250780300b03d5001d01408a60b0032407085044802203002609101003240d003100c91100c8000c000700342851815092501525010011403900d41d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 817852005 1250 817850755 817850771
    0x50708070c0c0f06110c0316060c0602090d050102090a051203301f0f0501120903090e1906051203070b150310141b0f090319061b052506 60
    0x800369140806810191780c0c22102d180c00080035460210180c2c4640e1103a08007c8101c6001e64a80403d1421100c280c240224106040e003040c00090180190749500512480c0003442000410b40c000c003000202200d090807890f88071801e001d02e0000c281145e400702e80c400c00034040b001215000707403596040c944a2410840007520010460f40c441503802c40100040510100e24450340350301098050501a165080340e90f203800e000806200c03110400c1015155205809014507200d61020380241040c10070352031203400c002e507500003182d441c400d0140e481e514003403011071949442c803420095070340c1041c003c50400303080740c50311045000c0290408004988803901428652024468034001c1c1c00d40900c001071300b14506400c41c0c26080c0041c211040a5844c8810215008154081d03035103c08014580c1034440c48130341e0100f032400701c45c030b282c6040c0703000408801010071149801140d2580d2103409482c0d04020003510558550040e00322640040f41003003a480c0c0e4042280c24203260079400b900300890111 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 817853255 1250 817852005 817852019
    0x114040e031e0702100305190903020c031b03100b061909080a081206090610032705030301030203240a051302121612020f15070519110103050708070c0c 67
    0x402d040e011001103900119101055180c080b000207410f0440342001d00451900c9895010101030000201c480940c1e640c0c004402d140c402c011900d030b0498090103d4900d40f0300803130003484a00d5001040c5d0300c248036101100c070000c4500e000380702403035034060b008900300f103800c00b0403a44d420300d40c600c484100070203401d002521400402880714101d02030b4101d19a41c07241e082000c030748100e00a10442c012420364041c001315031034101c01c040714652945000180486c2020001901c50844000c40c0d207600307940c0349031909120b0048000c5049a100b01c04568507039100301900314241002c010912044012140020700c40c4a01d9000342d940500141d981d143ea42040350300088151401c0b50800c1c021768044041c503602d5105040081b400351040d41400120600958002603a85a46041c141c0c0986094820030a00000f243c0070f8840266004d02a101a2406c2c542074881118042030700740e444003020440030f1420350181c840d89002e00d28503510414190b5031644203441b04040d24070102c032003405915001a40f4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 817854505 1250 817853255 817853287
    0xf0e130c0e090613020102031c0f0c1d01020705090c030703180503091002031e0d09210f0504210201022508150f1b04030f0c0501030f050114040e03 65
    0x5805030380720108940c2803050765030740381000041c44140804150115480540e800200342c072821140070340002e80c1100450103040181802c0582521018144041122036903003104014142d01140e400aa85124805c1c00490390342c8050310449811201031804a4001d41c81c1000560b4011070034140820b401440141c3c4900c0703410140d4041d5019040464210040d250105035203402c001544025401e00d5440b01400c503151452001c004000f00700090020000700d0150031000c0e185400c9490780e1166500d80b44070f1614200c103001420b00249141c08030340030f6240200281d0b8191081001800c80350894084800d0782000400e0301641580300303115444d98441d8805034800142900c10129500d010320b05410f040c5010111292000445d507090108490420400c00c0030b50701c030051004440c102001d2242ea000d00e40310300d41003c4c0503040441c51042c1030140e4414503c040300d400382e0342080140d0707900b0450390486600f07002c0d460303044120072520050344c0f410380c10078103144480c00d0a032403400c51007000c602a2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 817855755 1250 817854505 817854509
    0x50a0305040503010f06182c0717010c050403021302070b1501110a0f020103150b1909050f030c0f040f02070501051608070915031b02011d070f0e130c 66
    0x840014051016040a020399121100407100074030085040c4500c250700041107000c125940d60391402328800002c00e083d0140c45802801e02c4040d0607800120505488807458020a180c44c01c00d04080c20080d00305100b5500d0603207459403014181810340e801c00203145800202d041ca059009e0203200701043c030810310a07000e03814898620384040d030714000140800c2002c450345000758200001c0c0d035002c1254007c03000d48181c1e09207800111115040b00c00150741c0c1d843e421415002e980030401958029885650109400c485e84904001c0d0b561001000214094608003a0b0143c200e10207510040c00e028483c2c50f090383c4014008902c00582c001c85404030b070030086003903545a44900522043c1540d006d00b540e01d140003840c2c101851b00e400940584150b20920503c13860080c02c1c20000e417110701c2580120040707001d000f82c1407489268010000e000e004050000d12944030801010080e945002490f00200c850386580c441d00c2901c1c00b05000070400303005240e06003800070500d8401c00620003042c5000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 817857005 1250 817855755 817855757
    0x4080f0310061d0f1225051806030d080a02040b16022119110d0f0c0816060309020613031b08030301030f02040203130501060803040503120406090b0c0a050a03 70
    0x7189860701000401c0d82c04103a05140f10603208541c008515260254607004007002505c002e9a002d0007204000c4c6002c82070b56065000341004034207000c8140d014644541100d504031200001c140100b0044001b0407815140c00781c0c0750744075292002d140c1e8000c03001c0c42d078010024034005050643d110100400341d400044000c601041300461305003185814000c0c1c4d102c00c103460170800b446161120001d035454880c900c104450b00200003107601003015071046500c10010240810303070282c0040c6080c03034031600040c004a0b00c0842e40e10001c11050390025401070750006001021582a28001003a0000d00b00420146c1c1c020004008800390080c090207884002d40c411180608100e014100c91105481281c1140c22582c00800c01000801e000100d41407803203404440041c0d5035141c45032030103250301d00200003c001e5405c140c800500000e0220103030084800c2903082d6000010042001d80311031040b402090301080340c81c2c070103010103801203002d441a840c0b0311003240c1050041e52596071610f4100e50040b4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 817858255 1250 817857005 817857031
    0xa11120d0e01050c04050d080d06030614150405090c19050325120309060f170117010b06042105030706020c06311104060b04150e0312070b04080f03 65
    0x2480441c024402c29a024121600a44c03d2508100002d8045a0b2803580503000c03d00105141902d1605540200c005640c011008c010f101c010b06482d9400c04011600940d00150101d20700318a81040d00520780324924840140440c43e280c002003114070040c0007581c0302c2c124541000400c40707444c00c22448015036850f984200340003140c400030244070481d0380c0051a2040510140d18000381c1c00c4115001070310300d9806c0407180749814031380440d1114030b51441110f03910202740000442151a95a001c1044110402804103000300c0c1e041c8840381c4518419005082e44424002030406c07031495012240d244640140c07880d10710030351120002e036003000c6003402c081c1d0018024071100060100d03c0040d0700b5031000078130303a41e00d0f02803505005161440074082c00f0211004400740d0a0b903a55400b01001d40070842555451310744802d4500446000001800085002090178581620300080e4404000280c21382d0f0515080300c2e555940c40301a0042c104841004050104a12404c20070010f1441281540010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 817859505 1250 817858255 817858271
    0xc0b0d0b0f4009051e0d0c150e0a03080a050c0408030403020622090606080f09100b04110a0e090105061201030312020d1d0d0f0212180319050c060f0a11120d 69
    0x70b810304140d0300a10301c046501c46c1800550719034000c3d07651054a40c04c4982c011040c1c0e4400700c2d440c06000c10201280fa00e004114052040641080f00c950040103c29020440b903502c07210701e2a00c3c4d01c0b1710300403207450b68414003041006140040c0140301c48005a280301a140e14829120040c40230a604080c0781d40f0784841c418444503130f00c044141d9001498090a0426040403800d41d61a245070300d42005d4415241e04c800003094035a0b030400207241262100d290340e1412134480042c2061444d0740b02a12a900580c00000c04d482c240081d10b401090049131f11205918542e8283c800310203000305a81116000d12030300741898000d1140d41036a07590703107000d8200958050485c5040550700304451041c00010100320540c0799000a500d4490300300c0e5498980d4074040030041c1d07a41c1c61003c44031964140f1031070b00034051040f038031070f440043d440c403441c2141c8580f14a141085140e0180d0101020301900c180a80101e031446448140c0c40a6410700c151144104040c40c3c0c40c0041e4040c0340c850403459140c00074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 817860755 1250 817859505 817859533
    0x15060806150108040309050d11031f050109060812070f150903030b03010e071401030615020c030d0206160c0807062409110a0c0c0b0d0b0f400905 64
    0x950701e201e80900e8090841c0c6402d64000d8107640b4240155030084c8130401e4201c0400101e010071302c2074420300900711044d880301011500540305040340303020050360408000045140e5140104815540780e0b2000e004455880c03002c1d1000307504242020f6851480c881403200c003041800c1020300e511a59018041001d2101d41005420b8a2503150058080d0703240ca0100748500101044900a40300004084011540b90341c004130003800d050341054000044560b441d800150300010504100203094041e55500c1151490590300c030b0000301d6070b001984041c403144603641d610440d00460204d20980006040424580f40d003801c48000c011422081c0c0450000c121011002d40c8004004003080c10b000d2180445c031a0a41044e8041d880100080c4a030360090316040015112013a000742420103865030322603140c0400741019204003000d450140101c1200755030503003818126000c501c0500701c04a0700c038642d003a00030100300c1d034410740c2190441c80d540c060000314481c1d40164211540168010320504c072203148 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 817862005 1250 817860755 817860781
    0x60f09100236030c01050c0c06030a1b092106060b0c06101406040504020306010c050a0b010609091a0112110f070c141509010c0b010308030a111e0715060806 69
    0x910040140b000030701c8080c41d660005403005100500f803800c0c03901c0724000401c0d2458005207034681c581c0090080200310301e4036002d611000130804801d00c00040424114002c1c1c2d52550f4600480c1d4003020411550a940082030940314030684c4194000602035588200070040c981100c0f1642a00f50407040500600b00c402102d5000a06546020182c0c9070341c0741c0c2e0000f04984601d00c1030074025900400000e285170300030301003a502643c20000b03840d1480364520344012100d00900404000c0768542c48007041c5d501d681c0c404d500f0340340c03d1450002c02c400c1d034a100540c2c0480e020203420103003580300e01e28510044070a001805001282240e459250040c030725202201c0840c40e04002c0da9407072400d000c008266142e8030409071624502d80c119503034152000049806d21003d00020b821160040000000c02c440e0100940c4200e920090403c24100c0c218019141889140000080c44106010f440e540c040d00200078010944900020107580c031217a110070054413155808800765801140030007030782e104228 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 817863255 1250 817862005 817862077
    0x606010e03030414091b0a020607030f05040b060d0c0b040b091201090b070c0c0302211606050405011d0d0c031203060b07061121011412060f091002 65
    0x4000e50f00782420814048451504100791911440c01000866000e42a1201c1d110100d65469411a50b507500034002035502c05080d5900000203140c07010411012209128030b5006942c0032445c0c0d005030f00e4010400c0345a0541030015100700425030b40010b801a41c240051004240701c0341c10584400082c010050a040995500c0f0700d640d04041d0840000b4401c2c1c0c18496200481c1c3c10100c2d8107810f10304110040d44000c1c1c0000350482c905041c01c1c02d8640c03003000c8810b00840038408a0b04660950911103102200e02d104403000b04c0c4040c401844590b0065043c0c0c1c01768461203002c00440456840080c002d04452502179819440025040c003c0c0458003140038288165401e040c00098501003d1350860720809101400442da500e444102d88011041280c1c1e1400401040c903c0c00d1400541d000c2d041c10080c85180400602c0b01d038000c506081c00c11810f03090300b003503801400c010307600d4416210081d04010040b09881c014441c110b000c0389418800340204891000d0901c10108076408000704001500d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 817864505 1250 817863255 817863259
    0xa0b0606122508010f0501052b021c090201080a0b010c0203010921021b0d0204090516140a0b0f0d090221072102040926180108040507060305091507020606010e 70
    0x10005000b4410001c00850803500c00f840e1141d070301c2050201d000306800c2652701030300c12011403010114658815402a1900202409016203050001c00803030040f54a8160000d02084980e0000b40310042d803980a181200c4041c10980000d6060b82d000038215080c0800031034840c51148502083c4240881a40420090700c1c0020100300c5c5840031512031700742c1488200c51107001031308158030854445420180c956a445001c0f206100b04500651b030042d0054000c41c604240301450024080c50400312101c2158400140c040c84c05001c0d1f90040c1450b44034840740e4103800c0d1682c219000503202d1a00c0381070314110101e000c1d442541148205818081264003148050300364222403001000030240001d0001d50403240000c1107900c502d040c6405120080c0541e1b09500351060b0303113500c1c80010004140e212105a10603812021100041d070f81105e0a0702d001c0d00a40c081c070018020a40280e10017904011000d04031b540046030b24007210007000041300c070000140c00c5902802a6540c006011107880001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 817865755 1250 817864505 817864517
    0x5010f0c0308071e091e060816050d05010b070203151302060c0f030c030c01051608010b18060d14010503033c0a030617150c0d1104350a0b06061225 65
    0x130342403002300703881c00292803001c2c003801c500608080307140568120382d600102c0c0c1206116a40c0d4034820005250002d50050380a8001c3d8010b01c0e840d00034992816101710178020010002c0b06561f001d002050f000300701481c045100d81c01d88a0124072040024041d80a41600110b5540001d04107585c00e5071806420600105807006c80810040d07000031300c250660750102702c02915403284540441d00001e81184458103c14002060b41c018046a004401c142d007c0900f106180d9aa44090559174401c2e007660400c5940c00503284170003109130f5990805a0082c0c1d00d0342113040c046080b1f401c641c81e4004090040443c0d5141c2d0704100684d107806404401c000a80050f114401581c0000726001100400c1480f855000280303108038a0520b07130201003004c000d0792440c0d443d107856800c0c200c1c48418018001d41c440d0454284c141000507800b0241c90741040c041c024000c40c102d141d071020001a405480300d50301c20707824021800c100540500040c07092603075500256003d455101c0c0380c10491001c2042004101d9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 817867005 1250 817865755 817865759
    0xd0b1504020f030f040c3003030f05010806010602070605160f050a1208060406050904030e04020901091d04140a0f06051504050a0606030b013209060408031305010f0c0308071e091e 79
    0x10001001c0e1f003410612400f0314400300450f1608070020906100c0d481210351034007002240451700001ca45060b1442a0200c80d0002d44682e416902402508803040f0302e0481d41007540002461a000851140e1141007150a40ca50561310003100303401695400700060300100030480340d49894042e80c0000c000a40d140d000740e003481c0d200108800d1180c1c941d503005903000998180180d200e4491300000b000c2c0343d000d02c201429000760058540100b554103580c03100c88202810302424000c112420030301c0c0d2050361302e00d000c180d5980d1034002d01801021071a01d540d040075a040644c486000d030030b2243c2c01d85031000401608155018049a5813420b9042c104160b49900340304c0680780c905121090401440d50051014081481031072a20900d03001c160400f0001c100003400d440000013074440540504035050429840da001118050b01d06460fa40009465803c0c2c00301107402549426000700240c0740100e0f03c407070756401e9030515400c094242c000041890104000a5040d0b1052180d0440c9111400584038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 817868255 1250 817867005 817867049
    0x1605010815120f010203181207060c0e0a080a0311010b01120f0204030807050304080f0610031101030e03040605070b1e041707020a170c0d0b1504020f030f040c 70
    0x800c0003071496450032001030751080503036aa07524201c50140810203c840480342c1801036400b0f500250340070498002c028a440c0d00b000d0020507030100741741c9800030300c90501003291100400351482c001d00c802808607880f061100c64807284e1001c006410003c000301024a983d1900600c140100751140380241d00d00341184415030390001c25800071043d0060007246015000d90400020320440e0300c0201004d40c0042d4030003c00001002510845600006850000b070040c800700e03031a16800c4a00180140540b41c007840015084a19016028810300d4005094081c0440c2c2030703d07503802600179038045080401c0b100204404094640c0c0c0c030182e006081c100042007070410551144025200822901140000c04000303005c050580300110740040100e14a29680c1100a0910b010240000c12031301417085003007203505000c10f901b818a54003018600c0c0541c0c498600b08408114036004962082d0208500241c1304501d202650150500d403400c60035504240c1b4002d0035015a50340100721480c280f8141d01da80e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 817869505 1250 817868255 817868267
    0x1f0e0109020c030c0102070b0609090705010c080706180606080c0d050304030b22060212091507180e0a0e010c14030f0703091a06010f092402150c030702160501 70
    0x122840302000d61205401d00b0301d1030031401002c9a8030610b620205088051066146840d0300494081e40c00600549482407101d454008a00440c0d01241040c500c0c40000f400180061100b103004420000785000c075104140090b194001090b0b520303e840e20024009075100384030f18850a0310844469000d4507681e50348075200d00440c07101502c204800070001c0c0240820100c80c2202e504101c42105980640746403002c000e40281c400070100600c41c50001380005000180000e0407003680c040103005507210130044420012000d03141207007006807840028020032440f02c00e80900034200700882ca04802250880c215000b400a10003000403013240a100300e0390182c1181d420504050152041d82d03520362069000d094500401031401a0a0900940f0a803c0c0d0310820302070502680c0d00301d5051040541100c440c8c2485c020078149011842d588805007010521900300e8402c0c3c0c3c0184d444e28071140b0000800084115407603050000000100040c043c0c2c1400f00801181901c0c45201500f07040900087c24 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 817870755 1250 817869505 817869509
    0xf0206011701020c07090e011401123903020f0a05090103080a180608040b0c091305041103030403051e07061e0c0b2a1207080c071a1f0e01 61
    0x241010100c0c1c90503000e00c20f40481d001c103203015086501a03075032100d0400c014440520903060951808040750407508000700118101c1c0c00c3e405500a4048558880f05000701c3c000300110842d40040880d52003000503a0841034201e100401da20781e0651860041c40002501524501d220741d0305c0c004140710964600c07000906480e0809c502ea5240c0c000800c0a03035591f0280700c07a240b944040b071100050455408000070740b00306d2013440055043e4461b800301c103259024450f0b801d9403010012043d522030350045e40c025a40700f406440441c0740d0011040110781940d010f900152800d030041001c5031507200d9925003e481136200c0c80e004050040c40c0c02d4006254102d44414000e10703031009510a40480e10030f01400442e03540042e10302c64141483c400340604941030403414480c0409120074003012038041e9080d6a119005141c0f1298a41d595400403158504010203440410405100704004030b01c0e088078030b030700e420b404090405140c140780b080c400032885265960f640001d02030f4030038441d04400d40e41e9141 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 817872005 1250 817870755 817870769
    0x9030f12190c02062803050601050d02132c0106050a1b050c0909030a030c1d0103052203030b012703030e0a030b090705240a1d06070f050d0f020601 65
    0x103a140d0149001c82d0780c240c021074081e40c05640841d1528414000d017110380640ca940e10342c62207260700145425800d40e0b0044406c40e001c500180079001002070190010302c10b83d81100c01510074140c480307031500840c083c6903004207541080d12a0102c0c4001c080b0745154058141410401d08080b500000181019079001a201508181107000c01c10403008100022070840000c1640340a03240903090b240d580d802c107414020006c0d00f0100ba0000c40d034029270b1009080c682c001050741030040e1000044d070140c1806007010010ba21080ca61503890088010000c0900f44650740105822079924001091180154100303000c1c040c400c0004c1c0b1420032116184001c42e0b5060415004802c00d010010780000c03d02d502c00b4240320300c06020004200c902041c1b5400342c6404403800e16140e2a404412140360034001d01503083e056041040d03001084c055600c1b8210101d03094a482c02681914005c2358641d008200202c032860301314030017401008820322410450703007080d240c440d590342c0d0b21040c000e640d0013042c4a114 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 817873255 1250 817872005 817872037
    0x80606240708090d060b040c0f120c0504030f030306050f0a320414060a12030203031302040b04020703020607110f07140a1d0a1104140f012309030f12 66
    0x1100300b08240056030000d4800405074050380704d050810101414040c655184600d1800180c202d259000c0c03c00300181e09550f13602c0ca00040041d0f40403400410100150005100c0244400000150760b4208080603d100382d40105626203440140806030808550304ca1290b0f400c82c0c0c040c0a01d0400f0a503440455440e507049000c408a60007840c0b5a40e0070542c25642c1180c104101c68192510300c000e410f0003400c003503401c01c04280d6507021034081c0c10034035100140141c000300041018041102641c80c0202d0005000045088104000a080fa8400481100503030032040c00c0041054012003083d100d1541000038158400350200c1a036100c03040ca0042c02082c4940960440007a10382604a0740501400200016455a100285000804101c8240d403e8a08020729500094500c2040d90226140e100c658501c0b0300d003100c1080b0405e4120094541000b82281d00600455042c2c4e4050f00369000c400360680d80d401b440c1d014141400100134805810354010241c0309200c140c01c5e0103d4100d07102003814030f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 817874505 1250 817873255 817873267
    0xc06051315090515090c210303010306060602011d070620070b0c0d0513030f020102150703063b060d050d0e01260c030c1309020408060624 61
    0x214500c00c0c1805018101201c601c45800142200b42d01c00303000103000308110340340d09001c1683d000911208841c445a9608510f41340c4004d42410368401d000c0840a26191010300c1c0c0175241d880c45d5400176131090710070613214001044116020710592400650190000d1180d0841c1c41060359144400e110b03c5040000c40c02e800c3c42810210810320000136002e0f025110030680e2640d22004540248105103080e00840400c580801e0082c42100c804404400660942c10b2868a840d2103001c5012402e0741035001320071b000003801448a102ca1b1049242d40c5000038401d0030040f80030000c00d070302c03000160040101c082010b4407049500682454012008400c0c1c0c0a503240c4000c41c5c2825041c0d00020141c2c82215010a181c58000714030340007032202a41e2708200d80c81d2040fa10070000f100612803014121a01c40458031000d01200115030201c910301e180d41c036200c1004509505a81142d2011214a6010405220341307031080c84102c0d04810211502c01744565044607180a0041c41c0040d500f03004800250 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 817875755 1250 817874505 817874521
    0x10c150e0115030303060608010e0105010804230607080603030703021203040827090a05190e010204050a17071401052d07030c0b0a18082110080c04020a0c0605 70
    0xa503111400c860080c02451091425504410803900045012030b0900c1030200701c071881100d0282c103e44000a07403030340607440d100041d42c0d4684c02174026030301e85115691006804020400d1441b20f68403980040c101490300c00c1c40103000c40d6001d000d40c1e11a400c01c004103000710380e000500100000625241564030f03200ea24060b03c0d684902280f000002d03062610711604600c0c2c1e0016010301100c02e540c5a1401d1b0354828101c1d0403550111503128100b001c1500280300c0701480d50189600c494100001072070261503000094003221998800003501c405104600756035101072003100c008000c00b00040c00301c1d0a00c900060994040c2c11161914040c100440540006050610b0b15481c039211105c2c03542c50141d82001400c60103400c00a596001031400440da400881e846036281e00884001c00201030030203a5100905903012505000742c0b039030884003044903002a050a00e010b0030b080d69407540d11903e4200f14a0406404100c154840da10600c0701801c0e00703402201030620542e001000240d103030f81d0302031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 817877005 1250 817875755 817875761
    0x3040305011103011404090b0106031509020f09040b0409051c14030a02040302120a02210a0203060c09210d120e06040501020a1209081803070e04030315050102060402010c15 76
    0x400a003080d0700700462406103000820040d8107890b88800058555031503a000e21080c2e44910800034481c00d40c460042020f1480795001580900c190640c2c146080d65644100080e82c10245a820b12004005800341042c0307000d02c94510004802c5d6424070141d8440d486003a21001c0c1010241d034dc00a402c1203080000344200c41341c401c200c041c04861500c0e41802040758009402c98002203015032a0141c2c1d120b901d01d07000a5629105034001c04c6262032401d11400c0c03112200301030710650494401d100300315006a1303042c01024803a208202d540c90300d90014904100309081c0c4044074039942c4001c84808a0078007404140d141c258005401c02e00d151480003d000f50052010b0074002c655400313410305000030810190010403043d01543d5942801114420b810700403115400d50007000380780100700414495480c08000b01000c10001d054428107aa04d01542c0700038407003200e080b4006a42e80800300754481340105404094002032004141c649007a0340060075102c00c0740805403440345090501084100c15030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 817878255 1250 817877005 817877009
    0x80a0302090105070b0a1a010206090d120e030304050109170f04051c1a0109051b090f03070816030605010e041121030a050d06090207150b030c0612100e070c060e0304 73
    0x54182051443c2c4900c540c6c0c01801c02e038209a00301c034404014000d540d840000c649028502d101c020b4000350b00031400030b4804c40c40c40d21201c0380b0b00781c071103040b1100240c0510207988254010000800c8039403203494030400c100f4103102080c020000600c0407070341003425442030fa015030b102600c1c0c03540d0069901885007508002a10b0050000c010805d40d02d80031082030509904885090030300b4403468541550305952403441c1004199018000d00c1011224a440e1070500030404028003900d001540310170313003d410f040b90400401138841c8100d00c1081003101500ca00d5004142031601030f4040c0c2020754a03541003030200388041d48a6070400500000d007418101c000c001c80036009040382d907100c90302c80001d891900300d031628420143c0307070400018404005008850540d0390184c040c1c2540340c41281204000c211000c0300310b800d03100e1501c40103043d0b212200202004440c403099079803507141c075105100c03102400d504036008040c0041d05000b0340313640110350390802a920400201e0700790304004815185006903 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 817879505 1250 817878255 817878263
    0x72c01030f0213050115390606030516030309050303090f01050c0705040c0e04140106020a081809010b040524090d11041817040f15020f010c0801060219080a030209010507 75
    0x2004c0006411450b06244c00314100c8107880700301ca013003000514540707010010300c55000031081110000603007440782100c1c840c205104240c0006e6442e207075241c1038501a84424201c00f0416503840500070705800c00c006000906007100250f03c1c041210004c00d40b4031000000b184d050000c0824403082c11102401703d4009070401800400905903d400d005055680345243e403801145071008004c880240300070190305841d102e0700180114640707555101e4042d41b10101005c0e2030080c500c0081b00c1e59443c459114000c101d4010a561554204000c005d0f405426903000e54004d04203c101c0c1c1740b00030700c0e00c0c15034801e40000c984207440e941c11800d2440740040c9510082d03501074603160300860318880342500e498034513002c0c461001400d4803410078100d00b4400c500944400121904081100509180888601c08410320541b101108840302650030340307440c2e4100101182c51400184040f031b604004c1030200d903004541c4103004681640b25032845128280f070081c00c25400141040c1d50340d0090741100d100c9544 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 817880755 1250 817879505 817879511
    0x509010c03120e060a0b060c07030201051605190308090d120209060d2405030f0c090604061814060103200307020703020a090b13050c030a2705072c01030f0213 70
    0x2e800d400f40d485400844020b80b0300c500e004031981c10707800e040c1d059440c03030a00d080c000d25620f800c1d500151a05e8211710030381190691003c1140d000250140210112420759021444528050380360141c2244401042210300d03a1100140544090b4000d00c00002141c0c20500180c0d41c03401600481d02512a001c0640301d054140380c0c040d103102d00c1018242280088240514000940760010161a6042c000414001e03030302c107030041561072a045802c070740c02900040c00000c216503120030880d404000b5449045089a9034412054900100030555500190902c1d040014002d003a21039440e80a010440014000000c00080c00c903900230081103000c3c54004020156145d610780612000e402c0c10720f242c6025006454501000044500500340106041d82c0d190f808c40d6560340d0910018000040b510102822130f0441918180345100890902d0703001c0d00162058a0800c10103514240104d078100e40d101c9075620142c032860805152641c15240d211880103602e28644c00080d4040f020104a040540d103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 817882005 1250 817880755 817880771
    0x1b0309080d080105100509090a0b130509160608060a26030c0708190206030123190501020708070302150c01020c0d09090b0d0506070f050c060103050a030206160509010c0312 76
    0x180000c210b5040b2241259008000c6803d04030448442c01030021140d00040101c0104030700c150703107801507a03000001902c0c10070000c03d0300718030406a98040d00c1c4400b2942000c1c055500040c0196001c0c0041e00190800a0450801d000461401d4440c3c0c4110001801c0c801d4841140c104107840c40c1503145205001c688e254000b007000d8503140c0e1011f114980700e03485028035498a0409207861140031a40040569095171b1a00c4069244540c01c045000d0609100034844000c070740d2800c2d00540803117140100180c10600b414000b900d8000950403101003944481010001a0b498600c201203152540580c0c0d601c03011402d40385070281c0604501c900301805560418841680d0115044080310300302c680c184820120401440002c5206001c05040384d0070070f5001668150046000129000702e0346402490912032030511402c0050a130000c41e50340e042001680180750f8100b100c10341012200000c00401450000c01910610600c24020f050103460041c981c24107001d6101d5440480c015001400b83c90707 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 817883255 1250 817882005 817882007
    0x5130b0a030b090d021c0f0309051b1c050a0210180905041205033903131202060c0702150c010906050f0903040f18020415030c02120306011b0309080d 66
    0x541298544030502c5406640380f40c55100003070746259409001c103801b207000c4035410200d601000707200c040001d02d5280c044d0400003c004100b0034403201041c515008207101210100705042a851382075080c0c4070307c10412240882c001250319a0b840e0303411500003502003403403802510200c2c081c4640a112400000340020010a1504041d210303500c42c1c1801c4105645043c0706a13041d000580c0d80810300c3c04202a12882110180801d01003401d03068111018000c40e503400b41c030706500494400283d4541c3e400702c00f0070000d403100c502c42201110b0000d85030070f15001024121500603080081c0c80b96103984d0300c145416800004503068148888005d110880040c10600080c0400b80c9080140a2008002520b03045000c41900c050320710014101d10f8292404041201075100c0e04c1c0c05e010344980c2044000b41a823403001c0d483c80c00c100700c4e031801704090703000d298040e09114000c05440050030b810420002d103a0b80c80320085c5001918201041441100b131708048400101c0e86d00030720140e10034555100602 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 817884505 1250 817883255 817883273
    0x705091e0c0a02100c08042a030f170a1e0c060c020615010f090605030903092701060509152b0902091803040515070611120609040c05130b0a03 63
    0x80b00c250702203900e000b05500a0500f02e40d401c41c40c0c9800111940089400200480c140b101ba00c40d0240d841c110b5002c240000c8040030b4819841180d203009030380c1481b000c00c2001d0000102c40c12551103000e05011203040b000c4c2062034418071008881081d500c0e400112030040410904558001c001004800208000a907444000743c4920f0815003950503c0403403584510b6145004800325901c03140350518104043d2240d4102428955044c081803001a6294075440f58413a200050000a444110410301807180c045006800c03120400408010303400c255120011184295014040950744c0e03070140321a441200e52820780148030802d03d00180038240015500510000360086444c00e0981e1985400418a200c3d9030f00d1045054000348800c200318a040e450100c4a0800617102c20318000d642c0d42c80508035603001c4080c41241001241c002c0400b800c602c046c0c5c0d400441540d01500f9403c0c0798440703011568043c852a441203c004c0c0c2902c550f4106070b00030343c02200001d408018441d460f844d10003d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 817885755 1250 817884505 817884517
    0x30a0306031b0602100b0a03051510141c03050d09050106171911010c080d051005040212010905060f03071701050c04030c1503140703060906060e030705091e0c 70
    0x90085801015000071042064540449038513400400440204a0f98031010300b00c40703040c080d0310000702c0c0f0000010680034084030040043c0b00d644011b042ca0500c91300e20707110015401c2041c00c1c58110781010001d403034240346c84006041c0c0721482001c69025180c00c488074480d880d0102030207400c1c05010420400c4c150001015560000d0101010000d80500c1035641c00400140c02d18440101c00d2080c041a00e900308110304100601d0081c1e000a15615105915448040d51610b42c0b43d464080191401e1908030020250030704403019442d0100c4011182e1401c481805100261380e5100040350081e5180d2800101d2008080d00345c0d0390701c50b0b6481e954403944103080d130140710650030000092105180d80c3c0440d03003542d900c1984044058105000009610010300142c000d0603512514580311812040c2500e00c12045541d022803c1400d0840c82c100340e039908e5004000f44006100c0040e0b950390040740c0c20094410030303180d6003074a0742e84c0b80e202c0a481c0d40c80c1c084400c0100308030090040010600c001051 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 817887005 1250 817885755 817885763
    0x804050c0d14100b0306070f08060f0d12080703051003030f210c0c0b06040b032808030a0912032313021008010603110403080f070507090510090f050108060c130305030a030603 77
    0x143c1c9903207007c0b09407440741d0080c003448000344203440010150f00d440d401e0f881c00b2200180680c86030320303440c0c1d0310f4940018005841502051002c0100100154540151640f00c5110348098064a2566401600e1001c0c1307200c01800b40820b020b00701c5411140c120b002101000b03107072014401c0e404031403405411000c5400042c0c07107000b6114000750403030070540500804441c0103001403110000e408451301d0b0b5100c2c41400c9448a030412031240010481c50ba0246003c4d041003200080d00001c1c518207940242401e207030140a043c1000300860046558422009103800c80b50414030325560340d044400008008004001c0d400000c003841144402d1707000703414506a441039281080591032030f03a1502e600b4051880020040101001a00c0e201588440944580c9102d001141c003007988803103105040d100700301d865100200c001142044103854034060071503400c24448041005504011850341c407110004d21602d00f40c1c3c0001400f0030303c81c0094072118000e58208094035125070004600501500140c40f042e1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 817888255 1250 817887005 817887013
    0xe031b010513120804050307021503090f0a0201090611070512010b010216120204020711031c020c04090b180307060e0a02010905010e10030e0f060c0a0f0804050c0d14100b03 76
    0x103900b84445018010426810010a0343c41805010003154800c2c401002240c00f0300062100300f005840d6070304401e41075011540090b880c6e2500814043c80c1900140d40c42d02580d01c0507013003d0250340c002e61804181d41072840c010141d60405812603107001034a81c0044c0e080340e960856007170b81f60340c10b500c41000304500768255110024280e0170782c042401e00d40603140b2503034282c05100005140c268000e00740c41d4490894a0346002c5801d00080c205005030341451410b10760304402c0100c0c9581844441c00207001200d04104491031610362100c3c4242c01082d40030a200114010f1010b190108160f178207a55024a091000c2c59401040c2500d034803c0b041c08174081400b100010034550301403005001d01c0f0030050100c0e0352424104404902400f034a065006403402841180b0060400500240740b00314070042d00c050303407007445d05001800d4044842c10300d030400c90540c081c0400144c0c0483e0401c1b01050490f842c0d00d200c203450400c104254031809030041c1d14840c00c4800200100c041d0003030b6403031100850035a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 817889505 1250 817888255 817888261
    0xb0105010206090318040f020a090603050c16140a300302030108210405190e100b1c0216150c0302091507060e16090509010207020f0105030a0e031b0105 67
    0x1a640d0b02800d0340d1107100b43c0c0040c8001c8080542011040c100080c00500200d031424043d14008201d9020388626000590118001d000381b0340c16005180e004a500940301c0d14080c9841d15910400c0f0101d80c006000c6107501032000180c280411044040b40c1d0442c0c0c0c0613520401d804404910304140400c003804c0d5403807200411120310300034400d030f074120b0300c2c140d01a080d000c1c0d4504407018905c1740c40c0380c5600c11903428000407850b80c5900c8080d1b40c0c1c6001401c00003210a0401030080744240000b0503448103d42514400d100d64040c10003610300c2c00490f40b4407001e0684005601070068041c28507000d80078620000c0d80c0702071140d000002180c00b096003008110040200030101e05a1080c0718400742c21071240a0400030304014280144a01801071100051860f0b450500c1403c080380c06001c0000011102000e100008261080301e801880c11002103240c4185580440c0c080328000b41d009050140c044001011070690741c1141c03024030050001e803641d550b8403d4030541d10000c42003604000390720340800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 817890755 1250 817889505 817889507
    0xb0f18090f010501080615030109020c01180203150a020c010903090608090c0307050f030a0606090e0f0a03090e06040915020d060f0f0b210c0702010f050a0c0204050901091407030b010501 82
    0x200c1c010380d40c49541c8661603007424010b64400b0b00181005410140c9503240c2d00d480318014020314041c214004000d41c1c0c90756901509829079685400584501503010b80c980300680e00020050a85008481c4040c25a43c482201c1c8009000d22000549103500f0200002c041580c805400b50907500103449080c055228142c1844e958280300f1002c41e05580280002c0c8120300e001058600341800003000c41d603902e0090380c3c800e82500d0055024020003905e40c0d0b1080c6040d0401c2c090b08140241100c010610381d82c050b24010608105441028091005900814041e8507103401078040c540c2c000341d810189025001c24240254051900303040168503211001c20f450b90142c0010b0b08940c10307010000c85942c140320a42d1402e81c0405902c00c140a41003d84680800c0c00303515207846403084161198607a0b800d070002400041d0240031200070402c013040402c03216500000001072281e016a00000e81c5d0b1b451444042c01400300ba200940900c101c8403500c0c25101b00000d44600703807031040d807008903966a00c4d80 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 817892005 1250 817890755 817890769
    0x61528090f14042703121104030605010f0e070f030b060f070f0c050d2102210a0306170d030908041a090f030a0b0c0d0b0612040b06010f0203220b0f18 66
    0x141e032010541013200c0200417901c150305840c0e20810714000081e01181c090005046540140e000b1214a13480e90010410400040302d0003004025440c2018039501d03041400810103140040711005150707841c405861591184000d480700c0802c800c3c6801d0756011a42007040b10743c025208201c5844100c01e40c049414104200390102c002c2e8448440d01103002d910115204244000104504510a10f42d00010000b86840340f50042c032845e031203803540d03480c143c0b000905454980d0840b08060110304184100310714009800c00101190307180c0041c2020701c80c0b515603010710543d40f003521611615886420315601080040848600c00c1b2480550b1503003000c24985c41e500710340c0c40070f84041c0203200080c2d00c1d00e90b03d070010140700d03440b1035001458986680008081d90803503c0a4140294014104801c00101912007074002e003090070301510380740b00110020b54078880e40c4900c141500003802590840c51100c2c4030707039028200e000402c0b030712043e90f10142d070800c1d003080c1161452880601c802e102d280c10003070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 817893255 1250 817892005 817892051
    0x51501060306060e040506151614010b151605010606031509050402010c0f050f100504050105092b1704050c09070311040b0f070b0f061528090f1404 65
    0x21316600700c85103021042100400303000740150380100c02e40d213508000000510045c2a40380d2511030100b000105410504104040d9031100c41043c1e14014000200341c0d40d006030f004003024841c0c0e455590702c5803040821460101e580c401011903003000c0300800c02a4042c0c004085001c0700e00c804d1020941c1d2030748aa42a035405a8000c1e0228030b0022901c3d012403148005903071418000d00880300e02e0041b000c581490324440ba4401501590b0300c005110402c6000c0c0030315908a29040010b054611480e6400750810b50345440110441c102c00c20703035880490240c3c402c00c0f1450181c8865078910300c0c250a10a0712200c180c2c02d41441200031030000391010b0702a20075100401601d00c1d40f81d05007810082c02003031540c80200441c0503000140400c1d00000d0803501c1651041c00241c03160926801d00600b840182c40e40591110501103003403001d10b168102d0424915000c9802c00110980040c0000c01990304910035044060301e4040e0358004200100c041c1c050042c03949058408004c18030110900c0c404d100411 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 817894505 1250 817893255 817893257
    0xe220c0510181514130314010e06070503090a021206090d090b16031e0e040e21070c0302120609070506072006160c050f06030c0301090c051605150106030606 69
    0x8000340030000d60007000b0303a03c01000381041020b14250000d454405e4001d400143c2c544c08a10a040c003c114009000d0848103560070001c0c0094072950f1121a20b50030001c00328400c1001c080000740300e40404209a0130390303e4024000d00d19400c04544201e0301c07000304403483c05841c86100c48044000e03105a003641c0c11115101c100d10b0821520f00c544183d1100b580c0e6050f01000b80b01c2014800000f2091445007240e039654840c5100c0c44010b50071301064600b0b1800550264000d00c0740040c80d000300c800014002c08000c4402991496140703000c02c4450401e070030194011100e503904000900c000100140260700407400c64541641c2c0304100205803040070001000c039050012130100301220822020445400240340070300b00300100c02840c0c85a540310310180c50390610b01d0b03410000b0381401240c24010550980e4101c3c07540c5891509443c3c03520040c841d03c50450f586010f02d14407580b080c4c0c1a50004140f140e2603101c09030050503e0344e034400c81d90220319407803a441400090f202d4000e210b080d04481003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 817895755 1250 817894505 817894547
    0x51b121e09070b0d020d06060f02070b030709030b040215030112060501080613082109070e0a3c14041109040521090a0602012408070e220c0510 63
    0x200943c0482c2070b000740114000d016002c1c0118100b10040307000e100e002d04401c0e5201c6004181a000091510300d0326488403110300380401c01d11800542c081305820980703800554400302500e840c0b01040803c007140c0120b841c085800b00010503000410600b084142e13000700e00500c402d9881d20003040c0c41300da0550340c140e1450344a05140001071882c0010f8100380025048e01d844c5006542d8490500d00001c80e40707020103800140c0140072949008031158cc0210304044108064102d111001c02480ea840040c0420f82d940001400440300303600d4a041010956a5400d02040035620507000ea1400152412991000101500000c81c104007609520681c0c0180080a07013141c108200d0512030000048540210001c1020000540711406520002c245d81d5000044038101c85041210a00c503c0d1601f0b960820881c604100c140e500103200c4080d41c501d400803500903100c3d10441607007a003008443c8000120703801c41940602c68400c000c10120741c03040e1041c450060a00c841290f881649451105107485 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 817897005 1250 817895755 817895759
    0x1030b1009020f1204030216080304170c060f090a08030409090b0708061023030108060f010b04060906180914040201080a02130e0907050a0b0a02070b041503051b121e0907 75
    0xb0940b413101d800c01e00030700682d101d920110081c000d8200e1650003000041d8000142040a118103002c0c0302c007101e501e000904501d607281e9000500c1c0d8032480039003501103000400c80075011390300d13405080000c00701c40b0200d076a40c035079541143d0050040c8000682d016000c1100084405014110541c4101c10042290b0640d20000b01c0640d89248240e14040000703820340d0740504400030280085020b40600c00003050b42d450000310300c00441405801c803103001032003070204000e01500400404117983c2242010f4200e2241c030703040508440f0a95111035401e030304003101213a116009410030350007103000ba66181100da07207003421101a4401c0b100c01149040c5094000c0100d0807000c41440d8016420009560302d065580f00066903448581d084060401c03030000300742c0885070701004100c00500e0f641030010305080c689441d44400c20300610440040c9500c9200185405056013115004404005c80b0706072182d90360449280a0f40c07044464240e4400003208170080d007058044454420b8032031900a0007024 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 817898255 1250 817897005 817897027
    0x380c0307060e1011130501021606030c1b290606040b09030106030b07050409140103080f0c120a0f2a020607050c06071a100e160504080601030b1009020f 67
    0x6600c00300e40c0c03410f020781e041d9048002d40078022a000000742d03d880584070740540c10442c82c0b210b12a801541990300401c2e0400203da00380e0f80c03c80482e8914200000c03018144641660242003e0060510640080c020f00341000302c0b08200c500303e6900010119010b031880044440030131402e4a0165001070240810003c0d003841c60f0040c4403050001d4000b00384560f81c0d0380c4030a004601910500007040c0045000c2c01001c03060310500b00c1e044481e02810841d545540c560050511a03c0c0b21444250300004410309030307500401010400c0004c000d1100d0359403021030001805040c034007109400140304440c0046010422110b8034070b20f085401c0c18000300d081150300b009210f601100003241c041c0506a070301e0019603255405405968059030b0090840240801d0b0345030b00510003010034481c181d107050148141da43c0070140581c8000503402c2044410740c0c01006640b1130103141d0225103e1311560001104011341850505c1c081c0c20310901e400140b80c0c595900d4000d038001c0300e1810701255005c2c813100642d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 817899505 1250 817898255 817898261
    0x10303051c05250212030f010e0a0b0d030503070c053007023613030305010510080703050c120115020c100806091009090501050411060a020a08090604380c030706 71
    0xe43c80900440343c141d08066480c0509400031607600d41c80e0010307140100801002411190350140c0c101c0710801c410058400050028026035001404026020000402441c0520311003000e040c0c01204032400c40100c100c40348441070f00f03002d2003101986400c3c1e800d0040c0c000c140a94503841c0e4000e00700d4581820288a4a8051465041c0c810b2111103e20484442d0410400158020706808403108101c04c601d040203001d90308181d0240740980001400900c0841d4021441074000d1198600405d21742c0f20184440c1c064041c1303012500858540b80000500d100e0140ea145038840520340035122407140c2c040401030340d19a41490b210118641d10002440f514091302d0190b80720340050604410300340c844071040100c50402c401100d40340e40d40c00900042c4a80c00c7c0e07001001c1102103900c40c0c6040e001c8030f002511900d4004008015a40200395004c2c15038030b10065401401040c4035083d0640320303180c00700455041c1204410015480d401c4841480c01040040310080c03080400110303d0542c40344d54100007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 817900755 1250 817899505 817899571
    0x120d080610180807150e06090904170a092c070e010903150f060906080c0f03030c1c1e1b0c09052802040f030b0c070b010303051c05 58
    0x100040365000c0c540107000b48040801030020791009041032810144003044d00c0c2e404540c07200c00d00414688038401c607550b0800b25401038005640481158a0314603041102d4050030651040800740822400d45095010700800125004c40c8585800403602c0d58246042005135206d500078800c040000409550003035201051001041c5400c41c5210740d640c591050f40d0401c407100401841c1c0380c4842020008584c0141000382031010003c00100e89020010f5030380d8524141c1c5180035208581041000b40d0b03090040d0340c00c505901c402d640e83d2a6042480702030114102401c8030204262900d40e0081040210307070303010913a805444d490402d80703146040c1c030003002000b002160305001700300c40482c40d00414000d07c0e0003101400d04607000840c000855501424980181c0d410340c0384188410003010700c0007a112022640c02585020640d00c9501103030b11648030b00b0401034525000724000008059000000701510400d14800c8020040f144000c14203030f800c02c2d9112040ba81c04241d180d9200301a42d855845 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 817902005 1250 817900755 817900757
    0x503041407150503041401060b0d0b270910150311030a0c0f060f18031106070812010e0a0e0703080a0507051204080d0503040302070b03040f050307050a02120d080610 73
    0x40030307510244000340b000c40000d40b10005038040140000c100c0141180d8a0210804000b400040c1c284140c03000c1c20300403c92440a00c6440d0007518540f900c0f07201000380c1445886078105464600c90304191558030f010b0f01c0001d8103101d101c500d0140500b0700e10079160003612045142d0860fa1a41c0c0ba03a134807824144075a65814060207250a0010702d80200c2c1c28010007903140944545884c2c010040d001038400f17010001802035940c59120500c0030100c030342065941c00340030000d282100c003000c5003182c0620340006211100000e0b410b10480701c500e4056049441c0100700e00c41c07030f40e2a803203e0404d4541382041c80c90160b00c2003800744009052540070f0182c900c43da143c401d00703003582500c401c0e1804010001120305a40000780a01c071204060008001451540c10800d1071420705030342c003e580d07254030701c03e00240c54404008038040003081044030100e2604102200d0f00c0d96000d0510649505800c030080348a5050110040602800442c1c0c19480404540b00e80c01142d84038022301c00c2803000585040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 817903255 1250 817902005 817902013
    0x130b0703200708010b01090810020309011b030615110604060f0b0402130305160323010f020403061a0a050310050a1404230c0d12020a022106130305030414 68
    0x3052070226003001e8000099200500882e8034107500d41d07084412100f91181003111118042c0100c54000a0340003141306c0003280181c0da5a03500d504a80100315006503034203421080c921900820341c0c90b030041801e40e1140c46010031003456003441564618036205014076560002000500492443d0344030455000b5a6003010031b0010a1000103400c903841800550031301c080e03000f418024040100001002c807403903100c140340d20070b0958880d001f004850040d604c5600800008440b1080703c00c0d080b0102c905030000e015502c0c0c41d200d14045024005004800052401c58030101b0140d141c800001c0c411514040c01808202000e10740101c05440003c06031650399880c0c4440c2007100d00254400b03840750703020703410394184414000103075104407800441012165101d0100c02242d40d9407440b95205459000012901346200c14006038100070220101035880125101000d45900340180100802803a0400b0360308070781e813807011201849001003009000240c081c0005000100a05140c0300b41d08144230440e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 817904505 1250 817903255 817903277
    0xb1e1501053a050a02094b030c010309110103020f040806010b0a0f020d0f0c02041e1a0405220503040b0c1507030b030a150e010509011d03130b0703 65
    0x32040d98844040c203a00ba680c02880d40e0385400489104190f0814140b0a06528103402d800002d0703401e004440c44041610082c041e030300141802c410b00c2c0ca80040c004081c1e00d030b10310045501000045419000d2500038010406040055807291043c0048e40b984810111901e40c042030045009420110000c060700000b0400464000c400704446402030003210751240c1d031808410001049507000c05440d005540c4a0201c007046190824010044140c41e40b0300203149905034000103000d031113201d50b0241d0014030081810b42c00384068015100b6082211f4000714060404814041141d2007114807000c450110740f008900344d14680c0c14600c00342e0003001200d0410351107000080941d400900000c00e40c0d4042850a00820100e541d000d5011001c2d007410884a4000d070b000c242c9552200c000142082c0304401503e102c548268004920119a80020451071030000010790013044081c1c1502c01c281c07100d4001142451000086522034400c10400140c082d10b01590182e413608003c00c02c405220540d842 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 817905755 1250 817904505 817904557
    0x105070c02120c2b170a14040e060103050c070f0b010510021f090f021807030f1b0f1215050a09050c040603020717030406050a15080a0f05120301030b1e150105 70
    0x390b45c4180101e8441e07030350751ba0302c202c805003030700402458180c02e1480c14401080041101d61160384e1080c001c7c00c000c541692541d15900091240c0f8030b00034444017202e900b01051040d40c10103d0f059910985092000c13841c65002030380d4400010b11080d01130400c070011103881d40e140e0381101e1301c110303c00c6000b00080040c1d680003501c841c20014800180000c0d2800700211154513001d00c3c441d40700e40708010404070000300c404071394500040c0d01032800d03c205014043c003170902c150555400c125000f14100644136144c0c154440c058a2445154440c1c0c541000c04a0508803d21405010302240c802c060324151801708180c000e9004050b017541c027040e1080182303a000c4000740056225510461001a50f0301e06405c406044038594151000b41404405042c00841000100c920b80c0c6900f203031682d144001d03c3c2c5412031a00808107280803500502000020401603e510401e0140426400300e206407207411000d07860210040390140c590805074503a404255004034001d107259080360028800740c20b42d40c10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 817907005 1250 817905755 817905773
    0xd09091506030b060f030915010501091503051e16143903040e010306180210030f1b0f0f0305040c05040c0e101e050304021806030307050105070c02120c2b 68
    0x5140d0003235000103c4012080b04c03518181c0d40503101c00d080086e1098100143d111005016a034010103040d901c0000c140042140001c002ca9007290301518a4140380900154091114166121011540101c120f5184c0c180341c2050b9144154205a2848103100720320446e00e0b06400c1814a890100c0e10400d000f805000034030003400502035401c4105800c1d451460702c0301c12071300005c5034286a60b840351113010043c0e50f60006c082d4006501c0c90040b0700e50302c68904400c01032441000000741000700c1d400710710034190407600c111450001600c4004400080a0703090f000e46904840060202066160038400c0703242c00c1c0d004542300e560900d040103150403070340d0115804440354240700d070108504c1c81c0c88031920b1050300081002030700c2c0c5142560641c14a5404182154070b00b0800180d02d11280c4001509900c00708155640c65070482c0003400517040c00480601b0829991009a00401107840c5030361043c078001840d80400c6002a10380c0c00c58006145640c4200c0e020700034240c0030000e071400c0303d00120302e03540 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 817908255 1250 817907005 817907011
    0x30f04080a12020c0c010807020a051510170a02120a0c05060d0b10020c033c0a23010b010f0503040201080a18060f050105032d07050604080d09091506030b060f03 71
    0x2c1c00e64005c810009001180002d0466085500c00141a400070f5404a44a8070b154584c40034424141c07075100032003da80b412a001110f0022940710040d4400c8000240b100302540241ca519011b826640c0c100b5468550400c0302514002d0b44560030491800c00038001c098070404031a00140c0101c40e200080c066018400e11240141e000704202202481d092181440c016549540350b00a5041144240d041c18020440d040205a80310380c040b4507404c082c0f0400e451140e200315480b10f0340790124210018441d04555054003036190014898055001c1c00d07603500051402d40340d441c21a65254011140400c004100d015000e458440e1007801d20840720401220a100720740100340412a00320710000c0303c5059001e40c1c0709a00c6050300d1600715000300850081c5803100000c2034000f2002c000c50a1518005074001600b10710000340015058002207400d80c9464240c0d50780ba0700740d072307a11020036040d174161542038a800050418100010707400303035101d001294805000c042c108000307807102e072009820032 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 817909505 1250 817908255 817908277
    0x42a050a14071a24090a0905070b0a0f05030f040b060f0406061709070b300720010c120e15090a020a271a0415050a060302030f04080a1202 61
    0x10801402408012926500020200099a640910660b8800130b940380383c0384c85000d5681000401d40c90036061300300c510a1904001119502e40d5190388180c0940d0100c50f07900001580214100798580c4500112405010360f1a9080c9007919251695056210060710055000d010303540708204035191405180002c01c0941c4586241c41d42d0001c82581000c0001c048042580084034203115a44901c000d807402480d00d4000350b070100002c208844c4a2480b0003c111180b80d4003c0e0800a4207030740100c00c144040b0010303404c65000005120503078241e9000300003403030204107a0070100d11881c115034415560303004007800301c403424240b60400a0f9403500a0b2151010390704510070700815420000d21000080c01070642019242900510082c000402c0190006100c2e8881f09034401d102900f180301e0f08507140080003007000408101c3e90009216107407151600840604000080c1d281c040d01c00c2c1c9110384403242c01c15142d03546035941c40140740e0160901e4402e00440e4007880f0361980300ca2014010b02150 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 817910755 1250 817909505 817909523
    0x403081801091416080105100303200f06181b1306230f120a0305090f0310060608070203180f04091e033506030c061206042a050a1407 59
    0x60100b0007588561356411503042d07603041c001844800a08920f0241c2105e0f01494500d52079500108004016406144541d000b841380900030241840007248a03400b80710402c01200c0380d000c50910040c1c40d25039842106a41184031610282c03142081d041c03d00f440d64150382c00080440d02d070412400c4028845000305100c0020003000c0c0c1450521074100359030040100c0e000e085010b001d083e140e0369600c882134002e040240210700c1b0a155200c1403040da400e24001029035240e000400c1a80f0b0091440b03114250006428101280d902800402140c2010005115440080c02c0c1103040c420b5540c1c1194485030020350f10540400031030a038481a950600142d52078405924131410018404001e08184005040031181d2000d2038410001c10149400c5254004040c2655088000780c284000c040304140c11400c00900c0d204518141040341c0d210301c800311820840c800911074004e030382540d83c881150031804600d840719481409071000e000310000616149092005000d0f45001c01d4005100455151381 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 817912005 1250 817910755 817910773
    0xd06060206100e0c0a0c1e0302010209030709182406080a0303050907062a1202010906060f081f06050a0f081009110105180303030f011d04030818010914 67
    0x14442c100740c000300001d036030004440c100b20104512a200d06449107040c0001b07075020780c040240001800a03000e801c03025101134441141001b038040d610040c5a05e11074001c4035004620f81e801d0348142c10b0300501c0c104084c840d9101958502044d044c00c4240c811401800c980b02c9400280784e40610805040602c000d03180031a02d525006d81558009030499110342c00c541c0003809655440320703882c000c00c0c1c1d03601c034000c9405951410305212039880301c4024050412000302008118bc054211051251080c40c082281c1c5a0b01c90808101d82c105004900e51030b00000d1200d01c01310319245000500c02c1169900048556440000502d5503c0c00d84c04102c480780c1c032a104001061043c03180010300340700c0d09020b20410405a07a01007403540780801041c1440404280a00c5680702c428a020b81203001504581e030343e040500548900032000d1181d1a07980e0800d030ba80105400d03a4080c1640a5036041c1c40304002c13070f16950041c850303d0a019a003440e0540d40ea1145201060f10001e4108900c20702c900034001c400d03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 817913255 1250 817912005 817912021
    0x6041509170303150114070b0c0c0f03030402130207140706360b0f040e010803030a051f0905060d0602180405150303030c090402040b0f03191407140d06060206 70
    0x1440031402001a400510800c003031584c021320648441c013070900e800840000c098803070400a003c1c01001502103400704040100b040b00349802801e111079500100e03100ea903480590282e80f44001c4034001d4005814001010038035203550003a00c5940d1150400c90140070719101024900502a4032640024180f20703100780c03540305007801c4a804d09040e400001000c050542c241d00d92003c0c07a03c20509005400200f690b0b1041c40441a50007801f90074100c2025965905602030740c0360016240130074510314180c0414000e00c2400c03160030000c107000e541c00142d0303481c0104407070042500804035074112040d0b0901c9400110b652008091f1808100302580009448000740811a00007c00308000c0b5001240c44c482155000070a9070390108c524004150b6070f00158020070046d004513030011421003c00f244c0b888811011001840c0b0681c08200f145400340703880c0c00f40e2000ea81a039154250341c0104d41c00495480340c842c0c10b1319802c1c206880040f51800c081d42103840101c40c0185d010400681240050003992 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 817914505 1250 817913255 817913279
    0x6030213021215010e0111071728020901090f0f02030901020d1109130b03070302030a05030c0c01090e01030605061206101418010b0309011b05041e03080d020906041509 74
    0x140c03404207400070708103e28001030202d45503107117060306010f80c3c11006544110300300710801c0940001030460401a440c80c100716031344d80c4100c0c0708424901742031004088081c07181c03110049030350700103000312016440d100b03803600142a03070281c4081310750b12000708001d10000303400198003428030900010383c0c0d40c605481c00b000701c0b9100400f940300c00104102d00e104640d80c034142c50000c915684070000e208400a0002840c0c440107920094250141011040600a0120242c008000d03014140c2e0134243c4410011140c030b078104d01540c1148440000140003141050b4403c80c1c2c00040036214001c03094603640f80520b008000c4070284140d90850398240402c160251580b040c4840c1070b030b0740221080004a03640718800050203000260788010002809804c0d00750440850802d00305050348900540040c01003040d44540111080544d11a003000e40c003100142d02501125001b800490a061140d44400b01950040940c0340e0700076818400441d034004540301c1000100140d890341c628091500000a42d8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 817915755 1250 817914505 817914511
    0x20310050f01080702060a1a09040507180501060c0b06010210090b011802281b03121a0a090203180106150e0a0e0c07152d02040602031606060302130212 67
    0x10441d0541c10b03c0011a000203000b03401201d52000890f11108e045946003590307030409149039005500c10700784018400041281c4064501d54484c174809203041840c240f060350b10a00c1072a0000d94481e948102041c8103981c225009841441070341c2c1ca20704000800000d6611081040c0d8a920654004020207040f9102d2540c4441e658030301581020400e15414035041d40c1101004030440d840d0810503810b9110340c2061909030101c024501c0403040900b00103103410340c81c5d4030010003e4030b8003882c014004036142c2c1c040c20483d0010021492a402d04522101a40008d0200008100c0c00b032812080700a0a010f510094912401c044562400c2c4440040001560781d4000d401030310001024001041c45003540b940c4101300704038099071141d05240011501103031a10b01010307249420344001501030070030700001006041030020003044603041e000034200e100d140300b01c074050380c02001003044405c000c241d28140f55009840c0018030690700e4021410040c0c0300c400010350541e00203030590303900310802181c5030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 817917005 1250 817915755 817915757
    0x12091101020d090b0d11190801030c0e01052d060a020307020f040b130b0f1c0c06020607050d05040f0b010b04032f120109241a06030105150d020310050f01 68
    0x450a4941300d80600039100d48000c1400e042c0e224800c45000c00390310340c00c60301da01d400719620040c424100c20f0b00801c080400e0008590480c4c01050010307688001c07000080c141c3d500100f440120340c1401001110280084005407e40b00c03031403c59880039503d07140600342e07a84203a0081d681e81e04091040103915101445000d00c00c40c5010b141038510b03291000502c0301140080307000511240008000744408a488040d0386e0700071180c0c0c041040445120740d8803100c01b4400c0c220030340e030b107515108280e80322041203512800080d018042d80011312400d4018a800900038800c500d00110b0315121070231011001d0308014030f16a000602041000000a1010000e6000e111a103458910a00f042c0010b1812009231520030942e80321841c001c2d0b4000e61140d000190300903880c20148203a11030040810501d00c4641601d54a80364442c82004240c61022122900003800c952450f800d080c10803511105216491000c500e0500004541003541d1000703600810b2400f10310903060380303041c00708418507450f150031038 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 817918255 1250 817917005 817917017
    0x1c02121e030c0c090702010f06030c030b09060c1611060a03051009020f0403151e0506100503010509010302010c030903060c0e1318080f0c0a11040b1009050103020a12091101020d 78
    0x82041200030403078003c58041150740d2800e0b41c90b9004200e024180c0c92110381e07441460802d0000c00c000c0c211580d282220700c5049080485e03511001d803c0c0c0c83e07140c100ea6020700c061040021031400d244801010b44014407802d040c861981c0c2c24404140b141e00903040e9200400e40c0c0b070050085070441030b4a244d0007480001002c0d1b10701114010342d62081c0c000d03480020031410a1501d01029030596820524214012104a40c00703441200104000303000240c80003070042100d4003061040034030600c1141e040c0c4001610204040e40385034011507000000c03440503010099400000701c0015140c1c0581441c245960307556803d224034641c200302c10322565103040301d203143c603000030010780d00760305668000c5458001c0d80842d21128240c224018034441d074404880b2078000c0d81a90400c0050076031308242c244070103036400c00080070743c442404000501400b940b40403401041003000079600c250000c203042210762030310106109445c4458819600194002c84100c0304110788045a035a0410010340c4400482ca022 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 817919505 1250 817918255 817918267
    0x101e09050603161a0c010c0801050907090308030402060309010207050303091501052d060903010c120e010b030613020f090f04210903080f09060f030a0b0a050f1c02121e03 75
    0x403c0c1caa441902c2a20b0b001c1e40c103000032240c005458002e68840c3d44000009101000010f88000c218680900665206444040110702c2180c0701e0480e840c143d9a104400d0b81c916100ca4080040344e800017402d03039425640800031100011400e00142d40142c90410003440c21034885045080c2080c01604698082c007130b031070b83c94041c16441d50440f00903010b290031002400050b03035000c07135003a10619940c2605036083c03d520700c01103a80400c100380403015220081000030003034658217013030301c1240b8455a451b41c4000b002c41c219404080094030300074402814001c140020714007049024500300c07081540354134024100014040303148019600c4016800c4010f104440c4024003802d1440c8600000c0c5c50301c0404a5942c00021340541114100c20001744126102d04241050520f268400c40310b2158150406070b461105003069014070003034510080107140300e10308090910803421001c8c04c0344070b06013924120440260b140c0000d2454201c0006015003c403501c0326219409461a840364902c0c2a8410064 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 817920755 1250 817919505 817919533
    0x120906060607150903020c0901150206060402070f1b1a0a020f06060306070e0111062e051c021f0302030a181a1008010510150810050603101e09050603 66
    0x948070f580400990010f00418903044c101d24103500c0f04001508410010f001203103940c5100c032100c12039031203542183d01a50341c1c00705000076809068002860031005034501c0c0006001202d196080034070001e061000960358980d0f80707814000c540040711900c000015080c0c19540e05000e40009110210001d201e0760400001003550703070800400350400c07c002c69502e0304041c0e1040c09203180700800c280890b0b0341030400e40100c10602e0026102d201c9144010710f040000c0c00441d035800000c03280000e0015196109501504049000c4104200e81c0000900c0e01108611900382c5681c1040e803041d6801030312032504203680c20440340300340c060110070544a180c0900192041d06040141d441000c7c0c0170303015403680381c80f02c140003059420071401c5500f40000c20040052811009003190700300c159501c03044c4102c0d42c05486690060b5401d0036120300d655003e10031410400015900004c42101c5d04103440c0d0740b00c52001d111032460000c00c0710100d011004100c0d003030582c00340c2a00540f08130f002e06800204008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 817922005 1250 817920755 817920773
    0xb2208071208190c03020706021b070806072f0a0507030b01120f0602070602120903030403030501060306080c0d11040c180611060a051b0d200a120b0303070206120906060607 76
    0x4003c009081d192005a480d141c070a405845043d80c1c002d10a5440301e22181d000425103400c604056658420722030002200c400000b0700600802d00368031361307500074000a00720107440e90421049041d01d2041d06440c4100704820000440c22502840103440802e00750301d8240c4904a0680c0303c403042c202030550b1880030070b14940030420780310703840030300141c0d110510303d840c0000e070240842d01c0c1c48942c541c2e0200001d1101c08401584107078482e640c10132949c0c1e02c564080c1c08440081c0200c00c03580d1b00c024000c18940c05d010021410090103a9a1704a041810a00040968000500341d07030005c1d00c48000c040043c0c080b0000c50002e401a4144a944502840c08941e50340c08020841c001d10b54803040030411494a1904241c41002d200340c411307541d040c41c8946034018010484003000d0040b0301d00071016401e01107100b0766007040401d0703541d04040042081c2080c00380030a10350503541800204a800010384d6820014402c00050610300f90a40c60402c08003402d00200421540c0107400400c404800500489 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 817923255 1250 817922005 817922041
    0x2a0a03051b12100f0308031b0414060c0a0c0f170c010e01050f0706060e0915040305040b0d060801021b0d0c0f020907030e0f370b2208071208 62
    0x142c92500035989100100c0b40c00310007507004a007800001d41d0040140800b2400441c8035121542c81c01c4140d001c0101441e00501c81d901c103600020202c5190186289018070081c0a1017402504807042c140c969103602010b10101d90000c460f9165007401080090b0340484015841002c80000d0f015680d04040060250001c801d0013904220002031410000000780b0141c49034590040001c02c0010340781c2240c814288030a07240042c06110b03110200c0025140040e4461165900d0398400c1d04103403520000c41441c4c0c208001d12040e540e06e403000807034444024400751007084106000307454540660f804140c02d1241c0b00b0610700800407441c851202140c0f003044000b1a0a41c15280701d04140e80d10082140100f003144038586080c050002d11922020707000401d6000782541e40c41c10f1108445408403101c01c046c5014414070403460080c00e0764041110201055400340d6649094058040030070603150800742c0301001202d480c2d43c0400e9003030134030941c004010018440e9051500c03440c2407540e40d04090003981 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 817924505 1250 817923255 817923277
    0x2071d160903080c010b120a1104050a06121209080325031209060506040605010507020f0616050d020706141804090c090f0b0f01020a1203052a0a03051b 67
    0x30a02102a20310507040c001c000e42e0012200ca841e15242c680c91130184c0a002942481100b9250385030101482c08075420181d264860341c004000900c2d0028040549001090100c0e01a40d0b10b000264a001d02c0b00501c030381600c03d1054065848850101800d0092103410960380c0740d2080c0685490040141d41c02501082581421100c103181450308a43d03e03d00807004440351801c00208004220054000e54041e1008440502c8465281d00046070b2602401c20040d500c001021245241424a48000d0181c911403040782c450040d42608d40c9441e1500404c9031000583c03008004201d280e074082540100b030348000c0f01c10b5250006209038420b0064400300650f2046540769138090404c41040540002486064414408201d811484e04014019690228040e0002007800e801c25880807404915140c0c1c000c0207110103500c1c0c200c0072001414003c045410010541100404500010030302060700d15010714102c0c0c4c3c540b65104011309440014180c0d034a220700d0301c1c0c46c40c03c0c240301210542e0b1048201d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 817925755 1250 817924505 817924531
    0x11090114031009020c010213051005040603020c0f1c08100605070605070e0a1517061c030e130905010e060906070e2103042606040602091f0f02071d 65
    0x52070b07159240101c00c603440000710707520004000c00e0011045d005085d809a1900380e44080941e214240b00c0124040241400051000c010500072540650302404551035503004481401007108203d030301d400242d407820302003d0681d18000321391540c041e10099000d149055050142460300401501e00e00074454014406074490300003400040c85210100540c11006000308615541c8000400c24110300004960000d041416076890503030a000f0000d0280704041c04140203078041904c02521580c00201c200d04004141003480b841b03a40d400300380c0210f0088040006482611898824211045031580050f0b0703420075410007220400c00b04040382d000032135050850321000c02900003480004220401042c0e0700b00265081c0010fa0b0000192054941c001c1ca014844480d514289800110800c1c0341711060344a00e0004002400340d4015000408002d40780d60150404509101d9102c2300c2c900000c0d0028050150f8050f440e41c1c10005100204003682002d100200d44030034102c146840103000e0074144c42 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 817927005 1250 817925755 817925761
    0xc040506180f0105030127030c150f050115020a1119030b090f070806240114030a090605070c08030402040c0c0203071d01060912201309061109011403 66
    0x503000740c80d4124030034580c0140d001c0d180111203861100000e0007a9402507103020f4010300d052000c400009020386a02441961001c030303a45e401c65079184400d01c100e80d03c2c07014001c080c09031502806049020002802c01090541c1861032095903100b1440342c07031085600100c41d14000c200300c2d4100020191064810b2205a0303041b80c1039403414400d40d84024007180411041090000e40482c002c00310355810010303103121a5507007601a0791080155040101880b0205004203590362540f41c406a0710410f04009171403285003051042160000ca8100c0126a103a03400c00040013424070500754052494285004a2011b82d21102064080280000d00446e650080389214600802440782683e40c01000c4883d001e4076407540d840790b40c004040000c1200c901d0300001c034010340140103040a5403010742102040040e00c2e242c076040111a004a961580d1f0f68001c0313a819511000040c0b003900302400008a074100b03c600d4050b084445a00b1a40410281402094283da070300c04840c2d010040c0043d0000d0b1251 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 817928255 1250 817927005 817927009
    0x14010315080304080307200105031602070509040501140601021f0b0a080303100305060601022113240e0a03020a030312150e070e030106032d0c0b0304021207080c040506 74
    0x20031650888035080c880882c000a12510010040c00094410030042c0e407155026044403484040b5861068080f40090000606122103039580c1c0102e02440c0c4100c1f80d1540d50b5601185490340c040d541aa000c0e5101c1c545008a01d904a100b00d8102c0c1d001c0c401007600d0000022846021f0104c82080039096440c1c60881c0c07603954404030b0504c040c051b0002035a6890820140c0e5000380c0d0030f2840101c40f24029140054115800400d2941d9411a01301da41c070701440c000405460300d81d001400460005400040202d8450030600c61407807504d0344582400c81040d40400050503010a500c00140300313907102c50050005854a090b118216540342c18800440c801341e48a46d40035000c440d241c000d44010111000520390700700910300d40a10340941f40c0406c841c5200d0241401c1c0e40c80780c00081c04016038080202e0812003004c03114004d002400c4151003506400f82d403140c0b203411107540b0500110f04c0100601c001e524100130300d00f210300b02c800003d1900364901440d040c1c84a40c1403000a200380d0352100001c1c52a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 817929505 1250 817928255 817928291
    0x1602030703080406050915090306040204091b0605030a0b0405060f06030907031703101d0f1003020402040810110703020a030c0c080d0906120c09050907030912030605130501140103 79
    0x1455005101c982c6407130312050018001e0700081110b6108a10000000b011800300c5400c071264441e014001e0078141c0d07180d8090001030550001d00700c3d02c118880140d810110000e4052038003808103a9200d540d02d0410b05800429921100c00c1c02d4860b52802c41808556541c90084810b40c800c107840da00d40320b598031504d0906102d442d03803020b070404c4070700e1038510011800e5500442c484c0c15590028900c3c01c1d103d5568401d1180d501011028400103980460a50814080169400300e0031040b416039541e180d03804181641c00590000e565640a0900181585020300424030850300144441c1e04000454400035a250007114016061205810384d071014007050000d40d03c05801140e04450416030301c00401080001c8500c1081d0004a04400124185c80c0500402040c202a580c0d84040c1504000c00c2042254014240c0b405050380d480810001801280041d00450a1520001681490310040c0484c01d40b08104500300e80e80f4040043c8040103034180203840c0c0c4042841d00080c5400101003180b22 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 817930755 1250 817929505 817929509
    0x50102160302030a021207032f01090803061018030816240b150405150d0507080403170f0c0c010603051f0605190b0304112715030316020307 62
    0x440120301040c401490780010003080074035595030031034541c9034603880114418003030404010006105003500f40c2251201c901d0345400f821340741b0754200500041c0520302c1c1c2142d03143c210403500100d0100400c4060b1610022a288052003030500d40e00c1d001001d004001c45044030b002c014502d00c0003084040c94116580c2601018a502c107114404017240301e102250b030070743c0448052046a00300701c890012401d08005107500d89524078056414181007904101c5807080c01c804a82c1e01c810140b02c007c0b848243d40c098940110180d0302d664089042600740146981c001e91031118003d50243c003800390b01510038840c0d0b540005090740c23054070352040d104a1030241580c0ea00c060083c0c400c00894443c110a03404000d5020040100c040005e039030388206001e02003004440e9800d10968442040101c80c0301ca200855000344211286d06004442d00002240cc420750072948521366010b048404042040c4140140c10410030110b085e4101c140d0303000643d991082005101352490a083e984085481c10860b07080 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 817932005 1250 817930755 817930777
    0x7110d06063f02100c060906020313050f060f180f060a0e0706030902030d27030c090c020c1f02071d070f180e0606070204020a080a0e01110d09050102 66
    0xc02c82c41900c0034115600074501c0310041501941c1041000d00d5400100c484081d0390203016640b14851519056903200d2041e00240c0f00c0d00d0326100140c000035140e10085200d85254243d019000340c45003400e524016402450ba0400ea00420074031840060080e0700700d5021000c500341802509034120140d08050740d1076220380d454403401c2d0034091803508a410200c2d00384000821161490b90ba08821400d80c0c500c0a0080e4154000d2011181c4140c841e0b403461095803000206e1030400d4421014050204960758000e0340c0c400700000d01031044010a00070050500083e200808580c10300030005008070703c404070715015030203418440400031070090007100024030314100c11010007160081d0043c2d1039141211004001908481c10040c000d005881d0f0034403418203429a07282c500d0815140e000e4010000d010f07142c0c82030f420301c02540169214002801d0190b9603950314105801d1800b581425508000d007007503081d0f4140000c40d170100820364151082581c60000c00f0501d01911706106d0300911914401c45 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 817933255 1250 817932005 817932029
    0x708010e0f06040e0d2a030804080a030b0a0e0a0b0f03150612030c0f0c030a0804090e1005191d0d0c1104150f14090c0d0b040609090b0105030307110d0606 68
    0x1805c0540c0040c035940808041c41c110b10480c034405a044c0e050149445801004103200e01d01041c08031b2002005040c0c40045410009a20058440040c41a41059100c0441d520110082012007a0240a10020840140c0d001c0341400a10400262034014100740d4080304084803000400503a508410910880304402c262990b0706003624010740c6a02000b100110075124403145041181800607815480d0740e04051014203007824001c01d1000741001c490605580c0c8680840272210342118070649000d6081506600c52000b00003008600b03a90350641443d8440c0303100c03a81c4001d40038000c80c0c0807041d903030745250040d07088900c0d00e0309040003801d0b5040c29400a140c00c2e0100740c1c0d805505107e00075150f040905a8105580f010385403541030349000c1c803130f420082010201c1c80100114010380b00e0384d45682004141201c400003c00c2c110760242d03210100c2107840da20250248000c0c011f109016240940c051441c05100340c40d1083c6002c0308c16085802070003030680031b400f4050564800400740004e40045 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 817934505 1250 817933255 817933273
    0x6071a090127020612100f090b0f010908071202061605010204081209030d140714070510021b091902180109060c12110f0a0c0e0708010e0f06040e 64
    0x903000300400c040b40003054200b00700b1400c0c02c2c2035488105011690050616107440003a03080c1003103c0c4000b500c0c0714070300c400b0340c400461402c60403440744010f022180d01c00284100084204452200f400020300d0500c8040002440108408070f03400044c0c45044840da9030042591000ca00940710703508890007404c040c1050700040003c190014400c440f80c1c4802c850700d0b50b06468400b602e5101764104580c1c0340d070100b1700300c40d103040c01400b080260b80c0e00c1450301d03400c011480c0c4803405a960001a0342d007068014007424811860302074100d1b00c44134814401492045803624010f00c105070383c06411b80c8218110710014038000d41c91050440b030b4414004040d51030700c0010298108044d40d04401d1800700700b0400011035070a1044040d40c3c281034000042d8245107540d02c1041d038548001008198460246c1d251496040c40300b04502440b03984036240e00d9030354034036000000d001040b0183c40c540802444000412011040602c0c40d80c001c0e500500340e0382c5603100c1c80700060041c0444a0b45407914002d803144 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 817935755 1250 817934505 817934521
    0xc030d0f0203151f0e040e0d020a0b0703020438040f030201080114061b0115080c092203030e1f0902040b121506031e0a03020d0c0f0206071a 62
    0x2550141c800c0300102071400b242e03002081030360411100c0e0350700c0e80e8414080d500e00c120301c10405c400300d4690180001035070601c8009803a003170002c1c0c1c52641c030140c1d011015000410601d40200c5d0f900070b01030b103011410281042039040340c04810f80059400c2e040c0e43c9526080300920300402d5031141141c0c584460ba40d660303c107400a0b00701c0c642e00c13040c1d0114103460000110b0755480718000d884442d004000e40d2610f0601d0900c41401060f9142c030b40320301c0d0350316050800d0340c0c004030b950b41005e031007803000820200140408000101c0402071502c00a54204d0043e2104441d2404101001c2a0b060801181a03030444c00031610741050351b510400c2e10300d51b849103980f41c00029480140310a00a480900031507038080d080c01a5401c081c444265685d014407401c0d0204014007061a40051004003511072204400c0007402d43e180031001520f24a41200c1541410160104030041c0c42d1151800c0055041c0c900b6250011202c000e040080c0c06854006036080030804074850340032540003500814810350900da04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 817937005 1250 817935755 817935757
    0x7060c15090318140a0306150e2a0a0903080c01110f0901020c010c03080c07060e010609050603100c0206010b0c01022809060c210507050118060b100c06020c030d0f02 73
    0x110007000c2ca01c00f5401040d00341c11142c0b881e040c1100078103080945ca107182e50780c400405ca035101868000181410200345070741c0f00608140105620802c8903080309107003c000244c0521030480c8400c5001c10040099015000302012003201d401544061700d401d1020030103030141c4a03c002c0805140c0e800a590003082a03003c0c00703059007080031703800c449100c41c240005440c070744143c0601502190611000807007a01c11403005051292280358082408810204800e003990503a80040302c40703c1d141c4d010403d09060400c02c200052a50740414400c0e150640d0010751500018064000031b01000160314019660940441e087e2020924003140882490408402181d14101c40b80e00040c0300c0380b00024456100d000340020007500402503038441c81e81484609104940c502c103040c2032100500c24040400c2c02071185009180132040c441008082c80c3c0b80c040300f1500d031380750140d200307009100c0041ca1855214030340417a1154800030050742d48003090031140ca18090016150100c5040044d81161714805030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 817938255 1250 817937005 817937027
    0x30b0a0b100503090d0836010e0d0e10140a110a0515060306010e011202010c1e020310060e13020109150804020315090303040b04170403150e0307150507121406030606030606010207060c150903 84
    0x4d0350f20401c803c10bc01c100b014174501a810301001405c51740c254640341c0080002028908560305004140ea000c003108203040c134100020540317641c0c0180e5105900c682d403100000da401207003100a00044d60401481109000041c0101c0c000440403003000411a405051211407150b088031410940503c51646642c0410840c5812806070240200040507090709010344025200c1d00d444200b01a80c0782c0c1d0035049a008120303816810001142e900150310034500582d040c9090803590307100391500e06030041c146040c2c800e030158070340710030b41004202100700040141c0f5041940641c950b400c2c2d894a003410125203503000f181004032100040c000003000000c000292099145010070302407094048403403616809000700140c0010300c1c41142c098070f894550310a990201c00c07410244850f201201041007100c00003400c1d200c8038051002840710303900e820850144d01040c110014141e516140740001e491307103160303c129001d003c4810490020070005140140c0648240c403010031145c40701c0d0900408401d640 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 817939505 1250 817938255 817938257
    0x13050103200301051017120a0503010f0b0f120411130c030612050309190f09090b060306061f0e0d06090308010e040c030b0a0b100503090d0836010e0d 66
    0x907440d8030308242418081d59120707807407a401d0540058070b040380b0700342400c0f1070703a00745401409856001c1044c1d07881c500c05000e2149444e0350380e80c0c90358100040ba0314486500d13006030004100a0014440b1818030504a60f400103003601070004c551100e1034003594110200042e40d41c880c005071801440760180f039010341d0300ba191a035824000c0316a03841e182c0d05034440281d00900142c100b0084840c1c1750910f002000090041d041d1a680c10f140c4d181015090304c07401390003108843d40c50340302c00ea007440292001c0c1908140220068030013403c03ca000181c00c0f034042492500428000303c0401d07100c80c01a01103001c2ca03100501082a80c411902e03081004140c000703402c0700403510710030020907080b408452292140380d0102d0500e005904507207403003e021000814140040340c640c05901c510b600c40c1454204c441c4680c1d00c1c0d498490600b4402d072400e001103403030300b0410452a86e0030004880c07603829459104c44100c41c500201508407040b1f58142042c0703280035400700d42c00e0425060804500140400102801e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 817940755 1250 817939505 817939553
    0x2c07080618010f17070f081f0b01020606040f0e0a060509010608070803090d06060b0c0a030201060812180d0b0117010b060702090a0e1e03030f070302070b04060b13050103 75
    0x245030420340c4440028050b402c20000165001d01240b626800c0b01c1201441d0031044441299030b600180c1006d95031a08005580c0d0000c00410800300150180100d4019a5440502511855800003507a5403001003c80b4031a5840e1a444581d04086501c4070000d00307180029101805140c0c202200500b00a64288505620b41034000441c80c401050031010348841d480590b180c8441481081020415404140e0340107980e0a000600e0b800a04000c040c5d00c881c05014000051542c2000303402c40d5115032050429812622030300007840f03852070450366105c003040c00c000144c008801c04a400740c400c1100040807404d0010000c107000302c3d40e121020384040b101009000c103a8030b1106009039801405070080d080010000443d6032022580c0010002c4404801254800c2c02906003581c05000c82420030501ca800000500503030041e0420341640c400000d0a0075813400013544e0302d00c44001e80043c0060301075956081c603015160b0f01e0014480302c14008410510640d40c4900b0903044942121142e0214111 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 817942005 1250 817940755 817940779
    0x717070602030405010504090203100e070f090f0501210e032b0c0525050319020115241b060507081005030c06090301020702040c03050601140c03042c070806 69
    0x301c0041190180c48060b55443c0c149440e150070308020790800341c042200001341c070070041402041d540440740300322841d0340d406d15010000c00c0040c0205d456038000d141c520382401c500707002c02c0e40c200d01c95600303000a034860301d220201c400c02d0b00c00051048005c458041d0000003103240005040400d440346144010011680c045c409030000b108441d0740324800380c041181880f2000e00403040c8500480f108200c0c02031300301c1c0c0e414140d9480c0d041d640011a5060002c3c84001e205d104a0303424411402542403401c244a022403c181c000141c2d8101c900484c1081c014419065482a11441d262070304c881a410307030000c5604651400c000136010842d5400700080d14200042c40c510032542d020011250040d0150100c40c289005010b030b181d02011460b901503408202440050700c07640b0842c80b030303500319980c0020241440c038001488186e1a00c9034400f403c10a001c1c114180101108960488920701004810340c054075124041d86040812940614401c0720b08002d007443e000300449201c0c01d000c46140100c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 817943255 1250 817942005 817942007
    0xe0d03020f01051509010e0108061303050c070306020d060b0c0a0f02031e1032060d02150301051c08031f03020d050c09070201020c0a290103050a030e010503090d08071107170706 78
    0x2a424030480c040f2b41e1000c2c020032400344203c01104407030740c040d103000340c6000301c2400d50350b18048450b80211013031a4002a0303541c0445c114070501014004260031103181011101204c0c0c1d03103164000000c0c0144d403003d0546401c55404004c030345102d40034808011900c94082000e540c480e89103040d00e50000b400c1841c003508031022003001c10342c910084548801d1003450b028200100c404028201c2d5000808031510401680e078a1079200b10003841c20075210f96940c1007006210f1040c940c7c00d8021115180e08500c1d80003d11b046d420340394030007851440c11450207240c1d074880181016680c006900601429407880a00c80301150010704d51006841e604030f00e4031550001ca080b03104400c0050059001304108000040400c800b03402c07400d00070071f41206048015003aa00c030581080e0f0044a26070301ca55081da0400d0740120040c0c02c18442401c215007985006480b968031040e000166204000b500c50008a1840c01100c88241c201001d0341160281d0741c03105d0320117030152458107441803644241ca81c005092 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 817944505 1250 817943255 817943279
    0x509011b030f0807050d02180316030b0a0207050a1e02040b27090102130b0c010513080421060203090109140a030e0d060917090117070e0d03020f0105150901 69
    0x103561558480d03441a2070880c0c215a0418094203003410844100129501c030381c01400030b0094030540032501c1c007040044408042c03602c0c480301815010394003220170070400b0603101100c050780301404441c0940d941003a881c00504000c1d110358010407001c4440102c0307510740500f00305240c03100c4c401c0c0c40c01c0001c80e2110b000c128108100821803901c00903501034a00e2442c200c1d825041d00b01c500c0c5070000d802d202041e4031902d9541083e0301320881c01c0c2d20104e20842418024043d464105240005481100c03100d41c48000c03e0b84a6802444041511025180301c550f8880e50414201504024115141d0521140c014040c1a20781400c0c0c49592003007020488050010955100c8035505440d00c107412034005041c0180324440f1601034900035541d101f40707408500c600914000b0b8480812100d40d948003d03400240506a04420520401010304204105541c000032042e801c03010072284480c503000607190032441c104100c08130002c65404c200c2070052a095410550740c9070242160842840c5e038030b868215000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 817945755 1250 817944505 817944557
    0x1b140111060619030b07180b07080f031f08060105011409090604051f08030307031112010e100803040f0e060306070c1212050f07030f0b060301050f1f050901 69
    0x90354101d10003050b458500009610503007515603110032116590707512100000f40301260360f41c010807249001c0b100001c140383c8024000c0c0614140040c280000c41d02c0e040014007403c03910403040305000001c111113400c0724a4440b083c59026014140d42b81d141d2560355200d403000c0c49118045183c07120030304008440c40b17003039651106020340581502c1e62480c0401c40a070030054154890031030f010000401107005450b007000600804802150740b030904450090071102040d841c505100400c0c45609507101c0d4003480c00c0d0440d80c40f6006180a500c070f003d8140c0c0e160407203a02c12041803000103400a04040c402c2e070f8000c100c400c3d00b408080c46070b4591060540b2120121030310000140304540207400181c1814440044151b180f4052400f0702d0074070243d900b01c41e4140d075135420418030f0200b04065140d0601407243e031002080340a00c030129601c004a005030106004a512a120014000303103030303460320801001140c1d10030b03411103c0e520045c80c01524030380c001c02c07066000602960400d0780c458002c3c628050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 817947005 1250 817945755 817945787
    0x207021507030302040812030106020d0801062c0a0801050402090105091b070f0c0603091b151b021c0b060d020d060b033417060c161b1401 61
    0x105244200c540ea4140d02051048041c15800e00c800300d443d0300c0c1003143c00d4404882e000150303901c0d4100ba4010b8640000103e803071080142c17941c01404869402200048c00c2d112240f00d01061076074010000401d44400c0038401d800020310b04002a0908054101d80d0086009840d92060360740c8803420f100b4455400c0f03a2440f00c50324843c01c02e1200c0107051004040b2203008980090f0391000a540b286a40312180e413240700002e4481c0304c02018080380001c140e002c00000c40140010a03d41120390441508a4404400380003d078210040f40c958805070405038a5402842c0070300c5031220403c000c0c070261007420f06a52803654000050400e0030300401420302503070024242508011241c2e2000c02403d00078404075050300500140d040d4400320b25289000b0702c607410f0701201c80902c0314143e0420038202640308030045498583c400651b01d03000710340d0b02e401c9880304260780e0703454541d191080d070b03c0b94900f600104600c5840003140b81511549102c1000c0d00c0901c030070440c0c44141c600044403040c131000c0300d0107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 817948255 1250 817947005 817947019
    0x108070501360302091f050f0607050105040b101a0906030c1902010b1e0a030803061801060f0306121a09010e03120402040c080c030123060a020d030c0201020702 71
    0x1104940c06001500c00304950001e440c002c0b21180380c0e2201400e0035074100c160403802c03881c0d001e008502d0103608090340030341c0403a20034080f400c81c0d00801d12182c3c0300307108090062104507903c0945448903c202d8a074650040d000340b060703080038940f04184003012940b440b1940083d11001c41c41c4403050104960344640c0f030446a04020044007009943d6201901141c0705100400400d0041c100094103692506503a0300002070149444091000003412034201c0d22230780c20115000b4450b0b030f8038011083c05403500300c2d0203180c407660340002003040d210901548110300c0c2d0901c80005450740d4805980c0007225401c2c0d4090100c40c0e1303240c0e0001044982102d0003000c40e050700c820040e40f0401c044a09074007030042c0c400400d08940c04000541542d11503030a91001c0c81800713081200350300b414002c01100f40e43d9407800c05101d150182090403140410f005c0c0304203000046044040940b01e60080c903c00300002840159a00400e540180d80e9034285502c04002c00d0402d01110039050044c030980c0c540ca90080e10744 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 817949505 1250 817948255 817948259
    0x10150524040b1605160602010b0f0a0e070c0c090b0f040c020d12150605040e0108030307020a060c0e1005030403090e0c040612060f0e19090305090d0c031424010807 72
    0x40841e802c0f542d50701424000714030045002c140200400a03032410991010700d805800d10100909440e0b000c014523003c2c1c1850350744504240c5500701d07010100e030f40003020004a502e4a140c2114aa00040720103001c1c4030b1540004615060300b42c3c00b203144044200c0e100b8041d00c80b03140c140000da502500e80c0381c002da000040781e0400c0314010241c820b4503205201d00080c1c001403503031a01301c84103d5600082c0000b9008141449240e100981240c09071100c41d0003507086d0300c2c10381d40003591203000a1009203519110000002c056008007400c0c004100300030000c0100e6201080028400d400c1190140e000410314176000801c02c0e12003404034003d204014641e41f0301405c001e401c0d20350110f0705544c5c0e01d8269960800055030034207842c031030f000f0f000c60b16180891810310300006030600080031448030945140505050000760020112008030703000f0b90b0440c034940600d04010450f180f00f0740c0702812940c11440c0d0080003504c080740c007052a000014030000c02080701450403861240074005d42c07180d50311041013 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 817950755 1250 817949505 817949519
    0x1507080f070905100e13150b0d0b04020f0702090f09120c07030812040210020708100b0f0a0612150e01090e070b2a01050f0f091015052404 61
    0x1440d921919900340002d10a58440c049600900340e60004000560f02941d183d08130300c0c03c41e5090040070340c41002403140c0754203600402c0c21203100d440745001c009400250700d030041006801554004400030401c544400c040c400105907640b0034007007284038032050000075480d1003045078224080c07030040000705043c4102240140e070a40c4180c9090800c1d2103500750000000307450200400c1e460b40002410b44c100c1c10544140410301d074000c0b0280045d904005d005200c00200046e81c4070346610f40d840302142010000303012900d18949000c0d0580c014080c03907008150181c01c11400700c0d2400c2e440f4810061111000c007041d250560307500900c0614084180108000311040d00b050102c0c0e00428107a4020590b6020f0900341c40e880507010304c81c2e0401414880c0d400700741c02c2941078030802c1464003d10075481c1120405048050041603040000745900206820075401c028600f118282c040081282c150781c007aa82d9881c0d1040e00c105072054841c80c101740b501d007021001c648503a0180d10a92424182000c00c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 817952005 1250 817950755 817950781
    0x2191d011b051903020d14090603060406050607030216080102090a05120102040f12050706030c020a230d03090b0604060312030903020a150219140403030c02240309150708 75
    0x2000003821000c1c101d03410041241800500c40148082800000614841c83c010742041030040c00302045c865594810085101d00e04222007000e00104c807035555a43c1d4210000b8003d0400d60801790f00104045420700400d0340000300300045039441c0d0410b003281540d40a03114203030310031411310035004544001c0403c40b6080c0040d0301e1007a000c1c440c002505180c0c44030103c1a120800b0340c03100e5a000f061b01c00c400203201040c440c840c0600400d02e014002c03601c06072801303907940010a00041154240014100701c10780202042000c2c0c00181060740c034100340e0702c1030045c0503081d0a00181c48200b1400702140c9640340c14424102102e0380803028422081d00040c0641c010b11078006c0c183d0940c01040f0b020f0303000174280ca002040312012448011307183c84c4200d55030440f0303040350b000503400d0007603138407411101044403000d84045a03810f03c1c11013410b0600d031003c41c8943c014003402542d0800654000800c40c28010055481940040c1c1140d041045c2e282c0150b604074829035544000c0b62a43d804103241307800c00c01d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 817953255 1250 817952005 817952027
    0xb0411090d060905032107021629030a0e070909020102070b0f0c0a150f06030c05041e021809130b0610110a14070812030c0c12070602191d01 62
    0x55030025907040c01361507480c00c5500c500400752001c0d1321520402c441c0140b58410a030801d203a8401040050116044d8800488460096010480c00d50070080c10f0300312480503e25007039544a001075120b0800141704030140164030403e0380c0900500e0303030124110207140314881009805038020079420b4a0a1a01c8089501894181e40d40c00000c11501004d07910420081900a104680030441d07001150301d25000c42d518080310f1500e05081036010004a8840070404040d41d2085a00207045c140c48944450001c1101d00543e0580e03002007250f560039194441190341050042c2d800362101d503290341440c0c1541c50f043c01c0041c071806010010400074141025022001e803002e003000408036004540b500d1a0484c21502115161052001402c10400901100c402407502030002c1041c1c030805510781004d400300601c1903000000105659078200010480c110f2001d051290b40f40d0745000d43d013070400196005a40d050000540228608407a610405100290003580445004c40032944401114815000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 817954505 1250 817953255 817953263
    0x80d150f0e0c0a0e01120905031305040504022805031f0e060127020904090f14070b070204020c1906050a060e0105030d110709110304110111030d09030507081c0b0411090d 75
    0x5281c800c04106d0b1280102c25400b0700000c40c0c030703440451a1f680da405e400340c02c0310340114101428080142c40b00707a0390400003800040922403c10381004104811174841d80a01e5240c850500643d00104081c0450810281c0b1000c042c401d0824000180359030320000c5c0708280754910600c5411400d10b840804450802c14065000740c030740305c003d10000d400d603214504162201003120309101c04015100c41c4160440800390050034030649801a039007014000c49401074040c6400046c22800c44400740b28003000c81140c1c03260420700b030010b420420010303c0c2c1141c085038039910b0104041040001640c4084c101c560060060482d8010158115140d405040e4080140c2c4500400410440d02a0143d4006101804901c0707440380350038100f4201c06840030410505100602032104022035000c005c0b1313000c201060340d010645030300f1803408a0321403080703600103000344001140a04000a500c0750802c960003154006001f041100e0040004450343c01c00f031503005440c00c0003c40200d003840c0b0b5807011000e010b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 817955755 1250 817954505 817954517
    0x90c0309030d0c27060c020d0c05041b020d0201110703211a040f020f1e0f0706021803060f150604031403040f210f080d150f0e0c0a0e01 60
    0x10b000901020350b0342ea4450750011a2007046959403510501045055881501e54040c4500303117032900c05006c16841e00c2c3c0190049202c041c014092125034295180186000f4008000078804640c5091040f0001c01030b010050041d50300703484191340305000b8400e1302804804080e192030140c1d40c1c151612010000f021040860815980103001c0707151103a00074243c81003c405c4144072024041104943c0c003010407030452441030007000700400b028805e68001c10094641000303080c039117220184960050700103004110300700003038003001c000003900541407540a010100094040107410142c60b85405c580e0388150b4442080002e513034000082c101c03550010082d0140f85003680b40d481d5012000307902c0030300304a00d83c8002802c02c9051000d080840017019008941e603600023540303642c3d691100d007080b0003402c01010210120203208008040303c0802d120044100b089001e112200c180d0518640710b5060080c2c0c244000042e19048260040d105040d1a854030345481e81070001030f58003e4081d0620b034100701d4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 817957005 1250 817955755 817955767
    0xe150f01110109061529030a0b03070b040603061a03071409041e060602060603120f070c051f030c110307060e1204090212062d040b04060603020d140105090c030903 72
    0xb01521603105214852030030400c00030b0414941b03210ba02d2148078041440c03a01c550000811484e52400c0e0385e000f201c210400b040124807000064034102884c0c01c2003508400010340000c0950300f55215108a400c1c9013103901d03000f8614100c0461a0004032031440101c0d00f8001c4500314500e42400500040c100180009590264240c1a40010505082e0741003210368075902880115010000658090000c4005100010008891400030b01501f030f14488414004500002000b41031120040a04409030200d15a01000396045107940329090304040460b1a200a03c41e0841c0321700100160360020200840c42c0c4a8a036032154010500d14481c06054068040111500244540101300801d1405400368403107009074180302e003600c1d0240540340b02d45084d440d04280c1407814007000344c0e0100e603070602e0031006400301c010030b01802d01c1c811440e601511704031011801d01d4166002d0405075084150400110f40701602950700ca050a0083daa408070100c8001400c400f10440110740c08003040d4103490810f4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 817958255 1250 817957005 817957013
    0x30d0f1805010b03011b090b0304060b10020a06050f0618041104020c030a11060714032e03030201150305060f04050a0515010512011a040e1f060e150f01110109 70
    0x2401503441152030365120f035003198007443c00340a400035420444489061001e0054406411b0307504c940320305802c2c2c4138040001002c0c0155a40300c4101441e000c1c040300c030b0016501c50025110004132804031992440c150100d8444c3e40c2c5400c105109081c00f40614104403c19000715001c03480044c801c468500e1040c00119003529203001078288054050011a100c01813a42c0c00f510a1407080c0c0f42c070341150700c51800c01c035406a001e600c004d00b02801400c5d83e0303980d49500798100c42c2d212140c0c9404456443d685a05501d03a0304071100107045a020342d00800401380c035102500c181d11035501c40078100d40d001d000443c186000c45450703540c01510078000c443d280394480e030b10359040c6521041d130513000d2214040104002d01300f082d541182c280c1c134070008011075042d1180302180140060f00d25402030781d540c402c4640e03800c0f0810000e01c42d0a80c1e00b207540303802d4908040620181196000e0420704c1c03083c580210f000080c40e8055540e0003074005101c108210303058401164075203002600b505880d0f490b007035484082 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 817959505 1250 817958255 817958291
    0xf050d0e0f06280c02030714090f0405010b0312040915030c031209030c080c130938090616090803030403050d0f0507080103350307030204031203060305120c030d0f 72
    0x1c80c119211052031350f54600405091650340c3d402808c15046074800c00c020f40d9181c1c00c1c600e5110038260100e5001d07840e00e00300b0900420021841c7c0fa018441c1c4148803400c00c00e44406441101e400c7c0009000c0381c2e11128203110a0000d80c88000c1000601c2c0b103060002980704006111380401c14542440b080c0e940391a42c501201003648028003d40001e41d818040c0d0038504c1780e0108104c81c43c0b00a03c03a0341059520030741440320341c5560121110644051303000700c184141044544142d620032203c15130a05000d2162150802d0301d0a180292162107031f048030340e0003246d460382142c258402840c1540d40d6a00c5c180d0340c5a003d07415618155a0b541c000d200e07218030921825015264030341c3c0d403004540c1140341a0320545206c0c007201a000d00d021a24161100d4016103000806062490864680d200c1610540181c0120f4200410400048441500c074642c582e00240c11603001d1811a0944024000c0d0420940b00b40440221507400400812045110580050300c41c440c0d00c1c0000901c0d00380f040d00040c10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 817960755 1250 817959505 817959577
    0xf04060c0b0a020403030e0f03030d09055b0603051f050c1c0e0703050f0c01050711041503051218030706270504090f050d0e0f06 57
    0x42000090304100744041c0180256000212010071807a141c02d41c0c801421000030341d10414071032030030003a200865850500075600c82d1750f4810014894129145400e03901d603008090004400090103000b07180404541070b0700241822025809014208402004010035540090700b0350340e012014110842c980d1144240300c02503003d1400303049601c0c080c80020311505181e51100d48464184010f00c02c28441034000c40300d41070415503504489040c6409400e0282208140882e2903005001d4004188440451449980d00440301944c0c0180305c041c0040d10180500310007c2c001011203030603004503041c41c1d401314105012070b40b1107100c02540e030750351380c1e04d07010031010880001e143c0130804140d441d8014030000036418084001e00103003410280003c142e00744c3d1103000c018140c183d940c512809400d0000071809000b01810038002c9001a082141350810f59020458483c070a04204d12136051040c400c0c40c100340b900400d0804100c0032001003140640000d103500209400d506c680415040a08101c005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 817962005 1250 817960755 817960757
    0x9030b010f14090c0d0e120f09010f02030f040509060102100e0102130609210201170708060f0306040b0117010f06080d030b060c0a03050711090f160207050603011a0f0406 75
    0x440c1c90418044030764070100e141846000d00708007002e0015540502040c0c842c4c80c0101080000c0e243c000f90100c40c81c000a00241c60716400380040d8900440b0300f440010600900c00381c9904071100a038441c200e940e403041200b034250188040c0824050f600d400845a03400a105204486000c0342c00300321001242c0c0400b10100301c6d69400103001041c03588041c80c09006090324184400c03401d1500c4e41c40128a40101c00d03c1c816007403001420011680681c20007842e8545480b1040022f18000f0b03400341c203034002035562034442e01258000031940d141c0081d1442c031980e0310204403411039190100030f01154500b449074403020b54a412100c1d500c030040b4415180103082840050228600c0510098100c61344000e0390b50080f1020441040c03000d4001440e1410310741e142c0342003a0b0b00c0f40c1500b0140d103100c51036000c4a41c030050000c04e110f04020ba005850740130b542000c003001418403080901f66602c41c0c00e40319154100206200402c41c010280c18440482d540c2d810041c0e1401940950501c11984240c0000c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 817963255 1250 817962005 817962029
    0x314030a0504030e01050702010801150c080d061e03020d24021201050a0603230907050a06050a1701080d0e130507111c0914030a060203010609030510060605070206070309030b01 78
    0xb05055201124030614242828040c0c07801e503082c0c0000f03080c41030501540f502001034146449046219040c1130002a8102600c1610340050030b107608054140c80c07045c014000c50324807503c07840381d404c90a070303c2c100c1c0c0e03005180042442841e900c0b542100d1020324070b40d00c010150f0341a68441503080c0003c7c40366000701b20942c85250305100400141e81203a4000303c00305440c19181c800c901840c1081d01011010001d4100c0c3c560f6174104a4501d01021074104603042180e0704000502140c2141c0504030944a0351076421740c50041218180d440c2000344520740da254042c40344002028000c11900c070550074090480b4210b09205040401039800945075140068941054801c034513100f031110182c02413030950003417075802d0740302d900134148084c2c0d00402044880040702d014156031f0820500345039551060040d5181c3da500c8601428031200e510042d0342d140525041c0b0740c0d1086591040c1c0003981e4041d00c680c1d06144842d003d0001d01d0f000800100e05120010201101088880303098500800c45100d000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 817964505 1250 817963255 817963261
    0x9082a030c0a1d0a152904060f080a360206070b0103022716020f07091e02161e0503030420010813080d0b061602040b060307050403020d0314030a05 65
    0x210702c1e2040c00911035008640780280c001051021175080381c0c101c40740c00425100c01d10140325203124011184004840348440060001740d443d070071107066201d4040c0ca8445100701c0c0c1e16040c54100f6607280260f0924003009520003001088411725198014204840c5000c4501c1e54a0740850000c2e44aa83c0070340c1d83c11503000c01081140341c5002d25010040c1049440032800c42160502040a071025119028410500d640000c0c094400c11000414860f42c1084420b03040e0388a52800007003035081d081d045550300320b15980c10505224001c5500d0300780152000c0c0c4c081902c5031112030003502036220b8103030140b1801c840c94010030400c00117175001c1c9002d10112030304c0ba4640d480c1c40c00e42c2c4041e00841418840448104024030521788403994255400644140c0d0320409104008020801c404085510070000308501e19540b88140120405600c20740c0d04101d100042c008021080c00101e510b0b00000d0030400c030a20041c24050720100300c8500c0703820014541b002c5200d0700151b030f8004581409601d507840d020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 817965755 1250 817964505 817964549
    0xa121401032a03110112090b0f0c0a0806040507090b03040c06031d0a0b0402030f0a03051207090e1f2d0902041a0c0c030307080a09082a030c0a 63
    0x803109040c450300c07001418118404503440c0c01503000d44401303410149421080003d50740200c0c00d13031008031844030040181240919145510203c1903480b8a070041034600091036148014040f16139030552506c843c0c036166280420080545402131003001000076400c0b001031396540c001c02440c0114400c131542032680782048401411501103c008100030b0790b4520a80d0450706000c45c40d000c0307441d00042142500ea50703d0002c40c0c60305040e050110300d14803074008031000345a805000b0341140b5080b0038016005407210041200c0c3d1801c140681c000c07180c240c0020071450801208982d4144000c080040e54044d62522410b124109100790082029440d543c134240c40d0600301050805420454000c5041c141001361001c003605ea41003100c101e01000003100c09510704200903400c025a0001c00712030b55031b0b02c0c40c6042d000da60031604d001070100d20204408a412039010411400f034455580c2500c04c1c0d5206607807100c000c2407d80049640601030040700d0110340d2181400715002e0a07a14602189a83d0400c0c2c2c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 817967005 1250 817965755 817965773
    0x503160521040309051309020405091c0f031b03020703020114010e180a08040b09131107230f0c1201060b16080f0c01151d0c0a12140103 60
    0x5804420040208070140d21400c8112440200007020003400c41d60381c0d920f15058030301844540041c1d0380601c15801440200c0341c0e940284200620a8905000548070001d00b15654184910210400c8100d00065507d0030b1003002400650a0103181c049507880c01010303642c51200810030030300300194000171130805060b024041d00b100e600d0342c0302c41c1c0c61180d807501952420550000d071040c9500c5200d80c0c1168240f003c1046030540d0325401c500360320359655851408010701da20651140c0d0040d44e81c5245611241d4443c40384098551686040e00d103000d0740c56071511a024101140703410101890f0b42141c0f511001008414202e0111000030940e200010040146c002891041c0d00d1840e814003005010321901c2384180c80301012020b41107405450249011516030054401042c050315001c100200f01480c15002400b200720300c8000040310035100c0941002000c030f110a841d071401c00c2107000c1031a08404070000c245041051070070220000302d449482d415502154800b160001c030210042c414440c01c16 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 817968255 1250 817967005 817967041
    0x7120f1a01030c060c050c040507091e050f15030705072d03020111270d12181a090108060f130f06170a20091f0801020f0d091703070503 60
    0x204000411700780554489035a050107043c154012520350010a04041c002e0311814050700c2100a01a10141550205c1c0e06101329403003400d00c18100b001030041d981c2040c443e0b026988858011191855851110a032610303482080210780010310b07d0440f2000031007100ca054525505034508070002e9186080c02420b450807071042c0d101900c81005404811803200d0344904002208003400d136946041c03c400198004243c503000780c985c01d10740b074110700466800303d540318030320031109806010103407600c4500c1c00712694a0030075101c1c18000c2003003a01d03030340c055148141d20260003012500030880b8000454140381a0f00c1740c1005c0395844d205d4000101003980900001303090644640110541c0e0701c2c100c25900c0203440805000c2d04d561800480340d5921100094007500000f41c007080460510021000c5442000d02c800e2000c14445400070810503030600840c0d15024014034418140b1030425445001040c0602088651400c0502450107081d90030020f903128a54940301d42e0b44900d002d9040020941d00c075 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 817969505 1250 817968255 817968257
    0x60203281a0f0307050112020403060c2607050301030609050709061805240108180115061b0201081503240609010b0a05030a1a0301090602180d0507120f1a01030c06 72
    0x100d108140d500c0c001a640211582440e100041030740ca5407c01009114980019145a05000c0d5240307580b07400c44020003803460085d102c4089982c0c04014000d0505080e02e54000107001000104003140d03580d006001d0b441e02490565400c50380e9901c1c400c04403403041e8419015840d01c0c110400400c103041c490168421024050042c42da0840040007000901e51900765040c0204000070480000c0c480300c00300080c00e8200000c0080501c4142d943e501000c042c41502c000600307412003056400381d02e800001c3d00c0755043c7c44201d81500d400144007594682d14444c01e41520409041400c80c10007149460a03001b030040d806403007800c0040500440300c405030440c02d1440d00c2004044072150b84103084a0b132000340030000051442903684030240312560002002e9056003402d542d203040c032103107900801800001c6010120000041405d000c040505943c02a02c15001203c00300904003407841c5140a403032041030011484d2005a0702d86440c8030808021494280a980045c410010180c20000140601e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 817970755 1250 817969505 817969519
    0xc120a15120b0604180605130606060f091415040f150f020c0609010c0506090708060a2009030102041805040c050603090a030f0516211b060203281a 65
    0x1890701c50482807900a440c2a000e02e071740700f5046203c0c025049600340d5140e4022001e202500b04001c82140f000c01048050b61242d01c0c108001801601910000c10700501988a45039410320300520001420003551811303030480c3d034280c81000300c0caa200000700042c010304141102c540e1304081d00890b00710000d05030401400501c3d030b444074890740c00060b045485001101e14550b00c030051710040702e50b0004248000c04500c521410712001031400b0032050280c0d103000003140d00c283e0f10700042900341c4110b140c4c04054400200c01c085500d4200100034000c100c0c014001500e400d680c0d140e260440c0c5203245069820683c0c07082844108020400070000401c1d08682c03407401e5060614607181c480014640c02802d209000085140342400b400584180c0341401c0c4182c0c401701800e007003a5858007100c140c5100500366040c0030000d55406107581060840300100c2c0806032860a43d01c110080d400501300717040c0a000040714804000146c190407820f0f202549002c90354004030301503400d1074054440041c0c4074000c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 817972005 1250 817970755 817970789
    0x15091e0603022b060c0503160e06090904061820030c09130515090f1204062c0d0f110906060a03110702061917010b120c120a15 56
    0x43c8443c2000904070041640c00f0218031014581040c54000c01d500501031803d004042804a800002035842020003480904900315050800c17980c6205a14409912280c103000e40d401600341010120f0b442441038900050910145840040c07070203401404441d108910805c00d403e19040c03800719800aa0142e00500c021064a4000fa45000000f0710078040c05101d1000d00040c05810482140d098071a04840400c50a1040e526511407400c0c0d0321152052040d5949019964401c1045808560a55644620003004021615205c1c5500312044144140001410589a44016211800c184206c6400601c0d0740f01c0e19041d1020030311425050320030003000003085256154030301160200701c21032500041080040c1d210104074000c00e44041e400203804182031b42d21503500c4990070548809a192400f0040000d20220b00e1484e00340102c0042d15014000c42038044904020140c0040c4110807040c00c0600205151b030010204884600156071244540b4139001820319940014203100c40041d81071070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 817973255 1250 817972005 817972009
    0xe1905090c13180602030a15050306060105030601020708100c0f03050402100f09030804080105010806010e132013050106080a1829010e0f10060804020f0415091e060302 74
    0x10344481c85900402d1003584601030504140d018481a1030902070600030320060f820003400070b40080722442072003490202042c0c0e940c60725200303800450b28014020503040c0d48030001180c0641028100506500c01d01c000030a0701c4030305004e8982c0301441c07a0800a0442e120744002480c280c45503010a043c1842c0000380f00268484200c074070200a1242000700b41456210022604011240d0020f814610301203804181448190801c81c1210200801c45007030f0707602c0d40d0405e140110140c0b440800c2124080f100320001d030301e070a800c80ca481c010051000811500758040303000d103003000d100d16000c4d60744c1b10014840035402034038081e080705400004200103c06004040481c90402c04003420300484403c0f048404481400c41c0644c40d01100556141565100d80c80000f800301507428103070341c1a1003400074032400380351412002251410350350360140f03440e0b640a1080308105681c1c02904243c4404248000e10040b154000040c4105c60b0006101d00b24250350744201c00468051182e86800c080b010800350b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 817974505 1250 817973255 817973263
    0xa1e02030610060f18050d1b1a0403170d0c0807031103090703030809030d020406020d0f0e0d11040b0405090a140111041521050712150909020102070e010e190509 71
    0x407460f5041c217020b1805025005411010603900c465840500d03290408100101c5810010142c1116071800d03d41680380c0008101c0104c2c459070440c8595801d02c42000410082c5810981c1c00b07c01c3c203d001d260148601500080d1122812040081642d0100b031010990740362190b40008091003040c1419410019817141c0c0b01e9030300f84805020880700c58040385840d4001c0c411a81d11f070701009421075580b69122000380d1252080080c81000c20030200c1c98034031050007401490744203c4010107000e0150307055a42c418100a00c60a40c98006584020008040e1554801c15005840210003022280300d117103405450506034030a04141641440650002d00f101402074500341d03480340108074802c0c00f01d0003003141c1010301c06c0455241c0c00c0c01c0c201c0f00c000016032070740458014a060741c4c03841d41e0703a2007141301d90302a03c4102c1c22029110b407a40307200308212969640800001ca20500c1501c0c0d007542d641100ca81510006e800a06101c080d0300107004451003140e0a140c032500c202a41409585000c50100b82c036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 817975755 1250 817974505 817974527
    0x320030d0f050d020a031404030c0c0807140108040807060e0c0307051c0201080711030403060c03230106030c20010c080609041a040f080a1814060f0c0a1e0203061006 73
    0x3003d80c001c6103082c1424020341001c054503503060712001a901e81b504004111100070700007690010803102d800300320031102042010541d8000b40741d010406240c41c004440a0400400a54083c401448820006841c5018030301c207403600d07180204005010321080509160560344106d1080030082001d0324500103865540207081e409007090741c2c0f50354428800307030f850000c06410483c1d10b00000401108120450744011300c0b180c050340d410004800589020b6140c0c0c4103403182c5043c1e040c0ca03040104846482034109040d260300d1881c101c051200c681e442500d001305411040d01c02a5114420130980e140d105135504e5200324100c40580841c201500c86411040301c048410310b172900894002001d2100b0316040e0b5040c50b5020259640d9a8071000000333251180f45510215401148800043ea00c403640d8480710980d0001091207152400700381c1c07250540c0d827280482c034850780241c10346000800e840b845044080e03401c040c41003c04d507986104050800e05d0013071245070001c5210343d0500c0b04076800a03407000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 817977005 1250 817975755 817975777
    0x405120c31050405150a05040501110301032a05040c0207081011030a0b030115171507122f07150c0e0d03031518050c0406020616090320030d0f05 64
    0x10b0b40340c941d0306140381884100c8040e07509107030403042882144600d40e44650700c100c1c010002000b0522480032246460b20080c4070107001c0e010300c2a10140c4041d010707400e0003000ea448540d40d585140d0b580c0d010a00307486240380301c1c4000d030700729403810802240280324884105c6122b141c00c000340c044003028070003903000241c240300c031301d90b038423021400c04e03480960003417600c81000c00001008542e55a04810a0500354401c1c002da400b5405030700c0701800c450385a407030140311944c8508031116144564140144454520003080101510321111415601b0b080003412403103c04007190390320040d051402d004866070700c0841046150403140d4908940c0301c45455a00d07241203400c04c20403541818100e002e03090750580c013114003a94003400510b05071100d41d02079100200d0700050001c2e6442c03800c00505402a0310030788000d80c001c000002ca2141c06400c820680c1c15103400c1844070142ca94039400100c0002008840c030495184190b0b00052808011200b220b03882441c00620001d81c10034001c0041c09018400d003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 817978255 1250 817977005 817977011
    0x4030803090a0c09091a061e0303210906090a02030304090c030f0507081506130605030714030705030717070909020309011d0a0308010e22080405120c31 67
    0xc1c0e6800001d0100b00e00d4250015218055252503480d00b41c002c100f402011112202250500740c41031004484152152500a1909170131520900d03e00003000c0d04e05000030b506001c2001103411480c1c898040c03c0f100110700c02052050314110807154030740a400342190b800360b4000c206010040e5000811074060301d502000c0030a9030111841d0070b4010340b02e102944400c0c5030a1004205045910031002441609280030440c80c1483c1501803210718442c51211205240d141841885002c0c0a80000e40d0010070754a0f081c0401000c81c0711541081d0010f07200c0100184001007485440b5600070381044030038000d000905094200824064500d215520520054580200000c0c0c07419100307521100848026801542160311800300c41c40e2501c07034400044003c1402000085075041212a1041c4210b4410b0f600c00c45c483c3d007141c1c0300140070f81e80003000c41d120401040045021345806020842c0c5003011401041a441c29070300300301c0d04c0d191004812208038213542041301c07410481e0b1200000418850800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 817979505 1250 817978255 817978261
    0x816030b0126010207050d080c0f040306050c12040b0114060322030e0303041806080309090c0705032b060603200708040317030a0b01020a120810150c06110c0304030803 74
    0x15032079800301c202c203426a502c040f03440028070030046503541c00c462050740c2c0e040c2140c4c2c40c02c0d0380303440c0b5010744d00c1d07100140700c000c1c0018000900e080d480340b038024211280150600d40109119110040d044401701c80082440004010703101b001c04035028410000c9603050305525102210814002c203106070b20031440c69081a82c01894000c032400000e40307001070103032035841b6110385002d0740328034094403240780b114178246000034920300100596024142c02803441240e503d9684025195422501c819036060100b0042e00c0c5404540010700c912a005910402e60780b15060b2440508548032540208181070a207071045480800e450f1101c1c0d44211507031402a00d5400e0360034100d400340541d41009046a006403680e07500d10703041101440c4150f000740c005001e1003004800480c1c45000502004109021500b800c1210900400b0000da11110308044008410f82d100758038089910390f1007140001c81c090b040c804051000b80d00590505a050102030b80c0340880850703505580780b01e24403020345100b2001c408 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 817980755 1250 817979505 817979549
    0x105180f040c050c0c030d0c17220302130938130c08070f17100504080a090f05100503090f0609150610090b0310050d08040816030b01 59
    0x1521203104014004014a20a1041c0034000d5800410003004920410105050030700d00040c2140020f10355a40e0300280814a6880c0003885812280030360204000f80029000c030fa02840d021075460302050040400d1600c2c50050044440005c05003201050404840390b01282c1c800070341c03009840021400340d41e80802d0f07506ca252190350142d92203407000320010070b100c000314030850003510050107840b0b003000f29541d074020680c2c0e592161180b001e001248001c100913681c554203401001c00c0e04c0da001d035200e08490b0380c214000c44104a404443d014008542190302691100c1d41c0c01c003034480c40b51448859410800002d8110141850030000c022002001030301741d0f41c052102600e041388c84c4084828a081415041d40c5842d00210001805c200c41c1c400030b92103180c070000c4402c0040d039580b00d115a40b4200480004a940024114443c200c0000d030002100c0c0c40f04d9030a680341c680950f4583e5211405e18003d64102110780c140440d0356505404148040341e41108040d0440b204403407020350500f840c0b20 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 817982005 1250 817980755 817980769
    0x1a070212010905061e1f08010203040501150b12130606080d020a1505070f030e21030a11030613090303061802180901120303050402040b0604150201050114010518 71
    0x50080d0004450a03000340904015041a40420303c11010307507071141d4481205810740504401e0482542c001080440c0c01d449004540454400407030502056442c0c48000950aa80c004c0c1d500b220b150307544d000c02e00e1410f100c0d003071154090140071a0305440c040901400c0c0030804000b507c00c421440e1408114010801698000d000038903000c130595041c54080f9201a40300c4110750301c01c0c0c0f41c02c0b08041080c40046042c0c800e8038400e10383d40d269548080300070041100108010340380304e0b000303100c0c800940402004045410540448003055140d69290150780798040c0c0c1c6024038039000020050003440700791307916500440e2105009040000c1d030040941006c6020305481c0e40031aa80342c40704203034110846c449030020b001400107108101039800343c010501c07600d150240701e5010b00000c001000000a40700760499030f0030900042c8081000c109910009851303501a60203040441552850f080f2101d8080c05240e006084c41010347c04d0700c028034800a462481808c050144280321000d6401960b61402c1c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 817983255 1250 817982005 817982017
    0x1401030b06090a06081f1a0d09200103291e0901090209100806060a0c051c211404080f070f050304050a0b040503031e0c0d030903030506010314011a 65
    0x10002410269203840203003085d5415503626040d81c0303000f0410300340c40030040c40701d008035103000c9a03040d89065888446851500b0450000d41d520f0784400755140400c0303040c0103c01c3e058800c545000c46a0003900b0002d01101c01418444d5015455040440c011480b080d40a4180e81c1c02920f000b800700c41080d8a10b052582a8900e440c0e08c101d1500022680d04082da000c4c0950794000c0c2c40020800c96201016a00310b28110358060344200f00f00140aaa41c2c410300c045616240b00d042120b503d07145140c200d1000e1072100c490b14000403484100d105001c0441890100a46039100b02040700b0389450840b42e45142c1c004101410010300045c030459a419000200c130200354000c442c0c00168140740c41e0454a036445489081d100c3c05000c1e5001c50342c0031040c0d0454086480050042d480c0c04003c66a40103070181081c0f541894000c01d100103000e000e024002071100b0859641c000691504610307004e400c40303a0281446040624040703000d182400e1030b96840d0b054804070000a90411254100c0b0000d9208607 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 817984505 1250 817983255 817983259
    0xf0e090705010c0302210702040e0307170f1315020106150503010308090645010512060a15020a05060a0204060e0415091a031b0d0327060e0f0a1401030b0609 69
    0x107860b06d00c1500028007600d11a07101b120b0911504211000e01c5a0380e004800c2c011b401012803034120b1414165403030051103c41043e1903841e00304514002e140d5903c28144d070001c0c1ca0700318012194150140e082c03052001401c203070421103440b081d510000401900050000810a401c001a10103960b80e0301d000341e8001c54100e002e40c02c449180c02d20b071305180c42e2003549030214070038810014804074082c849000320100b1040e91514141203044100f0400c00a01600e015005900c50401168811684550900311a0250000c10041c945403410324035142d030090001183c00e205000034441e40d5030201102080c2101101c0114041021580b800b000d000d00d0b510464109140422041c402101c007000000003002c01c42c00d44440910030046512403440d02c2c46040d61040680030108002030084111100e11f0248142d041041118110840d00da001283c00020205110f400108124075194240c988458405d48848500c42d152036141690b08880851003414183c0342c4002003650744854041d034000b00741c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 817985611 1106 817984505 817984543
    0x110123100b031e0a06030f1b09180302010609020a1b060b1809010e0a0c17030d060f0303090608160804080d0906060f0e090705010c0302 60
    0x400c04200004080004140140080081c5210364100103019030115041c0c0070220f0310000040640402909010060000132624200703400d140c0c0c1d001020034550150031740725600b0718486802076290f040c075000c05183d0346400c07481800031140c06600200500303074880c188982a0b120311136124007c20b40f2101d0419902500d02d410502040c081c060000b4510a07000004019200d0b103101c82c60385d55800c0003405007005007845170807240d0034540010458a0389982e6000e211500b144601003a1320380e0741e00013000f805014001c80350744a030484020480d0507200d2001c0160810140010b40005080c0600072513000d0140d500c65019803400a03c0842c49030340f60000721104ca1000303204407401c43c2c2c140040011032020380202d840044c0700b15804682c103070404400d480482c04070340c08507082002035403d10800000228034041503503402e01e0003480314100340c142070746082c60741c0c4c41626035400d03 = true := by decide +kernel

theorem cover : BRFrame.Cov 817805755 817985611 := by
  have h0 := BRFrame.cov_init 817805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 817805755 ≤ n) (h2 : n < 817985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
