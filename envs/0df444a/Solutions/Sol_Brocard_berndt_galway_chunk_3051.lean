-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3051
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:30:54.878766+00:00
-- url     : https://prove2.me/submissions/83c833b5-f34e-4b4d-9911-0414575e0808

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 548561151 ≤ n < 548741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 548562401 1250 548561151 548561159
    0x110a030c050a17120304031b0f03030506030102031506091207080f0d110d0804080d0513060506031b101125060e010c2301021c1805030415090510020d030501 69
    0x78480b049540c10b910b501800622400f0410b130300b03440d880104190305010000c015002d80b0082c0039202c400b0750303006200140e4106154500202680c07005407461780710f617005109100d41d00c42d06008e9900b001d881100cbea240d0701c00b401000306280079506640030120b03000d50100000c407010007190001409100106031603910040b924142ca08100d09011880d4552001407100704103401452007941240c01001c640d401d041d4a10703100f5040d2441240c62402000c52010b2200400c841c0e400369a422010071005050f02401c1c0c00a000080081220f00a101d03001d007460b031500007806000b001000c00c0c0d10134207507181c0f9020041e54101000900f040041c41008aa40004480d4031414441d075103064140d46ea00400c90042e15200d0010b010030111150b400f00842c910703001c1000910003400c0c0b80c03412002c2c0e0383c3c0e6400103d1202c0102e0b203040e4504000303044180c83c0500021008403c507030035030344c0c4079040c000490040441242d9810030b0f81c00403500900c01410b20300c038035074000410180a400382c5d503040c010b07680c81d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 548563651 1250 548562401 548562419
    0x30421110316020f040c0504060c080d06120b0108210f2512090f050105070501290307050409030c08030709030b0c1218120c0a33050403020a02040504110a030c050a 72
    0x4035032071b07000013907002c1c030050080c6172180d203908103a2802240000d06004480034100308941c51036006144214040b0808000c00c01c07250b00da6401050b03018060722949038040c00b000018100d01e0442051f031080060040c281c20543c800307461003100382c5a4071124900030b02514284004c00c00ca0107890704822060300611052260b0090425204409800c2056500e48001502c1c46e4204410490382d035525030b110030545000c2d00c860540685410150306181089100900d82003a001e0b800c5280a11708040c41c9802080d0004c0b04078910b02d038001e40c3e05980b6540c4103000c8603403c109404c0103000440b10800d202c022450b01c3c01801e102d03918100440160703101c03100030140640500c05e04801035000b40781c3c0280d2401d0180058182d00840c4002d8604c070703011076510051481c0c01c0d00288401803945820001d040d0400810181e104001c420082100e801c1c9920007940d1401c291034000e118640720301c002010007100010442d80c00c2000f0b8102c0c0380b095141c0c41d0440185031980180c2d0701603401c1c8e00e800207910700 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 548564901 1250 548563651 548563661
    0x3031b09180501060e1017240d11060306060705060103050c1305131203020c1c0201052202100e04090b010905060609060d0e120c06060312030421110316020f04 70
    0x40f01d8803101c1400c0d54440038404941d03d954955814007400ca22400c1f910744000c9005440b52950150581e0524000d0410094003071054410310700528940e014040000c03405c42c039100101d6000c49656403a641c400c00000d5640c80f13015001043c0307029080000081090000e110b0f8604002200c3e10140d80d01e080c4c00040440f54100c49100181d00891104404a1f05d0381c001c030f1a4000c210302d0050b19110349442c0c014035000e000e40c01c10f01c00304480c2c06c001240c81d60a2041a400c407410701062181a5143c19001d034440c1a000c4010b07100c0c031014403a07060800c1c056654901000000341081c01000c28a00b00000e100b10709218080c8840d0030803001420074a4404221004280003e001c3c905120034030940d10000c20440703180c0c0360584660f0308070344480c501d04409041841e6815004085602c0c20750145800d0801004841000d00d01c14024000010300c803000442c0c190392060003458441808040840c0c1c0c101a9184203a024000013910500d000781c84803c4213442802070340d008080000080c24002140c0e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 548566151 1250 548564901 548564909
    0x80d1103040206070615050325090513150605040f0b0406060302250218010806010311010302031b031902040f080111190804030e03030f0d051803041203031b09180501 73
    0x10010880c44c00000c1140d030201202c3e41ea0074002c07046550301d40010910b00008081c81c3e05081c0d0030082d0104101504e500d00c2006444000c0341442107003000883c0d5506c0c3d2403151002025030364070b0a5070b02051846944010001c14000380244145548501140000e00a81c44c02500a50030410042126400381c004c030347c2c1e12030301403000c002c0074800154411401d001011040764001900c00d0351808002c500c140c1d06000e0980301c00604202d515600e468802a10503100d013a05150040c4104041c2c68681403900c2080c41d9403820b040d40d259511f03d40141c0310780e04d40c0c070103d00e110b01c04500807074a4a0498000805d5883c0c8800070006c03068250100716050285032000311001c02c2030800740c11014803070030010b03400c03a12a0925030960b02002c070000b410340e00309040b02c800c1510b000c2400c55100a8500440c0d80190b00c2035010315034a0000341c0310381d449109901030601035491070380c010410984258001c074000c803103c41144a40f00e160040041545d001440b88002040d000b02c0012800d95441c402c0300e04031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 548567401 1250 548566151 548566159
    0xf1b0a03080c07022403060913110d080c070306020d0e071223060f251416060905070e01170d080717100303080a060303200712080d11030402 62
    0x1e649650710a0b005a115481c200e030400c50310b81c904a10110004080d084003450100195104d01d003190030301115200043c280c01c0344100c000781c6040030504984280d40c03c28015201220040d0700e90806601a01c0f0700110380100744203002e0008280300c0c0d08e5021b4080d0507000c51040c0608880d40684a0703440e0601e0098031640b1303000200d540000782031014050110940c400c0c107103044005010080e0b007040008c590701116900c0940c00c1009a280b150040ca040111210307030000030000d807410080101011111101c1d030620000368500f1001030f11031807601b440c3e6100f80248100b25580c078003191a40d0305445190b0f1b90701c80c000c001103020350400304c840410904030801000c083e0720400080340c50f5480500003000740042642c03080003030255202410b00c036903031010141e90098a075140041140c50000c1c10000030501c5e000342400001c0e80030700d1280c0301c81c03402c054030301a100b20020342c5030030a80c00c1e0703120031002520b4100c0401045108000b502490200c03440400621400c17241031160b0b40700c110740084d44 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 548568651 1250 548567401 548567417
    0x3021206063c030f0304121502120a0b010207080d030f0507021f0c031509021216051803120714061b030703091a0a0f0f0209011b06020f0f1b0a03 64
    0xb400702d102820030140c01d40102124144007200280d076056521a8021458880c9070f8113a0318140000c5034010340b5050300c40002107180030450300060b000240c0141201c50510f44139007041216a20800c4100c02500c0103209540717445021100280c0102040c0b40301542081c18040064249400404e0a03e45880704520155101410a50f008010700c4040c80c98018144e0b0346164898100c000ca450002401c401c2d000140d844c11707801c40d40e4158183c028240740c0a03601d0320714811504c661050a558038403540c400d20030300014610f00064200b01000228038044640410034009000040820600c80810807054a255031a243d00d030481d01c16032070301c041102d800100049200c40744264031030505c00e07004481d00b2507210488002e41e40354401c1038500b102960b883d00081c98615a051161020302020400114a40703a003200000c3c11782c2c1072100b800103030b098061900000740029a0101c8809003d40b00005c0e56a845840d5150400d8224140940c98807900035403c119403030300020b800588680603182c0401d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 548569901 1250 548568651 548568739
    0x20414011d03060c2b060914070e1003060e040507051504080d08070219121206080a0f08120403021605030d02060604021606020412210e040203100302120606 69
    0x2907592049176510311041e8018071160940d8512141c080f6421906a404600d40f450208010241d500c080942c01c0048140414440c0b0306030801001541000e080d14004000f607a4200c091380140b90544c007040c41d0800c10000c2008100000c216002a5841104c0c0c2c0d00103203001084a00d0325004a0044020b59404518038410041c001c90407150300412034811640305103900c0d00f901c408030025410880d40a640700c413200307030503940001003086105502d100401545140602d899030f2190f04100150433156940200c5041c0220f0100315050343e10303518003d43c0c041c10700c0d140003550741ea0068000c0307401301c01006020909103000b061100e201c0c54039500904503130716014100402580000e6400d9050100070302d081c0001034140c00640000d02c900a44981d21070103e051905100118a00304200300da005c1a880581036004040035000240503034006849a488464003a01006141c001943c0b000311256007045004000400d14171510043d200c83c014202004010699120b40c648030b101e1044040200403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 548571151 1250 548569901 548569921
    0x3060f050a050705043f050618031303110f1e0a09020a0e01110f0703080903070602030708030411010c0c030b061e010c080f0f0a0504140d0807150906020414011d0306 73
    0x1107152000c120200c400401603940034940030b4008404031fa21390014400c102c01d5111031210801d49141d5070f0055803900302102e4a20080034030f503000050415003000600160f03511002e0307441c03410020203400c0030841404640c504400326030780c3d01002d120348100b00003c03c420406000b07132800c03140035442d030603c0b50314071000540e4084803000f0b881d0b44c184030f40100d2444440080140740c00071070080a080796038401d0042454140016030f0061000d5500070010a00060310543c2105c0c0c0c840c1d001b2034400d0403881040300407203400c05600000b800c115100301000c000d0244da0501c050150104950f51110343c007901602d5003061241c01850740c04a10246465808a01c6100c0142001e400720b500f2103191614002e1200c10a0308544104000940085014000010380c1e20841660410403105012a42883d541e480300c035114100f80204080ca00d01d40141d2071032902e4120340d0401e42e015505544407502c403c0d00c22269801601c1280c000b1300059000e0302c0c0108410410501a20302401605441d0754100303000e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 548572401 1250 548571151 548571209
    0xe04020d050c040213090e060403080403110a0c15021005161d090f010305060a0e100c0509101d04020903030301032d050d030c020d0e040e0703060f050a05070504 71
    0x2a1124011006241210f9849200800d00300d014500c07503064481c204010034044501d021100c0049a2140e4140808240c00c181c88070742c810303418501640180c00d446101400d015841c0c1e80100108009080850b0b0001100100306210120390b0032505181950741030001944c805460103c0c49505180d060b044051040062540d40c007182c0c5170b280141c104400c0802e60151003224020a03a0301d903034005004000c0244100e035000401080c05000d001ca0b5400001d88500ca542c0d0024043c954540078403800602400654040701c00080c500c42d00482041005080c05100c680ca0010742c00320034114445e00c1c0f40510071380341100000341c01507003542e0960303940100b120b10440c01004195259034031100c100c41709d20420704196204401415503541910000390a444030700c0752100a540200b0310300b40f001640010804800c1000311000314001d144010550305044080d00090565810160220500401600518000c0241d0502000303240c0e519007080341c82d07020b00e01131988440c0681000c600b0840c044842 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 548573651 1250 548572401 548572403
    0x3122708090a03150207120c081207090306050703050901230109020733110405330c03030912090303040b07061803080702010b01030b0102030f0f0d050718050a0e04020d 74
    0x41c2c0d42075034881d201c0b891044e0503103408810854000481c102000700c52414596080c015040c82000c030f40d556a10051140201204807900c0a2032000040380301d4880c4400c1c03c015a00301c0d07030800c0715040c40d04004001d03000848a0540540c00c14804000c8101038103122840011a100f407030005900301280c0301c01940c440c01090b10400d2480b400400f14040c00882c410624820990010340403013480e41e1801540c0003003000202001081c0410815510348181c41900c01c4c070114292503542e201807030422582c00cd148220311402c040441c5100c550040000210b0046001130222001c2010a2080b030f1198400c4242d5150150400d000401280c6c0d003100c0a00075007032041030042030521003100300c0003128447c50011381c0000c1010080c41000c40c0c0a02c03030366485070070a181c180a070840c42c1001030754034030912503c00c040c1200001d48410a88028041e50007000600c90144440d0030300302e900401c00045000300c2c60300d00921820000701032420b03410000c1150701101307441c0742581d21902001070005d00400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 548574901 1250 548573651 548573659
    0x6040b07210b040b060f0a090e04081204052811030304061b031704080a08061f0f02070f06050406020f010501080d050a02030c0601090218090402090c03040507030b01030312270809 79
    0x1130b0401455459130003800d007000d41000c3d03040e11010301910091000e00c07039600c03002005030a070091001013240f490460300310403c5d40e44540d00756155031810600e095210b650b05182c0380c0034051841c40c04580040300304061805161491000c01400c02016124410b61207104d020400444148000f00d04009501120034020705240c0c00c03040801c03450400f048000c075000c50300e00e000040c00100c1c8503048000c0301d410070025600c80ca0a02c0c16003e640e550f2102402c0c01f4401e01080c0740085c0c80c903500c00c0060502904480020b000c0c41903541c0320281032074006000d84800340c01340b512503182e01441445014100c03100c60b0001e00c2a506106820f40305a809007034a06d0840c00100300c011012101004524000c0c0404140180d0341d00849200d0105001700348200b41c4105158070503c00580d480e0803180f07801c440168845580c07600c80740740080c03a2804551000b007602c00000d000009054000950110f141200030050001251024007444c988680c03804105513455044400707404148840d025140b01c6070098 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 548576151 1250 548574901 548574911
    0x30507020f0a08090103050c090d0b130203010f091109040507140604080d09080111090307032010020102030403121806050c1c0207060e070608010b07020a12030206040b07210b04 78
    0x30500030b0401841140944039000d000031040710175641840b82951041c1d40c5d200160a2044404c001224088c0c0300d54044e101e00d10758404107000d010480c58090350268024000c001c2840b0031980c0002820b0540c40a54581c01a004003400302e040015916106070740c0000585100d9050000d103844e015000c84001d43c10140074440070940400402c401c18000901d52a0318500914103081c0c2825101d030304c0040c0050260070300401c001601c00050744000d480e8002100d0501140040000b901003401c00449030340f18000320b01100c203298040d401580900c4c025a280000e0306004148074081d1003039207000b0740c00005000010000304150790f225a8018a0110003246081120799812442e00340a0144060040d80024500704100052052407640115040541f01c150f1400f40040c0041d041403046205501000412004560360044640050880000480c09980440c1002591160103c4c0c0c226107103407209001c54500e80c0500c00e50b07500305035200c6128859518400760140038100070240b480d0010b44030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 548577401 1250 548576151 548576173
    0x141305010803121e0f041103120406051b01180b06100e0111010617030c1e07050607050a051212182d07032d02030307080306010507140d030e15010603050702 69
    0x40103a000c1e04205c4001c2d41316041500b8645c0d840d0241044091081e0721074102420311442e450107035030031a032481c1092074690071620300c403228500300001c02c0c04c0654601f482c9002154a43c0c0b0001058070f00811851005564007010310080c2704424010402040c407641c012019588165045904c900d88040045003d950303a0941848100d40041d640c0c0c0302c0d803c00700303618122040400400701401d0740e04480a00680804038199104c422502070b40f409020000380d24018000c00b004940c50a0340d2040440710458040200d20986401201d45000d0f20f48001000c1801520401c01d0302208124600c081c0204041c00b480115074800d5001c4000c0050101202801c810541030040750025401640ca1200504066400324802500f90b410309890a8400ca03504002d030301d0010030748100d694403c000c0d87d92520707171070300684440c060804000e01c40813403249610040d03000484c030070b000054079880078800400812829921140102e101e1400e404520380100006ca03ca9042140c000503207005450100150f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 548578651 1250 548577401 548577451
    0x5040806151c053304031b050607030203070f020a150e01060e0a0e0c0915040507030e102703050304060902011b060b0f091312120614130501080312 65
    0x9450b2040d16140c00c48a03103000b500c414500c24203a0f901d9604d061042d141580741344c9140444021700007034100210300080c2c84400c00024603182031650090103c4001c3c0c42c1c80b07030b4014040d40c0102c07801030005041e44015183d15000042e04d1001c9a441000d000c60b00484040c1e540040143c014050900e641381d810000f54003046101c1c0901481d240840812643c0c1e0704120586804280011030340500550406c12540072002c45410b0f038020421100410292103045046018092010345200c46010706080300781e040c0566808200c1164800c0b03954103c5a0903150441c42c1c11380755102c00343c04902d0800c00140090815031000e850325105040030340d100c0c1d10152110b4840c1081d80c404940c01070f42c6d5807440c6034900d410000440070440c2107601d0741e190314000018118440da039000051410b4001042651b0040c083c016031030300c005948404000c03559881c070880d01c50300b02c900000d07070181181400c2065103490760b0195605840c00700000714900340490251503c0302d08010060420301404503c84c0d058661 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 548579901 1250 548578651 548578699
    0x60e24131b12020a08060105090118020d050f0402010305010b0306030d03090f0f0b010f080604080702040903030e12072f0d0302240702060708060a050114130602011b0504080615 78
    0x400502d40703800c0768507481031005441c841d0704002d00d80c3e4030190040000d03650b001d05841c10759900c4c15007105000c600e001e8041c064003860b603190302c42c542003d08105000c10751080c100d00c11070007641e0a201c1a661307460f03501c07041c0c4015140c0c6a096041071001044c1c442c001d0b0091041c141c894440c01306d00c2221521118400704d80101c0880b00036003020010000c5100c06034a0b0b0020300b00380c102a084070f0420741d40d490814031500e0802030040362100d00047c14980a913100302a8407140e003042d681e20f041000e00c2524190f00141c02101d452140f8890035031020004070b4200703103800a10b00c0ca000c05407401d004210003041301c402c00318110300c500d0b4043c2054a48039801211801c802d40504103043c20300900107030070410000e000d90100304520b01045041d54640c112181160001c2c200035000031041e0341905a90f128107085c41f002c0907044140090010344c1540710249580044544070b42003510802e0032a4648903a01c25050300754018000718014090b030207542d405400b0008c1c43e91103080c04c0b410300d15203000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 548581151 1250 548579901 548579909
    0x12090311210106090c110343060e0d0e03030409020325050a091202011d01020f15010e010614030103060b060c0f150a090c121e060e24131b 61
    0x3500d9002d03084045800c050001c800d030b098003000c0c50030701d424040413602c041500c210400303402142341d507240c0500d40b0418448802140407076848680189908040010b090414414001071040d1220500c1241c810b250036003d220001380514030342468420f6900c081d40000d000e42c1c0b10f14040d04405000c07003800c000e10800c00411a11803c0c1c0310340641c04080c0c81034065a102030321024910f01d1010046c0ea010103124515002c4480703448034a521800102c2c41c0c000000c08865851040d18141545910b1030403060381200e81ca144800032a17a21800d00329001c1f0f88100769180000000c0c00140005425a0014828014007518160408240c42144d9142044042c00700c41d690b08411440b018491801034407951010b9418000e001c06d119aa444541c2100d81d0b11484020004401e003e5081000f031540c4850a401c0302d00420615101a00749a40200a105030421072803103084080544914a0900c110140e41c0084090440c0d036a1200004840d42c0d02040440f801076486200005c1511160a190f000e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 548582401 1250 548581151 548581169
    0x7020d0812131b0602031b070b130e01060c020d0303020307020c090a05040507051203120907050a08060108010c0c120e0d080301061106090102090f13020409090f12090311210106 78
    0x900321814400340f441d2145001d10301a020341d403002e02c00550004102c40d15403042610400a4919494080c3d050403c144c202001c80c3c100050a100c0143e480101d52003030740c0101c82a904166079400007a200300d2a00a0f000390880e2016482902007030203079010f50361100c2c0314011b0341c01400200c00091000c00c400c40d01070070080d0341c640c1440f0502a003003203840701900066440342c0380c840e900109555039000c0d400182c60001e0f484030004078500d10a0004000415024004401c002e0311400c040342c03280b00034043d142e0258a4844030300f4401e0300c2101e0030000103402c840c0c501c0e001942000200c41074811140b0045d001584d0005480c0007800d03c4004500030105a44c0c0d002407196480c0c1502c0c144100580040000c1e03005115404160340c60810750480311100702c0b91001c1d10000ca1f10364030042d02a5904c0082101d28040c110014010314030049a0a623100b00601000d82c50303285415920091180030140001c0141c162645090400403040c81402980745403503000c3d10a030410443c00e403102d54000d4142 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 548583651 1250 548582401 548582431
    0x20d0320070e04031106071e030f0501080304210b0112030201180b060f031c030b030a050f01090c0603140402040c03022a060f0405030a0c0206040909121107050607020d0812 76
    0x14950b00070411002d480170800500b540d030070800300082c041030119444280ca0380e07900207012541070085d8031040c40380208032020b21072036035210075203510b9401a00c04d101c800c0d6210201221202000d032403045486602092a903510b0b42080c200030107080448204405544da0b860001142038600d44500401500c80d20303a08845140000902c4032800b52135190b9030107580047c2c0d0804140400d03032400030b01003441d4600065070742000400a85041d10641014150703004910f0f41846030035064000342d5001d03014021a4001980d2080101c0c100c1d8910010010191410310101e0010b150540250b420300c512482c026082140041d00211400241c1c170300c1401822010b16203030300360351341881281e9100744003400c04051482c05e500c0e040d440784180c040c0c4100300312440c0d51250840da102010303a0054948808100480340091400066071901a01c403140415290703181c0b030b0110b60b00084c881d0296480a82440d0800342a5800c0c040030703d0848008851070701c0288401d10b00c800311000e083e84500c03411030008003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 548584901 1250 548583651 548583653
    0x3090f0f0c080102040e040209070c0b040501091e150519111e2703030409060303020f060108011b0311040506030f0a0507050301031a06031c03150b07020d0320070e04 73
    0xd0307085041d440704565900500c01041250b80300c0142981c0150161a699415a5801d00c210303541044050001c00070302501050106000c015404107a419108072101c0901c0c0d84040e6020b441d240306120018600e00f410741c1442d034401c801ea0401c4d80c03c00410000c420080401c00107207400d841c0f85004040781c4500c0800d60b0b0605000030500a6440c5070032400391071031b2228082c24400b9020071911420801d03071000d4680c14039910b0801c1203400404151204002094491038029240d504241168240c1e00c600e000201d4490818071550710b591045a403d554503604980c0c0640181404480e0460100005e01000840b030711107500842c4903402c0200e0b00d500520f01001c0c54000c80e0009418202040000c0c00144009400d452400107182c4c000001c0080546c1d690001078a03242c40480c24541c010389128040300d059415030010702c06540c0081040010540303c5480758400d000d00000a94030032201500c02c03000c240609030718514008040000340700c0c688010343c00c070301c0d04034150b104802821402c02008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 548586151 1250 548584901 548584913
    0x703051315200705300f090603101403060105030d180302061b10090b13020d05161802030903090114040b0c1506030d08060909010209030f03070b0c13060c0303090f0f 73
    0x3103007038081c0307282c03d5171440c003107940701040c60003845031055000c90001000403180b03104200761070003190010310466032480c01903a680100d8920744904161060300b1000d2070490320307000c80d615059074000780040a42d10141f640071100c0480002c552800d000d01d4900100158443d00d0013811950038101650314801c00784144980380001105014045c1031a04c500b0030006000800525000038400304581040c00d030500000f03244107010407005084e48038004a00c459640b82d075041104484c0307906070360941c04481c0e0300003030182e1004a42e03c040d540c00400554003a5802608103220380000d0b641c250b8141501c40700b00ea4007a038004e90075402c0544c048800030607110702075000181d1015098000e401020351500001d40800c201900c90781c17190403114000f441c090825415103032815001821520044260f482d110349030f0b07000340000e480d03009820002030740b060003510485580c0c0120a620f40c00c070900d0301c10210780002402000f1400c15489203000004100c3c40441d4401103400703211040801e0700107240c08 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 548587401 1250 548586151 548586163
    0x9020a02070b130b03040204110d0f0c0203121609050907030b0406090605060306010f120617060703060614030901020403060609020d0b01030e2d0f0d03050703051315200705 76
    0x2c001001e6007041040c3c2865103036040041103402c8807110984a071164400500a840c151869400ca01400b2546002803051034000c06041201628100426034141c50120780385d1003804201c209000009003c01c0c02d07603001c2001d4103800070341072030003054490b11400090442c6a0944030000020340b51103040c04a0311b8244150002066079046c1001154508008510a0300005040b036060001c42d2030b60201303543c0a1224a4039a1581c1601003242a403100a201c072200c4110100040510400c000030340d072940244034101c01c3e202c1a444946402d030210a64407641e500081c001043c55409100000020f102c40c0222070242a018002680740e0b01c422105d0812602000c49280c105400c0009800a081c800304140703c5000e40075900c0c58444012000342c441c0c40c0c00c0b20070803800e513110354000c0c264032604c00306240c81920700b580d030240800e03101e4103011020f54406442e01840c01d5500310320308000440a000242070354242d403801084030041d241210030f034180e408a81c0b110045000440d1401c00c10306001d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 548588651 1250 548587401 548587409
    0x301030302071202090a1d070b04140d050307140307060906061401030c08060f060405090a0618090b01060503062706030708060c18012a060c0c2a050a09020a0207 71
    0xc5194003c00c20f030005000208040c1c112214070780d035528540e07a039210882502c000754003c1000c0350100c2d681c03803c105d00c09074058482c40f0180c4130403011039240ba1400501d0b80801c2078010000b9400c0c644141c8401120a0394150810070030f1000300125000988203010304005d10340036010015042d45810b03100b2803071607030031180d0a04140c90015001415608910b600c3d411410603208890108034243c00700e40359104a4000942c1308064204200440f16a41c2040c0309503600400a424080140c80340d40080e00c00b003c0005000d035882c42d0050086170f1049000e5540404020310155540b911405090111852465279001c190203c00c2080101d081c01c00200f00100622401003015181c110081c4419004084c500e49190040502034903090b8485d10081c10b0650100007845904240b030200a2403801124504803107075820240004116030250401c2c2015a4021518000b6642c441444100c000300309a01e41483c0303030301004041481d465480e00d0601504921100581e01c440008000c0d15001c403544c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 548589901 1250 548588651 548588669
    0x40209180f040303060608130b10090905010203100501110c0108061c0f02040c051e0307051903270b13080d110d060f031203050403030f0e160e28090b0705030103030207 74
    0x103201142307200c50041425603401405103449620350703851a2611180607401000010f007000154824810198011405280d0309076407090041d50350801034442c021080c400c00d9407900310403247c207200e5000b2090680d00000c002c0c072003124200c00c0a14071802c1c02d44c1100c280e41d8031030a04400411820980f05a408102e241e0400714100890076030813401d810a020000140b1040210106203010300490550782d100a05180c02103403143c00c940c0c000c1c001e00e41d40c02401e4034511034076100142d03042016a0040f516800652140c500e0385d60030712070141d40c1319640c1c04aa485d035081080040c11f130940d118050300881d00003100c03580e40550090200c01d40d00383d500801e48d08403258100f040000c40140721302024070360301e00340481c1c603a0300c80c1400c0d0020300681410607982070626250103840d504c0030518002c000454841c0000d001d44405103000d00d150119a000c0d80c5106180071483c072904008007040b400d103005040861554401e555804003128155108000720394003000500c06c054040c407800000c0c0130144 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 548591151 1250 548589901 548589917
    0x203010f110f0c0307020306010e100f060801141503150f0307080a02130f05040f020111010e1f0e030a1806030b0d021003091407091103060a05040209180f0403030606 73
    0x1c582a81078407810030035042940c1c1c0040d504031222018800d03112420340040c11303601150383d500401f0b0703200c0808450100c441440309102060301c142d95125502130707500c0742d81c0e000d000341c0c2003840d0035420380300e0251400ea0101088005c04004410310005500c01c41030b907503030381804850780d030141700c107095240324100d100c0d400581c0705010300305000034115030413601240c40306600e0100170b00c900003c001402c0c07005240ca040c0010041406000840040720900c02c2e44c9548002c5401c0c5401400c81d00050201c2503617030480180480001d103d1151555080c412743c10000d0f8040680141074070355444407941c2d0010078504004135040d5402400070382d0040101707080c2406004070150001d4107035802008001c1c80389910103e2014402d201e0b60002410f9544815400384075013420b000700d0b503550510700c16204070f0742c00d0544c10740d40c14400c3c5040d60f0107040f0140038403200e03034141007c10000e504003032445170300314410055081c00d804d0090348440c0103a0380b41c00d010086003481c4c180142034800f96001a0300b800420 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 548592401 1250 548591151 548591171
    0x5010e0604081002092404061b03140f040b0d0f0c0801030302070603050c09040504050a150606020705041a0a0306021e070f1212090302060603060711100e0a1e0203010f 74
    0x20440fa00c500700031040040e5034007a48000691054402d80108040c030000100d03e02c0110f10803001001645c1c036a0311516487c20b200610940701c09400c11b801030024080c038038080001d806039005400c00b82e030140e4a0341d003840e8662200c215107801001d1308000c15038403001c1c1c0c0c0c11308142c5445000401074140c50840e40540c11600c002e955200c0c13512540003059a40d50004144071200e1056032101c80f4003c200340130070700385800c11543e1000c4c40001600c800151050101ca00e00f421300c203c0301143e00c1034000d040020326000c00c00c8000c0114102003100c041c00326107007000c81d654901c00d40010314464074005840f84003800400c1126814200150b0140b1020403d0301c0c00700365801031010484d5403122090a00a004100843e200042c4910001903e07081c45813580c100740e004642c2910440c0d0903800c541c030940d100b1004803140c110046d041903003030700003071440512000c09802105a0710003810403104940400c4c0d03200400300440315460104483c540500d60118a001c1c0641516804000ba007800705043d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 548593651 1250 548592401 548592403
    0x203040c0b13050a121401020301060c1e02100215090115090c030e030d06080111040b070308091f0903030b03060907090c020a0b0f07080109051e04031e0905010e060408 74
    0xa0285403901e10001c540c1502102c5021040000340101402041d44507959a0140c94070342d010790f404075061000540090501c140501c00c0d24125295a0b8400c10100c1c00c0b84c4a48041c04c0d03010300003051843c80c22246070050784803810440280130f010390007890300840c0d41c000700c100081c010b001c86100d64101074200101c0104105000140d032000c100005501041150aa000300100c0316000d8045c040481c0e11520384181e54070980484040380000c1c00b18250803521a1803521460140d80f0480c44140000004640b01d072229550041030b090440d031003c0d94a114407440c4070042d40c5407191f51507c5200c018200369060103190915101580100000c1c28960030309030310384040d4001c206180d0750f03e4151160301c5108000c1d50f184150001484d0420b82403004041c0690a01201d120011540100002500780464828107209048094030402c2000b6900d400c02140b55010300140e00700448102c52600911200c5180718050b04030b6280d085061b0b2800001501d602c1ca2595814804c02060004000ca468 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 548594901 1250 548593651 548593673
    0x17090a050d020760050c070902090604030b1914160f03141e011e05040f1d0f010c09050303120a1b020604110915150d020d060e0703020304 61
    0x1011300e000038121200d180301e0340e5540351a545071401e081912440a58040761140305035001da03107009012041a1450001d48151003040c0000e54168844038082102c98042c0d8058907104400400b0f852402c2d5483d01c0d4510101000e0360280440400344100031400b40c6a849034105410700c00b0050301c400d15003000500c0d01c054a100303585092000c0f0f45003803c00507201e07512003422140d134140740103100d0078120000f244103040342c441c0301030249605c1c0002c81d030107a0030b80d48001700f21502c0402c1003202d8201002d1201900009202d8428039444190014042c0200d19180c0b00f5500450020008585802e40c5c40b800d46550044113000d20200d440248290b44001c4202c0314010241c03503807803890740c4480c03003c00c0040102c00803800c20f4148850314a00382d983d001ca800d9000700e001305003840403803501c6810070411410a03105c10341702c400b40790860b01140c107008006041d003104840d0010704102520391410140d0340148160340310147d03640c105000321079880d590385400c1022483e08604500e0140c2e070f0001184 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 548596151 1250 548594901 548594939
    0x902130525021c05090d0c03051605090406090312020703030f050a0204050d0f020a0f03030f0807140d09030903020a0815090102070507050118180e0105090d0806010e0117090a050d0207 81
    0x4111807000c006441c0c007413821292811800b5111a1002c4201d0902500c1528580022502800f44200d1040c8100d080e40c640c5081c2d0b14014680400f03601c441d0b46800007810b140d0703412828480b01c030310110121002c3e0720140400a009480100f02c190143e07001e00116000100200300b200d00c140b209014030380310624521035860b0704c006041001c580300e0001407941c0b5195030094850070750300b000c084101607001e4103107080d407060f03500d4448090b1030380c11050b0b40784190762107280050702003400302c0d000c01c0385142c216401e554000d0900178845078698003c10a0400135400500c1c8682c0560760002c055203105140740d5000b8040c600860405e1030350395889465000d03038440d107810445540790741d003d00202050301000400a07012004038190b60940c912015002880c03241e00300e03510301000580302071b1001c900c1103482c5000740c0e02c8105a9440e0070054600752401064a8100200044841d51060540a506001d040b41d10010301c519040c5141191a26145914000840d00304410401801c200d08042201c0340d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 548597401 1250 548596151 548596183
    0x6021e030706180219030302030f0f09041506140310030b060604090510050109080c031c0c050a14121207200a1101020d05181201090213052502 63
    0xa1181292441c01060806400d1034501010400031000d0325840942d898420390b8092549034118541e014502c2980c0320281c00341c0c10401c014440c2c00e007000024031000441c9403410f030900c4c0c00c242c045400c0312001c1d088400d8486960f4030912039160494500c03102800400403081c51031030100c80ca41030703c403100d2100134407000d80580454519a00d21058402504600d0010041864400c40c4030410020910130329020925038140802e40035008038580510707900c058001c0c0744010210709008644041010310074104032a003400c41c000180e080c004002200c0c00f821103540d250216115003403c6c40150b0300007460440017000344000307090b061501180e0000003410291819242e02d149143c299410310349401450080000c51020484800700045201d00203a08070b5810b04042d440948040c49019a01100400c01c01d20060baa85043d40307070710301015411400403c00d036500d03a0200e50303c0c9c1c407090124104103442d801001a030f9490440e034500181821884040c2c040f81d01c0320302a440b03d403011550401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 548598651 1250 548597401 548597443
    0x91503060b0406150c1e0f030822050615010801031e0f15020307091e051212120a20030f04030c080a020703030e040c09260105010608150a0602 63
    0x2035a55164443c20050049424074524184400300090060401e450308540b0550f4410156440340b456090352500b01e0b40c880b4a40c2100da6190720243c0e03044d0001010b152014880c2c0107a0640399410620b0640d0ba14841c1c0c0007442c3c0c034148680c80c00904500c8003031707840c10840d03040c0040000ca0703c524810283e01c000807007000c0c042116070800e000b440f1400301000c3c1c14a142c448810b08100c0c019401544241d05a40e1030000e0143c44980c9680c400c080c0030b0040605038194503003840185042c00c0384001c0c01110b0b00413200301d808046a1003006400c0440d1280c0c80700411001c1080220300d07801203030004988010410200c80d42880c00494074040603080c84c13503035021040000e0400d1b0051103040a030076003204086071030b240c0030b000c001c0d580c00150200328006280c2030003004003420070380a2030b290035041c2d4517681c0c06642800440d00c15004a107a0803020030891151b40d501c0d504003845501e0203492030f40c0c8d502c4c0c21441e00f40082080340d541140c1140c0500400d000400c851980840c041c01c1c809507910003002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 548599901 1250 548598651 548598671
    0xa0b010b0f0f03010f03060e210a052203120503040210141303110114090a03080a20010b0913120305091f140603070605120a14090d080109150306 64
    0x1101d8011101d410240340c600000108940c66400c504208503840b42400744018071548104540f200e040c5140403801ea1180c0c10308010400c40d2401810098013503182950412028030700d02481c114000c0b020500f070900c04141413081c848400151a1402c00a0801d10b03e141041d0f8046884083c0580c100c1040103409021041ca074402c10003220704000c094842c0061454507818040100300c502c620340c0c2c2c0400c500c0000222521303403080648035090401060800036074a10b403180d8a4585c0007200c3d007000c0103002202809050700042c000d42060030110b0000441c038403848284003482d00040c1414281d51092001c6034000b900540c1c038404c122207540341c0401c003500e602a0140c0f0b800940340c140c8030f101c002d041540481c0203881d07028051103d84d03c009408151124020f0584500d0035001d00d10002d04200040b5000102e0784c0c610540041c1c1605d0001081003250068241c00d11080e00d03444070982008181c40351081d0b0100c1468094413440c030080000070040042d83d4694841d40c4001485580c94040c0c0e11 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 548601151 1250 548599901 548599927
    0x2101802030f1b0d08090609010203130e010f241805151201051203030a0504030903061b08070228080d0e030a090f0f030f020d0203030d1401080a0b010b 67
    0x4149550241c102d440c0c0405400340c49807210948071a2070320000c208505801c40b45800308403c24265044611603141c20b5221060007441c2d03001000203070551208000444480d000c04082c0c80c01014100701e8185154182940c5011001580d030011410032585103005420b11071010008094448504084242c0c03401c0d91002c1c0c05006090b0f0040b0383c06120050300590052188005003010740703040b400000740742c0e02c1d407080001580f0990000b8841c1d602c00d000003240342c1031591002d40c0040c0203041c40303013000d0354a0352400f00b681e2030300d040307480c0100c0c0d40101400c55075004901d103078001c4004d0000d400142032205003881010080f032031006020001101450a00080c0002c860103022400c50074049464983d00c26a41c030381c1710006800000700c102c44001400d054200c0300741c054680c5c4010303007069240b440d1200750b4400034942d010b90340800d883d481c0d040140d40800050628034103030710300412000070201e105500c5030416402381e440381c1c010094003c000340d60322032491f0544940c000540d03110501d0507001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 548602401 1250 548601151 548601191
    0x50d050a02040e0309011e08011e080709061e03020306060d0f0203010608010608100519020306011b030f1403010312081306051302150c1b01030b0613090b0604060210 73
    0x40c2d0000d25107000075250b540d000c0000c24800e0003e80b600c140b020003065007046011500824180024000b10050042d5603065007060f541c4404843e40880b03054840d5201410304a403580070350310740c554484082043c40301c0018000305002081400380c00b8a80340d500480e403650b02c01054030348245130800d904010495150411a015070b0003500810940c0c3d01c2d864810700a1080c0c2c0103015440c07151000c01b49483c400c501850740725422601201e2142412840e000c40130f1b420180c03030f440c10311042a00c58407545045500301c4a08078020399075500303460404040500748000c1500d064100f5070040005102040300c81c0f0414010040c5d0340b07030248140d501c00201c8081e6001c41e46000744482d01341001d20150f5101d055142c0020360007101d0001110300294000c60700d62243c51300c9000283c112280d000f074080070b0400d01114042040c1004600e4003590350000d242075215410140040f4000c180c10b01c014030f5544681034a24906403020761501d07050500c040d50f280080110040c0c903036100c60700d100740d00c00c002e900 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 548603651 1250 548602401 548602403
    0x102122101050f012102160b0a180c05010e06040503150a0f020705070b030a0b030313060305060609010e0108190e0105040507080d08040803090c06041401080906070504050103050c160515070203030709050d050a 92
    0xc0c0d00d400d030547c0d14020001c1082a1030040c00c2508201e00110001c4565803103900303156214203000e00c1c0514110056520300b295089250380454280400582c58609000402e40c014904510282c1c5240811381c0204440400000d555a1481800b01d00c00017440010400e00f910809030030141c03030340d80d205950006000c1140800d41c01d40004140608104c01e098118015540d0949081c404c1c0d076280414864a4080c095403640003071a101c8590005500880e0000d030401c1c20150540c21400c0c5176155041a200610803d04250313564200300801d1110074803059001c1c0440070040c1960b074002c8100148403030341c0030f48080c1000e08000003062603003030108160b620742c1b40007512454440381d0740e420322100b801401483d240400c0241b000540c0b9028082651481203000303032100c0c1d04203030403d401140104801085940c54240c02c003c1440c004d002c51040c818800c1c400d4004003d207001c40e07c035210900e40003805400130355005005100b501c0b0b800c00345003c1078450070360301a001d508940c10110300d07007501b00038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 548604901 1250 548603651 548603677
    0x70e0106020a112b030e01051908191a0906090c0a050c03071703040b06150d15170717060708071103071a0a0c02060402060f03060102122101050f012102 67
    0x43c844d001406405068032501e021b030315851801c0101c074005503401d20410740e0120b0b01140310b240a284680c0a45186500100011103002904802c490000304031500c21190b43c004e4120640b12907490324211142a5004d0f200b5a400d03c924140800b00c0c040038069001c24000380903020428080c404c80030401d507040c1680010035544081d0702d02c7c0e4048500d51094600303658050203c0001900b600300b10b20b9480c5170042c00b6642074507004080a20741c005204441c45140c070340d854550000f880d5200d100b0840c2c01080000d02801c0010702e0220b085070400caa407964015550000d0040221407a040141640c0c8013000342011000010140040c078118851040000c02650326818141030002c0008205481140200001c000106422805995544044138001d60103202000802040607041d0041e60b04003d040c01201c11004400342c64026070341000b42810003550b0b810b68071200301e17994078654074010641603440040c602c00302d10000b082415000700513410549440310b401048151903040715261a9070361 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 548606151 1250 548604901 548604949
    0x12162c040302150709090c030b0922200301050907080d18030b07090519030f1b1503090203210901080712061706070201020306011d0a1505030405070e0106020a11 71
    0x4100070300b032a1072501818100500d809084517540703000348501d41c48274600500038aa45d81c2c5c0c0c80d01145851400c0c00142ca041c15040b0861800551089481d000c1d1080700d02c0d0345500d40860340d0504d82140c071b000300004520b5005d00c0003041016030105101c942804107182107079440202d501b411003070b80c1c00e80d80001d02e03100490041214035503001f18a5020783c0c0089414001c84030b00400d461078409281d0101034101c03c0c10b244244000fa8141302c0b83c4452144640c205003440d50344244909002114500c0c660101e40c50b02c0b4241d0031882c1c18084491441a11058181030104103180304540e80504a400303814050101c0118032400d0090102481041541c44280186038a48106140d10011302c101d2101c18400c580c0410107440c010b00a070f921900d0182d6445202a6580c07000d000e0340003514132515001041c5880c00b144240300c182d40ea4180543caa00c0e16aa03e0410b4070745545011803540c8840390f05104600180b107403a9000c01c98404440c3c100b14070341c603000348050001d800c0010300040e24003070f00915 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 548607401 1250 548606151 548606161
    0x20a060c031707090b070f0c180e0318090603010f0606110f03030c071b08010c050306120d12091406011d0f07052712162c04030215 58
    0x5201818214442d40e204411080342c003151201c085000e03030700c150100e400c507401442140f280c0005080341e0b078010420200d00c01e1407611000c1d1a008180c0008800003c44601035203100024000c201d0b10f003002074025413502c1c0e425410b0101d24205008150300c03c1e500e940104070150b5094008009920031043c04000f01c603038510b0b003c1d105803480e84051340e040c080d03050a80107600021043ea485602c8d566170041c03034111180d0b110001020f104081d01070102070380c18041a540e40034403803e07881c4030040e103419540c0e041100070094031410305003c003074050f405820841c2901d580560180e0314080c010070040b800007811301d0b15050124541540c09018403501d8000250640c0c101c0f074034000038410540c03c00040d1a01a00e90700d0202c000c032000740100700c04200080c803115801b846c0600024100b20350400248080d00054031151450580011650080301c943e502c6008126280340182848064000f0001c0c00d010007030583d440c08a40c100c0380e07104850000303050600070b00001841500d20482c1c00494505 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 548608651 1250 548607401 548607407
    0x10030c02100b090c03040c030b0903070314031b0d06050d0b0a0b0a03030c020607060b1f03060b0a140a0c050d08011d010605030a0c0318080c1510060516020a06 70
    0x844081000188074052189445940610400d911004090400b8000f81d45604840d54903a00c090412110094083c000202091100071401d009440f00800303160b43e5081420000c0c815290004a07541448003001441410340d41c400341c8848141e009181e8036107c0c2e0f081011103004011a602c6690400c001c0c1004a007000041d00300c0fa84981d0b10700c14100b041010071001e002000c0c485000c01404241c400c1e018101500d098005040341c18800d41022440ca140900800c0201c110400200500c04100c00c25803540c9825020b60809080c212a05505041103c40018100c140c8a100514a0580080c10b880c00380d01c00d40100384035581250890b82401c1d417040b0b0090005000344238402851090b05007060441642c0391041e0304888075545d4003070031501c03850580b1000700004032a220500d552110101078440f05045150005401050520b40754104620304c0c9050100c060301c010100007410040055441032481910b042d914945400781d00c034440410008243d16408901a6005080711000a80c1542c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 548609901 1250 548608651 548608661
    0x6020a020a0e040f060b1903080d0c0f0c020f06042d32191d0f07020a1202011112042f011b080f04170d0804030e0f1003 53
    0x48207403100400d40365900c441001035441036030028481400340e903080b8041a60f54100c1054500001e02c00c00303400181146e01609112654421034042e5008030320700c44621010300c118642200301e030170440510240c0701c3c40100b90840710f52009200d8810701c80c9100264880009840242c091103000300c40c0707401440c01c54140038030b03a24091980414039440c04240d4911440d80486017004034001c3d0b07403000c4c01d02d1221001801c41000f90b260456601107400514008102518008003d464100d464003510b1086000c4615001000002c0007803100d4140040190300041c07104402d86c0091064600001c00d1008a01502d80c42c3d0000910801c0400c0c03440c06880b01603040c60059204251200f414205050042e818030b054266086080f010401404129401071074980c00512a869040051a241d03075903d07000380c1c200405d00c89081c7e801250031300c81c1c83d4180303020402403040c40d401082e04203046613000b4884400148001d040001c05140a0070700d0f01d610051000d040d5001704550303202c164499009000702 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 548611151 1250 548609901 548609903
    0x601060c0c0b1315170c09060706050109020a090806100b130807030c05120a020a140a0e0c0d05090712062703030b091003050a06110714060601080a020f0901210606020a 74
    0x907400341a240c80c0c243c01422581100c1c003020b0100b07001399903910300d51b800b41e4209030038454000c14108041070000c1c48a00c00c140c0a00003d441c01611982c1044004043c0c01c000d4011003c0c581c0030200f840341e2804c26400400c115101c07604036950340c200ca40c10150790565242d101080c0c62245000c0801000380411303012084c0c41050300e5900c00e55043c451000d81d50034861001940014880c030084c80002c0c12203c2c4a204410050700f4010000d9607490303001c20410003169461140d51022031403013004040c5001b000c0e08010404000c0c200f141c240701c90340e907000040c103400a20301603440201600890b243c820204445038050001400038249040203806000208000d510840c42c0c000005e084144175568201078a802c00300030100510580da030704c40203000f40d007040f40c05810244a583c0020b5452010801407100c0f00c005000141044e030000b4000c0400030308000318280c01803155a90121070300b400d50700066000d28115400181e20320900c80b030745810b900819402410403a0202d0f401e40c00254001e405 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 548612401 1250 548611151 548611169
    0x609100305060c04060f08130f0606050a0905150303270a0b04121412040b070c030c080304030c09022718090c0f041104120303060b03130b07020106080601060c0c0b13 73
    0x140000030202c3c7c007140d0856114081d440c4203078107180410410300070720b01024820500005c01d81d88800008582c62000d900c0603003a02d13107030820800c082441c044981003124054008504003061880e4000d90800314050740b165000000301e10403c1940c480104400422001c56070b50b6840380c9840c41d00e102c0c0c4403441e8090310060104921035500709d40c005010344100055034020b40c2441e061200c281001d074010442601c800c0c4415901101080d2145a102e00414400c4011540e461540c90400e0106600c0d0b84901c00552041c49403c0384e507401700303049441100e030a10040011030380318030002e0100b008844e03003110065411400c105440c1000200000807440440d443e0105060040401c400d071029441034015a40341400b04121002901b140c041e00e1034840d05001c0341464403501400c3c1183c008451904c1842040c1200c0801d2012401655410132510710092059606103040079a58a106100705420858400c819a080c000410210300c003412200c100d460b981c4007034250440001034280204d543c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 548613651 1250 548612401 548612417
    0x3031d0706050901050a09081e0d050a0507060507021c090501111f0b21010203071413062604050a0201201005041509030914180609100305060c0406 65
    0x110880000368482218915922280303800b4041c0c1c011500b64011108450030301408203c0400e4101d0140030b04c1c60700c50104d5410b00030442c0c40c01c0301145010122a80f200c18401c0c108800d50041c0c1c0d002045690690b08100c001c501a10385450407840d0421a100c0c0501c2e01403001d80000041c0e90209490f02181e02c2640d13000001c801549406499082507420b91030205962000c030b2100640d035410100d81080001c00e5002c0210195028110308140c40010f216581d600104120501c0e80040300140d000807054070f922706180e4520320f84448221940a18420300c4030000660758000c40c021210300f1500480300c0940c200e4145440d11035136074461258100e012442c013030301100c00c50690f08500031403600710600a00c0f1603074036200454014034010b8800d035203120b580c540b40c0d43c0d030100c18010044002e10954a0344007080c600056900005010802c0c4c910644404c4e92600d035400381c1d141d45a0b006841181e514056890b04028051010282d602c01421350080e0010811420103d0018108440c0349407035903d4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 548614901 1250 548613651 548613701
    0x181c0b0105030111090409031b03030905060c0918060a09090c03020a06020c090a0905030f0304030f140a0203040603050a0603021507050c0301050417030615040f0305010b0a0e0c03041104090303 85
    0xc240ca0041c011000308404c18080c189580c078141c0c01c4082c145019080403003d5020340503040d8080302c0e6410040d4013098a80003100d0800c50200051540201c560044d14100f16410300044c0d9208100c0d2000c41984e8440c601040255171168210360042c26070001c1000781005503d03004000814a11050b482842050800200381b800803420248900e0700810084c03403559044010001001485070554a82c8010b004500c038280d072410044d40510f001e5228103504000144000b000d404103003640101511b02400b050310340d2038000060320146c0700c1030309011600d0b60740c51000a000b00a198000303507001000b0203032540510005001003d40c240a40b080d44c2000e0290030a042c2030b1601070720010710041c0d0f01821070204e1403140c4003030350300180c0050641040c55502c000c2011160019003260750045e104000c2002080001d1082580306c00041d5807583d04146001031103a2b01d81401044c0c2d4050040020011342000070902c40610741c118001d1041000440314113000b0020511070803048107032208410654 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 548616151 1250 548614901 548614903
    0xc03100f0605060301063207060506120c01050315010c020303180117090a08071505011403070905090d1407080f040608090c090c0a0e041a0a061d06181c0b010503 71
    0x641640da00d602c4290030055030300a00c620030100340f024039040e01e500c447d1340c030607154610f001000c00c0c03802580c0200703c9041134410401022076285030491642d005550400050342c01000342e99000d20711918072051142d074180184c900c9403c0303840081d81804001218040c43c00002c400e16019142030b0707205d02409102c04071816100c181070318281100d0b8031038204600040d440c20000c00d400d500c10301380320001c51101c400c010103582c02070b089150040070a4400c44d002e420104038940c010803601c0300500caa4248018000d0b1100c0102c4403402c10810305052440800007040300301e0390803a0b0320401c565a42c846040c460005034119004800000b504200441e141190019903007000c1ca200030054005074440d01d814480c00e921040c0090148806003c200300c9640c1e452103102c45c0e40c4a00c50b65000715607051410445a03a100d500508144076024003c064a210040c25884090b10240c80f040c0e50344104103514901c00711071669280c1c3c0040007220201801d01500c40b500202e52082c84040801d9883d60205 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 548617401 1250 548616151 548616157
    0x9010e071a090105160c140d0c030f0804120c0e101410091203030204091401081513081909090c2f0307030206070e030d050403080c0c03100f060506 65
    0x4507440509012144200c4401c40c00411107503005050152030b141820401302d07124185840103680000c2134003030800c43e030008a2500071310200100c408040f5020300d0b64410f0780300030b00c038040503000e6070407491401c00300056102151b005c0d1200710f14185582015161005281c41113000b00c040c00030125010070720201d0b5a48086056901059641c103e8101c094140030f110041c400208040000304140011968007103412107001e04d020365000340c1d07601c1c2850296011381310345584131500c0148078001000350a1000c5001e084501c813410315001e01d9224241c40d8180c003a1422800340c440e41000502d00e100340c6500c0b407060b071106030640340c10542540d2a03d4400441e0314041c002c90106a1880307040360021138031000d42c1150b4021003501c01c1661002540c407455a040b0100450159003e00e0a105d1802d80010480007420012001814064229440203200d4000c80c8001020303500c012070703050405d1600b8048641c1110001d001c0b0ba030b000350781d900c2d440301030004104201c913003e15180022403a41001c00c21 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 548618651 1250 548617401 548617409
    0x1103011826040e0a1e111312050601050d03020a080d06031b0b04170a1203090b0f09030706020c0c090f0109060914060d15020301180f0e120d18060509010e07 69
    0x1014806071380340311050000c0c101e070355160101d68150354514603210501e40b040341544007401d210340d0380f03454128920340c040c152a60080840c103400f00a80d240090000a0510305542003607807e0000c040e074600d03060740b03020320844000b40b0f840804541040d00340d80c10760100b01203d000d0015441818803008614401c80124004d000f5400e10800042c070580e141c0c950640600c0641d8021a545004241c440d504d0308050420000001f940b2101030703100703011040d00d055402c811490b41039441402c01c966507039a00e205010000b05241e8010481c4000c1c41014403040e40f4414001d0300554181c944000c01410340341003401001079040c5054000b060b2040684242c06040c1e814035002d8101d505c5800030000740c0da04211003250a2450042203108600007030002e14001c1c80e400c0d0011107400294904034055a00c005000d800030340c40c01d0101c0e124910f000410b1106007107010880c80e541d081c0640090050040070000c2c01c20f20100c88141802c004081e401a4810702c04500204403100360311a000d62200e13404c0c85 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 548619901 1250 548618651 548618669
    0xb0717010620070810060f06091208090301020d050a0e01150e04021212130e090a0204090c0f12020a1202010f050d060f170609030412110301182604 65
    0x401404402c0c010240311040c2004072280500c1c02c11040c01c00c1c0c0c50090300740c1000607640c0103541500300000c02400740c1e4003d008200f80166030030342840381c0140300f0340082c4903420b546c0c0038070242d06041c001d828040b22003120f40035000359a1100c6801c50080600819540099454940a0309a120041c10321501d500d81030410080010240750001c00000c078039000c4c00507680032081c140b0f81c1000d050300300078207081e01144044094a40c82c01030900e41e404807807584210f1001101030104003000f40c000c1044000d071941190001545400b03428030580250a84d00a40d2031140c2000010074850022140c90034918800c070303420000b40c0e0302c4000700d40c41c120081400074003003600c00d02e45890850050029203803110b20361b1030005070b1555841e500b40301204d40e41d000101c0c0c50480b44000030049404c0c00019440024400114541460004180d2a00d50303118000391044030711100082c1c443d5000e401582e00e415100005403110390550824054110307901c501000c01a4005400018061141007610200c038000c00e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 548621151 1250 548619901 548619947
    0x3110f06160204053103080c341502040f0803090108190b0312040602010c2a0c0906060806031902060d0b0f0a09021c09020d0201051e040b070b07 64
    0xc0e00f4807018000152002c424500030320200354003070b0496a10400241494021309440c1d180c54103000e44100c2000c2d00081241c0390400c0700035800c80903070545203c010417046d5510380007060f110000ca295004800c0050618440c14000403042516802a0040c0c8060442140056649200781c55903442540a100d010a01103030000c1c030188203410304e01c0442c0380920700102e4040781401c0002d08104041040740c8400d4004102444080d5091042515040300c0c1e0602c8040f00c2d441d001c48240039a003030351940d00004202c052540820014040801c000e081c5207506004854503800042c0440c1c000b104c80c103000b445142410b0340420001070214034982d8018194910b040d000415501c05841145aa240c200d0111810015a43c507209820002000c04040050311400545440f00351200516020300c40c1e03034140206200540c2d504409904aa075090901c150303200b002003501d0000031007480200c06460004200080c0c0d4030500c0703004161141c8101d813401c91a6644420a48084082440361218401c0c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 548622401 1250 548621151 548621153
    0x305040320162d050d022803061b0804051f090b10090e060c09010c02060c030d05040308090f1009030e0a0602030c06010509011d07030e1e060106020d02030f090d0c03110f0616 77
    0x2006003402c141005156003400070201200210305c2c8070b059008442c12680c1d030080680c200c0c12b09018030103075200303403a00a80508054907859640e8181d448080501c494030701c4050a03504c040d601a002c0e060384111000180c1c680700d550070107481100c4c8510101daa08142e4060302c4800d0200341c1d2481881031030b5202e81071041d04030046501c8045008100c3e08580308200f228100c19080010341110b261151000c03070a40391502d0020900903001d00009015480062014140c03580400c481001c080580c00c001a1844c0c181821106022895031954000c110201d02007003c075408001491408040812a425640e130760b02480803c24092180712a01071049996008003200c2810040d00050383d07140100d120342200d06441d0800c0c070460101d503035804428410035400da006000090050500b07001400002e4032004002c1d440340704034062103034200000a141c01e115616000198041908461004280e40e16480c014806140480300c0c1c5108810b03403030a054403450300408035003402c40c0325242060043e0003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 548623651 1250 548622401 548622409
    0x61603030915140c090312030a0902210c150d0504080301150e09010308090a0905010f1724130b040b1e04020f04020702060f120105100305040320162d050d02 69
    0x30060701c5e0781401950401c1c51f0780e0302c4101c0a9030180d483c050b000515070000c1e00c100402035050724019403170b1510301069480d10350004110011484416a4002060805500b03005018803603450740b80e5409107004203010a00400e43c01440c180c2d04c801c00110001032030381405440f02403802074600c0c2d00c925824018000680c0f0760f80a8007003000040e00d5010001d80318000d8406480d002d800824454640010420581000f0b44030071a426034030304080c1000801c8002002c4a410b42e8200c0101c2d02105003011902c10400309241824854002c007401046040601d40090b100034141c1da4900801d85000880200c0b40529004a01560380103161883c2e1103a544103100194003e850240d90141c0180b22101200c5104d1004000f0680d403d0314882880d81020700f0080c01100ba02e0380713501010702e007504201c0004d400c40081c0304a0300c914400503400700500e520007071a0103004400e0594032020560001250195110030f0405041c0300140c083d0544a204072080d40429a8816141c1c051400c402c18405414 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 548624901 1250 548623651 548623657
    0x6080f040209071b1a06030c01050f090111070b0c01050a1d0d03050702010e01020412050106080706230f12070e120601030b1f12020108151e061603030915140c 70
    0x1519403006003801a1039241c207900c48050b81c5c00d07501180c814904100b06840c003486815170980c02400c01074109041401c00364111b00407aa00d05051121028001000352010400100106140c5075007a42c0d5a10701c1042c0381c060002a1a9095013505000075541c54501d15803039100080400c000400040a030424200e018000242581c0c042d5562420705c2e8100c00d40c00c1c00144080c0c04038800c3c244010007103141c00d60841d80b02c0c0d8041032003a0003280d020320450b94130030901e48900290400e04041022415510f9070188500140301340300d180005030549010040704409441850141c07070741c11b21281c0140511a02c1003400c081000700d03810090040c00002c00d2a0032031070300050703284120800f45810840808290703030950070010801181d21a40d40456a200d607541c0e5000e541d22441e001005041c00c081036004d01d0b02840c110802000d400400039540319001904c00d000d84420706039504480704d0502800405480c5003d40d40c0190b42d00c00900d004405010b8442c0700341c10300341c0c42985a907414800c04c80c550 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 548626151 1250 548624901 548624927
    0x90207020306270708070e0702070b0703110c06030a0b040c02120f340c0b0708090907020c04052403010209060433030609050604060602030316140703020706080f04020907 75
    0x3010340d2400e0380b45403c0411094000d0500c2400800130b00d402d100c102462814014040710456001010902420443d038080e940d106070305041068040c900b21842c2400e0580100e0100e030414804420042100055041108110415502004001c000180490f1918a203400c5104031100c2041003070008450140280044007240d002044131200c44c0f41464440500c04000c500d5112441c1c4500051294181d000d800519043c12810f01d404815a5100941d018000029105080090010741c0c61402840f1940840000074420046450211107102002001c030100001580e1200a079166604052080b58400c11004004905243c40d2080c0b03001524501610315004c502c60b07141406044030202400448c64201d5100402c003e03040ca02d087c3d040f075600902d07951180c0d0800508118064022040301e400c51034281d21606101d182013400c5d00d95921100300300034201800a80f00c810306a000c90f05070b0a4880755990280c203600c400c404180325540c10b60f8080d50010156001c20300301d601030b10880f4110f03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 548627401 1250 548626151 548626201
    0xc0e0f06070c0b090907022b211e060509061507050d030203060907170c0c03090a03060203070f0504030b0f061503240d150f1d0c0406090207020306 65
    0x1c0001c658a500000405a0040960540200c2c00f2600c500d0500c0c1c20a030b0001680c4000c2c8a00c5180748400d500642d041c07030b07045c20402c0f10160101c06940c0720b445074403110070300500445c951210303d201c090700500c03200300500101454100880040c403441e0090600310b030710003068050f032174aa103010014245600d900240c500b110402101c8000b82080c03012a24260654a0058036850680280074014900421280810030814124803001caa180d840c680c12070b85441300a601c4207140d0302c14510710710660b440a580607210300c07000010402644c005610407202682e80c100c48003030399182901c650203a03000003000c109907000010001900c1c072040b5540064010401d41c4841e001600c40300310380d03005484804019105100962000100c008050140310381030355074001c112031580b150f0035030200c50b0b802558180d480b1510017441a2a41d00100e05a9612600c2120101684440c05a90702c850302d0400d405103060940006500800b8030a40d44001d4015003d0000e070b569402070300d117014070741c10001c04031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 548628651 1250 548627401 548627407
    0x90411010306081504110d03020318032e110702032a0d0602030f0708070230040b0408160e0103030f0c0c0b0c100504030e060f19030f0b040c0e0f06 65
    0x40400401c0040c4d840344e00e0b01081c0d0703400d00305410800402c43c1070180d12030050b4000081b002c001b9034000104c4030385e221107025040d03610101174002401e10514601500340031582d6440f90098043c040d410002c0081062400c0122001c031640b6111580100c01d4041c1d855041044800b01d11038248000d2251106c411811383c50204540c00040c030714404070001611a26808410000e100aa00c200ad940140150500845a1800e9080255603800f200116000107818034100042141c90307100d5050381000c20304500d600d0b142c65013155185500a03203d200c40610852004001d0345600e0101c00c0281c0b00e580f2820030b140ea0071510192081c26402018400304200d50500da800b1505100c040400381100c0103400e96200d015402e5645080f03002811424100d26080601002a070030140c42c080903402501c0c026220324000840100c01e01607840c00101404807034054610642c0d0692080c04a410780301c004010003021442480100c076454080c01c004150b1800c200061031401082d0091054001071020789 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 548629901 1250 548628651 548628659
    0x708070b1207031b0c060c03112704020c0c030610081c050706090c180216061e02160b090607021518010e10140405190f050a030c150b090411010306 65
    0x104c20a02c4500c0b120004000c102400308011003070141c0d600b898603600d0300b40f00350316103403c001c4003510400d81011030071a01092000210494401d840720b5140f0014011500d03850614440c40e02c03114215440703032187c043d070800152080da007a08840186d0b003484005021104040c807411072500342140c0b014060000902070341c00050000d001e0310b521184a4642801018a000500e488010f0004040e400300c80c014444621101610b85c58001c10f10340040c030214414920b50030a0039031b003540381e81c44c0150350f00010b00c01e100040d07010b40f0959510304c501b001c11180c1d80d404507000d465140c1524101c005070011030b00300104003c01c84100384c101c81000d810704600200d440140303003110003c0100c1c40d01c0c4d070024004d5000030b00580c400d403480001d9418031200c0d80e1502c0c0d40c4403a100c10b0644515154007885aa01c03100f4000300342d2450740500d5114084901d10241030a002d45420b18080089480510404c00d10340044018090250076030000303005003840703840b90b95601d0390260012030554105a500c0d8400a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 548631151 1250 548629901 548629931
    0x30503090f0a1e031b0518040c050a08030a022404030305100801020d0e0705010e0a030305071505090c030c010f0f0c050307080a050a030e0c0609090a090b16020708070b120703 77
    0x1012240e0320b10a0300c1502d61071450407403c80029140c46140217560000c0410103030301d801307510803402001c0d4120041140c4e0b0b5480c000030186400d0b00081c0d001041c4640101e0301840010040220044980032203a00400031030401c41e0000d0225500c8800542110110300000c4c0aa0031003508800c0504000c81c0300b80d12148001d08903003011000107903440c1c858207031040400080c0300900c0501400c0c40c02002e000c3d4030b000880e100c00080e04c0b0050800c10001034800c180581e074181d4202820f640c5070240101c0c02d02c40c41e410313500c29401c0c01241c402c0c055010101c0302c03503001d2000e081848146807104100b0410f04c0505487c4104980030541c0c0900041240800040a880c01004c1c0e14901d500c0d01902c030f4000c0e000003022036030b4010091843d80c1c4003004034295640c0e01029955226401c8a07d0050303580d4020210014001e0b06030000d203c0254a030600c40440c28807503c01c001d83d00c00b5400c54403401e0f59004072079039410361842401c0c0740301e40401802c447d01c410003801560142440c1800708441c480141e0320 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 548632401 1250 548631151 548631179
    0xf0501020c0709060509072007050a06030e0c121b030a020301020a08040b010801050c0d020702030f01050702010b040e150402280303200d0807181a03040516030503090f0a 75
    0x40c0ca5400100d02406a041148035010252200780c4170b460080c603051001409201950011010000e0181051070023504d0400c0104050031000e8007803001244e6425025014004034420401103004c0d04c1a12002d5042c020304034024003200d04001c080241c41035250940c001c036040010b94140c01003004100150b2024002807a40c880c90341c0d1044058a06410061380512060b0040840b81e41403c062101e020403807400d80ea8010030002d00169100381a100180c90b010415a000102c0e5080400700690581c0651090b4000c100584041c41b101052600094540502c001101ca40004c0b02c40440c000d070034030a00d848d04820400c0c5650a584c0c1c00d0245440140c0030a6004030001040344010006411070100162071000c820801041c10b1158a403000d098124000e003102d041280d004a4074001038550b01e0200020b144c0d0039040c000c00c890b200c004004a51049800340c445105010040b1030143d400140841100d4000780070394103040c040410004c44280c001d80c4103501118140022808004140c45 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 548633651 1250 548632401 548632417
    0x605090d020f0f21040305100f06082113030b09060103061505090402090a060b0c06100b090901031b031401151403030a210c360306090f050102 63
    0x40c0038a03494064024544041d07041041a10780001c0c1505400d000300103041c2d9124a0901000003420300916540703041c074016580040c005101d0250145c140141c0f540c0b03c1d5851100700c0900703004045e21303680810f50703965078900d02e0004142c10b019038014030060302010300607000394100d180d008595a621400c6e625034041c1d40c042c40c2d070380094004108001044c4119500e80e5103085010f03007541d1400c0700043c0300600c0108041d0080d80d0000010f8810005680240302400700c002405844501500c0d809a0303e6030704454800d02c80d4112500030583d8030541c42501c0c0d001d070008010b01300d03503070a543d62084800c50b006c0d4010f4400d1400000407000940c454a0030008100b200700009003030200f80850810000282c0c0107a03004605d8a400401d9074a0200844500c0000d60500d000714028203401d0941341115101d036200901c1c901142110a1070f4010401c003d0140300b240590101c1000d05030540200c2c1c0c81190307580b001d0b83e806030204000303403464206050b40e90103050003001f0904075880c1c01d03086e64001c0304 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 548634901 1250 548633651 548633653
    0x4050a0b0c010b041b0305130b040204050601020a0203102007050607050d1103040807060b15040521060718091517160609050a2c13050708030a090603050615031003060509 75
    0x26804405d02c1d4544140d80d4071445000d0706200301c0c0909d8a59001c0c8400141c0068000e0b5100e03000280c469000300301260701c1603400307001c91f0040c203800d95220700100811000d010500c1103081d004054400c1c080c1c161001d950300030000d0101c0740c4a811007600d9550151940c010116100c0030705605410500d009075114600071720b04031703945810a103400d4003101d001d209601d120700e10000c13a80301c800010400740c5090303542c00d580e040780c4010340ca9581000c01c00c0c03891074190b503846003504004034160710504604800415041807030605480c0c0b24034005880514001009001520104100c00c40000400d444521650340684081d044030054107201001140c200b0004540007035410007141c105210303000001e28084040c60f4402078601184002c80304142901442c140d080d41c04203851150080e00050519448012204d105030707103c00b8940c03241c2104090101007403d110000500c41d0090056510505005082d005646501011950036401c060400b140040c10f0080100004215114031802400c16038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 548636151 1250 548634901 548634941
    0x709030512091011070e1b032401050a021203130b07030617010212011412030706090605160522090213030c1d150114030f1b04050a0b0c010b04 63
    0x2018402e142d07500d800c4002c00c04c40000160038216001240b858161741d907008149480d51205040600391b0383c1a28400b48802a000040c4921440e254526200b064040d525100c03400b580a00195941d0180016081c09a00b100c02d111001220f0f090080d94007464140c940100e40b911038440c20038544084900d903001c02d0342d8900501c189030a6002d40d4044d1002c140c0250319000d0014000b20a40c20188103081886404070b114100030340e229810700c00c1a41c00c4d00200e80e103c030a141484009414110401e42d20305182c40c01003502d00034905071007400030004e5200d252802c0030084416003002007504801c0001d20b050030022901990500007012038902102885407841c3c15410108000c800a600c000f001044101c015041c40d031301301e1021980100e440c0e2010b58010089001661840440910502001800030030086031032039030303099140200051098041101c84191000c1a50704c654028540c1c0540481c50800a62030003000400103202048004103c004001001c9416210401e0400342964010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 548637401 1250 548636151 548636167
    0x1140708060306010b03102303060f04060b0409020105040b0315040e030c1501060e010c0501020c030a05040305010b15030a1808070605010e150a0b0a051e030114270709030512 77
    0x3000742e84d02500f4034207260341c5503041841000c1601d86040c80350b80c08941c07450745070f0454403a0110825150920143c1921450316041c001ca14403500100c40485810381380004030480e60074244181d01900c3d03810b8490700c0c80c1509181c90344c441600300030449410102c882d602494140c0b520302560701d12801c0e18008540b00c0c41c0b6039030300c0d41c00c00f0400705c00950074481080041164603882103402c0003050080c00c1c010103902107070174101d0192083c01200800c46c4000120710700b600b540440100111b074000c038000c02000c00340c03208000078907201c8404031002d0070003840861104c0b0f0103680048590210b400306181815095613504800781c0080900350360f042d5541004224145600c104c6a0740600220121221020754000041a0071054010115404404206018403d006100f15108440501184048201c110200070400c1e84240540302c400c1914406820b11402c01c11568810180c0d03a41451142ca44450050195044010f0100e01001001680040466414400c0c00b081c10403952060b81e44480f4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 548638651 1250 548637401 548637403
    0xf0b030703140c030c0d0212031e09100f080402010318020423060a0b0a03114b0904020d2403030206060901081c02011b020106050301050a02040b0a0f02011407080603 73
    0x961202d940c045d03000a00761050590300c00110038940c0c0e604480b50301a500e41400c0452550007141d80c801211011146884a1110481c000d440941412500c1d407600c280074010460303c0d4108007050f84049511500810300540c0660420341e50654440f40381038110340030780c0024003030301d038940403030300c2c480da0a100019815455251042d80c00b4406441e0301004514000b01e0341100c0c440c01a29504055456504130342c03040c0c8100c101c0d0f03603803040800720440204050709120165401e021410100840d806108410302100344500926030b81c400300c4a03800c00384a1024030003e540401c045003106503542111001803207c416220412a410140c0b00b10801e0a44c036020740740001c0a04075070320400d0400010040d041c4009624800c1e44d00800c0c04540314802c80c0801e0380503041c9014158003c90341d88004c0c051107a4158072650071204214020f124988030701c0c00e4041203102d280640a1010810485811a980920010000d0881900c000140600080119223404400352490f40015510703000b070101510b8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 548639901 1250 548638651 548638663
    0x60605041406090d0b060d140d02150c04090e010204050301110705010b0402270111030d140a110a1107030206070c060f032703050d0f0203070f170a0f0b03070314 71
    0x42035482c0c0d490072440c3c03000601906a85000149022913a5001511703a071200380049202d140d121001400c0100081950780d1281d000c402e54400502c91028160700600c1e2240c0482d00400d2091089807038181481c0c10301015204000c465811076400308030001da592402d12a454180c8181d40040c1d0302c030560791038403a095682e807074500c503c1a401070040310200c1000501030220b036441280d400c3d11511240b00165802e00c2100740801c100d00010603402070144c06034000583e0b0340440340c4100321036614424008101c60355004442c503059410b20984032054020006e200042c10980101d6a0b003503070f00c0e80050155800542c0840307400003410b030100212500000031203a5076082c0c1c1070501c80341910251013848280504e0385805000313110300d228420300d4024011940d020550300001d1050800a4520310041d42c02521600d00041241c0288000103200e81540003411031a82c580e00410348031910314401070400420a000841da49000920351070b541017041600030351241403512604010891120304200e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 548641151 1250 548639901 548639939
    0x13170d0305040201050906032205030a0906020715111e010b040c03140604050a06030807050a0c050a0b030a020307050d0c08060f0105070206030c160f051f020c0c0d031206060504 78
    0x1070a15090000503a0000c00707640f69401c2c02d80703415489039903509001031342c0d130ba000f00420009602c1e1552901888804801070603940c01a40301e50000954405040b665200288510b00050030b646030300451061145204030001d0b44080119140c1142c4801c02c42d640c03402d140a41d8000fa0b54950fa000580e04150013010700c83d22880c00d0801c0704000b5803038501a0014002d1a081c0f02d0b0350b861001a1162960340d110101541c0c00042c016212001450280c1d81c0d03089044041c0c47c09010f45034000340074a44102c0c07242c151070604030510b0841d102c000b504e0300603400140455042c4002070000020501080c0728541b50022a540e0f040c0e01030811000340312200340d14804003030400608200c0c620240e242c04080726007249040340f99680d40c0c1980f0a514110700400303880140070803070b0b51512605110000806101801ca04c410081040b4a03980d0780804900c21480300d248150000c1e4502c0d911071400ca2030407041e44c0c0c0241000d641c8031070800703103610403585640c05c0040840c030b000c5030030b0243c140300e051a62210 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 548642401 1250 548641151 548641157
    0x9070509100504050319050f0d0504030c050d12030218060a02010c1413030f0503040905090303010311180f060d1b0e18070302100c0501020a030203060f0906010f0e040213170d 77
    0xd0b0504000c00d8440312484e051b0032007038034204680f8007000030030405003801c05004001e41d0500b044402004240c1da100f80300a407180060340da004565031600c10360b414503070bda1020702c03030040c20030004094000c0d4100300441005503d0300c0c544031005444440041200c06415400000c00038032403c1c000d01110701d07038100090880e40c140425045241c40c292000292500410032070004902031034468554407694204e45012401c20080c80070507040000510b0503213228001c0403c100c6650414482903110341000541943c280202143e04c40c02031051b07850304400040c08984c0b08000036259581c4840700007111000c41c909080c03041141500705107603a81c01040041120040250401c070541d903d15a50001a104e00078807460140c0c0d00d4002c006101c11250300c24002e54903000800300180081d0000c80d0402c0c002c2405c851101640c1c900054450b2181405840c0d10302c24041182d001ca915200410302150016820080300d200341482609601c0103110702c1040d14251000d488415041c140203107080818 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 548643651 1250 548642401 548642407
    0xb09041802010e01050c070810021e0304150908070b0702070f0e040807060b060c0a1b14130b010c050f060907050d0b0115090e070e0a1a041a09090705091005 69
    0x140e0b07100f10300491140e030034030340b0030380b1482480120b03400e080280d40034182611402440b01c0d5000c80c0d170b4014110b0110001d078011250402000704030601e1004480c000d04034910b00804014900c4140e00131003079103029141240c01c0c9200380d0340d44200b45c0000d0321204050f0340700f00d00c00c000c42030000c41c03c540644200c00034a0010b06083da107540107405482c2005182c2511410800c3c1300d43c0315002036071240d03010310003120050b010906000b010b1609401c0c20380b540c40f1200314080765030841103026005010000d0808d4042d040341d00d400c040100080c02105042009a204540c04548100100d004840140c40034010a00300324558170320b40b080781e6015034065840d01c1d0040003c907454008090440b80794100d80e141d02c0790042012138401009800c50303070049241405001c0895844900c9441e580001c0c1c91040203d030f00d8088150910f0002005000390060402c014848064850302c043d0005545080d4141040386d22000100c2c0c0c11401c81d40440025001300b40300c0d0303841c03400480c08224020a070030083e01e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 548644901 1250 548643651 548643653
    0xf050d0e09060f1206070518040e030901030902040f020d0506030607032901120204060e0405090f1207020a080a050303160f09150212030711010608070b07030c08090a0b090418 77
    0x3007048020002ca12500141c10000c0d910f440f407903605241c0c0040c060aa40071441c0480020b4540d0700901c04414400e1101c01c8900542d040610500c16107540c17a40080d41000e900c00b004401414421500300e03009500c0304602c00c1c41400900141c101d4120550300401c162910400f41803070201c00a055104041c148038071010000104060040c20300d110401d4403540c0d4044800580756442205c0c031785060503100180001e0229800103030307541c400a04841c28004d41d2640e82d02150380f082c080d0001d0a0741c3d0441034250100d0403001000b80300f001c1c406040703c000d8642c0c5640e443c0c1440c2a8010654158000204120510100b9000000c48000391b08010180707030704101e001444484071340160080c100144040c600e2a5008010f03000e0b4401510001e281e6030700c0d025200030010312421200c00619828040045520390002c41c51400362110000070500b030070500c1d20100c650182e244010b480701072003048104002d4442e541c512020740765070348140c0c3e41c0f94080414003046031028501244003c60000c5000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 548646151 1250 548644901 548644909
    0x40303110d0c0f050c100c05060f0402210a06020c0109050601120812090c0a060906020f120a050306061b011a0415090e0114011401320f070f0f050d0e 66
    0x104080c2d8000c808880c100341c05280c45843c2c0f1900342500386d40082c0840c454000241d1042e10900414030034000d440035a05c03051a0981d4450040d90000d5119110300ca495684000c2180c1020354020b003002100c201246648880089911010034030903680d45418000e0140841040318900421040c03441c10700701040b50f101c2c1101806542443d0301070140c0b84002c12400001000752401c0c8d0f0704002c0203190407513503514020b488240e05208500c058000c44441310111640403030700003c5c8040001c0d030310349880c60301841180c0307075800144019403100081c84100e62a031310f0080400300900181c4000698188844103102c0101005805d082c030560a1210a1a10f2100070034400c04486007000c2c08145010030020481c09005810b015142b03000844000140580c40780d54201025182a02c60224a41801c026800705140030202400902500e10319020905c1e40040107145188a88030920b0030001903540d10008020030b40f0781a03400054245000d018413105020702003d60042d0309100409140050101d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 548647401 1250 548646151 548646167
    0xd050a050d0908040509091507020a0203190503070c080303220210030c0905120102090f0406210218130c060206190b030705090103030f02070816030212150c040303110d 74
    0x50580944030031402e010070801e6401d84028000c002c010080d64030300300d50029038584692461082d403007020800324021500100310401c115400ce8080c1c03401d02401044403000e11403000c401c4a41d03200c100050070100707545071001c40c054000900034650b04d041480c1c2e0701d901e1901e1202040e4081c038410074103500603510315128104a98440c00c003c100f21707400c0842903921010385c0e4045a042099079101d41c488950650003131100708022106a481c100d04101400110b5000d40114400716020740d03007108a01042070001011030340300070415a042000c817021a000303003000b9140c50350b104200f44015001c002485040a0152400e84010400c5203020340405c0d0751980401252185541d81d0008441d65880c1803024401a0401a0040d206541d49140041040c3c801030390400060042c10404915210003007496180703c4c0310440c1070200700742550204070b03562240f60381800303a9128400d0b8180305040c90882141c0708002d4000055100c41c40d609014100c1c007060744170015541c20400240103003680003511 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 548648651 1250 548647401 548647417
    0xa1b0f0303120617070806010f050a050909030d0204060804020f0108090606060c241b07050703110d051203061302040503030301140105041802090f0d02222301080d050a05 75
    0x482210801c42102c08002048581c00c100f009407884079208041060020b00c445c00c0b540384208851705aaa54000d0601c02041c900626030f00c500d811008204504c0e005681c03039004103400007038174a040405202e0108a0788151300c100007203040802000150701e07001448400c0d0b0303c3c0030f003006141e5250440340d29440c0d580080c001803150b50f010038140b200708010000c510b22003005080d07810380420124040442c2d6070086980175199420b2800f012a48458042500c40305940304004000003402d6503500020443c221505036003106141c2031101c0401d400304000d40850004000c019030b282010f50500a030b1b5482c00038500100c4d8010003040256480000480341103512000c02d03001091542c00c0102c1d0140304560181840c407540d0000302d034586a06a0003400c203094126443c62100e410942440b1000701e40200195001300480d81015414a628815901a42103e50002000f4021881d540244010344d919103c2a60362103005001c1c03a08100004602800e5a0500f01d013410b154450041140c42084a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 548649901 1250 548648651 548648657
    0x5100810090c0e0901170606030f10091104050703090512280302071b0807050a0312030f0209030f060f1b04090c020309041d0c0a0b09090c0f0c0a1b0f0303 68
    0x2d55907a20500c0303000e842e4000c031001003032101c06580d548401d08030106007000100b06c0e405036001196040c500004e1240008140201600c405002421054014888404243d80304c10b0410f0340e003051683d0345d1050b50f1040130240c800080f48441818054949030008680702e00d0680c00f0032654400d8005500000300c850400610844980c4e01441c08030064050f0b0b140040c1002c490440401c4071b140c00036507440c1514042d90444130b03540c1d650001c00c1100e1a05201c083c0c020892500040c05042c030a4005000f003e80501c0050b1130200110046031a021480c01c0c961314a81211081c4412111503595541d084114441034007000c0e200c280050113648a14891a4001940ea0110b0044540240140d80440800034000c0000b94200b0300180040b040301c2c40382441170b00485c0807031502440c104541c04191041d180c01682002020403c0c0040c500018043e5146035609100c89644851140d00800c840441400500f128a02c0c0303240c50003403002c0c296080c2c400140c00f0b0400340042202800c040040769010f103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 548651151 1250 548649901 548649911
    0x6180709153209041a0d050a0b0901020f030c0901020c03060a0b010305010e04020a120302073c06050a0c05011e0204082404060b0d020d03020106141219051203010f0510081009 77
    0x700b0145031a03c0c81130175a5400c4a06c0e03ea030001800804240056014001e440010b42682c0c0c0d400814201e201d030f41d044002000c0144089014041e856000c1c150004040c01100c021209100009191100c112504805a80c5940d010031555078140216401000c12a44001c50340c101580007580d245028000d8449254406070208245842041013070300402141171003404c400590848119801c0c201c218410413a0300e0907030015294003011220404880c11603a03410309143c881401215042c2246006540780d41d05c64111501031000e0780264064156210401665603151031f21203402c0c0001c00000a03a650829410350300d85440d901007065019910000000702ca0b03d915001a1a01c0f000e58400b0f500f0240c81c01d0340303d04241d01580b1010980396000c7c55140c501180e83c08208194002c80c2500d82d0f160002078960710440e81d0822039007102c910031000c3d5283d00d011a6180745240d04240e11905000d01d032210104140e09290400041c605003600c1c1001d5030346041c04141c00305041500c1034400c00b943ea2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 548652401 1250 548651151 548651171
    0x71b0f020d08040b040e011a0915030901331d060108041406040b0a150303020717030c03030403090f0e0121020307091d070e0618070915320904 63
    0x107401c030b0f0040e150105106440d1526445107030307224542400340e144580c100c80844442c200394201078445591005059001c2c190301c05606041c59000500390840540d200c0480c0039401040c40042c3c42c281c40d4081c2030045142007803544120030b4103240c0c040304550b5482c1145511800d035100300d00e03a01c02001c0c20941003944541ca40001c03031101009030300351680249c60a0000700510100243e01480f61400240b05c600d60046103403607403614902c0000c001d070380980f408000040440034030143c1407016605503410003110059990440c1e004481c110000f40b02c8070814402c0c003200503a90790152095411a20071581440710f2600e0104030f07904100c40701000d45081000f15034040144d50060f1441010510800c03000304010229440000b20b044040c0c02900360101d03900c0785011400744141300003130503800320310880c415107003010314003a1074602004840c41001c948400d20281100100b440c03170782c42018160f50280c005c04240e4604480c03141c60540c0708001c01b5400201019901605822a0006400192 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 548653651 1250 548652401 548652413
    0x5190b0d1a07080a02160f081306080103050105091606030b04060f17060906130312090215040e1003170c010207060e0f0d050a17062106071b0f020d 65
    0x440540280301a00d06840400304910a000032406107100b5240e2410310780300d680000f0241d0040003d0f0b40c00a10f0071b0030b20fa04c081148034811a1505000700d510501c1c18901100d000302c481c2c16500410003052403d40104100310003407141a07440882540580011003107507400907101e580600c01c040c00c044d00c5410028503950345500a0f0b00500e10305001d02d04240d501c03245411102c608000c2c0d152240501d10028814450209240b071003414a40c00c951300742003d82c0e9081c0c409540302810108400d40d14420080144c907100c980c10390300c4985106064556103000000c9140c164001e00c10790000260a07000c00c0007403c18010002004c90b8041020346400b44446410300900800102070481070800b401d01c4142c6101288404256407032001340ca48008000b0400e841e2481000c600000107206024103100706080c0454071a080700008007260300409190041200d0110700700000444c41d0490420301080719001140d448903100003641c3c442010801d41c54840d01e1024020b40617000c0c40c880d41c00902000b0f5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 548654901 1250 548653651 548653669
    0xf070e1518090d0905010503010b03061215070c11010c05060a0203090c040f06050405100308031501030207060c03050a0614011713080705010204060801060302250201021609091505190b 81
    0x111030910411600c0c1c4034804550f41c2c2d090706440004200c10603400320302e5502c250f088a041e18403101c000303491911fa00c0309001e0948002c101220341409402c28521031026010071444c0111104da81302c8600500d1420584c1d03040e4480c0d01240d041c03101c07944c0041d0000d600412010b60080100d02c0040e1a1b65030030001c03a00b03090111085590141c645040703020740018030740c4000d05494054604001540e0340d0310300d8402c0c0500a0001a08a000c10320000e12134002c0d02c40c003c000c00382c1c18500075040c542c41c0e030385146c1034441140d41c0e000807985039420426001801d1140320700070100d041643c0c034a208604000b820004000d01c00c62034008030100040c01c0c20542000141d10568011046541c409003410818000d400602815000904000002600700e11a000351414034100380906d8501c0740c84a035500102107a0b40104905600588500119590300d007140b180080c031210710301003104051490300c40c071f0148071072100068440c42c4c5011300500c1020b164194602c50b0b028500001c44030b42c07040001d44809 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 548656151 1250 548654901 548654929
    0x1409131407091103160203090d080708070b070309110f010f050310081603030905150a0f030f150e060402030403020a2006030a0b01020f0f120a230304050f070e15 71
    0x25050010190600c001000250305c40caa0800c10b11a16001444080b6180c0c455601d10716030103007200041d240407505c00740041084511072000580386c81d01a9a400070500c0c03049400c58023080d91038040c1c9043c071030351090900c002803007103d040c5101c04244c000a4840400f00c0c0720b1008000c00072000842910100503a0707009010f080c0c0841e641013988a19004004040313004c11030015034914030008641c00c140b03d05440c50074100502d0b60411207030701d204a8480e019040f1610400d500c420092800041601c00d41e0012100111390704120350400c44001a1072602921907801103204008102c00300342e02041c810445a84202003003196468484c01610801c8001c0003541d000c20000240300a01903254803031a6258400e03003c1c0c800c1144108402a210801d031480b03152582c0000740c0d4200302c3d0140e00000c04401c2c2c00b604151828050f0f52241c1d112205a800e0102e01010b8004244400d00c1420050300344004030010090003418107002283c41c1c41180034219a03038090301202e1082490352801c114000807 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 548657401 1250 548656151 548656169
    0x606050904050c030d0905010504090c02031b0d0f0c08030103060504050f1c09060f0c080903070801020d020406031118060a0311070b010321080609040303060803040f1409131407 78
    0x9041c02d050980e03c88032121440d5200e48210040784244030702074a0010100c40d01612a60309051610749120080c01c4e9040b1030303a0171400304000100345894440845c540c10320b041c1000f08652407248c1000707010b115040c00c0d08800c0c42481c1074170038001110641200d040d60750100c2d01082d0394660b464417500d08029034604507041d016801ca01601c44087e9400a15a11610390710320342400ea80710800d40f41459a0f1508134001012034200f0000310f6526001008098030190071034203556500c0c1107090881e00100b5031643c0e0316400280400003079915000750481c0c04105400e8500d17051032170074090348600e00d0030030040c0104008120681e00600035031001034564211f60b4607131342d607030900d1625540c41d0209000403039078481030038010b40030442c0c0c814911411701c80c02d48501c1d0aa4440031304000510340000c004400305522400e012480d0700d414800750005080c02e40c0b041c04410b040014505400c40140291401081030700c0c100907108050708440460f1075001500c11100c0c11680710282e0074031555400c98400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 548658651 1250 548657401 548657419
    0x2009120601060e15030c090409020a08160314070609061101090f051606050309030d090c0b0f030a0609020906030c09040609050c04210f0308131505180a0c12060605 72
    0x207140d030000740060b00890300b12101d10484100e45014682c0c5e0100381e81c5421150300a208001c40c030f0030544c1c400894503000403c141760302035440226516000070043c0168400603e001c0410801081d2601844110000b03406401241d00f003420040c503855840c469601081600c5914100c020000e612030741c029904240c803501d0070102070405a95030003601c240680d82c1c54131110300060051140060f03d0003083c60102461038203608081060103056280410784110002c10000940c12440c4070043c001c022030940312139101e290064011040790825407021407414010080c3c0c044580c0c585040b290b0207091111155160f44603400071034001d1080360401c00c402850102070142d21011000a04102c0b0640b481c881c0f52000d91129031710032003000020007003030921000303402d10000e40241c2d0700d9903220354020a152043c144070303207622041040d994540300405540300c00b803125103200120403c038684110f5004146420495450441e4010307544980c007066444015044101b02e000d4104c60b008050040c20600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 548659901 1250 548658651 548658659
    0x115080c0a120c030614010c0803010b130905070201090b0c04050a17011e06150e0307060503071101060f0512011a0105090604050603040813050a0f14040b04141602012009120601 78
    0x13005141602503800741c0709040d1400301c125880350f803100701ca00f43d1203e4541d04592904000070826000f003040c4800041d02401c0104251680c3d100d040e22800300d075800440d44450604141a0f80b8030f01800404079460100f0040c81a925856800c00071a51510b01d44010031148554050040808224031341014449814003002840e00c0c2c2c0004042d15174924030249061280e48041d1444150826520740541040204200a50040c800340d903011500782868000200c0300c104e01821140c070358201c00c0160810403030600c400d0034640300740301a0141a0001b0045403914070302c00c001c07000015450303d040260008044105850f001d040e02c0c01003801501c0640c0384d040920303041d885508603034110040c2c0098418001174900c1e102c00e010003180d4001c070003681c406080410b1650408007080115810035185c40c000c04194845200309446600604202c500d64240b07505840d035981d034072034501d00c03c680c1049070a10850f000c070405030822001c0e4921140ea20b88004001c1040d4941d82a0307840719034000e40700005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 548661151 1250 548659901 548659907
    0x50c0a030e0d080307031d0c0d0b31030806100203070f051e1c0201140406020d09020904080a030b040b030c061b0d0503040c06050414060304050c03030f120115080c0a120c 75
    0x89040c070101814034108402e1440b10348c1d82c0c0c12851855071005010f008a4041000c3c00000e9401461040e13101d00a44010403e00c4000c0c1c480090309041c4084442c40d51f010301d83c0c0000003582082080b1601102c490b00550000d51301e00a49901800101022a12004020081000d00790354181580c160420070a000141e9480f841061035590390701807950111042548188140150060156591103442d1245d4803408002d4100c0040d6244080d0740d40b603c1405a074070903222a100304c1c820648180e88410070f400040a44586180d8240503d051015150707440d80d01054030200700368145c64407030700e800003415000c11480a4480e03040c1c0b00c0c003c141d2040c2040d0b900400461066015044100703560f6620031003224a0b201c2c0d840707465001c081c52102c094451410718019a003190144007201c541d5800c580011f415035201130490030182d000050209540c01000741c515004223101001da45a401d0864400781410500501e00e4032124400900c0c540d900307000b0100c2155803103905104004c05520f0500c0a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 548662401 1250 548661151 548661161
    0xa0e09070914040b012306041203170c3103030e180411010807030b0a151101061202010f180b030402040501092d0e030d02030a0507050c0a030e0d08030703 68
    0x1840030608000d44204034080b03260842d8083c1313911011040c1c4580c40c00030f60076480c0810040740101405120351240b000da45407000303840a0141004201c6c0f01100c1464060040a410a442d61600817203604001c0c13084070300c600750750280d000114103210381020070151994004071000701303040a401744ca0000c0189170340440c20a1441030195084003013079a01d4840709040740c0d412a00202001d5548600c80269440b0314a1f07583c1282c3d03542008030b00c0da045900000c440f0007030760f0080a02c0030800d00040d01d06580c00041100c4041c103100c000c0107102d0410018800000300e061010b410301407120f0100800303c0c07050042d41c83c200410040c021503513480d08085501940180c600764492420032001040d002d03050710901060285140540e0031010071200210001c5240c1001c6400c12943c0d03c8800d44661803d10013090110010640103a4a19103100604216280075012008001c41802452041c0710001244180550141440f8003c1c4038010001124000300c04401000b41c40007109001e070780c503019000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 548663651 1250 548662401 548662409
    0xc0102010b0319020f060c1e0c060f0414060c060108030a020d050a1d190f0807060f21091211060601020c0a05090915040503120f0714090a0e0907 64
    0x78440c11403041d00300b543d20051540c058640290540c5580010300d0003600c1000d81250240645003818601c5055504102180c0114640300c08a8660480c0c51601031140c68105a8100d808500b403074000c0c0360b40d60140c09540244c180c4540032000c12401c40d036445064901c200c0c58403040b100c0070340e164500f1680702d400c2524554003621550024002d803a000c0c0d015140c0401c0c256461000202102c02d80074040c003490382d87c0c160881000c0c03015283c04c08618007003001500c10840800c591a2800d41e0b41ea00d0034105500c8501007021401400480660103400d02c09070620701c1d80e400d5a01c0102c144018001d00074544000e06401189201c1500c06402c07191400c07242101d4003d032900e5036603407001a40c070b071400e00400aa210001e00d805000350310703000c84020b810510090840d12400b110701140004581c0980301036449600c003043c02c020903d4101c1c00168058540c4628441c24204420f000d480c43c04154160300350082c021032524669140c01500300001c0c480424074003111b045c0750014075114429402 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 548664901 1250 548663651 548663653
    0x90806150603150d02040507030902011101021243030b0909190609052e021305040c0c0c0f0f051f0f180b03010e07080601020a03030c17090c0102 64
    0x6282030403101a200c2140c0c80142040c0c1c5555110000b007148910540c0000f58030500c8100602c02580799403241600c03903085910001154034440c000540400d00790742c018011b45c0c0c010400301069402c8000d02c980c0040c55107210341c4000308500c00124086140080243c0500b298002c0e0050030405260303144d112941c10348040118400000c180009100100d440000300d030b0005400760407441c0444482c1208600810740011018801e83c2c82504008411034911090803903101c2d05650304038491070390132006083c5503085141500003c1e06c1c44001e5818403c15100300e6448030001411400350000a80302d543c0007141e803900503218040300381d10400038064048a5a200103000c03c880c2070200b4110240c05010300e10000e0140440800c56028140229035030401840c140c0c2025407403416050040980780f48000191650b04280c5160a05c0ca0000c0c08102044414024031006903000308455641d1901841e011803031450603901500c2a01c035004003d85100b40c42020017054000200d070201540710268 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 548666151 1250 548664901 548664913
    0x405040f1a0f0c1e03070c050a15050c121914090a030306080706020a15021309090201020c0a0b090d06020c0f0f0c040902011e020c060d09030806010203030c0d0e0a080a0908 76
    0xa0f10311018015601d9070140044a12a03803024890000c0107984d01c030165182c11071048003c0e5072a14200142c0c690304803031200175001180301b4150301d0300440354060105c206060034247c0307010350690700a4002d00100a0b038141c40c140d4041c82d80e000d030002d904031301e807945110100e4242500031503900c81c001c6409400013454103101040341c100102d19141205c84550040c0340d4104c43c1c4d10b4054001001c01c1d003141030350798200114040c8034030360000745008200c8000f001601499a000282c20420341c007106174810401c4031024460010b00106039040d500d401ea829180300400ea03d0110000c1c400c103807100c41c45100d04d826040c0c0e07000300013920724003449000d0103841c405400a000d1005860407064000c1c08600001220884802800b1014840c04000e104441004401038042003403644022031210513651140c1c0d60b201170603003003540160000d4081c80110b140d450040032104203409010680d500345615150b0210311000200071048031103404c200c09075034a0001d0040640f0982c100d00c59803174280580 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 548667401 1250 548666151 548666161
    0xf030b12150c1e0f160302031e0406080109020c0f011e0f1116050a0c1202270a1a060c030406080a0209060405040b1c060209120111090405040f1a0f 65
    0x32100741d441d83c00e18008070390f0740c0c56441e14407225150490011040010801e010100703401800310b00e04040300380a80c019641c0c0d040c10860056401000940d5080340d850304200401c0340316800900d090455188203401038a82041800c2a401e00e0317522401e031170f403540c01c0c618441058504480410048800c2440403c03a01d05002c40550a13101941841c4550010a00a80070350804103e00304220f54856400e4030101c500554608540d94903d8000000005140c444030b01141080000c000304801c01c40c0407034007108c585205640580100600306003010384c960a4103107401040b80d1044050340700061200341c072520b841174419500d0b08103101d0071000a010b0070100b0b205942a1003144c403a503402800c1685018240010700000d0101c80781c0361500907080115062445040e0002c6c410310910500300582c2d200d040d2000c0000a1408889208042c0d00d8060420f4000b0750440c1211a010030076600442c445d550350801d00f1240b01064006000c131400700000228003042044020b1041c40d12141c5114691170f0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 548668651 1250 548667401 548667421
    0x9083001050d1515090606180501030e121206010f26070e0301021809150d1101170406050a060b03070518121005270307030f030b1215 59
    0x144480280040280100520007402c0c4080b554004500a405024606000c4449082164103a82c00c03800c00285800062102c003240d030107800e0040c40d2500d4400040c1018985101010f55284101418140e0f100b420074201e03102481001c90078801a0b0740030307884ac00740d1403200c0761541b41158490b0000300c0403001c403c542070055003124079918100b0300810a0550120404495100180c107003018403520f240380c21a165024001840003d10711010b0706840181c0c3c805000009902900d18003d078a40040300c1c80154542c50110080c0703d41154441c051070f01c110340141c0740018102088082000203800b0001446103c1e000240a048001c804004642e51215151490301095441d4000a081040350b24000c404d40c0d00440358000f001000490600240d071841d03858038200d520221075032500c640c1004030f00b895481045807441d0307050450b080303112952030070151079100d00360004080c4100401502d454911980c4a00740c0864013410740c00110441d040d9140c0d50703114040708004881c0e02000051b2101134 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 548669901 1250 548668651 548668717
    0x22d1c090b072a12030c0807060518060a0606020c010e0f2707030501060806060307020c060301120b01120c05130f02030f01090c0e0102030901030e0307060903110706020c030a060504150908 83
    0x8903140f8050b0030703049255400c5800e005041b0060fa0003240c00d06c1030b5800b10320903100d418062109400c0150b032088469041505140d0000c250010b920300c3d0400802400350040340b0007400401c24603040b102c506400c800a040103402041c01900b00c1800b00d00c103603804155009000c3c103c00c405981c844141c1c2c9525040302070302c07000d00500000881400200d41503050590155401440b5401690b40740a9510003140c00c2d50404d81c08100c40c2501100d4000a02070845140760141240c00707034134941c02c4201e48400b0300001203407051600902102070742060300c103d41e600811904000c60030940d500d0500100d4a01945000e00642600078501068500d080740600310b0305240b020180c0195040c141480c0054009003180b0003803c0d03c900041150f01c00107001c0d40319045610b403003522414030020070000d06600c0d01400e40c101c1810f5600c200a288100c0e58001703040c000c0541e201a0104140d9900d203401c4010724402503401303044074240302e20002007040c010007614800d001c0300c00126488140c0ca03e0703480d1082d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 548671151 1250 548669901 548669909
    0x4020a090204140402070515043215071e020c040509030a0c140304050d051c021f1515020703030e150304060b03011407022d1c090b072a 60
    0x2443c03030244020241800d80242111030f0044c0e0075100c40c820384400a000c0074000b203404440c0c004031008401240c04085100c070600343d25211078400188003044c80707555980900d8070b070040384003803100005854600c0384c07450843d004206400c00b5996280d41001a50f2003040b0707090b8038803c9081900250540c43c000007a07518a8006540d0b240d80d030042521400c180c0000c94598000c540820000410151a80b4104030304c3c02e44100001c0c0846ca040c100103d40d4595054580c40c01c6421200c540b803218540a0030074514021203960026103129150b4020702c0313448960703110707007c04412104801d0405802241c0803048901a0700c44105081138441000000903c4044a02081c5000d001003804a01d40d03a100e40170010024000207a040e51130505031907650f000322140c1c0016484483c0c1100108104940300240c030226841e00701c9800f5049564540f070f851528008801102107007d9105800d118100328001042e01e001245da850030f090410302c0079600034180c81c41515100c0040ca6035602c1c0c03080004c00846e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 548672401 1250 548671151 548671169
    0x90907030906021e030f0105010201050712150302180f0903040f12050709240605030f0103060b01090504020d020405030c0a0f12240603030e0405220204021306050304020a090204 78
    0x1695500005800a2030a840300395502c0c0d07400e0100403a01403042403c070090404440c0031301e480345080110701c000c40c40142c1006045904050501120702d80001c43c0b10700040d1041400f20300140c598251442c40e00382c80d400a540212802c2d140c00c218030294043c81e0055a82441210059449854490307032441103108103028081024003c0054440101001010301d124600342d034903196581042c4c170309640900404000c078044034910b4507502843c0007080002015a403d2043c15840c3c9411442c00b800014800508000d841e0303c0c62218607803060b081d8002502d8020400c5440d818450280700003034025001d80c5000c0e20444c141c0d08102c1c50448003100884100050781003140c0d060103070705001070400b0744084880303503411208803410b03100e02c00340c00d020030001340000a103607407842c140180070200d202030300c50103985040b0611800404501820702807600d0119014900e4000703101290081c416040c0c6062000c001c1440440d0207603000c1c000714010b0780201c80f900341c1c00c5c0e264000383c400c81c0b00321301c030320198 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 548673651 1250 548672401 548672419
    0x303080a0c0302040e01030c060224181e03090a0509040c03030f05040f03111507050a08031504050108010c0905091e13020d03020d20060a09260903060c09 68
    0xc8812950825030040500c0d01e005402c059998481c4a4144420380044540c0c81c0000310a012130341e4104113100124420b05038a69503025500148a80d4241c00b034840d41c00181d9615400809510070407004900b0819078203604010007903043d0054403500710341480d52003100c3c00a000a014035081040d240941c0e08010320701c4419185984c03d95001603688100f006001080c08009140d5108903941d400440c094080c442421072460b080188410191a20003110b20040c00001e02040d070024151400c1a40000d04c140c1c1c1e510340c2c9840f0180010b41200443d17000d418440042680c50064010341d003a040c070342e291109071544680403c142040e040b621000448107041100311503500300d00c03c05030002c2011000030101070440e00402c41c911000791701070b0003581c841410718440f9548864251446a44154003202141c0d13440c8c1c0b4103480c1c1c58041c05c0c51405a071150145414029541401c0d42012098003180d5840d0314600304030482d40d006501d06074484e005800000c0d224244c15412564410002048001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 548674901 1250 548673651 548673661
    0x70e01021c0c02030604060504030201140421030b040906270b0a1a090702160b1903090204020c030a1d011d01050304140714030c0a050f01120b090c0901020610030308 73
    0x140c0750110300348410004001451000740e00c0610000c3e02490003187c0110305450300c1d05005c3c1c25206100b040030240041c1400300000b00b00c001c1c052a018210b0342d20000c44d0950f041d14214040e104103601d081d07109140c2160882007020640c80050844141603201d01ea8449032020300d035180e0300c24800170b4407407000f55000071480c031070b203510840082c1e401d680002003e00364040440c500400c101e6100015910a20707070310001c0c105400c1c00d5401401c15207030151804898950038030480310101c0854080c551149500011580c50350103a03070752604200100c03a1a070b042e920008045810310003846186803503052110460303500c102601c4500039524041486070030541c070011100c42d40001c2003074440910502c0c40807055202880302030011300e917101d5103402c1607007190200b43c28901840c02c0984500f00403034040150382c540e10541411345409003004840d6480110000c006058206d001d0799000e1074030b20030030011607505401f07041039000a03400c039506582c3d810b04031001003e850001402140c04a40050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 548676151 1250 548674901 548674933
    0x3140703080118060902070b010509090703170a090305120901120e07031106070203060f15090103120c030203160b04060e0102070506010b030c090306090a1b0e04060902010c08070b010905070e0102 86
    0x18050030b480741800504d56984041401c1242c000120440321200e031800100f01d40e2078520281a04031030000b0140181c1d074030799918180d0035140501e100e15928008a402804140100d11100c01182c01005492910442030f45201030342d4000700090380440c2e11102c111070304507224030070840340d107032070304010310001e810341d11400f05036202035140070350087d002c00c603541c0103840520245005103540c09121086062180000c2c00f1060001c02e018060711110b801000440c445920001803c80c6504010303504043c58203040f406c40c400c060343d2072200c100c0910701004201071004840d1065024480c100091140912810700380e00c20341401030910751155005106040340301c0c00554100999034445890140c144021908100c0b08582c0100b00e900400218020300200281103584240c440d0b03400e03070f102030410034982e5540001074030240840c2d550300d15950459000d0707404600c405800c0742000783c0f00d078003a00d1b10b074102010900550000b41e00300808202c1c1c0c02e0103240c0104440710141c0142032200e251014213 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 548677401 1250 548676151 548676179
    0x301091d0c1e0d0f023f0313080f0606010c0210120b0307030807060c0f020d0c170d05070f11070611070504090305031e0709050d14010c02030403031407030801 70
    0x10705802c0014900c0050260381c3c00120000701c510418035002020100d00420036092401042a52030300903808261210103206074084c1c80401ca142e40403442d000000b01c2c924a07501503400e1000d8104090503003c901c02c100000c11010171800d0000703e48543d503e001c01101c18849110b4000c0d007011026601d015004e00a10b9801045100d8a00008a5130100d00000e890402c640c0c0c4141c40a200c0040c000e81405610301aa8a00c41500d00b0203071340801034054000e660325100d99a900c00c10842d501d103c410030840c1e1204040c0720070703490003071500c0ea800c00078000003c22040d83c413403020515015100c61307038900030005e480900c0a10f002a04038546801c0050b103409000c40e0b00c51000e0f014000021800765198803d0b1103601d400384c0d6880d601da152245016480c0c010100e10801d02e21400780030070040c41d510148001c107458058a00c0c2486a54900c0c03e0030740c0312340038400c5c910b45500f032811100c3d4582e800009041228000e0352401d443d184011035141c098803a0741000b60008040d5001031066103828881 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 548678651 1250 548677401 548677429
    0x6051b0f090f03030a0c0308010914010308030c131502060a050103030f0c02030f03030403030b0a0b090f12031e0a030f0b090c30040210030507020a110a05150301091d0c 74
    0xb00c0e403501a05400203402c5601010b400d00c0812441c286d58030506521404540c0035001c0004104425490303409145400c0405110043ca0f900c400000654541c5624040d6100d4500d442e2080600640792422003070105522480080184a041d00080a40a060103914100e0b905030300c5049040010b4070040342c101e0541142640c09d4071664041110007802040107500c80d900995000920200e080100020b40d60725034000781344081c0a0042d00002d80d038450f0400d40c3c0600480b8084904a030902d0268114010844551100c010600102d01e20081c2c070b1009091b01d494070b6a080200b10b194500d0401190071291105802001d2180040c1d40c15400710010800c0100c404130700c3d50450303243e41c0c007202602c000e10344194000c85410180030441c20043c0709141040150308060049281000c4000d664009040003d0021044803910f42a80d40f40c2e131804a0292101034800208250880001041c6034000c1c462407031040c0c80c11034080c1450400352002d4044a01c50720240c81041c9038034082040442c14000c2d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 548679901 1250 548678651 548678659
    0x1031a0d2d0c05010e271b07030e04050a0c02060606070212100207030e01051206010c15022110050604030b0405030405042c1609230403020a06051b0f09 67
    0xc00c821102181100ca04441da100328048040e540c2840001007600c0c849003483c9001e805c541461000740e00c00c59603c10000d0007141803041141d80c1d440c146103a486604880c0005401d00000e4240500d54824401598110192424031294444503540c070200c81c01600714600680010b80070820a281100042c50841d000500d4655000781c84821642024001203030fa4013103641c00a845030405401c180030918001c0b00342082e60500b80c070070400b40d060800013440c81c3d04000341c0420781000c110010601015940c1d28100864503201c0c1141c80c1711942045a6003044070100e0031000510000501d2180000d0355005486103040030b156503124000414003400071a0240028003000c10746881d9440340401000d80d00d80307600c084034a006001c001860010782c803c402504084502d10a0304c00c2041e00b00e0481c0c0903910000340d030300484603404e070301182d4159031010121008000e0105059000521250860044104101e107403aa010400f446034455420114101418040b00e5441d6034440080d00b03500c0e5020b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 548681151 1250 548679901 548679953
    0x2505060f0d0c09060f02060c030c07210f080105030a1a0705040905151003060e0c0d060b16230a02040207050a0b0702030c01061202030c12240601031a0d 67
    0x106408240c2e99400355102c00540c200300c0030841c0710390040920701540c12900141c031a5043c49400e034801880000e100310117080001070750f0010425100321140d84207503100c1038034900c0803000c3c3d00101204412880030700010301601c0007044603c1c000c201c80818541c0003842c0b81c1000c005015103228404000c01c1401480790a110020340e2082d5400391500c40d100e00b0201045055840c01009032491500805504241c40c00381c2c1840400e10480003c3e4020f2030000d042da40b60f003510404040070345481e0b04082100207012401e086080e00108032100118898902d01c50740000610560640e110110000d4800d0390244840201604040e4010660070340200103450601d4140d850320094044143d9541c0700590000030702d0308100c03c0a00c2000050880ca00c0c3d8045040219000603030390340004080184600411120b040d54030000700640c41401404803c1100c1046000884601d103000031119107012900741741e11102641940541c039040a04020114012900300c0c3d294141c2026203842d000070880303501 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 548682401 1250 548681151 548681167
    0x10e04092f1c1b0b1b030306030604032708010507090509040f0b0a11070f02030c010306081005180d05070c0e041a190f050406060b0301033f030b032505060f 69
    0x4910f412001c0c0c07400303d40c3c842d0b6a8180c01d24051003e80d07040707200c000581040c400d01884c4e5038045145600700d074040c6000000851071710700c0403100407603000c440382d940b4620b19000900c446064005510074545521404251552041800800031040714014003172a4002c92322030000b50314241941d008400e500d00020b4140c00e02d21035452980c02104180e0740100ca210954045245c2040100712400d42072a06010441c5000c1101e40e40e8604980c43c0d10825440f030300020703115103000d010b00381310581100031125045110003016100d50711190050303482002a480100741802c14501c1c7d03500a580c86000086490600041e2059504d0043c04030520b5502c12600002621040e0044541010790741100145904280c40c10104903400c03540b00c031601134801e00040000c5614501c0800d0500306509020300b085450150b0000c00120115500d8421984450a6000543d055000341801c81c011344c200c0d01510f64511801c3c00d0103000e03d60340e03a0640340400040c000345c10a10003400701e48801d89025410541c1d4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 548683651 1250 548682401 548682443
    0x90c040321120504030203090f03070602030403231f1406011416081b010608060c1204050106050a0b0340020f0a0e250801050f010e04092f1c 62
    0x4203139400d03030069202003255450791030000c0c501c0101001c124000c01200c1d24000c1c0194580c0101c1c0303c0a4241204841840080c4414000c1004901000360a6136540c040490f00c09a451500c001030000c030500d04844600301c0d4060001187c05410305860f5161842040c2401d9503c1360700c40b5603030446e0404a01002000a8150000303080203001c1b00c0d020505401c0040c98007400c507a42c41d80080a07a034000028800601054422aa0710001240d45107000e50b54a0030032301d015000d1944510f41201a5650014036001450080d602441d65442440704940c8042c004882c45410f0f02c90b0700d520401e42442206c001d203030704103111810318400313040340140f61101030000f040204280d10080c081c0505008005254048032480f0765103600e10360031a14400d10b81d01000308903020502465004044400007120940c1c01603e0500e24440020003c0c005803405240051030440458032100501454403010714000340516024130160001030f02000305800c40303140c403043c840b2700c030481a01c0200150901c0081c07461 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 548684901 1250 548683651 548683661
    0x90a050f010f11120705030c0c1b01321309020c0c0306070f120506010c050307140d14030f0c0c4206090c0d1406090c04032112 56
    0x25010000155045441580c4020380f007030500c80700454481004508940b10307071503400300c0c0c2180c000e2420301d40f81e0f42c8500c0240034034490f88540091358450348401150084d0701c100000d40e191401ea960405415210340001c03c101121408541e104c80814030529103889290083c0001490b07244600300d00340d42e102d02c410308990289000440c2c0d508400340d040e103582400c01c0301580001840c41c10030b50320303c040503004104040c0080510302c0c2c1c60320303034010075404d0b84220701a134a00c07a000000d0702d65411942c43c080d4030300d44a01c000c040f01c0d4004c00096109450154100d1a8000c0c40350003010b26643d5802560016954018054241c05809110400076400c0420001c03100c1c0d102400707408210344a440c40701d200103e004c2824404240d03949203031504800c0b0000302d1a0402000e6824602c16100c2c0441082c42d80140ca034000d00203854207425082587c581c1c05254080c100c241e507402003c0d16416042c8100d8031075804090001116080c80c01040008001161500d501c1072074a2800105410040d006441c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 548686151 1250 548684901 548684923
    0x2112021c0c2003030604060b04290708031e0a06081203040f0803070807090801110906030a0603060527030c0a0f0804050405071205100321030b0907030c080c090a0e090a05 75
    0xf501c00300070060982054400c0300003134064007138101e0629180005005000c1c4403460b403181050380030100000030304e9500702910300155218510740d8892800141c4501010b2841e000b01109201c0c2c840482c180141c984507000c19994904090020100c01d2403e42d000c60303101402c11600c1c64070900b100e402013a0288051806078070540c3d101c141c0d44c101810014806800790b00300b86000d03450854101403030003440c8112410f0300000c0d00d01c5034403542c50340d002c18014291540068921428401080b001030105800405415050a49247c42129040c0310341d6503802035844401d01c1c2c0e40300b002001c000c5011700c0c2240b00075520801251b0318080e240d03004034064070001c2c1c907800040303481540310162461240c01a560b1044188404403500c92841d215201180103032400000c20400e50800000d9031031080c1c100c906841c07005805c1d01140e0920150041c010505500a24000740b5014049062060b922040340c03a0100001d00703144601c1e080040c0c031442c8060140241c00c0c20700c64009030740c00240c41401a130040c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 548687401 1250 548686151 548686153
    0x801020d0228050909180109050c0a06031118220c0e030a12050a180803090f1c03030c03091401050712060e0a0902030a2112021c0c20 59
    0x7041c118400c08801070152184650782400044071040403507121044d80e0074054100d0703c210390340c0ca80350b59000c01c0144540e5118099400e1521103024041c000034401c1805406507128803403150343da40c04804455542d100004501010800350481d200e4101440c1060380006048904144d00070700168012408012040c1c0044c2e22011402c2100390007100c010f02e02c09040d00a080000007030744c1d030780004445c1480050301307001c1c1c08249510464400e41d4034241d600311a45408440c00d0301c901d002550398102501441c03203181449814042400e140e04207a00c942800800d4500000c03280d50144c01400008410320b04040d940c110480c013040300ca20700800e60182c81000020a8203001c200203040010b132102e402d15050a090f02000f510b0341c0d824503294000d680000008040700a0f02c006800c050b10014050111015407060f0301400b20706990740e03a0124165210407880c140304458180503800f4071092208040d50400780210030201e6a00010f403440e205140888451140d211104500d400c90494050b003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 548688651 1250 548687401 548687407
    0x120c2a06071b050406060e190816080709020c0d0e01051303140d080601050d0e030702100918090f03030f0f0f090209060301091214071709031e03030a090203070801020d02 75
    0x403a07880b0441010140405690501070b0b5424402c02500364020220b00034095901001c040c03907012035000c1403201910400054621104418800c00d00c40501801810181d00078030500156428207403084034900071380c81c1c001d0000e544801c0e00540707858404a00342414010b08000c040c0f0310710601c110307280282d481150302c0c13621100444c101c02c1c50859051604c0044c45108020320002d0307038210b81581c10400d0354402c086001e07601e444c00381d811406041d000a4200c50910341040440750880044000d0340d090641800b10394003010a0207080d14089000900107601e0407051002080c840d401180080c207868001180c406800140202110242d880c881c400da5641d50500046241144109800c104120006e010103030300740e1030310800c001e0000d10910510506244d81144c0c13030892820340381c1c000d07000000f59250381368000c04c111059200128507442405041d0219442c00748072040c000b10361407030000070350550b42d582419000401d1550002e036418881c2400000d04100b090004010b02c80602e0f002680b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 548689901 1250 548688651 548688683
    0x61303110c130207030e0904020604050f010504150e010f08010b0a08060105130b040501030c080f0c0306032521030e01080c0906030a0c030b0319060f1d0708120c2a0607 74
    0x6c03000280c03240c498403d00014080c0405030b650402950296842207666510541d240d90050b07031702c0e100781c6d444a80105201c900b45414990003100141009400783c82e40c204c221402e400445a810090244000480d014044c0480302d500c203104996200006040c290f02d8042d07403802050603110035501401a001c00010b080c8083d51b85401a0200010039050040b024104181c050b0038001c00101203520076a404000140c455404200400c0304c01408441058500340c0d50300000324017003041c0a034428048070100000500d4040c060b20004031500359071100301c0030ad50117004548020026202100a0405010000c1c50380d03102070055010f002d90f000e00040800058a0246c29610141f403624800e03008000c0301300c030442120008451071a40140d0000e01003030500010340081a43c1000c0440500d56003c9450703800c2d50004020003500c0c1074104880b005c1d2504210a1154810786904155907002486d0360402c2d00b86926200341104041e1000717140c00070f0000041041ca802401d0160380d50945803040103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 548691151 1250 548689901 548689907
    0x20103110309100f020414090702070f03080a02011802012c0301060902031602010603080f0715020307080603160617100306020f04031e20130f1409061303110c13020703 74
    0x801d403144c403c2c0941c1018a800c01c00b0181883c034000c0759004101500005500e98030170f10a0b0805000c0710721149008507200d05180610350009522440503628095000800d89802005024000d0b030503900c40d020500084040388800c2e43d00d0100102c45200720419124903079082c0035820117082d4400c8010b80b01d24045507852021810822000250391400ca001c2c4045581c42040343c42d00c14108283c55680c244928092034501040301c1511891480481071203129039001c41c1441c0140000c0341103e0318041c082010500840b040c0c07003100e0100303140351010114460006426640f1a80c0483c00c5010203940b512014160380c400341115400200c00034041c0208005501d60b80300300d40c2c610b004108424503554500b100282c3d105000030b0500d00c00c0b81e10411568030361400c03d401da41c1d40340090145028000640c40031f803007145604440840d0000010340c10301000607805d4414800c00101440840550310300707031072403034140003185428010300c1c001841544410480c20041681c2c0140140d849015003001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 548692401 1250 548691151 548691161
    0xb09070216120507150c050a0c08101413020103090210090609080607080f191514040e120c101802040e030a0801090b0a260f0a03051602010311030910 66
    0x802859821024144081580082c5401c150b502140b02c0e1981d0001170803050314158401a4000c0c100e11071080d48a0412005a07411422658802d0440366004040030459090b80d05004410450b4107510000039817030405041c0501e60940181000180804c46d0f40104086032040c1c502c280128081220802204d036000194400a01840d0041c00c01c5080104005103160409400320110060741c0c004211869841c04080d0811010481c080200c80074000ca6900b5600f49407180302107160010040a150b424140114076210000002a05c1c040d03580c154440303110b81005c5214011032056580c1c0112040c410300c03584a60410680520400d02d400e44104419a5111091100541c000303000007040d1a41010b401d5066079194480802d100303141e1380129802400710b61182e91901d4981c0d02a440804441140000c41c00c58131050b070b59040d200d1312600340d40f000f000320300800041c010420b1607084e00d03043e002184014414507020035074400100161090388c00540d4141c1080e00141e40e80c8040b40c0c40e030720030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 548693651 1250 548692401 548692409
    0x9060f1706150d03090b0d1a0402070305043614070504051809012c15010e0f0606070b01061107080607090302091503011803090f050a0306020d0b09070216 68
    0x91090780b609840d4101050340c4034031500e000312201042a42018001c400104c060b003565a8101d1329802c00d030400c03002900017115807140740e40c0c00700f0515019090500884240381d8060301d4840c60b180c9400103003031340401000a80030307007804101c0131030340981414006c03140c42170700818020994090b1819910140711007c8c08560074000300708810042500c98800601d00590001c2d18140c030ba43d10300c44000c0c05031000d59200b501220404c000c82901c0e0544030b410005884e603003021581e1848000d00103a085140a02a040ea40382c0c1400010b0844a060000d8a41c0802c018002c0e90034445aa503942034503120a0300590042071050701c442140150411100c801008040001c00503410300e01d00107444a00c2c20300005e4052001b250006a0002d800220f03010b00e090003400801500c4403803080d550064550000460000704028000a41400500d00e6076050f40c6000b400b18081c140b45035516030083d448640030105558560700d500c1e889a0b540f1290500c074042035000f40c01840f107400d440510708400750304 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 548694901 1250 548693651 548693653
    0x90705010905090a020918240a030b060d030309051002041d06060f09040b030d0c0510050106080a0f0e010501091509020c030d23070504030308060102011802040b040609060f17 77
    0x54208042da9642d81d401350011800080180e0783c44507080407450700a42d4070340b54a602414501800400300d040024400240c441d00e030000c581411080c10051840b12501c1301178100150741011443c2c501c1c028213406c19542c86814001000421507552900303000d40c4825201c2100d5000c42c00b040f22203002c0e448004c5008c4205040451480d100000030000d004825045900d250086900390b03003070711183d201c400c0c0c004c001403c0f0303010364102441c020680c0c884610100c070903004103080715100700d055019650585500e6129260341d13645110f0400014000911007188142d1100c030040507400081c1f00c0c00740a808104000329041d10300d424a07e045040582c40409860310410660b000504003105985150000c4040450a1401400082c0340c400000400090101014090040c400e0304a00248112482506c0d244000d980c1c003001603081b03500311060036079607428114050006140541c411074162500070400902c00c0d80f15460001204c0d800d4001c1514014400d03002c6c070050205035040c407031a40d0828 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 548696151 1250 548694901 548694917
    0x9310309050907030b0109140a081507140301030f0f020409120801080c0d0807110f03030c160911090d21030207051c090e13020603070e010305011e140409081209070501 74
    0x50700003004141d123071090b0344000c810840600515590207060000504940e0f041340c04554003802000503d007001d6407281c0110b4090200040d100e41d221080e01d0480760000b03444c03403524509440d6405c000140c0b600890b071084c0d50380c0007040000c1c1d40070b100a4046078980c0e6112003560415514a1500750580c1d400c84c41521540c0c0391100280082044401140d4802c0110101c54101c0c0046018240c86485c500d5140c0000302d201903580100140070205602e0800f20082029612039802c01110103012281c00004410032003501e103801c000c00754038113142c81560404480640c01251064071020a000d82000940000b413842c24403030100030140008405020303400d00781c1401c1401406c119028030076107809080c010001880c0d50b10b071643e159405030300502056600e14181790001d180d14004461540402c0c50440040b460040c1c00000c0e00d40c12501210b4180703c0c0b030400a0083c4058816620140d2191b1900034000014144001034100040b5800070f00300582800882c0074101121604014104030107030f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 548697401 1250 548696151 548696171
    0x6060a0e09120c0c0d1511070f2907021f060602190303110a03020304050f07031709042c070e1006080717040b01080c040b0931030905090703 62
    0x70070b000020b0007401103466601c80c4000c00c42c81c10010030030150b5a000140d028000d041c8001c0326aa10081c00c1802e004021240088181d15901d0281240141803854404c4c0d8100c00102c0724900000b00d21960480c016590785e800c2e007000a01030084030010b0040c0c1100381001d0004803900c1071151440103401c801e010481c10050003d59604a4052040044c102020003005150082e40541e1040b1070070009250f8032030b540000500a54400d5400701c45030302c910040080f0020022407a4800d51741e00c1418040710000d4070130482a1600480d5607564402c1e43c402000e8100d0041c80d03140c054104110305050003401041c40041e0a10071140e01020b0901405020000c1904004440005440580c00c115020303440b600d004447d581c4c42c80095006490400c000e001c18450105e000724102c4180703400300c4981c41d900314144419100c080402607000b43d800340104400c2d8a451065010704181106408445054940f0855400c110305400707601085009500b0311090400b105081d61140e00e40c14203002112407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 548698651 1250 548697401 548697403
    0xc4602011d010b1807050705010513020a080c0d0803090f0703060f0b0a1202010309061107030e0405011505040b0c010b060a2601031a0703021b010213092307021603030206060a0e09 79
    0x40842c10131020b108400c005000a4024410f40d0203054001008015504d418850b84225114070340c01603106030821540003d8000e0009851881540c014041c4d000f040c81c01e0780c61511641018241031000d0092424041036401c0400200c0c0085004280110b041c3c1d143c0440902110104c0010390b026a002800a01c07100d10040c030407030706280d42072030700183c0b2820394107081d401807030b0b01004103c04400006140040c1507011450503515602260108080e9036900160a0145025014100400c400388003c204023841c610103404082085000800d101654400203070496010f810644081141940d50710040c62034000d095044442c4404181e01039410350b190b4440c11501c1400040340810f1001c0090070180c4a90150b56081c60310b0f00042e4030043e45601000d0103500440190000034061010003c0c6100da04e0241580d28450002035280c0303a034990704108002c81004201c841507115a18120b0094004003c0301760003140a0f6020f40098148402000003c2c5029802070301b03200420703010f01c644800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 548699901 1250 548698651 548698669
    0x20309065401170f0601021507020d0c0c050301021c0b0306241f05120a0b0109030b040f1709040c0c0803071d04050c0405090c4602011d010b 62
    0x80807108803007100038040101c1d5416060101032040c8040a0184000c07540310009540c0581d07070980a481002004440c0b880c03049208441c04401030b840035800d420710600490000d03062501a151202031141c4030008079003039034410314040c01c00084610750074841e00040e200350b0515100840141403d030070820180726030002a50600c0d9000502c8540340300382d41d550901c4901541c0104280c591400a4080010385550040301e10303019902045000a6944041071040c4864001c0503141c05060341d086480b203048a050003803040b610700740120301c2400460340082d01a03c1c01d841c102c1d42c00c1d9072540e60800340015181500200400d00c0b02c3c4061503000a51018148d03944070180d07182011001c9030a220711085011000c0301c01c1c1c0c00500d4031050080c4c0000c203800410945500b034801691680702c880d48962a4822040c00e00f48244009006c201320055075204d01c0840c1d40340941d41076900301c8803021084421026a00c00740541c2d5141e2114001d102600383c0f194055081e00c0c000c021042e2000b012800d680 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 548701151 1250 548699901 548700037
    0x6011503110d1109040501080f1b030d110f06040c092910050d1b021c020307061d030d0506040609090b0a0c03020f180f04021c05060102030906 63
    0x140d16860301c42c2c480161442502c40c0380384d000307200b0b004ea943d440d0b40300d644844e1a400c25002d64007901804c14201c05140d070a003e14404050001c14041c08a00c000f2034201c0961929007103a40110364100a40c403c0401001d80542d00800a40100c645800c00e204200c81d040307881440c140078004110f0380d000318400e10700b186103801624821151250858200c801340314501005440507d0000210f00c241f103d584507074150801c0303800720740c01024040000d91508041c0310030400141d200300607100020f88160080d032001091809c80010302c00400c0ca00310706540000d440c550f241c560341c0c1c0400c4190300c0d0034006c050003024012001c0200c841c00e51603103151218000c2203510f8068a42c00601000c40c401c6e81103900c5000306101c49500ca5028425002401d28002e5a19109080c3c1d0203084200c0d280520803910084501c80098150a240500300c1c0050840101568103500040c840b1040c55180d0800a149400002c00c011942001107103240301400900449200004245802680402c54901c4d84030011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 548702401 1250 548701151 548701177
    0x1e0f07050d11040b040f180605220917070317060d06240f030507090516030b010c051002090112060303050304150603060903050306040b010c0b060f0118080601150311 73
    0x90240e03400e42180c074820350b0301060b0385440014001600300d4188806c4010348181000042e00d091140c600341040d00e4180c01055844090350840300c01e01000b1194079804004546408030b03081c0081e8a56542e07580c100041e000c503140d00014010109584001e0800018150580b240c900e41003203000b040074081030001c024510740c0c1e03482d0b480e0b502c400c000390700a000542c0d1151583c21980c0301c9100c91180c01c410301c81210644150100030950702d42c40d014091080007401c404444095040d0012001750864900e520305120000e040f107000700d039003071003010a418105d40000d80c1c2d505010000503c0350f002c1120440f07a0f02e19145041c00017a901008a82c0c010b5000440821402020307010a401081c02d5031004012a00c3c10001c13004244c0c201d4040c5208200440c1c0c200002d640c0ca00042d1103807560701e440284a00d0080002039150300e0000d03000c0c801e454040c50b140080e58410002c2d000290700301d4004040540c00003004001e9041080c04110f101102c83c40c0038041e0741840b4080f81228080c4100800364 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 548703651 1250 548702401 548702411
    0xa0615031e0c2007081b12032503030b092a0309030f0f0f0c0a0b0c0c070605031503030301030605090708030406080705070305091c020114040605071b0e1e0f07050d 72
    0x7240b0383c1006040c0290800710241d441c15004140c0c08250130044482e0f0500420b080145681c40d0300b000b2007514101c00d40900081c91000540080a001c00100c6200324107040ea40c00d2142119101c554142d44603020b0701d60351a080d000f400100d80c11103c15250005609a020005c02035540b6022069030200045010760903103804080d001d040d010301488003074005031540419000f030300074030000b003201c002c0d0f0250f41008490b0310303900c0f80c410f100e1240c0c81d44d452059106601c100401340c0710b00001d5500680d05a151003043c008030002909551003a80203550702c5e03494600b84007070030105001c858010309442c0011403400c0d00d04640035105000080c015014080041604010306004008071600309100070f01ca0b091042c4003100940050f1070350301081c0e0004003000c03409103c4107a20303012503060301d14540740c407420301c501c550780c2c3c0c45e401c2185082040414801d9400041100d0310102d514001c40080d0341d4100000148601591011001041150010980d0050009440e040310490702078032614100411 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 548704901 1250 548703651 548703707
    0x305120a090203060f01030317010803090108272a010c060b0307030b09010c030b062713020f0a08060301050106091403120a021605040e0d080a0615031e0c 68
    0x810012201035014080c9104000042e00111021750513288241c8402031a00645040510408000d00643d24030b90300802600c5e10360360103081d50540c05030074681d16016078407103800401450803862403078514551006107540c0300c5101140140f582451031406981d100007900300000d148003541e46020b407000c3d90b1703010703801c11135102404554007654100103100c0890a0210720103000784400c0795144000303480c0084566031490100c080300c02d146002c0c0d0304001c0e0341005028020304a004007050070b034003125060382c1c850002c405d030011307149040280507440d884420801026014910040150384241d24150060040580000900040c0d41c07102e40c5800100e1801380c0424580100900111064140402d8400500d980001ca5041c031f00c00440707d0024440e5220103000c141d4002112070502a0091003a41096030306c1130341459441200d101c0046960303503032907006114041014420340d001941702c100d0348030020200091001c59440d044410410b0380401c81000b80400b80444050100e0a5242c0c104a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 548706151 1250 548704901 548704921
    0x50301050d0f021503010509060306040201081f0f030c080601060e090a0b03150a1b03090506070302090303040b070501060306111207210608030d060605040b0906130837030512 77
    0x140c0c00941c003074084c42d495201845495681d801c05d124079403184420380b00040390f60038041001ca01603503068440c00c051ba00c1e140003852a45118102c61441107080c40c4000580d150b40c0b0070840d00840c06100c09071041c50401c1c02c41814504142c101c0418030000300c40c480103070b1300e84c80c0149070302031030f0340d80f00140d80320082c40081d00f414004403032840612025400d01144141c40d80c401c5d00701860301d02e100300050000c04d60541c142d4460007809010303500034a001074190390003500213117000703140141036034a015141e02004800c1d810418007603031246e65484041c0108090b0b40b00b0502d03200400880142021904949100c00c3e14000302110100800c41e650b11596180100a0301016110f030402400020385039084280d503508002001103400d81400700010f900e42c0101c0c04c6400356200465000d02d4a1201c400740030b040d074440766000400305d5040750001000c130028098400c0040c100740d8034070400d80c030340348812180414001d03240380b06c418280c100740c3c00603810a007218000704071329440e00c0555450883d42 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 548707401 1250 548706151 548706173
    0x1150e011710140f0a150c022107060c200402040b040b030604180215070201022e151d0c070501090506040311120702040207060e0706051c0507050301050d 68
    0x48803010784020720296112581902082e03c96005100c55011008010861071140041e02260407610b0004180100f0344403581d210b003000868208038a201c0216800320b10241321120060f01c00300b039625a070104145c3d0510041004080c03600d000002c100303013516054400002520512080340b040c040000ca40e446d640c060342e00802201c1d25181d1210755031182001030344e2013110301c244254a0f1075444030348a1020038160303400e60b4016010035a6110440e8a0061541c06110140c0c19845159545e15446940c000b07482070300107500c400d500c01840c03030010900960710140305500b403010b40030800744135102106c540c180c9462110103a40b00e840d102c008400130107100b0b14101400755420024130070705001d00020018080e074400e540304490350300651000c0303883d0101040c0424640c501002080054941034000e07200130340c0120f2000440c0b4030342507a00c6107081103542c0000f010031400b041d584801040000082c2c1070948201040c41745103800d28004102d440140555403007503907a186203d05004843d108 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 548708651 1250 548707401 548707427
    0x100615200703061a040609061a03190f06150f050d0207140102040305060118050403121d3408070b1b0303070c0b01060203090922050a0f05010b0901150e01 68
    0x10000e80c100b4642c031113440ca82007030106010302d0a09a00142e55081880b91100b1500c0c0c1808500390703140001966900c940c0003600440923400d200860f06409403080c818682091400741e0002000e5140100380303040e014151400206000401e68280741844e000300071501d080700401c0700140d540b245131800301d0b040701e401503160000e5840894044100b00f00020260f058441d043c285040c200180e54001007075230000c86005000070b00c1401c0b1444400d41c00d0b0001c060306400c035404e685891400e21205490030064148481c0709003006401d10344590010310701005a0f500c0e0310940e00c00d6034184140241c0e64500d502c60300a035140001240000b5400000001d400703a1007000940355a8103004500a000c1110024140d54802c0b51400008010380000100d81d00340c0700283c40e1850b40c2d41c41e021596100d400425a080364201d04903c0f0390006071040c070507603101c640b14032400609102c150070440e003102c18204c10680248200380c0148001010401c6240c4461240c3c6041c400d01e080c1c04004949030310140301 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 548709901 1250 548708651 548708663
    0x60902034c05041119030908040509090601061206060e0607171201140409050a14031c021215130203070509120f0c011d0906030a080c100615200703 65
    0x1e8040c126552030a10100c4408580134400da641196416131688280c1c99507124050100c15035645c0d0314000e8001800c0c039402070018070708040c3d4034030200341c02032002ca0703954145d43c01c07040051201d550024846181d50404900c00c0100341d0400ba005003a810242007400e00c600030105441c4100b001c3c16500c2015802070020440c0c950f070808101c05803110083c0258600ca400944031855642844d2044003901038001c07004002200c100e884040852109a1105000307000070005100c070340720f0010002c5403001c1c15000050341e40c074235108400b20004000e8628483d0000d144410300b40ba6a03031109202956400b102e00598036240ea0100341d50314410034060940040324100640101480425002c11020100043e92010412440111100d0003181c07060507007104c01034280415411f100c01865840140074044502e030300419102e4101c26000011a00c0c410342c808580d4410b07144075030041c04002c00e4804450a00f041003560301501044866600c3c3d800141101061011104200004401560010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 548711151 1250 548709901 548710021
    0xd0c060906091406010e0c0d020d0e030310180e030406050c0a0b04031214060603070c08091c02120105010513050406200a020f030c0a0b06061c0b0406090203 69
    0x302e4443c242c104001c2990300c0c1400307020000a01d60b4000d039000e030304c40c91b024030600d490203180d540140c000350040c42d10001c415a80f01e4551180f072000b003006502031090b00448a060918160800b11000903842a0580441c10700c6541000c40e28000300383d805560072400e025880b409a80651441c0c80108000a002450440b0030301052681061a1a00c581c0c0c4030342051040c0104107241300640300041c0ca016801140420000f06043c1c4500500e02d4400d01c0b8175459860004501c0000d02c00c01038110050b03514811111442c0114500381e40140a1050740100a2100d9890f041c00030348c0714030504861360019600e9a0020702009a03c1e030001e14120704402e2009512001da007d550150f400c1f00c040d42d005803044070121294042d0020903124000900c0c00141240c030681d03515000c8004002d00059003010043c001207492441d801d902080414040b02e00080c00d01000081205440142e44004c00e180c0c410424080d0108000b902c10580f035564040c154442c0009489040002880c9281469614210 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 548712401 1250 548711151 548711153
    0x110a06021e0316080a0209030d0e13020c0f0f0a030504210f1506080a020a092f07030e01080408070b0606090607060203011703090109031103100c180608090d0c06090609 74
    0x103c0069140700c14550b07403001250317a140442800c911a0501c51541540581e0401c12a9442511051400702d00540803050521800d550032042e81c0100d00d1520305134119004840b40740741c0800030388402004600c02010507188545028050b445103001d501d000c1980d070001c410340700100b64404030909901c4090f80241a0450400300031803020540707003004d0b4a041490004007900000ac01c40c40b81c0d134008140000952800c1c40d44401410074411507650384440703618010000103800100d180e0312122000d9955104850b14004001c110603910f401e0611003c0814000400c04010a0760442d0b54050b000055070340713500000949034000d1029440d1b10490005800c000c000868010314100c4031400c0f130010083c0c0e4190f910710f840c0d0284842260004003034141c2003001c980000711a280c04100034040da40d030781c0ba8181c561002da4480040b5600411001e046580c1410901c980c100b000305554989001d003420280307140303034403040c68074a910200f280d40c1f4400003d222072079005c040070342d520210400c814892 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 548713651 1250 548712401 548712421
    0x1a130b070c0212121225020703060c050f0405061309050109061a030411090a1112150d030504090b03030f030108010c0f0e0105071e06090605060301060501110a06021e03 74
    0x4524412405160f18045101941c2400540e4428618401e00300344d00701200e00103519012400180200701c10b0304808186446039030826010380202960794003900c44141903003800f50550f08811248401c11074100202191003800c0700641d81507400031102d09542f1002030321070b1811800c440e000354068a10304000018000e03480d501c444112000e1100b803c003030300070700d80c6110483e000444010305031011045000d46a49810f55029502c071801000004925440000342c40282d0042581000c045107507200f07000c80c022000f541c00c1024502150b265401422659004106016600c1942d540c5600d8251103074450343c1c2031050318400c10b44031405903102e40c0d40310003281c0130340040d10142e804961240c1c4480b00043c880c8160285100040e12050300c1c2421554a0300809501189190226034a03240032100041c0e040c001d0b000d0070b9001d6000480c0ea0b0900344100f40c21903100b5444503041c045a030703038141c1e120b800c0810b600218580010005882c2c000d9070035003403c04000c01a42c0078407008000100103030205 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 548714901 1250 548713651 548713667
    0x1051602070503010e07121a0a09020a05190b1c0e030405090705040608010b03060d050616020f03132112091805130f0303110703031b0c1a130b07 64
    0x110650889000342c2d551400c0c94220b501c3c445c034141c4c075600305140031f0112139040944e03108594840c1c15240342c03104031141d602240440c1541c40b14081d507210801082035203001200540640021941c0e03818003000107110b07100003030080c0f203800d13800f84001c0795a0400f080c0080c0c40d0420251012014015200114103194803980903005643c403401195000c01c0480d480f5500b61019945e6075260303103009902342410040700c1e40004107407582c012040d840c9000059401d00c44607029101d0107420001d0383c130741c4450180c02c25060030380800341e81e8028414030b006461f28607400411140111103081020704100e00001f4000c00c0d2050141042400182040c0340740d030312111403001c44400700301e18265007044103100300595a003950aa050b501c00010040045010340c0c3b481c20010b880707800c6c0001c0c4843d084c2c0000d8103582044c6000d23404a659151150301421214038801c01e840e0b8107182180c8028050b80e180c000f0303032001e41400782c6c207103c07140005110500442208509150071603160110361524030320044c0424 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 548716151 1250 548714901 548714941
    0x161808150a050708150a090f0b040e03090f0f0d050604032003040b12070e0901180608010207230c0a23010c030f0c0206071703040308180604030f020f0105 68
    0x90304440014514409034440c0502030b6541d41ea4205141e116000a44c05291841a0302ea074411070060740000d4402c5203104c0e003210481105400b083c8000b1002c1000304880c6007243c641044d410800031030303403180d45101203020382007401c46105089441c4040070480e8540f0710300c00281140315040a00041c90b03000001c140d00078007e50203204081031403030030f150f40328015846880c110080c244055000c41c0407a45406034801003d23344055050480000a00007031700130b80c854003250f58403010140d5100003502481c0007825161000b50714207529a640d41c031808400421000400e21100e041640c0c0c40c5c4140841d100070b01d401484480b800d40c0b10205000407071910b0700308816201304059541840d50040200c1d012040d0103890b652809120640150740c0100c42c44403c0342e000d001000104002840070105010080c5452996500d0349000d1034094004040500322800300307072015440070130b09113000030203503845545458060443c4000c01c1d010703460001c65041001065003014200302000140fa11034800751 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 548717401 1250 548716151 548716183
    0x52101110307020105340804030e090103030905040f06241e08070327122102071112030715020702090703091217010b090109080f010203101508161808 66
    0x804601c0c0a800708038006c00d40c02c03440c0f00e0000494a061140140003140d0f1050080c200070390f1403851440090702d0721000740c0088001c0b0b07040020a1059003094842c8405228148500b009510701740035410310098040d03080160030003042c41030301072100d203e011504044600c075503401c0340340d440001003c3d246920840d200300000307113000d422303045540d0344030075000c10b25135030900d982024132013074640492050780b14200505210518104144019804003003a4001020107001610703040c0c0d82c9400c0c21740302c1d0341c01c41541c8219640044100700f45d8000c000c0318401030740100ca00039603000c2c042481010f4050724a0217076102500004000845801d90000c8801d94403c0c40c041c035426044503401e44102d081d42400000c01d85a000060006400e03e100500b8042014108011000e541c0c40d4120b18100104c9546e000c7c903500402446041c020041008001d018010705000320000030020050241100504840565881d0310500c80340c03d00030b002d84043d4542440c0450001e82d00d070748100b0342d80d44088403001d002c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 548718651 1250 548717401 548717431
    0x5120408070b062d042c0c03070602030a0c06060314011508011104062102130e090705180403090f08010606020f0a0506071404150c030e030601052101110307020105 72
    0x18a02d000d1089048840e400301e25400308403951003041d01c81140400c1056001643c48400154901041c400c0d040461109076010002c1006c80c200d250802426250341c41c0079912005c820300010350040161901d0208074034149042024504284020f0304c6540e0000c6c2c1005900042c0484d02c40c011f4101101103602282c00c0304140c0d9844921608840f058284070b03d803680d044c002844440c3c4641c210b00c1c80200c1c102c0324541c140e110461f4440c2280d00258000384406004407041000c04070081c042644a1040d40140c501546810041196141c0d40510306e440341d81c0f10f1001030200750160900344081e02081d04031410617a1111810b42c020405030045002500c40c0e0348000e4001b11000920412441e400b0300a0000343e01c8007003094400310600750441420020034800482e0004041c420400a03082a43d603072a1101d8803810080d0645500d481590700a4006400502445c5caa400342c511300c4840c43e200c0c400b02900d03400740050040c030003030040403825a00001800540f95054000d10701410610096141c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 548719901 1250 548718651 548718661
    0xb090601081b07020303070b10030b100f152606031207020a1202030f06040501050f010503010507021203070e0303031504150305120708070f050d0906230a05120408070b 74
    0x6429008a40300c5050902d000c00010001d04808003908625201504880c240000f50b9a686400201101e1141078145414010400e2018080c1059001741024807051085400e1a8004260100500a005c604441c803088140028480d801c03036601e0070302807410034440100140032150ba0312404e5030f41620034420044228042c0c0100d9045821070741e40148601441c80c500040c0711100d040103502641c1c18010f440b0341d04c030010014000c1034800c0b40720300000a428035044084003011881030304014000c0c0e01d80b030100315113241c0010b2111066503036002ca07643c6075600d0800841d10384050540040e01400040140300d592241c0e0380b180b0440c080222400c0c0402c050789880402901018400501154014040b0022505e0203600401c2464041c00180f46007440680303981c0288011000d080350540d1200c000c540426901a20305000b4280350300e0b0002d16201154070741410600c09040d5110158400100900180d01840803500292150000200341d8036250a00003601d4001820a41700c140071100092 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 548721151 1250 548719901 548719907
    0x15060905030703060b010216030501091703073015080705030313140402160b06010f020102041401050318062503060605070b060409060515040f060501090b0c19060b090601 75
    0x400e649015008142d910700d1510b030313103029085008001d41503004445184045081003035000029600400020945501030314181c2004d8031141c070041911034091041c85402036100114481601c0c0b030207081c4513100d021418461003035421a00c0e00900e1842c0810300c6190181008a6000305d0300404107032801d40e9510420315460744585014608004000c40040c04904101d62894444c6c4c0390140c40141080704a89001a07c001c24140a0b25802220000c000d2150303886806000071000328802903050038680142103201c21041c1802c107040c40800320002d5403004041680215118020044441500b031a0500301c82c003881420340c6120116a00b01c511014074060701840707045801554400b841d00800c0d8803100d10308440900f90329405a2034074141d0021510341d024543c016802d607503207500349075100c40030070045603103030817254400c981082c2c010005680c003c10f01e10110741c0c45c0c7c0d660035079403a00d00e11900d051482c2e01015031a00170740107055605002140c0d10940581704142d540602d0364407150015 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 548722401 1250 548721151 548721167
    0x70603022b0b030d0f02071d0c0f09040213051009140f0402120a0603031404060801050d060e06040b071205130b0402010207030606060203070309270e0a0b01091a0105030906060f180a1506 82
    0x100415030b88c0030041252419036100920142e000c415116042070710810024007030382d0100691315806407003a1010301c10307890104071345c50f607114441c105180244d240207241e85094450031102c612903281c150481c18140c45075012035201240c0f0803c45481850414074200c01010107000c10380000f2000070b690403030201d81c0c60844054071421344032080d51b6840e0034104604003030f40c424122281601e84500901c00750302040080e00641c410064901c161501d050010103c0581450040505050070b0a001e00751030200400703048103802041180060f691400143c6c0b40843d00e600c02800d1074940000040c16030303400b2000d021094480e03962802d40316590804040500c1042000d81903103055103034640b420740c2c074550081a10400c10401c1c0d4007040d83c29117403658420400d03480000c265403502d07015248014100b2031149440f070242801340c210304020003015540e03107000741070714010894150040040c2d42c0308960300042d803000c0e0340c0c02d9015107480d01707040d4040c040c40c3c4800c40011042010110b85140680380c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 548723651 1250 548722401 548722439
    0x916030c030b070c0c030b190203090601140d0305090d1a0906060301141e0612030f030a0c0206090304060c1b1e08010606053c070302070603022b0b030d0f0207 70
    0x608800700d05507141c00d030814001900180c1306051235084014181c0d4280007452090710000c001c2c10303040d813500080b0140c0f128014038076486600c0f10190400040c0c2c100044e544201c00903991803164140301e00e4202c0c030a00285011042406401040200030800050580d01c02e98080e030003407003031a03140c0d8058460000144d6626044140900d4404900d84003040c0142d80000d004051190121414089504560160b03004010b00f6000008001242c05180600c0025a500744001c0c5141d00c1d10341d200030303128000d40c0105c0081040300c8a00b0800d004480c039849030601d00400080701c00f9070755070094017244417218820310000f8045480c0081d1085046c8a81e00450b502c50b143c03145020446402213000454000c100200319030b2012801c41041c446070032a0700b00b20b082c10325241d981e914908001e0300e011070680c8801c003010f00401c0301541d080d102d248002c0d401c400f82c0719159900800f2000c480e025010708801d01e90148540145002010744c08068030400000230b03000e540c02951211508509001c020315 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 548724901 1250 548723651 548723663
    0x18020a050402031b031f121a070918091a01050a150309060e0a020102070b030105060d0903110a1b080106030b0610260f06040c0207030303050916030c030b070c 70
    0x40400ca542000d4005540c0301101030040c3e510b80390b02d502c03207000139001900d00002c90107403c02191b000303410141d107400160180c00100c00f0380003002d03a100100c10744005880140d010110001c10706040c00b443e50304000c2c0c1040c08078a61580d00143c1110b00402c4900341c190340c0c116039681d807000818141004079050b1a006007410003081d0800074440113122041010008040c6d40302d5048010035514825040030800f004c001d07103a41420ba000082c5400d03a6900900014a0100010080b81c0d64120484198849207c3c001ca03500e0002e05082c0c031504c0e451000c4483c0e60240c120354008110501c10b280c1181c000340c02030349412030346516a080c2224000e0000400409a00005c94260302c1c0440115009884502d000740003114844041015425072400d52559080c02800748441c000302003141d01c0d0301501c15a020440c40c0d0750342400a41d10308040c4070240030b0599030008942c0b40d0606200c251001c0204907034408805941c0e1801400c44c40040c0b00c240c4030b02124101041c02a03100b4184001a160020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 548726151 1250 548724901 548724919
    0x1006050d0b01230612013002090c21061302040e0a020705070b04080a030e040e061308040b13030204050f040b040b1003060e0c0a140114030a060302061605011802 71
    0x542000c941221642203800c0300c1c1100445a24584c0e01c0740002d281800940203001032651400c401800441000030b001c254206030304410300e02c628081c00351551104d40440d1140ca00c0e4489014054403441041c240b01c400890700c880350282d0f04603052446006250a0720404284038079503d0740c0c0c04a01441c018a40d9800c0000040350704c00100380c000d02a4507015800340c0c1c02c600c1d605c01144a003540070340d0220780d2540004462109044d00310143c050804e05c1694148010340d61840b6003501e4880040042c00c0c03016050710000240304900060f60003402401c4002580d4101c01c0050010b50b807400e120492181c0d040c54001049126400000c9020710b0b807146c20f01051351525a14064801030003000403910400311030000012850031b0148034800c82c20400580400c0350803409001c0702ca11260420340c000f0700c01e428600001d90307114102450040020807050380303a4440a00c0c0e02e0141405600103035100902190f40221020804441c043d803d100c0c10003000223080c1405521140b8564000203541711100d5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 548727401 1250 548726151 548726159
    0x20406020d0320070b0f060f18252705010e01140702040f020309100b061801020f0601091b0f090b0c1f020a110313120f0602040303021006050d0b01 65
    0x340c003c1c0b0035580180c08045103222401da0501001d41002c41c054034003070324400c02d114102580c580300e190400c005860002542034142c1c0850500e16907100201c110601150000e00e80000c401c282208540d40d10308c00340c003529510b900c001c20034175100c807107180c1b91064400c02c010420b81129260bc21584103071644509280130500540d84101d000402c500e100e4001c018800041c2e40703d03c6141c000181d40c2c0001a102c1c00d049001a00e80020258810003c901d00f90a41c031840e90b81c94191070701500b061300c0300e00c3d0704016140101d050024107101c050b1144145070000c148003103a504100705003400002520240c113480901110b00d800d04420420201b00c3d0320b40148440d281810040140c0c0d1260402c4a0076200c9440c0140c62807860340c240b0305d0107240d01007202e14800358400d00400090740103400940c01c01002084540c0c000209100c1e80106181205806c41040200c52040d081c580c1c0060045482e15524180a0b40f44d2101401500d9854503000000c1001d1400620302030380c091300301d40c1c0810141c2c00c3c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 548728651 1250 548727401 548727407
    0x601031101140c0109170307082208030a02210411090a0608061515130510020a080c010b0a0506161103010f0603150c05071e1a0108150604020406020d 66
    0x5100160307040205081d02641c04001c090010840150b19000024400c1c00c0c81c01d00c0f421806000340e032182d07100700070018840010f5011300c2c0150004540d036101e004c0b003103040781080040c000100004011450100c02c0101d5150035034042c0540c116001c026624030107a44040e00d60344032048500825910003200c03003040320700f4047c5500f07078040c081810000e00c054070b404002c0c2c94030f20100d0714040482300001411610b400c00c07000d51002c0d03200d011003440c10410121420040b00c41280a514010680321031010100f44c4204601d00c074868208034150340d12841c000c0d03014041d0202850040c000c1740001000a50350510000301d504c1792500c032080d0b1920192a42d40d02c507900e01401c145642c55900c031038100001512512840009500c5005070302c20010f000000c2e2030580c2e456450003400e2000074044040820042403d0b06004190100010300d410031a1070412840b080040500b11403805070760010036400000501d0800c01070307007950142d0b91035803000304000a034480d50240b030005030000014000c0c0680 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 548729901 1250 548728651 548728673
    0x10c080f04061d0d030f0b060d02070f0209071101050f15011101090206031009060b0f0406141e04180504150b0f04050405011407020304030804032004112a060103 71
    0x481070b5008070300d100e40110840800c0702c05400100c0c0030b8128484505201d0f03010320584164415900080c45416070840010f06a0b00030606001003d980018840080046041ca00e1001c1507008102c40e505041014000782400d6403100380b41d50642c03804000c00c1010700781510241c480c03e85e0090024000000d8001103400d0708850404003269900c4407071910069807810045e41c41544030880600040b450684000192407040e4003640e180e4404010490742d419030507084405594060804104424644a00d80820711828040f1700701a8078080e800b0303104100c0c0c80c0c010401c840c0200700b480c44849444080404841054400a18504402881c405900c090750451039114070001c041040e1604410003140a80e1800c4070200c038030740d5550042071505401c0180403500a4968401981403e0035a40c64661600c1940400f800110501c01c0c1d2902d82d0f442403203800c81c00b003c090000d0143c1c0994560840080e0028248614001c04001410108075510141d01300c3c43d01e030103c001c000c66480d40d203c5e46070000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 548731151 1250 548729901 548729903
    0x1201020f0a021c2c0609090429060d031119060917180909030c0f0604052b080c220305100902131a09041a1308090f1c080d050108010c080f04 62
    0x420a106c009042d58039508020b20540c0286900810304a02d11305555108440103c0044003001401c24005583c0301e209000e404a94581003070071060704c01804480c580503504a04111158801707414034104195504008210391044c0c02e482c1c00300500c0305040070703540140c04101040d100036031030b510071915020868a8200b0803040540e403803c040541c001b820080340a00d14032207540f1980c10b01c01044400c001c122440e2541c010341c0c41e070303036003110800e000201c010074084400c100c074407004610768204003400c5131807d00740a0b241d070b408818a0640e4800044007072105503204d0040383e40302d100c01f109900641404503801080e006c10911409001b00080c401401c1c55101c85246504288081d11340b500303064000c074040d454000c0003030700000689041e40d000030852414084006544800620200155003000174222042c14980c0010303c00300751203410900301388284101c41001c91302840a40f034010b114490380d146041c4010f81e250f8243c42d01740d40d605803143c3c0000e88040c000600c06025000c0e116040303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 548732401 1250 548731151 548731159
    0x3062a120e01021b15090a06020a021912030c180302120a02310911010e010e031c020106050303161e020603070905010e04050609061201020f0a021c2c 66
    0x5a00a03019050032a041140c4030f140081001d0b01c40150044108030b405c51030801030200481a140402881d5250800720b100100115004100307603242c0c900900c02c0468071a1000b04100704c500060402c0e1501c586455205400f080c6407508600d491071150800107404000341c2c4880103800c0c9113509100405150420034643d41c0140c0f01820300503a180121a400040c04510041c000c550b02c4041e1030621002000b44140c1c1d0f4500001302000038041c0e0342c0361140c1c07082400c05c0d11404000c07a0060303078851041500d00c0d5150098081c8902c02e50040d1128515a641d40d40c020070003961100145656886030a0004100c0510007070142c0c0004e049000340d43c405591a10096040c0c4240e1340450b0480d00240c40503004128417560034445960302405694040d6000c031020721041c109400070803002d81e40a070240b4054422a042d0303c112041c25011130341c50b090190300c083c0d0b40f85007620b0020744801d890344c11012002400102c114585104150441565085903e50309810321941000c94111030762908082d04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 548733651 1250 548732401 548732411
    0x6080304180b0603070c03020f0a030c02062b0507020c0d0503190c050d05040e070503040f02040507110303100312050c0c040209180901090b01171e01020c120403062a12 74
    0x3498981034003842c010340d0176880703030303100c085080c0b13006810031210601c001e409038000000c85020a03030100d2035200c55074050b5855942d5008946c41248030f064103070ba14142c5071074400d8040d610000d40b03901440c81071146d81d080d1448c1680190400240822074a005030250b40244100075207402071000b06a0080010b080103290075100e0740c1d071141421004261070011030b070045810020344c0030a19002d54000345519000c0e15500d0980d884940d550445440a8040c40c1d45900054020f4003540c220312414000d40212602c0c1e00d0060250f01064000713000c1266084d41d0a42021aa0350281058031800c006801c050003001040000b480025000780d400c11741d101044800007805032000c604924080d4074020000b00c3d4080c2c86040464040bc0103a01802c007100003003900390481c8901044407118150000340781c1280b802c0d04101640a40030b599400001e502488988601c03003071000000f80100e0744186010304c01174281c0d0b5001010b8038020b00300780303000000c3c42c924452110701c10118010010b0342c1c12000030f4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 548734901 1250 548733651 548733671
    0x90a020a080307230316030912060519020a09060c02180103060b03070510141308030a09080c04050402010903030c0201030e010608010605130510030b0a02040e071707030608030418 79
    0x120003100e9520203861604002480c00c04d00c50440b041d102d981104900d01c1500c69240610280da070b20900d40d110b03410190100c4800209441032040000415080f500405099410300f0720b8801810199010320a28503100600c4014101a009580d401d030041c0c0c4902c48028a03040e010b4444c600e0803542260306c180c0303c01d444040d002e04c0d9400715020b98020080002d54048400900d4a003010a030030681c42042c60301c40807100300ea401414042d0b5140e40311700c03003030712080240d4400d540d03414250009070050101003440414030b0b900c0b00660f405c4810040c12a58411282d001303000c201c450503103020b40001c0f034084003800403901130540100c880780b041c540020000c0b54843c4242c00c6a609400107061030351562000c00c91441c280744100021441440100401d0030300e2602101441c0c010710004110305100300000303081c2c105650603900140071100d801800f51800d02c2006000c641c041040c1c090707090504c4c002c2425188240720340801d0300e0080d00194580360514891001f00b01d007600c90032038510b480b144410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 548736151 1250 548734901 548734909
    0x9181b091b210f0f09030f0a090f0b0a02070f081b180109050610020f030301090905070306060b0904111614010b33030906040206092b020301050c070f0b090a02 70
    0x8521400b103020541d09200c00030340200728014000c00c032500001e100307200e003010010088800c080404100310303131341d00702e442d00648031960b069000035400c0c850410b001484c403080c01c00809020b01c41e03a013600d82036030322818105107010039801010f0465100074400c2d1a101c0d4842d400c0401603400800c0003007000c0076a221440142026082404016150024402d1900704102034076a4052036002420904003c00901075481c00705200d00329005071100030308018004188076444c06550004014401e503a20740d400f2346040d512041c4414055032901f0031407284a166041914030005181101e0b0f0180038440c0c5030f6102a00340e00b10742c04959540e0300c01c00301c15541d850010140ea101585800401c06058100000d516900003040351656001001000703034a900100d0140d51042c3c1c1203580b9512102c024000c100070729500b003611003440c00c5841c4200f03480146034118490182c401c074024040ca94a40128140a01031058020071244080728824000350200034096405007501e412103052070480d800103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 548737401 1250 548736151 548736187
    0xe090a0f0305070b150102060705070308160e030307051b0a080a150209180603010c0c05061b0d021b010c09120609020d06090f1a010b161109181b091b 66
    0x885c002c3c80d102500845103580600505500c090103090590a04105480140009030018a12042c0546100d100100c131400b9000301c0c80036038405021241c95801515156603603c8102d840540e0f0020039422104031032900c50400b40941390541c000e0719603400f0981d19485044004e034904004150284605440354403500b4025800d4104640c1c850001d04141e0141400c54452044c1d0804100c002118440494000901140c211004046a104200851800c00d80900402c141d40b0110342c0002030f10021041c440142040d5000084000c0100d2003c404050b141d04c0010b114880d840c60400000c0e80200300030f81e200c00701290010f0f1017051980c6141e52520121003592a007201c100c901ca440c25000d11200b40a402032007410b10007002c80c2c0394180145480d407800b40c10007541800100b101c0850030001d10040a12070407034098400601400c0000400d484185045280e0013588203541c40264106017200f100024442c02034601c0a02e40c03181003032007200540401084031120700c100f04076000300500c0491 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 548738651 1250 548737401 548737411
    0x2160f062f100b060301050a1a0c10050603100603030e010c0c050306090a170c0604152009010f0e060d1104030c090203150d1101030b1503010b030906010e090a0f0305070b 75
    0xa0407402c00642c1c0220120390941240d00d00400003800144034a44814946100b680c00b000c4001c50070060f0075032409868816145079042d103000341c2c8100b858071802a08483c4c010003046003030f01c840c80c1030141604201d40c290302c00600001c0c0ba1801c405402d5014032481c4000360701030290400e00701d40785c0700401c0c50300d442a547c01e6510350010036528180005491030812000546a400d803510a0b480841c59071038102520181075007400e1000e03017282e40750301c1d40139801c03c50007190701802c201f1010200500a80010a2940c0442c894210318051144204030000c84900000c200e00e081c500f100c1403d40081c1804084004854006c2001201050400c2c045078000d01c40c280700980c0c2c074903103449030f03508051020b01038500814407105440005018030380301e803002c05400c0c80d0005940088100241d10012502c1c05034604050020021a580308407000441c0302d14042d030115486d03030741d8440c2c80040d0484201c9102916410616182c40001c80e1920501c2d82c2d14020710f041070503d28542c40c0e2410801c0280c074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 548739901 1250 548738651 548738653
    0x20f03030721030e07030b06010815090a0b01081003020d0b09070e0127020405030303181e010e010b0f010c0b04080d020406030e0d02030a0c110307090212010602160f062f 75
    0xb03200c0744500e03031500902403090401070240401600c1c2d660381001255000e4202414010b600c00010301401160464400c420401010310009081454010f0002d050070301a50703000450010000f00814010103460301200d901130459040e00340c05032a415510407024001070702900800c0300c002240d203840305030b0501900e1069100f01d11b450b08190055240503a06580d030915070300500c01044250303000300689a009074150300002a0040c04101107042c03000410708602c8461603609481c41d0300c50b056004040340100c4100030411002e0440411580c2c4459011950000303c0015070325001546405100d50450321403910b0340d00381b803111047c090590700030b6000080025031302c44402d50461420440080450a0b50021314640090560020401068030384003030321102c00f0382e0003e011500c0400c00c0038010040300b01d00715103030300c0040c0062944c54828454100184a0060f01e100003506400819044403220030b01c100c1c1700f500d006000e0f81c40c41e1412000c009d00550034800080d420f00711f0078030481e10103e840 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 548741007 1106 548739901 548739953
    0x50906030708010f0c1106040206030112030c1a0a1406060412031101050708090f0102091c290a1404110d02060f041212050a0c020f030307 61
    0x81c0c80040190300c0c0010541d044401d17640040e84001d01c41d078451688440c0000c0c540e55a034000c0e10b02a40c4001c040004000744a040c0d061907406900c2030034a6140c1c540c0395203031b02e0406403c090119020200c01c5040010f000c009100d130074000c41c0034030a09050350500c0c034045080703401940104c0f03050600285100080c0b50140010b0030090030410028080d40c40d103034500400851040e2800091481612014a1740c40b0041c000c2d42c0071070402070210341c200109a402e031520180c6005090700c42121600b10118050320f02640f0040506500580ac0b000382807a910340b808443c600319001802c85901c2003440009100400c00100443c011984130120308070500028032580308103142010425000203000035003d51085010450038000c0d2400d4000d8040b040b000d4a0a128071035a0324001035a1038411001481c10050074042d40c3c0c0040c00300d906050f540e56400c03210203e40d10600c1003e0b03e9079 = true := by decide +kernel

theorem cover : BRFrame.Cov 548561151 548741007 := by
  have h0 := BRFrame.cov_init 548561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 548561151 ≤ n) (h2 : n < 548741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
