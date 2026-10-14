-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1469
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:08:23.311175+00:00
-- url     : https://prove2.me/submissions/2cd21276-e2c6-40be-8928-d3dc54900aa2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 264028776 ≤ n < 264208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 264030026 1250 264028776 264028811
    0x90613082a0d02010908010509060702010507050405010507121103070b0403030b040b03100c03110703081008060f07051e03070507060e0319030504081e2205060304060209121f 77
    0x51055440050198038010030300840d9400e0b00c2e01241480760181e404541e03610280155031050180034010003091408840080c2034074000b51aa20a00c8401c01007840030703076403080071504080c0d00811440ca0401041c0811908101d401072004c0240c040410000104040e40c40343d180101d0107542c061180c0801c101c1008200c4000380b0480398103a101c494103c441d9422070b00942491262800c0002e00c80318030300c106041d607134450401100012000780400040c2d0282000c035001034080103000301098035000010f900303040b1000e00300d041404004582c1ea5180600c4603081c0c9056403404245980302e00700040003030300d02d070028a0308403902030400d14001300303602001054900640510b8aa03190300000c09109034001d00c1d001c0c20590307041c18200300c1d003c082e010b0503240000000ac10300e022075903072902548503c6009186806402c10200144080095030b0306c4000b5203802c181c021400598982d9550000f42d41c4044161200400c0e0140c40e41c810010590403582c201d0000c0c214000340280c03060f600d2003454 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 264031276 1250 264030026 264030073
    0x301080c091b0712110c0f0906040b30010504081605070302060a0801050906010c080a14090d050303041707050a020105030a0906050108010f0c050c030a05030c0705010501030503030403111603021509061308 90
    0x100b000030010108642e1800850481c0c1082010704001010038029001c0b5841c0c245401d0401c6688200c6401c2c1803110701109404144624033000030005400e00d030359110036910508000f2400c040c003a01480c4d09201c41404007000855004100c00da581194603000f13800300704240300d81c9215444d5640001d16a50083c0c40284500394024030071807406950841c240d8006100500d00240c45034148004102a11900e800e5410140140000e41d101d1619240115210301c1304868294034807400d12220000403400521001d04560900b0229100d55800000368018840030380040c000504000000a10800640c400700c003040c00c40700180002ea81d828130941c0c25114040c018541a4420800d0b03600061064002d960480058100f907403620741c440d26151b00751203080e04182d603190400800d002c200354000d41608034032000040548144210410381444c064071034400a0b0040b03052030045008803841c3c03011210f0000c0010030303560311226110308201181e500741c01025014801c1c0b5244043c00c0c40011070308031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 264032526 1250 264031276 264031279
    0x11030901020d120209040e07080105010515031612051e07230703032a1d010534030c120203030603030d09080f030106081603020301080c091b0712110c 66
    0x52004008108441c000380e803900840502ea400d00502174640c0d10740c014000c00d0042c2c0402004080d04000b0107508603481a40614442e202d0541000106001e400a0f2940000342500706008507841c0d03807058466010701840550361910302010090b403807000c40300401341002c984c0b21062081c1e07140e40050b5480f0300ca03a0445600c2c4990000c50710040c10040005004040c800d00c2c0c00f01c1e4040c0e03030740340351100b8045c80600d0b901c818020302c00c4403124580c000400440c03030840f815000ea011100d0b80000e4114481c00404c8422440003549406070743e55100c00000b441c2c1102d4002a40c0e0b000b0a04008048800c203420450307e8500040e001c3ea511440041542c1c000c41c40240590310707058506030b41000074512840f04031407101d024402c9901d02c8402d0b2000d0750003000203449910603440c1403600b0f8800c00c012810381c8018944180018410202e000030031a03030712101074802c6421a180c3c0d0032001415002921068a0240001605803c10034440441c4040c0701150b02e6044490301d80c4880b40c1d0b100e60232100c02d107 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 264033776 1250 264032526 264032533
    0x50f01090e0705091905040c090b040c080c0a0905191802030403090e040c080102120402130e03032e031101170601020303060d060b0d0c0f1208070b04021c050d1103090102 75
    0x3d1082d03261106007140c00c50040521502c240d80100c030920240d52041310143c80101040e00c2c01c104100503802011129035085404010600c58900094911074004c1c12140907090b001c82c56400d014001c815000c060900100b40c00c00000100380c86500e840c1c0e880c0a008864032080208503841c0c102070083c3c07401150b0540b20655a181402c040d000c0541c0d00620a44541c03c1c03482000521150032f10080c04003507041c94603034840f450940140581d0f0a01040d42202c0f0310714105400d10480404000c3e80d030860b000401c1984041c541100030043c0c0402103a40c2c0c54500c2180c0d900004000691010781841c001c2a01d8641d41c244d54140d0406d0001002c40e0005d000d41c10800028903036150003205088d415200745400101c03800300c130f40401d100307500e881c030104d6511080c1241803180e01c2d141140c105c000c052a00303100c000204107a44810a60207160350082c03241000a022038115601c0c0c00134400c8039500380b03109221400e05820a1039683c3d101d2195040461400c045500300e007400031086030501c00068004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 264035026 1250 264033776 264033779
    0x702070909260d09050106030209010b1326010509010209280b0d060918151109060c0a0506100e0705030c0711041805010203180115030312060315050f01090e07 70
    0x90900790b141c1604607001d20841009900d407114010f11420465901840000420508600c14010301240c1030f0002141400107000181703480740c402094034140e43c90707003900155650000e030107000f0031048100501480c0d400c0c201040740d080415409400a0030b0222810f4a4006101e45410000440310030b1541c509800703800e05101007003201008081c03446c138580c0d00091440da030381a04000c0f20541c182600e4015240308550041c000c10008000d00700c0c030814010456081d8107221010345100f40491a07004010100d81f01d0a8401c0070b000640202e5005000c0c0c41951410082003402503400d4011001d014428001040c4014465130949204582c600c1c1060715184880d1192009a03225030000e5034000d85403140710802000605489440750f20400015899043c1700c2d1440294900d0134401603440d07854850010300030b951003801c100c2260b0b00b508081c1c0010003142c1c0000064410350700701070b140440c0d031b50514040031603603401281314031640c010030340841c1d80341c0003448207a07080c80b401c283c1d032684007180 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 264036276 1250 264035026 264035063
    0x7030f030903090f08010c0f1e0e0a0812031006180302040b0a0302031207051b0a0e0a180c140108060622030f050a031b020604090b060d140702070909 66
    0x65104103010b414441d80c0f8568800004400044c2a000a280c0341d440b0f1a16a900c10b801c00014074500110707041103120a055140503002c141204042902001407001185a007510fa1140c0e203000b52082c1d50641d107000c81600901d001c5a44282e4644070b10009015001501c94451010052802c400c0da00c028849460f5030204000340c001c8090066112050f0080000180d074104001d807048210107040580b03440f41d50400605010184003c510410b41c1c42614901d256600c0301180300b564241c03040e08a842c1c40d800c41700e40c010000308002442101d100c102103814800b040d038900044072000000000f0703001c040801103071041c07425501d40b50881c50500804403170505030a0501d4250744006900c66200c1d0362901c400410800540080e90b06402401d00c55007070541c040e2002440442c845009844c940d0f20b58041507003813041d841002c401c19980c240c071501540d90704040328110745145a05205104040c0c0041d80c4103130082c0c1d18107000d0f00c2800000100000301d801000803e1343c102c0050480c0841040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 264037526 1250 264036276 264036281
    0x1080a0b0105060318010e0105100806090c010c080705070b1e0c0d031e021209061003030212070c0e041208090a020a0902130e09030301031a0411011116180506040207030f03 76
    0x9149a15508802e02105ea19010911035104041c407841c0011840381001907025081188540000c180781c0c0098040005558000039194002c200c2807130410300c12801030926800703601580030000d00c0d13405003c20000d9400c072008040c21821814030180303914146150410851403003403002018041d007021000d10103060282d440340311200058199103441d45000c101c0c02080364080020390301c62144007014000850400c000d402d0b800948440055595400c40d100a07544131606d902090901c07500040c00d0302007010950700c00c0000c05241d18403484034105490508030021501d0103034000504241c00042d048100004ca544001e90050483d040e05400c02d80540040e40c040c2114601d000c040a400244c08240c1c011060700c00e00d0084003440d101d5040d0f26009d2801442407e803940481071003402d00010446020607900700c05401d01303028103101824140241440e03411080d035442180c001700001000c851021048601d841941e000308055941d00040000300c0c000d4103000303000204948400102c0c14041d9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 264038776 1250 264037526 264037531
    0x6040b1c1103030c010f06030606050324061c03020c010315050f010305090c091305010b0a1d090109080a0c02030115121b090c030b01030507030629190c02010801080a0b01050603 78
    0x2900f52454121044d07811401e4420078100800360399540d06003041030041d144600d10140104070007815210740b40340186142d20005e0301d1400c014044440c040f40c800c3e41c0f84000d410742c1c1440c5056642e000111401d02130344414420601e00c1c082402d06e05804032162181c201c000c16030b40010034400400e855040110010240101420340c640300b425101800756a5007031000c0e12652080440c0d0841d40ca040c5002403d40ccc4007c04004e0084c0e41c1a00144910000540d080085a1a41d0555075559031080643c0b0b0150540318005466040001242c06006034048004003806000760700a001d855030381c0c01c22034800d48152040c2c03285032007210541800515050310301c0d0ba0925200316000621a02d985030307501103440c5030700218003003995003803041c010b560075000f415400621400c0402500d8504036005200d43c005141d0503507144454042d0720300c0c8030b2142c0240c0c0c1401d200c2210b001e41d0501d13518000380c400c1d444840c059001c50408400003030b035031000003005c00344654032080d0340040c0c1e46040c05110749900007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 264040026 1250 264038776 264038779
    0xf0f020a0203060c07030210050105010c060b2d0a051f030b18010b070606061d090705070f050a0b0f04050a0f080f030709050f040e0a080d021204050606040b1c11 71
    0x28100d403031016039010400350740125085101ca07581c62000b0300c2c02900d8480700118800b04141014010040c1c0d0381c00401c140d42d4150041004a0a0005000042c108800d82905e5202c2d662440003240c0301c0c0c541070892015501c1c4c044e00c0040d507558407101040f8000c4c0200001e9943c29100c250700c200c2d05846030300180c04001010340f1002d20305548400712801c6030310903040140c44c07a0000c11400c085c04042c0c041c1100030b05c40f9084c480d83c4240c1e808c48081c0c840c02039004850040c410342000c03a0042e4030030001c540105811540361481d0308058940780f5120001100141d03102d40c008008102d13042461000c0c140200d0744400141a4840b140d40c840c0c842d422919400e4508040a01c00c926415400400961080c6015a05e0712040d5080401b04081020062042405107140c8004107843c101e0019204039a40c0c3c101003940c1d150000d032030401020744680305140c0350072040340c000d0004110000500c54000d000444050144008490910020680642d070004148101c1c00121000c110515214240d0040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 264041276 1250 264040026 264040033
    0x8010e0a110d0c180b092d100b070f021e132c0a26070809060c01140106080c0306060f070302100203130c0b040602030316030e060f250f0f02 62
    0x5551000380c0d042404c3e8904200615240c0c510080380f072801c0c111041c0c2c0407844800d081d00781351401e0060203211103a00c00403444c140701140070030494514201e008000b0859401d00c596035158500e0091b42c2450304100490003644490ba445140500091401c1040071020300310b881d102d1034a90060380a41010040f40115816004000051142e80c0340b80200c100001402840c89516500d402c5e100310003007103c1024006095100011045c1d0120102e5002c10f800454443e290b40d00007000803400d20400043c03070429880c16000d40607503d0007410071030490701c0b243c4650145686580121115100488506611610400a80e08481289400b0384030860003881141c040d900d00e0304c42c0100700e9005503910b2907140f0700d642d001401c001c004885074000d0711385165907508240c68013034060f40d28000989980000445100d0500119100350710002c0c44aa043c4211012810120138121420f201911004001d00c1c1c052200020740e4214002c045550603940d07203920505400c01011514400400804000c600 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 264042526 1250 264041276 264041279
    0xf470d021606090506070309020f0409020f030601030615141807180b0903011d07060e0d050a1a1e0604020904060b1207020d0f141c0e060108010e0a110d0c 68
    0xd03500c07140500d040d8828640000c0c403003640c2c24450329000c0300800180c1014280042400140c55031900040c01c000255004104801544000341300b031201d04205a2b0144100340000082c84100d4000050700005030b003074488003544034050040c1d824410080e040d00403121031800a0b103550f007405042d030b0158543c50729626400d50310b01d5211801d48603900c080552000800d0100f02d0703250030f2007541c4100255070f070b0045249000c003080700e0f10f50f00c01d0f12480092165094a11003151164045c18500503401015034040c0807c51400ca42240c281800201440a2940008034585011000c02c5824a481030320104207640e40c0f01004042d50080e09403d800584422000031020b884002601c052000340388480118a000100240350008408143d001c0021040300c29203204d810604107801000030f05081d50340c1e80808010300c80480003c0d0320030b0350221b04c3c0211039810000041042416600850000d1104840104010355030b40e0100710068950800101d41e9001c80c1740c0403149480d080d205035030403540039 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 264043776 1250 264042526 264042547
    0x20603180d0f02100605090f04060e060403020601090b090712050705040503190b100f03121e020d080a05190510050d080406180e040b040203070f470d02 67
    0x640c0c1c0d205180003041011142482443d01444640a0342d44811000c0082e20300c1c1c20001a10514048c002107441607610001c10240030f4590040c6c1c0084c0494401c50700542001e1400a5643c03600b44541d06000740780100000091400c5040310b07001d8411607131412112013941c25a5401824050800c906100d000c0000245503103043c005110500b00010542c0305124241c00e00000208005100b98400d07058104107102d170321080c001890503240c001400c50480c05030342c0802e0301c03900c410080c2160016200201e000b5480e0f0b00081a042401459483c8081a181c583c0040700b580e40545046e94404044e604600d013542540e4031080d485151280302c000010ba590b800700300e402c0740d118015205c50034002010320035203400c5008030544902c402c488950452420902c8140240b0141c80100f070209050003040641d83c04000308405072400c84968815507545442c220603002d4008503295003480700d00701540d01d00c0a0b1041c080040e035034011070300c0d40f00b500061074001154440685400301903428045031640 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 264045026 1250 264043776 264043783
    0x9190618240b04022d040b0d0f0b01020d0203191e020d0912020306060405070c1a010504290f010519030525140c0111030916050108040c0302060318 65
    0xc0081503070410031207116034000c0300c265060ba0014a00441c010042072800a96070b070019072100c0300280d0080e1500c000020300e04d605200703543c030032452850041801e07894070010b9030141e5414020000108013400c2104010ba84507040c880c0114090382051240c0a5240c10350501040008540d00e0448001c540190070b44650403840302c5ea00006a11141940302400e401404440c05410700440904030b40c000d55000030f9031210f00a218038040d80e160000311b004107010b4400c13450f080d41d008103254900718040c3c0000c0752040d801d105592140b42802c0d02c8d00340551551200120645100300c00b181c1c0380051b40c0c00d03c68900d1034134020904224041202051000d64148160803d813000da074082a0b50921701e6125100341c1c26458132405c0900303130071302100f0f99503004802c980c8600c450003481e503100c0324841044c0e8018001850491b1504400004110702d075600450442d5101006440040fa015240c02c01183c03440b00071107000f0302c0054540414400351070844040c55000d0802089203100ca07900110032801c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 264046276 1250 264045026 264045053
    0x5060d020a1415130801060602060c1c020702060d0b040c0e0303031302033307030e15071e0c1e0302070e0411040c0f140a0f1b050106030b090609190618 67
    0x104552110803c0c40001c50070b004c7c21004245910041800381040c0010361610700c20024035065500070103250b0320100403180c040d80e8510360014500360300c40880f400d034070025280606100f803103170345844841460980501c1c1c1040b070b03900d00580210f045541d11304002c0070820703030307540103130381c9031152503054078203401d080d003015003a00b0101c0216050043c81d1141481406000b5000c4021300d420b200c0703051142c045c0052049040365049941031156100c1a600340d940c8800000c142d00e03c220803e0b4040d8040e6007241a0200d1144079144034a01e502003e04001d115400d15600140183c11028081048c50b05c0b1444190b04103014a074070074040d207a404002400c82d4031011158010400b0350440340142e03078202c40042c4410141d501d0340b92034200801c800a041e040c02044070800d100300940b840c1c0020010f045410042d13a8498002c2200645908020880ca00100c070a00240c1c40303031100040c000d0740302007654034682d442c02004041c00105e665071400a81641da1324000d003e289000e480703021036080d24940340d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 264047526 1250 264046276 264046297
    0xa0e030a02040603080703110a1e110907031508010b0f0904060209030105010f1806050321040b03150a090603080304030509030a060c030509010c02010b131e0504060b010305060d020a1415 82
    0xc6d544c15a518000e0420b01c10001103070b0190304103409050100b1507840a004621841c05200102c034040da29006011105990040d600259160b04104110ba01a03114003208180d40b500d114005a89280a41c265030010818580100e501c440740720607401e101c40425042840b60a000d814265540080b03421200240e018280040c13205504102000c0310100da09440219484144000c609020210340c1e81e503521505084402d0580c5c179401420390b40781d02a00c02030012603801d150742c0d007840503004440064040c40759104150512000482c00f005124620407294000001ca00319950350705c0644203034000d0800941c06028040c15038000610910441a1001445e100019942050036405d8210351103110343c0010740e850b002146000d651a10144210402c0c040c03004610100b102c2001c016400304000013078841c41c02c15041c80200011070b001008150002c0c4d030b08100c96075900c2d00f007004840e031480d4040c0d0051500d44080c0980c22502124541044010f02400b0300d1442611840c2d4ac00c0d8042c45024 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 264048776 1250 264047526 264047543
    0x7020a1412030d141317090d02040516021c09050f0a180c0e030307320607050c060709150309030201020f04030c031101081b0c1207030201140a05010602030a0e030a02040603 76
    0x8100d140c484c00002e03030080c0820407058100d00e5665100c2c0c200e14444407002d801004081105911079803003440d41c40c0420342c003420034001400c08540c90719032680c035043d1f00c00c00350044150102600000340408624031a45584002c0b240d0302c0d25080c0400440032030b840703d8000f0800d00300402c07000d041c403080300420085e02e007001a00f2203c103800107100154140d0054031a030010803c41010910840d131103542d40384074400c2003441f5101c21000101c24250b07842441d0403400307150104640d440d0070402500300171222109441c03555440340400c0307400d2003050241030a0010b048243c0303c2080d2003543300307004d164820b00005150028032100b501980d00030740c0c4221100c0d101071406000300040c1024180ca140b5007820205040e0402c80381ba03c02810f5980c0440c1c0310ba10020503204100042000119034491a04240c5507a0350010304000b0302901d100031a0341000c0f401c80e0003040d040882c3d072003040d040b100c1541c00f55041102c003031022100c1141061070301c1d5252140da14058091b940350b10404000714400c11a2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 264050026 1250 264048776 264048791
    0xc0503120c0307022e181e1a1e0406090b1501030605060a090b180a03080901022a04230705070201020d0206010f090203040f0510150b07020a1412030d 66
    0x91a01000c541c13a000c00d0b1120341c108030105150b4000580f003290b451000440e00400070b8006d0030100d5170044000c0e02a0350b16046140c10300c0c1d443c03142d412255024200e51445140324810048510105a40c490350b401c00580818400c0c60042c84180d4125102d2903000c0341c6e40c6415101c000c1c540b4000d07205440c0d800c0c0210300142c41983c15100b404000d02d1f09555050500b42c3c0041e015210800724850010012800140c015415502c4800361402000003070001602c90345030b05105225410048800c0e01500c501b0400408411441198000141d291184d01203006414014040034051800017014000003000c0e2100700c0700004603c030bd100c0c200c1680c0381a02d0f82d946000080c68203140920701f1065403c40b400501c1011401381d20b900035900c40820243c2d5940311490454064002c0da04045c003d406043c414445040d1242c1000c4114804442000c1615441d40913021880c400c889009501c0b142d828402c00c176190424581c0036290200074102080301071041021030071075100c45a01f01540350394001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 264051276 1250 264050026 264050041
    0x305090904030917071409130b07020607030b04090f021306171c170c070816150e1f0e010e160e0c1801030e01021e0d0e0d0206070c0503120c03 63
    0x135101038a0052030700502c0d41c20310f040090a4112100f8803854068183c006c0050003050072031481442076940111a103000386084d44000791142c0041e2a080c1c0000e06107001c03096a0b103081d0242500380d03500090384903819446642006052080307081500081074a5040001c0d60300001e11f00c1d107040141c02e0000d001c44445103005440c0c0501c0140b404418081c51304d80c13000342008220340c1a9842000c5218007540c0d801a82040000b9004682d0ba04d9083c1c542c0441003000c0042110b441d003652440c0041c103015003070201c0b0000d516078030151403400300e010742c9403103290616210790000d1f10301c1c0c5510000041c0c5890394a40341c50400c01e00d00040145041e0143d0100a0005011810365204103021611410100204c0c801e411010090480504268503541e210700307580429411250008102104d2514102d032001c9655041d801c40c07268031089a250040000500001080d550921039255002d4030780e42e82c88820560b040e454151041d80c880c84140400845000341340d18807405103403003a20325a200d1500c0320 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 264052526 1250 264051276 264051299
    0x822030201060e0f07080c070204200d0b0a060509041e0509030a020606010e060307050336060105040c0801030206030c070501090f051608060a0c03020702040204031a0a091a0403050909040309 84
    0x8260b07011811350310b03040100d42030380001c0182d04200c0d0500403543c0c1c3d0000340001400303071084800c59080798844092208520384a0001080405500101400a214402e0402403551907910030000032580810048215182940c40f050f183c0790314400c1c00302008540c0000b4411560f08403203802c059400042c192050700c0e010000564025424a41018209801d0001c240270b0b00010300483c05001e408004101c10601c60306100448108540507400c078441c46500300d520406180c8075034101f40c00356100106460901d0300496008041585600300580d20b50b5007803002661004091003d041d8090110703c000074028001e070043c5900440c44102060a2810664242500b9171012034034801e46140410810346c02264056210300201e000280001e2a03403001c1c1c001e480b4050300258440c1c0300003004010441000d0003108491800400c0d401560fa80c42e8181040b60300d05c00e800b400104d0082c04002c44c001101c2c0c1c426030701c50310a2800d28101050f410100c0c0c0d045805503000c07000b0918101d03082c4460007541 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 264053776 1250 264052526 264052531
    0x31051903120618111b0601090e01050c030127062402010506090a05100b0304120f0503090a0807030905040219030f02070804090c140c03090906010507120822030201060e 74
    0x400d0100040740c40c00031a42100204001d00480d0242c44a41d00715040d9074900c15144180a800103600b41c00d02d0001c00a600c46c202400340e03919540c034028241002c0b00051003424891a840366540d4603617400c161450701091a1030310168050008410141e81d140da0301d00421000301031048401000e211048030300b8108071403c400c25411a0300d40320030007002e6505e0b000701a4004d007150070001129151401420000b0079107410140480d0400000d000030400c41054554041d0b0b840da841d0a98010022002c41d490f02c4140c0d07407200958041c2c942003001c2020310005082e820310a0a041e01115501c10110707059810404110300800007960a030541e0f40e030940a5078500c14851a42149404407a9841c464940101c2c0100c400d09039446452450b101c1c0100c080d51020717007224101d1600c8858411902d0790300d0340110741c10f038000d4842d41c020466950152054401d00c95200031a0655501140c0c0111405c46004100c40401c0805440344140841090340310002d403800bd90020617680c0c203000701c003881318001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 264055026 1250 264053776 264053807
    0x615020c0f0d020904020906040615170a050f01152003070203060106020c0a091802040212011502070302101d152203080306090403030e0106150e030631051903 70
    0x499207082c0c01030380c444544075030142d411200081c0c103031a410045070080242d5000030486000382809404501d0b002a9009105080003d115680d42e030b90010300710a0b904281cae4840304815128005100c1001031100d590065011842c0001440e50041c0b54694161034031007004c807640d040001d01c902941401c1c400d650152089000900001d0150804988401482c0c0304480e07100e80e451030b403c4a060b02010340c00650f283c00400030f40d1102c0c7d140046030340c0c0b00c00c207115142c048400c031030f042c0281500100f42d10044170f4008042030402040d88809442030740d8201400714100c00002003118050b91130141002c07546080c0c040d6940c075010b01105404100480c0b42c900103180b144250104005407213441207030341c4404c013070782d40140a8a41e0f20307043d00030f0951922764140035401d01c02c2c04200c00090b0014081000030998402c40001d801c0c1d000c0c0758940f02c040d5070034262100b01441c402e000f6164000c20385400c3e220040c6040d48003056450740e42c10440d2041515a02402d58648041071603440140089003122 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 264056276 1250 264055026 264055039
    0xf050f070206250e01020102070c030b060a0e040308040f031b06020a110703080d021c0e010f050c0a0f030e1204030b011e0810110c03030a05071d030a02090402040615020c0f 76
    0x80050f69103000400110140c04105614400110030f901c00c1d0142da030455409050003010503240d19022041260440d0f034540613800340c2c000012040f0150304034901951b0135454503e2a503d45443c1c00015403124002942444507003040460710011351610703102214003131000141c03142054400182011908103466449600c0360500344041440e1600b01c4203c0d801c0342e500140d40e43c00e071080c2d14506055802404080614000c40e82d601c211040d002640519590507040045548500c40354500c0c0c01101718100014000c0c10510081901a5000018030000b01c1c3c201c41c8407030104020580d0700e40c0241c1007121042c4400004000c240c3c0c181c041d00c0c900c060000c1c0d404e40e641d0300f4402002d986840030240805042e071101071300503040f0801d404450210f00d5110559940c2d140251060000c2c01050700c010000401241031701d52203402e00c800020f10a0002009410f00c025032381c003000b103081d01c0179100b6039003c0d0b81c07180001a040441e400c0c421503542650050614880e141007044200c0c2c0c01031460b41c5c0600f0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 264057526 1250 264056276 264056311
    0x1c060503010b150c0c030d02010f06060302030423030c0a060b04060f0e0a0c0905041a01020705040621111206070206060d110118090606271a03040302010f050f070206 73
    0x40d0b40300c0003c1045010502060744445200080034070700903a0000c800e40502402e40584422039041d0080d54401000200030304c40c196407480708500320301c002ca1b406400031014041181e41051403410080c140002d41d81101d041c4442d0840301e9003003070b805100071107855a6800d0a20714a0a00c7e0003003600800ba11940c0f0204a494203260725955903004180d900035641d00e48150294a003d0781c80c1d00c018203009441004004901040f507500e404031111298098131840800141038506405050241ca6424440006800c0b14032103005035540080340842d41c02500720514030a90310350340103403103011807400010070b6242407095001c1d00701080a858103005a110b940f000f008104800071440e4003400a2800e0301d8000803c0280d945010724540180a12130306050000880b01d0307209400e000c520140035802c001c04401c40f9480801c6050324403801c1c0c0046240351074a510180c100000d55480f502900021400503129200c2000301d800c101c5420240c02400b07000d0040407581080345503800458001444501c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 264058776 1250 264057526 264057529
    0x21309030f050d090813080105130201230403020402030411090c0a0c030e18010e090706021603060c050c0a03020a060b030313050910081609140411010e151c060503010b 74
    0x39010030303800400d10100281c441c5880c00303d1340c082c01c0c074070341c0041ea41900d0758140b00804404e50010301c558155503090a007c02d4982280d05088400700307905031114403507400040002c1c2c0003041c0340308040c2031800c4103200010246e200c3e400194407662041203016050140340042040b04080540020490300051114910058000031413203109509800c0012003006110000f0b040c01d14000500329000c20080c00020701c0208403008a4018420001940c0c007198444030100d0381c7e03628490340c0d80d8912500c02e104201058540c1c0c8038100316121403030b00760328100016200910340540ca500071401a0b0080100105100703031031081801c40070f030440141d840c2400340360115400411600907140725100800c00324000d0305901c442035008041144c1503c0341018024081c1564141034440c4035169030402e41c0803000e001c117030003c1d1072113583e008024245104407034004540c5188640c02c0181c104007141c1160f41c030f81d502080902521403000749150035181c0c586030f00005580356503000c140641c0c10b1040c4030b03680c3e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 264060026 1250 264058776 264058787
    0x8060c07080310090903020109030206011409180f16060201060902030c030a0b0319050a0b010602011b0302030403051b0d11031c150f080303040b15090606131a0702130903 75
    0xc0a41160900380c8a86402c0d00302040000796610080280b4a07109000c01003540641040f22824020b809071902aa40c0c0d03400a2410000c800100b41e0041c510000940075143c2c0c04c1c49003410202c60400c69900844042070f141c58803452000d08403041050040422100e0303424001d11001e801605420742c01c5040c40751581c2050302028144400d2580c40f1040300391300751410044041c3ca00403041e140c202c22002030034081e0312401c1e0001e044d29491806000071803214014001c0729041007912032024030b05e5416400841c020340021300100c041000411001103201000682641c001c50b003440a0955122560000780030003080702c200c00c5040d001448080010b41e50300420b4247c0d0300c03800f200407600d0550458040b0441005410131f02c031001003004046818080003010350302c0345102e2444ac48064840404c0c00384205900c65900798824203c00005500341002c00140114480111796800641c0c1c6980440e07580d0a0601c090303810748500825507505503c0c04001801281700005c408000403219038a00810 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 264061276 1250 264060026 264060037
    0xc03030f01081c12090c0f0303090b070507031b0306060e0114042901090e1303020d021b0112020705060106030b0a0f0e07050c070e0f0403031d0c04050703020904110c0708060c 77
    0x9008940d0052400404150000300c174803070740155940085030711071039080301480c61400140e0004200e4500820182401404c1354201d83d003101c020404146141da030ba011907540446161201c03991106c000000400c14000e9201401c0403c202d01c10345d40c10407650284005803440301e94421420034500000580c2da06908049000300c5912076103414008200580d1030752303242c0e403019440c5a400020404c07600c90181c2e50600311807195007611100d01403044203e0341c0b074480340d125022410041032401e0031036000704103214045088090140c10601d045d04c4840c2401800d03408076000c00e031600c2c0190b21624110030014050401030000d00c1d051410700302414440c400007070114080c804001040340344c1c1c42003000740c0f100030258821882513610704040c90380059041900d084000c28241082c100065104540c0490541c401c3c000600613084902c0410000e40030203401c10003070603800c014071344c82c5807214020743c1e095000740b4803074940d03031041d117036040d8607000c41c40d88001d115070492010b2095440c0002c045030b8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 264062526 1250 264061276 264061333
    0x20307020a090c020111160b1f050906010c1e050705182d100f0f050915041b08091606120b1305151201020915031003080c03030f0108 59
    0x1502003143c003041e4010000411000d25000c03000c5402d1300120b01c101c2c05044010700c80d020100298451000307490708010082c0078183c2c44041d0940900241c20320b100c03042e030701142c14902040c1d000002c1d26410ba04440c642112451200320458607000d0001c04c010071030040005075040196010303000c0c0000e040f82405841509542000002c0b28502c4071300d5800348860900c952041001820406503856022200e44500611034141c0e800000e28110400e1118084031005007219009956503003030700300e1428441e841250f001e566507082030585880740d5182c030b03e46a41601e441101d4200407408902c0c1c190070b00300e441090081003c05000d075503804081c001c0e650400d108080b42d5070301c084c00014040c00c001070030031202034600b01c10032100c5c42c84032580242e26542941c2c00010100c17940c02d550709070302c074241d000d42d040303921402d0061450700080e000b503038015030070520000e0700391312030b50b034007020364084552910198004824480d9a1800e203a0300346c01024038000509581d000c4001880e8503401280c03000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 264063776 1250 264062526 264062531
    0xf1a07120902120d0909050109020412230607030f0b10020a0201050a2d0e180606070203100c030b0a060908150c0919090e06010b0301050d05031605010209040c020307020a09 76
    0x25400c6441d455009080c084140d41550720b803584c0d07200e0003000c20a161054035103a45c02c0c04000187d10320303540308517401c0d14549500070300350a031141c860150007050b210b51450300006045024804000c280111800782203a50340108100032207200003410340b00450300d0107100e02c42c081c00d510ba0441e00044c288154550a0800d10340f280a00501581e03005102c0c41c00300030a01401001c2c1454001c0020034000c114555110720002c81000010b00c2f80140e110075000580c6400b00380410000d2030604084d003039452000301200c01c1030420010550503100c100e10080e01080c2c039565541098902504d0300c5d009010300c0c1c540441028500311155960b03009000c1412005140103000c071303042c452440304590200b05c0c0906003518a103e40d480e040b8101c1000d00c1241079143c43c0820754161103501044403130485003807290702400c603401c19007081100101c045d011106440704102d400740036040c0082482c1c415010310001600c4540b5030f0180070586041d0500107045400820079003006075038082661040e03440b0b00000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 264065026 1250 264063776 264063791
    0x1031a0a060c0f0501021911150c1308030d09020414090d03090201110609101b080115020304081204050f04020903030a033b011401060906080a0b0a030f1a0712 70
    0x2000e03d404608030064502d50001410394541d14540d4106a108181c030f56030407004a000369000ea880301d214100742c16103414980e010595848140001d020007010141d4580403c3d07655a64940c0343d640b20701c0810b4061520b50b5548000c0d03107010f10403040f14440002d1a043e036441d100080039102c201000302d00c405d00d42e072520700c00d0969105191008400200c4021074445d81000c0c0c04040e03654041203d0100b000d400c04072841c8141e45011707030310503020101d88c407481a640d08102c1800711305101d140141003188418000000c2285040140182071005418481e64643c101002d0040356411045c07030320f000710300400c5040400c0e1000402c480381c000036440c3c00121080400c12031340101c0e01507148114045080450400b40307001c000507100020380d8035802042580614500344e0803035482486020085040503108015081c05008110b43c40b040780540041c1154070b60000551680f0141c0007a20764041c0c41c003150782080030000c4200c4800710011801c27200380c500b12100070200b1820510018109444482c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 264066276 1250 264065026 264065033
    0x426060c0f070321020d1a010f0c15020d110a021c0f110708010c020c030606090106090e0903130b0903060a09080f07060603020d08090915130c1e0e01031a0a060c 71
    0x2910401c0c010403131030941daa40c2000c000b92000d400b032103800d8900a00083c000c82855030042e03400134403001ea15190004508880e855100030581d004441004c059002c104030481000180304604c0c8084000060503155420164001e14040060a0301040e803e512030030407000680001505803011000d25112640c580559005402c10f42103500102d503540c240840c3c9024560049807422241209070111825940c54004010b6040001e115180c0401d030540300c14000c1a510301340b0164401001e504a070710b0a03400540a0080c030032181d000706950304010031640851303d07007407201540010140500303001400407a120050148600040082a010001410401c002d2075400c40c1000710780051090038107142504024160b80d100503000f0703110f042e5840006000d000408415050bd101c0078041e40744009001c10f04400500c60994103500b84000070792403d00c00301401c0b5078007512219276564481c0c1803c001d0005030a07588000000401304c09441c1c440c46850f103a000300c2c08101d0b406071415000d80d0b5144e04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 264067526 1250 264066276 264066317
    0x9010207020d030306210b060613030c0b1b010b0f011d0301020301181803021009031704030201060e060411090f060f130e010b031512030426060c0f0703 67
    0x500094020b000b402d01c40060540651010f0304551b664043d6440700e0903540d001c00200484210000d020a2904020440d2800c00401401480c00b1500701198031a4803a1110030050701d0710b9009200e01080003a016801e1136106004640780b041902c02400a0122500043c5003400405000b504002d225183d10b0902520700e44060403211003d0300841d036035612100c0078412125448100102c203070400c49070403404880da241021640ea0180d000d04a0b155104180c2c001820400030241d080041800c102c04201000303000850150380310783c0002503694500303103000c0d9444800070100c51196141c205080d0f241d9280c4812070300e400300c045864003038200407000041c2440c050a804101c005c0000b10b0003200005086046500340c800c1d030719140503240c1e65101180128402102c18061450f202d0000f030b001070501d2621101c60003030441c180d134101a03e88403802c0d0b8078943c0d150707920030805490b4101c1c00c503150113005042e00b00c480c1407081482c3c8034800500c0d02461103402e800500b008294810070508a0301340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 264068776 1250 264067526 264067537
    0x31c0306091d070509090d12020409020a020f0105070e03190c08010501030804030b0c0708040909030c05100212100302010504150c05010f02090907090e01061101020702040c02241e090102 82
    0xaa0040002c1c4a90a0350101c5030380401454140910915501140300c0c0b50012105100b0000031005142090060500325011405503900700c04040d020f000c0462014402e002810b684012540180100207880c4022825500b0180031182840162403040c3c0721507d000c00c4200420004800708040c2d8901450700140b14125640701030025440d1000100800420000400880303010340c100a2080d02d60300b072140b19a124444000b06000310030402005052081c0e0000c0178098068144182550180e480d0340e41850030982e2129402603000441400d410b8212000c5a008400c01d015a41058156030000e080741c4120301481884207858842c0c444083d00ca0700d490043c15030301600134800c10441d5030b20180a9000300100a2080c0b6002c00042c40f11032081903084112440420070041d0ba074680700302515081c80c0200343c91a595001c100c1c00d409070300c660007040314010032540203003100641904d50b503220b00d0200311a100da52058100340b248441190704c0300c8460300d00d2441d888150b5100c140b1418020300c60b1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 264070026 1250 264068776 264068789
    0x40b0102030c0601030b070f1103160f150204081002040b0f1e070c0e010501030915020a031808090a0605070c0311010903210801090b0a031e02122505031c0306 70
    0xf20000802000340f00c2d042c460150391652074042c25101082c10a4407810b04003541043c15503c1448401448600300c80c04c803003800e024104154180780d01e0740300c4040c20480e404045003e2a00083c0801c107034441000110b8907246400303401c50400d030801001200702d2148002502080401040c241d8612071a0303400740c030040d003d0111704d030303587c40142c5400340180280f031003100036400a890000515502a0103400700e001d0b81f041d1005c0303207510061003040c000c1d08262564820103540f20a100c0241c1d10017002086440d0181419239107601e100e108200085589421100030000c00344803510000700d02c6034001c019203501090003251900f490300100ca0900355540080c1010034018016500310414209050850f6496a6030300603603038950801c0001c2d24101ca0072903402c003044000400218911040c03c0c00f4441c40a05101107005907a00005c2e40b168a0b100c00b00398681200c40b460044590102c22505200500285800528074020000717841c1c10000d8545d4810803820803040440e01d201b507000f0b030040c004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 264071276 1250 264070026 264070033
    0x141203010b130b1605070608010e0403030c0e030318030105060102010b011b0312020708070c050108091b0f06040303180608100302040e0f010f1d03070c120303420b0405040b0102030c 80
    0x1070026604011880400641c1c440c00303890000700d0080d100da9488d6060364111401c0c507031036880b41d907003c50043c1800e404440030000c400d600248160381c240020304054800e001c0c540703c00710b8404101070031500f005d440b150541e8075014240003541d03040748424199003803e0b400ea843d182110300381907590b6800c0d0061220700070f200040130030401410102070101c090180005920507912400190f50701c0c08260f0b56101c059000c500c410041c074180c0c0d501c8281d00b036000341c00c0291050354400801c2a6400581040713003c158007560308640c010190202e0340083c28249400f010600f4000d44030304c0a0492400080c0c00f513510341d0346c06180544200404001c0c5c0c80c054008220308003499114000918915050141c00b0094803d510780d040c10000544141940140300b07181d280746070080c0100d108120394000c40c00d150f00d41c2d18850031400e404001001c840e4800d8800303012080c00038002c0101d030002d24800c0d401e41160510a12641d0644001c0c1c5059071400c1d100041c01030f0b00140103038070314045c0c004100c44510 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 264072526 1250 264071276 264071287
    0x150b090c0309010c080f06130e030d020307021c0e130b0a0b031005150318100504060515010201150501030b120304080307110d0b070f141303141203010b130b 69
    0xd548500461040d400c1400800c003400d40c8000440740054161070100180510101080341842c10480a0031011103424000030018298230041d400d5800001b0310002c40b80d40403040028907038051154056191089040d601e869001d490041d1440c9c0c105010f02d0300419a80d41d40000781c0e6041c1c0d0004982000007816003801710354078449038445138011542800324044841300080d0360b060032050f0000107900884042e085a072031101c07850801a0b008400c50b42440380c84115840d20340e5600c2140d01650040307402060380c0c40d00d202465840784c4411441c90441e85450001c0603046450420201030300e50900c1c01213901c0d51060006040f060320f5010010032404000b034000340e0400c0000007807841078419410701007074108040402c0040d4010740f07006014000f0b17540000d07001510070140e090014080d820416907032284801400070311b41144944079121b4004034001c0c001e0205010204400b407d00800502d80010b04e0b1030180f210340010310800201c1e000210b259083d00c000c04e0541c101401080c0d001c0303921755 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 264073776 1250 264072526 264072541
    0xf030321021615060b0412020619050301140a06021e01020f0a1d04020c120906120708060a0f15030e0307020907021f0c090605070201030b190608011d04150b09 70
    0x381d642d014125a806640d60540800300518007030740d000c42d030700284154105403404801035848401e1f03120407030b07102c4000c02c40cac0c14095586528003000750307000e9039400b600d81d03044c4900c0d070113000c00340400c0314030500307920a08010003580000c07901e03072002410640300d000340103295245029008511090007180c070b000c140712411030350001402805400c1c00c5200c1d8044000d0f9400d20040344186a021310280d0045001010800c102c1c200034411142d005d03006a11b800c8003400024007900c1c0c292603890024000a00340300c003528003080d954000d4910345000002c841d25020424600314200c03c03a1106042d2114500c0020801c1403096a0900d5000780c194401881c101d04000e4640210502030f6403803040914a00c0102c03001442010305502d0103803640d882c4907040600907507a035080740004038101600d4003038840c2c41e5200c1c05500758251b01c0c0659000346090901c080900a90070507042034540e0145511066240c21210740460b40168005aa010807001d2078410040035204258000b60030202450511400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 264075026 1250 264073776 264073807
    0x907020a0308060904080a0f0c080f040602241602030403150506131505090606070501090b06041d1504050f0303010f0303091e0317160506090708070f03032102 70
    0x12510a5480c1c066640d649000c0086604d4180c17400b500b2041c0520800d84a0b44c010148020ba089960808480400180e55000c001d680300e0f10400d8860503000c2340401020390100003459982c0300c203e0b040720798180e40048002000320000c040c1009085110b202a038294004d10840d8040c40c2c1008000481c010046c205001802003a50050b005403070074941984040c00c14843c1c4440803c1d110392072481e0078642000c1100090020307000540c4800104070650000c0c2c0c0911442281c10b1242030358000602c0e00004010071038800c580d150f06404681c4d44506888030011a021807500f600300030aa150342c445080952900e00c6000c12541c551200000209404241d6801781c4100d0744250741303644a4503101c0443c80c0c401a10416050400c900180050001900a0f500107010f0400c10000e1801c00b07221006070075844001400580322034001100340820044148011005410644020801c103032501100e5109261180b20180810131002e408149ca145042c0c0c038101481d824400554a85000302c0e070345541c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 264076276 1250 264075026 264075043
    0x609060c0f021c0815100201050a060915030209070302120901060816180f0b0312120604020316030e030d0533011b050c060a080910050c160201020c090702 68
    0x441c003401091810184002054030400104114501c1d02c20843c54041c0c80081014003442c107040c40f210484080e5449141c1ca103030080c0c5140e40007013568140394130064102c030303041d4005803c0181000200840603003152150404c8039415902400c4559840c04114004c0c083e000b031454007105640c0030300800c420150094815500c468056030400b01d1000741100c012002c600c180200e11480f83c020348090012944400c0c03040040f504041f41401810000a06000d046103910b0341181010901c05459880307101601da0040c002e440462450900404101c03400384820b02d000101038883c1d07140c8000680610075944114181c01c1c003400103080202d5200c8c505030610100d9000c807500c003080d100d03030726040d02610b10764841d040c2c45000e90142400305d04841d182d0f00000940b030a02c21805441c40700d450301d100511030306c44182e5407591241043c5d000c103820444004107490110342824203003c40690440112803401007255481107a4540302d10041c2d060083c1c601d001c90340010104100040242c0101e030615 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 264077526 1250 264076276 264076301
    0x210e03030103140a0c050d030e04060816050301090c05090403051309090308070e0108070509150f0306120a33060e16020109080a030c0504080708160e06010c020418060906 75
    0x8185100b443c01035031000307030030009000f07000d03c44020007042c1414132894003101c0c0030b441d0140c00400000c0c041420b6803c240d00442d11944002040c0d0012081c01454a0103864200c00a101e80460b0342c6501c0d1002c2d1060090030302c40d00600000c41c08150003902120003440c0000700700304506030760300020401800f07070545c140e020502000002d82440c1c450801e040e103c0005840744101034450410884030754000c511078035008180c0d5903001018906613006040030854218034503030307680703403a1040c071428002030f41a464135a413042c2031400000c3c41d0b040049140010306080203005044000c2c8017400300c0240c0c42e9074115980b8041c0040b8400d090442d00ba03105040c0301c00603082e01800180101d088a803201c5011340f00030b07030520000d0032043c865080001e1403002403400c6414151509400ea080a805070320085140d0b01011103e410030102c105180f00400c5c1c003508480c028901080041c010080054009118603a1040d84d90b501c401110442501103412040c1000350503814500103001782282e44100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 264078776 1250 264077526 264077543
    0x304030f0507200301020702040e06060f060304081213020405090d1e09030b06040b030d0c0b07080603030901031d0703030302030a060509090a12021c1e0801050a06210e03030103 78
    0x8440301e00030700440d410746a010040e420000b4070002d0104031500a50503541d41550200800e00160303545014042c08904200c2c040c1c0000c1c00c1c09010000c001860310100c034050b00041c000c000106801405503044d00761014056071056035422030501c002d8001d20300003544645440d062140354600090b40001040d40ca480d80442e5075107481d1003001d405507400c05080040c50385101800000d43c0d9090150708003001600104948050100080c10000204201c80024035040029820f00c015049071a800940c5801c100d2914141080030a48901c01e100600b03041c1500c64080d4001e039014104610600c409281c252051241c482c900140a5030007900c04509840c204900801c003031074940d40f0103010740c00d0f50000700244034156a500424110070b9184600350f0041000a580e902441d9245100020307903a61010490701600c0f206174180c81705011150700300400100140b00a48a0004a000390380c0b403803c02104034003ea810340101910501d0320050850700b4076601031038015001024606891051204 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 264080026 1250 264078776 264078797
    0x905070906080c03120f09150c0604050f1522150518011401080601290d020306011106010302010801121403040303020f060c0708030c0a050c0615040606084503030403 73
    0x2051150058520a61000078104030160191070048501c2c42c230043c58019150070a004e00c0c403214108141140c042d14207800083e016540c0303500500c1243c6002200c1c070b84c0c410040c14004100c0c0094140740c04c581c419100d0600c002014418000d0458200d40c1004900740071a24244060364100450452500d00560901000b40350f502a40b20125042e81c030000000d0415070700c1c000c0702880c8030b006506482504003078000c2c044078203c181d6004088040f0b01c1c25015a81703040000c001800f00b800c4404d4130a0310380202d0010300050b0b038460312284c111103905103103a0321421181480b003010492551007554070701c03001500004154022075050b4400311408140e440e681d0340c50011486520031020000d001c544200005044d0f401041c000d40040022468201d083c058040c900d14900141680c3c14060402c054024080d2840d260146101400c0d0a2030080100c0c10801c040d5004000d108844400ca8880f001480da0100f100d039605000403540d28401301c090303802c07a440c601e8076a0700588080d80004c040075107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 264081276 1250 264080026 264080053
    0x30e100605030c0612060f19030804140d020d0b0c1303050d02060c04181a04180605091906090f0215030702010c0c02010c02041e02040b040e06010201090b01090905070906080c03 78
    0x151005141c49445c5034400303a41d09002c001d520244c00040035444014a46010b0003100c0754400d05020710300c10881d882c1c1d941e00303101d14000d010560b060128418011501c0703000041e01c0300e844d17415490790700c040c48916540781d041480c036050040041189040d4640d203400003d00c100001c10001d0200780b502a40ca440c0c03034045800280344030710b01034100c0c1801c0144810035890b1a030782c480d000b130100d01141e2010300d07040c00b00010191070945a012202036000c0366180d0070321266114054101c2e0300b1400812107041c030405454134606151201a00795507642d45c082003400611080350020315401406403000c5881e071240c0441c290030940c5c0c21001586030450944425001e8180c8502d903075016182c0300030844050303081002902c610750380342d5001c00c00f1404c0381c0c44143d80ca002810181240320121030700c81c0d06040e850100008000c0c2014111782c10300303562902181c840d65019041d070f4644180466640458100b40c3c1c5000c1c481d600403520035241410000741c000d000704059800010490039120003d05000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 264082526 1250 264081276 264081289
    0x10e06010801080718020f0412050c010504080c0f04090f031214010f03080a03060b030106030609392d0e0d08041e0308120907120c03020d0201030e100605030c 70
    0x54405140d10048007400117040d041d20340094034681010251816140144800b2581c00c264031980718104614000c1d001c0040038017a18080c2802072800e241841d1810745203640d54803100c02140d009400420494940d0349664101d0750030150040c5602100c6422454020201040b001e402e07030039030b480e14015618054a104013141210080903032100941e06640f5060619405000d0740801d1658800001611404d00300241d40204a9903d0004000d407a260031341068907260300c10441c0010b6005020354802919101d48403142081e1b0110465800348010159042560299520b25000700d0325079400c400e62003003c208542680a0707407810703c41141c0c02e0500602c00c2c01550000c20740801808140290f04160707501c0000112020381c1402c00e16586e4840b40116448009a4800d8046400412954140c1040f0200080124450001c8960b903661070700303034100703c0da400001e100781100303040c080c1560320a41082c050348410300c007550001e04c1844402001000140304985c0a07000b803044c4006c0d42c1c039120303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 264083776 1250 264082526 264082529
    0x60e0408070b0a150e0c1210050301060e13060b180406020d140912031302060706020a0305010e010b0904020304020a030614090d0e01021504170f04051c0807030c06060914010e06010801 81
    0xb02404a1142c03d18910340d0000c5c80040052400d41018442401c880041c107004500035034064102c00080b038142010301d0300f96680ba401400781599010f09203c99100c40352100740440790081000280b081c200d4001980d074462025981c1d00d10a1000240414445103500030000c10b2582e070703403c124100c45042020181641281c8500e070720340054442e14080400000103560089a41f8080400e908259001400300d8002d6034060b510103a0101e4550003040d09840380c83d01601990762568400c0d0314101d520340d640e01c120f59046020b20f03000b0000c1011503c4800c600350140da801002800302500c901440c1c540d0190840303040c4000d1040c002d0a1584500451600c205110103a0140c0740940103002d604007103a0b4041c0003101c4954a150003c1d060040810144c80088034446030555500e207410100300304102c14409003280d20050a805200003800203048940a80e411b080810041126003069030062103140d00c580109400c1c411041c09241c0c1e00c0150314165403042d903001318251901001110100002d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 264085026 1250 264083776 264083801
    0x210108070e06010c24020403060209031b0904080f09100e0901090506010c1b03020301021b1203010608010e100305070f03051614130b1c1101031407030e01060e0408070b0a 75
    0xc240c5003000f0071038200c0384c3d44401c02d441e01900603d440e170300b20080c201c0e4400c0d8420385104d41e01103204105840c042c04090044c007005d2211415000c1008006044000058402040c40d0700000d814144514240300ba500d2450009060301803021079031201500c5d00c004104c07180d00c103e059000104905100e8811540210410b0390b8007014000f0a41c0d9070002c021005008002c40d4070b400742c0000c016902400280900d03400040c1701a00d03403146e4903080e46083c10001400414907030500040c801c16a104000e1811a441c1a00c0c1090030b0b04ca9080d4a00d0551365904050000c2c011207201242c0c0c0a00c0340a80c9003102d00ca84100c514102881c180d282c0440c080e4002d150094640130300c100001c3c80c04503a074110480c0100d2000074010807400004020840380c546032420b03032104242c0d000c24401c4034074282042c0c2d0020308080c45a5411070484035802c0d00014800414142e0b40c1407104141c04003580041c019141d40e112000c0541841e04000d9559040100101c4291680b078000803280b20003030003580e101401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 264086276 1250 264085026 264085037
    0x60602031902070801020f0403170f1c090209010b041e121103070905040507030c09090c0303200a0515091501091a130507080c07170c03210108070e0601 67
    0x10111074020091040c400c40004500c9401c4011918103420301c002c002d4500300b020391956940c45c0d403602c0011170004c514541c842c41402c0c4040d8801010100803103101c031058400b030b01d20721002100207030010440c03510040d40220040b000401d19185420050083e1b40c08013107105299442494120801e000c180070300121014180c1d603d030002a03402075104d01d4400002c3c280c411450720b6070784130070440e2012181034071540e0081204005102c8110800009401c078800140450200d039290602c0140701032000404100c400344089154000070030116100704203071016210780c2041c90400c1c03070782c4003441d0300308070403030390900010039002540064164600c031003252401c10240c0ca08401100100b82000780f000103c80182d06c0b185861352104400060a4401e03840010b03c1d00746803400401070311004040c1d2160030000c11400d00800c0c208281e00243c0543c000081d40e4914000062506600820310145402d030351140058620100c1e20b50102c4c140d415000807038084c41c4d95040131403c605d00903624540401c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 264087526 1250 264086276 264086287
    0xd020c0307140420180f010c021804080f18031b10031e0e01020d0c1b0209060f0406080d08100b1602010908070b070c05030307020619090801050411040f06060203 71
    0x1025003040440702c0c00d04280e011000142100002141d010b0201755208a04a00c5264014035000c000149444428640802c0c01c20103a808a50609629522010000744000010f0100091070040710460210014045d4440c008071080508240a0b88001c034464018038030051000d0810802c208512500100f4a60481a04120075001801204003884556001c41d00b0340c141a10f8a010303802440b6100800142c1d03442c01b0b41c1c014030485030386402240c20400e0101c61249003003090608541c01640481d0042d441d5260400081ea0903507001c896a5000340c00c00074005040d01000c41c4844042c04a61281c0e0041d035100201c000c010039440c096405100c03810700000e144100c1401284100318410306040c1c81c0300380c0300c840303031842e2580b544d02031003c05500050440802108480c01c1c0020f110a07030055040a03413030b40c00a1028011441c424030740700102c4240400ca0761042c20703040c0080c10254020041030500c1e00740745c0f45444451040900460174001011101d002510500c000c8807000e41c003079800c15 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 264088776 1250 264087526 264087529
    0x2010507060b060307090305060703050405070b09180a1506020a0b040f0515040503030108070b070803010603020f040f08060403112b090e0f15010801060c060506210d020c030714 78
    0x150404403040d41c5856a402c0524000d495150007940a0f5001c1e40390070f0007103840e52521618201c4003c1c00c410816082070207120001d18009041000d881c0511403040e06d42928502051420329081c880504030310114083c441700c018103512851170704c00110b81072a800ca89914090b40d448200d0900140548404400600800c44106a40c0300e40c034890f4007680d00d100301c1c0700c0000c0021901500c00365243d41000004102110040041c2c0c2c0042c038240e0000390514510382c0351142e076400140700b48000e01d034002925803c2951910210b0300545218810120540d884115560342c070001102c01b1030100b80700305010010008002840c036a0703d40c0f80210081020111004640440301030850b08040c420143c0b00030542124071002e491044140401041e074a01e000d04040b070780c2148400056042c00380c1040140015540200400d01c0d280d0400c90110b82c54407200c0c0466807289182030044003a800c518184190000c020484210307205096007101e40d071000078002c040d16541c5e180b0408003041c010712100103d070b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 264090026 1250 264088776 264088787
    0x80405090c0702090403020c12070515030711030d02090406060806090402040902031e15010603020705030301121509112e0309050a020405010315230703020c0f07090608190f0201 78
    0x81002000078506012035030b408107a18a9055034200c0141e080b4115031411402c00890320b50003c2007030b03002840c000e8548004902c0211484140e001d101d0800000141181e000713410114810940004032640c1c1c40300c02250768025082410000d10990624800041a80c400c601183c011013008000c1106501c0d02c2e800c200c002c0000400490b0140145070001001c242420130b08132100b511070002c4d004000b6141401c05c22868160450740a040c41845a1408600c0000c240c90540d61002042407010a031030509080554452140c041400d0420102c0c4003008003900d268000e2a40540e540001210000c0c0b0080c810080c20000d446030703569080c0b54110140c482e41040d00000e00a400361030782c0b4812500030505a440c242c005403900010b20700c9116481300d091040b121a040c40c0c11058101c40b2002c048600e184401410010402d9004110001402018441c40301700400d60400c68022984d40c0740060081c101901c5000240d02030000ca2000c4014070040000919900084200c0302281a41c0150741 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 264091276 1250 264090026 264090031
    0x160206040c2c10090506060c060718031b1e03020f0d06110403080c1c080115050c0d02240402030a021c0602071a160e06030a0e0a08130803040308040509 67
    0x10b00c00c044082d48400d00c0e210004040c000c40100211005250a00d684001030740c00c0a48894000d100403c502a85104041403864100d122490030800300606c0a040c03100c40d503025040030b40300e2249a1240c003103c00c0c4c40c41c0c000007111b160500d04400e90200c04440d40101c8810701c8080d400144110354105549842040c1143c481c0c441c0400203100022003240304e000b41c00c542c004441410340010007401e000341c00c100c1c4001400c041502c45009008050008080302818070170681c2580c46004841c0500c1d0043d010303202524441c03002ca0b261181e021900950700c0000d0700c0c07140a01030100c10f00300210900304000c030b442150060001c1c101d0000a034281f01c001c8628a101d4201030504449410016119000400d00035019442c0280998481d0042020900c0d0242c032400f8000c03040d40c0c1e860840780e0400300d0b0081d004070441702070b070b01ca40c1c0e5070903410090702c0040c455078814050f901101e403c01980341c002d88045130361121f840c0c10581e124800b0b2580c900c16400007500070b10b0144400c000600d4001030840e0b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 264092526 1250 264091276 264091319
    0xd06060e060c0d03052d1b0319092901060f020d0504050d110d0506040b1006120903030b03072705130f05070f0308120606182107030803160206040c 65
    0x140c007680c036218081c04820100e1400d0b031140b412001d110b46440f00c07e01e100080c8410b0069a855810420a0600d0310700c003a0ba900124283c03103580790824841e5040c501d40c4420f0b0a00744000031b5588150a520039032000340500c42c085007207200c1040106100144041002455481e41481c080c205001c2081150043c0e404a0714071000c032080d400c0e181c88401100c65114401d0005240710700b401c1c81c00208100d4020100c2e1b012102400d000c001869106150203c0c08040d84e800184455803070034114050302588480070381503c584ca100040f5031080e88d52036007070649104046112465000500c0c025100281c0b0210304500100450703d021079031711480001c1603441001103d000782d6480450249181c00f980c0107807042d00d0042001032980125943c3c0c5603000008440c050314206050502842c940d4003441114001c4001500480003c141c4500164440c1140c034212a01a90350345040c1c0c5065000311001580003511209843e5028000900c46010b141d20000401c0c1803400e00c4003010044400000c1d08 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 264093776 1250 264092526 264092551
    0x2030709053f10150b03100807120614010e0609101a09040c0201060f0603090c05060d150e060603160e100201021806040b04050409020310020d06060e060c0d0305 71
    0x4680300c248050019800c98050b02a100c01c80d000024103900702007035414070b149103030b051184140e03a0f100100ba40209031401141090740b03e072900e6925000c00032141d00700d904688681c410100303100741126a03802070107110b01070502c030080c4d103034400008022081c403460f8290202c140c0030170748a1825003400c03540118440000000d46581d4012a640200c40c5c03c807110f00d43c6800a1000600d040500030101100c545000a2004500d00308096081e507500f0702c580001c0654800c4404100300425965400505004000a840d504200350140c014980240e603204104400780c0001106028900a40d00c43c0ba4010031140c2140d80b120800840074402d07541081c10010083c1000d03540385e5650144095010056000580b034542b4440701c030700e88203141c0030345621035072040c00104480001070f0116000c0e14010740303021a002c04c451011034a8071141000340351047c2d00101c1c550300b01212325804181280c0f403a07a101c42081d5107240c24401503128901d5128001d40280c9840d54a0354001e0700196000b400e222400c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 264095026 1250 264093776 264093829
    0x709020a110712140a05100509010204090e1b1f14070b07020a050708121c060302090403080a050f01050105090409020a080f0723060a0c0204090b010b030907090203070905 75
    0x2080c1041e039280c0002e402c3c03180208120707080c0404d0750880c03000c1308000001004019400c1c4c45442c0d590400b01c12800c0d42d251500002145042e0031340595006111420080c0b0189403031000c89925019110049181064800c500096502e88110000c8404c000c4000e004401c9800000c1115102c3d9454805800d01c0002c2000070000344d51803140c1c0c0d03c0341c519580500080480f526060342404801e500042642e8028040140da2002c8642200c601c0c1d005c400700e0706e58800011400d04041c01c2c03642e1010354003100c3ca03c208414140c202c000355104086051041007903681c0c0110380d0050344003c0c000d2500140d0203009404007420540c3c010700300355000801c8a1041d41d0341d2010140390000040d082d42050b00000f01c20001c100c1940c66240d41d0403610810015902d07081d40100c1c150340140d125000c10844880850025501c40d90300080c602500b2240d840095a1141072041440d8400c0e903803034201d481034502c0018203000c0d920a49000d000c403581c40300c032440d1501c0100702609081640c08031484100a04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 264096276 1250 264095026 264095057
    0x8070f0804120f060b030c1e030106030b01080609071e0302010c0c08070909031205011a071401090606060e01090302090a09080c03161b060f050a0309150204050f010c050709020a 78
    0x10030aa226102e43c0c0c20040e034100518068085c0e900e441d20540c000d5110100c049201e85d0741030039900c4030078410640100d8004076000028050710080d4009043c0c41003110010540b0b1901040c0503100d003135048201d03031060744e50f920b9001d90602204c032990389103460800300340010340c0728814181c1c0040c0a00100e041c1c00352100c44c001d04041c00c83d403001125a42c3c2c2d0140e88201a000720b0100e004a08a12080010b0340c074192030414119400c01c0134203140f100000f885810014840140c40e860803c0f40000c0050202d00e190900041c245070040d1000b258036079200340000d40c4212024002d5941c00390050526880d4211913402410701d5030001c0fa960401841490000320080025020b8260f02080c02d900040082c20121445500c2d2014069200d500303500031700456411a009000140c010f14160b540d48040780821070040c5484440181180d0b1302800070040700074560040c0069035000c4810002d41c3e901880191a41010070b80010120303049690300f080b80704215405041941846c0c102803001210004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 264097526 1250 264096276 264096299
    0x60906110714030f011e060b0c03040504021303050106030b250f030213030803041505103005030c07060327080901050913140a020708181f230708070f0804 68
    0x912400c2d086d410340388450010b410300881e0010112144003914200c8481c28140c6c8070711071805402d026a4001840703031100d8404107031a10007513400c0741c001c004cc01d441c0e10b03218054400c1076684034910040c000400f0300503448003184038a01e100769198058100846002a400b94100c1c00c098030301c1103424000040850103110080d88913510030013184500304002001c04c0103d504c09070103031a0301c400c1030100f440074414408131043c5200c620201d100700410312110f096071551014600804c030340800701c0c817110032240028441040e42d502d03880a02a000f0801e000c080450428804800304081300d1803c1c00c04640b141c001003a40d0746040c50558980100c03036012421a40401ea80102c41c55503d80706202245009001c40340c02c052807400031751808002c1d0300d4100301400b8802031440f14620b280c1d50000c003651081d00d00c001403560f141880c1c411009510001c4e24402d1054458003015060340400101c030807c540c00c1b2141d440d4007003240780c10410251552903000c2032004046a80c0202000003185011042 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 264098776 1250 264097526 264097541
    0x60e0f0405010f060b03011d09070314030706110d0b030c0303070b0a0204090507020d020c060f040509101a040815070215070c0203030f0304020f01090e070507020d1209060906110714030f01 83
    0x31800136a50b9450300800c0048e020400c902211000700803400e000208001050210441e60018506e440c00248041480c0c2548501400101102d140c00581d1800604030070240c003075180c20500c100140c68108040c15114a000800300340c0c1a0820441000012032038040240c00078120403005042c180c80d030002400300d580c151625800359100e000940000d6a0400041070300040c182c03603da0500700800b03942c2c80e090060f0700613a44200c150760000380901c0b10440d0054020400c10083d241c0d0bd0a4614181d405640035004101c1640501c0b840b905d160207200e0202d5000381c2e2907a00800c48499084845400c0480c058960700c1003010303040149004da40c04001030f10700d01c01d804c003200e0740d241003600c10444103140200710503060242d84c0e54100003855101d00300030751214003402c0480c0d803080c132031002031a034800214009001c6080d4410030303017105030300101500c00d403800341c7c555540e101d81b140419560000c55186000700c030317400798100384116003040f0794a2200500180c1211003146e141940c050075103188 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 264100026 1250 264098776 264098789
    0x302011b0804030b0c031f05100c030e1009140102010e030706051308030106030c0e120a11061e030105090606031005012307110f0f030a020f0105190305060310060e0f0405010f06 78
    0x8000e00080f52800c014448942200c2885180e001d2310380004940c0c80708581d5a0340d0309011980b00983c0502d030007046160500000100459503c0019200c0601010b401c1e01541045105811061100754014410310301420340480085091191990750b03d4007a003002002c0c3c40d420b4920740048000181500c02543c0a40190749010403c1c011185000301201080c4030494070038043c58081000c45003000c108800c41c01d030071001044030030440901040c4a840313240303c1c5140c0f01200012006188480e440610b050312002c0b10080b00b203032101e03001c20015002c01e856010101c040050b0402c01513015101c075100c003081c0c0584401d0030400c4182c80c20703e17035000901c0650310940001903410240c54080b041e41580e090448036940c008440c1000b113a902d06161400a0198212640c8008540e0154081c0d54200130716068071001e0514510000b00601010780d0304501900c1a541264403041140c060182a1510389103950902d40d214040340c100c03d040684180c132107540e11400461480002c0c003810018001c4c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 264101276 1250 264100026 264100051
    0x10827030403150c0e010806190503070902070521040b031521010b06040b0d1d16060e0405041e020d0203100b01200d14210a0b0a0302011b0804030b 65
    0x1281002000e039003144d1aa0b000f041004031078a02c0c103a8002c18556048002a20780801c0400458654900c030002c9401c0f140c0e041c450390100268841c0a0380091480c20711841c01d03200c40c2c0040341c2c035130201c01c24680f40d0000c86a905100601192403860b000d541d0100c1d03140c2e442a40c409030440822000014200d5101c00219445440e8400840074044c200d41c98800b0b980662800e45030003802c00c030a000341903098154035201c00c600182000e1484c01200d101c8840d9094a8060391848032001203104d1740d20921020a402c009090500c0c0b9142c45040d100e213810800c04044400d184440b142d410043d214101d9001c140c0b03500b0030340561000c11103140001c09142001854a24600024040f54840d05084140c0001001d2480c030140c004101652007510b1400e0401c0403500898010001313006000c1000401f0300c00103c0180c8102242d003031180104503400003000350200900a010340d9846038000a03000c01e908503e0305141910819561282c0d5020b448454100340d10b81e500c44180301401d0320105100d06 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 264102526 1250 264101276 264101303
    0x30f170103030c0209063703050d0306030b0a150501030504050322141c03031808031005010f03020901020a330c2c060f0c031605120405010827030403 66
    0x14032004d01c540000c0115101031f01c0c0001c0c40c800d86000e0301840391003d20b04848a6141d442da4821114001c00795602000391148060005402001000d552006990440da003001082030a0160b1003004600c5420100c3e4010306403d100041d0b01800001e4000c40d0f003444100900c16000b2070402d004030f025012006080b61051a0070031003d203030692a0308807441007021159400c010303a00e0401409090f50306080228001c840c00c0c100780701c9083ca0074806400c501d0004100016001090100405d44000b602d135031501e290004411400c0340510440781f400b590101c65254045613017945008200c030002030b40c996840c288074410300d4040012345590f01c900c5840d8015500c0c008e03040f428040002190b41c0c0406d000c5c0d0350806610304246221226140260400920f480880c1200400c84000608000840740e07075040400100d030b001048894180e800340a48980100701003407100848046a078165915500ea07110b0b018908054001100e9100b489848420400e283e00d1091004d4002140102800c582c01e1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 264103776 1250 264102526 264102529
    0x6140601091a0a4b1218050a050309040606111519020a1206060311040308070302030906031806060915011d04061827081804240b0c060103030f170103030c02 69
    0x110000340080c25000c1a0421108031301d0ba014602d030003600610100850310030401d949402c85003c0394540a00140900c808400502c100000104103000e02510100101e95039007900301c8500c0500010f0112540041015201c00b4640517559234000480300c007008802240500103004980c42043e2203404240141c8102c10032100612940c0001c101608051240d00144d2018008500c00c9010051014001191510500d4420405d07615000da000d400550380b814031201510940541e40405407117071190500290003802d00c0d107a91401455680c0c4006410303050603006445055034181101e0400100840040165590f03000d040000c004204c090341d1400c0c6c200402409a0b50035090383c901d0402c1443c1540f190100c15124448601d400161031b985070700301c17440b00c40040780116802d1507101e4181803030303450300c209030f2440a114410300f41c440d408002d5540c0f440c1d6a0300c0c0201008454103030000401000480c1c02003ea41c0d003000e281d89008808080303030941c03100200b1005c1c0c106400060036281602c046 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 264105026 1250 264103776 264103877
    0x3060703090c150207030308040809090c0309010e1203060d14010f14130c05060f0d05091c020114010e09070305071202040c0309050d0302090402070f06140601091a0a 73
    0x43c10380f04039550400d030320500340a503603001c10303100c020200f10031400024140071456050f40e005100080c00d55405003845410021a0b0f001501c41949651a000b031a401003170303000070700707060b01404800c11a081d40e54040401406110001c020388080c41f69110076020340c4004e1207001c0c1000244640051008116502c02c0904c02000300306802d202c004500110200d1200040a4110340303048888a0317990754006c6034540715019203400419101d007024280705d103c401c0810510b060848400c1201a59401e2000481c241c032020143d00c140e410030301005012540c0e03010611075004100c0b2003190909662559018075050442d4070004000342000118021841c160068203010103d614060080c00d089886031a2200049a9000107241d4002030030315441e01d943d0155010160001c00c1450450141c0c1011f4003c1c1c04000b40b42c164a003502c07000600b256024410b1700e000c0d90000300300000c03200000c1d81190904d44c0060307045418042010354440390400c4d40c120401c000101c035452141c030600744940301400b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 264106276 1250 264105026 264105029
    0xc11160806090a030c0b07050705030a03290f040f02090607050105010f0506040b090415051002010506040b06070b010b0d021204030e0114090303072d1a06040614061803060703090c 79
    0xb1603800140700c1c4004a6070200c0386100c425006000241c540e1501403041c1c426125100700201140800310b0000c240703075019070141c500600c60030048510302003c841c600c151294520f0109a00840046803c4c00501701544020310540eaa0341005203043c103c50002102c6800081d42162140e440e000180642d550408006004000a441d00743c1400d0501d400044640200450140200d41d10b039a40005640000d000c41c2c001d0801610a003500a0310301d81c024064007044580318052030800704000e03081e040c8001100c0d2240d40203001d19000740d0806111000c00c0d44519500d1040c03e03000d10140d402c040843c02384c980150320903111594000ea8900000d0070f0019040502c00ca101c0b403d000c0e8402c2901c0201c11142c10641c0a000004540052000e0000d401d01c3d400308012201104e100450800070101c0c1d4481c05007040c040101340c2d036a0380404010070341b00c150040c4899102a0310890225051910250502c4d008440507030614a890070003007446d04800f102d070304001a459202c01c8040c003220b50031100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 264107526 1250 264106276 264106291
    0x130609080d0f1104050f0114030106032009030a02010c0c031e050f0609060601140d020309010209031006050d080f07330e07120c120303020912031c0c11160806 70
    0x40151407503055400d4011803041e0b9000d03560740d1b603104407681e10074012003d110701c80401e0070ba1a542c4980004004081f002524500c4107400000103014449480030b8468141c03000f0010084c00c000c56004542c0201200d5088903007080400b00480042c1300b20128a0054805800042d542c40239801c2c001d150000c2200d00d1000c9410004c14001c4ae502c01040070b030352208080c2080a074a03403089400d81e941307114500150901901c0441030003031224043d002030452010031411030315aa640e00c1d03482c0080380c02611803154403948001c00d28001800c1100509140304c0400b4540b820002d06440341c98604054103040f0304103031814103110850300d411451503504a11462000c014a49030341d0300f243e5031018540106180c2d10120340200b020403013905c1c9014040c1c1152601078040000c1403071b014020790040907089103e101c6201022407001c900000b5242800444001d6030102c45030303100a1070007030240350404030800240c640e80083c031007810000f8082003151841d001e51742514004409003003510150800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 264108776 1250 264107526 264107531
    0xf03030512180703061d0304080705151c0f090212010f0501080c0303091e032e1413021309140709020a0f0305070314010605030412030605031005130609080d0f 70
    0xb14100301d00040c00c24143c0b5446a000200501300886081c1028400c019176082c40c400041d000c10a00307008144c1030100c44050300ca80014803210a0301c0517a0f030041c0f25030f0169800784100c11000c0034105400200d00402140d1000800000075000b054486800d19507488007a0345034141007150071402c0c03180500410f00000a062a4401c01c0c002944a01c00e0070303100d40c0700344654090100d1803030508898480b5645c00034100c6080c9a540c14601d550809450301d4840e00b05805540040544800e01444c820440d5448690103243e66a220490210f901088140d0700000d01d40700700c2c0d035040c84910420010b9401428000089580034001c01e10b02820754006070300302d1340140203200b0b40702c0e00404d4800765522076003070101d00e0703a45145080703004002c3c01529400d8416408000510144c00c40c1c011401140900040074551101150903019164684181e5405074031200c0c9001075244035138010380d008903070180c04480242d41c5e038070743c8010303554048010750b13440c0c0c000142c1c2c0c1c666550354440e04080e4035090905 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 264110026 1250 264108776 264108811
    0x41b0e0a05010c03030b0609190314030a0905010c061103070306030204111e0d0e0d0804030201200d0207150f021b0c010c0605060d02090709060224010603020901090f03030512 77
    0xc1404030f000030024185520b50784ea41c1102d90b0354005451400e4000b0380000e00607404c03401c94800c000c0e0244400d6407020404c0940c9201d03600013000b15a10100c0b55150444014034103001142e10749400e000944178695102c0c00070078500000e9008600030582a58041101402c500420080300c1c5400d4a00c1e55118040000e100b50f000030000c0c1000e14000f400c1542e840d020b034140040041c24100c011640c0a008901250300e102d600129424052341c003a5000300320b0043c80540c882c0038050310040540c0100c0007444025426a01c81d0005c0078100d10403848007020326000c408440c02c0d120101c0c1190349807500840c1c06070b100300c651341e81c40d0119032181700103008014001d80060500c0ba41510094000303515080052016120200d90744c413150350180c810b52152502a200030100a070b2400b40800602401c0ca82d84051280240d400700800744c0d81d040c1d80c52a0746480e80c00d800940c0200c200c0360520609030310024505c0003501005c4000e5002c1d4441540d60400200702c40c02c4014004e21041c4d03a03070000313820b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 264111276 1250 264110026 264110029
    0x312070818030f12060402070507181d030307020f06010b070201030b0609060304030c0b0c0c03090d050712030c05070e07021506210a15051e0c0702041b0e0a05 70
    0x50642084860a020215441e040c41d11407207511484450314540c80700080704816558104010566600348952041d2152200001c00c410383c8102d0b90050040d034010541400921510142c09040c42c181c0900081e40c41c008400000c20040740c596002110f400c08000c0049907a0180b042010121112003d85915810184101c4550003942d0003c0e04040c0d840c1c08046468031110304590fa4200000e101544910342454010540c06084800310f80c082c00e11f5010914801e0381070150396591402101a605010000c2c0c02e000e1700d01c3c8406010354440c800c0d03200c00203850844000e04402c0c1c6d4040d541c0c244084080e030800034600f031416805500e03421250000c00c40c8141e8081408000c02242c000042e80a8481c0f80005005034141c8000010340282540001241c2e00001081c840084c415500b0416609030b04071614112941100c41103011070f01c94030001701ca00c0f400d01c032041d80440503040460030140203801040443c1d509800880b5200809041000c440350020040280101d045440401c0281040f0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 264112526 1250 264111276 264111307
    0x30c0212030a091401020c0f0c0d03120609020408030c06011a030c0706062303160e060d050f030a08060111060702071404020412050703030f08010f1517090d090803 72
    0x340e1503451060048049101d460098100708059904000100401281804580d0003544a25565101c6200702c001c0308000c0c2c040414101d821f000010090082c0300031544050328a00114100c18134219903540340172841c2e0b2300d60b1010f0005400e072407006585640001030014a0000180c00c02d2400051a4003801890b01c1640200c3e43e025604190ba01d850380041d151010140006802145a98a0001d6501443c0b11058009400c5606c12401c6aa100e81280c0e410010007403140140d070b03001900200011032509005510000540c40350084400c2040b42c54417071407c40d0440c003120400500c0d20b030107010087d82c1c03148082d003c8034240c2c0042c10082c186050081d680f030748144500507062000180a030341c0350707450340d064500510283d064903010002918240344c80745041c0c08101c02141e2600101002c06100b02d10860503648000c007500103a40c100081210440000d4540307008001004415140c011014443c4501904c4030760004c05041e008108060400502a004820070742e0060040b01003020f48003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 264113776 1250 264112526 264112543
    0x30c0812031501020a06140901060b04050a03020103150b03070804020f01020606090f07210e01060e040309140a1e05010807030c0503040f031b110108060a030305091917010219030c02 80
    0x74001c2c4065220b00507403c01445901c05880d15241442c1003e000040002051003103102d01c008100072900c0e40c0d4844450b01a60041030b80180e0040d1050005500982c446050400c00e8010034240564031044038603250b00460f0208001001403042c0300c00c40c00c007800ca0441d465024000342c0094900f000100e0098075008102404285801c808030340e0080c00740310700040d803400d40e1a11111010040d0400740c05014040e0001c07056619103040050301028510740c0c140208e51640e01c00310000d18000041120440c124003044d031060b84108002000558800b01805a128440034200c68901d4100050700c40540180488185424070110844030380c0d1010850743c0c0305600134070102118030141011035401c016500b1000b81c0c0f2490512000500c10b03d0032540151038400d0b40c4000c526503441c1c0074400034110b5032000a012400034410040c143c544440081314070b401c841d941c01c0005036100c510a00c2ca82c8a01c2c41d00b00706950001e080b06c0ca072500d090301e025039091a410207002041c004070000b03560b00d228 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 264115026 1250 264113776 264113791
    0x813030b0c1801140d050c0d02271c1428060e012c010b0907020708060c04050604090b01030e100e1b150c190606060818060a0b1810030c081203 63
    0x8450002e5207d40340d60302902e000c0a035400d82107444588044c86021480b0141d071440e00c0420700d800c4503112629006070b0b80c0d07102c0c00b8004844002d141240c0e441503143da01c15200101c0d10b0058007014250a10700d418501084900e02034614a80d01882c185002150307014640c20f02603034100302c1411207c405d06a68205500c81e41148020b1035441b6003070003801050070030a90f43e840107003038051007103850b4002003450548140390140c1e10591190800c4200520682c0b08254100005200030014440c407079008400e00c18041c1004100c020300c055000f420500d10210f020084c03039239909030040581c0304103c000042e0022003507482a0100c506c002600c4401480520160064002543c0121034030600c0718486d8966080802c0c500302d00c0d43e1410002501d258080c64001800740c0c1c001501d01d070380c80030b1032001c81401030024141c0303503c44096060182c68224100c58204407004e081484110800c02407911030285030340c1e02c1910500714501403040300d41940c00281d00303900c02801041d168000f0011240c00c41d40b07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 264116276 1250 264115026 264115031
    0x70504050616080304061407030603120f0c050a05010203071b1e02150c07180902130e030c0609011b170112300807030c08040813030b0c1801140d 64
    0x2515409282d120001c050010a10b24000c003e000c10007182e80c00030320350002d6000484841d40d071002c008078100c620512002c5c10994101d81c0c1401254051400c92500075034602c2c000c0d0003900c480d180d0500d401c1c103807502107585a40c0001041105036101c4007219810401c180e50320180c0000c0d484050705c140c400701d5003162800a0400040441d6038031984034604002054013191070300140703c042a16810346208810500e03950490741030340f1400901c5095044d41e40244140103030b508001e06080100f90101d080ca5403848108454aa80c80007017060703602c2541503000116003007039441d1206e01000300c2c45a000d81404060071485a4449202400c14150303170343d800548266100e00d0801c41c002c41d86100c2140715610592844154001c4800f4181045c1c12158650741d5541d16003540407401c48440000c100c001405c050003040c00a50800000c0000500054012660680781d440310110141d050f154661052400140040814058071052011010900307005010740c91000400303501d41304945400c0380d43c59 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 264117526 1250 264116276 264116287
    0x203090c0307090612080c1603030e09010902120a0e0c04021c0b030d0c08180a0306020306090c0313030e03121b10090b01050f0103150f090e06090312070909090b040204050a050705040506 82
    0xc003017007824480700310b103101005025a0f8ac10050315a036040f84845000e00010800420203011a00071500c11400201c092445507503690001e000a00c01e08904800d00d01031180c40d500b04e82d41d0f41c0094a459000c5c0c442c1e98040c6c03215055840115407a40c8002c031301030f400802070b200380f054001480300d8400340c004001d0340e03803a01041160000c14903900300c410303400000d50001109011540d80914410801070b1b0342e80712035840c1d83c980c0ca130303141c0000c9890b600080c00b080c040030f00082c45048440c400f108040d08a44e29600005460314003500151000c60454030071240b0304114501c20801c031000c80c0060441006505400d4448018449050091318010312404100110303a91096000600011150101d0403485844600b20f507650042489040f10003405d20000e184000d1001c07a103a40142402e100a51800614002141489900900041c10b0142c41007000a000c02c290041c6001a07118000d501c5203458244104403c071800582600401e41c9401e08010101d1341040449054800c01c4942036101c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 264118776 1250 264117526 264117547
    0x804120e0a03030302031f0f060c030e0405013812060d0c0305060117030906040312050d140403031b020706082701051006080f071206090203090c030709061208 70
    0x2440300e40c04098000300350120000a06500d0fa01940c0030b01c07240c030741c0340c01e000d40c46001ca180740700c00317600500f0024040b00034204085405110030aa40768800d00788401e00ca202200041e040b030704240e100e11024600c60000045000009010b983e0341d0f030b15245051075503040c852011a15010b8100942080f00c81c000c0812215910380d034092201d5540507200030141900c0307140c40c945400b420310400070380b400c800c1150f80400b6004130a03244204006020b00707003814034644568001c040080d00040a00904011440c58031283d40185401108640292641c0d800c2034500101102d24800a070303030101c880109200c8515502290071000c80d60340d40740401c500c0d15003050480c1c100b0a013000058010400850500c0c9508040d0081441054800c0b0024200e030350f226000d5480d071400300c8050b00b00005410000d90300900942c0121028544140700252040d104e0741400c04030b91080c0d8000c0d50551184d80c14100310701c0e0804c4040080d0494010a010092908154a40e0202c04c104001c0c5507050114809180 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 264120026 1250 264118776 264118787
    0x9050d0804080a050f0d0507020105030c090a0b0c011415060a081b07030e100f050d110d020c1f1806020714150106031413030e01021002030114030c040507080412 71
    0x54240a02540c460f0005464000d65440503160525501e00620030a01c80c1c0754013071401d8842890b01a11030310301d5035451110484144d400404060b0f0b010000c1c400100d031051664018000030480c1a00021301449231000d11030031100010301c407100c0200c900100c1a1213403514820386a4201d010304207051551034000390000c0036030419410074032042000c258002810f42c0030a00d8030f0110f900b55001074a41038600341c100d403c0d2052288000202e9400c00040c2201d6205910062058450914039410825501c0008041c1d034440d1010408640c021100c86000c87c0388101401c10b409000744081028000303010742110001c1c1254005000690f010458005020031410b012041c00088000d64240240901c0d041070410b4083c018a0300103498080300e50005c8080010003405021580c00343e109182055404482d0380500668150442c0036813210315a02001c2400614003800300c10103580a0921194281441e26a0301c1280c140700f0707400d0105002039a40c00c58501034000741c019030800d4181d190200107450 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 264121276 1250 264120026 264120029
    0x1202060d1d0c04050a0b1f050c070f090506030a0c060f0c0203161d04110621090304140303070b010e060d0c030b06012705060307110a080d0c020a0309050d0804 70
    0x1980c0041c24903611000c0001c106200391a40443d410025512888881021034592600080d0002d1540d402200810074060400a612416103000e500c0e100c1c2c0c07a07119905280c41540002c546134a0440c0c18886520340f0700030b0716441041a0000c008040c80303034031590250714040c4100300602818000c00c1d00e446200300242c0028503009070031240e401d4001185560700030300c9440313280c0031107002590b800c2c2d07101400054940205d80142d404d48040e840c0d0410486d0550264030740e1800341c00c10f000810b2078007100521040c030480511024684881c40c01c0c03110080e001c3c01106151190f0010030090700080c003010103190549030f03001040c070315595030403010494a10f58800d01a00388460700d14000204a644500c03140702c1d50080e039030078024100c42e10b440c800340f84c1214541c00c40a40112028462414441c000d55481901403070551a8149240c82070b9040003a11103082c0d0b010390000071030221840710741c0102c00c0785140c0e910081c03840d0740d0343e504c0041ca00201400303010300c07a402a01d005014440340c50309440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 264122526 1250 264121276 264121301
    0x16030308070c0c080604051e0705041109030a050a020f1008010b0a020102091210111c0506060d090b2401080a0207050a06051f090209031e0a050307050a0c080303011202060d 76
    0xd0041e5129000c084c0d59903030880d007c44562103450714801050504000b14a11460288000e048890814003000041c28290311140e4007110148100c1003950f5042000007041c60240c80030b404660142d0050082c1e42c0620101c103402900101103015482e90b10030150750450342c02c03010503500c901d400d9100720b0184c400d000b620740c0d00c4000088240464070002c42c0e1101007146009080001a4000c2884e1000d4000c6501060f284003100c0e42d2000c45044c0b64201940c04a001882030703140a01c5000c526088902810050320030002c000100306407034011115030503081c024036519501e0401c600c40002d2440000900b5411540e401060241c1000000c200305e040070396100c03005112520b0034000f41650100c03c0750040840c28480d1130300141c07105182c404c56032a0300c8040c1c0034107c1486014100900c4050403e10340c0414440c200c0380704040f6401f8400341904c85d02c240050720700041c00d41049041c5051541101089800400c010020246c1e04440c0d46081503040c2e031010f13200d49210a6000040401040c01d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 264123776 1250 264122526 264122543
    0xf2714160306080c060912070f0f061209080a081e0106020c120309090612030d020d0504110d03090b16120c02030607090506030105010309080c01050c0c010612020f09091c0207050a0816030308070c 86
    0x4120504940008ac007034610390383d254082420b0341c0380d200b001e0b580d64140140100c0d004101d9500c0c20343c49420f0403680f0084040c0402010641a860401c603010241e0001c00181c01c400304185541c5810310340d1204502400000314100b8484000242d03441c000641410302c10f09480d100d00424290a1064030441c2030148011034035002080c16542c00381200310b404641c0c410460182d0301003460071704150b0030115016074961102d0341c1000d0580d4101d40c0210f101a407401601d400800001d1207600c00824445150340d940000c9140c07501c141481d2800c040d0a0300c1c14403e000c0d6060289403206001d5a04407a02440d0100700f180321400c1048c040d104109400c195035090400704001c00407080c0050540001040081000b103a03959220040640300d254001c2d44502ea880602c02d0600d09440d54a400210701003d80703410101c482c06505500100301300c010096088590100403d00d800d01300c10300202542c4010f0600d01e00c60b44542d151a03a0305001c01018008261302051189200c2c0500c5110b00c1c0e84003500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 264125026 1250 264123776 264123779
    0x312020a0306140409051203101703210106021b0a05090403090501020618120a030e03030f1f0810092909070f2714160306080c060912070f 61
    0x280501194000e2502d02ca11640b901d40550425100e005c043d103804c0030140140d207641c0401002c450b480501240c5a840c00e00c3c1003c200d6651140000f8104590366008603a00c403da0490307218005121a41e15403080103d1004104031034020420301c03c106120320080c143c031503080c030004107407138020780280f5000f9107000300700001c1541001805050301e07001d808803030f500d40e680301c41d02840c9600c0e440c0c40000340c1c02c598421500c07511804050042050541004114004229059413441e00103c0f034540d050310381202407141c0240d1008001c0174002265a4100117036052000003070350303901084c0303404c00340c0d40d5a480602d041c40300000014004443d024650420011007044003072000d4000e483c55492801803a80005000c140200e000d4200c0f41150710941c103500b411000407110030940351a40400d00d0711840898100c0e006e411340c082c41080030368000390320201030f50340060882d2150b80240c9a5035204140040c510b54410087e5400c0744412588007400b410900c83d59420484d03035a000f44144110010b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 264126276 1250 264125026 264125047
    0x605030717090c01031109010c0f02041d0d0e03030a08040b190c0c20030606012d0c1a0118020a020304080a0b0103120f051b03070c09020a14030f13031202 68
    0x2d0f07a074070b0700030241e0b0103000381130135807030901820703c0780b0400c550124446500307200024035400840320a00d030005100240101c4525043d424984030382c0d4244426070400f0060480c9030b5044400303441607a40540041d42005039407000644440b04c00362003c2c003088404400205c0c405c51403a031310354425600410a01001e448a400903040b400a0f510844400d1840241c1002d02e008100015500d48802401404141c598000550f101c01c96412040840029402c042a00c1956a080000c00741126a10901d500c1c04e6820b00fa007801e840010020300c480e4050004014210316426001c10a69100d0760050f42c40e002103109134514412503201181c030313000319850344081c02003000b031160481e40034143c01030205991690442c0c0072105c00c18141c0c049a01441a041011140e05c1660000b08181e4222464500a0749440301000e1895003d8080150005481000254018880d4108800900364941942040030303421186560007040316543c03250400ca00002e061103074648002200c0c100c80308540c2c0e020480c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 264127526 1250 264126276 264126283
    0xf0221070f12030605040b0f09040609030507050d120c0513051c0510020c010506091918150f0b011b0b0a091502030105010e09070c030807140409020c0c0105090109060503071709 78
    0x2c0b800b03100e44d185c40319102c07e5040420901c1240140201080301d036981d10f0741d842c0001c081c0c01c00281d08021003803009a00040c81001082d41e03881c080e8070f6414485259150f42001c0d201100200801c20a06001500e02400340e9050107059403012184000018564200254001e0030810081c01078441e040c0c042d45641c9155004000240029000303101e03942d50481400903070b038410340344108075403400d00200100c040b19a002d03017100088000d151103080180d0710755a409000c1c40815402c015502d07505500311298611421103521020b0030082d11080300382840506d0f0741003040c2c01400c0c00f10040002044100030713a00c40c00c0000d0303001c45a60200d000b1444510029002401611b02151041040780303090300e070110100d0b02c1802c0d103035166840c07a80c460b9401c6030001c0010340139070306200c4100240380c128001075000c0e102230401420300584440b440ca0040340b51400d907952260500c40200b080070642e0b41e0040c2800251030302d50030080e80e030303890f20081113504842658001034090344c1d40090014200012 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 264128776 1250 264127526 264127529
    0x608150112181703010803070311010204090203040b091b030307060504060f020705100f15090e070302120132010614040513020c2a010c080903060103120f0221070f120306 75
    0x1000d03000c2681252404100d03c901c402e0160344903550007800402c000900c14181c0102c4201d140002504085d90360a0584c05d0b6001502c040302c003480070404101c0c00d4030080105140c600c8003500f212100b618a540170070340700e205460024081503124800034050004541000c025480320650071503564402d41040d036110591003951074041400e14501e039065640c14010100c180c0920318034081c6444c03900c04c2000003072181d071214905074082c440c40007016070b0304c0c401540c1446803d58000702e5090011541d100003642c0174001810442c0890030020082d9011400180c1940c0031030800940c038181c942035044e0709000300e900007a030102c2c880d5044c84000c07141d500a4070b000c0300d400d0308030b4103a2030103030404802800c456030a418a100c080103080e8807540c89401160001c07030041624901d40324804000c40d040c95000d030401e84410303071244a040031455000001a403031291a102406164410700800302d41c41030916618002d0510206221007804078058001c2e40165000e008240c000156480140c00392095 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 264130026 1250 264128776 264128783
    0x209070804052b0e0d060507230c0303040308100819030f0f0e10031104080c0f060711240703020f0606030714060f070c030f1b060815011218 62
    0x2220800f0640b140c40070a141d0804605035000400241080011140e401882c000968040c01010100010902e10310505003c0e50f602d58030030340c00c205185890041000e005c06804c420100800c03c501c0b00c250b0201c2030301c1d041039261170454480d41f04c22030302d420740c040f051308500d00f18081c0094401d05500d584120601861003a22804200d580055094503500d203403081200120b08296100c9203140380c5804080c101002600303001960719040590302d46c3c80c0d0410380203030b02c0e0369202c0540042d141c40c02c1c1d4011b80e0212000c403441454003450340d452030100b0300d6054109019074141101c200212200c4082c032030a0745188070741542c80d41000d044c0207503034801040015010340170300000300da80c03805c010401806a4822422010f50315400d0011b100e581d911501350310708254018824200040e134506485030095004d1525441203100d0f500304001801d6100241c6070800c04d15010410010b41c0040c3c40d03650013101d454144d078070880301c0340040e0342d0450f103480c00040c1c103450242682d4070f11516604d00c40d00e0a00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 264131276 1250 264130026 264130033
    0x105070f0f02060a0903050f0d020714030702061206040225020111073f03020307031412010303050c010902060c070f15090b03070302070f030f1209020108070e0409020907080405 78
    0x4140548220030102107003401600440009011540075030400007945101e403414602c2c000700508016100e80101041d1080903030002088400e105202000d008800c4080d006149050002d42c0041c15521400642c409840c2d03d00c40012440c1d5540e5042d241c180d000d40840d040c0f48035a02411489154460204030702145201d400c03525002c000190442c241c3d0340d000200700d88407540306448609883d8683c815042e030700407401c0c0765591504000d890983c0c18420740042d5100e00080c94045c10401b0110144a4013800620003e907008070082c020a04503505410001c0d40c651001d81da040c0500746c1050003a40244001500d0074901c0030018400007101c0b002c49046003034a444081140c07a8101000c02000040c01c1c2010502410580d00005c1d0703008009818014034040b00c075902c0190000319002d05038003251905034294200380d0061001400e013001c500c0c082000149950000c1d0084101030141c004210b0581201403560300c50ba4061902e080d00200320342400c0c42c02c3c2d0700040c451841158120744600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 264132526 1250 264131276 264131297
    0x60408040e0f0f0c181804030207061404090e03091e04060b181011010609020d0501052416020307090e12180d020a091503230a0b0a0b060c010507 64
    0x80e03040d01d007409880d101100c0461501c684c1c0440d900c980040c0c51200030704034501d80c0303010140c2e11206c000340951143c5c025602145804c0c1400703030414030a030713200b403051041b0111440c801000c07040444098030030603800001c42980d000a41441c5004103800079401c52100075196003444015080303941400002c6078240315640e111010001140180c075001120b04030a401d82c1c02c55864503400d03042803403c2d10301e002016803058035025070035100701d9401740100d150700182c190003050b8240515809000183c03454600681101a0009580001a400000764a01007418400038540004c103200b45074000307040b291072540350780c0f0040003400702c01c1e0a03c010b44207001000060264990941e4040e071800401000300b00c00c4501402601003988108a0348122080b40100d500e2100b4420304e1000288a15408032241c01c0d0300e05240c0303c01001c4501c101480f261100740e00f464070f00048202180b81c0c429190512620703084174040c00782c4090540d80758404000325a00700b041105520683c813440f0503594102664 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 264133776 1250 264132526 264132541
    0xc110f01090b09040b0306040f0611040305060a0b12010212090d110a140109020d0302060906010603150b0f0c030304290601120e07051c020a0902040605070f080c060408040e 76
    0x42009242240440d10a0300d08000c003034441c9000c1e2010550291001c00c0304110700700080c3c1003243c00c45040b00d0340508142903000b4884c1c1403203514427004582c8046132625046071a0181c0d1460010000c0c25410340754800c00080d0340f0345007181d200c0000210300941d2601c9441040e0801680200d40c401c030284038070322400c60414810111a103122100e01c3c00303405181c1d4036807294420301c481810750351900d6407034020311030041e1158116001054080e901070b15450030b0001700c0c81d007031130010383c491010581004840c00103070b21882c1024040328400d0702d07000d80e101100014a10789004000300019240404820001800841d101c682c10701d404280d0061074240300010358949041042d20303c0d80c0003945d04c0c20010b80000d9030342e00440010031500c00311000d456031400090311030400702654000c80c44102150904506041c240360020b0200c429081d8141030030004001e21a000d210700191034420640e8a1034148200c20044840103094801503c16901e89801d00c41005d502030721507085204030840000794031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 264135026 1250 264133776 264133789
    0x3030103020f0d1b0902040608150906010318020901060f080901090f0803041416140913080f040e010801090210080f07110312010e0702011506081f0909030c11 70
    0x50300d40c014140304120001c541440748104868000701c4103951420070034480f5906200d1100000c22020101580e00c43c1080d100520b030300009001041141805100e006507590f6050105900960030318001440c07041099500d130111100000180d00000090300104901d0ba020b10b10900040e041c0e2a2000385803169160300b401ca8100c02d10140441249001d40300004501c50000c5030010301801950218861001419092008031440e1540b10002c8180410440c01402205040950100c401d00c1c0720303203024042070f158820421002481c1140006d00180700d141a041a00c01a10f80c04002008640c2c551001d40d0080246d601e003a40705003060a52120718911415a0358468200f40c18003030640c1e00c440c3c5c030555032140001c0c0201207600090040705290b403400c0104900902c0404140310540c03c00450207170850750b0110360000458070130442031004603001b0520b1074002030b8481c900f100f04500403000c0036100585802000119080c4000a014507038081d64802002d0f000700d000c0c461500b0300c5003c0141c1c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 264136276 1250 264135026 264135029
    0x40b0c06010f06080c0f0310091b080c13120f0b010e090c091509040602091207050a050405090d05030a021303050c0406080c0a2303060403180501030207030503040b040c0e070f030e030301 82
    0x425070006c01c010143c00f84d0540145400c0207146181144944d22504007505541106001141c84c5000310844d0fa11558004d0b0040d0700120f040010074a80106a1030221200c1d0740c1c1e0043c04540030b0312519070801c00078119611440c1c03d0704000680c3e032550b152451100c18540540f03e070030051140e403001c0c2c4080d01d440c18500f405140b1040002a08005020030701101c60390040c0291081a03007401445803d0319401030380d80e681204200604601800e0600308060f410140e0011401945018200702c0c08a80024200136000c1c11401c02d143c407a1780c0c2c9030001d00a40301c2e007403841d18201500c41c0000100400000c8101f1076800844007401059150031400d40d03551004e4007100d902402d003401c10402c40c601c1da400e6401e807010b21407100b0210900100441c0c0740c48001d940440010b070801c20595540b81050111801801003440c09501d442c9894800800c28000a44003401d80b03110400841e08024000e80141d00a00b00408550264549030b0409440071741c500341204042401d010310b1603003250010003103d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 264137526 1250 264136276 264136291
    0x304080c0c2e0207080d0509130e15150a0f090b0d170702041b110d0305090607200708030c0c041509150e01090209011403040c0e0c040b0c06010f0608 66
    0x921015200c00c42c0c003580c1c001d0030050550049010100b02e803c03050040000c441000e890f0742ea0345041c41414002c106440c803201f9205503161020942c0c0a410104d44e00301c2034041d121100d413440e11640c0c8a5002016030f101042d03030000002d4000510b07000c07402c00082c01c13140352190401180d03100c2014007a003413002c00402440c5207000d10400d890900350038064680c050010b000060300100000c00e608240c0702d000b50000204400340141b1441010810403d0ba452030140b07020300aa0074a0700c0880e541d100c0107006501404000010200b00c811031360341d94202480008100d0320303000d46d65201d281d00c030352040311100801d01500406110f40d04050245800101c02c908030343d00c0c00c9203000c051600900c00301c0341e0400a260000d10008500d003940c0805806407081140040e44d48100500141116030038106508102c0424010080420205220b84003280c0a443c0c1105050792160307400b01440c416600603465641002c00d842d12016000503806060340c41c0e6079031049145481d508162002c0c0000c44004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 264138776 1250 264137526 264137569
    0x604020a060318060e28120c030509010509040f02030a0921020c1e0909070815010e0601030f020f0f130602030412080a0207031202030c0c090c0403020103020903120304080c0c 77
    0x7000080d059a1000500050817000e0f00e40300d2030b0a48a0f0195020b240300412400c0000d500d0080c20701c0041c41c1443e00401540c207080310054200d550140240c094010a6414400c022034120390544641e003145a00c003e101204550300d140034410540140400c0006032403503030030649095131039502071110368103104558004100c503d01420801008203c1d0011048844400c040b075140e103610340c1c140341c0380501c00c2c04015100c81c42c184030760039103421030b892880c0300001030400c010010040105102a040f10081c64045907140c401502c5101911030107944a0512900080d03046640c440940503101600c005607038080741036580c66049a9901403030280d803c4400c980300c0b0b610000f501000c010400a012030060b5141d0343c0e80d079100e07051070071480804000540c00004404030710600a20141d64042e100311901c00d254140144614540d004902009041c1640001e41d0202e40ea010030884552101c030000c010341d2882d081c58403c9013030300820440012882000c0342d81c051458890368520340b580720071906 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 264140026 1250 264138776 264138821
    0x3070e01021b150c01061811120402010e18090a0c0b04050906130f050112060c0c0c0510050f131508011802180d0c050a060801180518030a020604020a0603 68
    0x2c104a101c943d05030a800700c1d1040002442450080c02101c0050550240c0c0000300340706500c0100c203440071403c100000303950410014440e0600740c03070709941040e0203182c00031003081c0c0d60011509419840d0711754100600301c6410003419100c002a480c0151b4803074644440001d90f079042580d00c41c011801408ea01a88000005046007000200c95840b1042140c2c08162242003084c44001c0303c0c02078200d16810345850100b0b006100041c05a1030100c4a03c0c5001b0300d03104015200c041c400d01c15809a40c2c0701c0c0d5500b65529100e60700c24030603540440e9550740c4007035860100b5000101c10010500c07482100050b0355070b414040300d02444009040b241c0d0300209a42069500301c10307070005e500a00320040d40c0c08100d009110300d82c4030820540042c80c070449071214a14101410410100c04a5000b0810010070340d00500421840c8502142c10389124200442c190304d51100390700403403920502152840c0303c040b401e038480550008000b8001c40c001c1d00d280700e51503107500c0120144c0780116500140030400200307 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 264141276 1250 264140026 264140029
    0x70e19090510090c0306060e0106110d0917241f06120b011b0b0604050c07020d020d0203012a0f031118011b0f0b07180e060a050d050303070e01021b 65
    0x2100f40b26109202035a0496220350381d01084036002c0c5c0003d00c03c903400400500c07050780c00085c0f110708540080c00600c1450b041da42e00400024040c002c0e4a0640c103551000b810740c2404000d008003178107403820540d12540d20280801c5041208070b40c007a22070012035046190004007080800c080d5030461759030307030300840750300708902e003e0000c402d082810070141600c2106005502c1142843c41480b07024a0b101c0d034107000042006541c0050113248030b1070320800403440140d44101901f00c1d02d0341c2c162030500b03005c071960000034010442c0003001d41380032840d0b41d09800448118107450f01c0da00c0031900d0f2442786002e640030840c02c07240010014144544100498894801011001c2803075103814900b40e00500d1450008410030315080100311041309140b0103410412114004040d40034000e071400b5110702488860a40304a40b20384519808240c0f000c0101e805a01c560480368050907001d403102e40080300500e0b00035501d510403210340d000a0500003c55840c2d6102140307410070170f0703040d12020000e0b1071204d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 264142526 1250 264141276 264141281
    0x10609120c15080402030c060309100518070608070f0201050628051002030a110c0901170111030c03010504390e0d0506060306010f0e070804050a05070e19090510 71
    0x40941d8034401c084800a248852a15107003008025039580d6001800e1034414107107403c0324010607a118840034410000403802c00550301510300c884940200c1c4913290340714210402c11a0400051f560300541c24080f5140703800502050055295a440c03488400e0303c40022070032240150b90680c0d0065000d2860f50340340c00102403090507951061071074400f8907aa0000500c420840d070b1426005a0400f107a140302407500803e0703540b400212030700544600091040020040c0405000304142d542d542024050700b03120941c003078042c1c01c1e4000401552400c207048002d406400911130b4070b101c1d600700340303031440e550010722080b040c2040c2800803c2040e280c40d20070b4000740c0c0381d070301d0024040010b4080040c051b507403001010b001650060000c0d1600e4109031040c141005416048000c05009022042001c40000b20000d94085181e00d0041076a407074903c0e010b030070004034040143c207502c40d002c1c010488480654116000e0000028114401e080c92080c80f8241c900012018016030040d81d065240c0700701c0c94 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 264143776 1250 264142526 264142559
    0x809070b0403060b130c08010f06090e0117070b03011d01060519080703141e0112030c080708071b180b0a1202060c1609060f0803030a09060b04020c0f06070503010609 73
    0x1080c0c0c0c5d04404000e43d9103021078184082600006400303500400c030786851100420080e00365450b2540d90241014007992140506200307100a03110b044a13400c3d4000c4085c0520806048035618050b075a5079103810203a5840e0a040325141000800400090384501030400c4038080822221002d141c0b0201c08425100900005c008400b41030311400e2042c0742a6990750b1151052280e40001d4200114580310841c400700160806600d03d4940d800b81e0340401c2d000601c080409034442413a90751982513140c111004e0080700340092580c0714610000b240c0c80003243c64482030781d091265581c40840e1543c0d61070192054003858640107041d100c1e060119400d03413070800c038505001a04030380c42e0642d002c0c48540341040a0310008584810740c075050003d5412809158010541142041005401c08403282d849100c00740c019540e0325900c240310005c0103030710b8100c0b40030a07000410864543c00384480b220788030381c01541310701124018500000e858900500603a070503108103131364035001700d41050452011291074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 264145026 1250 264143776 264143779
    0xd0f11030c030d1101050a050118091e030f080c2b02040b0c060103051b010f030b01090b13030c0f120f06091b05012606060d18050d0809070b0403060b 66
    0x201c000c951119103040150b031007002c0d01c5503192a0100c44248100d800c48801030201b07591030341440010080b0013030340e0301c602440603284800080c41500e940f41c50400280e401c200c210988411000e0502032580211143d0103c0e40d0030303160211140c1c1c61500c0c09820f442002e03e89010103c1c00c03e215110002c0c0300c2c40b440c40d1800c595600501c0c050b01d4210703044098020380c2402219902400052003080024010505101800710001510742c4128002801c042c00301e14554040565a190381e1009078400c4800c1d0f0010f00a1354012592825468407058004030180015a24068490000107882c540b07800c2c4442242c2641c0c050606502c020382d5a401c07000382c0c40c201a51101d4480b10b0720408581038608403180e050b00d208060f00350600e090005041c01c50840c0c06140103010750314004510301c0103c4219540b00b281212030039600c124103601d40e40242a0762210000041030101d82318104100000c1c45a080100c60300c0d003140729900c0c00d9101e60b07100700c0d030300400c0014042400b00704005081e0703400c0031081e03180 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 264146276 1250 264145026 264145033
    0x6060a03150f0314121e0d1d0f0706180b090102030f03010e04031713111815010306050a15083103110d0806060c01110d020901020c0d0f1103 62
    0x10744051050200b1190342068a0f240c14041d212004500c081017060204603114040324103104800600c1842079140000b518000301e400203900c6c042c64415441a07811081071703516041c2441e031000c0255990114980880b90511501c540440c40d24000c0d40613428a040102405800a04103a15000180c2090003042e0542c4018440d20454100b0070b000346001c0c0200004010031460f15081c020103c1908502c0c0c822a20110f4044c82008003101b40312043c8241c0000e52002518a0600441d5030200303505458944013903040c040c0308180c5c4ca400310201d80d11009136801c0c000a1b885104200c40c5503050b210b1080c0700c0e088900c1260f1141e0060390703006e0784441c0c0c82154500d0f040c0c866648030b92010029200e499020701160b4108105504840d040e110205280000d101095176000701038114440640844d00c40d000109043d46815004d40101900a0340d62000c1511120089403440203500b14a0010b805400b41d00400c10b000e040440024501c4c54100d5026048a00e0301d441e00100c001e0b9a007002c0b0303014013 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 264147526 1250 264146276 264146279
    0x9090906060a080f0a020607110d05030a020601060306030b041205160305090a050910150c0c0308030402010306090608100207290f06031c1101060b040612050109060305030703110f0607050909070806060a0315 91
    0x2b81c0d41c1c408100c203d80200c01440d580c141c090070013420200160014014140b03808400e0003c0381a1040c41907000740c1c0b00c600d00d0400300b2041801d442c14040c0842203000312805510050405610001800402006840c041e181e031b502c5008200c00c0441c220b524141425146208000a08042090504d082c03681d0502040c0d100880e122100c9030812a0410b555000b4004148030440d645842840003e04d04900100070b040e00700b0034101d40701c03100710005004031600460600c05210180d00383c0d080d02e04400c1485009801006944149240e04813180d0200030200c5000400030701f00407683c03062010000c1700e400d0315600700e50801e440340c00c04495441150340da1500040395803094140200042c240e00c0e02c0b403541e0f0403440e40c1802c0c150340c016003018281509010003080003523000416900d9160f8581007850304c00c1c01003d20507140c0382c04c85803c200c00740300f400248802d10743c11800802d006401994800d40c150740e10902580c0e10807064402c0760300311008020041105110794024203004504818072916070303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 264148776 1250 264147526 264147529
    0x1503060b100c0825230607050d0e10050411011407020303070b0c070c14100203040302090417070b0f160201090b190204170102030a180308040602090609090906060a080f0a02060711 79
    0x30000500212160002440000314119070b40f20342c482d031402020010700c0c4c10728100310010b00c0e5002711295800c10a0711754103050f40c0102c040c0705181d03e4042117001040742d803405050400880800381070007408140c45c048000e4040c8e0714072040718219030300680190301d410082d80e2565240c01c0d0080c84070700c01d21428842c0b0000079115074040d400428a10720800b0100594004108814051840c03100030342d4801c100030130040c0c07119642258010b810010445c0307080201540700d0490b11510800820b4282000c00300220304001d0520b80d07000b201c079203103604100030500c2002c1e400c944810001030070900c4014000380718200305200005010195410260a140d60b4010000c1c0c000490405442142d40110401c1b02c2c01070184203441c903145294822080b218955100a4040708000c0d01c050315150700002e00e910325441e400200c2c0c2c2440c1c00500051031a1501a803d42d481d03041c2540c201d44180020400024489400104401c0b000c000380b000c0d225110385079082060540c443d020407900440b4885401825 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 264150026 1250 264148776 264148837
    0x305160f02060a080906060109080601150504080f0102130614030f04022d0f0d0b01060305040215071b0519050925020304060f18060c11041503060b100c08 68
    0x55403c64680035240e00381140b0b02414014001c1031981003040740901001502c000141c070604480f4600501c0750800c0081078115081c1c8100e4005240d244107400400c8081c403c154024100b050b2005452032143d5240e18045810b000c4070550358010320070900200e040522105029a00f103840240016001121403c1f5101401c564000d41c04080340550308029180c00d00c0c83c022318004104441d0719000c56410340d9007505500060003040c041540d100001400c648510082e2400f2041415007a610b880c100d250210010000b981c5030b04183d402100002914105a107800301d00c410f40c1c42a20602a04010900080440007006220300b4902441d0070620441200100768261125030302550f41c86081000181044070f001043e82d040080e108458800c0401203244482610030394a030603050700d140307800d06046031003414012660162a0042101c140042000881c080300e04c90340050003071040100c2000046450840054082074002e0584000584004010f2913104010403020160503072480702e8007030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 264151276 1250 264150026 264150037
    0xf030a0204110901031a09040f0c180b0f12030904230a090219051f05070b0c0306030f010905030304030e19030506060901050d030210020f360a030305160f0206 70
    0xd11072001803010040e59040c006d80f500103090180c824070860308400030515a520040014014205a40d100810804244507050007014540b132015010904045078800408403280068840c0c4500d0b1303110080350800d40c1c40b480700300e14110042e60a0010080134400038140d01e191104c00c100700701c0007207481e00b0303009a03160380035910317880000070341d49110b20500c225481c00c5080a61100c1c458401000a0f80d19148903000409965034180d14134100d0f00c2082c0c50034002c0040c01442c00000380100030029a280000c2c62149038202e085488450100000c0c074200c44152034050b080f40c1003040081c011900545031620490320103440301d84d900c00402302150309101980c10403103070713500201d0600800e440c0030703800180501400c41c2d040626812913a8042d40c0c98580d0081c005440b0340200701c81d500e004112090f503221a41c05022685031000f0110f10789500191000c55040c880c2e221180e00e4242e041ca044400180e07581900d40702d00e4002c10007000500f110b051102110850a021800c10043e03c0e81006000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 264152526 1250 264151276 264151301
    0x201110c0102030406051e040f020d021002010c02070911040e04030c0b09010f0b06190c02030c040903050c01050115080403030b0a0b0a0503061f020c010e0f060a0c0c050a0f03020f030a0204 83
    0x60f183d040c18038020096030030260024200c414000c554880e036010780d401c4141c1250340305d5500107034600c1c28804207600710081d06000c1e5100c091840c1c4100b0b01501900a070681c985c842d400d44a02a4554840008564410300c486440381c0c41400203100d061484460f1581160182c1490340c0041100d030b840d10100383d01242c0081269468403010003250b40075009080701c144044560130b0078814040074042100740f824965070200000c40d00154195101804200d01462024000b40003034135081c1800f4000307500c00c1c0c1c04a5141e42c600340c00040e540005004910314090965603840041c0c07a1520201c020300340f02c82642d90301100a100000701008003c0c0105110301646e2103c03034507031030b064042104c29000480f98415100c162003843d03403034039804075040c504c20100f401c0080401e600307100461550990940102c0d04400f0000304400c0b501d03041070f1482601849240b800c20ba964448090143d032020074882d1720304641c0d44503800d000501d8041c0700e40e050100003038111060310280750009420350b48800e4104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 264153776 1250 264152526 264152531
    0x30f05030705070b19020718050601030e0d050c1002130509071e1d040b01120e030c030d0509062203030504050c030a080405041103060604120302030c011b09080a0c03060c0201110c01 80
    0x20440d4010030905e0f00032910a0000d0210f161400e51000050b1030460101d0350076581e1100014150b038000d42c04500e621011008450680099000262140d400707605560400c0c4605014405440030500840745440301c04d01c1702c50a802e02d840c0622000c494048d143e1424020b0640003a4249240152605a203000c142d07200c0114401c0d001d20a00d081d24014100c40c05141010042101c1da40c202c07401d040902404500020f040050b03407560381c11401030000d407068034080041c0300c2405000a80205004d000d8400660f101074881200043c90666035031103004450310902031400c0400e0082e8032141e40300340501c003a070319148004000a403c000c0d4418080307d01510110b414041c038102441007001040107039507150720394106000010b84034021032061400311501080c8d1002010b1080c42541c1c00030481c0c2000b800820400d012100101080742e942034001456100700080880300000ca4802198001d000300782c1040c02c3d0f8650b4008ac0240c03109407019592911842c02e00420960020880000480c000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 264155026 1250 264153776 264153787
    0x61e0c030a03090b0112051e100e030a080906090a1104090b040312060f080304120c03020303120105100309081209121227100504060603020d080304030e0613030f05030705070b 77
    0x10350004d41068004e00135241c1c41c1c2c50140700041000400d0300300703000c80541c9904a00c01d50300040f8500a4181e00f0811118180b9031004040c1e01d0000141900034403903241c00d003080d80d403405241d80d1908200c40c5000c2c4c0d60302811091005c110120301c500c3d0750038409400401c01c0d1805031038184a250047d14128000341403140b0824084149100c4c1d600174040403001b0703602d00da2611140039506d01940c06488000303a4180300d40c8040000d21400c540086030701500362911031000204541145c042480f40301e009008843d580c8031828801d100e2000c140740c0c400412800c0481c074146110040c00001c2500c542881a0000882019840c00c0604000c080d0b0031250100c40c81c0c403040c3c503503070303150b42c40b0b040c101400890b0714521b108480030840700c024400b80c18000030b07543e8541c28410081d0002c0d6001a4200122158450501c07841c1c00c01144158041d417214500030443c1c10074081c080c0b182c0120400303810320196081c0009408502d0803c0468055400c480c1800e5203038a909090400c1c2da40011010f02d4005007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 264156276 1250 264155026 264155033
    0x60705031209061302120f0708070303110a02130b03010626010e0109030e01080c090405010605040e060306010e0a0e011b0f020d020c0612130609050106060e0a05061e0c030a0309 78
    0x19640b0001c408007411803410005021841c00026600c000d110b4064141c00c001c070b04108100b10216410410100c83d1865030360020303551104c6280c08250006050140c104044503c00200c840030349501400307101c118403c412180004001c044204c55040d5228000005c0d07015000d00383c1c5880c00902114041c246050410407821505240d0034480c080e414011030a0200c2c3d003243c05403d0f0110300f07013045211903881c060404c000344541c2600d594460b14180c004500c40742e04ca006031090f1001c00610000d583c03034140415603605e400b407103803400d01020701002450403061900007906070072088001203100300014003001000b4144175048000590043c1ea503074202d41c0d040111400200d01400600645180000803503202d00c2113601940d800b10324003020400c4908030340310142d0190b8100004001280c0140b030310f180030346030a00c60840019010310a91225262044c041f0084500040980b460444060030ba0304038070b01d03424442c1041c14001d2104c020070540500043c0a0070384180d40000b040005440c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 264157526 1250 264156276 264156307
    0xf0901030519050f1f03080409021309050c030a0507020609060406111e0c0106050618010804031b060c120c05040918080301030501050108011409030304020d020604091505030106050d0503040909020a0506070503 92
    0x4d060301d15905c404001040800c0151040f28280c1d25901070240e901c408855500101c50030744e034042040d40d0b150504020100d21000c0217075004c2c14101f00b01340104c2e22a580200e0b96000b00303a030740a04641184005c60001911a480715502200314a002400c00c890400c1642400701030f41d00c144141240002d4403003403584203214923006401d04690b094206201d03000c000d0501d0021216030343c10301024001260034140036003909104d060540c1f0440b01344400a2a03d1006080c06044034030200300c0d21600c0a00d074800318003c100e8a41d40070b55613581401d151403091000b5151610b00d881c10f4400482c0d4203402f00d260f5400035406140070f0000440c80354900040c880c210b40100c9209030109281d1814030215100200440f6046a0111542041403400f400018440e21543d4404c41242d80380c2695100c5a100388269001200d104a0081024659400512881c00703a90800200185c000300014880340c20a80e004a01c1c283c0050800c000c066291000724040e07078400b44096525500106d08200074480c0074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 264158776 1250 264157526 264157561
    0x15080f07050301060605070b090109080703170f01060c030c080f0304081c0c051902070819030e06070201051c09060204180c09140607030c0204050f0105010210020f0901030519050f 79
    0x150004c01c40c140c5850001003281c0202e40c0e0003030441800c000410807004c001d400080c296a0007180c0603070703240881d1501410901e0841c5200c0b41030100030000032850448030201383d040b2400b54a82486900f8903640890718000c2242c02113926440920880e000750f14214045d512a5106654040d5200b120b0460768514602c50040c04030301508040304803195035400300980d02c06900b80392400410010750101a03003095aa0741000c03245120300000c1030300924000d40150346c0700e40240c03100a400008601800aa8070401034040d0208e002005841e0f030290305440c1c400c3c141c1e100d03680b001079207541176038404003a41d00690140c6441000451100344440c00751049110a00140c1031040f8524034000c0d0a0080309090ba201c01d00c25500030850304180344c014990b41c5d4160b0741c0240200a2440c007400f01e060600000e026082c010f10506c140007022085034401c039180815001e10060408280c00011405002c004020012140449a980c40d070701030700b405490700490510382600b4552400711503071a0b031002c50 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 264160026 1250 264158776 264158779
    0x3050a0b1b0f0d020903100504031206060203070210050307020a05060403050301030c090203100311030a0206160c06020a050c22050709090e070b040308281e031a1315080f0705 77
    0x2001404402d94a8104442c500215603c01507103c51a2900080c240441c06490041040c2014104000c050344040c0c884040c0b00c00c403204101071519400c003240d4a0203541d20007500541c00c654012181c1d070161000c2c0d40c1c4100c440c4101d0b54140c1b80c5030ba500c3e0500d40161011801700308080018400c0005812020303000c1c0500348411130840c900311203800d00014851002500d5400c840d060b11210391414482480c00540140c078280e6074042c03035552040c0398030301c1a40c04c0da2070051409010810718404680c803002c00e6000340080401108103402c100004411b80e141c0608100645007122609a042c01550700c40c07140d036150209610726101d0641c05980d1495802401500117407c284400043d2205030b078252908022100d40b14200c044200000e40901c81e10010000252842d80500542c8500403078404181100c580380b00b00c0c1030603403c2d01034075904860308400a100107100c21082c1425100100f03800b070400c0300400d5443c03418031104100000c2c4d1f046001c2580015041985640c010030510008000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 264161276 1250 264160026 264160081
    0x5010e04020102030712032d23010b090604180e0f0327030307060207080c070509040b0402100e061602010801050321070314040e0f092b020703050a0b 66
    0x600da40000d44034031506100908a084420b140f10010b4820760203002e409214021003202111034070b1481c2d0117400030b192800718050030321010b10060380f0704a514201c030342c0c8a0140302c03c80d0790900c003601c80c040d0131801840360801c5083c00001510040100a40017210205600080490303c07412410f040100d60005007a0b194001c00807208403240700040c0503188400f03407102103001628080081c0c158820341348041e058134004038208061103448001040445139050844410540d69070900051090032038001c5c1403580c030316001a000d418000c02c0032501c15554038289146865150010740641c10801185d40c4114aaa4030fa00840d42c0102100e405418210024100b0145484010340c21500701801c9080301040803540320f08150241440d079041c010899030107511581c030350204c4411901c0454100140c0304052010400f088004a405051146401404101ca81d1005601c0c11503a040c02400c00843c45442800404110203110000c0654850101122981800104440015207582c0314400703400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 264162526 1250 264161276 264161281
    0x105040e070b031503010603050d03140907060905040506190e01050423011202060706020a02060f070f0c031d03030309030703020f190b0601032c0106060f02070e040501020408190605010e 82
    0x3000003a42c4c1e015400c0c50b0754480511000b00801c1c050105688014500d100d8442d2248146405401c151003944111100c00c541741e95294085984d45541c0c42000c01042c1300315000d00590030903803c0ba9070300c100c0c090b080380440c24a102c03401c41c2800c0c00d40d01400c02e48940c00700500c100d24050080103080c2d0300c4002150b488040c20880b01e03407001010307c2a00301e505085581c600454484000380c0d001e0b07540002e0300319121b00781500003a403904000c80b40c045002c10044000742940f40103205140080742d0941e15100f00c05120794060f5441d885001c0c8041180e004003000b070038940e5003003005500c24000c4a0245441d10500d03d0044e103081101d1050030000c2d0480341c885002d21070b207031220490f01e9800604401050701c420006030000c1c010710341c60300034203030502800c840c0c1002c09038400e146006400008102550303807610b0032260b0f4400c0803442801a08544030401500c0d88041074523800602480c00185020798941c1a14a42003184140c8492074a01244210500280d44629401040704940807030492 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 264163776 1250 264162526 264162539
    0x1090e270d0e030d1817010b090a0212010f0305150c13060c0506130b040b060d0609050a02010801050a0609060c05030405030a03020d0e0d080306040207030c02090114030105090f120715060e0105040e07 88
    0x4218501810b4031205000e603225106d400250400d982d96a000380c41e0059904000e10040701a6010030303400801d0040c89400060b26a9100310348604685e0803001900d44800078003080380c82d084c1e001e404031910030014484900862003c02050004201c16210449001e000b881c0441c2451001030488910348807001c101030124a2801d03209511641c440c8102206540b00000286018200300001d49140e18040032801000340001e00c9015050007600d6044860380e0342e800304240d510041c090800001c1d0300d11001c000080c06180010101c500c244103880c2001e458001192400202110030713001648462500a102504210190109082602c0ca0306203451582c40f0380b00b9910010301214011030303001a65105140c0310f1000d00c511035034014101e03820341d695210400d02c1c00c508012914030035441e1801141d03182c0c000184232a04c00041002500c20a100030580305000d401c001c5040e2004081c0420703800003140340380b065034040c24040701d40c01c038107504180a00003161040b02424840f0307400300000f070024 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 264165026 1250 264163776 264163817
    0x21908031c09020a060c080409060312020c1219020105040305150601140903030304170c0106080123060a120804080f030406030627020c0c091e0601090e270d0e030d 72
    0x540b05e0700c3c10160641850351601c3c00c1c5610407540032088803480c000b4003008101e50107501c3c001582150307007151041401e00080041482058030005003c4d84209080456582036402495100340141440e80c1059a81c3e1190360a14201d242540d42005078281044420b40c0c002c2c0c40c02030f4a440001c3d509040c1862000840e50781d20000d00b001c1c196445103601080d942196000b2100440c50030002401400d68a400c1580605000d1043c03012009124564080510040103a01c2c8100d200400c2030fa5075601d401c141400c2c0d42d008090943d000c110402001c11420420840814210210b4004554652400100504490f6a901724903004101c02e1103070352051038007042c0f000094003c0c0400603a2624245401c604d0091140b4000e038000e601d500411800420174810000345201465132107450f40d58550044030505001c6c002c00c8400b040d0300000c14a0401a001c50403d070b03642649968180710421541700d8540744810440c4400100245002c19060034184501100c40300b103824492204a0180c500081 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 264166276 1250 264165026 264165029
    0x301030b1f0b0327010608060a090203030715091e1112060708070302090a090603021305061c050a06111c051027020a080405060f01050616021908031c09020a 69
    0x1042d000710200f0380c1814580003c4403110090341d4540f00300260f03200b100780645198070442d070841c0158000220307a095a0b0140c00d44080d4010701540c03034107515559040c0300445c1405800101955519820000b404071418040c0541c403245241c1e600950902d00506824100e00a0300d0246060b030502c1032400c1c0c800a14560841641d00700a401650340384401c40007409400c400340e0380070200c3c05001801001980c030040941c0d009558200c41c00440905800075110180c811681044188500262100400c0182440b1510480030307940c0d8900b00382c80d07010507100200402d480c5503400155188403c0a0225011090220020140418075203241c41c0f0107209181d201e11079210703619401642403070081100012150038040d03400c5440c0c03090068020b1440c1e8040713408807554403036000400c0003030b01c482c280c45040700c4005003c2c0d8544000104035499003000d1072812a0411802d4400b003948220b50070b0a400a005400001d40d200e07a000030254011100039401c0c414403901d4001c0d66400360f182d5046010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 264167526 1250 264166276 264166289
    0xa05070b040f150e1002090907140903060f0703051f060c06060f0e100b041202010302070515070315090501030f031103160f060e030a0c1101021f020301030b1f 70
    0x400d41ea460601011541680400500c1103110382140c205059041c1d1180d03900c22025000c42d08100307442e0352001c00728850001029404102e1100152110b8440c04201981c03041d0b0500250030310a058000c2440e0a00076195501c2c502c0b072100030880e016505200c5d460b80100c0204d500c94984c242e0b100920440c070300c5405004200b140c03038440c40e004d2041e03981000c002004610790005000750f40c3d06584441200503640c680c6180c6a200000503005a000c05440903281080d5a4030a1204075500541c020b51019008035002d00036550306200d40008040070750300c905500d880201c3c030304c80c0704e16000c0c512030b01c91b03001012142e2a0400610210b480b80d0481c101c01c0b076250038040101141d201d500762a40c001c41c100d04040c4d402001d000001c010408103105405441800180b040461402200d80c42c2d00694950000207609003010b04045400d0342c040c10761007103060040d078101340c001300c4001c80107100c013005019070341d600003004000b00110070001685c42180b40740c0d54060b060380000645020000ca10030b80 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 264168776 1250 264167526 264167543
    0x90906050c090a1a160f02240a0c060f02070b04030806060a05190e120709050f060d02040c030609020d050f330f1c03081b090904320606010201020a0507 67
    0x8a034211444812100ca0031081c80a4031170881840c079003000c18030140c00b0128003844148211001d40d50b00b0381442280021001c0420f81410503410040781d0301c200716602076606684840c00f03441c91814510041961030b00039582c1e05504c0c5014180078000b000058503140c0501800c00c40860420380c13042c180d4154031000615100003050281b03003122074140840c00c45901000a000788070100f0030008000b000c4603404074060200380e6603140a4407021508035010350b08000c05581b450018a8298044620b010312414005280c58039001460b080f80c2000e801406180e58a01c18009150140412240c5c09540c141903944410444031a444001c0f0741900100d64644842c1095003d0b42d88441c824405814094800d0324059032243d580d100c250048407043d000f144652000c90b0a0705200501c0d4511030f01c019450910b4540d8034000e04c0b005210042c8203560001443c42404018200320024610701c603188508069890f01080f4024104103003d00114196071040001c5065142c200c02522165604440c80 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 264170026 1250 264168776 264168809
    0x102010507110703171e03091507170415020a090305011109151c0c0302030415050609061005040f03050f0d0e0112050406330605030103021f0c0c090906050c090a 71
    0x41c0201e500800d29404103807056054a84207006c0000007443c4200301a4040391042c0c0c3d0486010070310010190744c1000058041481500c008403030780b080303a0704140304000810403580e24540caa0304980080c8000c00004603002c03402c10510501340100d00c404812030012a00e040c01402c0040c0c18040086031485400001040403000600765541c9150469400712050040f100e0410004000f580115804c0741c440405d040f1101c0b07681c0e0188526881004040d040200f1900c40500b0021030250310200402004030801002c24808001c96000c0300552045004200f18000d400c1c2441c2420041c580120402028040b140e030580c2c0e00458454039904801c4c0001103588903810b02c4400752010080c0701c200c480840804c200034043c005141507110b1f062203c20845203031555800c0340c861001f0721010750703c41062a1841903400a0014a2018074000d0800144960180d40c4100c40702c07800760f110444455a0340b0180c402d00250b0f010f42980200c0c3ca05100f4603100c8500005450b1560b540608040075400f20710 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 264171276 1250 264170026 264170063
    0xd0503070602070503070201110d0c0602370306081506210d080406050a061202040b220501030308070c240b06040b040302120a020a03060b0604050d050105060102010507110703 77
    0x403600d480d50041425566043d0300c3c100180c4c1c03548500d20490005080c500305031a10031000c10718400e210140e60380c0400080c8103440b130b84080e410880c584c0c190007009940210010038150302010b0039032200728000161f050440006800ca680650140e0320a03082079282510302146810003550148d001c80c0c01c041d0900c00c0e190001e01a10b40003081d000c0610812400c0b082080c4c0202c3c4c20b034030075480340c0c00034092b99032016142c50a0350034901c80c1c1e00001c180940c1038001460145c100c0352034408040d05040e0074a035000303500864080103203441a85075030341e4001031061643c032506c0c0e568095001d0805c00100c22040e6200f038100d4106444004550684108061020502e078000c4019884002c02d526119a1294440f03611584248412841500840f12000b0384a0001c2900114560004d0055004a14540314100038241c124007e5920900800c8046203594a00350351810041c059000000c00d80340c000b001a084681c00750440c4113100e007404450031051b0000400c0c0050b1f0741d2021810703030311102c0c03082c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 264172526 1250 264171276 264171283
    0xb0a0f021204290117011d030405130e0a03080a0c090609060c0303060e0903090102071a190306030506161106040b0a0b01020307020301060603090c09050c070204182001090608010e060d05 82
    0xf42a2800180503000000c1d1110f00380713591001402d4100f00820802418100040e4410141d9000c00c0ca148c0040c0300c200301a24000c103103d035111045010200b180001000590b0802c2e15031082200072032011014003c0900091240302c0704041941000d01a25083c0300700941944050308ca10307020403102e4007210040503c250000c80081c490401c03c800c6c142820114151641c0110410304d00505c14580002880f901e466864040c80b13216400e1a8a00a66003e648001d0b1301d48902d03007030600d0703103c0300000000b40082110034800d506807414600c118911640040407004506100a110351014080c04086000c442e0500e07004500c01c00c0015581845100603400c6008032440a0360651a2100c0021a2501600f001552030704c241651041c050302c410b51942140c0c0245c40c1380500c10402c0c84800d0050a0079030003c180381010070a484900c900340d6a40d0079160b030310311344085416400c0015101c103658022020074003a0040e400d0000d22903040c1650003460040046c402c7d40704211244140c81805403d2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 264173776 1250 264172526 264172583
    0x8100515071b03050705190b07020d0302071215050a140604150b030f0106080619031203020f0c01060501080a140402040c14030f060f040b03060a09030504050a030b0a0f021204 77
    0x11580c50710340b40d52403c065407140e00034842d243c0108610300c2000c00505d0303540c0e603060984240c1840b072400c0c01140d0f02480104002980c0031400d40c03107410400f0809805005003e11200c2c4541d09072220580f11010410580c0e5020700305005131800c01c07121207594420007140ca0351041c01070300c2c0021020380e00030352011001d4050344901c201c0400002844130341c1d421144014140c0c0c1d8507403555415038450400707002e045400c0b521030307401054880c5402d100048898106a400d21100c0c5009400c1070501c802e04200d541c0b01517112201603545000810aa503000380104e41e001007800820400d20078400394155a003000240020b101c3c550300c0003084111409121400880d444100482e5140d02c1d10a00b81903152400341daa442c821a5900101180c3e4a803a0181a807061005030260026456004490b4050001c402c001c4040c01010310001c600780c1c90703141003035005500400416000b814071031404001c807122030001c178070f003280100824440c4400002000d6046603025007908a0416600b41c03094210515 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 264175026 1250 264173776 264173813
    0x4060605060c01020d05130510020d021e070515011d0615070b0a05010e1003120210020a0c1b0b04150302090603070e030618060105060d02280810051507 67
    0x410b61182403281540944030588030818200f00c144c0342c004280c061004003050040c035590049100d070000d41c4458006d44904040881c000d4146050300c0d807800e10091000c0341111000304049100b40a0003401c00550b2081c0b1114404c0401550500980742d20081051007600c5190021101103105030322803448020340c4c03a40c2c64481079110380407450150803801081d14102002c90030400080b41e0190010405401a4070f0150442260fa19566a00130f110f4045002c00c81507010300c0d082d96038806260300041c0b2050354696101c1000c40e0061074004084080c52103205003400c4441024899000703201e08460564809032910501c40c0c0e003442046020348249907080c0d412080c04000c1c002d0440c0c101d60034500c0400114140e079260358842d8840c4141c13a035003010140302d0364041c0004011505051000780307d62803c020002d8540304008124107511603001802c0d843c90040b0030910805207901100342c41d0408101007150403803e2900c00000c007101000010004a003800007241d80410000c440180e0942e5203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 264176276 1250 264175026 264175039
    0xa0902040308270f010f0c0f12141c09021c05030a1106061008180102031008060709060512060a0806040c1a042301030e0303090a1502030c090904060605 67
    0xc4a01c0c0c44903854002440c01c040e2910b81d103e8081940e12850a0580f50007405001c15942c800c09100441d0820140011301090141840c605c2000c904211a180c41490148001046401054100030041403c0e148400e0b58901d040c8048504800c806540400500160401090040f5a0300010361080410001e418010303040c140c191041200203c003602c05902d281c3c1311100100341c2c0c000c0060315444d084612581c0440c081188044003405030902c42e800042c0c003c0d50a00307190a00140c1d03400ca9100766103110b07141808000411201d041000203a611180c14580308102070306e03001010b07000340607140b802e881113040c16002640039110035040f88001c0c2400c4048803001e0920f81040003e61069004059840001c58010b40740120b010040b2400c0302d80000318000426170f0031007444d45040300c551403641003581752140d5000b881c00070400346000c1d031040340c06484c8940e100d1a000141030780c0c40350130f494070a0061040107014044042500c1c0303c0d00c02958070440c0c560711482c10900600c09500082e50000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 264177526 1250 264176276 264176279
    0x120a140a0e2403060d150905030304020f0607050a060b0d0c090509060a2c0109080703091509030b070509030a05060a02040f05030105010e0105060a03020c011d010c1d0607020a090204 80
    0x250300c4110400400c1054610051601d0901d1415020500c0d00e0607180340b804041001c1401820032015291056009a80c140a1000e49013613a0003501c6c07440a0658180d40301009000c19481c19814080003c0801c8601d0351411500703685607522a0301000f405000726985108020326a1076401041022551100507810915203401c0854010001071322880030070311501001034447c008a00c1035001c000d08500b00c411040100c1031400e115451440e28521055407510100d4000802090240250314425113420080714200814010b541c0c2403030000b81c1c01c00c0b090329000c001240e04104442c1d0001c084e4944103a4074201480864a40000603100a0981c41110208064141c0c4d07540600240c0304060b000b10750350399540d0704150036541c0c00e000d03845141303e030000100301b05c1c07910714014000c102180c107000d402c02100c10701480c00c551198854100100c140141078080744820720600720300c1401800e2490325010f1261074101186e41c618041c5000c2c00c000902e031801d56640c003c03004000d0050480c20356613a07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 264178776 1250 264177526 264177547
    0x4150302030604140124060f020d02031909050402030c03060108070212030f091507050910020f101508060108010f0b060712050c0703080d0e0d0f050a1d040c030902030d0e03120a14 79
    0x2000c03184140c0e80010ba80c08c0d00f4510704c034070118850000c08059402141815040343c81c0245003140484400d081c0440c4405c00681a100c9001a500c02c0c8690020a80c0300d1170100f0014003852001000c071021900300f9402000b200b02110256034104031248080809555440602450f00c0601503c040c5602d00d0740042000300d641c020020099080140d07185a800c8201c20000e82c4e64040c00c007290203e50300304140c43d100421096011492119200751a03081d8141d0b14480d103810020b01303800803561651203400002c0621241e009140e02e4a0064038658602080c5071189070009103150420000c0050009810480110410441c4040c43d00001070340da42d25401e84900d0010201001c40083c140035a125010001e8013880e0000f550195944950303181240e020011101407026202100480c0c04540b240a265206e611854940103075030b44002410341c40c680101494008207036200010000036204d100d010381c5001c030b82e141c52031040c1c00c1400e80710b0200324000d6074401e01460034402511000f04010030007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 264180026 1250 264178776 264178841
    0x30a050402040615080f06030109141c0c02100c230c0901080307261902010f0f0c05040e0415050403120501091109060c010e03030c09041503020306041401 68
    0x101e01c2120304210142c0c1d5440d1491440840d1111840482d1080d0002000c443c000c1d03c41d5903010310010000a000402640e6a030510000c0e081c95440561204000d1142c100302500130300d913000602d05140003c005664000342d40303808104000c0c070420842091600c10800899030f441d0700d4034400071400b62510407000300c5a40d106101a41c00d40b040010348000900c0c3c842c040100c0701c887d40c101c204051120700418659250b401011107480f01c04e44200512814100440040b4190544560000c22040450f50a0300195010300034610400740c079060210b22495002001c603000c03662198003000046e0f40f6800e001050901e0301c0f01000006040c00c041008160340a1000d1548480070182008281d8a4890304000c550510503000c1800100700500b264510748a805450f0020300c000c00031030b84002c14001d0b9070540d003050741e490140076004640800c42d89001c0c0248500d40b0408014000301d24995000130707a844901a1000c0c2081100a003058880e000a40044481401300145500240303e40303480348a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 264181276 1250 264180026 264180031
    0x11100615080606211b0d0e010e0c0127050d030302090108090601030b04110303070c15020c09040803130219080a031b0201091a040801060b130608041a04110303030a05 73
    0x740d1500d0014500d4541042a0742c101910b0350b840b40c0e0442034211480f5030302030002e444050301011400c4c001e0911920307100140141d10000d9804503000b40842d46035400c2d20320540500c030054200418110f9a0b0340c2c014000c1c130100f0741c86403140412400c6801000c3d141441500080d030003000c485100e000785501f50b0001c003000340007030782c9030b001c0c542d122101252507032428000100122110000b01d00413640300c140000c00d911008007502d1421026940300e92040c3c1c4603a1100301d10409030a4030030701080e01807050034102842070754003c01d10302c0c5c030760345a824511000f000c030f844600703210907060295200d900607660388201c2407406602403615409000d642e8044d03450200c0000d492005500c04010303080165220040d03040e100c110165080c011603103000c0e240c2c0c150109012005202c0040e400c80240100381c01468000902c581d178559016610000782e046800c504284042c1109100008072425580300da20720f8040f251818580b6245051610194401110f5a00d48004810311000c4617090744030382e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 264182526 1250 264181276 264181319
    0x3020915090f0a0b0a080109020f09040b06060a0e100c0c050103021c050702070b031311150d05041b0308070b0108030a050409020a09050603271f0930030525111006 72
    0x203c4d2b42001c50100301e820102103e00800304812140030509506080b406840581c400d0305080e0b03040c0382d40001003040e200401030140c00080c3c0a6402d00240140c0010600c040c20080c0fa0951616900c6020002140710070100405c00071b90b143c000a442c47d20a00554018015625160f0b6803420402c0b40c85543c03090b034210030f540385c0b500800c4000061410710b82d28001d5440c4101000c0c1442d0403041440d00404000f0029100c0741c0110410301000201c002c801c00c0039500c01c040761911420f250619203003844050300641003d078010404901555004000d41c0d04035100c072100541e496050b10002c5035441e84690101e03410900120910003104214202e40b4480580404d9041003442c0303d244d080c0d51046000705032104501e00000e46140c4103c80c0d0840c40201d8010b1021002034048800103881402408041094501c03c482a0303a41e000d42c94058280c01a0300003146a801000204c210820100c2e0700c0c00320014031201d50100605041e0501c8016072903945c0030410880380d60740340c0304600380760703440c001e1701 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 264183776 1250 264182526 264182539
    0x31504031107140d0807030c080a05040305060c0a0206011206060b030c0405040e16180b030a030503040209010602060c03240a09060603060b07110409051507050403020915090f0a0b0a08010902 84
    0x220301029a01c0a444403080f0050500e8118810741e200c1150aa1203007100b0390403c078502400c0400b00300b0ba2002080305039071903901c1c0c0e9619882d50600b64100280079101d2906010308000040c2500e50010706141558071050603000d841c18146481350040640d5480942400400b000700000503d620b03002c2d0003150402d4034107010000d110483c1a40b5403241620955240c042c5480901c420b03012039425801e482e818410006401d24000d000030b01e4075100c00700840024000200700030031801c0c02500c41c0d005001500080095003030000e407114040c00014011040855100f0002c0800c9071039040e00802180c014001c2108030740c0f5a01c100000d00510f02824001c64200140016080202c804842c4e140c1d41100316011505142e00070000600180141a40d1603c038048220300f0b212400d000c81400780c0100e4a502d680c41f80755105000000d4001082000f55034405451000142c131548521640060f8048035400241e0319168204003e03c186c80c9616084014000086150b010552164200d1402151035 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 264185026 1250 264183776 264183779
    0x11010906081b090111250e0103030c0b06010c061b09140f121c03090203010b0907020307230f0609010e0d0f030b04140a0f0e0c010f0e031504031107 65
    0x70354095078280d5080740e4004540b4022203420b02c2d504050a402c907070501d08446820b008089540ca4600c00e40d83c401b00a84030313010400714503600c0181e060010281241d2500c500d6146031405000d005482402408000b0381500041c2c40b684170f084103a803041d50104080241981441d110300e2901003090510020514000e0089400548102c07004241d1000800a00346032070010180328082d400c581c0e82d120780d44141d0703a803141d40d584c0003822102007182c02c0c0e4000640d404640101802e4072913110361103004501c2c4005200c0103590201c02c8681340d40e0070480308800d101070200380d0303032a85014001040c46030140040c20105180d0200b65503028022402c024400207000c1194a41c0b145581d4500300c0206421110381d040302c50081c1c0000e5041200104009510201c69800c4227241c1c008072803e0301003c0c0da601ea030140300e29a51051141e5003080d040240400540e8500107443c0000e914440d205000d45114004e2013544c3c2004406c41d210050510f40d030341e40c03c0614010304449a0700c0c54480302c50040400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 264186276 1250 264185026 264185039
    0x40605071d2206121203020703050a110f01020c0d0e030c060417030c0109060c0315051c02040f1109150c0304030303021b07060e010e010507051c0c050a110109 70
    0x48951080c00d4a1080c112240d03004000c101d20100700850701c0c900e1480b51144900480460320a040c003c1c0a032252110a08410346026081c10240c5202e1009040c4148030640c0800d07802401c0c2d80f904409410001080c8800880d681d240055003000140c9943c00055089000800401c80440c240c40f0b0b615901210081c043c200b649030301c50440125008074080c44100140030881e9100748144d00e403503007a2403910110000c2117080d144002820707140e0310345074141d40003911b0781807042d50441da00d00c0f441d0021182c1408000b03905001c82c540601c0442070709001c00007d40d074850380f1042d502280c0b40c0041040501c0c42e0074a4907290000108184100501100c0c0000105c102c821100100c076010003840c941815554242c00940146401403200c04101c40c64940d403500030441003002e1b060603103920b86001280c00004240141c0300c0c4403030703040201c1071109800045000800c0c4201c480d6211420380f02400032142110012110103014145201d0310f00a4010322000c045441080107081c2d0360035800300e890b101c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 264187526 1250 264186276 264186287
    0x21e01020c031e040905090a020a24030f0f0501030b0a140408160606080f010e01050705041d28020a02060610050d050709180510050d0812041a04030804060507 70
    0x90a040e0002c0280c3c3d04081202e803200c0c820000c150000b50b044c2502c0701c800c002210030403224543d1592096200b0300a6160014034000109048100f4000496086c024203d2160900381c004041c1504d0351411034480742e017030b0043ca81020401108002071b41c0d41e42030009561a00f40d403850500c9182c10300a11a40c52440c1010348103e400004503460100b1110900c0010410402c09403040d5039145000300703845c0400d0003c2c0f84407101250012540440c408000d908581002e0180c0007801002c0100300807107014035941c00d0806000e030b445642c05503103410050445030b145034086a20007103200c0450809422950141015680584c211140c640d10724013803007400c102c85043c0d9070100d8070070321101200c178805c0d4000c25800003243ca45501d969940d002c0c0700202220011f00301501b184c03580c04010a04500c120b5040050808403601c29a0169075110703c80d0724491079225452011540c00010305000d20404030001403050a10204c1c0c141c81c0c541001018500c0c26142103a069007000041600c4a1291 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 264188776 1250 264187526 264187537
    0xc2b111318091a090712080a0e0f0f01030e120a0207080c0f090103021c170405030105150105070b0c0702030709090302010c0c050309010516060c1e02010204060e04050a1407021e0102 80
    0x2143d03070190070094500480000000c2a05a0f6442203000c0420030581c4c0f026a0001c0c07078030030442142c98084c2000042c107078034030300c05609003c0d4a22000107505552401d44c402c5001c0d03002c0c00c1c0003c103800b4001240b07050203400e003124040c4c01000101030200ca54000340c041c08584903401a00c10740c5880f1401c003c986500303600819800580d850051000d45040d003041c10303005010000d02c0074030489503a10003580034144400580d01c01400700e404c04c4942020b025855101d41040000b2004801e12800a8010302800002420500c80100003c82040f2900c048070440f6800404507848030307607100e001c50f002c0c140e0940114015400e140c502c0180601900c403440505070311030065401e0942e400011111030304000351005068451420640105045105040a6608a43c3d884440c0600c441c802c01a00e0b4000d07400340b04581c8100810860107034024070341d810f128402c40b4042402d8441d030070950060005000c0400a103900681881160741e00060580040b0649286003468071106407a02c908030f0045 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 264190026 1250 264188776 264188783
    0x30301060e01050a1101050106050d1a030303041101110a0c06091509060f0212130e0c340b09070603061e0315021b01020904050c2b11131809 62
    0x40601c08066000b207000d05002001850460032140f000c94103d820750b40d01b82c0c005d0307004c5000090242d5150000e40900c034100040c0c20703105010b12040700c0200350b880c800108098140c0b02d11181c1280340740e1042e00000202c8001c40c0889010914034142000c0342d6400344114004201c08250010320b4611101480340c0200140d02ca181809140c2403059541ca039190b8880c2c01107018000d0f40100360800c19001d4050809500302e42c120720b034141b04400c82c003003401402502600c1020300429131680c0fa06200714407140c4400401400569007155903c0d00210854401007500010038100a43c04500180c0e5034100c58031964140559031340e90004401e401c1a11120742d010f001405410320120702c0b40002000703408490000140392001c0000b40c01c46100038010780b210a6500025203200d28a010f02400d900840403190092034800164070102c003480d1156803c40305400d40c00300301448051182d214840c0c4002d002e50311540c0300e0b00340e01c02c4240414107011307001441c2944480144444001e220f07820381c0e585d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 264191276 1250 264190026 264190037
    0xf01030201020d111c0201090606080102040f0b0c190501090c1a0403030503060a030204061211040501050d06051e09010e0f03120705070c030f060b0f191a070f0c03050d0203030106 79
    0x41c8041c040300e0b55544c2584801082c415401c220384040d5a200b0030340c0358900030351b00000b048405898440155105a4806c0d03d02d0307070051106101511007e0002d0302101c4501c1282035030761070207840881c02c0c00140c00300d8000e60342c00785102905000f01904545111845091201407944e1154007680749001900400711000106010600019000c0c800454101e80020441c0280307980d2507000806543c6950042c09504003840e01d01010071100c038110020a03c006c45061200d581040007207040300490341c4002c0c0145403074001090322142c00030040095241c0c02e054401041c60700b055070310702802c106040da803c03910032500600ea240502000fa036000012000e039095194542c680c0854094000f180306035048040d40c40f0000008113091464031300d813032007500b001c200c0051400c1006000031034604000e0040224524002d0000030700c0d00d1120956103640c010300b54680c0707031520b01c415500030108002d01c000d0b000385590050089400861081b688503008807064107400102c00c0341c0300c0c0001e206010120347c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 264192526 1250 264191276 264191293
    0xe0d02060a02070516030309030b091b100e09010e07230403020409030522050406050f010e01050f070203010f0b040b1f140706020a0e1215010311030705100203120f0103020102 77
    0x1000340c000f010228001c108441038030b100780b48076000042c2c0960040300842e140c49010020000000030055002c002c601c050506001c1c281c00c00055402460f20140c81545100408a2418004c040d1070103000409441c0c0403466031114001d044188056540c1e0012695140c10342020301680e86172010300c820980a50340c280351542d806d10024000c84001141400780070b002040d0b880101180560700d04e401c00000e03040381890041031104076207150304403502500403203001808998024603403080d00c50080c607000703543e80140707420509680903403c8001c1d85035013401ca641d400f2681c96009110307a040700b10b5013003180003000030411070141d17007001e000d0100400f031803410700c100c81c000c0038548005622100d041e440e00000b9030b10724040703034004a4450041034010a03c6101401d261010701940c0c851500200134140501c00c030301c12401e03414800180744920700b0740d84000645080c05150b000f0301e0068030340d000745001850080d4580d0411500d01e9400740c1c1440001d00010701d5032a002d41204c1e01070300940a000d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 264193776 1250 264192526 264192541
    0x627050a02040b07050a030914010f0818010c0207080d080115030b01031427070602070909050f070b030f06030c180a1b0c060f020c070b0a0c06020313060e0d0206 71
    0x142001030031010303050307400d00000800c95210320041c40350512030b501a001400f903529000c2c00143d0250000781000c81ea60305c1803007850343c100001c0050001d00d810504142d80d2902d6224802d0340c240c80c160340182d42445c01c440300ae16000103008060303946180540340c0781d00e00840704640f030071004d2182c56a00b81c071022011601c14081c2d84407a400141c185004900051282111000c076801501e1445640c40d02c41a01c840040c00804082580d1a064000c0d280d00c80ca0002d0080d0f8400c0070f8095082d0341035460402408204042000450080b680400e6a407480c0c0c1c0c62a03424560b400c1110b10058552954000131450300c0e02295000070004000c049103d88060305140e001c26250050018080994691200c0442c80702d40041f081003464070b5640d40d0384038415151280a650700e01c400c1210b460700500607142140c0010482e0019108501e0741c041e160380450804071460341c003218006e84470920000134020a41c80a40002055900605003030100d0600501103642d01c607070050807200141c002c0c5021840c0c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 264195026 1250 264193776 264193781
    0x40e03090d1a0c032205061b04150509030d030c05191704061e061d07020a060c0c020f01050304030c08130803040e0f070f050306060a140313060627 65
    0x42030103418581c00601030600944580c502c1502c0d260004080841003001641409080b0101110b960780d01945c42d205690b10142d850384040c1c00901940101e040d904000c041d08015900100591281e0240a10710302001074802d91004006600034001c40030b003205003c1c043d016441c182c40e00f070f81e40c09107050401c1107102c4622414580300707030401c2500c1454482c82c8150070030160146002e04400900c0b16403000c000c40131440c0303080813810a203081507002c21401201da00921051a00311400f80500c1d55002d008034106604018010246894642070901d41503100510202040c03080d01d03c245981c031060f00540389800111001000520a42014000915a2030140c8264640559904a100c0c6c980c00d52604541241e040328940c903041d1020403000c00920043c040c2c00914505004507000610741d801004c51000600c2c50380281000240600044d218071401c2c405ca08a01801c00d41341d0411142c8807608400c021020707540c5034203010700420711098000c1800540368001c04518030f8101040e001501 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 264196276 1250 264195026 264195049
    0xa061704060b0d080a020c1306080303130201050c100504112b02030102040f060503040204061514030402010203040f120215040f060e130c05070606080a02010e010c141204030c05040e0309 82
    0x1004120307048510001071211000e01050003c540203045402185014081c411234814401c1800c11b0819804114508000c021030707030010116a00c8498a982da0700059410b44100c15480c0c9491244840e21429020307164044d5005a20a410400d20051258100301c101c1115080098900700c605407070740200708415084a50081c07020b00094140381e614404142031003101e92007000400d0001080100b10300c3c1030301c00c0c50060f2a030040445030f0301c0e20307040c00108600c440c2160f98134002c90010111703040d68000c1098500601c2100d007062840354944901c28aa04406e6404038016107015070302e14a54044101034806a0b90007034200590719103050300403180702029110312a0440b82c001655544401c4134041d01101882c10785030f10b40d4a4106140807400c0b00c12030791084049030070512180d00140e0384040c4400b04110246051020742e401410418a111560300980e461031090384500004460400e01402c01ca0b03018100080600340d4410034041654885c418114803500700700421110b41c608402c83c0d01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 264197526 1250 264196276 264196279
    0x1050315030c10020309010201050a1a060304031b080a120603170f040b12101403060403050c1504060f0609060302060d020c120a0221090109090c11060a09020a061704060b 75
    0x240d01000b002c0201d80380c41804415040141c100049110265070240103494010b4040740381040380154201c14a8510051030903103510440d400808a02818446c4204405000e65215041a5645246040c0400d6840301340d095002c07903031001c1010110005031254408480c2c200da80c0000141031490109001d60228150400c003c5040c000070175100c0c0e192026103200c03d56000180c0d0729060500c00445003c1080c1d009500a1100b26403090305901c01140c09078000b541420b0858540c0c454031212420001d1812811440700314038006c1209106941d00480c40d11181c00004001c0700c0d8484d035490098445900001e500020200144e1512494590040240350b80d0103040e5820b07480800030540e0703998000440d5034016400b40f00000c1c618500c00c101c40b00504070000c5214500600360700060011071491040030820781e980d50008008034001d40060b0b0440d000c04090314010700c0d0070310411006064000040c2d015402c860008280d46000303c08892084140c405101c095603915a1200301400c18400c805 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 264198776 1250 264197526 264197533
    0x20d09050102040801060f0e160c0206070f11150703020307080c010b09130b070306080a230d030921270f061101050601050310030b0615030f090f010203060105031503 73
    0x28011940a00c060800381c0019400400c1c06890080c540115010710380004030341c05c021405101d00c0b008008981c0308000014107017070065030181d0000541c54051500c001d08070b40c50005258082205c01c40c2152a082002c55140303203070300181283c0000c24051101700501692040101c0c502181070b1360040c1c142d0200344000880c8559002021a0102d48181c0324244d40c40d549030540e204010086d8041e03540100c003031500f00070282c90b01a100740d17101c94104000c8c22040d4404500207100c034808003141c24540483c01212000129840020001d054914058a0b4a02c421034005114404110140b00842541c2e4980158008152000108c24034000c20a1604800000c00182c0b000c0e074079081c5402450103456108103240303481c6081b825508000e1900d41040000c01c10042d602c40e603810780c2030036603420032881c00180d5203c0c2c001c502030b9603036900c8012200401000708150f000151071801d1284030b045060701e004124129001d8280d000543c0d1035400f00d0001d00010f001d84070b040d010340d03900d03007001002ca = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 264200026 1250 264198776 264198791
    0x6030b041d06040506090109020f01050a0210290a0b0301061404181a03060402010f0309050f0303040c0302031009020d1419050601140303070c0e071e030c03230109020d 74
    0x21041c40e406034001c40350035400540820003400404d000040d030002c0c44034001d110030ba08a0f400190b80320025800d03141400710210b010001988200407440054050000820505c082010340005110001c200305c1401241c0b0030a0841604007042001e00b01c0c0c40001486055908250059810b220000418006c881040c00005540e5213240700007284000d000c0c01c00202824500003a2000e884005007050081d8018020703c80180d0307101d00f9541107010b45240000302407150349040340c200b062440180e00c0034030010080c003041c011225241e10459108504668140c908021520140c480d1210003030352050b01c80d5500408200c00e1900020041d40382401e455150041d45c400400200c7c05a0054a16921500041c0811403501c0d02203400100120010740c20100e650782c81303100c1007210b070061046520120000c186200c1c090111034005600d000007102c549521864000d0040c4000300b216000203043c001d02500c840175521500c0e10030b110b60088510740740e00740a0341038042d501c44510000800d0343c6818 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 264201276 1250 264200026 264200051
    0x5090d0b010f05130b0a05220615080906010f09090303020f031005030f0a211404060804150506130b0102030906070b0a0c14030103060903050706050906090d050405010906030b04 78
    0x2440307001c0e20701000d1080010b81007005005000c00c00d0b88440d596035180c0088104241c1d40ca6199604440e000c1340c0d0041140d96403203a94405001d44d03041041102d0a0100105901c503103980340c800164013543c3d41034156681c50711003d6031548284540c01c0c0f4440f652800f806441c0c0c0ca50080341105c8d010f41130151803d000c050241106070320407a0b060082c0200c1c20414030461605020300311384450024000e00380034156844d880308281c0c4551a000b4415002d18503500003074002c3c9000300b40a1041040c182d2200d55403030340581441e80803a03003101e821401811500911405216050003050f003e030008038000300c1e400c0280010002e10395071605501c410b015000741c9589050092034450b10840303c00030306017850408482030381c10340c40b068001d101510403450201075102c0140e03030441790003e030040b8607aa46410150b07064400c01401034401424075080110950002442d940504249c900311003609a42190440e0b05010f40d0042a0020740e4813071003000384034400c0d0003c16030450020400200c103000b401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 264202526 1250 264201276 264201293
    0x10c080d1112040312020406050901081305190515010303050723100b040e03030c1e07150204080c0f09011503020d0606030605191202130e010504030206060a060908060705090d 77
    0x4810480502c0b002c4100410168446904000d070a001042035052904207500a815805406c1401d410809020001140d6012200b45e0125058000301500c06204e51448401d881410b0118140d40070301c58460404030418456407814120380d007558545040c00c0c6070780c0c3c40340b098603a07030900070000c0040c88000c0c3c4426402440341c3c00821581000000c0c0c03004080041c4801d442c0100000c0840c4d4000b48100203403007020b80c0c21650351050700c90a0b070110300062541c08a4074011420f01410128a0101e00d0445811640c02001038a00c0c550448150441c200100941e07800600c905075000300341c1000401442020940d4a0361002c0181400b50074400c004084004944040d0f000c0b000103030700d4840421031070804240c07981016031090310800c5180e003008101d220400740810024050f40c1100c028001e80d41d03440e40640400002000207011a01781742c20000d54440e4181c810903c944515580014244c0c0951401c070b0845e100d180161800f50748941c000d80f607a03002401403d8000b0113101c0e0b43e400144104 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 264203776 1250 264202526 264202537
    0x50c010c0203031e0105100c1a0c120609060f010e0406030813060e09130f021503130b0105010203070f0b100f060807080a0207050307120e030f0303010311010c02010c080d11 76
    0x281e00a545911303085284090f5040b2152002400c1a203a400500858a80441c222441c0c0650305245e070302e410b540e181c241c1c030040949103201d8407803c0041c1031242d51920100240300d01c0000c840f11850719140d000400c500902c1c10f46c2c4982e881955100305d0741c01e9500610441a0303001c0e0041c00010105e5803a100d2202c13503407046221414165920005121f220340100b904600800256014891031074140844680d4019441c03005d4001c4481e6003c40c400c55880301410f4a68000c1d40d0140350306c0b82804006070082c4014060111111051140081055440003007a1414150841e040442c04e078120703103c1186c81c01001d4a00359001c0400d00000c0303000c0c0305041c9900020540c5565007a042e18140600511849015040140660041041d6004983c00200b910040c5170030500c20814038560761400c2d148445e03010600d6405000302d0403805001c0d80007001441c122405110410740390088003004480560b540e0100034003161400301c440c00404e0305040501780102c0103c400180070320050180917101c0c1c100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 264205026 1250 264203776 264203801
    0x6060d020708130f050d030c050106180e01140705070f0507030b0705120108030a0c08131502032106030316032a15050c03160e0909030a111c0c03050c01 67
    0xc0c803090751220240c1003001000c0d00c0b80000c00f41c07410000060040d01b182c0201a0401c9030040401d0103001080d441000105071074850140d40000f402c4101d0003901d02260312164651820000101c0304140403038040c1302d034803d580d071245010b500703070b60342c0c00e00300c008140680e903520a4400100000e090101030318040c1e0550745440e80c55941c0004600b00c400380580001c01e003504103000c410300082d00000d8926140d940028000c0c0c80da81c1186200300e5207200759000b082c15840c0301d00300c0e01009030040000d01507904000c054040c00056290f10b1902032500303a5000e605039008100410b01401211007111040703200707241031119850000a4903141c4170b9006009126980440000e004002e4104401c2c014800c48880c280a07618040f401da0b140390200404554004041c0040048540d00c120b000a10045c402041c060080c10f11484e66a541d03040080c0706404240c4418078a1214800091300280d605240903c0459030705e0a10002c80b800c2400003021800c0c81428031020040a4080c09120f0070400c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 264206276 1250 264205026 264205043
    0x3060212011202010c0308091915201204021c06060f120b01090506011107030b090d170403051312060504050d0e0a0b0a02030f0a0203030118140f06060d0207 69
    0x65416840c0040141a40001e201485011000d030040c1d0704124007501003601801c203640c079030740c40c6c0c4015802c10705284882d9180d40e07140d01d800d8080014981140f003003041e5440701040f410401c4d40740482aa90080700c1e6130b20864091144150700007038a034000da4013610181154400720540d012540342c1c08a401e501700c601540382e000c01d02011116001950040c60b4900d11010350305515142c0e800c0c9010180100d0720003075101e03000107210340d020702540c2d007a500984040f01d0115a0701d040c5030304007a0080d10502043c0c011080c500f490302e40b0500c074007120100e05040610094480740e4064030030340d120200b014058600500001650340302c0c2c0c1200803071207004180109a42c13600d468100d050110741c032680024071081a48030422526440c1c80001514440d00e4065980c14001c1400d0b403540c003490208404242c0002007548402ea4044080c60481380817043c068030b800503030788021041d80c11500041da1f001c4012000142c2d40c80810b52507507004040a0a16842c107000041c0c00c800303076440858151889003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 264207526 1250 264206276 264206287
    0x30a050318010c03050d2a03140c070b0f0613091101120515090901020909040521120703020a090b0c0115080d17070e04061202040507091505070318030602 68
    0x107680781051052400340f030990035080309660702030803500500306990344280d038440c4440041144100c003107125104425204041c0b0401d000700a029010040b0b8600ca1111040007250340c0780e0b51281594100f07075006e0306030252541e420160310f0504000a040c41d501202203450210209014410082290300842481e940f0032588800580140303020b2164102261416040000c01d41d148820040303036480480700c41185403100d0400b1400f900400220503400300410040c4401c000340000c0c0740c1c042e0849070240b441400400070680c483d60003041c0380e4000c0400464001548a48a940201020700480c18944030894640201100f140c015075000c0c2c1e0341d603650301802c0c401d615440b690030004022020040008070402030008103068024050b40190340e030450041001c0b203000390018505150b0140040280a41d14041c40e0810180140c0a070b01607442e040108014a208002400645004681000344040d003100215010303800700300140c04100003480d0400140398603c45a03001580626009a140c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 264208633 1107 264207526 264207547
    0x4021e0f04060e04021c0c0501030b01050c071401030e1605010e01170705030a0e0c031c05070c0801020c010b0102030c19140d0825050d05090c030a0503 67
    0x20b040600109154034803d40c8075200e0f500840390104105041d550940d14051943c8002e00b02c0390707070040c061000354040e03080a403004d14185003d034600040e69007203504280190300034640c402aa204001600e41e8103000b207041e000b10071406001803020520f51100c81180c0740c41454144200c0c4e00105044c0d030b005219403400000b403a0202849490704c548010403a520445803010b103645030418030002191300003110703c40f80c200a0010416003100c6120701c0c03180c1c50a60544400c0010070000c1c1c0c00000c03a448034200007000b03100c002684800300f45500d182504c8484103003d04646c0240551000c2c44d02c00a03449107038100350040340101c074280f81080316800002200184407849004040228550311075001d6100320410100701e03d034500d80c440d030034504035004522003002030804d01c0041c0e1804c6031680900c0d0003035100f074110b541c0008008007090900c0140d2400740c400750808105400d04 = true := by decide +kernel

theorem cover : BRFrame.Cov 264028776 264208633 := by
  have h0 := BRFrame.cov_init 264028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 264028776 ≤ n) (h2 : n < 264208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
