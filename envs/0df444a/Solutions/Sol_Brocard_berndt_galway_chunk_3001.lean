-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3001
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:22:24.467132+00:00
-- url     : https://prove2.me/submissions/cf294be3-ad56-4449-8beb-4e8c37829a13

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 539568345 ≤ n < 539748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 539569595 1250 539568345 539568349
    0x6011b121d0a03020904031101060b072306010b0d0207050604061d06040506011a0f03250201060605030a0e0a0b0a02030a0b01080402031c02031309051617070c020627 73
    0x500000c24401d05128035450101c00030510007122403100900411301400028281882101c41850180020000b481881e07610a40700001d600516001c1d0ba8040c9a1002c5041c0c1c401c04a2481d00c200711001c01034002c0ba07182000f110901d40100c280b80d021079408101700c800242082c840c162242c1d10544d000035054054901078003101018100500490307228100307110226600003507580c1103035117201c41e0400d001e9040b042c140c2d85000703030700346400020404024071103d01c1003031a88081e00da0205219105040c1c40c10003c034241c407954446d110106034100b0202c1c40c07410072604202d80b03048543e4101ca00000440e56010385d00381003100d0031106130f50701205002c0d21300e04a010343c4040c01c01c02d1a141269007005d800203600e40345e10005d40060012030f0590072021600070300c00d848401d0743d2414280100d541da00c0c00e00000c1d003000c440e910800c801e0584440001c6000c2c003103544002490540031115030761002d1042d200a88202000d0340d11070414020161004607101d200c91401ca025413a614801c4c80241c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 539570845 1250 539569595 539569607
    0xe1f05010e0903090114090118030b0402010305070801060c080c0c0d0c0306050a110d090203070b040b1b0f031c090c0f081005150f0604030237050102030301060806011b12 75
    0x2c0010160820051841e0f140c4e801034003003003d400b060405503655010100181c43d1a054161030701444039000c80e0000511811000e0f0034443c5001380c030280020780e1380c0141280d0b02282401030300042460400aa00800c000d10043c3c624244e00c407003121540081c150002e405032910850440303001d94400e10900400180b80a025041001e100003440110300900700c5400074000c0000c6082032543d5940d40006541d0304004d608014030184850b03da6903502c44290761200c0e401815400418982c202c016050b50034000354099040210102640c100404040e1150703104d0f00c1801c00f617443d1501c03040032002240b03040c50a00010600b040e4508000303032803c03070000c2c100b103012144a21250300c1c1908101c5002a2960304039a0f5600480d041c1c044c0d8401040040d83c1ca02031508043d402031184941c4c00c45c50311460150710202c0350b504d044602444904082e0b117111030520b001f1640160002d000400c42c2e14080e14003207810840504140007030300c0c5030b80260b1010002e4a0300c00d80700920070308610101d40760000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 539572095 1250 539570845 539570851
    0xb190e010e0f07080f0a020405060f0d030e0301320405031b0102041502061b0309010908031302031e2e150501091e03022b1103060115080a0e1f05010e 66
    0x4030142040e00b0030542d0491b01c403031020b50301078010f03519040011810394454403800c1104c0001000c0b200c0e85011410002c0c5213803485c4000328020740c6000c560300e50022000d124041c5003201030300d22a40181c0e0210a00c003108a000d04111420320060104206200b490440072401c035950f20001600e8614003c03010001004484415081d074002509001e00100080301c4044001c0074085840d56a46598041600400f8011070141240c070300401440035128030441200f1109000b141110304031600440410724984c00580344d40c0c4d10764000ca2115480d0104c450030f00c40040300000c007010054501c1406001510114079150418524810080c0010b42c0c1000c511005000008524401c400c0404a00e40b2506464040030f032003400341002d00040c000c00d11301c041c0ba0326011440e213804010607a160140110650040702882400361000100c0e814408003d010b11300612a91095420344030451881d0042180d854181128000d4070a80c010b043d240c0c0e40748000d000c0c0412000103056140c0928040420005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 539573345 1250 539572095 539572109
    0xf07030506010c030309051617010e060c07030804030212160b0901050705040b13030c0305071703070b07081306060b0d0b0307030302031926040201030506030a0b190e010e0f07 77
    0x10074085266840200743c03140300d0f807600780007483d0300d42d50600d580703803940003100070700802d1050a01180381c8540e4241c044901c00c5000080c86441011030040791a540700711115640f21806000b8000031a101c0ca01668000d400b1f801030301c8030b1980b0b0306d120181c90b90105008031345100b5a003038844100b144412905500030101802001307141400c1c1c800410f207200d5486402c1d480c1d0f0011907024084a168a81240110b0b0700a900810b425030360b141854803441d451040170521107210048902140b0003004494503180e004843c2d03200c030341c1c07918016a141c1d40098040b100c00d4041311005000290b0b10300c900000780980c40d4010307440c0e03c03610695600307442002c1d62480c0a03800603202003001a800000b44d0701e00105004002e25210f10b284011900c140480c5c500142c0341d1920141d000c00140c00d00341e103030701950007a60144000c1d69003009040da030b01440f144c0100350020303580c00580c248400c07041c403115000c159280450b00030300c146155401d441c01c0c0c01078500d042e04140f04100d00c0010802580b0010030300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 539574595 1250 539573345 539573351
    0xe190602070b0a1701060e120106050f0d111009091d100b010c0c091407050715050a24060807180b0901122315060405100201061205060f0703 62
    0x18844000d4480380c65100d00c0d40c81c100c010840390300440c02505140100746820301503901c1580d480100805400c4c407201c025024000d40d0306a00e0403200180107003801d6450103800000c0900f80c0c4030511104c401901002e0351414480116001d859581c0b00401800c5901d9940d07500c4d80c4c0d8286400c107000c407016240d000400c0b980b2154800d40c499000b15020514844417400001d4060488005840703143e880400201510312440e004a00005a80e1006142d00e038292030004007590781d980159400d20034080080d0100044040a00349000550040799001100160201e59525080135020300405203120b02e88003604103110a12609911120043d0f00044038501040044010360400c03860013180d0040a10507080012204141d9015480d045040c102a290400c00910fa050111100b40c5000c244070aa0326001400303c3c042d0020701c8403921520b03000410345441d051901c02084401c0c903541c986081555200c074000035010402c0125106e886001d400549160714050403008000c1100404080a0500d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 539575845 1250 539574595 539574599
    0xf0a03020603190b0d0512071103030f0d050709180b01031805060426030a05040c0b07030302120a0b150313050607122301050d05070b0f0912031905031503010603030e19 74
    0x2400047c00c2d4440102e4102c065541c08181c107162000119040255070140320000c0c1e2000c1811544008104003000c8010400c102d0311001411101c181203441410b0030540b0010031903800c400e06500c14403181c0414140002c0f04101d0200805000010318001da9160b00048100424804190100f09212864400c4aa0418021041c1541c0e9010140c0002d40d2075580b00d0008007084045005100a031000c0450180c9501c0d0030314008000c0d50003041c002c24951080e9012a01d0210a030250b194000300c01810107801103450030b101420f030b400080108060381d040c80d0956010078801d1000b503001d005980d075402400c81064109400b030318001c12104008103408000c010035009803000140c1560422540218601c1d11414001d18101d101d8014520702c01000501c80d0081b501c40b0002e080301c076410380b25030200b4148201d441f501e90040e0000c030b1460503c0383e080501c1080c850702c000c41d07004080c4501101d00703100d500007090840d010b80d04120041f03400304111300c001c4c4c905030b4070f0359810807030740c601500c00f0078 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 539577095 1250 539575845 539575853
    0x10501031e08070b040b041b0f06030f02040b04060203030610110d0507061b02010e070e0c09060919030501061a070302070e0705090d0b06100f020c0f0a03020603190b0d 74
    0x1400d106801121507070709500074040000010440d40c3c01a000400030300c0c541014200040705590546e0221081000e4101c44180b801d410300e110011140d022800080107880c0440c103902a005130301d0a00045d5a0811003c039240b9003010141c0043e0803294010350f200d1410000303110844900f60b40140c144040d03200034800c0140005202c04040c40c103454030075100d8a00340f500c000980000f04020042000b2180100d20540e415848841d02181e00e00440b000c09a44400304485240162880d915140d81002110300b1410030000a1400840192108102c54400403402c2040d80381d80d0402c40f9240d441d00001c1007100501081d2a030700c4028503080c0c0d0302d824000d540181d5214118030401d4220300807440080d01c540c1c040d40c1600d4008102170601065140240781c10304250104a03002d5104050480d00140914401e5482d001d4460a54005101d092080c000300400c101c1e9000c0740c01c0e48903170312070008801030f00c03020051801100d4030b0a00c0303c054180b5410100c191000a01c0b040c0c050b01881d52901d02103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 539578345 1250 539577095 539577113
    0x81c0e060408041202010509060309010c08221205130f06020601140108130303020c12030118090b0f060604090606020d02010e0d050702040905070b31050108040b0a0f050a020903070801050103 84
    0x7103215410f1101340001a2005965034000d21822a50040b808030030450032800642018252606030341c2d42e51010380e00c05100b030510206a141441c90010501c0d0301e040080c00041c445100c103146414410304101d07214050551118691308942d146410381d45040000a404000030b50240c0b1502c50009582042500001d003250b8005040c001008370705a01c200505000b64122030090060205454a0f030401d0506107160382c1c000c1c450030401c14840742d801c08000f041d92003031104143e030220003500c0ea41c50301488410307031140242084d40e10503401c11000a00100f0762142d82e000b482945c01401d4482d19641000e402c440c075800c1400700036086071507000581544402224442c1c0e904840028118205052403407800d44140c0100c85aa980003c54002e85185001c007421042c010303541090034900004a13030000d40d90b542c410179011031002000700d40020080d0056035802030303443d84000b072482c1d081d91281c03040e20010390740801c3c00783d400920000c035800c0c14403400e0081d16a00c00284110d5141d613030390b0221 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 539579595 1250 539578345 539578349
    0x6030c0612130c090603110a08191110110c1219060906110301050913020d02040504030e100915090510030e07030b0a1401080c0907110703081c0e06040804 68
    0x2901420600207010304810701c9080c0b03400c5410501000a0720307112a440802082207000c00da6101c00d441060b04454641100a00d041e220718001822001554403400e000b04032103039000303d070405020300d0b020b8408d40380c00014140c03802c05950b4065506001d00c04590030a030b000c2600e40e01465a9800c0b010401c0c10010b6202c0d90024208208030441c60b00341032010042c80e0701c200051103039050400074a00b0203103d4002c0d505aa000300e5540c00f040d12241c0428180c0e16801c41c0c000c0d00460b0401481d00949019071010768482d000e41090b080744400c060015081501d110065800700705a100240304112841c3c95159402c210380c20801c104030300300720010700551010440e110030152144078041c1016001d00c80d01005551060241c2001c0c1403000800010b03180e2040f015008130300c07260000a00d0b800024506008440140c0014125180c0300421142808487c1010b40b0502c554180040098410001041d180403100c41c12110f4144c03020f0300409490340c450030008a0342c0588184400300d0f26002c2145d003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 539580845 1250 539579595 539579617
    0xb06010f09031b060807090f03030806040f020d09060c11150a1508030a1403240f0a03050a0501051602030f031504050103050d030b0919090f0b160806030c06 69
    0x251031948031008941c00515500020300081d41012080103120255210302c0070340c2d000d500d40408640c2d980c5000c039114084e1744034101400a002d001040442c0c0140e560940054004d400410f46034000d260342d1042ea44400224180c4075039494001e02406003c0c0b1402400c00c0c0c0c686410f11f4003078504046665200010000c207a002d01c070078008a80c0b01d41055000c8020411180c154044440da244601c42d102d81180c03110b203002c1900c850302c1c11030715111881200e10403810520842c50050060014061202e0500c60305a04021020340c0745506075541f40100c002580300d00010265410035152031403d551010f04070780a880034801c41c68480e15004000d4800004564052a84950315003e030500c0c2409a42d1000e0342262601380040140000810f13186d012a046440c144038200d06803051143d02402100d03041d10800412038007801d003105035040b10984501514110031303c0b00b195100c141401c5c009035640303040c001451051144540d008184d5903480042240a06810075486010505520070251100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 539582095 1250 539580845 539580857
    0x8040213021c02090609041805060a0207080a0302030402041104301101050c0a320705010e0415030213020c07080105070f05071a010303050408010b09100302042706020d0c05070b0601 80
    0x10f0b2170f02030986048510080050028100c400c2c0d24030540c07000c2030020349440c0643c1002501d56040d9000301c92490f0703072104a0f00e142c00c142000c22402501701800c1240d006071105060595000801d0280000d0300b503000f2003c400c0480b16007000340c800103024600d054075000018500204501940304150001d081c00c0c07581d0340700d50b2200502c0c100fa0030701c1002040341c41c10310f41c02c9512407100c258031603480c0640002a1b04a070b59000340d01d40e41d0f490030b124481c0028640c0d00383c5c0b0070304c0c00d107500010b0f00585588841c601941d107960006101e050b56500f1243c1155010074244c070185010011340009082c540020801424442c0e001400d40060030704150034401e000825004100303000480f003080d51841d1443c1c4059585034a00141540d010b0b2007044a150700b040f0056026141c254183d034003440c00f090440d0041d500e1a800d00015055083d000c0200c0100c035840d82c030150300c07582068041d49114501c0103076900039860030201100c1d098804e8604007c002d100a00001e6023408a498100009003001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 539583345 1250 539582095 539582107
    0x12030307032a050306011d1e01021e0604030f050a1b021f032a0e09040302010605060d0c020622060e0c030f01020d06080f0a0312020f070308040213021c02 68
    0x80821520181d940b142c410010742601103640c2e92001c00380d070064500b41d0302c02a050760110b0300002d88078020050284d001d10a0040d180f948080c8400b00c005040041c01518001004400c1d101d07205458005441d0040d0414401c0004040e440403184009400c54100242013004044009240c0038101034501a0320212440c02d17419590303441d00141078014120780d10b020001e84880c008001d044000b80c0e018a0000010903c6100061082101d81d82c800c1a552401682c44800401581c114060300540540d540d03130b400030801d511660b00418000c1d60402001c14258090100246020002040389060075440118801c0d0154040c1401d800140c0011022075505404031846050861140e555549441009010b088418041d000307014001d0aa881c1084030382e5039004402d40700e0b0503c035400c2110b03401418014000034050502d010038401540c800508010900140031180d038441a400c1d40821984810001145411442d10383c0084480d1019803e090090561403010f031810401322009039004928 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 539584595 1250 539583345 539583371
    0x30106080402181f14060d1107120f021005070e011128060b060306030d12150914130c0612201306020a110d030c2a051203030703 57
    0x403e220003598081c005094188040c0620800d50300441110740307007000440019440c4580f0b48201407910000d051305141c4404007903450000c0010705045907600406200c4100071503090b10640c941050507844610740410f070444064900718041d441280e00ba07040c00c0400580395445580d45e1000324003030904174815400902c020b424030030425803002411040350041d80300340b50601c1c43d800c1424010141040300c29050b005111482c402110010f425a20002c2a002c540b0300c40c82201a040031039850002e21040e00425540c4008407541c0070150342600c40d03074070080d4404e00c0d02c10507170400a501d0500c1c04100c4a90745100c1c10958502c121001e02079102d0803084201c030300707402c0741c0b0340d610b401c82d000d070600c07044040c8002130350300003004040000b110110302182d66030002035900f004a0f088240003d19104030001c0000c01d602d440d074114100700122080d00b001a02c5501c41c090f00204080304e81440803051164000c0618903a40554464544800c0341488001c000c81100c2e04840700c0d14001c5007003509012 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 539585845 1250 539584595 539584609
    0x1707020a0506160e0d1707080c07030b15030d0c03120213080102040825050405040f0524100303210e030c0607080109020403050316050c030a03020a120201090503030106080402 77
    0x40d00c1402050100f1803560714809003511001400e88a441018407500280414155035200080a50180440858004130008043d0020303030321600000c0c0c900ba5220f0400380c1000e6450f441242c1025002e024003002c0400b00b100d0f042168029401070109902c2000000e12401072000c014003403001e001c40b6400d01e04940d804551901c89100c0ca00d102183c0e5034020346000358002e115691203400703000122543c0c2076002e140403004045184031001c0140c1080c0c2000000c203009881290010b190050250024000344001d0030410b546600c40c044441c040340510842d000d000784100801d50404606000007900038001404146408000c2d14074044900c10352801449040c401a100d03120214000350080d0000032250311664040d40e40daa0141d0780e80d10160140e00a41c08010709076081801a04509903e0802c100c2e06107020300110b43e4001c0b40700011a040c8806c81c081580141c012211540500c0310401c0055039000c01440204081c00b02912503030f0712404103008185c20001918041015076607001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 539587095 1250 539585845 539585863
    0x601030e0f0604060e030309100e0c1e090a05090d080a060506041e080a02060714070e01090c08060312030412020c04020d0c02010b040b09060103020703180f03051c170702 75
    0x3400319840c22410103691651140215401c451071802d0004c40c01c90000080145d034021000d00c00100764217080c142c0700e0000742400d07002c02d6289120708609640150ba400300c81d10303414100c11412000c800b0000041c0000400c0051210b42e100c1d0914041c40015400003e48c80d0050011385014210780d22445820400390210368022540001c02180104440710300403066400300a07100701c0c0c0d105066462003200e07155600c0038006507104001303002d00004500b0520000e0545c52404041c4ca00030354941402c1d030ba4502080c0c1200149c25542c02c0c006621641020150750051070840c001c00650000b40305501e03c41c031008100070100c00c0c103029240105d500800043ea02450001c00540d100d08116109900500800300400019800c1440240356800c15105a001e02039010300041c0c15a59440e006501940c01003000303e00300710b081344141f40108242d07070104016210042c0050a25861400e003940780c254840f0b10a162441100300e024150350300a03035522140c01030240008003036659504e003642420303000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 539588345 1250 539587095 539587121
    0xa110d060801050f160903080c011e02090a0f050a0b0c030f071a06011106040b060f0a0f15080c0304060504030c0f0303061a0408120304020a050d0803060906060918060103 75
    0x100c0030101d11090103402c00c611a00704640051110b40d504203032905084000b0103020013280da6414280081032290000b405903207404c4001050540f00c0705465410801844c0204125590100d840c841624000310000c00401f001e8a1281c00141410700050340910584200b6188000000b50208825000e0040e20402800402c005845105a00300301050544c5000d20f00035400c40c03d40050700960003100d08040700049034006014995460b591905000000f40582d42c1c007002c111f201e40720980d500e00e013010160040000800d0758910300300101c0503401d1045221010700c0b00140800a0340000c50f020740ea84103800c80804141d907140c6042c02e030390754015024064105424600300d2018560142c1001d000c03102030021005230b0204840c500400750042d0b0003250401d03001858818142034000c4003a40c2c000713000802c203104281c1e440d000a160428182e0f400c684507940481040100d03d007002ca41540031030243ca441d8a0070540710000b90f400c0990102040c02c5c0001000801c400d41d03c01c0d405482c8070905 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 539589595 1250 539588345 539588351
    0x30903190f02130b09010501050f030f040204060503160e0f070c15021201030f05060a11070204091707050706031503030e04020d0902030313170714131b200609060a110d 74
    0x80801120050134812828034001e00400700000b90782d51003103040311714846503441880d045440e003003200160610003401c2a03074815100d540100d81d581c0c092014180c40416406450101071070700550300410b8600604c000300102c8403104100045400081e401c60969002d0982841c00f482c041a101c004d016081223110b2141d4050004800c2020b4402d1180c1e82500420484405990712002002907851100e5580640d101c1407040314010b040c03a0300704aa0480c03144414802c0e12a0051000d101504034100c1030300c0c0350340b00c01c10800072550144100341101d0b0400a80044060a684000e0211303403034010090f010f44c0d40010118480d40295001c10300305c43d401000e03280c0d07a40780f600030001d031042980600ca03102c07004181000034202c1e00040b100c00306e445000c21107544241030002c000d050410000d143c10313201d440d400541c80a01420f24044920051901c0d00d41451825113021a003011f091040c50402c1c0d40000d09206091000003002d540c041c044030400304860300c1020303134000079004074041c00c205181 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 539590845 1250 539589595 539589619
    0x10512010609230a0603020a05060f0403050105070c0201091401020d11030c0d0e030c0d050a06110d020c070f0504090b160509041b080915013b0a0e030903190f02 71
    0x4411190900d82c3d4500000c581c40c54442c400110704813a2284002075022110b180f08018074142074010b002710008103a0070034107040d5251103035405e40368200c3e00000040c900307084000031583c103c003124014003091442246040ac1c5000041d40c0c59400b0542d00040c48010902000b81c858100121400f80000805403a40d00e204148060021000c03511310510a0149814060050414010b02114070740c1290082c6001c0c4515201c1e03400510100d444a0700510b01049011038041c1c0314001008040d000034001c00c149482c10b003d0206800864014138030460810b0510b9001c0b0b01602c0d8001d030005030641554450301003020050b24544034204c001508242800051030243c440c9005141000c600d540f2600d2090b81c927002c0b110f40f102c110b2040400c001110000500500180c0b03002c1000708041d0b81031812980c2400380b15101243d80381440304068054210410180840030f00034000c40b900c191005501b00810080021744070515049220400d5003110300100a20071802c03000001107070040d000381d42e515 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 539592095 1250 539590845 539590871
    0x1b0605011d012903132a0b18040e0a021c02040b06070b0406110d0c1205060117011a070605090a021002160b090301091b03050c010c020f0405090106080d0f0305090d0503010512010609 80
    0x281100c06c075005a01c41d60100082e60080030002c4031080300d00a6405845140c41d03000708001062461400300b1940b04001240c1c0047e01c07444014100c1e03200c0c2c6405100e06218501c1000140d800840c1602e0145c0c0c000e00c0302c035000404003288141c110f1350001c00841d01c0d0500c4121200213000d80c030b003280e440718205501c02d440c203078101c0d610714688691003c041c01b26a80d040c0040d01e031036513040340b180c16031081c5000400000d65411022070000420f941a070b4540b01c2039403a60025140306480800c10368108142c0e4038218079003404048200030b440e00150030301018003024280311101c2c074810403041c0c1c0c00c005000c011035902903106a00c540e90044445009040c4a0b0b480200000c2c2400b04507038500c184002003260790302440561fa0907946c010015082280141c0520000d04006011201107640300e00c4041034605003444144a00e0310305944d5840760090120004040c0c80001d0718811981c1c00540042085580c040300b201d05481081e5240100c8216440c5541e0040500b94440307000f43c0d1400d20b0328517800d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 539593345 1250 539592095 539592143
    0xf0507031a03070e010315110a0908010f110313050a05060108060610030924140403260603210408010c050304060507020c030c011b0605011d01290313 66
    0x2004007501e00c1c803a0345100c00e0658405150190010400d03040c0010000200c907080190347c4c006000f00013040c4550803220b400c015070000d403c41000719001410510069200b48200400001c1500090003440c00400304411240310150129130084044c00f6000c0031300004220b403c03100c03588002102d5540d030750741204039118002541c1c01807054070150f8248040740e110f03029881c2400e4000180d0902d0300d0700024101c0540c4128000c05114640301c40102144130b4041a40342e2003140a07440e5103160642c40160440c1590203020072407030b0b160348001401201d481c0004c0001c00040702e4048409146070a8148200500490f48400980c2d030a21000c2007036140d100c0080c50245210300414030070740e110003400341d88410354104100d40550280c08109415031184a509404850003030000005140e951034490648800760080c030b907880702200d28038600b80c891000300760042c41900c1200004002000c000b00c00161222003420070094044041141e454071041120380c2036921031040128000108400c0c440 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 539594595 1250 539593345 539593361
    0xc020f151306140f03010e060109051e0f040c1409060c060c07030f03020316140c030406021e06010b160204020d05090c0108060102010e0c1e030f03180d0201120903030f050703 77
    0x10701110540d05418089400c4e20b20030383c08070301e441342075a0800c400240700f1840200702c641040400100000d0355180d001d41c07102d13a60207001c09900100b090400b4000110700640a0038081c902d4038503d001501c1d400243d019455000c3e900960741d411a140001c0e815024842c40d074941c60280c1c0c010b0080b0003071742c10010640c892198540c0360580300d2400e02a0700701d0004546040c1c0d800f11015042a03568490420711034040c01e440209800c02c08003601551440d0800d802640c05640082000104146507644010110f91141d0062100390b061056000e8507014900d0f01d1020040c41415041c01c41d555a0151510300d107030001d081102e031404140c17035680c4100704d008260201b00541e0116001d0351040c066080c00481c40d41c0240000300b550310500114003c1c1510007580010f20307900030250b5a60071700c60803441900d000c00440d19146130b4005101411503101e4414840c0290051950040c1d80044c14549001b11901000401d042541405d80c085c14100c15002e456514240410004d6901070b070000d48 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 539595845 1250 539594595 539594597
    0x219020105060d02091501020a1b060219030f08420f0906061602040e030c06071803080c030d060303090f0501021209190305070f14010309030c020f151306 68
    0x2a02e030202409000788800b00c011750401155000100a020701c5100c10035490700603c101c4541d000f1680390064007800d0b84491a04407000302c502041500e604000500509036000ba0145109241c2d58018000c0b01524400c40d050024000000b0440045030302c14032400890030b2801c00c0a0321501c11400d0a224401c1d41d1050142070300c86411000d070a2141e8107140c881d00103000f01400b5142e0404024060700401c00852070340040588220060304c0e10300840200d00140f80040d41c80b0a00030070180d0030308000414078000c12040c0c07114900211800c119550841c0c4e000958155681c2c4099042415842541d8415140354103180001040581c4410603200321000c3c20841c04c20b41e900d8500484e01c0300e034000742204002c041441201501d24060140160144103007203403604856076a0303245400c1180e250b00c8201c07024040641000034000d2029403400301102440d00b005911015039000d080a6511140039002d00b4003060403242c9900d901614103200854007501070781310b060307a50804040c1c80150140d14 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 539597095 1250 539595845 539595851
    0x5030307231c1a0612010302010e0105130b1e16020f040b090a0b030c1002010b030724121113050f010c1e0804120305032502120d0b030102190201 64
    0x84250207a40080d90582d00d603038003003203100c5076070000c0003405000600c0c040c100a070448115207440e565408010303d00001a0a9905c0ca50342c0746000240881c1d9462035401e0500c00300700322001002d0f02d0b0807244800c4e10f03045080d4a85030b280880e007407800009003c03807040043d000060000e000300d201c144c3c00c81c600b910032521000407403003000034071043c0e03400144d06a800900350f00100c0d0404440d60004924041c010301110124040d010005403004090f07880c1c940540d6442c0004100340c1030501a49001d0710310382c030b0341c019081e1008801040000020042e0b00401480c0c1c0107a00704480260407401030101c2e048601d81c1c94040740c162208018586102c3c82e071142c0340441144580354002c907851601e40b60031008254040852007845a1140000f00c400ca078041400c01000c160055041c00107490305000784d030713034945a10340640c2c01101c040059464100780070015001c0c06005a00003002c036254501944541d842c1c0010400c400041c021640030160b055001007000c0482903c0d440101e070321030f6000d500174 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 539598345 1250 539597095 539597147
    0x4050109150204080c04090213020a200c06090d020a2303152e0305030301122918011401060804030f09030807030302090105070209010f050a1e030f0203070305030307 73
    0xca4100d1142d846503070ba2980015007685c00910340f6500046001e400500303601d40b07844540410408a0340700380e86000c040303800c50301000f1161852640d101014400d08004124034007280001548038051090b40600c102d26404039041191105c880003401001440d21001490f01d80c0304402c0d8081c4e10300c0400a003e8429a2120b500d0503040c8250079008204004080940c10624081500c03885201e10068640607548400040043c804200450081c0441124030642100ca441d001070081042600c3c46085803905141040203100c5070005d5421154000c40780c030542c018002064050550440f040e514441c0100c00012040d4101020f50700c04e80c8250b8921344071054a0070261080704440c000075010842c180404800640294000c0010105c1410401d0600d04554006010319a09800260176580452010011801e0090300100a480113191207007103041140e009030b21040079440051b01d0611070b442b209096481c280032800142d6081800d40c0c0e0341c0c1c9010716024101a00045441c0384011030b429403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 539599595 1250 539598345 539598383
    0x10f1703090a2115020d141e0a0e0118110108090303060907110d020d02010b100e0607230129090708100924090e061803090904050109 59
    0x11124034072402025807840e03c2c10a10640569598020f140784800150240c035008200510f00c0c040700c080d0058000360307940c1405403002050711201c001013507070740200000344440307151a0f41d04c4c1d00e03000248111003e019525200b500b000303030001c0d4203030b6400d95107405980580e9000c0c0c0b084116143c1d000307501c85007850789403c00440d40707840304a4070240a83c00c2440030580300d00d0500c0c55260404541d1401c0c16404009410741070034915803000d00d2000da03101d9011400015028000c44100c003e0032650820035240c8400c010342492070a410092180c48000b84640410001c50b207000031161002b80c0c1c04404e5400e840446000300388a11889008041d0525180300d15010f41000e024403401c0070b0800c1c6010b480d100026101c440c0f015000c200001c89580c80440e0210790b41c42070f40015240500344007120109071420014607082c582004100c00d0800312950317100000007c496402000c1d07031140454003014441c55a0845c0103622040b0f034000244414041841015080140300e030380100010310030349040403d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 539600845 1250 539599595 539599597
    0x5040e03090303030c0703031506110615240f1c050901050c0a030c0e310c0917011116020306090a02100e01020a020406090c0f1404030605150405010f1703 68
    0x192455050340708000141750244030f41c01900b405440703800c01040000305080810094003694108000240b120303a08080100c00070041d05400150040e503050020000c42c2c0801c0c400d05101e9844805140500d50500c5400b0440c411900e1408040c0c0310941c5400071241210042e031850140a1403060071b0a01040784003c0601c50580274000c0500320340c1c1780001c0044c0c01e0780074001e00580759040c030541e07107450b03d12522051002d0181c244400e60702d1494070f8540740112401251840c4c40003541c1d10308030a1031810f41c0c2210075076013580e0820601d034a05552812201d40500001c140e40340a114021401502554200f41600c520724400c4065602950b1860072a41c0d0b1007820003000b03503011075054a120000340c000c070355101043d401032040d01c0140358203070081402c0c1c4105620a0701d9207961680700c01602f030351007c10100b0700030081c9440c80a04080030b10107180c034004c500000c0c05150b6100e01013114403035403821024040310003510034025503075181c0c0100343c1c48089209820364120700888504500d04088 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 539602095 1250 539600845 539600857
    0x915031506080f040201031a040603030e04060e010e0423120d0e01140105130e15070f020304060504030605060a080a0605040215040b0f030a020c0a05070f06030e0d140d110405040e03 80
    0x10075400e03c1e6544d60700110050110600c03081c2d0404582c110b000790586071401a000a1800383c0c42e0b02c400900400180403c541c115427158400c040140c00620400403209420741c0c005400010300d02110029081c5a00e05413a411034500c2f15200d42202d07005694003c00140002d12a0b4201c1000500f00c603c132510700ba10740180c0141098409507006100b14545500c031101500a0050002452902030038611300d02031000e64000c2c81800c0141c10000d4440e8044142c6d0702c0a40c052002d50708141c50703c00301800714021404020025503d850020f2480d44038001c0090040c40e20004440164000381040b800030042a58103030300842e42e118590241c03150b200c0840b0100d5881028140c03502034901c55956850301301800fa42e0040b60208041880b5030806c01040103500c7c0107802030100b003858a1400c80b29405950700c401c0515060a0400070052000b040c950034610319420140b0312a1245840001c49104640b1610304041c0340c80030304050780c00c00f54050800d58400340c0301085041411652030350341740a80 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 539603345 1250 539602095 539602111
    0x6060e01020a0f050c0607030305150604150c170318070806070e04050406180b0a0e06040b0412020a05010510050f030309033414040518060c0a091503150608 69
    0x2102c0d140300290280351001c200e035000d0400d94001503500b00001d02e07268071a81c030a600080d103603810701c411005419a00d03050761071308031a0700e40b802e49042c0b000141f030745084c4251030510045a401d20280030f0544450282030400d00c40c0c00703950b0b02c0d1414002081d80740042400500b0701c500300001c03491910014409014a000c1d44030b0900e0050f8842c00c02000d041c1c01002250215101d80d490354070388444107002d0110a104644684407072030309421080446000340302e8405268059414000494460203400b60055000f02c45190b444030101e0050746000201c04000f425903103007404100b84501d16801d050142e0b003040f03407a01c03451002c10080503602c0c0208852168150000e103090f40e8440030b4400c02034081c110040803d140e040f800c01e054001185203601154180035000c510308903900d0f02d0b104040e84400a01090b40c003410a91545c0c6649030001064001c1990300055141200c3d4011248036008000305018200c1d000e0f0140d82c001d0160143d83e0860b4103042c042d05010030100d0045864600c16070745 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 539604595 1250 539603345 539603353
    0x10c050f1903120e060c07030e04051e1501050f0a03090b0703020a0216030506010e1b0706140c160605060613030c0303080c03070203031302010c05030a030504031407050c09090319090906060e0102 86
    0x140440001c4c213504c8007d0403410700074030a4902c2c046807614090103114030941001e5010030705604240c000074240c0103000c1c4241042c91142d0320301980e0008169401e8800c1c014a42da202c0d41a0041900205003082024000c1d0300b0700f0080164541e810b4004014860840d0b09a0300c1200a00345280c6880649000c000d041d6080403006200c521201d100c03441d804032000040b403813164403017111000b079030b88407075800d4030b19a44980f1102d0712080d0300700ca0250042955100e8030b03e440254503107000442440b00004060a071180c01007803061781d42c0800e4a260b0205a51843c2d01e0310383d6450084110000b51004801103080800000c40555202d42520b03c602d82a0b0080c603d15130f80c0c03000c004500c1000407422418808400c9140010442c00c00141010001945000483c1d00301810082c080c2ca41c941c200070516001080084000f4801003440184411300350740506094464072140740c11801841c201201005008245040320307130748020f0000840c0d4039000c0c100a0309807102c000300c941100400b221400344e80 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 539605845 1250 539604595 539604601
    0x22030b0f18010603080d051b03010e040318030812040c1a03090c1c0f052407140a0906080a06050d0f03080702010c0c0b0a1e020a140c0705010c050f1903120e06 70
    0x30701500940d82c40301c8951440045520999234802d415042a080020100000c0b4108403c054100044802181c030703441c0c400314014a5556040254850000c034120681920404501009404034541025111658034800304101c1442c1645040c4c000b160721180078446e42c480c3e060300341001c41e02c08000200e01c00f6a1f03001006180c5400302c9250b47c03c03104503038a1260510340c101210460707020b41c4880380c403c030245000d4280040d0060034101240e807211011942040702c480c0194201049404841c5a8100b2840c40d40d90088640002c140d9a031155402c03000d140c04034000c0018004c17070301481900c2900c07200318944640c40200e080700d068600d07034000724030311130164808151202c01580e407041c0500c001044c0c0f07032018058101c0c0309201c458022002500030401000c1683c02c08079010b101001d40803103078200207038403c082d43e4607911841500e052007041c14900c030910409100d4019907140c03110440d0b10070020398950003109005510140c0c001803d00d07618042c400064090800001641001400961 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 539607095 1250 539605845 539605867
    0x60d020901030b040c0306150504050f0c041401140703170f040f060e0102071a0121122007060207050112020a08010311010e0a0807080d1422030b0f1801060308 70
    0x80c0f400707032080e280903107064400000a8400e00410a100300e0900385000329900d00014001a100094a610007400002c4101b00b405000c80003a1400c4030f0811001d200a60040030043ea20181948800c181044002803c082410b82252104070700c0c422009000324590340c0c0e404003200f11801610000c16070715812690070045805038004c03552103461b0b01c1c001480c00056640f078508203400c1c4610302000d22002c000412540340c0c0301c406031a00040c2c0d0100141c461310550380d66450851100748042c01d2240282a40c0da540c000310380031222003401e00080f50a0980c9641d8044e41e211100c2c8500ca0008803008100e010007925402038a908140c1c42d00c80b04010703400c40e507481d04141c0e07030004041d040185048076100690b860b0f18001d80101910700151910a0510f2210750030001c2000c40c00d010b04c032204201d50307820100801142c0a1407141e4040d901d420440840c10304007003100e0b501c06402e81203000c09008030409001c10b8107000c0c410310310000e40500e804894a40c240c0b16544005030640e5810b1203500510 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 539608345 1250 539607095 539607113
    0xc05100509130209040e06040506060114030412140708040e06040c020c0114191106220b06041e020a090816090518030f070309061704030c03021f0e06060d02090103 72
    0x2402000000740c104131020000c20203ca00103422010603500900c1400140202440b405801503420b20b086a0080100c1b1249216031202038401043c04a4424405182c00d100d290f2400000703403194101c941d0380010307051051440c1c100e40144612807441c40080361140c136003481014415007498000c0c0101180c400c0c01554441000c415484002000b00091107000c9540e25102c01d0010482d00c4a1a02c80c100031b208030700e0300700010650000d26a9107400f501c2c080b038030700400f81d180a078400c0c2074881960b58840407070050107110030201060340711031021014001007500500004d074480d90b1520704603543c0300b00c802e558442441041740d5884206100740130f150155000740358000300e01034180001c0350880343c0700c43c41e5a120569960b034001c400320b0f004003010341c40300c0044010809403a1901070b01c00110301c0d96042c8280540001c007441450164201007600130701039901142e110000380c24200c0302000d42c0c0c5c0080c1031072400c0d00e00743e406240d00090140c504000e407807144d00e4024181c416241e00759030b241c201c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 539609595 1250 539608345 539608369
    0xc0a12052a0703090f0b030402060a020f030d0614010306060518030a0503030709030b0a0e060109090614070806011412011502120301060c11010206061e190b0301030c05100509 77
    0x203280c800301d600034241001d600c11100800480c0c0c609a40d980b0036040080c22102260440700080b42010000c000191044003036980103501141c5441d512080958164a010300c0e00c8501c840c2d40c0804a130256813400945e00c00c1e8200c4444e002180710102d82000114102d82207070140354045001030105025414141c8062010301c1c00c09412103d600c4615200c42d03142d5041100e40d400028040785040c420000c4801c401c50b00a084060240034150047c5031851316403c0500a603041c01d561007007654103014203504840703004444003010343e070982407409005262240455080d8041070b4000700300b203401d0b481d0300304403410b41c084039070b0041d42c6034201101c051001003800005821071140801c10041c007481a001507008010710f45030134610f80c4075403a10300039408034940f509056400c80d4003000f0081e05d07004c100000c0111401085595024840002800e01c0c0d92406108000240d211002c00c01c1107110000f181a24043c00c01044226901c10070400c80030950000e150002e0024031120055041160745000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 539610845 1250 539609595 539609611
    0x702030403021210061d0105010c030c06020a0f0e0a06021207020a0e0c030703060e01050d020420040605030a05130201050d050403050d0f020a03151d0c04030b090d080c0a1205 77
    0x1103099a02d4002542d40e018a41c50798003c3d400c002d00140500c0010b100710401055418091200e28110002c1d10460034014400d5038107126803901c1d940c0030103200e0b000481c5c10320f0340448115111000310704002c10b0440c01c6101000419030780c180e54050341c5450845070007140c409234020600c1c1d415207180d140d62508030f08401c0380c12070070302c00d40410340c001d50110310303071203412004003080d2a440c1a0a00030300390780450740640a1001544c005020700d407078815510104507010703203020500342c42c41421640315001188010080c0b50010074045445a0701100650080ba01c980c0d00f4000c58880c50f07da070030a480007000003030204100b00b042e204a500c541d085594007a0003810014241a518040482179803440c16003010309680c0062803591030b0303030544210b54100300401001d91055040000602e10000f07038541110006c000c40700043c4404d0540c03001c55000e1740d0300c10a4602203007405008030350382c2d000c000a1000414034000c0010001d40d80745c070a031080c607905980e610340415141494000181310141800d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 539612095 1250 539610845 539610847
    0x30906160609240615180302040e07051e1021061d15030d0309020f060d020301031a1311040e060f011809080f090109030b010f0e0c0918070203 63
    0x203404540c0714030802140c180a50307002c400d0400c410300b0f003128074480220341d01a203624004085c40b00a0408940a4107a01c10313040003880078441c0a84440416a5030703200a601604000c0c0c2000b03101380103d0107104496007600c00ca81042b80141e2004210f24071402d0440d00324260240502005100d52103421842603500d64000c0801801654441a9507a580082d0305021000008400c180000640c940d4015103d140e1030507078142d41c900087e19601c07200c80315810907480344100000d5503280c00d0030702c03c501401000c1541c1c4080620090707001e50400d100940c1e03000c01032502e482031100051851803056a4290740d20203004d5035542c0302e00543c0d1039a11265046a5161101e1840890400c4000c2c000c511106400d807056240030380c07107000c283d41d0a02400341e80c0d00380b81e880000140c1260a0b03407580f89510f20119103402000c401220721a00701d5101910008011000003151042c92100000303440e65410703010095038580b110007500d48624101540c018014480d054441c04803c0001c54020708244180c13 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 539613345 1250 539612095 539612137
    0x60207020a1203020d0f0203090102060601080603101a01030605030a034a0f01020a030804140120040906270b04060503030d0f140103030503180a08040303020f060601030608030906 79
    0x82074411003071000320007580c1700d00441c070100c5821030f4040404e030241c3e10044d46011a03420000f5240c40028000a0500c4072090104031190b9081c01008403208104808000d04007409015900c0750404580c0503002c646820000700d010f00380800c006440301c0d01a2a0504041d0040882650400260349a004807500da240c2ea0b8040f106541c5980da12051101822001103280404000c1e04603140741a0606560003000011f000940208000b54044c4c3c0000300c009514000b8001d40e4090000010014044414030041d0407180307001902500c1590b200b11402c00c00380791194299241c40100352820b4540310041f5001010541070303908151520003004e080030940f107581c1d1010034510b030001000c868000b03072990f070205500e2036a84a00407030b2190816440a05501d5074138080c01e6480054004d03480b00180d0003085020b15410484070104581c48110540e50316601d0600a403284210905403109006890204580d503100b40104801e0324102c00283d0f103000104000c01507164000b201c0156941c81c89030714 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 539614595 1250 539613345 539613359
    0xb0106080c12070c0c0504051306020c0a02030a0c061233050a060903060f020306010509063f0708071d01180b070b010b0708030a0b0d060e100e03070b04060207020a 72
    0x9868020b240c141ca89003504a07603482c080f45c0300c1515801481c003035890001000140240b03000c0040480e070300140d00503541c510b414145400d04425220194042c403410703150104106908803514101c0d07400d070307a4030401155041510710a460041002030103a480c1d12031001c200e489192504500c140014001e0390031250b940001c500c5840196024001040720301c0f8003002841aa4020500010b10510b030451651400c0400607007035004241420340200c03404290310b4a913041d00030645030109030b00700742901010b04c10091030440303500d8030a030140300b003c9a0700494400c0b07000b916014056031190719101c402801d020303000d03c50350704190565810052240d443d5100b00750405422000f4012407080e80e5900c4070359080040d10060107900495440d032040201202044212060380e4200613001c0001c54443c0c121000101d0349420382801901c12072a28030f81c0a540200058404800c0d000c0ca13009101510300750400390f84030700540b0170142c6801d80540014001516a500070840e4910040c81030300e2490700d07908 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 539615845 1250 539614595 539614627
    0x60a020f0d0e030c06090d110a0b03010b0307030614010212030c12010f03020411040b03040b0618090105040b010506040614090102160f08010605120a061d0d03060e01060801030b0106080c 82
    0x14015001c02d0080e2240034460405004814100d1800d50b401498529060041503264130802d0028188400400301e81440380e5905e5141001041030440298032561941030035245030784241d0750480480e141a1001400d141c01c10b941000051050700074080f40d46480140394131a0380020f0420408420801116000415101e9418003a000108000c80003038110720510007121341c0840b000b000010180010010702c980c040440368080c2d40094160fa40d900d44102041100081d40580f4601044150070001d0544055105a200ea4041c030b107404210b99a803c00d001251040c2e01480002030881003014042d1141400144614a0184100c034903a84108004044c41561500011301d4081c03440740400c40040c090244a019050032201c09054400704400265035901c182d0006080d55120001407088038000c90b400b410210606050312401c3c1d09030f54004005220034062540c20b92848000070862a04c2041028181c81d801248913020b81d013400000e84039010020507542c020b0b4020003a20100441041e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 539617095 1250 539615845 539615863
    0x20111030d060f0509072a15050c0706140105060f0c0c1005030403020705061c15090f0b12121b031905030105030c011416020105040b03010803220602070302060a020f 73
    0x7119070310b8813400c203030400c0014000606240104164080c0751a021401c1e8010640c129002011120300350300c140ca083c0d101207111140c0000303443e00d03110030031203102524002080028030801082200203002c00705084403041c00c1c0115604000140602d00c1048441c0d0010b0182105038030860325400702c00310005208015101d402c03030002e0f00c00701c01e0008264041104c1d0b4050603044a01c00e040a61a01090606400e9900f41d803801a403269142c0341c02c0307004c1805500142206002c140441444c0041d00380140c8100300000b4010840f00b0b10002c0080004610704460b180d80c60f1980c0e20302015200644403c40d508001c80807140410404190804202c0031082c004005c140c039a00c1d00c03589400101800c1c8200ea4202a0602a01c5203078140c1c03100001c0221071660007032030b985039015541800100c800e0b000715080400461030010002c9560310001000d8041d021102e5a900800c0c3c55107448007540d181e55106600169100f5242440140303010b03005815014403c0c41260f070400341c864a00d80c5000300b00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 539618345 1250 539617095 539617109
    0x803031323011d0109080702040c110105040606080706171302062203020a080f0a06050901150f05100c0503040b0a030f0f09020a0f21030e0a0320090105060304020111030d06 76
    0x1514a180c000402003148000c51403c0760000c0042c50700c2612000c1d000d1144100003441280d843c0e140b038998030f00400011074020b00744402003000b0b24180ca0924000c0c9424051200940718948001641c248584e0f00b000c5156181004d416107a21200300a03403944400000890f800581403081c00c017400c020070301c004c500500340c502c4003d210345036006100013140b09820882c1103401403d13052000d4500041d61044050340000001b80ca81c2d0750388111801850f120101c550703100800d0030005094882a0341c52401c1d0341003100c846036100119882074171640340403180140345400500040098400794405880010754508002c190882448803030400c84001c02c044031260b582d504000f800b5410320149004c0036207a01d41407800440e0420345a402e80c00c0410000070010b50050189504241c405c2c4260400c916000d48042240c5441e4980f42c00510181c46d44014041c5c0c610b40c80c00b460740b0702000e2590407180080c1505180d07880f15001110032485075148010144070422426918031400e1050314010001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 539619595 1250 539618345 539618351
    0x1213050f04140426040501051c1503050303090d0503090a060b010c0f0b191122090c170702070e040b0402041e0617030a21200a020f010501080303132301 67
    0x2840d41c04001c0c0b1805188103c16408045c40148156600401290241c1c42441400142d88410728102d8002e048840074200c10705004200003c20050300001543c06984c0c0e0400392980f6000680d000c50b080e000407114080250b01c0800084007241080e445a0070300c10040c54010400505900d4540350007030880c0084410038490010410018a002840c170119044c6540c24420700361168021146801500c0c02000f45500d01010070590a21603179040d801415010300c144111a0f0800001d80802214018070300c07040d80100000790314502c0803d40c0390075a6480d1b01c8220290f1159214101c0b2080000c10803604581d41d84607500d0f4031072442e00c40000704a203990000c10414100f910303528050502030075400c0340b540240102500c00d90020600c520008100c48a604018884180280a0041d1002c0300a6841060441c4034480e03028034000c0c1843d00d01c5400312040426820803203400c0365824494060207800c24804a40407180365030344019032602441e81000d14141c0002c1c02c4004101000ca201c080b695 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 539620845 1250 539619595 539619623
    0x1509041b17060a05100c0212210412080a2d030c030b0603040204020f07060e010504032d081801020c0109020f1f030b012f1213050f041404 61
    0x1610040a803a80341d00e009410700709041540c080741d02c001c1d95019080c0700d58242c4101c140035a00c1610030030314458000381501c00410151700d01a40350b0592016a14020302e101c0004104411810200c904032402080052100350464546001d50340000d0a103108001000c6c031640360503103846a511142c03008810b8000030305a004003000c0c00b22510000400241414108000110356400007034039032090301510050380d41c6101107011001ca205540e0001c025510f03000c03000f00a0f2605500c040e120b0b0b8401d48509602100c644038204c1d000102003007000b5111054208a0091341c492188250400c0c144241c1d040781d6118491481d003640c00944225225030340d2000c01e141035203030103507505504520139200516034100b000401003840800b14010014140c03903221541c9164032078003180802440c580420040204041c000482013801f44140e903001d44241d8101500400040044480702641c12050b40c145915207030a002d4101d030312481d5a44d0083d42c0b05070840880ca8030004440c4100c1c400e50820030040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 539622095 1250 539620845 539620847
    0x70809120d120c1d040506010302040b030c0a02100504050d18171c0f0f0813020a141018050f03010906151a1c09110604120308011203020c1509041b 65
    0x1440703c1c90b0710700c10044402d4440c0c43c99010000c5890511905071004120b03030f40c5240058001e40302e0360b8025070b20f1050000c100204032910b0740140c6509035561b8240e80008820403100d800303484003510082c0c4650440219010058040e1001070061050346000894481d501d134803407001c50030303660180861074110400362405207003118140c0e207a1602d941004450b45045800040190b10400824010700c202840480c1d0f034a10800c000012860b030040100a80507102d5404005c0803890b0008135019411080843e0600c5014880b03440c801d10f0140c0b00d1198442c6840c08002a002d400402c46426540c5c2c0e144910201c2c006029031500004031000c14507200c1e00c0e080341d15445248245800d62142c400380058401922501000da20301003010310082200750040c00c0050307050400e203c0550f4401ca00140c00039084030304441160406000c0d8980304c1d4140ea07100704511208001c040010010780001c071109100f46081c041100c0c13200b10300d4440500780008040450200c81070035540e00c00074150110421581 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 539623345 1250 539622095 539622101
    0x15020106090b100807080702010615050c01201c29030f030408190201030e0a03120b04090b0c132114010b150a0e03100207060605030303010b070809120d12 68
    0xb010090f5450900151100002055818040c0080040115690110340d40a100750810030140114200540c10600102c501074800d50102182080399401e0200d40020500986a01e000070740c440c0d684d061400032001d018040d54920102d012806035503414054550344141c1107482c21400110340c00100c00216001058a0714415060350800b0b50710420050208450100d038032900c40b17071800d040f2100c44105100580241c00030b00c620b142d040c03081c0341c150014180c1c031000500400c40003031001c00580306100c05000a40c0c012300070250400b10b40a02088030500914000c200540007000407051803919100c1c189404500425200b50b40c000b000000703001d003c40310303901c2048000017400800901d14140085004194040e04146a4410208100c0c15550040d002c0101e4400000c0c2501c9064951b1010000290445801594144c5c40c001e0041071500340042200c0c16a240480b4041c200300083d650795540d544454811504402c0549101d20b2403041000200403c00142d2a11708a001041c0504421 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 539624595 1250 539623345 539623361
    0x512011806082415090a1401120201081303050912030c060a0204030b040209042105040311091b030a020d050f0901050709050f13020f030c070c050108190504020a1502010609 76
    0x4a034104042c0000c1d0000c80780b0010f1407040c01140084260303500e004406032a407411444150708000c80744104000750741268449000c0400b4004002c04030b98944a46403450012904001d001c41c1c801400318150340400c0050b00242d134428035010740b81202400c00320f404652600c3c0e0300510b9a1005c02e4140b00b8040600c6525400082e0b10400c60070289107444600ca402e00261000e07018000c1540800d0030311044143c1d9001c49030550702c02d50502070b880013000303200b0360144c4002c0d11030700e8021301000c406103040910540034140207164050300c003000c1c0002d8881d80c4d201610320307040244d0030002a2201e0b0650f0062178850f900c000461061403a04403c1d0600399040104443d08001d10f94109000668031180d002420700810b0303601c44003250703040848100a10416980c03207410715010040000a00c2c54800502005205c1d0320031000c403659800054074050010385030206011140d60004071b9050441e441294000c1c00204040d00050f03503040c0c49010781718040f00e80c1300141d46404c0140710710b1845002d0310003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 539625845 1250 539624595 539624609
    0xa0b010f0909020a0b0c010e1606023a0306150e010e0906060301090209042a0908030f030406020c0a020a14030c0303072316061d100210020a0512011806 67
    0x80b07540e0880e030008074082c3c80c6000e0481c036a58082504508980254030280000c0f4406040312201c00d4032001c80103001d0551300c10140184039070800d540104401420358201090071220032856072203008032441304001c850803842c0400d955550005081407215120017408041d6440c0d02900c002c0040c0018200140c600c0b00b540107510f404180b2400391683c400316130449284000068580e84d2880c00503028040c0400000d480c440c8541c03901c103611402c00c0050070341b07280310f072500800c00d50344400031926030040d42400200036406100090210340d41c1e4000b05071550350242951685205a07000410001c410341000004200100c00300d850350a0400c02440055030031001541002600c2e580e00591000d2a88981c0841014090090340200c0c1045100014014080c0c092405238440000400c074000c0c180e26001007041c40b0010400300d00b41940314024012056001e040f00940d200e8403075019500c50042d0404014003080721001001e502c0454034040e12251030450603801d03502005900740c07005a04480 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 539627095 1250 539625845 539625851
    0x3a08060f180606090103060317091c0b06060a0504150e041d0c1c0c030605040b060907050d0c050d021b01060503030301180f0209040c0c02092d0c0702030a0b010f09 72
    0x4010080d0814001c0c1e80048120741c416a1002c03181e0040300a00b100c0d0344000c1448032501240a03c078580a40940b0810750103803548000d1544451000d210a4007010014003d41c00540200d4000c0c01d14030000c08481c801410042d1405036504041020209016807010005080d00342100540c5001e004a24441e68910030a181a906d5400702c2c0361210045580f0341d11912451032034140c98110401100030302904052480b00700d40d92410309101a2000b15030890f501d9803980d00160740c6250904c4041d000740407c2d504c02d0300f004445c40b03501e4001c0c1030404511007400000d1058808041c00c030b00040200c5004e00141030380559005168609450b503942005200760018001030141c606004020070328401c0021000c1001c0d80a4580d040c000c0c41907013040c540060a1140c2607058a4201d4010f0a006100741c41035051651400c2c400d0f250100c1d295070b5950b18100709040008040821201a500000070000c005d1802000340e001926285080d6011546404281c004001c440c004002150013024804418 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 539628345 1250 539627095 539627119
    0x8070207080f0c0d0501140f010f1d010b07050c0306090c0405101a0a0c0501020d23010305030f07022e230d090501090c0e06130b033a08060f 62
    0x229283d0030708034000382c002c0c8610200c4005120303094201d10203000c0c141030030324030604208840c4500c03100c003405020281403403004006080d48603d04994110384012446850710703400e02d4118900d0703038090201070f1254490115402c006a40074080d041c003540c10140140180f04d6042c0900c0190350340100407412100c0c04100c100a03d2200400002c01c501c1c0c40701c40c19580d0105903100369010009140c3c0038020f503201090003110600d1540c0714280d00308888913505013a402c2e0a11983c6d64500c2400000d0590b042071180c8103800c0060000b904400b0701c006d1032607000a04081101d4150b14a40880d01e0000034100100020607401240a6480314440d024012407c5200713514075105102e039010030184503541e0b00c403c01c10300400f03500c1901d4843d408081818450b507102c2d601031442d24180d034007911440d02030040d00340074915485195a002d40140240c0601210b000d52400c0f03081c400e01455000098500140000d408010b60b07101e2144140d4039003508600b030000034000419a001081c0d4002c00c0342540b4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 539629595 1250 539628345 539628373
    0x207030218070507150b2e140f031609051504060c150207050106080705010923060c030309030703031a0d06050702160612050a020306090703110909070807020708 71
    0x805004480300030600c0c0c0081e252030b00200e415200781d14000e414102c03d0070044203c425540c0264650003022204c05042c0c0f0703289214480c900c100b4403418141d103510202507101c0503019607140000d40c60420b402500f0250481e0f10410241e00031100c0024401015407018695a0480388640180000356100038110b03900500d451518072a60241c0340030300280703413210020410342c020074000c411811003041d03443d2035480c90443e0283c0218020300e4090300480e0307400300c0d4552040b4250000c4698180c058440c0700d81d510700040200c3d010103080c5400203030401030342d400c2400400055000da51074078029031f5944050f090060459119103d12103400d02c1e08944007205a03107050482c40d026410003000649502c940c1c50a0745000c40031500440d441003040d100081e0281c20108101030443d61030b80c00c0c4219521810a40101d120480320135504c5a13400380402c88051281c0d0007520200030301c200b400e20742110000000c880c0c400031200c0302c2c00114540f041000981e0b0500c0080000d0440310003c1c549038103c0300e8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 539630845 1250 539629595 539629609
    0x3050601030b0603010920030d1b060f090f141c05181f030f05010e01031218050604260c03061f090504061b0207050604261c020d02070302 61
    0x100c041c01c84101c07800410f000f55006e610000e581a44500301c4032013001990030701c1424041c1000081c0c46802541d080181c00760180c4050209001451840b0840000959551009111110041d00300355510040b84000954229100302e489016003411101112400303002d500d003a002c03803503008142002205100240d604603060382c004404008044003111180e4002c107070804e070f00c107180c1446480c213444460a1542c041d800f440242c2001c1105116a0f030329080b01d40c5200500388402050081f1080900b401240700318000c0703034011f138200c0500b01c0150b903880c000303181d40e00300783c004541c0d801c4814080e0301011351a0740648440c02c075100140c00f414880c0c034006901d44500810f01090340b50400740450f00b4881c04003d150240c241c100082003d0f082c076003080b400801c014000c000a540d0304d052251040e42c00040c4807011104000c040790300c0e003810500124400300178240c40c0000750069080b154004c6c0c40a2099015000c0302030341401c4c0118000304003e00d401c41c120500010b54015050910158540c06 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 539632095 1250 539630845 539630849
    0x1502010615050a050720040606031b030501050607060e1219081e01091e020c0303220f08090402210603210405040c17040507031704080606040b040219020705120703050601 75
    0x14006d42c07009100f5003045281b64024469001d40703095804a50b040d0158040f078900004581c44015019011109800300c60302800f82039408078041c0b0990000500940141080d4101c3c14251040350b069004114495000381444801c041e140e071990342001c60b03204014903401000c5070740e0040e0001700044805402c0b0818020500b0301e40e26040740d4460f044200c10442510400d10070115521640402e820341c4076001a201d80d04220488d40703030000848200604038500b290411070008560000350303103094465205c030303103101e4100da000d0003002d4a15500c0e00a11a00300004403041e4400d1400e402058207092070445440044080301d50141d0000b0307000c0080d82c09850302500d00017102c0d01c0b03a00060302d40c8151a0128071440400300c082104000000c0f5245048038030501d0410102a80700d00f0002407030080303004102040c0e00000000311145001d8000e8100d00c200504018901f4034032030402e5080e01c1c145c0c052000581d1100804002c241401440d0061065036903026108040c19940c40702c0c0c5980040c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 539633345 1250 539632095 539632103
    0x3050f0d082509231f140c01150305031225031a06031603050703050c03270607020714060405180a020c06150103050601020c091b041502010615050a0507 67
    0x14801003003041c0a0f08865000e01105428900262a2030f44000852003844804a008000100c2c114200510403401070302c00300141d4076003408440c00d03e190650940c1050f60a004250740751107240d1170302d80000780c204010354003400c0907507501d41044102002200002c2c8c4010b0345c0f0051450310100c9500c120200e00b070342a0030b0345400301c0d6541071041000024005250001c0e41b120000013800400d800540500f500700902c0c3d1000d101995031090161304980080b202003c01420400000302440949042007041ea0101060041d007514485015844c0c02001c1b605007001da0300504003030218030201c40c800611036000319036592a040c01d203404120541ca000d04070845c0309503050081288402075806507084000d00d0030888880745400305858210500a100380c901103031a15011802e02c0d4800300b1245000c8030040d0004105c0c0c4c850300e400c5141072a08008921003c10140000310320300560071101141c01c10994008140113041c07400a607010b000211000c018800c0401051108a400c442599000390f00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 539634595 1250 539633345 539633401
    0x503090f0703031b05070f0b0408100b0108010b16060507020601050f0306101502100e0102040509250e2d0916080606031e0a090c081204050409081303050f0d08 70
    0x6141742c42e80c03074040c132074010041c01e0740d0040011900884075000340c401c40f8510340849a280b800c0162841c01c65441c3c01036a400161618014041c40d00003800811440c2c140c00c42180c41020303951600001c44030150b80b2140181c0041d0300400c0b1501e40703500341c40c0d13201c4001c0b03003e461030f418684414215512548030f1103041c081c551400080c00c03802480004000080604180072440d5000f402c0e5000394007900407980b1403543c01020440031180d111602840d2a0b01000900410106110030340380c0c0880c06a8041c0d001d40800424610509442c0c4200f01e0154803101c1000c3c40301c192820132550321001003030400184020b403013000c141c135449102a0341207002035400d1540c1e038841c9112003007440003041c4910000f2103440705014201c4040d921a581c150300480085942a48a40c0381d00c0c1c4400f21076100030703400791040c403061003d8905580301d0320303a00744285001481e00301d59160342002584507500556840d013044805440300c803010702c13403090030b80780320700c3e0100244c45d1030040101403004e4041441210f0342 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 539635845 1250 539634595 539634647
    0xe0102040803071e020d0606091404080703030509070504021b0f0f030406080403090e07021b030c0d0227040305120604050f010b07032f0c04020f040302120a020a060503090f070303 79
    0x1381c50034582d2a07640140100c0048005410b000010713203094803c00c2c2c0028901030b0700c0d1250807405403869003d40d501800c1d603403806000b0b40701103000d4000541246c6990080000018407a83d8510060002c40c0000c84001c54482d42e081b03081e0b0401d038200b40b2000c1a5041401d101c01e0100010080320261541404d284685440703a08040315442500d410132031011500c2010f0201190300020380b12107240c420300d40060f4412030f080a054803074103a0798401760407071110140c0c10f005241048a8080c010760202c0c0d8500c550640e41c03481403181005450582c00700d540041d07120b0820f01032051180d071000e0252818407407414148404009010148a01d40c103400e008501c880070184103c5d174105034640d14005c101800342d90b05010010b5410404d050129a104281045c842c3d41420300943c1d440c62681501142403a2440c0c09011803d5a0842c1c04c02c41c0e40110344948005a41d0103c0c0d080203403a850361203a0700e034a40040020300d00440408141e146500400041001a900202451040c0080d0904845080d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 539637095 1250 539635845 539635883
    0x62703021c0f02060a0c02030c0a0e1b0903011407080a020412030f03090f29010f1214010f0603140a051b1c0f020103060f1a090a0b031005040e010204080307 69
    0x31808502c029400038001034515103081c0d206030b207403a00c58021801c2d201c041c600070b0100b01c5130303652070711031003580c2044200014500b50115802c00070065001ca001458050340b080000d0031038206845030f4440004510a0118155001a005620140e200e03011450b16003410391000c0000000d0400a04108070f0318010708080d88280c104011640d482800800801d8141c6825903603507510707040720703909800c2d042c4020800e0000c0d1502c0a04071411a06001130040c1050400d888151240341c0546110501000c40441c61800744598000c0d034840390b10016400d4210b12308400c40707086509110f5156401181e20601265000c10031484148104800f5601c5403802ca0102ea0090303119200440000000c2201308284a44d01c48011709e800d05c00d81e0204100d680304d8a070356030112914040c0a01c0f5602006609582013041001403902540042001c2000d99540c090600145e0003101c41e1742c00134800c10400c00c0341d0705182c007403130304a076400341c009505140c2001c1c9081e81c0c81c00b9602000e0b00712018140b81d48035031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 539638345 1250 539637095 539637113
    0x3060108371101020f0109020d020d0c0b0a1d040209090a0506151b191a07051b0309030106090204050114090604120b09072c07020f01020301062703021c 67
    0x2207040c81d04035206003040e500b480d0060800c011406400740c0101403468803404010302c5a400019402061030345c44400030307000c7c41254483c5910454094132085800f2030b80f03284030701c041c080c00c541660790030030701050000240c010000f4a030344481c0218010710250764666500f1031a26030006180c08000750136030759807000900503000082e00d8030301b0781c1c00092625900d09102c540007034440d40320310448406070f18151100013155485030001e0a810b88131170070303480f020740700d640030b07c1c0c000c03281d441c0031411322001e034094188200070003c950585610016100e0282e003803e029000003044003040171401c051420002070582ca0141c0356030300c00c0350400500444181e86040998014101c1c2c1340d0301078402041c80c6000c000c00e01c001d9640b50000d224000c0000b907080301c400440c1c0040790700c4001e08812000703400218410320070040e11500660041c420041c680c0311092000e140280f01d143d450b603610b110811103d51810b41e00000a0b94030050904040c0b01580320140a10449010a01d858448440030300b032035064 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 539639595 1250 539638345 539638423
    0x140d02090d06180506010506030c0406050706090b0f04020315070815150f03191a0f13090b0106030c080f0411010221031801090f020f040b03070b040f0503060108 71
    0x3800f8940440088003030860000b01450b20f1040301210000c1c3d889001700001c60000301c8141136a02c80800c81400110f12420107408128071030000400c009409541d40e860111080301e046400d05004400c10042d4641000b1007019550401d10a02c6182410300c0014a0900c009169000c44900c20841c4201911031900c03104504002c1c072640740e100c506461401ca00c952050340e04101c2c1e01164001615204c00a00c10700104501da0361800707540b8120706092090052202d44500d6010308a0750305400b89040c41d00070804120701c10001200c0540c1070100140488281500c11410054410200820014141030f41904a40c00540c80300c2440c0500d00103d203085003120a450080800d540c1050034840d180001d14028400201001d111420580e591422a5681c202c06000e940c5484c0c0390902600704403041c1e0640c048003a1000c01d12100e00341c08a07140c0381007035000800c0301200050801c0040040b210410240c1400c5001d4101c5502d460700080d0703904c00000f052803c032940d50364808005480d802c2601c4c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 539640845 1250 539639595 539639603
    0x10905121e030904050601050c10050c040503100f181703040516060c020a060305090c0d081308060f06030a03090626091f050705041707030b0f070f140d02090d 70
    0xc120400c509110703181d80104003e0790040d400c02e404544298065015038032800c003a18001d11050180ca8008405001301806a04c18001c041001050f2030f142880841041c0c08429800300c4d0250390340c541c00040304c84120b00040b4070405468048001400000c00030ba4041d90b0320300c3e807901d94585040080c2042408201c5805504041a000920759001004091540e000300c0b0501200caa60b03140c240c0680e18111405282504408a0340506180105000c0841c2c2c0c060006241442d0703105000703244c220403c4d00080d40551004007000003501c0d86d820015070120041c0c018111846540c1d401070400c24040c0a4141400030069030b444104090307580001d084a20000c201c10107040540c00641c84251652a5000b40c1c540d0880d01a1a00b146000701805504d9503942c0c945814904400c42d403044000014070701c1940180d00d00000454030135001c1500864a80a101d19a03003408400645018101c43c955002d101d03114038012450240242aa0200c54078030384007503a0f500507100041c510940940e4028 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 539642095 1250 539640845 539640883
    0x110403061e14010f0602120f1815042c0f09010b0a150f0e060f0c01140c0903190f0807060b0a03060203090d03091104090507030c0b0909011401090512 66
    0x90700d10042e003031412a116464190031081c0c40e103408076160f41c28200076004810003004070b4105061b4440c010300700300c0f06290801196050410024031034030741400c45684c08410114060112441e00c41d4420a0260300d810742030f4000002200c0c6045030320000740081484031f656070001e0b144c2002034200d000c290074010b0004a0903a2110701d48500030b4035651025000616181740c070503c490058000510103031004044a0800000d8141e60031540d00030548403106540711140c241c1040100301c507250242182c1b000c00b41c1c5400000d400d25103000040080b18440280c00194540494004001c1c0f54416401651a82c1d0707a45041c1082c5001c1c04802c481240c100a00340800414050141d0156001d02040b01c1550b206900c0584100c095906e180400303032a46804101910040c60154041c480c498807a0003900c8004c4c3c0e03240c42e11070b5114860b6000c2d04d80c21000207410328151034404101030240000f031141c19020030755200000c0440c4142d018050103808011000e01d400f113020055881c000e00d04000308 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 539643345 1250 539642095 539642111
    0x9100315090e10110c1c12050c21100306020306040905061806180c2806050c0d030c120b010207090f060305070b1e0a21091104110403061e 61
    0x12641e503004403071210400f514000c8049891607480c0203e071182115003000f410001d031660049045040c07160b00368010300c0780304180764881c0755850294600c01c201d41403504e5202c0042c800d045c180c241c41d0712002948030110348200800c07480d2103240310080e43d03000200140c607a964500407030000c0000e042c0107401c5104440412042001699680c0c00d43c0030100240e5046444954421498078002804490030360000c2c24408401d003000d40e080240c4602c0d240c00003040f1001c00c0c890f1240c450f029040800080e40c00101024500000c0251040384103c502d0204080440340500420b2500d00c6001360720015240c00c4d105080e40e10030030031741c4060104c6a2080101701d09242040c40145098441100c01d401404e500048500c195800d03030741050582c03042e400e6103002c184003500150780482e0031a0280701d00350080c03406040e198072050211500c4004006802d0646081101c5260145101d65100741e05240096040d4a1507905681c00c5030b6020703201145e9050700f0401c020401d03a80301aa804058500b4146c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 539644595 1250 539643345 539643371
    0x30f0d020901030f0203091203130c0806090105010e070c021306050603100302030f030a140c0a08070f050114010312051305040513032714012303150102030910031509 73
    0x411909a00f600c041000202400041040c0c0c0011518640f0980041e00c500c062000c42000840d031240c070340104888006d5a40e6912040c44032036400c0003d01c0e42c423000c1002a4290b0920410b80501508042c0401a25240c04000d1034a03130407000090241105004140940030702e81c001e40c004e8a03005100e41e850340340c500e90714046103000d48001d070301c240b02e40340120307200c0c04006c1304840202680f5a0703046814a445c2c070082d15640e0012141d54101d1092056140208041e00302600a007032080d96840882a407a0903d6401c2d0b5810201ca070504120510042000a9900f0b0380745000d1515801c0c56519500100d0040c000e64185a01040d0058102010468100724660003514001d210741c0301d03034660f000083c2a480344074044c402c0900a02810241c14060308008920904070568145022041843c200200c48000003000e000201c500300f002c0284450400401e1b041d1002c0031003840110308011656000840303d0a000840700d040c10742d501044861450751424087c00760603800c8040c0081501048 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 539645845 1250 539644595 539644597
    0x50d030c0c060f1803020604030201030b0a0f030605040b0133050d09080c01050702030a081906090e0a02010207120b040813080703080901260a0507030b04230106030e0706050c030f0d02 81
    0x14000d0010740013601060850f00e1960100f030682c0e40160409051a0841d80150003c103142c05071164070550b01c180000b00c0c000000082409180705038404504c5003424502070740c3d2214180c0110401d0a1038008101c0094410a403907842a8201d80c2032260300a40703c50281c800d4462441081c194030b04206031501400198401440e074901d481000704003607074503180d04076107900523019240005024000440d640c1c50b0181c0c0003260864440d40d000031800e649081502c11141000f45030302c0c2c940c05c0440b484083d5a010f01c604002040e400380a0001c4103025600d06070700e0800100000c0c074194010071504103484400800030042d1809200326a580c9403031f8102301c42075800c0703149440d001400c29918102c85a05c40040340740341d201c156070703030300e000e501c45100800103020020012020550f80301c0e9008901d65560090500d00071481180002c8901c05520402c0e15041c1600500281400c10803914081100000d0000c119600da01c2c02d903858541410701075040d88a001000701840b0300200300c810990304194 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 539647095 1250 539645845 539645867
    0x609021f020a17131202060d020714070b03060303090904051204060513050307050d080901210905070512070e040f0203030301030803090c0d08160c0b03010308030906090c0307050d030c0c06 83
    0x200b840d410701c030b0103484040001c1c4200c003410b100a0300c10300c00c10408804001706007120a031004010504151031025044226000041c082d035142c400300c1182440500c0034001d0a015000c1859414550329041e00426500e10600c9000382c01101e01130002818000e0a004103602203004020140e81d442d0350320401003140d08201d01006082c4004440000d2500c0c0c00104a01120409004900b81d00360325181c0810a410201c0ca80c1c0c144a1071100201310742402d011340c510491400c59001520030b5a60038142d20b032100f00c1c0c108034000d0340c5000405920184c00079602042303c40801c001d511f9995949400103105481040007501031001000100030058000013840c45140000c040325614012a0100b200240380f820000d00512020820081c03406d0810070003e6202d0700034811781c08d0b181c1d5a0700040d1840d0344246e0080da08244080b081c0031761441c05000e51a0040002c20040c9100703020344000944410003842210300c50710312a1801000c140c01090802085a003100420524542d03a20024043c44104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 539648345 1250 539647095 539647103
    0x13080d0305041a060117190603060c02010e0303270715020c0f0d1502030703090c090903180e0106120b180106021218060a0314100911040b070609021f020a 68
    0x200c0c50310f8400321121000748036070b405030760313040403141d000d1402c0e00707269809407040213802d0316801c4858111444d8010701004504c54103001030170840c0c8040003800c441c6000c1c02020150010414042c1101d20305070344200c10006100e444110800500c01549404017560100354403101d02c00c990100035401044802d5045400d4402c98211102241040020568440d0040241d002c440d4a40710ba0091a030203998008064200080c00141584035031030a841964400c610054403048520101a4841580101e02d0030156021408904140d03a83c586442d050180c1c0e0200a83c1585000d2001c1c1150041c400074540540f03591480f0f00c0415046584490900501016100b4000c00d24203000a60741140c90740710980d134200c0440070303d1908102c1c156000c1c0e2449400c140c0c0f0f81c1c00c41403d48030144030460140300b2f614811022207261806440545d24141407540d82c006007880108040c07400d01c4115091940d0180e000110040e00f4800281800100c0ca26001d00f100c03045441407043d034000403019131441c01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 539649595 1250 539648345 539648363
    0x9020d05011413270501090611070816030e04110309070b181e0a06090801150f031e060f1d0703020d0305031812091309120513080d030504 61
    0x200d0369490042e1020544841d0004001c115040340d0402950043c2480c800c60516504c075002011485900300c444140e05880c06c0c0d40d0b0322090800c201962041d40e0001c561051281d080003400d841d140e02501914404034007044400a0040130148500e50700030a46400800c02c004030340744004d40341101e03041120b61400714400c05c000454400858001e4480103081074011a00700c03049501032250022409802c615441d80d111255001a90f451b16500040c0a9990b6030301003040c40c1500382400d441201e84284202c9451250070701481c1900d1055806a0750400c03180f4480421f444040c1d6003140e0418405030a1910385031b5600c1d0240700c10f4000481d0101c00815403400401101202da4846c0d1032484021751003114610300800090191011b141d11814214a2655001d001c100d40c0d4100b0505c80b041c503080100011303044c616494220b4542c1745000b02420100300342505a40c076156610034580750141030080100b030341c52003071508013040d0f03000c0e0407524240c600c50002260040d01418040c0c8085500041d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 539650845 1250 539649595 539649599
    0x319050906010f1a091203130b0702030d0813170d0c09081507110a050109020114191202040b0403260711010f110109240204050d020609040e0709020d0501 68
    0x180018403141603c1210b8485002c8619100340a40d00a442d02103d1420340d4090143c00001d944003000488806002c00107140c1e100550313040c0b81c0c134000254101c805211000e01c10040561800523022400d00d5842c04c0c03048140e290002a01c0c00b504000e60028940c500030221001c041d81c240d0b000e40700b260303e5080188005160072105450213501401800450b900c407201c4900381d0910488240d1300820b0724100032442007032011600c0e04191441105840c9c50791110307104011564080c00030400307508001c1625091500c2e640355146103030b51020560382003241c655a03100c0700014650480d8000c002e803035502d03942c0e143d4074038200344210700700b021084c50300d54064040314070705044034110f900050b402910b1aa4130001c040040da4407003000f944100821081c0040310b902e20009100d19000c0c41d00599205c0c4000b0002c80c2c419002c104c0303146072160484c3c0140001c000b00d8590842c1c080503164115181e81d11008000c01260003001180e00e458128803540e8400903400d061a8020012000d5648081c0510f07a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 539652095 1250 539650845 539650861
    0x30801050a060c0210051c02040e01050d0503181f020601081603050304150903020d0308250207030f0602070b271606050d290103050604090803040201180b031905 71
    0x440511402c00410703400c0310301030010701d40380050b50301905031800c105003054102403140701c408980c004d049468550010b0309000b10140c220046004040885090345070210740e507a000c0c4c480c0034040c0324a1040345480100386881d900c1807400c41c0c5040718a45030300141005200700950350b403002e1054503158040d242d0200034041028569200f82c80d082801149003511b011404c0d03080320501d2240b03104101c001900400180d40c2e2580d01a0090f0007a0f40d245d000d41041c40d00e41d1440c20010105603001200425005c81e80751300403a000c0c0c110fa03000341001c0081031040c01c14030040d100f0403500420801810080041d071040f91404140d111a615102080702220300400607540d00d000c40d00b2204200d0030030002c06c100c900c039400034071940303034080380101e1352800e10110f00c0ca01280f0081031404605142844010b02d503494421641c0c08034044805102007030494035112514403003d40040c2c100111000c50b224005001500f42000705210340009969281000c0c6908003540030941582d04a030905011840d46 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 539653345 1250 539652095 539652109
    0x3114101401121a09010b040c0302090f0d120c0206090306010f0602060a09030813080d060e0129030103080304031e0509120f1209190e011410050a030b0d0b1303080105 73
    0x30f0b41c02200d0701400881d4986000c0d040700001c008507115900c4000700000740e03c1c3e500600c810091b80d502c0242c1c0381d00f480700800c100c5c0843c6445950181010f8901c060101e01c4c18111402c2000d840c1c00c100306242601e0001c25081d00c0340d165a02c1d050712555000055034a00c3d040403c017100c0c0ca542c03d0310100d4039140c8504050311400c1c00701030b000444441c045141d041ca24000c8501c07541c0305011051805031059440c07803e5030f05652000d204104a0401040400043c84884000c03504500c5540c8041c10807a50b0302d8214003041c040900250400701c009010180540da0881006051031507409201180c400c00034210342c030032034055000e520661110641608001000315500414901621702c84c3e11120b0301e96150f82005061980c010303041c1c014410b842c0000e8002c0409400f28882d1103242c1d6050110000002250498441c096020320b0a26840d50b81d01c002541d10007103a504d000700e518108800024800d100444000d00001c04007802d1140340d04020a501102d14461303104c0804d1681e070380c000c010035 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 539654595 1250 539653345 539653379
    0x190f0206070e0109030506150906040c02030d180212072c0613061805090f0f070b0d0b040c1707030b0d030c05011103040c0e3114101401 60
    0x140e400040400c00c1d45018401009800c030040c54607100c1c4d03a81d01c0e110702d4504142525042d803171104071900c8000a04204595540c41002a9810300042d071020000039664807401d6011f24034035076102c2da048003a5103203c400740c840c907400900038820203204c0d8145d507442e4295442001c013007001c040d0304808441c0002c14400c2d01c6042c0071621501c80d03036501d4240480710000c6128000711644e607100c0070900d07441c544003030b42a890101c9000585c501d02415401d02d419480b40700c50348580d0103040c0307212071080b0003d0b0300030030390b42014240d6844442c0002004060502c6034a100c1d070260130044000c4403942c0c4168280000c0d0b05a003444072441e110304505504607401034032825005006001904007007802807040c0800703540305000005105000e07010082c115001070780c3c100c40007600b09804008000c010b01c0b41a4000703101580903131040400000d5a900b40055242e0100ea01c0200b12004091046082d11001c060058806582c0072060380c0c1c12003401819070028801c03507041020b0010480a02c1d05900d524 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 539655845 1250 539654595 539654597
    0x309020f040c140c010e100e030307050d0e1005040b060d0201021b0102030d0e2514010c0f0203060c13061110021b0d0f0905010309030210050c0904060308190f 70
    0x14400584509000160188081100c1400700c000030941c003440f5164010030002c00050000550b80503070b44100d85c1812520b402c1e068146003012608a000b0030080102c070381160729400e0041e6503200881510001e442c1d003002d000c64034028180156550410f9400c540e2140384154cc003107540d030792940e0801c0f00400b008000a0700507441060307082c982d141e502008541e1800e05004803410120005000415208000e01c24400e581251810800368044241d00b03501c411070007044498100e040c1107900d40880d10180807203040040139000c0805105d9559215944190080d064850714542010042e041c0d5014134640f00001407205400074009110311100c140c0c400207800500707001c1c00e1020043c0e000e500090113406040030350b075926050b00041042140392618140d100c0c0107c00319800c002030714428040d48054141814020f50070300007640480e240c01c17019502d4800250303640b240500381000b0302a004890717405c40d00c1c01c100881445220400f600b5501da1001c004a806694030000302c0d43e080111600e10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 539657095 1250 539655845 539655859
    0x1203020a030e0d0807082101061d130e16081914010e03160510060b0901030c0519030204150c0807080f1c051f0f031104020d15080c01030902 62
    0xd030000e031082d4414841032030000c00418a28095881c0c8407030550114604540181e400107104110103413a102c102480102007842c641e0030340c035059020303110304010703514410205d5000000078019901c1e4092258003005258040040212a15109943e40020301c200c207000c061200780010340c60400070701e007905408028000c140014840d03603110700704045d002d0100000e5403a12042ca441b40b40400140400001410f448402c180c40360500c2410200d051041d96506400d00380d0030300c0303404c0c240d0048610400080c42c00094524510004075000c0c010700614107150202c401014003900da054000e04152903c00b54a040365000c0c04c40c0c00d036000e00048200601d024418400c06010070f210401030502d91018843d0b40c0d1070008076000140b6807140d510420040b03259500d0900c54001c1151404103102455105a84450380c00e00d1a004c042100742c0c07000400018246d45a41095111501516418000780f40b050242c2c0791100040461030b6250701030102c0901c2404080c1d03005604c207004031182190003400d08 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 539658345 1250 539657095 539657113
    0x90f11030601080d030e0a0b04030c0605090d050913151d0a0209030613080706020d1b0206010503030d09061d21180622080d030b0103021c050907240801120302 70
    0x150050319202030a2507450007000d0b0500041450b0788c00c4640f02c3ca22a558500907501c0c02e280030012500041c0c04004240d000e01c10041209030041c1c1114030440c4110307445000d5024410f02c42e4044e20003e80c00307580041960000140c0402c070b070201c1c00c1081d411081340d11110b03519144840100d000d17180c0899031541c054004204500c1942100801c1240200110b42c5800c201d51220400d0764868003242c2013441d60b81036039a640b1045943c481842c41214030141910b5458000000e95034020490502c4015070342d20109020000320380d101c14807031020300020030440d011554034207844400400e442020308080c41da07007880296252080340d5001703c94079969141c00c00d0070740c2440815009154221401010071000c0c014050460321602d00800a04005044070a80050014296490000e140d4141070060080c42110303540002551180b406c1804009480d540f0805030a1504a040c0e00c80d8090340d0300c2021180303202e61226400c0101072103d0b2034840a80e40d03a075201c04c0301903221100250050708500d1741c0c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 539659595 1250 539658345 539658347
    0x1030b043e03130c060e13050606160605090c011701090903091211150a1202070c1a030108070b0405010215100906090b0a06030b0a03061e090f11030601080d 69
    0x54501800000c0a52000c82045140103852541c801d4580d00c40d103911543d820010001d0095140e006000507280c09400d0708001b501040c0d210392111036600c9800e0700c402c000b40c51a02c803081503480d07004840a103549240060f09024008040644020030180116960181d141d4000c00000c805100300c002100310603032a040b9400c00500250404500300302130100c00085c1c00f10016680e026030790060f06000d400c00d81e041c00300030350140c010580d411584000d0014a9006400601c8a44c201c080d8103005a41c5010510300500d065015401081c0b034181c01007004000d6906050155040e00c10201c01c852405885845030545070190340b040b01e0050340a0f04000c9041e41c085012950402599400840040e482d11014070694142d50000c0d0205940c403410034000345400c59803440108914201040086500001b041510210b03010141807503490702c51f8007480c2036001c602d041c00308020400c00c1100d440036103040303a6054000541502ca0000c0c01008020920700070405904032140782004050b201c1600c04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 539660845 1250 539659595 539659661
    0x606030f04110d030216170a1b0e0112060501140607140c030f030d2f03040512120106031b081f08070f050306100f2706090b01030b04 59
    0x80b0b0360203000da80c0034500740d29502d003802c500034842d802030282d031900e54000754800e031a560f21600040d80c0328404940c141c2ca020644094968004040101040c0c1d4106084c12620304e81c0d00c40c03902d0540c6900002501854800c450025500c103002c00d00c0507076640c240082c1e03031001410302650f1084041000c007001564207448a91002440029200e20800040000f41040c3d1841340e078035200e1b0030000d0000a2044a8803032441c04560050f044e81490304066100000c8806600b00042001d8002000c030301407000c01c1220049100142c980c0b00c2d80c03510744110201801d0002e209282c08a8100041070040310403600c0003c0c0c4542c459624041281c0d5143c41268602c0074145860440b8003004401040a25041c01603001401000300c510f4841880e20060500e007403001001d21120800324002408400582e080305801c8440c10a0300c201c46020110708198400c2444210540013443c1a600281c4000c1d15040013500f407030241c0302000032054040500c41a1003540c040a2010640518840b0103107074030030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 539662095 1250 539660845 539660851
    0x90a0e0402060f071a090105061002160b07140703030e0901150c0b060a080102070609020f10090b0f0d1d070603020f0319091e0b0c0426030c010c05070204050903030606030f 76
    0xc00c40c1c0d14285d4100038415960101500c07400c0c066519001000120308010180c0c0940700d903984000e0151507960502401c200102d40220750301004d000445509006081038040d1680c82d07900e05842c00d00e40d69240280800680c140d1032030040441400000c6c541500218000000010361904640551036035a8141161002841198010311384030000c20040b07002d2002e070810700d10658000400700013034010882100040c0e000300d8482e082003011004880d92000580c021a07140103045612082861892500f41c016100c5c000740c094a04100d164080c0d0200c400041c850b80e080054501103a00c81f07900b10164803400c0340022341c4150802c04200c0400c103d0003560450200c10790001540c010950350500c80340d45001c0301c01c054120310146107007404068015203410a0500e00020725091500c1021030100011000780c0030103c51010101c45031900c140200c900350f8010130005c1091508054000d041e80c2c02268059010f60300e07040020724100300020491b80201c0c0d00070456801c1d95039071086507006440003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 539663345 1250 539662095 539662103
    0x1140106360e09160815040f080309012901050901120f050f01030302060702011a0d020a050402040b0d0501120203150a0b0405040303050609070e0127081002090a0e0402060f07 77
    0x303145142030081d4800041000d004103008a02503401c21207030040c40c20b26904240c3c103100590b0300d400c01c0508400141c14141052090300200036039a94200304407103036541b030b5000d00309074400410040c20751410361002124040d40c0c3c504031005542717001819003a100d2620541d0116104114400c0250701410441004114072000428480b005020b20f8040da1425200d46440091050041c420160103100180d4001d849100030040c03041081200c0c04c80d84106e80c0381c940039900340001c24080d5120303004880040d143c0031b401076643c0c9070b075007442c0402076104070300e00e60880d4075120000c90802d50301c0150001c0241c000b0010902604013038202e030b1444001501c0040c10a95540d00c00019403194025584128000c0d10b00041902c0c3c44010b0020040c002030068042204492441e0341603a0080381c0b184c8420324800c08000050302e81108503e111515810600440c851034030482c1801e42190001c00280f03e05880b8801156a919031b5001406800d5034001d501c60400d200c000c0da00c000e18400b41201d0342c05 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 539664595 1250 539663345 539663417
    0x10b1c050106170109140c0a030f02012007080c0324091c0302030114010c052a03030c0705030705010206013605040501051b09060405060903010608160801140106 71
    0x18440d210841c0d842030300f01c600341c5651079081d40b40500a0800742d10424a5400340640355846245001440560382404000c008101d01d42d540070030369110f4501201e041d18603101842c40d01d0084415282e444166116403091441406c0c003481e02410702040b0340d03d205490789041100222040650040340310024021010703441802d89481c001c1400301010260030a190318010795a505001c0112950b07140404402d0600100500c800c001500001d40d4441010500d0903c4202155007041d81a4001144a48551621000c6460401d040300072401c00700300c0d0707412800c8500c0c0541d10001a41c44135001d01c140c4460000a00c036624141a40b00046043c008520800c1e50704040d10f580300a0032290140e4083e0b42d10303035680301001030003e134250111904081e40030309142412118070008415208a00610380103480118800800740c609402040c003511012003a2215201d81050044820b840351155440303540c03e0803103070030404070b000c0309044c165541582d07aa004115001c0481d0700c110245c14a0020711342c5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 539665845 1250 539664595 539664599
    0x210b030c1c020d0b1e04020f2206030c08010c180915050d0b07030e07050607170405040603080304200a0302010c0212060106091e05012102071208070f02010b1c050106 73
    0x3c1c64003040b4030040e115003415030b03060400001c500ba1040d03281c2c0700d00d00e0044000d024000075968241100000c2071040710444c001d201d4070501d801694036800c154a500b2400c090010040015946080e03042e81d0820008028807424001c00b21420041503001040e00140003100744a18030071038201d044140181c8480d140c04070740c2c48012404041c0741e00400d0b03408503d040b040c800303003940c58040c0700e20301100c4000510b603d50502000178968822044010301e06902100744d00010051001910000d1a005108001c80c0346d413824940150740c030846d0226001c101c0a582e080144e9a01d441c460424800500006100c0341143d0046d02c6900c0403d174181c0c0c6c480325108074030040101c1040114041e08080e5a40c14406140031032280c5201c410f030750542d10621014009000c1070340e2121448808100003041784052a01c4802c3c000000d20513014040c01d41c2d410030b0740c8082003540100c84a0301034181640d9a2000200f000d03c100d00b222448100e95601407001c0030a0584c04101084c4081e129009100000e5070907 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 539667095 1250 539665845 539665849
    0x403140a0903030215010602060a02091c05030306010f0302030907230d05070501090807301713090c0807180e0f0103051216030315090c210b030c1c02 66
    0x14101403211000603401d61070074000c2690500080181794074010000d030315941855006901c4603c01031516402d2580851031070305607510304120000e000002e074441b00e2011441c3c2800340c3c613944115001800f1480300c552802026100e031080300d03c10b2000e140078000d05da091290303101006601051011021915001005080e40c8035581c1c1c0c0d8110784600000d040390392800c4005030102019902142433504910b01c204040b604c2060703010150b00400e128018141c021401403a49900e010001608541c0b0f07100d011003d0211040007440603980c20b00c541d00482c6e54442104c0e041d5150381e1040b0000586e4403001c640111f01482c41c51244c5000c0207440310081c0c0d1281d024483d04181150704000c240c24100040083c05400d006c0c0130f0f03c41000c5101c43c0e1500c82a03041000d81860000b9005040560f1900c4640c4036811820f40e00300500015101031140d0240c50344010856042c01e039000c5c01c10000301d04238220140301403213041001c0701d003d8060010700e400e01381000703045142e000154407680390385d061510040e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 539668345 1250 539667095 539667097
    0xd0c1e0506130f06030b06220f060306050901170a0b06060c0f01060311030105091b0301110d09021207210c0e011d010519090905120a030617010501060e09040314 71
    0x42d000c0348103402c8070500c0c041002c0c1d4200401d50062091610b80079004c11103403101c0c411148621024075010381d9429140c282441c03070030072603404220106484072010800301d9058103c0421039104072140e550a90b01d0305031995181000c0b1100c200c10f5030062490100003448980c019602170b00080145041413200e1032140d04124031000e010007641d542e1036050003040209200c408100b04242c00070003031440c2100350300399600690b04000303188441940a0203450b590940050aa070900501040e849451061024015280c0c24000302d02c43c1d42c410031740201040c400104c0300101e41021140110003410201142000301d4103010030741c0e51000608000c0380100300140d8060081c0a000f10301c180350307154261104088030040e00a40e101d0140070302c414082503000110390040e151404000146000d603403414030b1a01e2444500149401008100d120085805030304c684110b803010080031002d542040b424600b00c5000740a6403020500950340821542807059009510610908103d40008107032002016a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 539669595 1250 539668345 539668357
    0xe010c0318050621010b070507060c050a050706080f0f0c160206040306051611030403081b010f0504140d0504081011071703041e0203061906031514060d0c1e0506 71
    0x204c134000d019615003c51010042d4018400021220301303042c4540d40342c0c0d4036001c0500c40d075010008180289002c0c800d06000043c041a402000c842e0290f544240c05405c0a204588150085040000003640712070700c10301140c0f10341a503c0b122441c01c400340756100480d6026820590b000ad9081c4404000107a107071250b0f031b000311030003402e8240390702c900c0c80000c0018050090400c2135401c103000420000c0d20030002d6991000080d000700110100c440d070203900401d000c2030349015450504d02408180010f0084e5000320902c02401d42d58061246803040c0c0305032241d442003550560240039994542125640464810f2952522061801080361074281c44c0d840e000c10100c0706e05900100384010802200c5903505540c1107084c0450008803550006611a04000d1141c03c009110329101140201113a0202d409141d1102c1c0d400c26245003228910000e00d80f0500c4814851120008180e483c58070b10050007100b544081d004407403508001c4d45503d0603800b18280032105610090209266a031540034000e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 539670845 1250 539669595 539669617
    0x31a030606150f13090b030d0e060a0e100906080907060c17040e0106030203071805010c06050c2b050a0b06042c010914390c0604050a0b070e010c03180506 68
    0x4c1540c20560520104c4e40130f00c110314442d6110b40886184150000030b80316503100f0844050345c07950350b50340e4240c8002000c5842d0560200c0840c114070f003d03a0304202da41040d40d01d99600c050341c550700c01c0140f07541c850003809224040f80d00150761400051004010600340120003000d0703070401d503440c0c04d40c0a81007020380003007004c29008806c200c9100c0d07000c1c8102940d062218907440d5503520b40400030b480c01c20a5400685000d4807540061603200c1490202da410402c0c1080304451100a220058403003094442ca08a0503070030400416010f02c0b4070700604101d664002c011030b1400340342c045010100e10aa403003402c1000c003124090654601c26107400350003000300d04c0d004030f03144121854030344003250010038401900c0c43c3c031004100c8d041d03612203000421000c0d90000c81c81c07041c90505420003d000c3c2e940c1500e024031a1804010401c000810217100e05481603800760703000e03102c6447c1030320301e03100c5440e500d0f0005075034414010110344189091200580d403c2c801a40301601e03040491083d610040c542c00d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 539672095 1250 539670845 539670877
    0x1505060f040f0906050f1608010b040e0703060b030c07110d1218030b1008060709060915050909010914090f0c010e0d050604080408120f1209071d07031a030606150f 72
    0x1f00b00070071040030420440d20640380403203240d03041c150884642d000d035006d0751412003860000100c05902a502c1a8003400420881c99200e01c4c0c804068401076100c00400c540407210086031940e281402903040e185c00b5449029840c0b0841a004c0c201c0e02c1d4981c036031852601e0045844000080f580c01c0f02207078001c0180112500311031307050072245031806901410342010864070b01320422540303138440320040545421000c2c102c450343c401c40c0101c505000390400c603035001c2141c07400003a60001c42c0c1d03c510303027000b9038210a0716650703901e40840c4d844546d2194028803e0300100c550300d507150b20402d414182190700410419441019880d25480c051781110f0481e8034005c0003034140b0282030100405451000c012140f80e00d4520481410b100c0f50068a1815000c602c0590101d000c41c2c0060207640080c00da030800f00c3e600300742c800356044405003055400e280400e1400403184100e4a5800b030101240c20041c0061496444190a1100c580d20f042c00d070b01c60092090114421441c5264001e04040100400030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 539673345 1250 539672095 539672101
    0x2071a0702060f06180114120105011511030406050a0c020a030f0f20030c09041403030a021309111c0605030f031803030304050a0618080c0a1505060f040f0906050f 72
    0xd00348198015013101d104803000100707800080c401d058840e05450350b101121003204c416602181000c0c00e039802d10259542444004a911410080742c030400161682e40d0a961607107008026480c2c0c030860140d107000980822618030198002c24441e8801c0f84082d020566080d130702c1c0c036580004c4403611011504405002ca0001c28800b90b6808001e0400100c415012088840c02c0000e681d66404494a805200303030f0800503052001c80040c0070a5299441c05480d924a41400304030000d61001c0c81c1c074082c3c1c020341072000c11100a280305140d058102000c4851030018980b04119503602498070404c075241e281e4001040300c1d00c00b030010b040140c0c104002152115a50541802003c0101e01494081d500030300030040410bc1c0040e10001081c1c20060001d0300307a254144220091031110405840c000002544c0b0b034840800140d25030032140a411140d03082d540d50b890450640d501581e0741940038038842c0c00d100f035500d89030340303d5902044001c000085d582d100d80d4440c825104121442c0034694000c0d410 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 539674595 1250 539673345 539673361
    0x9020f090108100617090c1507050f0c09070509120102040b0408060108060c0a051818040506090a02010207270f0504120c0203060103060c020a0f06020912070b04060302071a070206 79
    0x5080d0410b080d5400c0c01a040d003412130080100b4005a6078044a24802e80424861442803007070030324001000d0004021000b1403858540b4952001c141200c8502c2082441540100301040c00341844100070b11112950720303650300848480d000369180a502c0010001030b044641d5003440100010401031140f00c0d1198900603806080660503840b989440d002103003041113290b0170901710b80b65440a402e00c20346803c50780c8404501500c40c0c02a0b16001541100950f03440308110010030b00c00c9108504031940c50b40c40345031041d01d030014480020301603408114184011513030080b00f00c0e000d10500c8220420081808899000d0b140c03040b4000c6200c0755114248014806072503420700550b4440d06129040c0c180c0e55010968403113051001910305961203205120b000d109001d000145030700090104c40c5210241030120081d4405150541700d07800c01c01c1c02030088100842c181046513441201ca03420240b0340341041d0080d41c00901c003221640703000c803440c030080110520b045000c0d04040d03005081c6440c101170307 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 539675845 1250 539674595 539674607
    0x30e011410090e0703021908030d09061803020606090c090904140706091a0d020c030304032d05040b090406050612041208040203100b032802030601062d02030409020f0901 75
    0x26030b05841c108104011107000c000360000c00c8030350581e0310449110031a06d2a0340c9102c22034200041c680000644000400360a80040d0045030242d40100600c005007440b0f01c41285503404010096009940003803910300d80f0f80c110f00c0e8003010101c0780c9441c0103403034400a51141c0781110100d0395982c05861000c003140d000c20105025001c01e0428554031800d042035000c1c2400080108841c005001038880c0c2a80559010313650326000c441d0440341c072810180f5003c0d00342d0042c0c074a070803126003690b00c07400c8800000407090106000340d0340700d2514050900650a0030750340680800c0340c110b61242400a01c07502e076000104289202c50640c05418103180c600f91641c840341545200400c4400c00501c03000d80d0780403d481000b9042c0b884001581c12110300401d080240310401e91060545d0302010f102701c100b102d074854964510031003e56040d0fa0b2901020381d0910b02904001400d120304c0070075142800450f10040c40c0c19049030040340e0070941d035605014180c0e406030b403001c20f00d003a0200700702c142960848 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 539677095 1250 539675845 539675849
    0x60801170c01081305100606030209031005130b15060c070e0f100e09121902070503010509151f09020912010603030f12060905090f0d05040305120a030e011410 70
    0x1810301c0c0d45501000901541c0060b0403411006072050b280c000f006000c0043d02008000d002017402041d0361420050300035041034a20502900600039508860f0380c141c848c0510070155046041d90705d90303003515a2009000020118007281d4500c1030450155a01d42028080740d401c0000208001424403c0100d20039030080c00c00745150926a0500c2026000212850b05480082204e545283c0d81c1201061601c103c0101d80900c910300050310a180c3c441b9400b6a40310701c0115000c4035203460707413130040c1400c03182c00703ca101030150401c04172400c9451b00303504015000505003c207078240b02c22080e00315001c00480d0348803c3c603281d8001518491800c00309801e40118106400801c907061658030060080d2910780307019410005a00744550614555500400190014003c2088585442c0d45401d0342c0e0b0385a007414540c80d2284070340c9018003501c26030848043d2a0705c48080d21000000742c1004000c1c1c1c1240e8207030001e0540303441061344608424407510030801d00301d40c0c0a05c407508010032a018801116 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 539678345 1250 539677095 539677139
    0x501030201020316031b0311070f12020f031510030204050f0f010627080106030204060f080a020603070c0b09011d010204030c2d030b06011407030c2a060801 69
    0x420240c0c1e0044242c403d4109890202c0c800c030b0f402890212801c0c0c0d40200052a145212041241031540c000c816507a9000e00c403080741c2c043c2c1d407280495000c6080390312800c150b074103061740c0001c0141040c0c00d4042c0ca10700b0240c2200c0c2c1c07942140c03613000d4003800c0444944c0a01c1e110304008000303500e0513000d240e81115003200c5604290605030010444403905024210074001024102d030701501c90038603102100d060138005400019241c483c0d0502801c0d281c401644107609000010504c0c6038500c14103000c4600c20320080c25107040c258240b00c03040d0401000103051001160914003c51345900d049845085004000689148014007144035418000e02d6075009a1050000340000703004200c1d03241c282c49400566850304116568180c0c0d96800c1441c500800341d02d182400010030168046460207000240ca0300590440c44110426840c018514003800080c101340145020440b590249c98501c0c800c00e47c05003482c01072920745800503e440e0300c500c002450320001040120b60082c52042c00c01c1c09 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 539679595 1250 539678345 539678351
    0x1d040501050c0f09010c051e0312060603010f03030c020103090b0c0c011b05070b10091e0f090f060c03060b0f0706050618180a240e0a020109060e040609050f061003 72
    0x16400150303410b006211301c05061003090b44050003030140030441c40c601030032240d13040c02c40036004028094894004c410f00c84080001500414000e2610f2402c0d40d050b140f400180c0200603107140c50454400b03001060681c1030550f03860f0307000d001c11800c5000c5ca10550807100b074142c0d581112a5120f086072031181c0400d0300d03c9003211603882c06551000403110816009600740d0040c2d106c40344420890780d480d510035171100e85002846005aa4995500000c062803070404104c291601d0038504e045e80c250321801001168200d8004001800544c4142d42c00c002d0343c60002a0749880c0c120041d0307654000a8400c04010b4003090345404c01995010b05136200c1d10039500e51007061001c81c81c50000200160100c60101c00c512400c2c812020100011200da54000c201080c150040300c03100070020358a080a80745503410b104400014801c0090b82281c42d40c0d041e500e0300002841e000d02290440b80c41110107034856122040003400b440140211030251040000c01d04040c00d1103020090f000400300806001e15007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 539680845 1250 539679595 539679607
    0x3040c060e041e0b0102030c0f0601230d0803070507050f031e0408060606030615040f260606060a0e120102030a051b090d0312180c06020f120a091d040501050c 70
    0xb00f000881c049003c40c010010903400e60700700042c1d045000f800c901a030980300743c250b071510450001951504036410451003e04040c903814104000c05403005540b40c20600d03220482c0c000a0003500159032091071481c2c03203030520106507507141c141803420b65454225840400c000c800d09004030a401c0d8a035a4041c460fa2415190025542d2518402071042d4820100400020040c0d1100b40c10000369802c02100c2998464944c000c0440c446d00c1c40c0160510068422040c21680b40311904403424030850500a054942c0c80c20104131590f88036800d07082c02c001031401d00a805480e0121610070300401a0300240e260b1400c5c60202e0222a4000e05943d00300c80780d10034600c0c590240314202c07503a1220680c1d418801d11454181600e096070b42030b010140030340c80c00400300f501c43d002040009a1512413503c281c641552044101d03035501e1000d030307408041d810107580311a00e1084c9000030030231389005043c020005035645052011084a400c910340b40b07410f801c000c100800c0303401c4c07041561013042c50200a060074 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 539682095 1250 539680845 539680871
    0x10608030702031c17181002070323040506210c040513050a09080f070302010b0a0f060804020d1a07030b04020304080706020c1005010603090312050105010e060f0f03040c060e04 78
    0x2480302c0d064036a1900203a0b44410148100c201640c403420095566200303007000d000102151302c110006d21400c0c040d2140e8034501e4035440c02103c14068040e81d5800c0d0040314a00341030761030401c812405551311070410001913251100c2d4080c0045c1031843c1c84803101ca402d07010410005030b8000b0403103548807070200030511281e5901d0000841403440001c0002e49651303a01001e00080030305910281c210000032403607030728031010300c4000d00d80c080c4240d000380b001208080a00448003e40c0c020b04c51401c00c45403060049034803d800c2c05901500051000031040e52a880d160070703c5017902c005c1c800b14292a4200000c00307415014400396403105480451440c903150321040d42d98014500d00506481c1c0001d40c000f12940208036030030100100410400003542c1d41d441c06001012084012004a101e4200c900f90141c00b504c5240c3c100c400603103800082141800070840c0701d500012a40000030010301004100142000c007070b62003184100500c0503060306025002e03205800e1010098031403400d042c04083c1c40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 539683345 1250 539682095 539682103
    0x11181203040605031005180402010216050f060702270402150c06060d1b15030e0106141504240801080610060e040b0904060204140105030c0a082806030501060803070203 74
    0x1100986020340d141c1d12140a0074403049400c0e40701c268041c980380c0c5061f4a8a10451030980594400d800301c64030705440740c0048111181612401d580004440b21860071070400320010441280b0040160820301030520501c1c1c6010718403050100b030510303e00204011400c003456134000318030403c00049d00b005858012241d903841c000300716600658840112408224086c4ca0130710801c9032484065500948903040c0c40d804007030314002c02c80024202800108144010312400e404d42d510324181840d030100b0032052000b10001a00030b18500030f810840000c01e100007084124010580c6003c80f01e410821007001806a001070300700b49110780116051226401820309917404590160808200303607050040054001c12401150b5500588075208104c00c009243e0f0040c0141d44084640d00d02e000f0b071100c011100341c0070444d1040020941000b604078414090b510856114140c070a0103a003004081c04440c001541074001401c250361110000d004005003030150b000a80800e00046046c1201d6400080d13403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 539684595 1250 539683345 539683349
    0x1401080415090807020603040b070e010302071106090a15030501030312140f06061b03070c060302040f060809010b0d03030b0306010e0709050108090f0a12020d0216030219091118120304 81
    0x2199916032500041105100940340c0b84d50f00108a82e03100d05c1d280c00c2c45240c8010403502480080d03030f6216926010740c024825540141d0700b120003080c20714000410310402c2d61140a00d542c0c0401c2c484170009011078042d2005d8195106030341c0104141d4911325014013048035448042c07000a0503d903216006e4500d001040d07501680d61001d00c10a51a0980840d21070710034982e42e5038242000811030302c00480004010000284038401c8130100a585540440880c0541d002e00c110b55210000200a0300f03109001c0c0c07a400c8505000002070300d11800000071050403042d2000c44c0825150500a1828502400f64500410880b419141c03140b500160080941982d4004e2a060100710400b0641454042014a4a0503610411031305100700c14200041e0340984140d0060052140d0b610181c026807001c14400c00c40d0400bc2c00007500b050444d800c000384600c00c82040c4a40c0e960282e40043d4107000c9000e9211401c04941e0181c0d82c0d2000d5180010000307600513000350084404000b0014403920010403642 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 539685845 1250 539684595 539684633
    0x100b0f150711030601120b0f0c043c03030e0301110910120603050a051c080402010c06020c0d0504141f08041b1503050a05040c0303080601020c0901090614010804 71
    0x2a4a9000d450b05041c480c20a038400e54141c850a8004181b90380302c01425918940507848401e85540d07240040130103040221440c20103528207102c00c00010940e140307000c000e5440ca8003c0c90b07c104880f8083c83c0c00129030b802d80a50300c1c01c407010070400d25401251203c508031054009000076080c980c901800d621072258580d0040d09030103180d04526100d41040e044150b9003200a1124907601d09005507034001d030340d4054825020340380314507031882500601501e00c904980c035401c00598440e0019901c2c1c01d4914020b90720240c00300b1403020340c0c3c1818410540940b0b0035131a2203840760308020070510811148241d450050b200c00600e81107298079400c169030f00a50600d1b0014065545241c8006141d128084d4100c10001041e80451308000c1c00400c609400d08903541042144e036160203030301c181d58090343e0141c5240820501400840d01c540062540044103004942350001008040b4103034410991181c070b2151394a5600388209440d5880e007035890102403900800b14100754a400f0054142c50703400407 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 539687095 1250 539685845 539685847
    0x70f020d0c150f0207060903031d0d081b03100611010605090f1f081c09060e010f140a050c07050409081215040903050d2a05220305100b0f15 62
    0xd030340d6940e40d0410341015903c0d60040d5103d00451030004050b25140008402207401c011103036007440c2142c00d2040340083c2c0b0f900108005440f128085d140c0c0301010740628504030600c00400781d0091003030025400b603414a05400011450014028100b07810843d44003503507414410308120035990192042c1d00b04825007003401568544071000d580d61410000c00c01020303a5801400202c170301c004260218001810b0080d03081100d101141202c0d0f4000720b0140c42c004c1500d41c69030000c030354172404205100101504201c9090780045803c0c0c54140c203c0364030f04c00083c40018580210140034051200200804e4400b8010041980d581c5c40d22401407440040b020400c0070006902c42c0041c4d010031041c03701c0a44104200911414018a00c2c2c1c0702441449420f030030800e034040d000c01280751500c0714401c0034400030b09550304128100c416038010702e40b052000c901048034130120072624259000843c8102c000300024502c8406200c140c0d0380c07843d20288a2011000042c0c1c00340c0751050300344502e18041d1055 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 539688345 1250 539687095 539687123
    0x301020f22030605010e19090b13060f1b1e0c1704030f030c02030d0206061509010c05030c0619050106090603020a0c0605010e09011404050307020f031207030206070f020d0c 76
    0x940030101071680042d20090501e4000110b1844070b50ba003500500300810039444506041c007904041e41c07203100006009038aa0000030329001c0451100900f5144100d8000c100c0401c40c24000701a15180401080c104c02c2c8030181707000c0c81e50004807003421a0764001185002044480c005030141110100140003541003180b0912500707450012a4051030303110b01b0450780b4a0031070800401c2a00010b104034042d01c00c1c074404c030014a00000d155480366070010200507070316104a41d8680c01e50003070b0f0541e50500112040a400041d4180301400711503d07104d004028500d4942c40c00f61a04060070907150b0301d24503010050205661101e0b0842c103503103050501596030601303050300300c4048103d440003900d100d01c1e102c0007103400c1d40046817260080002c04000d000241c10049418038015059030b0051a0f0751041094100500f44000214084000101640c88212001e048101e10390700540d011801a000802000261900285660b0202c0410310040006180d001e001401900c84200c000d04440e00b91044 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 539689595 1250 539688345 539688397
    0x1050105030403180807030c06170c090a03150903230304121209060c09050f0a05130e060421080103050a030e03010f02040906030b1b0d0c0216060c020109050301020f 73
    0x1490304d13101842610481c80c540d1a0985500d0f62180d00007150001c040c50000504503104082c1540300a0402c034403070b18039445452040c65240d00252506800010780b40c1d000010407548240010584081107021400100702c0c5001003031101c0310050048c1031a1001c2c002d1112400101c26664829444030100680d900c5001041c0c0f12200c40700c0d4850841800c1281c0c1c0d03400c009481c1c11042c0e07401820340b10b4002d80c0f07880300100582100f0100446c2d800c0303440017604204504d06944102c1c0c4180c8a0480003a5009162900d9401c0060840d02a511600c407243d4804403070010410100000380b10f40390000301d5504682c0c030f10361140c45081e0003404200130680302c070056036001c1d40010b001d88c2402a003195030380c1e41d40392028041c0c0464802903032501a00000140d0402c000c2050500d04000001d6681c5042c6240030201c0c000c01014020360b0851289000807060500101070841c05000e10b529036103d600320600c00146441481d07080300b030199005020140301c2c994140240c403502c2c43c4070b5286030b078207113000c1c50 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 539690845 1250 539689595 539689607
    0x31f030f11010216180e06150f0609060a08190207030e010c030e270f06011b08040306020d1d0c0907110c090106031b0f0c020d0f0203120307031505030601050105030403 74
    0x21241c00003c4c50030f00011000003a82554070001d1603200180031814044a004d51140001c503004020001285a240d20600d0050440c5144040040031141000444804100b00da040020b240d004030750301c0e0f010702617080c446440690018001860641c0b92014690b4002c000301100ca1145051113451441e0004150003258940c6101b140605600100326004290b40b9103202014868603410303110001088a4040030b4811a2081d0f4040e140d0541900d000c2804851030745a221043e01e10f10b81c103000100005501e030004240140d12000045040c2c030b213121850805d954030510001c1075a2000d80c4026540c6ca540703140e154481114200302c081003021014044c104000b0320342d46a8860444000850300980540c4600103045007050710049401e046001602c000d010000d281d0045000740401c08010302e440c81c034511030503105d64110850b02c41c0030350103e4078040595040003118040401003201c5a40d140c0b04d101022201c504005903d0b528220219403030380018000e45042010000010b400e15000d03031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 539692095 1250 539690845 539690863
    0x30030a0f09030e0f0108040c0605070812090109021002032d04091e050705070308010e0a110a02070e10030b0f04020f1002010e0705040c050904200a05031f030f110102 73
    0x300107009a1001c1d150081030f280040e400305204051030501805a0f52250f60194030030b5521035a107803a000d080c414140d2340d40c1c10240c41180d210740e081002e4a04014500c00c030078021840c200c00071440951034410800500e607098413160456100f44140203005403080d0720700c0d0405070445c0070136007541410080c51120b8440e50f0042480c660504618205801d4064110000c01840f5142000581c036812000c55442c4280c1d08003400003000c00c401885110814002d4540100c41c1407070009801c9a9040d00c04071541101e8000d001680001504010740301c403003121036501c2894052002509400d541c0e078507146210240c0082c1c00c860303c001c00034045444418100d00c8854008000201d4184803100081c0600790107448204c16028404000429061500500d0002d40e643c1d1115400c00d05404c00348801403640094440000510444e500c58898010004000c501d8250352181d0303680c60100714000b204500c201008140e6500306000700041001c0d01c0058400359484202031035601c8031000100e151600350 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 539693345 1250 539692095 539692121
    0xc100b1309080c060603030403020d03110a02090901150807050303180d1b1403120306010e28050405220206030c12190b0a080c0d03051306080930030a 66
    0x20000c0c00d102e03004020b01500281041120f00669441040c1600c0340500e1000a400c01e20384070135040001d0059244c0002c0c81c1590045030b038040c020303400142c008107082d02c2d024100c1c1d555814162109050b514400302410701d0a004090ba2450900440c0d40c0784240344044865444500c00d4a409a5800c0c4a20462941048500100c003603d54002001c1181d54400d561035807800400d900003e050204141450059120106040d07039100e5006440c0021004503540c2d11542c4413410302c074800222010332007070500d01000d40540a051000303100440303602901c814008242002c009518010b10ba41103076200d94103070303003035074a0340c4a182004008c0e010303401088003510400c42c2004844503d042c4060818180820244144a40b90061201c00b80c49409030f0340460300510000c940c40c1c1000d0104c809042d2083c540149003070643c250542107500aa0802e90000d0708031001c0c0864681c01b04083c1c40c1d4072000d402c507854200f50082200c038000c2110302030408281e20210005d10315020325408103a000502d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 539694595 1250 539693345 539693351
    0x2040c0c2a151707020703020108010e041a0a0203160507021e0a090c0507021e0a06030c05130311010f080702060601030507031103090a0303060b1204080c0304030c08060a050a020c100b13 82
    0x21605000d030224800150740c3c080c0f8030b48400000d66061001598108a03a0103131181c840c540d0815000701e9a412000b402a2103a007080c2522003500340c1e034045900d01c00c070b5045100580381d0420400c0990b030144000740d43c10030440240502405070741c0d030b1441d04420509020700307241180500d501082d08803a0f2584103100e158540100c051810350008001e03e4200c0c0b00329a13452014207124007000d00503a0040704e050b04421005001d102071030003641b04003510f01c1c00b42803041c144903192070b8a0a0015080e001116800740d11304842d80c09580100c2c11816520071760802001c40c0ca04004001e565240081c1354604050302c64000c1000c00d8000d500020342441a031801ca40d5034502141038a595103060b2001700d0000c2d19001c40041d1603410b103015220528468040c10502d520749484151b15904442220f9480b804200000000503940030150f000070004a80580082d1a004c11148200c583c000c00c0f10180c580100184018500d010401d03004814140e03100003503500000e0302042c010351144a441c0c621a207 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 539695845 1250 539694595 539694629
    0x130b09010b0c01060f06050d050a060b13030501050903071e1a0a020a08060a05030304050423010e071d010c0b0720010e0c10050a12090602030403050702040c0c2a 71
    0xe050018a64015240000c1c015182d5071210041005c007203210750000100d0600c5200349100054021680103115403001045080c0c884103a0b07800ea42c00700094000d5030881910400822400780909680314007544d014509240540e2130307510301d41c005002110144040082144100180200010003520540c06091030a10709058003070000e6211821110200308903400180305884c1036641002036620142c00395003014076050500c40070380244072007410044184520300041c60304d0310726602d000703080d10940c1382c00909240e0806407000380f40c56002c5100004a094040a60340c0220445091030f92042250b8569903410f9008c9a4803917410700001c3c09510041e104220810054000b0704e0b00813400030544a002d107100040001d0b140404d01240040b41081c0714244c0124011b6561083c0c01d00d50fa00080342424940d134950080741e20440d0102d002c103202049100642c145441125402102410710400c1d80c44142c5800f000b0b01481720b101d08000c10380903000c418115070500144010081c140b140e0b0a058 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 539697095 1250 539695845 539695859
    0xa0903150501030b090c010f1d040905010605130608060402090403020c030a05010c170118090f0b0a060e06040b0904170405040515040e120a050a0302040b0a0801030606080a11130b0901 81
    0x30f1100791401501072000c80d0750560041600c0c0403010050712444030148032244103a6a0702000c0b10600c3c3d2001104d14243e26070344840c040c038164144200c0000450714107100810104400301390200c0e003000d1410406000800e400204680c12680403100d400d6541e80b07501e82207203441c0c4110350135a05070007400c401c0404c1000542240d40b010540d6162500702103604076454107400001d10881d4090f00c51043c044100b441c07981d220464a900603c034840e610707845502c40c03952450003642e0844c140c9541d45000c2004c0503001006980041c000c139814020102900006a01050041d1001d4400c604810700005800500000c03070b0300902015000344460302d8007024951120000c11507490140b42040d80c100c80e0030b1408149402d40d11007030000c46003000d000700070455198201c103400d0000d150b42000089412019000640410350781d03552000995030440c03400606036601d560102c0000d81c446038215002900b00d8280401d0030109030f41100a04104011030000703850803810542c3c12000d0381002184003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 539698345 1250 539697095 539697101
    0x504240902040b04020a020a230f160b0c0d0f0912050c13021219270507090c020d05070501321e0627010b0912070506030c0a090315 58
    0x103503008070780420495400106100c26071065805030340040c0c0041c2d000c0030025207010784800c05013200e13041700080300004141c22850001b82000c1240d007030780800c503052101d1171000300380c02c05003501e810a0381c14515601180c0da03940522860000034040181d04004081c0c6c465680c0b60014a84600801014549400c10075140c030000c0a05501426525007035810814150003182c0c40c503d44802074008a54524452845049000e062150000e4441510340c04018600d001c15240661200030302c0c06d0446545442031130103080d58080d594603400c1001007001d046d00030a600c070403075009050442c4d641406140503401411900b144580c550b10001d501840c500e0381003101c41c103804198010075401d8948102c0c1581002d405440003220300a01070020340300e420708854104a601001d0411848018140c20f09084602d098120b010f507640041070a010a1400c0c0d49000303019900c11000e0803049080102040d6184802840f207850230b41f000501c005042e120340c0d1074000540d000080b185601c6050503a810107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 539699595 1250 539698345 539698361
    0xd1b05010c0201050d0f0e0d1d09151212070b2d0c0a090503010c0203041e0b0405040b130e030a14030c2d030c0304060e011a240408011401060804030e04050424 70
    0x118407400c070b048000c2c0d030801e040e005015204082c21001c1340c0380741c0000c00cc022000c611300d10500c0d000b44d0a100d0752481d0181d010700400791181e00070130080d190045000e4440a03d40303501207400b040700c2501090001c0c14070032003504540800180c5640d032003810401c0c0c8081505900254040d843d04000c462000c0d400310103042510300c01d041042c003407103903420040341110035809444803441d0100300c100610f01e45a80002c3d05000041c240c0d1840e802c03001c04000c212a131001c40c500007a08006095110290702c40d0300c09803440c200300c402600310300f041d40c0d0000880c0200726030044024681c4114008001c4078403c00709006034040c00702c503903038640604201100e0f00156403c640f4203080c000003140710001806042c032802128100c0c40e00522400041200542e244034001014840f00f0701d00c10a1150f800009001905d012400070400304002c68410000c0ca505078030500c100081d03841070000103a40a0b81d403000200003214041803d450b20300b00320315144d41551800140d02120101c03150704603015002054 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 539700845 1250 539699595 539699627
    0x1e0d140102120112121d0306160e0a0f030b0a0207052a010302030402130b0f04060b0702030d020f03030a240602100e0105270109020d1b05010c0201050d0f0e0d 70
    0xb41d590f83c401d51080f403103030421001000901009203080240d4031620382c0040c50001129102c000c503d5102c042414030030195030070850300014120b40d00140b80c0148070940080001c4d240c0d0308110745401e000704c0c007145060000401c4260124003207029603086405070703480542c0003402d56060500e40d2139014240d202d451711400d6224800d48903c681580240700351382c45982c0260070024440ca1a4084400800f1a0407044d42d00001c1c140f210400c035199846200064814080e40990b104818010945050b0f01c03170701960308561091048580011020007601e81180d1321711004112030000b0100d00300c019114016400b8080c040020014145600140712409105881c000f0481c1c03408030981d15003628011100744c24000320a240019514225000118034903081000002e080c00303855000071f0010140b03c80a0390550400c0b00c0a043d186a00f00101d001001e0909028015044690001c5d1040c0210540c14220903500c1100e0807154090350006003208071800147d460b02084c800b80a400304512224281c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 539702095 1250 539700845 539700877
    0x5060f070e0a03030e1003060f090212060d0203150a1407050a0f08150d020a0306050408070c080a03080604050a14180c03060c0405040c020a06050c09090708061e0d140102 75
    0x155079040000008094070b425035141c101e041c0c0e0900601000e440c10b49410000c0640d508400164801c40f840c1c008060001c0d130700d016903140740940c1400c081020140c603051203400c0308408600140e82c00510510184603490011240e075450700528001410030407014842c403090842007084445c0d2003c000c04c4004c145071603014281010f510304642541d01160b06030210940c02c7c40071800e03860680d81054160344000c0c01c00001d10307200e40c0ca60040e03500c141c0c4c08480e0641d000c141c03101084400c0811801801d070300d500401552038141c40007095001c000d812940210340d00d4020a0011035981c101030010340c50342c064050141040700440304a034400c4d40a89135640600541d566075860040ad400c1d00801804081c1410203060004000040401c001e0600c151700c68400d440000407010f0041a01c00d0f0000c8400c0d5442d800c0550034400208001400d0300b0400080904124072580e0300c0e000c0421400f20001071648050780300b03010a030340d00c0902101401c01d080c40741400c0b0982c4030540041040e450515156 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 539703345 1250 539702095 539702117
    0x1361d03030601091806091b0e090702060a05181e1006050105070b071b0503070302010b010f08160e0d060608011a010f08060301110f070c1a0403080c0a05060f07 71
    0x20503180d0000b5214680043e0340b1040410400d410080c01d1300e43c0d145d0720300000a909076a1070b40e000c12155020a1031200302003a0003015100d0f60000d19400000000740c40701140b502e0b004400239224034004110f8003c013075554012503590302d442c0300c02000d00c2d8000340490b20280c1c1e0301c0500c081d181284a04400702c910904445403491880d5000300000c0b16010784a090401c0c045548103820071200401d400e04000d07003c00000490341c10518a140c2305402034001d180d0701d540c82c1c14000e0965000c0c49402e030500c2440c200c020030300e80c2c0c04030007507070301440001040d0302c4450310f8801125003c0a82485c076a000041c0d451800502c40a944890101da881078001c0001c0310380346078140c10308503410685502085054030100703c414040c1741403e80c010001000025a10078000003100c00350000b06007041711180100d41d801c02c2225a80f640380250280155030100540307640f000c01064800c0780002003e0f842c0200b4865651001000b01e00c525652280998240745002040006801002c0ba000310000382500c4034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 539704595 1250 539703345 539703401
    0x4080a0212030a0f03110c16030c0608151c050303011d09070b0a0c11100306210809011202090a1d070807020a12050c06160f02030903060136 62
    0x1114007100d4140c40b42d04186002d4074060f0010a16140e0764140701030100940d400721f80061190106800e0911600c2001d9800c60810309034200058128905020b407640c1030120100c028030850605002c01c40b00c0d2a1100100a00d02100308008a0010202e00c4084004921940c0088514482113a4600c54407016507841207031035612031b03091268801c81a01000044080c903c150361001c141c9008152600380c1c1c200c0c0b0808182c120b8a100411030000f5903940b000c1c4040c0c40c2040c0480c0f11450865040c00c2406855158442c2e14030614861034107100703460050040c01c82c5203030195075805d00700505c1c0c011016602d000303140113800780464007a01100409c000680356400f402c4030071700428543c1c0c01818090072540d00d050606a209207103506101c0c0510001050010400c5407600c5490740d0b281001c070306602d81c180070b40048400c0502d0400d54005100d48103894400092140c112000d4007500114026060480302e542c507031041038030354007100a40440782000711580190600446981c80c0312510826120 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 539705845 1250 539704595 539704597
    0x120501083a0f030c140306061312050d080a0e061801060905090f0c060f03150a03020301240807051806220b010e0423060f210d0c050d0c060f0204080a021203 69
    0x1000125145003407007c00c2160811501600700e1495008103201e640740c503602062004051018229041d50140a07040310301c0764440807454101891030382c10f00c81e07034200001d00d64039032034020881855089900740001d94103409421240003840c021070108032030300f050030480707440322121407461400d40b2541c580802242005001c032407242112000310380c2507845d41c030070080584060b13841c629408840214048056034084c0305444514070500a140d8014110b0150190a00c501ba480352100750840f0104201384d82710f009082070711403440f03024040182d0302c00340000c944441341d1a441c2c0f0741141c02c2e0004071140c8125840340400382400d0300d603c0c0344500500100025034610320200030641c004081d00441c42010403041c0c9400132402000e880c0c5001c420310115003040b03208180942410202810b54002900a202c04104000d0354548110180b480ea01d41c10350741e1002161b800c0812900000000c14044c413540202c20300703400a141950381d182da40d50925610100b00000340d02c0740c0f443d1116915903100c008 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 539707095 1250 539705845 539705867
    0x20703020414100b130515030a0606030606020307020105090a0807030b040b0903180d0203120f3115020313090b01020f0a120323070206010303120501083a0f030c 71
    0x541e0141c0b071410861504d110360428102c0941c4680c01181c04200c5d580d0b18080c25410044124070141c032407070900707152419140a60300c40d030185864448140500d69010044171605e079028203200341d840021201081645407164422002e072f0254407000f008014080c01c85600907401180350302400e80355145601c1c0c4078442c14000003000000c000b200c40c49400d042103003002c00ca000030280c8000254141301c16550b0390001c03102650040d0002400b401150300d030103001801a0743ca0030203a115460003031820303428580034010f940c104400100d00b00900c0f48200101c0d80510307960a066580b4595469410020700406980f55016001d09600d20036549000903980c8445034000041c1117614200800c150018420040c084104001030081003490040324004640207103481e50050100c3e61441c140142030a812041c208915030801c80100301000000034444401000c000800340044404001c0ca1950b2a00d07148203030000300801c1c041503406d50402d000e200c019205071401c1c007003440d89100850390b40d0400b03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 539708345 1250 539707095 539707111
    0x2a0a1b08070e0405030d0c0f030606080f06040b060417010b0a171b040905010e0f010510120b0606120708090610081b04090b0c0406090518181c020703020414 69
    0x1c068100182d1800c07060300c0350824064002d4138606141c2006900c1a2805140ca06020400b01504100c07120750503c1034100030300980c500f52045040044c0902552800600458406d5845041c00c814070b0340c075a001c44000b04907025048820074003550250340a03010354065203100c0c2040000001c0d503d44107089444000c0d010101503d5034030307008183d66608800c8603c2c0c56401c40d40d02c02c001c0f00013903001d109034060f01c4045402096900c02006185003034440044c507201c140c07412840200075101c03c0c0075120310801c1c1c1c04003820103259030718408100f5034000d4484c000d941302c10420602014a410107a018017130750340401518400c1d81e46007150304e0410490b114041c0c0e5944002181442c0303840f482e0401d00c0e41140200017061803000c0c0e4880601c819410758002151074030010f0104000c0f90440403200051900380d9400c4000006c0c8401d00c0328240303000309075051a0039810b050301410312041c801070718010010361a0041c06020b40d24001e40c0c5e00e00601040340500e14115040b41c400007100003540c820026 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 539709595 1250 539708345 539708353
    0xf0121060e1003150f06051801090e030a051903021312022b060e1510180c080105060304060608030d0209040f140106111c0f030b0d0203122a0a1b08 65
    0x100c1c4a40300180540000400c5c04c40e594034003c20701d96200c2c01c40309140d11b07808130040d40c19418500084120744042400402540c41008418045a04401a01c0411084c600b0303210110403000c4040d4082d11658080c010003141502c1c2c041070007da0000d100038424001d0f60003a002038800d001202d43e40c50402090481854000414000144650001d210340502e00003500c2c5090341c501c1048140d00c40907a601880f03440354410902c90611403122076500d13644071560500414101c1c440240080e41c060007604e0290340700100040500500c1d0f004080241149412a5070300d04041d034a04009400070402d82e44158144400d1146000d1140140303520040c15800300080c503483c105080d079810849001442c03281c003400180603041d17546034000781603103486503c0e140c41142007448002c0c1143c40c8172520301e20800c00c0044440240c1c1b400a0316140c6041c907509129a00c10359103990a484a0f09000b1124209444004a02d2a09008145002210b1148009940b60100c0c1da10340c02d041807042c084d111140d40 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 539710845 1250 539709595 539709623
    0x1104290316030e030c07030b070e210f0a24060f06200a030c02010f211a030303100306051308030c0711041802010801080d0203090f0121060e1003 64
    0x1452122001c00c03851039040c002501890402224119000302c001009103401c1030104106014110b2286075101c049807520b54443d40e0004001a403130b82c00b91b41d02c1000c901650058801e085810414005880055404c4851500540c541126403d00c003c41c0c22140d0542404550b031410307503901841040d50000341c800d046075030801008845c006420300d0401025518280c0c0c00c07110000c02c0c800c0c600013a0196880c05d031400c010f40009030452020f81c0d008400c01101040030785030a0b401d02d06001104850031004a120b12002c1c01c1050500c0c5003c11a0350301d8040001403125884c00c070150315003240e21401090205a0750302180342d44038a10b08202405a65007040042e0200f07903020000e1075080e02c01c1801c40d40740102c013808241141e6012101103503810152081c0c00556030004005d030300500c4d0144c02000f1100e44800001d49034042c01603840d0207074096054001a0740e01901006000301250300d4030071b03107851810000d10040d0075548908240c0c3c180543c041161110082c0c0388030b003901e41013410950290 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 539712095 1250 539710845 539710861
    0x103090312150b070f211b2105041403030a050703210504050a21020c0d020d14100b0102060103020a0509130b070c0203070f0e13030e0411042903 64
    0x41250b284204a00040c0e1020032901e03030030030103411242e0003081c3c044482d50359494401460201010b01c04415041090100c1540390301481d0a5031507250f1404040f40211280b90101d128000c804282c401c084044201941c0c9642c84400340c0b003150300180e441c8442c0780d903403020300d0746a21500186d00005141008242d001ca0f00400054410002c202c0303480181042c0c0c1c3d02ca03442110401e0714101c0d2150440e40342a420310100020304003070f940316552400003071101814043d45e50071100034024014510003061001750340e00c3e4500b4904494000c01c3e030380c0403015008045a26041984c1002e03018034608a0021929480040d046058135405048004154104001c12040c080c1c001c0120026285030340441000440200c103c60040d907231030311000303410000c4e841058100b041d103411407445881c01c5103007042404100c90855400025664200582035500d0900b00d410741c1810a8264002d400c0800040002560400030801c0b035407104ca29030800040c0b11103902c0701c1c1980030442a8000000c1c00030070b03904 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 539713345 1250 539712095 539712101
    0x141b06041d07020f0706030b01122c01110a0806030601080a030905121603030509010e03060f010905130b100302041409060106050f16060f0e2811031e0c0103090312 72
    0x1e00e00495000a1031311001502c5c0994a41200d00000c0c0c94011604131540c10140708103030141c00b0407041c045640581c3d40d0400030380400034906c0750b4040e0120350690b55031007903000c07502d0052030518003580c4001000c0e0150680806440d202d00030302c40d040c0002524480407600040c0140d03d650f594512078504000c004100304442c0d02d410a50084180b903103036a12198140000071480707074850644440b01100007400c10075204600c640207410050400c4410342926000300e0540c0c1400000189079120300b4508045440d030500000e00d07030b5a502d0180902e500c0d19089400480e44221070902040391024908000b64400341e8800c01154041001030260f01d01034809000a410300d843c406003004100c16400401f020380c03000a03508035036503004020307045006000e6842030b43c82c000010070410000750b2402c3c040204611403803a142d4402c1400343c0401c0700603058805080340040c1240c511510310044442c1c03114140407203801a115509034000d0a50003401851600d42c3c042d2038003031328030128200300805 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 539714595 1250 539713345 539713351
    0xb010509091920040c030b0f04060f150c1a04060b042c030c010c0809010e030903120904110307020c040b010f0e0409210507050709060e010b0a0309141b06041d 70
    0x10001d00f07169400640d122071142c000d6400199802290507109041403114044000780b10900585c2880020f10000703182d40441c104440100700d0070890707a8800b40044440440c1250000c002c203481c111049100700701d001c12039020390b02a0000700710b00c41d40d0074204000c9480f0303040700200c4520fa551003407010740080549003003004608001d403445e01407440c01542c2100c041c2c24644005c00c420209001103d40c0c24450409001c507042e00842c40c041e0301c1c0e40080c0d520318044901d4205c4000014280c0342945a581002c10760306900c004841c0c172410304006c083d4580880694580c010737132400d15003412640c400c11010700080b10700d840300b4042c01c00d6403040c0000b6142c480010b60385005030700380280814000c12490381e143e003070a5070380300d403651614a0941e0a180079503100d01051801c0c81001e012000d400d210b840d044030303800c0011681c0d0300d81e5070710700790003030988410007828040070540c1c8a26442404503074000412480b100707000c000c510300c00c100442c90180d409011424100024070a0440c0c3c540540d01d60 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 539715845 1250 539714595 539714633
    0x60705010b060c0a05060c0309120a050c0a0c031b03170a090e0c03071e02120a030f05010905010f23010507030c170a0f0c021e06040b070b0105090919 66
    0x20700c0031041d1002c240154002030340c100c4503034000845481400401e018054004655210032451400c201c00d0b000e54031041450109200180014032200c6203000e030088440096a0105440300c8001030b080014483e4000d1000741d0f00c92400b90069042c280c6080491421349500c458125450303034119000110641104102505003c2e1603003010400400b9184940c1c4900303001030006035131b8507040b41d0080071401c0100c40090f5075080c0b41d0780000c0c580c3d00031520700c40004200b0440e0303455491000d0101c002d81080d854203d1801c1c0fa003000450302c00b0054009506035003540b0310350407005079541a41032411000300034061489050040c4107001d036100c0d0009081850191401c50b13058a01c54962101d005005003410310850700000c0c1149010385c10034586c10130107159061601c1c0048190f00070812000c9141041c0401c0341030b03030104444c40e6480e20292405400110140c0d61505c003940f40480400c6000c0c000e041c8103010366030014440c01030014000654502102c0c1a0141c1641d550b075400648010f242016 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 539717095 1250 539715845 539715851
    0x10326190806120f0c030d020f070302090c25060c0203040501080105040513080a0c1511070213062303070e040c090203060102010609020a1d0109150e0301020702060f0a0305012306070501 82
    0x1000608101c4d06548803800301c041c150b42040d0004052a203204010114155008958842078201000c0341806c11250154bd10744981c2d507a000801c101c0344aa218101c03841c261038980d0380000100c103120003510500c94141000301545065042c0c0ea00d02071417090a0000b00102c00501070ba05041e0170582c0c0185c0682a9800c0c80c000306ea4a900c60b03038004140c40c00008203440300001c01e10000d40780806100412000410003003d0100350210706104049c03002c1d02540c0341c8072a01d00b02c01ca0130740c0803000800c01d41d908940c0540c1081c00c204055540802c8151291041200101d03408441c6007960f03001c0c070f50052045d8182454284017202079040108554150b5581e5040059072007264002061420032a544000f00080390342c500308401041e00394814100144030200f4000c074071140701c0c0e94140c00054102a90030290040001f40a0b105000c0006d4104001007129000355640501520760b602050f2028020b40c2e880d03070040c14a0011027040008410102100d8240700e05000b0003e1510500a80000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 539718345 1250 539717095 539717119
    0x633040302040c18050409020a060c0201171003020411090a1a090303120108060a050702060c090411040f17030a021b01030b040e0609010c1106072006010326190806 72
    0x2030100c81141a14201080e1055a48001100b5484c007050152100f180c0030040409985c01181d21042240688010300840019100c103580c05041c02d0b00d011560058038003000d2604d0542d485200c0c0080c40300328000c40c10046002005214401a5070b200e5001900f110402031901001c12829480180c0120030b6003803c0250308841d80b014401007620b12030708414007182d07500d06003440d4606040104030402030342ca06414005025804a12650000c0800c40041c2d111103075400014000d004440790b07a40c0c4648002400902c040c0c0d080c05c0102212004515004142d44c10311480da1030784602540200182c0103100441303035420b240c0141ca05a000107140004980c082100802d0494581121801859101a0802c94090800d01521007407080511340860008030a0100c3d0f036032a50007415a81c18080d41282000ca80000c004100b03900b01c041c1c0c02111881c5d40e490800d20311040340c1d48410b8048060b4510030a11100c008004c4407805a03c1000340c20038051400b200321010f060140155030b02a0203040d80e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 539719595 1250 539718345 539718349
    0x307050c030309071d0601020717010612051e12070204200c010e0d022b11030a0e09180a1b23310b060712170633040302 53
    0x246200f11a2a001420031604010106141800d5070314140c24905c8042e0030040786076404100348049842e801d0f0b45030702c0a41c15022990140ca510b0300440e00d52008004140d060000005441c1c2101c6120041081c96080324074405480e408000b04085000d034040101c500141030551108050304081c4d00c6189158102c020070000640c0805041000c6a4413489980040c0c0011300540600f503c00e07000800b0002c0c21a8500c0010740ca210319000382e046c403d01c1400307100f1402240c0c0b00510b030041c0340680756100d01080024000c482c7d00041c3c1c5001d080d520001070408412040040f100f140c3c10002000c540446588003111001d804d61118588421451300141c130910700c1c109244c0c03000d184012030060503546414490030082040e2a035550340f00c6403007111a0404414080001070b0b071000307030212740103100b5000f01d5064444d000b4020040d004800380303111140d038040068074941201058100c3e842d00d4803800c11050600030000480701400104001340201e407040c401da1042210510b4450030316a40b500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 539720845 1250 539719595 539719597
    0x150f050712050c09010c020f03010f020f12010605040b27100906140403110d08040b12090f0a08180312070506090706020a0f11060c010f0b040b120a080307050c03 71
    0x1004004501c011001062080076401910740c0000c0406669042c00c0203a00002c4c082403003020041d0245880940c0300c0e205480a41007001c8242054074159514000d024030006554001d00d15080b525003502d00100c2e84030302c2001110b04551446889904200c403d844600184825031803622204000a5895800303849116403016150302c03944803140300702d103440c1e0041c1002e0001c5c545645c0c111010481400020368900120b00440750581d41c0700804034003480d0401c620710a40c0c0042c40e03034000201d01103ea0800b82c40c0c034940301e0661042602c1031030360908503003980c03a2481c0c80001c02c0d114083c81580b07140f080c000c82c1070301124001411100c5803901024220160341c030110080e038540d000041000f50f00d017400c001c00c0700101314510041c400f03c0120788900c4003034441ca01000305171240416004d901c3d07070386040941c0d0071888405c1c020840d0b00072003012100141000300c8514000d60419015910f146840c1d4000101080c02c04041c1056a5042c0d481d0711042d80010000800c0c0403091100441e0094104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 539722095 1250 539720845 539720851
    0x5030315030c1f030e07080d030c11060c0a0e06090901050f0a0513090302010e0d02150a020708120118091e02010512010e0f0f070e01032706020918040c03150f05 71
    0x100d282c0c4100708070f000141690340c260482560b56201c000c041220341e40c001f4070b2420080b6240350028081001c02401c0780e01031403180d1030700c1051003544103016010038598010f1804c613000c0d40303610a10715035480c10f00156003c0c0741c140c0c59000e540e0400401c0541171001000811400003089101e6031a15640080c0900c0c1413900e4120a4981d101e04403410150244a00002aa082c2c07008261618107044001e5440000e20700b4003070341c80d11070000700d0740000d0f158040d901225841041ca40d01ca1150250800c001e08017449020b107540c0805070420005032a0744107820100d41c004080108040e042d00655411007034100c070481c10000104080c940144000c2030181c064551300000c0784140c2421802003084120140c607058000314034406100314260400d8203021004402e003008201c00080108440c840710071803403520a40c0c90a1300c45a03040020710783c018428008102c4001034409000c020160388010122801414003140354014400f241d5154021505101d0003c008070b480340c0c02c00fa840c005d0720026 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 539723345 1250 539722095 539722129
    0x2151e0709080c10021011031e2509050a030b0a14010f1202030c0913030f050f07022103040f06120204050117042a091a030d05130915180905030315030c 67
    0x8c800e01a592112202c0c801442c2404800407490741044100d11400305580090058512010000c0b00101030203103080714000e0000030301c000c20269503410f01641072101218000d0a440c40c12041c410000c003507041050603600b0303000d80d030740d40c160520704038590703c0141c00020382c0e01d80f0981154a5042e0b80d4000342e00e224101402082c9000e9125240c050408040d0000c95002c1c41003d1010035911040e0b40c00351543c1640403610b000080c4200900200203009d40760020f0b1045c000054040703184003405050904503032050382d818004c10720308551041240103a009050015840240d030101c20018219610340141c09403280c41c3c800d40354001040710500c8510b000d903207400500c0f41c00f000784407c01e21414800c1501c0c40f08120240f41306000007515030f06001152424050046118040345030050189405404264010410620f00134a413007190321440c85140070105045800591021060203411180c507800001107044d5100c40c6540d10742001a1040c48e505441001c040c52031581da26884801c03000300c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 539724595 1250 539723345 539723347
    0x50102070b070f1e051b030a021506090c0f040f1206060504140a021c06030c140d0305030106140f070b0f0c0c030d02030702151e0709080c10021011 65
    0x115103400004400c004012030184040020000507664010f0b8804e404101c51904010940c601c1e42000d035800d000d10030210100d52a841302c0d10510750f600000070441044542c080342c5001d40b146055540343c0c5403c0fa074507900140c044d0045010782ca42c04c006403403050320b1745c100301d403c180d222074079850034158585c0481c1c1003140e00e08064040c402e151007001c024100698082c014040000e4803619190000f4000d0b1801d56800143d00001a900c0409205604440141032004607070747e0601c0b5030030264a0141010740c01e0808001005407614140c6508481d506442c0d050031a80b800c07100f900c00701c0c45400c1c07030000094108030541811840c10300518445124080d000b010f41011001e0240a801c024401045a9420415100504c030b001050740d1110210820150392941c035950220309207030340400c8801641c40790f9418000e600c804410902c00c0b10420f0f426a00b50382e9120174080360030600740c1c424074020760030035000c1c8001420a0150441c1c1650f15004855161805035185421036001c0d00d031907210094 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 539725845 1250 539724595 539724607
    0xf15120103030e090702031615060803071703071b0503070b2401030b180406020912030a0f0f0f0509041103090705150f1210080106090c1e020715020c0904050102 71
    0x5040b000c0c410781c151090702d20b00082d28251700065900d204440900b062600e058102d041040b00342014136421620341041408602d0b502d02c400340da2904007000c01c951781203200355100c14082c08141901d02c01d00c401d6030ba480c060489042c607051902d119140a44141c041042020003041118802e48c1c06161030b4500111500c03205d2072450307040c0341d8000d01d490415052626085180c0c0d2025218141c2143c0040f410440e611f0300c0c81c00c2802880b8800400d5000b011003000a0b9020790301001401c1c4446103070700d80410a80b4050300c112a4103581d000210041481e560510440b81d2140c8041c11000c40050300029030744000d40094142600203c1c4d20a5043c0d1081d40188950304218a0416410300030b1036415003803250741140c01c200c5004480070304030701480e514001307601c1803a00b0721040000c1120030020010a07880e41a00f0010b07042c4483d031000402c5042c900e2503210031245210070880381481d0301522000d414807540310541c0d2400c240d400300b144a0807020310b0460b6150780340140210300c82e00006039242 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 539727095 1250 539725845 539725847
    0x100302071a1f051e030f011a0307090203040b01030b0402032407020f010510050607030903060608060709080604050a02040b0609040515010201200316050409020a09170307020f0f1512010303 83
    0x442c1110000241c1d810000c10001c0d900ca5510958881c8032100300d800701d510211010a00c0c020049551b401150f0922000d00704c412005944985284010742c20340b07040344c1d11000c1140591005550003026585400c0040001c00c042c8507400c0d412034402400d96220460300c0020201040c4030b43c1c040c03006510043e051014403a010000c0201541d60b5400034002450440c00280002c1c023244a03990103101c001034802c081610509403030740070f107511a81c02c220143d21203a071981d59010458034074000c107804030f201007408031001442a10850f4000c00400307100340dc03907003880041d0000e103214941107402408601c000e941e640c0034443c170800f5005c003440c0194002000081c00d40d403200042c06c42d0f281c07420a454400000010482c0c1c2d11250b0321031010100e50464008a52511032a03128611031071010462048031980100c50030216001741c3e09070084904005031443d16441500002940424007421201c01420945101008103c00926071840a048840720301844c1d8850104188203072042c4005000309 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 539728345 1250 539727095 539727121
    0x20d03090303024f0504150510030605030d0c24180609110901030c0605030403120c030203090c0102030a0c0605060a0e04030c0302303f01080c010e100302071a 70
    0x3603891561440f038040c2007040f2035001044c0364001d0900071a141c044803c542c170034070b1405400409020f040800c80540d58840180200003d0041602c00c0c01400e4005034800e01c01e9440e030310050f030084290f0b56099001c07071107036140d400d0304400146000d842da68450318130342e21044055200d501480d00401c40d62203d240c5050f010062140070b600c6441d11900501c00300d8207007d125020750b6034504020380e4940300d5040c10b58180c101c852100b401c0e141001e2041d68075136072540203980035990450403281c0c0580f0361001a40c1324021018040c000441024041e404a080e40e0485900308002800310702c03603a61100511140004200c03005e6005c5241c200d40c8008043e410030036802d000ca4080c142144021040d01011040041d900d01d601079444042558035400d6001854640000500c000c07122080014030024002000c645510b209580011400060340200c0850304103808203050751a019510038a0301000014104a03c3d641c08050b42403100000150f14600f28802c45041e041c08407a6a113080004030880c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 539729595 1250 539728345 539728447
    0xf0b12271f06300503070c12300c0309030213051915060c02122506090e01050402160c09020d0b1c121704060c030e0607020d0309030302 60
    0x40c000700100703e0035101c3c42d04141408401c011502d044141c1c941d03402d0451450042c00e07030140005c002260001030036030202c02450061031081c0703500e5442c80b038040150044246030f50460008114103118189065101d110000c888501c28204041519180e402240103981c1c1c1c0540300b81901d40d124244046201e00c480680350300b1004000900900380480e0542904502c0c07031040f00c0c18048400100c00443d5142d102140e8018941e104a8036010f07500e040c48802c15819601c0c181c4510310503200803e0306440b5094107019240d1403184034026910300014003000b58802a4a48000ea6034104640006904c00e84040c00800145402503180c00440c2803000440d41410903a900c144c000007404002c075000c41c0c0e6002c036056000001d2410398602c0c840192112280b40d03000720512103411081108215295003c0d828401c01683e0030403105944030032096440e0310a58515015034040201c0c0301c4418400e401070400c0768401c0c9030140c1030520bc29230800100540d800d40c0709002c01300100642c844411505403142d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 539730845 1250 539729595 539729609
    0x1306020f030a15032109080102070302070509061e0f010c0c0b030108012a0c080c031c0c030b0a0b031f0b120a020f040b0f220f0b12271f06 61
    0x410389146540350901c3d0880e0710414800c45c45501040c2c828140106050f41c000d140d0000259540c1140b0701c1d00079255038090166600c501035000100b021820005e40b85000302c2d004081034620bc60365101001140421800d0b2141045038202101c00000c041400803001400c40b040c0094030f075410044001c2c2503448000800d1480f00300440b10710014090301d8843e448070545400d10200d40b010b1400c1640c080d206a480181c0607100025410700c080b081e000000c0d0f60000194000c000b200300d103000880540e810304810380e0b4070805260302440b4a6543c07000035900840c1495040343c61025640c0141e0b036032804d59001010003040800d400f00c8100d49500d203e030788200a051b00b1803030300d181d005041000e40514001c0585d00400868200c0107107100d1000ca13401c410181c4801e104840d800110024608a1030050209810707007085c00164021000e8251208200c05420b50952542c4226503402e8a4a000340c3c100f88184a103400d007020884140060040041c480850117501801582c4200c299040e50344419 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 539732095 1250 539730845 539730881
    0x2724020114070507050709150302010e03030310150908070605030f0702060907060509151602180412080901241d1b030c040f080a1101020313030201081306020f030a 72
    0x70000c04000700d40c41d48072030390341031842e1552500d0501034036101a170b03003041c0a01481c1243e00c0308510605140142200e100740d0b0344444030b40c0000309054890000795940f40e1884481c031000c1c841403004480107401502e052812950305665280030b149000c9041c1e00c41000300300c0000602083d045a084003907404a1036000606032810080c5416507034911510aa50810a01040803c2c1942e1600c11240d00428800300d20340d2201d403040760b402c80c0c20b01c114900328841d41c0412650407038130b021951240d124030341058264071051f8100e02c0c145e40c0350500411603140c0b5544e03100c0580e001c0c68403c625440c3c4101c84000e40c1195400d1101614094103103030074444e480c0100c2420440300d04e51030806031052480400380240c994443c50094000c900030f42d0010004011b40440100310140000350f030046460081d50285481000440103a031a8480c008907464101c4c0740a205001550003900056017040b02d11800d900b1001883d107540742241c00c00b180710824074200000303118042c1094000d03403840000440241c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 539733345 1250 539732095 539732111
    0x611010b09011a0408060c03060a080715080c04050315041b1a130e180c01030203060904060518010e011a03070e0a18020a03061b0e030d27240201 64
    0x6291214144140da00d0001210400440c10a101c802e84c0c0080071400201c0d0380a081041b14054190022680c0038010605100006004400000c01104613102e080340f6a8083d5000304080f16800001040c03107648081c204000105070320304020043d02180c885800c3d200c5800c0601d4070821103814201641a113159141040c005400030382d1002180c54031003555591f071090b0f41802c0e0b03114585a80d10000d1280c01e400104541c0c030b01d14503030540046440805803400e6408600042d1f080340020340d12550021301e240000303400103800f07521507900410340d4284220701e804031681050070346882e14142c2d465651508800541885d07441d041d141d0030380f0110043c0942d40c1c10684031070700040c1c00804000302e071620f510500104030511240c3c40ba0640d0054184004d003900e80c02d180000d400b00381d4103690302e6010469003d4031244146101503007140d005000e400580c020300070444005031400482d1003890a000703242e00d5103440d040b0302800104900310040025000c1d800511060f00f004280d00c5007503905042c2c403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 539734595 1250 539733345 539733349
    0x20d0c080604330203061908031201060215150d05030a0c0b090c3703060212060a030804140609130c0906030504020f0126090303060307090902060f090105070c030602040611010b 78
    0x82d060f01000104401a02c83d5186000a54846490802d44410000303480700450498004401040d007000ca91408a0441c0d03a07408040380d407a14248044c0400030b110801043d401d03078101d03500e0303041244010403008203004c16490f82c03425540b11024a001060051401c2001c000945e0701460340b103401724000d004201e50220103d904440e1503c10072071000b20a0a04200941c0020720210510381c801101403c22603c07480c000c2c0007036102c507100c11842858000010660310344004082d0540b07900c0344006090510b00040003200792804905d540d40542c0a1120819940b03881201c1424610342c550040780c852a0303500050400800c0303400900401d0b0911042001503101c070400301445500c20b2909400105880c03400311441040740c0d840320b50400891050040901000020350302420044069135074450b660341d40e28049454544000350000780a00c040d590300e20b00140a82800c0c5010b040c820314100c401d07a210700014105400c01c44003a0f90126091209035801502c031041d50070214000c000785040700740 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 539735845 1250 539734595 539734673
    0x524010318030c080408150a0b09060d06050c09060d14060a03030504050904080d0e06010f140108010b090103020c07030305030106020c0618040b012a020907030c08070c020d0c080604 80
    0x3016050002e030743c01e1a42000b00f81c204441c01031a50400391820240581103080c0c0b10001501e03021511424422041103900c0e0140007507010301c0c13008041000c69287c80d07a8020151000500c00f8020720f40600054403540c42e0400108450b02e07132800d000a501c000701074482007540000e0643ea020b5082001c0510000381c01c401200e096550441e1010925070b25898a15035034400c42c44035091150800c004000c20110000340c480c10f84250101e41800c083d00c42c0c040156009103265903600084e16803004008004120000b8014500185800351510040c07002035460681250700450029800200404c505d035030500048040107c1102c4075894000303548032044160700c1130030515118550340c0d0019610780e030190001551729000e044000c46148070303100300a0b4030754021146c00d0f0700412804d4002103150703101c3c3c070500200603a55201e500340d58130740c1802140e1501ca80c60040360420392642d10440803420b0242468020f01164000705024a40b07868036400c1c01c8030894417442001030540c1c682c044540901 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 539737095 1250 539735845 539735891
    0x10903060207020607080711030f030c0c2b15060503030901050901030e0a020a1e0506030f180f0313060224190204050402030901091406040f0b070302070605240103 72
    0x420140c1c40c0c203050b0000a181740304652009016050000350b00c2e04006103421107840800c0100c040e2a429903812002640317030b108810b45007015801400094030719250400061030a13000c007007a54140c1d800c07090361458007a00c06400642d440260740c8098106205107000f41805000140d029504080e80798001800c54001d1759075850605444407108155000e040040104440e0024505500e030303951190702074041d0103068a001c0020b40d00320350110300360070075400700c034095810b00d284013400355a0183c04418103000c03424500707010b004990842060a10400240c00e4403100714420784502e42c5000b038080d180003124124001ea4916079600038180c1d04c1d12041d226070043c1c4286e04049038000960084000388641d401082c0d0180c03001c004c1c4401010154415024140300b104020040e021841500b079035410102c0d40103110144104140c40001c1c0302c01c80e001e41042c0d45c0d05002d42015110380e22482510343c00c4460403100e0440c4007600300c85503543e0401c18002e10742800e08006442010700b01ea44000088 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 539738345 1250 539737095 539737103
    0x302060402010804032c1c0b04060e072c060f090c09151303050706110304090903051b012717030c0c07270b0906090405160311040614010903 62
    0x2010028045c94040c0c0d440c2841502d0031042003c50704010380d5200f0b54a11651301190107541c0c0340240002140074074281c103072901e8020b01071074602d60302c80e07580304041c00d00028a07060500075408002148810480400f00d440d20b021040c3e40420b91030504000c4c544002020f80c1d00c1040304031002c04c0941c44640490313412401d0709515558034120307200898001b0002c44410490480c0005200c4459040c1040c24415203200b4001d450510307507118002c5415907800441403145420401040182c43c5050740400c0609109060550818181060b800030303e02103200c1c40c0b4116511049000b00c0c001009410550010076507105860072441910b404c42d01d002012010300f0005000804102010401740c240d400194000c0d089806050301c54083e0703411188007204107101181100a194442881da0041055944000c2c020307032955546c0b1009c200145002602c159118003230140f800034400200f100c001c0c06103009010440c81c84403100705010803540303240e100d0314000c1071100310810240c0c0c1c4402d500d402c403500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 539739595 1250 539738345 539738357
    0xb040b060a081b1326031c06050d120201060b030c09040510090606110f1902060319020f0a18030c030807051212010801140c04121103010228020a030206040201 70
    0xf881c1d4520300490140350003a001d4000210360075010380741c4405044191000ca8480f180c4e0040d101519101450407034250707503070039041442a10720100740040c100030800e0904c0404248181d42e880400c01811800d68103960b012040c11400d46c0080d02409510010940a01e1443c5145032440c0100707d58007406070365610980d140d60224620101204040d0050007009000700005075907960003901e0300c00582403008043c080c0466000103110042608030165142041e881c50500705982000815840180b29902e0341500d4070802c00b0032401c0e440584102c01c1135200a41d580e890b5614043c0c558103641d07142c58540d024400017800003904400b40703030045031307801544130703403690b1061a00072b00b00030300101090781c144000b01c0e218000b0750074140c100b4100d556500007004159901200710b03010100032a054920b4440c10042002140c034404c03c012052401103070039203000448840001d00307a90010011030202d80c181d1640e02105490003070350003a402070500060441d455140c2d0042c3d2514001031010381030001c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 539740845 1250 539739595 539739601
    0x31e050109020303031e01060906021c0c050d020705040f020f0405270f15030a05120901020a0c23090108061b07060513060e1b0d21030b040b040b060a08 67
    0x18250092907440b80d0040a41382c80b0f00c3e1500401d8500300b94082e01c4041240d86900000d8030900841401040da070056002d440020003100413810ba85040c054003508021413585c0c1c28002c9a001d01c2140f0300b880040c1d01508040746031030f00304001e54810f07580c9889194810803001c604039030301000715412510160751440045030140e0003100d003104028045031200804a0070008903e403101c1d1018850700d14004800701c44152032060580d03600c42420000c205a000000c80d18855990001511080354144100d038032004140d61a40c5103003c10b80c0c011000c2c018468114104591a09405540c42030241d490004a40c5406181e03503442001800c00c10200d5411110b40f1504022102141c1d5a00c0e0050000e0069003020310820b51010407007541a20b08515044000d40d00d00301c04a40c0404c001c0740c0e07800d2000c0c00c1c8001d9040140c000446102210103031500001d070f04100c400001c6002c3d0308025034800149500c444818481554050710107288100c1c901a50740c1030903a034180c1660b0f85080ca62400d0f14041d6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 539742095 1250 539740845 539740853
    0x12060102030f070501020d051305030307110309030f0609060c13030308040c0b0a0e010206070203040501200f120301030309060c0201050f130503010f09050c0f06041707090603060e060709031e 84
    0xb1103145018815540001203070800c1c0001500102410b0300c16040070452551040c010031402596901c0042c42ca400c204040b8015034810b00150050503d07103070540e46072200c0c034000280f03003da1400000c20240c004204108054500344486544503102818007450224212040f00300c0700a2804024240800800490213200f60304d44d03890040e1040c15416030b41c0316801c0d00081c0117081b4448e9070500500c0f0f1200051141c41c40842600c0440e00113031070310300410705e0708000b040f0481c00040203400b240c49481e000340e040c3c0104115031129100580c0314140d484d41513007030051481411f5001a02070000720703140c00340140da104040700d51040d80503e02c1901d40c003040740800c480a0b000e80c0881c1c0d0540c00d02c0002e00f580a0781e940311098040c8100d048548083c580c8052003d52404400340c1c0f940118148020400603030244401d5042e070b01010195403145849114400848883da042510a01c0c0c1d1802c0b0000c0d03000c0b0420070070f50072842d02d080c0319032841c0c61540c0750741c0ca031007d10038850440706400b03200d00108 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 539743345 1250 539742095 539742097
    0x3200703140c06070305030103231911090112052431121b0c050607021c12110609102007111c0b0a050402010e0d030306060809030f1206010203 63
    0x540c0c0000c021507a81c00d1a42170040164000380000d41e10702d040003e80140c201031300070b1044a403030b40c804040e004c2c1030b0f1214101400082803040940d056017007001c0c40e000325034405000601805c1310406490b95402281040c61502404d000b58034519040030030f4003910078a0703818000394880b6445040005880003814030940d00d05550240c1c07612000c40108040800240c510303001b05505140d980c208642c0011020040c3e00c204920015000c83c0502e2802c3c4810304041008100103400034010360340c44004480b0090409a2a49080da02e000244401046043c1c3c00f940003200d941c80d6000408050400c0000340340c844008090413600f5650310352415000080003d0088500c1c08000d540d41e4032644181400004a1481c1ea40b141c400e500c800406906201510300e50038000740c102c0e203641c410b5507071041c800c0001c0501820903410b0006440800c0c0700b40e5140c0380d040d0181e51090707402051182c50000060042c4501030040181a00244031000318500c0c4041924100c0b0b00f00600480b0ba5164a00140e0071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 539744595 1250 539743345 539743363
    0x60d03050d230a050f070e1c0f02090406050604050a05090c31020d0e0111160c090504050d090e090309061c020f070b07020102030c070615090c0c0320070314 69
    0x401d580400c00407000c500b540828131400c1744030712001503030751112030403a50000d0140c41198007054240c400300d5000013441681003600e205148410065045400080d0202000c07113040b00c80719140d82c10050f9a040500403240c01c550300c00c2c01400a42085a40540c0b40d507200000c2d1400307003410b045120621480d0204144940000c1c010b0400440840090b91019500c200c0c9040c2c2c0190602d0300401d61080c052207440d407140d440302980303420050048000b01240700035034825500042e13020004210501540f1415018620031030007817220700f280e1a0003174031400e159401803038100340c4070041200a980c04130458000b020100c0300c0e243d54000d5007140d644070700701090b01d00d00ca00c0e201040304101810f488005040c50f80c001d0140b84059a60040d00700e09030b01c4220784d42c0345824028024840012800d4100c481030f00c00d15540104040e8807695403000b00c50318485000c0c00103131802501020b054200f88508450940040068070003c841703912250340d2407040c880148150035202003206d107401c0c140040e610f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 539745845 1250 539744595 539744651
    0x309060f0501080d081b04060c081c14090a03140a020304170304230a050609041404061514090408160f050102191803082a15060d03050d 60
    0x101c656111403001d42e40e0380f001c0e54064041414000898400181c0000c003a240e00c02c692495843e05050110488400c0040401118101c4043c001d65903032620700c01880982e136156480014cc074000202480980740c201404080b00354001c10203402c0845c2d4041103e00d903a00e0020703081541c6d130b615182d08034603500c03841d441458440046c0080d007003c2c080220040088aa00c2d090180b600380c02c50724450a00f00302d07200c90300d9205080d12410051350904002070203021100070000602101249114803030300c50121307400c540f995682e640550319030302c1d4901c3c1e100103020903a440412414001e004608440400f900c0503210a03000b00f0311403c00008807207000c800035880084448441c58034a0014080e401003410324551004486515030004d20031200002c001c4014000b004403c3c1c907540740ea001941c0802c11201460369072002c0e18100e060300400030b02d0003e500c8030090074003101d60956004c010030060401c5200c0c0007464011000300b0340c410207440c250240400c0003d45e840c000000f0311000c082000050b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 539747095 1250 539745845 539745851
    0x12090602121e060613052e080f06010c03210c1d060301090f021e0c070504111e1b0f15060a170309130f0e0f211308060a11040509070309060f 62
    0x62000c020940782140310001c005100042d81f068034083e21450f80071180300c15079000040008065620462210b034505000b4106140880c102040b80a502420503540004491300c410355035040d990f1000011441e8001494038440383c510368030000750688810301c00e00c494a9241c04404401403100e6040f44c00503013988030b284c8034084000308500c82d00e4000341034480c01c81c0540710340050a418907010707a900c8103a15400035403901040c940400c201c0c051181e582000c1c08003d104208901c0c40417110f40c40c0c3e8200c0c08004000d05c40b10001007501e00000b071515180c0c420b9101050100301e807034148000c4151041c4603070381140481800c07111880c600640c410725500038103c040800007241954002134160300171582c00e11400f900342c01665600c030038030f64500760030b42c0c4402040c04440c1c042004c45a01d02d5800a81103203403104102411111200c00e80144225401150510603503644d10711036500d542070140b428034103241c0351200144054070010407100505407101c1d900c00804c5040d620440030000c1441c010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 539748201 1106 539747095 539747119
    0x60506150a0305071707020f01051806070c0f020927010603080913060e09070f090b010e12030702120d0f020102030606030403030b0112090602121e06061305 69
    0x1c0c1042091000c1c000644285c0c10b000309001d03010315801000f4141050903441d08450700501800140d908850201e14800e6000c00ca982e4800e01c41d0a117150780b0b1945081c4000301e142c58960082d400049481002030700c085190540a426902c01c141d207030215640c3c0c002038204c41e00781c00050312101c1c080c0301184c0517103030000d410b85000586410100c0d81c0366442400b2000d1890948440140d608180400c0c00440c40705103102005084040040c0044030300c880020709050900400d8038062880046014212071003041119001035010317048144400c00014507548403070b01040d1000001300e074401511040b520500235039002d4000100b0140c07542d2150340d410390040110640c0e950610140c20742c196544281c1e8403ca40d826802440c0140c0d0720f0001801d001c404160040103403216800040031041407118a2800550119043c9c460350340d5441c8003188280c010b42280d11541e8000908003607 = true := by decide +kernel

theorem cover : BRFrame.Cov 539568345 539748201 := by
  have h0 := BRFrame.cov_init 539568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 539568345 ≤ n) (h2 : n < 539748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
