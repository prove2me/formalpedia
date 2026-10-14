-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0589
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:36:26.388868+00:00
-- url     : https://prove2.me/submissions/0e779d37-3e0f-435c-b948-06b3926a44fe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 105755395 ≤ n < 105935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 105756645 1250 105755395 105755399
    0x204031b0612151a07120f08010f0602030a0806040902150301050f01080405062a0f04031203020910030f0207021e01020d0f050a031505060a18090204030c0b0306121006 74
    0x1402c09401181180e070040c0034080303906070380c48548900c2200d0080510801c50381468400c0c0750300348010b840340b15a01101d40c45240407408400341c030074601f0522000010760b03020008143d01e00008203580866507150002e42c10180381190582d50004010a030030f8100742d85000e8240569101d010110710443c0d42e6007280d0340c80d41084140325040d140340c403015051003100014040026000501d03a980b00307503100c2c00100214003000c8061011003007400030a807624004510b4040341c030003a0004004032482002c1c11101d0024011007130b8140e0180c10701d099030050080561104240c040c5e0010340c9281c03101c0b400146440043e9000801c080303d2901d041407800d5a1025000107075804100b00c502c3c0030310504100c0e58182240310010004c0c4502031400301059183c07040703104002034558083c0042c1c0401424161112820000107109030fa102901002c00c1e074889000048100c09842100c0940743c010301c4441c5483e04091501c0c0d1a6440944403603084001358640c4a0a0f034401d11110310186a95900811100c4c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 105757895 1250 105756645 105756647
    0x40228020c04060f090e0c1216050901060806010c02040f06060806040e031918030b09060601030c050313060b06040302030601120606060306060f0305040501060509090a0510050105220204031b06 85
    0x140852110300d0080740343c42c00500184060300d000301c00711600040c0c089588500d01c03100d2420070000302c0a03d40c01421500c0559001c1001149a90408910022000c001603681007042000d4200388102d1005c1280d4001103041540308100b900e000a001030000301f000b030f6030322014200700c490340c0e0701400009805100740140c1d03190030b014204061881000942c00c10b109203e4060010190a2024003400401e40443d026030b480e02403000c00858001c280380e43e40745000c1540e1615000200c40ca1400a45041c2c42444903e015a00f540d004100058400990204c2035540340000c100e014001c5501100034800000180e408004a90103400740c03901c0100c9030f4290307180c20010340e00c003600714905241c205001400450751111001300c0e29031051501144a846508056004007031a8004903003003c1e2403420041010000140100014410411111000050400103046420a00502e03520080b81011002c00c0f04140030200410707004c1d540e0061909940b03548102c41041d1003006100c41e6260703001c003003042c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 105759145 1250 105757895 105757903
    0x31902010506030a0206090105220909030f171b120702030406020708070e0604091401090b060f18010905041b0303091802092103040504090c090506010207030c1404022802 75
    0x1034103034001d01c8084c5107039000a025004003800d290400401041107490086403046810110302b909603610382030740d2949089006080e0f40d00c1d0940214100401c0100003c1c881c4a80900803060304c50070b58502c0d19401d945883c02442d0f1850740d404800e050040d0503010781051041d500036007154006541d078925251001e42042041e500c80003407a00304406c10041c0841c0182d0140e4020002c60740001c00c03c0c520300c0e00013440a18003041351082d620301842c0f40200003404d00d205006100c100e40c642045000b0904101d045042d0908100c00901144010003c0988070381000390041e1044950f1244114141c0a03004007602540c0154006016110304100b03400d4120003420070401200d8055190142c01c801042007020708989042000701c20801d8181c07405030138000da0f0007030030f1700500c1030000b0041410800c11301011402840c041d94600b101203102e66000142010440b5804a00340d44000c7c90701515a103402403c496040c0c000b0380820079010080100208607803288102c3e090038981e1079010500900d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 105760395 1250 105759145 105759151
    0x1101082e06090f080606010807120203040614090712080c030c1606090e010b160201050c010f0501080c010c05060c0a020705060a02010c02010f020f07080915070c080c04050c07020415080319020105 86
    0x21a03c003030f0070b081c0002c5402140e490341c084c0080c240090281c0b54140200c07140d1845401e03900c441440031082c001084010307080542c040c0714016500e079881d1590b8860607201c00c01840740e404409190070365100091010005090404071000a80382003112403510b950500d40d480c12072411103013441d0b5040c441c0380d81011401c0040d0050f150300a035698144150b540f01442446100704000b03007801400e208580c4502c00311084002c9010083c82080a6009404040e24082c001d460090249541c4182e030b0b544110a10b0884503002401005941c94412154126600146244c0214000d030710001c07500e900d41070010550b440c13241d400003030b00001240000b400c40e2070030403103860b00700d004000512640d51154160780c0801c1e0040141c50340e50002d04009484081e4641e0441703480000413440d8018800400c95400403520904203482605002c0f030304000c00c40303804899203100000d09001540150825a0110b0a1200c5013413074807952075220340005165801c94540301d51000e11041d805080d50b982030140c190 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 105761645 1250 105760395 105760409
    0x403050a020f0d0c020f0415060f020c040504020102060103020d060f02030c091804050717010e011d1009210c14060915010f0905060607080406050a17041101082e0609 73
    0x55002e1103071000804d5500c662001030700c00e4911105103031003a51143e01c1140c3c4410180144c620150707881c01c0281030302c58000d100310090300504608a1050500b4006c0c1031003158141c0c05000503a00b9a401c2140e801e1400f074041c0e0717500e0f03503525016481107810b100031030040041d002c07090b4803803030030b10100469102c860a0b60030441942c80280400148009100d600380c0307050308102034204199044850041c40c504c0c14142803582003040f21980b964680400101c00a045025a082a22944080e00650703111400c010150024081c0d00300700200501207145620020b4602091001c4080d290700341420010a202205a0449024000c81c00b00c1040245200300f04944440c401e0761610041c0d050070182d83c0701c1d01d4031203510b9400280403036846d8422985a0350384000d900382c13205e03102c80c0018402c1d04100c40900216003a05110115040f040c001c143c4210345c0820a18001c014140044440b550003804c2c08020a80f4885070404181c0c4004002c121240c500d5100a4400d107400f00041c00481107a000c50 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 105762895 1250 105761645 105761653
    0x7171606120b18040204020306010203121015110d050d060503030315040501060e01120b01020a080705030d14060d02040b010513080606030601060531030b0a0e061803120c0d050403050a020f 83
    0x82003110031503041513003c0e8048900507283e50380c07040144c0c15407003140139844600511604012006042170603103019075021251000c1110841042603c4007044807560440c0da5210569461406100748000c00f441d54454030301084240c0d0392004a451904161404658400d0794415071200742000c0c400c4d00d0040109240113058212120300191054016034200f00032280c99150301c072042e0340208424140d02f41d0100c01c6170759230f20030350911a880740c100940d240645424a1444512003040c801c800e8041d40c1c0061200c000e2811030b60800004006050080f41403000c01d22401d07003d00c00354030070300f4000e000080c042e004074034100d03080504010058210600303216090216030010540c1c508040c0c1c01c211034942d04c7c04d103501d06484003001049039074401042d5007502004c0040554842d0021102804203800321151038540103110301030803119040303070307551030b4402c1c851601021000340722140c005c0c040c2c0e42803914018500da901d00981780105d1f026400705a00040e0070341c0003641040f001105158a04c090 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 105764145 1250 105762895 105762919
    0x1030c09180e03071208070207081203070302071a0a09060b0301050403080c1c050703021b070b0a0f03091203050402210d050a03020c0616020c040e07171606120b 71
    0x505080000085511592942d86011110b654400c004a41480e0b4002000442c444000480180214011100d280050080b0100000c22031400550052042c500240181c19a80c0b00b020440003500262016103c200b0040281800c12203034400d02400345c44101008500f4000c582001000c0e20030403518903002e603240600308030100e5070000e074094005106040c4266948843c03c840f10362442d50707403003520307801d4a09000e001000350582e00030034140203400c02d00c1020560030000c1507181c1c5128800d41c00354801c20400900024403465488000c4411810300040101d4551502039101e00410190030103c2d5072803090209500d00b0b641625a80c1000100210304110304100b415240c00d85000c030441440070205010300854041e03010307548010800000c07540c8a00e0281081d05080f408001d1101c0903002d00c4d1030101e441d042901808401d03c48417001044140d28048414148104038400381f0404d00469074283c0c1c1d02d0a0148003500105101d944501803141103050400489500110a61241d0303ea0310700 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 105765395 1250 105764145 105764159
    0x3010515030609010605071a010e061203180f0301060b16030816020d030b06070f05060412050f0702100c1203150605070b060d0204150303031b03020a0801030b041505010603090201030c09 82
    0x203c181569400e160251702c07142e103443c100251160f50300341c0042c80d98040c0000f1414000c41503e9a119a90031940c2810382d0f02d554000940340d10070490401c03000395580280e030109080407980c031103410a0140c00050360580e605100c010382e801c007900c1516000900b001a00c28035a01c40e19031a045800c0c040140ac40c800740040c041e40c0d4804e240b4550040c5600e481403503515940d80b00075030340b000342c122400390155507040c5030850722030104075400c5904840504045010701e2048d400c0e0f4030610120024149418415000c0022560800010740100b01403405000300048403c230920200b10b200d82c6000c540c440c1401d1540c43c1060f4503030404400c00200744000d04c041001c011019030000301c15915542548540d001040152101203501d00810380c01c503c00204256069218003034070311150448080441d4140340890982c030854050b14000307032005006101141300664110303006486684c404003411021000f81d404d54000f6402440425610101da5040d560035010f181040c1f02c40d483d14030865420124 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 105766645 1250 105765395 105765409
    0xc011b090605070f060605100c02090f1902090406081509010e0c060403081806040605040e0c030402090403050d020d0c080613050708010b0c0c3303010303050a0c020609090903030105150306 83
    0x103c00f609006285521006125007507129801130200a0803059a400744d032070020b031443c03079031800407070040301240c0c0040e64403040000518050340e10003154256170000004c0a001a4100710315880c2d01a40c0c2e910000341440c42040700c030070742400d0824142401d00d1b000e810340382103e1044a1000e030300d800c4200c4201c0c4a0740d51008031400d030390b844a0410303140c04242030101c905c00d02220103542c0000c00020302042064003c80a0412644841201d013904c2c1d4926031648003d000c1910000d4000388030001050010740180080c100b0100070100042c14045136a40b00c10684400c02c056101090032041800b0075030a010b6120031180005550502040c107003050b0003070458005105101c0794140101e803081410405118000031828000c1540c401076031310320ad203984115007036600f5115140074072030700215000105c0c040d24120f1750992582410000031070030a80300030400d080e003240d100e2010042c4803800e50f00e92440d903000e40f0b4240300030764030707507060109000f400c036805540100000e1007802007104680d2044 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 105767895 1250 105766645 105766657
    0x6091b040504061409030301090b010c17030403021002041d0906040f03080712020f0315030f0a03030b041410210c140102010e030c010905010b0d020609040b13020c011b090605 77
    0x140d00050203a9032030901500800f1258183e04c0c07024916001c1c0b02d43e40c0800809103050b40e4011004204003a020b60054542403c44600280030111410304042220340c841c02071580709009006071400e1000c00c603080c2c0b04980c05500400030110703001d0bd000c00c1100e1021000c3c2d903c001481c005009901303050310703080c40c01c18410800408001c0c04100040410b0b01ca845400105e031900c10003551a0302c44c800e100d04030b5800460303014041528150a916107840c000500401004516000d00160b04c01ca4400720302402c800380003d81c0007500c0320141c543c2072a80307800c82e6224960303008481c0720a9062802d460340b148034000700d0321160900300c800000070490260000301141c50b0551065040c54111005074003406603603a2000c00f9000c0402c0c207280208041d0001c8884078841c1001708545007401d4100940e0064098000e5001001441040328a003001d80c0100700340d00e4000c000c004d03000c24024080e070581c0c2c400003904103182d4440e01d41c0c03500003030003005004041d26203003444080745061503c002c20601440c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 105769145 1250 105767895 105767899
    0x1303080402040c0e12030d0b0a0e01181b0c0303050c1306051c05040b040b090a110d02030a0b0a02071502040302100c0f0b0106050301052422050603150306091b 70
    0x286203820600d50058181c92040003000c1c203501c620f85c1010780b1007a00c0360003609422903814103041c512181c030700d401d952400c00d444a21110302d5080e406c100c14941a001481a025450755881340500840e40c1142c41402030005c80c0d07504d61010303021a180017400d0360409810801c84a4080c0001c0049140f20000ca90070703120145000d07625040040c03800341a545405200c10f0072107203444244428422080e481921031760207205185055102e40e1003260742c8140861000c0c0090349a000361424501d007000c00d00d548140010100d500100c4d4a40b100c4099a1094400c010103960002c2c0020800100000c00000c03070341000700440c02c00c2d00d19000b18152441304030403c0100071140145400b0000401d900d440d0541e00000368400540e161031025006078028056240326005e451120042640003441d403513040c50803d200305050800e2181d03041198a001069548105a40e00c00410103860380c1000e1885803451007040707c0307808030603000d041c1020b10242231008260000200d0440b00b0135061036001c580042 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 105770395 1250 105769145 105769151
    0xb1003030e04110f070204110309300414032401090f0e060a02070f1502040303030e0307020315060310050f0106030617060105010e040b03031206010207081912051905070b130308040204 81
    0x203520009000782300e034444402811201005004004200151600d0700003241468128040f0542c08060a1000c01080142d01c2010401c81880b8808420000f0380c0c1c003560207411104e81400000f0310305441000c103c561034440030714400400180141c0c0c0602149000b288200b0000240d050030090740ba43d07002040040701580002d204010003907140340f000c0c015500301400c0301e100c0000c01084070196106102c241c0019061204200030500c002c002c65007150b500800608006a0407061091034500081c60a81d25001d800821b070681800f502695100d818980e003500000d43c106100070f81250380b0758100e01009600504240d00203a00003503800c0c1541e50074200341d0420100080003c010302407510031580c060101141107200b0401042d61140103080c241c00b5542d82030348441103070b07603036240c0e4a900184d0307550a080240040f6500d0036440c1d003100031900c0d090b0b03d8512801100c4011401407031300c8600040b00000e0100c1401218051960445540804c81c51019030989004101600240002e842666 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 105771645 1250 105770395 105770407
    0x306150315061c0302030913060b190e03010204031b08030316080c0409020412060b150706020708070c031a01061722060f1e05270a0b1003030e04110f 66
    0x1803012802d00700e00d40d07030240c0783e001c08101d441c00039203c4d00036600320303400b44002c03203442c42d03141c50240a044251002021650f060041d400d000c000d100560100490a00c506034034080c98684003800100301a501525462440d50048020703904111303040d0740800d010345c1040c000c1c0680b80c00d4240c2c5611800500d0300c0c01644644684c1440005803095600042c0064030000e400500d50000e21050003583d030182604100e000c0c42c49042c0300345407400e0003110480307960810154000942e03c0e4094401640140a503d0400001d540c0c0c5003501e41d00c40c0c105a58940b441188086c69071184403200340581150b14181f25102c440415200301d83c00098001c3d10864060b110b48500d010b04102010304068010303c1c1440b40300300000010000b08040200000380c1354146500c0c28440030f060180a000e11807480c0340800740d8443c5510b07038034200903039080c000c40d5010740101c25020072001c0035482d00510b050074904520514518018214181c950f010600a03400c0c010302c448000c2203003050b15603407090010340b0756443d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 105772895 1250 105771645 105771649
    0x150b130f0903080114210c03010c12050709030b01090c05160b0f180c0f04140c040501091208040e09030705010905010c0f0c030816021e072c0a0f0209040f0506030615031506 76
    0x147c00c1e6041c5540661030544c6d0003501c0da41c043d60591802c0e02c045000c0103d912840360072a040300382c90001600a1694038010441201d840c2e1000545020902c1d00c2ea04000d43d08070790104014450300e064807099009001d01c00d1390156004041c1d00402d031041d4503041c0f00718501944d41c650740c07084507035440b80e40b0300c013140b0703185d40c4450b0030804109042c0521019030703280c28865490325030424000c0c980080c40c001d0020440d038001103010b010040c0c100d50503a040516040c980300c1c81c400010301c000d203e40010710103100020b00034080e00034041d01c12000828802c00c0308d0001003201c4013240c08001040b81411100e40403030303007060000d5000450411750009110000c401030389081c6903e000c403a441150340440b80700003100425003a05075078078000251b00d400e4a0b80301c0074000308483c902584105002c0004200c1a078410340c050403126034400030150811080342c0c00141140c180c83d01f00e841964880c020016a85020320060307510071000d00b075940c07110001030301190b13580ea05058051200ca40c0c880100c0e82c59 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 105774145 1250 105772895 105772903
    0x609030c05040518012408030c1009061103161403070c031404050d050604060f0516050c0c0d110a0803030c070303050a0605060c1e0604150b130f090308011421 70
    0x204003000024030507812031b0b0401c030030311100144203004050111000811036000200c00c0ba043d12002c200182403040c2e444c801d040007031000200c1240c03504d950310f000c4611408080f02440c459181610b0500f100c2c03810700300160204030a081d604098400400130410466088410551003940600c0c080c0d0b80d2600004000000c0d10440d00540c0d4040e60000581c0108440003541511440c0300e14018131402602104600c181d8105848141414000140d40c525861189001d0a88140a0011148000310150214903011214002030702d4410b404086507406060198210b0024509407000f1480c6151030242000d00d8040c54000504040c1c684c03020a2a484c903e1300b01c600039080080455680340840c0c2e402c0c03940e502c0c0e504415103008102c034030400d0300c0440c003041c094070aa0308120300c0b0620b16a1101440d000b130441c0c1c0d000c15400800c40040c1c4040620520520b1000024520002205100c03030801401800050f0720003d40340c00c0c1522010491746604141601c4003607021244109010400c83d15420 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 105775395 1250 105774145 105774181
    0x10605131701021e0307020a08030a060f1502160308040b09060903120309160f0501051b0f07060905031207060c020703170901031109100f02120c0f070609030c050405 73
    0x310088000c1c004201c4074043d802000d01c2519084030000200d10340c511a40180000c03140440540c21290440d00441c071840002d43d8809030716040000e600351964214180c180c034a42080c101500040c072000120394040001d07071034440190b07035407145940c0f0310b940700c0d0303110b200780c0c0600da250f0301c404a4140102c1e00ca200c161015114000c00340c40100302000014401d0f60812030b0751000300d2060bd01481540b051100c10300c1c00765101e8020041009080000565950b4800d903419000701540741109401083c09000843c004d102c8030010300751451411100130000691070300180d2094204200c400401080c0c042111202035010b100400c4201350b03c1c405074184080b980c0050501c4009620404201241704010000034109880400200b0780701d41c801d0f01140203510080703030040702001034810602e02400ca40a48103400340b0403111000c518845401e529002300c820b0745041e51141c076901c42180802d00c1b02c50301411080c42c002140920f0341d10340c250350b90030758490103002d81c0c1e0b650046101050200c031003840c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 105776645 1250 105775395 105775409
    0xa050102040308130509070504060c020d050d0e12030a021c020c090a0f0c0f0c0b0405070506070c03060501050402090d08030a09060e06040b01061d19090e060907050103020f0301060513 81
    0x1d00d565690602c00003652044014001030b998800e00801d080c41c007104c5160084040d90340c2c641c01c040c10700c1000d55601c622008166806070302c612215000800070414510300c0061a42c070301c01260015001d004054a0030031007009150001e11500b048541c1c00142c00744403203105003018010a10007901a4140a0b0710703030351550009040000c00a55071041c1e00500743c5d0b8407008004005104d0008400c855194140c0041c00000302101e1400e4040b441800900d0b03041800354040e42c0d40e143d074904c001105e903400050101c4074101782c40020007c3c082030b4810700340100800c1c5d40940c80d050045002902c40200948006c24086001c408103200800d070f607121000742d80c0d0201007006041c0c819000281d550404990494000100790000f0481a101c4c180c070b44907810825030400e849410041c200140044888100d0070000451640001c19030514000c0211900030b1401030304060800c0d04110382030043c10303001541850700404c0221001650301d011a0304440d040e1030416103a0310005803170500012580e2001c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 105777895 1250 105776645 105776647
    0x30602040f0f050a050907080405070902030a0b01110a050303010b0a050c01050a0204050906180a0b12030316140901020a080c0109150b01020106090902031002090111071d01080a0c0b0c0a050102 85
    0x114080702911a004142d0700c2d1041030030400c65a0354100002c40103140589500503da0341c0c003080e03d0714010094240c01c2403180b015210200c0e220481030b801c13a042280d09501d0540c442409134100d5030011451140340d0b810740c01820700401e10741c07912a500e20061080450f510310000721079540078819820781da20204030400901c01d84c104140701c41d0107900203001da01c0c0701e543d034200895040e01d000f01000c221000000c0000d0040c0e030700d406002e0b00802007289071540200c0c011341c214540c2079040c03000f54804c0c10048030411b40c005020f40000d14021f085640400300c06805c11049880f683c001401c00490780d84040416603070000b018a06d40542110300000706260414070220020180c640c00c0024200c07420303802080407641e510a800d042d501d8140000e50103400071100305280040795002072600440605014401040030f00e203080c90000658010344152240d443c440482d2890000c01c540100034102c0141407800d0b064580359010301e1213124503010094001041c0080f001e061086102d03080d0448021 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 105779145 1250 105777895 105777899
    0xf020f030f0f0c040c050310030204230109060906150c0f0303090b04060905010b040227010c0206030c030106090909050d111c02060f13030203030a0903050d02073f1803060204 77
    0x2c0c0396280c0c20208060310035410300950b8218039102d4800e99100c1d500103c915620b803841c0d602827200400c405000405c3c04d60044000040c440c3d103031041c9034000c01000d000000c0040c0b5000c03075141216616004040008012030300444d0b060b07400610305910f9500100d500150301d50307510301a070081081d50001001c2d54102c1c004c1105201160344140740c1d4900400080c0000c04080041004038403c6160719504990300248145245134a20a800403054040c100ba40d014052600001e07a95041150040d0402c10000014829540d0200300e00d002030407800c2050140380d2081d59a2600d8000401007641001700b01c40006a100300104100302459464011482942514000081d1511000ca9000c0c2440b211b00c00400c0c207c401c0a01c0050b80b1540603800782d8215100c042c50b100103403104e0581036080010070301ca00c003180c1001b4401803d441e40300e00d28961820902003402ea8401c40c021016a04c500a40c856440e07510010222209581003c0d00d0904290403040905054960041d00b001c3e058030320210340 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 105780395 1250 105779145 105779173
    0x6050d050a02010806010905180c1213140a020a090203280e0609060c03040b090715051c09020f040b13060909020901170c1c0b090c0f04090f020f030f 66
    0x482100d00030707a220f5441e85e941c1001075806890500c00c081c0c0101c0880b4140c00c000c070b0541105038200c11251000c03440d0080484e4501c111000540d995860a2119003155040000280b100400c1c0312004015042c14803241e000200030303021502c40c10706510340000003d41d00d6424451420f0380c00007000309502110004260500041020070a404c08500c1002c000c110702103030001e0624030480309041c02a28680d100c0d5644c54074450080c1c0a0380b00d511032841c001c504443c90b48034185c20181d140c0c0c1d03030548803e4095640403403200c0814400d80c07400d15009140c8003507220340c008400307241c04c03d45021030460045801300740344003003020201c100280b4018001c941c0c18a20b4201950481c002c0f10903200d5640c070360300c011000340c00b00d4071a021241c0c4000d280310f015050050b42c21b203407090840c84103403160040340c442240000c030449610744507411080181800e40744c5100c0d88900404260750400c0506010356a0641d030805000000c0d2007421503920b06985a5410406070f001209010269083c10100e640c1d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 105781645 1250 105780395 105780403
    0x1020303240a0b130518060d020a0b160308070309030f1404230301051f030b060d0b04051c0f05030121020a0602060609160819060906061110020c030a0e0406050d05 72
    0xd21310010703040c40140002d50b0702d00381c6451720866880b40c08400403503d450b810400d00040452003260846c00514000600612032000b4000c840348146940e84000402d1600800451005000310140351820180002190340181c60400440b103e0a041480c540640c04100d940c0c043c5074004400400040011814030f6050343c0d070800050016002031025840340c42580b8000043c010414841641c0ca2004101086200381c60070b401c42030260102c1d000542e20b0300c2d500c58201080b00c2c01e130f03002d40c002d5041690301428540c0d18199105903180440110b600c00e4002092480b042c0300e801454205034143d0821051b20300e804840007503006040003560341d81c896029481d84c8048424034420300300301e0005118680f000740c010b58141c050f6559115140d031780340d1058a502c0c490204145c40f566480d40040785d900b07070f5880b030000039003034a48480c2e840500a01c04103142207061800e00101070300600c81e0508011000040c1c40b0191900e0400d10414200f10010400420f4142d10265103c0e145109500a10002003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 105782895 1250 105781645 105781657
    0x121906020403110907080c03040204110a020102220b04090b030c060a11010f0203100302012f0f060610020601050603070318030503060418020901170f01090b090607080601020303240a0b 81
    0x1c207002079081d0f19001c001001e0021610780380410110f10008a80c0c140000095600c14801480041c0180c012040000260050b421980250f903000882c40701000c1030101c41554000d0002d9030801c858140001008180180e101d00d0a410351111a489101d9505015015040c1809880182c440603506c01c014150900e00150303d0b015441c0160001200c440c500840340318215007144880200d10316401100c0b0300d01e1510034070340030345413080204880021203d00c60038880030f0750f4005c2440101d03ca90040c00d0001c00b80c621441031006400c080c00c9a40c020a415044032011990a81c403555405826006096587c01c034204200d201d211040c00c00da0440c1c040c600511080d20204550b501003014400c501b1203146e0082c2d80040075000400c2507818103070142c5000399580c001d4504050001c450642550300f006800c840d00e44014080050007003081011036441852894081030341d00740703400040e40301d00c4090075094241100c0c2803220021094200f500c4051000a0301c010700d80d69440c22400c840f50808 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 105784145 1250 105782895 105782903
    0x30d020712050309030405062505010506010906050306030601050d0215040e191440060b0a060f08130b0906091606051b0c0a030303050603010506011b02121906020403 73
    0x20448072028411030907030744103910881c021840c0034140001c002d000d412070758201085034941c41070702c40d042842242c0b00f404036215000100301420b295001402e02e0070f06030001c208000046c002c009455600282c40d03411100255090b143e68903050000c1640381c04000722410703140c1e00006000030000b4000302240e114400703400140603122030031410f08081d6030094416046642445002c2000340d042c0d0710b000c418040c203107503d25076049800c404282c40000d8034074003001c01d104e0840d504030030710460b400b440d407481804031500d00030241040b402910010791444a0810051081c0016503011000300e40102010b8000384a1000c0d864800351040d941e14046600c11018099080d15251141243d5144425288981c89090904030001b101c21025040c401554000b44903201c40340c085070300e8003852040994020740d0702041c1450503100345030960780082c0900741088029005501c040d98140e162544131681101c6524130000b10403001032030b141c0d45c161440196403010035145c080001c1d40c3e004104484c45 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 105785395 1250 105784145 105784163
    0x306030601050607030206040303110d0e0303041e0209010306020a0e060c0d020c0102070821121303080108030906040608070c060c020312360a0506040c0e0603012d0b03030d0207 78
    0x2240280803460241c1c0d58002d01580c007c0c000f1400281c040e8100c0c150810034030074110b0818100d1700c400019184040c1184419410000c180300501202c54000d40501003020a0345002d6942d580c00710354010014800a4003a81d8040746181c8080d10400081011034401001d0035291016455140d44400e9585041009849004440703c400d500125100044511000c0074100e0000c00407221154103110b13401c0880c91880820504002c1030305507031428000c80701c210300000c1d040043c0c078020700410b206800814096205125640059039000115000d485103490500c0c907a0f1150030381039441d003407184c00041015060060404040e68004094149107401c0d1300b845656440d035104441e64810354282400c0701620400540030702010803941e040c0c0b9079900c0d01c111000000315845160400c00c094404540009045004100314a03042001d40c1e0400d03002c400070000300001c09411100060080c00490045841103120030482c03c0d640d001c084003510180942e581d403241520384400a600414040300e10b190 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 105786645 1250 105785395 105785399
    0x1030804051002010b012a1b060912020603011505073e0d02090c0f0a0504170303070e130605061206011106010f0b030411041a03010e0a080316050c120306030601 71
    0xf10500514100e1041a1104000703041e100502044441c2c00140e00103500c1138050842000424518089246d800c003855044020760800800810f08101c40e40140e801c0c0780d500c510359015130b44078022241100e44120300107100c610310f020306551707a0042c84800380038041e404500003d5002c10b008101d2a040007102620b50599400d09010780382c01c42c50700c581e500170042d81014001414500c4d040c940180203a600503040204403504613415a20015454000580205081042d009440213600308602080d003d98150701e4141c0c8010302c0542c583e032400744100700c1460180e1840b0f03042e41c0540003800000e01340302e544079100c108064840f0001e4038968006103042800d4021b10f000032a960781614018440c2c03071b20307003490200312182c2504003038003e80b464a04098202c03440d039110b10660521070060fa440c0c240540f00c080406003124070b03040c00d005054000c0c0e058400000c5801c0c007201d40c40410364580e1425003201c07040c02c44290007400141e0074648210034038800d440d900400a1849000c0c214110b40e81e580e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 105787895 1250 105786645 105786647
    0xc020706050f04050d02030a08030114090a1a010309110a060315080604051c050d14041a0709050111160f150302070807120c020918011406010c02011209020405010308040510 76
    0x200c11041d910000100522044c409450451a050b4045000808440a1a00b651203400095000380c0c4454010100c2540202490508a0440d54000384000c0b042129803095901c80c2d002c1100e1882107810140d940008104108d801003101070284406002042e249803109030280003080c0c2c5841281c040070316004001000500040c0c2c140c4644d5118025100351000040d1611b400201603541100b800302c203008641410255204103000c49441c00d1071906903081608200c2c503950311407400741e6030706c1c000d85082080207078104c000f602c00c0340c07402c0c41c1940c112045160400d00300003d000e001e0000c440c200c0e1001807442c5150204101380c03480e10484000902581509404034401c1c900d000380280000c1c0210b00c0402c001400540d010006401c045010300c4481d8001256482c08440700403054021811000c00300200f4840c1c400c458100c1c5902e480c59082040010300400002d035002810401e00341440141c3c0400e603006034103c9030340a0b000b0300041d41c4a1402084035009801220300075a07585003500303002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 105789145 1250 105787895 105787897
    0x9120102040510050310030615030b060d02150c1006090903171b1b15160813141002030703061409040c0302040e0f0f01020a0e090708190b030a0302010c02070605 71
    0x1d49000f01100ca80104040099074203810013006030b0036004a401c0000045800d40c010510079500398405106000c1c01c500e000d00302c0f01005401e2500401d029400c0c01e0060b1a106895a50009505180d40c1c940c2d902603a400d150103c1418000061030a0800000b00da9840d500f10000c00d61181d100c0c0e48804a4090100503000782c1111644601109825281010124030004100b0030906100d568140d224407140f40e844c14030b030180c1110814603500100700100c003140c01d407218070711150b162501c07960a16206210540d0742d002d01c00f802911080c8000549030804100fa42c0a289a400c01507480e0b01c2c204101400034503107845a000d0000301c0340200310b1a4a00000300ba44103644c0145060185800d680a03c001040c40090301e0a80340f042ca0740141807074000708111440780b9040d900259607446225802041c1c401c02031040e030300411258040c05440381d0041c041c47e80c000c800c41048141043c540800c1c81c05400c1e4800f55540501860300048103069064020345500b0700c8540807121402e694079421116 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 105790395 1250 105789145 105789149
    0x1206010510080403020d030504020402070609050c0f060405060301031103010905070807080607030e0d0c06150321090b030f04030e0a03030503072a0206090321071101020127020d08040b0912010204 86
    0x1604110140c406d000e001e42e21140d003150014100600b08581681c50004070f035101c480079107103603001e0441c02600e03103041601c0f00d05020041c1d6141c5c0c00c207841d00340403420310700042c04018040c0400002ca0301c241d46003580b0502070507030020100c85816a41f65007454440c101402150b89038003031800007508480c0280100d0017a03801c6480100750f0f054001c201107e24180d040c104640a50300c54683d02500b01c9081d4101c400b45015110140341044034070022042090f8003007410003400400c0500f0000e450654040d25070025a856400109542d9443c080741d10304a1480c034a82e00584049000c400e1507030210140d80700d201c45458031110060b1380c207072400a0307440e21074201c1e5940010b00c49a10050a0440243c80c44403c064111000d400302c1500310080e100c1030f0507440707181e80008900c00e000c2c840143c034401402031b0280000c00842080b524003004030b1050500b05600c1c0000071034080c08540391080c0e51405550080c03181a281e64543e02090410fa00007007040340f140d01d401544130319042044c422981 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 105791645 1250 105790395 105790397
    0x7020601051008101e050a09140106111f02030402040b01030902060d0e010e0601030524010608060d080c0604030206070e090f151f030501050411120403050c0c1206010510080403 78
    0x380032000d0740c074100c2c3c0c0302400814818103012441d0b0009181c0d032401030b0001c480c10340c4078944030038a801c01051008082c80755001035401c60a084c11342881484505449064540d9031030202c010074060540301c4c3c5001c500c92103506010f4100f03003044c051a429a406507026034401c49003405074100080044003905e25004010b5401031041120084034000c66010502c2c1041e00000440c50807001c0d54401d0400100740c0c0240e07025040301e081035036130311412041903150a040100454007941400e000516070000106001d010b04d60f5810190309019a000903903400c5003000d01212024542881c0c000d403240c4064a051020031a43c810081c400e261180075144920909440c6c250701c0d071781b82502c80080040104c1070541061100b1980c082e051041c41600c0c00300c1030541c80c045550b51506045c03000f25410b201c4002300c503034801d2103032145205101038019000707074240c500030b900c0f10100507907141000075000745a98041014201584900740224169040710b1049802d03001c00c000490080e40c403150220f400034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 105792895 1250 105791645 105791659
    0xf0c09010210020904060f030b04050706080f060d030c0b10150c02010804060b0d0b04240605030318060d0f05150102010506060d090c0302060a11010b150901270f0801050702060105 79
    0x40b10609550192030100e4000304080381b010f644046c40a1714407450341050b990403c1807000c0109115042002e400104130500e0014041c1c5403a1098902c08a009440310f441000b01208900c01c0c5031080e51004c000355084030803020b8a090061000c180c210722403013149182c07007007120400607060190364611b911030740603141c04005035569030361a00101a28005168050000c5152401041c03002611038421442100c259440826142c140c0f01c285c400c00720b0002e0524203241061206440201c01e0340c0060b0003c204012060b290180090210301400f804bd0b02036500d4400f496180c090035400241c01194504582940c8110b29001203003070704c104842c9190005010048140d03074441a9014000c014056511205130f29101da001032220342c0b10a200f0320004001c400c6c0b816070340d4001e01c64100300b040102d500c1590040d104003e141c6e0360040d030448505000b100111400c86010181d9032a4415642e0003503000ba036034803003202124003996405032020039031070540003c842c02e00025120703050761001060305c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 105794145 1250 105792895 105792913
    0x2040b1c020405180f0d110a0201090603020706110a0e040f0b09041e080f0711030715140d02040e090d0c02031005040602070b0103051f150608091e060f0c090102 71
    0x40700103030501a000800c2211384018503a00c00740c042c000001c802800c080a400c40c010b82c40d40040c50a401c464050f0815000300c03070548010b031f800074200742c110307010303404c000da06c40107039040070002454540314001d900b4400050301505207a1041c06100d071031000f00e8040100c41001101c10341160001440780d42c10043d9203011078049040f83c0c1c11010100d00601410390001e40607900c88045411409a504042c5070107e40d8400300800c3e030f040c810081300b080c0e009003100307031405075011100d02e002c204040c140034403148910082c2c0b1400d8216041d81480200c00e6503520782c3c4440c2c2c0141d44000715103514190081e26192030006106540d40092181c009004208501054200c0c800a00f80504200c036480d508114042c00142e4144200380254001c0000c1e2282940708200900380071542c03d926000e8514220100030010044803010090750080c0c03401040aa0f0307503401c0d143c03602c1c546a03030040c0512903400705401002c40010f221b1b4400c05a81603074055039169408140214058049440d0141e0400380ca2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 105795395 1250 105794145 105794149
    0x307020105130b0d02120601020c0114210430021b0105070b0a09030305010503030a090306090812040b07021204060c060906110703030204081c08070503090a0c080a02040b1c02 77
    0x20740105100e04812440540d41c40300b007440f0b02c1c0d108203a40713a1034940124001260345140700c25070307a00c5503003030000d01232020307070000005c2004403c440c00301005000412104081c210301c2041846800001030226124206070820100032000a409481c00415141840c405002d00c5845203540c09181d0f001009406110305110348450302078032100d4100001401040041002c00d422940540c5246a0004208101d824024150303038058024501a50082103e44100d0794490485001c8070b402010000f500c0781e90b86041071180c803400400b0041030041400b40000c1c40401c0c14018003030529030302102e100e14050034128009019030701c2541d000c0751024030b0700742c0407074200c1d0407100f0f10074030444001448030407850345250b854018210641c00203501040500280100b042400030321040c140100034070020a03480107010040080c6154200400400031074483d620801100358000d038846410b01c0844d449e280c00a03030b1150001c1003a8440d80c10305000300082d050103082e400711400580c000340060304003502 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 105796645 1250 105795395 105795397
    0x8070e07050304050c060f0a02070902030705071509051f0b01020c0a211b060305060405010302030604170708190f09140d080906040e041a01050315040f02040c050a030e010e0307020105 81
    0xf206581c2c0b40910745456001e50b0302c1c000100301925010078055150914000c0003454401c194000c101d0345032040042c004481d400070166402e00c2d9210b20041d080c041000707180c0c0054175000c0ea00030720501c100c0c3e0b8a08411180c4e020344500030741042c0300802101c000e4000482ea03515201c0034030354100a112100307208035842464040139500189100104030500c4c1d56483c1890b080c551034250b064030003010240b00550345402016000101103606001c207505580010713032200000b07040103100391504c03000d19000c26400001c0d102e11581080115450b4825840728030043c014106050700012014000220403901800c0c00209a618502c0c150316607070400c82c20311010b8a4507140a4401800501600c0c00d20b984210042c00a8208051300c400d860410b854240e070f40003100710558903800e2030000140400d03100012101c4c12440340030800341e0301e92207d0a209000d40036140d0040c1d0024200070a0041d0f643d0000c005284440a550742040310b44070480d00345080341c000c1c05044803590420040900950701c610 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 105797895 1250 105796645 105796651
    0x80402010c020d0203070306050a0b01021f020a18030602070b0c0307020c240409021206010c0803070503180102130305060907030302071701060f0909061a0303120c0d060605120108070e070503 84
    0x10341090140360513500000c0ca00002a8000c54100b5110b004101502619014601c0030031001e0008108200f00361003600e8880c0b00e03012050328036a07400f140205400348652030740c5141030420641a140c581d101d080120180d2f000050940d0009107050102e0090425517003128402d02e101d80c05401c0089450040020310080c0c0b900c240c51040c006856540c260401305c000300010b00b403001005a1328014840d58a291950040407141444091500b00010404840c1126800800c0e46000d581c0e0380c0c0c0d0303202d40038003000003052140800e40c40170408a44d00b801c8009075009907030040c001c460050380c7e900c2c8426038491240c00003e0058011400c01c10443c030000a091710515800c800104101d40c6403e001002c0c802c0d02c0c0c0c85030201c2c5032100640000d020942c0706540d14074501d40e2199814081c001e012aa03070740b080c20006040c080c0d00c08005180240c07254150741e1994840030040c4900f66071480c008003c2c0d000261165812083e02000040041001402900b110070300b0408a40366950204c00340c81350b070002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 105799145 1250 105797895 105797899
    0xc0c02130507020c03030c060105040507020304030b0f09011b0f1709100504060207080703022407090608070905091504050a0506030706050c0114040f0302011415040b010c0203030a08010810090201080402010c02 92
    0x11210700e11302e6a01400a031195135020001048558540b400f0081034520161071a000d43d04104003e0010403000300e6160f60103640e03906181803e8889503030880c01401c0654150601c4043e0340e009044242e0b000d01511780c00c0c0309541d5046020402420045400c11040d100511b1a90000104500d800c1d11500029400b5001d007000608040c0340b074131502080c1d809408210010f81240103203481400208000ca85401c800b035240883d50303d40f22030040c1c0303100780d0fa00410050050050000c1c0c2c800d031045d2481409440050800c5981d400d01c00b140380c002001c106005842203013000005440b690251280b503202d00c1004006205051030f003e0241d48035406003514456035500c1d00750109500e40340701d03080340c082c0348a4108841d4400d06420020f00f11601d8480c07a80c505a00b81003030180304e00a20078002400d000465001910700e0072000185c4205501d2035000b50107010104c0d0202d02c5075000860f45040315031030300070345a10f40d58a22041085400c440700087c0800c01100110703000d544680082e000c51440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 105800395 1250 105799145 105799153
    0x908060f150f1903080901091202060a200d020c0f06071e030c050601030818040e07061103040905010b0a18180f090605090d0e0111030712020304051c060c0c0213050702 74
    0x3c5002106400301040c2c005655002d0b001a41c00d030f555911032035180003040070051012903185540d00080c01c510400d81008104490340600c52010810840d00301d00e980c040e581200d41003d03160030b010307458900b6070348045d1240400c00c404c01c0706420204102d4104582c810300100782d1a1070300c1c2c806110307a02c5103441602000407120000c00001c004001031400385000d42201500c0d4501c1c4114004108200c02d50180528141020a1034085000559101b03403511410420280c01c03400d018036107180610b50001501908000002485c1d001c2c041c01006400c8990342ea207113003002120190785001d100e03441100c0301d02180112018211203250b103d105104095034011071060400d85440f8213403117099840003840e41111041e42c0850b90402c9080340048030a080501c8a4030780d0000f09503c034000c0b01000303011041f5020401714001d101340221000303002c1c010a44a066913a260044405528100e421542140303040b604140103809190505100c3c0d6004103540b000210034104807001c1d041c0580074105500c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 105801645 1250 105800395 105800419
    0xe10090f0504020906030a022d100e040f020702130b120307030810051801120201090911120f011419090612030f03020405090c0a03060e070c020306060405010308160f0209070908060f150f 82
    0x542c00507032b401d41c011a951030300710400045017040304075003031621641d004501c10820b050040c1c450702104034010b40340c00000031f1003482e0384020a42c4404145e050b92103a000000c0c400003056001150a40101c0701c015042c0440341c1ca4409100b014007d00a0411201e4180f078010400c40300c6c0c8100445089106240c4040005d507200c6806060b20721001010f4045180801c017040840b0084285580c4020008801c0140b07516090111500706480200c0d10f000e0f03113501c16018001118081c0d100004c02403900304100641c0d4416075a64541381c0c22a0132800142c0b100103030140036200340203039025a40020401c0c0041e031508450080541c1c0104080c0041c50f840b5440040c082c69103000c120b11501c0c0d00e44551100340c1c1d0a00c105030400c8001016503100380c1c9000e00500c0416000c10540b8200701c040340000c004540e00b801d080d50b41c0800c1010080d8012415806c1122036079000c3c520704200e44000342180c85070f8a401c8401c0314456030446039400c0d080c00c0351110b0f0039680b4212a018019560203006009401 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 105802895 1250 105801645 105801649
    0x1031e0503030c0c010e0705101d1e1207050a0b070f230d050f0a05090a0f03200126100b0d020c060105190e10090f0504020906030a022d 60
    0x1070000c40c3c0c00c08080601041d10a66248280108140d900c68540030b0009107003071400282e500c04501a5400801c4201d5013400700e018124030040d042c24170001c000c4544036100341194100c1a10112800d4000e0506485807036080000261010640b18020b00038282d980c00e00d03108124a03001800140c48003001c0c2d010316404a582c4000300510040a8209a01e50300380643c0040e00c4e01d2002100d41e41040820000b1460801004040d526007100918120759910300040c0081ca2040c05038124410100c1000b600104110307034842d0003a4030b00d01004a20f4080668100123503502136100c0d4080080780101500c071241d40038079120503684a10710030980121252646001103464000282007014590300040c40441035004110b42070041c80102d450982c040e04ca01580b01207001e0921410003000c0c1d4410114107090135030008180a424284801c00c60165031912030350144c1019240bd81c0a15240703c0811100d0902064800c08643c0103840c1024031414440584aa148044180c825208114076810616 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 105804145 1250 105802895 105802897
    0x60103030f12020a09050f011106010b070f0206030712060e06030c011206080d080a050f010b0f090d02100302030402040e010203070203250b04240203040f0b10030c090f0b0301050f01031e0503 84
    0x16a845d00015410715060010620030035441906000c01c480e00443c440c0000907041d41520300e0644905e40781e0195161860061441507002507101c0800700130024899401040c800100340c40070300c22f00c4420b558586071031500109448064041c1c0000c10301007059400740301c080d04001c4801c05c00086495030341e0440c42c10803290702da0500028245405020700300c0418001c50b60080d001814503134543d4075160112880c2c0c400e58400e145642c50101e001410303a9a50740c5104d6000d50060f143c80d0020700703600001402580111400c91043e13140414158844105100340c2c1e125401c990000c610786080304035481000711601030000d4413a103541c818500021000302050f0b000d58440c0303c1e205c1910b54050a1005658440030101803014418001c1001050402980104107900408000682e032200c4a9907100d40d1051303007025083d0070300100c0000d00c500407a4401c1c2c0c8441c050010810401c00c85c04201400c2e5072051310000e218000301401440410380c0e201d1040300c3c5461403950802191429900c941c11 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 105805395 1250 105804145 105804157
    0x1401020408010903030b030c03062a04060906030f051b0c03040504110306010909090b011203020c09160e04050624041a0405010908161404060801020c16050d05060103030f1202 77
    0x107140d4403000c18104040d094010f02c1102070342200600546480b602c04699200c00003072003441854403100d40550760f001000b03c00046d01030002c46071030f0b0b181d03101c1e080902100414032910001a181c00042e0f007122a082c440c3c0d500070a05d24406000d0108040d0800403140c2207514000c1841c0000c010024240e078031403080d1890f040caa1840c850301c1c0d01d000c60024115085e95480078110034107040c00340d80014034044140c5c0c1900d0304d00011000f0284103050887c03600c0815013605402010507820b2086650410354074491340d0007136a940d42c01c2030b19501d00380400d544040c0d807102e4000c400e4454041084120039407144e510705040c40600e050580e9002040c210328008050b403246170b1000201403100d9680202c190001d4038042e002041d1104120b4106041c04c1c1c00d9100c0c2e03503201c51044044049e160384075040b0000030000d0000030744d103e5070041c9607240c40d940d03000020240e0402ea16400143c0d42020b0b10340704c8001d0340180c00350040342c3ca941c80a940c181c1c0c0c4000c4030000c215030020080c400309524800381c80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 105806645 1250 105805395 105805409
    0x60303040902040f031103070b1c0b090907030c0603060e06040f1b0c02030709020c1902030f030706150503010e070303030e0307022106090102031012020d050102072f010e01030914010204 82
    0x3296441c40c105001e1501c1b09101c1c05020b40c220000a0100054200842c0c1c00d0040c083c41100c0c2c00d400c40d000c0d54009100016485500128150921402c00d030000340340f43c1503902840030480c1041d07683d001681150707817500c500200403035040c00003203482ca003540c002420080704441c0803419a4150015880068101c0c40010200740c900c0d40b00d034250b05082002c0b501070020080214504160300c049103039520076101da9803100f0700e250000711003152400e105440500200c4030459403101018500324001c1c12240d07400c192800d41d1014002030034a0140985070303004070851701400c220f034110344089002e82071083d5091010311040220380300685030380340480c415900700c1006807404c44100c1a45401c009d4003501c912142ea0062091102044201c1c1030003040312000c01c00d4103617950081c40418248003a012000c0c02c00e5202058143c240700040038480c3c5001d10b038801d00d12100100c500c007900382801c03010345140080c0c040355035003e581d4080ea01c242c803003c0c000c1006000c4001c3c080b00050a80e4001e0308258 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 105807895 1250 105806645 105806669
    0x705011202071e0c050910051306210b160e06030a02091e031009031b1a0705071b03050304030b06060c0706030e0d05180402031312021b01020307170306030304090204 73
    0x8030130301c0704054105003d031078229000d0711182400c407e007171464541342c0520361103180020302a550720402a07018074000e21446041c1c2c80b81d100a9580e4403a41d00480b1815030344c600344540002c0252020031004104040d01d9201c10315244282d105000c16031b00000c00000c002a82040040b140e07aa880c51184401d0060401000c46001c80000785401c02d03900002a44a060a04180c1c00010b07800204981001d4041100780b5000005130070600b1803c00203221a107000f10362070050008a5911400030070000703006405411640b030840d2a103071104000307031001800c550410301c000c1c00060f6210340003a4004000034031b01802d0000c0d46219a081c0f0903158003040c0440c2e594101103c0682c418415440311100c1810200e05203082030506a80080341d00d61203e12503540000040c50004011508000140c1c011003041d581040d110400396035406030020308035082d907a03003405080f15840001110100d95104a585640d05501c040e185400e030009030150383d0500041c840495400500d10140004010702ca80c04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 105809145 1250 105807895 105807953
    0xe01030f0c06020607020c130b040906050a0605030d020d0e040e0d0f03111804020705011d0a0302100c170405072309180d08060d02090c070b0703020c070501120207 72
    0x8048800059407180c4190b40118017001205500451164607540c800e8565403510020011010b004044074140d507503000d80b410902e801030090503409544101c0541504100c540c1c0c8400c1090384c1d410540391050016840711100840051042040c80d40f0700d07030060000b08410001e503a01900f8140119400b0700051841034122031925414054582c540ea18121050b2130010a400300311002c0340d0300a4141d000d2a00003801204001c0d00354807a11321707000d42510300c2c0c4d841c0041e800504d4454485150035001031044034040060369801e0300c84c8820008164a410b5030b88a0300c0c3c0c0140c0e907010f00007441941c0341c1c0604400002e40700780c01c560210035405401c070078400340700700301d810001480005482d800c402d032007050031003500d42000500c0266450440c20101c1c0c01d65140d10001e480c1182c1c900c4003d41060840041c06070780085103015100148c1b25040019a65445c0c0d0700c11800c031301800001060952022100b00f03e154040d62100081403c0c140c40945400034a480d02890b40030b1071103150014030401c101d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 105810395 1250 105809145 105809153
    0x50c040c0503070e0f060703030e0f0106030c0306050705090a050d05010b040e0709060e040c0e090102040320030c09041518020306010f051f020304061409030715030b030c06070b100e01030f 83
    0xc0b100004040705c00d44100928080030880c0c80c003d03210018103050742d07983d0341ea10b2402c0c1000041500300f5110002d00ac2c1d643c0700d24045010100b50300c07040303811a09280c04100802d008006681030b00301e010303094502a92901042003140c100702441136405541c0d44039240318680b1180101d02e100340304500200510f41c1b801e00c4180031103115030700c503601500c000b0050100041c10000c0b42812118020389d00f03c41e80e15140000c074024802c03940010241100c200d400e0402c001c0804c4100302c1c2c50012400c1d100c2c401c50720418010a82e4040318001e2202d03120094000406080383e00c00862241d807007000c8000f8072140d42c0441d150800c01e8002011050080804100f64641840d031182022230b08003d128a8140800c8040e40d40d000c2c2d40107020a00c40e41c00d210400180d015815200c2040000741142c0c0d80c20b03500d400720140c04a503031681c0c800190030a81c02e00b00d6420002031080c030426014005528061440d22403880d17103180644110011650104000f80310700c646030072140614001c14050031910740600c5c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 105811645 1250 105810395 105810407
    0xe07270e090c0f130b011e0201140a05041106030a06030c0f0305120c0309090612060703050604050a0207022b050a0305121e1603020c160504060f0b0a0c050c040c050307 74
    0xc48500c100c0d4410103503010b0b5111401c4e400004441c4c3c18000c035024000c40010303660006114900e00341c240540010340201c1d94150800e2042042c03510402d0200d45880114009883c800c980240a4400c000d2103110681803400c0119400900c4a500003611600c07540ca41c512a203c5a128041d13509070207030f007402885800d008001852883c0c7c0000e0f480c001040a80c0b980302e00a1080d680d205030424000510035803120b503d0130001168900c141c4080b4a00640090f009040c1034805030f010b0780c5402c001900d121414803c481805400404100700114035907a0400400e9128813103082240a000b0110300064003044418003140c4a03854460b15114039141c84510b030305c801450301e44041c007110000406081284255600038204103e80150706447c03c0381600a8410001081198450414000004c0440881507410350f04112410b104a640e541c00341081c000d254042c62060f644104913401c4c072640201c040042d8944194203481c4120560780005084400d0340c041c00d0081200001081240355100d8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 105812895 1250 105811645 105811663
    0x40f090c020307032007050409031107080607050f030903091207150804120305091e070315023a0204030803060906040c050901260103030c0b070206010e07270e09 71
    0xc03000b54102102a00d00801d2030070950034806412410b0000e079a0b030000705000440c0540741c040d105100d400e02615000f000d41b8202242c194690180c4034022856030f001003180c500940d55550303020309100040613400301c607500180001c0814441000008040e03111010101002030a040c00f13426400c2c41c2c80c1361420700440e84100b6104112054007080005041900b55541c41d01561800145980d281c0100d9454881401300180c4044110380b10858a1000003c480050300e21400c00241d4010048240320300340d004000000f20300110507a4003110305254441001031000b0b00128080800f413092143c10100c1c2c0c825002550114400820080981802d1303e07900d41100c0255820000c010300c11000034418000c0141c01410001104266080240018840e005400b4001d5181c0c016503580c0c0317400780041c4804102251800c49250001e01240e0011a000c2c0c104c03003400c8442061a540c540c012103003004c110302c843d00d80101c01280700342000303880724254020382180d8140407050308102d550340786440014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 105814145 1250 105812895 105812897
    0x14210405030a120501031707230f0706030e0607080603120708030708070c0c030303200d0207060b09040f1101090b12060f12070b030406060305060c13060801060807080a060b040f090c 80
    0x101004100141087d540315181488240300c01d40c03a401c1c030385040c04406c7d940400d45281c45444804090100d0000301e1a445c0c817050711000c4640c0c203031b0346180541c15900c26041e400b030150001400241d8140c015404550b1219006041d00c101000c10700302451150045101030b26084804020403c042d5000302a050300180c1904180092480a5464440010250000a04050301d5110340d03000d0040c44c00d00d921900182103589512008140c0f80c001c0250010442540c0907800e04c11514031a041510401d4080c90700481840b0564415440300d1403405003103c4c01c0d5040180360a000a8816411405002c1035801080c6110440c02d18008000b12004654030161244420104594087d000055600100c1d034198400f981c9990b9903080082c002e2815070700180c050f009010030840c0d07154003c80104840d070b4009121040d119140d0404071111007090156a010401043c0401d078584e0040035480d40c89020030f0004601240c1346c0103041309a411a9002da80c90f44400c200c20300108401c4d000c0c0c02d5421034a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 105815395 1250 105814145 105814151
    0x408010c05040e15060412030e03010b151e0d020a030b090a0510060c080405090702070f0b070309050906040905010e0304060207091802011b0b04030c05010b04050714210405030a12 79
    0x4000c014807030310b0300c041e204e0140c07020364041e00781c110780f203110640300100311001024008400328240a8940c8007494100c03842546010307050b8100d4602115400b0f02e81c18492102810800026982c030708108180714101e00201e002c0c421141c4000b034074002069000c284c1c0c0d030003041c220003183c20301c01107000c0078248102c0a400c001c100070500a004051200b21400c600c1c0c08900a00c140c20300f0080d521440d003041c0e0308590b08108200c1080d40010b41801200d60400c0180211540c52003940024090004000c0c0090701c0c4c00000c1180c2d2810511940e00490b0061000404c3c1030244d03100f81c00c558402418070710503000490200030703e0303030140480b4005000c050710038040c45180c0360307400c8410040d080c0002c1c1400883c0e0b1968200741d03075041003828855400105003451b030809003070203011004102c604481300d40c20300c0300c080300d181850f0003854003846643c1c80e030340706030040780880507802d411170880c00c882c02813040b01c02e01510410300b0300346028600480213540c0e03a04404100400f03c045030701040f601241 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 105816645 1250 105815395 105815399
    0x904230a110c06090105010e0106050c1f0b031c0f02060618180115030c12050706080a0207020904060504020307080610090203101509060f0c0803130201020316080408010c0504 77
    0x20600062a44502400c60008103440400e0501d8094042e819452000b8030506081100c524815400f003030590741038003050782d030580c1d80d40342c00c58452140304914609a004404801c3c41803100740c0d003030301101f00d12800100b80480141c0129141500c075812821001e9508030442c0c0e8507030b802c012400300c00d00300b030b2020f4407075807401b580440c821420035583e81d111450144009400c0209030301104551080140003800702c2d0034a041d50305c0494030756020a032503014044800240401380021581f038402d611802403d0100e03d050b0b0207441c9140010715030481203800f00203000040e51084007440c803c40c49410700143d40d041c00d00606140c00040e8010003000c0c0c0c80382e4180180f10003401c40c00b0b0101c41c48654003507a00e6545c444102d0421b00d00703510200f802d01200c901402d04c41d07080100304041c1c0b100c1c0e0b03464600d141c190907812980030314110405072a6101c100049000848000c8640301c156006004591400491f910042981110f1040a50740c514010800380b01d41a000e01859901031042d24146051038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 105817895 1250 105816645 105816701
    0x50604030c0509040f0507030c05030c0a081911030a050a110306090604060b03030405041802040c03020a120209061306050301080105090a121b14160b070c060f02160b0904 75
    0x46618022070f40700d0480d4100007030820211003880c005155020060f40c414568910b00f04c0888841809428800c0c000c0c270340996540d0402d920300b08102c84044009050f841004c880080b00310407034a0341561001c400d00840505614200700ca0700903148a040100303a45055410010742e1195410559840707600550103000c4103240021b203075074000d9001030b0001410210200040c0c0340d48242d600454000c0d0400385039400e82078600b42840c00881c02a58144441503640008400700e2240900d0440030420924803032094000326809842291720240c082c0707281503980500c080c5420107951040d400100c0c000010b20010b20300303020b1503030002d03203640060400c01903590f01d907080c0000844d401c030100b00c1c403880c5503001007519030505106543c1144401c803a5070160b2103e140c8440f210b4100f43c500034a00600045c68400d00401c4540003904001c041000c582800d208442400e10320329440210b00c10600c0040141460504040080ca007810b5003941d58201350003030005071603e481d40d01c2615242c0c504024401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 105819145 1250 105817895 105817913
    0x9040608010204292710181a07060203010801060f080a17030a150303020105060f01020606030703020402030933060103050403080105090601050403061517060403141b01020c1605060403 81
    0x10345001c04203440540c255141010032800b0f02c0854030410311780c1035612814999107407040400100242c3d0aa190100c030144203075041070601c0f244803804100403004104607120284148407000360040114680420764482c6802c2e82c00030307007042c80182d54a10b010455103482c01c0d4260010002c0001900d1a6401900c1c4d480e042200c03d42c4a5030464000000203290760082d6000392004000d464104001c02d49a05000b13000380030860380103000c0d13403803c01e1881c06076000144040c0703c1c10000700104038041c215402e220194002600b160014820142c151141c10080b8840c1c00303100c160000800c1c40100030003004c5880304006400b55051500e000c0c14000400c1e030103030b5031030b040d0703207003070303554880350340f40d030710048941d4802c60340058407591402d1ba10450041c00e9105040840e05100341c5640750050410000ba158a004e8038001c0220300c000004c841400d80741805807841c00405400c2c2c082c0074406039105426070f4000202034000c0c0d0480a411f4507102500701c00309000e03000981c0c01c2403d160a698032070350340f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 105820395 1250 105819145 105819179
    0x807080f0606070c03080304060b0f040216060e030702030712030306090e0607200706030212070e0303070308060103060e0906041a0603191104060b0315030d090510020703050d0509040608010204 85
    0x5690005040703000c0c0700c0e4042902008680c40284140c7e68a072508191004007400c440c030030320440c00340c0303480011460240295640c00100124004031010349680d1540149402218100b5600050000d0360144c0d5050010364014109084001d030130360350602e00202146c1c0c1940040c020079252a102110119000880546c0803056080407680d10342a00c6d54090075601000c180041c5201d40100481d5556140c0c0180414030714806041d201d64407100700c2542d140d0075140100d505039001744408030121b441084940e03007041041c10300048864131500e290101c08812100426580d100c01c2c188800c2041c0f043e0391040c01d80342030b401c45003241050070029840e001803001000c0010000f2269005008880118600c1d0b075200030700400405681d07440701c000c190030031511100d4003030404c000d03021142008903800322540c1c215640c0c540d1135424401000105003042c452501184114a00440000c40402000c0703a918506e40715161a540c8100c10001600e0b900d03003080001d80d0041c801000040501c50030b00c22 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 105821645 1250 105820395 105820399
    0xa0810060807050a11070605070201030f060303211404060903120b0307050618031b03060a05060616080705120301090b0627032e06060804121110090507060807080f06 73
    0x580c80640c4c00301110100c10580340c4400c9030190990014000307801c000103250040c801e827001c0c0594208107000c032007200c009104c0940440c07030980c02d2030010b24040c1003400c0d808010032000905412402d07080701d40d101c400c40b0111400759980040a084c1600102e0101c1d040d41c9050040c045c08105102094035803020740300f039a009280210b961084581d44d0804150300340d00c094200c4803d05c007541240c6940c2500784a600d8000d000d004081060903440d03006240c0315902c050f10103440d01e40c1d211041041926021b0043d42d42c940c0a2001d800042d009100c1c4689106600000503142c1d41440101b44c112070724402411322481041103000c010303240600b460700d0f814910851114154001d02c0103e41400b454001c4208924113100981900b60f181c1c0c0204240f038130350a101009080d84610041c2c691000690300500340101440385d801000f4401c07000e18921a9160080c0c82d02d14546e10001000d0f10400320003140d07550010395041c00116441814107600a045151a0700c85041000c6441805280074001c18 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 105822895 1250 105821645 105821647
    0xe06030720060708010b12070f120f050a1a130203060d02100201050f010b040b0d0e12040e1815041209050a03050c1005042d0503120a081006080705 65
    0x5008603004982605507080c0103566510341d07140d0391200301c0d140d40c421100300c008120710300000b1440074051800d9960300f08500c2c1122400e5120881c0580350140c0a0016904014080c1260f0303501d29414000c1000c449000903020503981404c005c11015101030f4510086006180d400108803139464244052012103207040042e500d442d942c000c41d08000c00e0714006504101c900007002001981503120501c80d120300707012a20266203035440e000c0c40d44640e205455040c4400c0c0500030b441c102e00d5108203602c400704000c5488a04060a410200d0f42040d40084900381090b010440b86a14070070aa010702c01c11603000c0c119014001958564580e40a0400790280011308002e8046078000d0101d03070f001d045e0081c4107118240da285481c6640706079101c03080f40940791803800d005589008d07a080c6c900340c0c1c1c0c800c0b913a1402001d6202000000c80310f41c005c0d4074009a140c400000350380e05d05000b50340b40e40e241501c00d42e5881104070800340501c038002d000003c21210380d09042140039408551190410709520b011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 105824145 1250 105822895 105822901
    0xd020f0402120c0a03050f060d02042415030b06090603040f05010209030613050c01080705030c0c0c0402040f0f0e01140f0310060608011a070510050601020a0b0f01061209030e0603 79
    0x30400a0040e40c02c1501c1c0260280300344402d468070540913050344481903609110680e0340e41b4000311090030956600d40c1050018803d071006140c2500300d41d07500e203400c1c03200d8a5620780282251303200c00c080c1e070310840418006905c94940e00b5450302030545006c40070b582e91071611304c0100202d03075035110090015004140c4244260f041080a40484003480070040403102c0c5c80c1005001d9101101c1d601c2411511480f0345240c02c15a0350103100c189106103016191607041d5541d10b51915007075448400880b03d540101c1250071466a0b4500c040c1002c0c00444440e140000d082a100c0c0310410340642000840c245400010000c240c1da260b601c0c0c4031400700381c40f0342c43e1841c5030034003003440c20040411100d1500d007401004100c95034440d401a04079400e1140d11240b01d113107801410058440c1c0c0d00064000d4024001d655003981c002c0e002181c12520601c100c912104140d100c00400c2501031702c2404200184000421042d0b0348803105007140d07110610204059000ba542c09014140300c100c500d40280808000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 105825395 1250 105824145 105824149
    0x40b040b0c100204061809050708041101180902030406110c0a0204090c090e0606010306060f0206060405040f050f03120a0c0507031808070b0405090906010f1e0f0b0a0f020303060d020f 81
    0x241c180c681c0b02c1e00384195100ca803168006010f82d209000e4150300060001c5000842d03400d075004513400b40b015900c0d4610540c0340c5440c1c100c482e4056214060500aa21644803c100c3c1103000c910020400e4040058490402d40f501c10289c880c0e200d4a601004010301c0400c3c4000c0d00820210074030740e41141c00003550b2b205850000041c1c403c55101000f81070bd011144c0155000106003d0b2084009a800704070f500c4d12010700b130751640c000304200d000590105001070307100d0a16504c4150054041c0301e0008080c03803582d9941e071600c4040d08000402e42c00c0465808040c0d14644030458100d00380c00c0003805141d5000a00600c680100d241c0541001001940403070381305800c0100c0809013088400361085c013501e848110000780c0c428840c0d240991003076030000f00080e2022404a050b1180c040c01240281d00d0400410f41141d6105810201102d128000003802c0b415241c1e5000144481c182040e102c10615902810b1040c0304901e001c03d54004000304140c1e41d98006152591a50444240c8001e00e96000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 105826645 1250 105825395 105825403
    0x2070305060a1a0904140f0d05090607020a26010c14030a15170a05150c0f0f09100f0206060a030b0601030e010f05070302040f0801150b091f050c1002040b040b0c 71
    0x1142a80021365402400b091146041002d203104c8200c030121048101e407a045950f4905807800001c00180080c020030b01c0900c1c1910040c15140e00003000482065191403a444840c0c00c95a01c001a0050401b0381782580c12007801007075008009400d0041d181c2040c200c0c4540c1501c4000e1440482035500c5001c11200b07800411658003500b0b064401c141d4141201c0b401c00c3c0d0303a0480c40000e90305485654140c40d03410805c9403a082c4102c6501250710b0500281d21b0100d102500664a001d0341e480b03043c2300941983c1c441412410405a550382c41c2c1c129000d4a10001e07040100240c6090301501c2100028804541180c1040360070000c2880c0004820405008442c0140030400500c0b0700141070906014403181d06030041c009030703000d0000c08040d0903590444c131401c90349482c00c114140d4100b40b034100400034030340c0c2c054641c421340074000c0a1280141a200f1440510740300654000c26008100c0d00d03200d400812500c100c106601c0401c5103818101030480c0d41c0c501a81c401c100c180c11000503102c01a0400b44 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 105827895 1250 105826645 105826691
    0x30a0e010915050702070902070206040e040f06020f0702090105030c031c0c0204050a0b09060604060207030f020a1e09180321060305030424030203070518060c030c0105041202070305060a 82
    0xc8407003181d0311202c1001c0d000c2c003410b540c100014484c1d030070042543d0f0520710840d503156500070110b900d001d00c0e0401d400c2c030403840244180d03003e420341c55820020401d1030004090944400d40b0060361001c0b0b03441004143c0c001a0402030290340910101001074500080301840c00500c140354103009800040200d1707911840c1600203402a00302014031680c28a1500040c0c4000c1044400c0c444644c3c680050189a008070701c102c100692281600f00080390351908005003560004d0106c1101e2500e41a180900c03030702d044000c04000304284010424200584180d800d5100d6252485000e220241c6005010728441d1020180941c1c0d01ca94440150700103a00440045500005681d100c80da2035010035454480c540c5011000401c1d50341c21020240300344200d900c11091354407100e08010214800c0303941a546011100d030001d030200031007a41c01200b0000341100030ba4020000c901c0349050301d04281401c14420340c4a041d903120810030700000d040480d10980c040300c00400000c504d40c1c40c0c01e441401c90022 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 105829145 1250 105827895 105827903
    0x9020604081608070e0408030a020d020d02071505010b0f040b031504050f0405070914010e0403030605040f15090b0f0d0f0b1302121203070e040f060e040215070305030a0e0109 77
    0x203040c1902c041c910780c020489104000b039a01c800ea0fa540c00d4421210211401020b107041000003480c41011640580b40d0103041400050803d13003c11120812030740b080200741d0b00c3c00b001c06061011801d6038000c0342d0240c8030344c149490a00c912a04409480d02030f13070180c03440d2010080009128200c0303035005010f00c01d0004105100b507060405031090301c05820740d020b40b6203000b03020021900e0349441c02008a20b0031085800c0d410350386000e120410f503034000340c011420561151000116940c9a0041003104010501c002900b01c1070095100210301c0b071079200c3ca90039820544541301564802c50b0070941c1c01c00c00c0d41c0c054603144245c0382412a42c0c80060009020700e40e19414001d075480010707400542c03036100f501e00c000c21400d0b4030550356842d08900744001c0540302c1080040c0c9103e00c1031a050194040c0030b00081105c41c0d03c100e4440135503260750098035403072480c801000700f94a4208ec41581c1020402249444d0900544000304030340b100800b00002c69403217800c61080013030309500c114441c40d08 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 105830395 1250 105829145 105829153
    0x30111030a020301060807050a09050f0d05070e07110106030c12140d0503011401080906070e0a0e011502010b060403051002090a0e040b0609150f100915260402060702040902060408 79
    0x401c1c000c1034000e4000380581c8000906002c009012580100116071269081e030700d0b540f0006151000b00481407a09001254100c005400094001707481001700340c011705022902d558052402080082070030b4803007410248981e040410030008590713030005050588443c081509144e0351113040c90404007050f5115031805115090415a5441d4004c020358180e0742400c4000c02515076100044845890a0b1442d114640009000c203e615009181230700c0300150242500f0541e17a61800f81c0c607000002680850411015008480d0308603a0a2140010450040b9445810142036849445d500e1102e03c0d0050011940003c022a1542d200441600100350b04c0500f80340d68038080c9010598000141c541c0d5015940c3c26003c0f500b5003d0010540300d00780c030090f048880745107541007004041780c7c6d1030203ea0203000ca91000425111844950390900240b540c66105140224840b4900c03501c0030981c4105015182c1c00500c00141c1d203240454101d039404076000f0504040600010721a88500d84c08120948a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 105831645 1250 105830395 105830401
    0x1b030c0a09051807030b0a2105010f0204061d09070203160201021903020109021e0d0305091906020d0f090501091502010e071e0803030405190c050d0b0103050c01030e0d050903011103 80
    0x1030003503c90ba1089050750740c01d1140501031024445402d406000c1c0800c80c0d641c9960891001e042c5d1859041c1481c00746c0000b0078100c2c03131b5034114000c80c1e1154210000055540b0004000110034015403095010700341c42c007a140e0710b0040c5009459000300031700c0040703000c1000e106005582c03007001002e080580d0300b01486240507280c42c01034020500000100c3c000d044031a20b4181303140030400000380100d03024003001030f208181c0c0d408aa6030b501089070107501142d50202440c9084489905102502080d00280200a14104080c207140610180701d41040200001030011340d030700607080c0086a0100d01d44030300c20340c109041640504903c03010010244100f040000700d000d03081c014107a00300800028443c0e000c6d1034a0103946c4074442103801800c0c0d80d000c0b841c84038294140214034240e480c040c52522417000d4440c0000790303442d00d031400280d46001c83d55006000f400f009100e4455440c109080410511060001c050b85503103901d2000818058007041d030311600d403402c2d04401e030071608004449a82c9d103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 105832895 1250 105831645 105831679
    0x303011a0708031005031902090a0b1c03020609060a06030f151407020606011101090f02120703060603050309040b0405060a1511010608030a09080307030e100519080a051b030c0a0905 80
    0x74101303100d410300c87e21541c282032046002540340c00045c03070b030041c0070b800c15541d4a88050300546105403903250003c10b205d00c2c07080c1000340c10011581d568031030350250034075061444840e03140c108054010a801440c110301007001814240c1640e294036401401804000410144a4010100c2c1d802142c0d4603407035101048040c0e40d001c107042d03215250076241c10b010b00e600200e699003200c00150380200101512401403001d860601c5a104090010300100c03154180c5039500d00050702c04580c0304881c0c81c1c1c0045411a503921303142c01012440c240c00c0e00c0400880c40e03c1c0c070000d04114441c6c4103c907683c3e180c1400e4030b40c145119040500003460300c00000d001032070780c481a0399580d034040ca0303505000451180c004100c01c0008421542001d401d6901e14268090700320400c1034032214400098140541003020358040020085480c124001b2512409114640001d9040960b24014400c2c008896500b40d400d00c4101c04500b60303a04482c0c1d0f40492038444584c9e1030709481b8603507690081d603402807428030300701c0c602 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 105834145 1250 105832895 105832921
    0x5040b01030b01080706120f06150503010e01170a0b041103010c05070605011d0c09130c08040506010506030702120919080304060210020316211104050103110c0303011a070803 77
    0xa0b8816030400d205680d841844a4444040d40200c03c0060104401003d1080003508501070800202c40d0000b00030341d450b00c048001d881409644804900040010055006408120b41c01041422404100c10441d00c0040b501c92402000c01010030392000f0106003032001d240000882c615000e0b000f00848020407070041c0198100e4001103417101d080100201c2c148011604640200c48035075024171461321100351100c4950000325a00c2d401c483c00410031761203005a801090042d90080d118608a420030303084c0703035050100c141c010a00987d4200148010340c2d500003a016000b0011611003a110580e45000a440743d01c0240084d03002070310b6a0b00862011030110040045a40d01d4003162220b2410700b01000a83c00120794904034400d10349280804103010350004100032031040e0a00e00d01e20507007002c00b0100c03030702943c8036a15210701050500440d43c05100703521030a00e002d450700741400f84a44000d130307072440140240c10203144452240000c448187c1c0a0b139200396441500651640752000c801111 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 105835395 1250 105834145 105834149
    0x807080a0b09090312090703032a0803010f0510080105010e01140c15071b0305070b0901020d05190c0e09061c0f0501091a06010225050612070f1b030806120105040b01 73
    0x171001c100d40c0400c0074507000150004c11290b160301c0c1c00c0340f0000318550a000e460a1420045291150400b8a10009002030f000b5070107030608070703200c8061038288014840110f034101080301c00d02146a0040c0000d1f80c2042d030780c1511400074a00111080c402c25001580c9001d01980d11196108500c88200c041d0301300d080c0f0070300c200503d079100340802411019800d00c0360510035015020034000c000fa440405c48000400b6031045444001501c0c01140c0038441040703c901701c40090304d00340300240c000d0300c0544038081c1010000003464490309617040580000c443e8200509051300c26000c95680b510080e1080107800704842d00144e682180e00600e061050103001d2100044a03445c00c5500706400240c0003a00260043c101a80241a602604441c10101e04080b091000319040003490000e0580d44040c0204803202800d1034a4a990a2041014040364040050b04051042e0510181c0c7d44118481d0140c0300c0a400d460110415241c0c1c4022861000103075908107155402d00c010401400710000c00241 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 105836645 1250 105835395 105835417
    0x120e24040201270501050310081c02071a16060902130605100914040c020c270106030204030201170a0605060705010218010e0a0509060f031c1e0807080a0b090903 71
    0x1c0542070100c021808480e401c50070001404070008113005a5200c1c1d80a5a80300c88a40c040521803a00d40201c103140c0340c040d155001c030201e80191b40340c240761340c148200c000914010008840045421085442d9401040d280041d116402e620b6401400000e404c0707030403600c0d00503001c9442c00500030050000b5180f207010342c50291a0ba49003520185100d03030103140443e290755651900c000c0e40314040002500e0505030b07120452080d040501c91701e13969000004c45403224521114035460b541142d200d04c440e0140e000301c061502c14030080003d030743c228103140c42c1c0c101410450185030391030b03242000081541d07402150b001000401c0c4201009030560040c03050a0142072258040c0240c0c00044600c0c80b041514240c005144110400107400d02ea415590440c100034590b51038041c400c00030a14201c08005030811304000b54440c252020782000f00c1c01c0444e0809200f1461900107600c01604109020305041c040001c00c034001140b0940580c060500032800514984030340c10000d8459030703640c100302040e039 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 105837895 1250 105836645 105836657
    0x8070e06032410060e090408070c031203090501050a11040b1c050a14060906010e0d1e0b01170c060708180a08070f120b040201080603031b0a0b060301020a120e24040201 74
    0x46284c0340104456413128000500070b00481e0344039941e50b02d9903000168100c0302400d00a401000241d09050315543c111380c3c0e40d42c00175490605081c00f0b801d40d4030150801761180d1520807107071440950581103d05480c841103000d651010401d40c4400302410b0314110b484c03298034040600034032815541041b800f0420303085d000714651b141c0004001d80b004083d20072034003051151040c030300d4601f44140c401c0c801c28092040c20b4030300c00c1000c18211080c041e01404460f0503070480d0040c000c1d0100206040c0c06a01007400401e0b500304481c001c01c0d5607111f0000e0151017020b001c1003840b045800f0340380440c11000050024246140d42d0700c070280c2d403002d880c050400142441400401c090100394a10038840b80c010141c1c03003103a2100d17001950658000f920450f09030100f0400c0200d030300c1c007582030940038480040040811a600b41417942c42a0806800d540c401c1c1d00410081c140e82d40c0c800e40c0c203194581d0010300007070b449600185280c6400100650320020514030400481d61200006500b4403c60007070300c902d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 105839145 1250 105837895 105837899
    0x305120c03010513020309071503020c03160210050304050a060b0a05030a0b07140703020304051c080c060a0c1e030c02071503020c010c09050303040e070507060501032a08070e06032410 81
    0x44d000d90000b200d61001a5010880803c07000f007403048240058401c90030010701d4600700c890301904581c06140001c134184001c150200c00c5041c542c005480054203032521a046040950b100c5032161108074024103c02c0c0c481100500350342d01c030789904004000c020219015080145042e00e1100401c40c0c81a012540c406d80040b11450f001080380c80d610b0385640510b14190405040120404e440300c3d890710780001c40d1405c00c0008054800030b01100b00188000d04c010310b40300c01c000c8162107020fa481030401206540622101c8421180780c3d800d0003041c1400314148200d07004c01c078036042d40c59020380b0800081002c162502034059001380b03600d9101000a00550440c4c4e2010f44407010b0510840d505070307004110800501e0880801e05d030300301880d4079040e8501259521b03054244d4000780c10507102004118104c0a070810080618005d0880b03480b0101d100c189000c000a03110035a6200381c1d80c1e00c4a4100004241c0e0344e0a20042025030341070003c16240c121a058031855000342100c076030740008600080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 105840395 1250 105839145 105839179
    0x20a0b0f0c090108041511071506030f020405060d08031e100f0605280e1c0b070309020301020714010b01021e0613061b02010b24030f040305120c030105 67
    0x3140d80325018441c0030a2401d07810000449901d000140251158809400d032505402040d02941c80390490040620381c45a4050904100d1610703565a1500d2407490154200300103100d5040d0784601d5074045800043d244d44401c04075001040805004056540c008200219420745a110314100c141c0039014101c02d65440c3c400c00710626550165041c901000e41d030400420380300340001c00800700d0040c1340252412080d21000c0c1c90021452410300480c18415407102030b0308003404610308041c0241c0b210381941d085500e5041000d4400340c02c0c0030030503844540401c19900e09404880141742c0c0640031031001001c0f0200c040c000d024440034030b8014044c403250440b0b12051440400c0185200d08081c14064440e20005004c0d0040600c0440c0d509807141c0800c680f04014043c41c8003052020340000c11464080d00422801d48a11400040c010980408107403110300a002501d43c0400c0d09034050007107850b02d0605503080c3c0150390f031403042a80f02c2020000b6440480300510f04076801620220030450420703503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 105841645 1250 105840395 105840421
    0x120b03010b03120a1103030907032d11150d050f0603030a0504090903090503010f0b01020f031201030611160809130209090f100801110c0c060313081810020a0b 70
    0xc03406505034401c0010461000300f9500034a0002d10905080402c240107030115030031034204680306100c58204660400c140902c1800d4414003402c041e00401013401030018100c14011a07500c050300b0700c400e403c0080901c2e1100b050059005d1710122003903480710070a00d400006440c084400440c0c1682a20201e00c0c0760600000b5500189103a803100b5040c68140b9400e00010001104150308124000000090750f490a200e48074082c42e44e080301040d1041c80c400068a481c891000c10003940c2d1040000d051030401410a0505490b40300720081110000f40399030808501a810503e4401c14402e2031800800020b50002c1500840940f001e607030212500164404034003c84078a650800510070004803042d01c40d1104c0c69121001c03c2c0c2d4800d03155100c050040c00c44181041c41d041030032000512401140007080b103c00004d0703007200c035246180390095240200d030314042d030020702c0c0d240e020584804051030010021600c0c003018106d0040e40782a000020350b102400002a0750394138080380480e1021102203 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 105842895 1250 105841645 105841661
    0x2102060606030f060a0506070b16050a0504060815040c02071a1e0a020111031f091505130905010c0807080a0902010914040207120206070210050f0402060c030c0d120b0301 75
    0x9101d2811a91059a0032424a43c010b0415510404114022038599a0000a00710715401211410428585120300ca44001c0ca01981101480fa040c03111140580d481002c85082d90a00e140003102612480354001041505140c41d962150400314014115540000d000b0222100081d1040c80f5031410214261144280e40c0304c400c42c000403240840359050781000409a0700024070000a810f80503078820f00481e0400d070342d503150030403400120710020102485844080c00107407004104200580004030300b81102c5124041c001d09440205041c044015800015816048402800844010b0400420219040318003201217008180820151011880307280092503042c3c4907001c3d05801c161001d05082c80307241ca1242d0242d0200019000248131030b00d118400501c1d40c0080507541080e110183c01d100703c0c40003c145030b41c688000c1001c0200840385003904160166100e80c9e442243d1404e1900f14890200c07075103e24460742c100301d0071490384100c030420b001c0e0755080e040050030108403c2500ba601c0503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 105844145 1250 105842895 105842899
    0x30c05070b04030c141b09090304030303110403080d0c11010902090c03060d080f0702030d1d06030a09120e03100204081b0a03020a09020c060a2309010b0a0321020606 73
    0x40c006000060410700c85150041e000e400c24032442040c60340c680200c10310040d0089115080140c03480000d001140c0c0400222004850f040c4161400821065503801244006800c040d11a2901000c0c030110344c3c1160301860b04264000c4c3c0e940724448804000e01888514100024603120000c4201ca006101d840d80c0c45500070041c900c2074540d1075413203000350805041190300c201d103482043c0004860707900030000841401c108946522850040505141b0069080c8041c030a001444401400d00d03e00c031100d8040041703441c0c58603038640c52a12001001e0149004013a010b115450181c140d400810100c907009084089483c200b0b90705580209a000c1c0d8861016154000b030719071072404c518500500180f841c0644607544151341c0e500001c13a5030340545e00440300181d00080d480340a1905000c6660700c032020342070030f02c41e0b0a403c000c2ca861036105600002d505200d403c0104540d00f13000c1d0482207841a00030b0044d10b02c01d4403810150b0744c070440e641203200c250840e0304005602e14008100c1511071000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 105845395 1250 105844145 105844147
    0x603072103030b03030903011e0506091303120216141002180906030114010e01030b090a02011b0515190608070e04140c092d04120309060905030408010912030c05 71
    0x5075500398098202084a00d9043c0803d0000340800d450910030500b402c210107071298980c2c5030412003401100c038040d103490f004e030003814104000b00d00c00022004415505142038210003044184200007070040e0011208142070204116050001d100030004180320b6180030385d200c44981d03030303214000c80c840c0d064948904591600700b11507610303149a01c41c1d4003400203070010540c1441c903407100c00c0d509801d0f04461444100f40005006009180c0c0ca40d0307600001403c0104841101d50f000a829184406014400040c83ca40803030100001072000b104900601d401d500c81b90704141d0b44d44000440540503818016141c01400078009200161242c1114140044943d03070b511107465003100c8420340c2c1743d954503074491a00310204549810504601c01c0c002c169110214000d52a081440c240d1404280700304075180e00c00740300115001003e4800002000d080c0041c0d52041d624029015000340b200192150001190014540c84190009060386200b0740146025480d0f0388800c4c0c0840d0b025080b205c0c00140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 105846645 1250 105845395 105845459
    0x611161202030a02060d0c14040501050f0d0e010c09081626070b030c070309060c0b150409020307080114060a0e040201030c03060905190501060509010507060b06041508060307 77
    0x104205440080e03001400b0764445030060780100f0070980c0700d1041903e00590350314456120b15400ba0066203065498581580f800b0300c1c2000080c0341d4003c68240060546001440c80811292035010b82c441d0030b01b200c0240403010b09404040c0c940d01181c481e0042c00e004280c004a214103400f4202826546101c07007d44142400c4d6070f100c6406190012481c69500c80c0d600042002641c00e8003451040b43d40d03040560392550f0528008142d07401ca83d0240003480102c110903800180d1501840b0340c8981c901c1d0104c040000e02000241c041c12074490083e406008940c000b18140c0010340020480b01c404002181c5503494440500c034000c1c0091003921819202c0001060040d0b12075040380b06032301c1e4189804284581c4520185040312000c0c3d078440441d6007010107501d624403544c09843d006201905085040500303c8001070014030480ca401841d4950311b0800c1c408903038407481139a015000e07158100781030840c0400040c01900f000e4030340c41d100c0d10441d10700007880190b00501185c000d0307000781052034141c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 105847895 1250 105846645 105846659
    0x9030315050604290702030a0f050c01030524010504090f090209090609030a03091b0605070309091a0112090602070804210201140904060b210c03070e010c03021213061116 75
    0x1c11911213804002810050300c000341c1e40800454003042d0080b111113081072024600f09140403000f410382c6051608110400c42d07150f506c9640010f040342d182101039440080000101c41c90f10464100000c16440d240e0080c216a026612002899100390b40c46103a07602c40203045641c0307200442c1c013400507034410005600d0b8107100750018041c280c402d6001c11601d00858009031121402504214001080803071350000303060380b200c19000100183c2e1420004000386555107040d1200c5c14a1003070500141400302a11035441d984240c807a04e4004c2411922201c2a1500700000c2d8010700c28000c80001446211440100c840081102035a050710742c9410b403043d0010303594158004d49640c0c0d610031760764440050784604000090085484a4511142e5041c00303040002c410107014104030318444040c020820400c0e0403004074004803009007030144004205e031400300d01e400c01c81e413448114081c2c0880c09501c450003c41142c02034900c141c49804281d4903c240ca01c5e0f0302c150203503110444010420f0100800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 105849145 1250 105847895 105847949
    0x905090a0b06310f0c030b150c0a0507080d021605130902030109050d030b0102010c0305220516060c0c05030313030803090f0f030703080f010305101e09030315050604 73
    0x5100d14182c01602c405008681c454251040303d03102c101900c50042c10381e080c15512500d00c0025840c1810485030803100e01182e000d000c210001c00c11100f00140900d030400e400c0148240346a40a0100d40c111a1618005038480c8462407a20000d80304954000d410660f5802c1c0c04c2080d1030005d89281c3340c68505118210140c49200c6007641c055607900c640c103000c100c2c01e1154885540c180e032404504201504002070031542c00741460b204052901e000e2103040d007840b400303c4640e0607900d02d044000c0c485a0070101c2c1003803c80c10340441b55080745030000640e141c01204031000680150125020255a2014180c492184e1030003810701210020341800000c60382000b0b1500000200111200303102a40a02440e120191a8940695001207501801c141d80300c80101d03484030a1000008081d495076039021356603a0100950849030b52200c100780c5200c1040c001080203150040428803400300207080180040481c00035600042007070800200c0c213802e200c001c8030225061200ba40c2c4600b0a42500d450b41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 105850395 1250 105849145 105849169
    0x5190614130902070b0f1005010203030f0a0e07061214131b09060608100f0302011e03090804030f050d140a0e030c0603012303010510140a0b03010902040905090a0b06 73
    0x1c05040d00d00410000700c40c0c0301602c0c06910505090f03a580c204940204600140100600075004800109021b5642c0c04030079070f5002408840c61200640701c00741000c002d00001c141011251040d00b100040b00f90b800000d09600c0b10020404105c004050f00400214090403100300300d11500d0350034000c001030006400d002060945a0341c2503c150707100e1010100b501c2469201000003181241070143c10b80d2050142ea0041884115445c82c65155a0000e0900c0d00301d11124070342840c598802e00900d40c042d40010a6990303100d542942c1d05c648925080c4801ea104500944072481620902d0007401c1c0a0909103450411420301c941c00c10140200c01c480c4204000203141c0c150160310445810b13a207540e000740d03019201c0b07102ca05c1d01102e080c11900c0010704001c0c02c12442070307052100380182c60586403c8841a1345076038001c03a10007424980440d0060682d40c3c046040039000000002c0c2c07401c083d50140c0280ca0060b6420700c25612505200c83da0b80050100140c14109580e003c18810f240001c12211 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 105851645 1250 105850395 105850417
    0x13030503060103111b07290f0f07080c0609010e19030905030a0302031e03130602030603011e0506040e0f0615150408070e07170f0a0e030d0605190614 66
    0x40c000d03498681c1452640c0241704d1401c0c07000101d1a090141e80d00a001c0803014180c251042c6a00d010840281503a080a0710303010124014001410035450f00840102c0f080444000c0d1880e40d42c03070315864414810342c0308070714444281c088d010100380f501c041070048115000b480c100400c031441c40c0a0021181a47d900300850521620400000351030314203010743d1a025029030050740d103c0d65071b03c09607880054a00e00780080d0040810030807a0204410359503600c0c06400840058581e42d075200428010310100030f1101074009095035400c1103241ca600b016106507420340e0103101c881d40e00030034642c0e24040403c041281c0d1b0001c00000d6072030250181940000140140301f01c0c101d151440b500c4038142d00c6900000856040340030244807104c5580c100301d0b00036565240506424a05003060102d03031001034a084090b80c080800b20714040e035107811000502150206480e51a05150400c10080c4800d1003a14012503407001540c6420315105060001c59003d0b1301d40300000840c1c4141c900301680000c0c0790358 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 105852895 1250 105851645 105851651
    0x106050d02090a0e07020f070b04060f0c05100b030f030f0706020a02010b060705031905030712111c0603060506030303070503040303180b070509040f0e030d27050706030c020613030503060103 84
    0x81d000307a0b10422080004c2403640038810103410115030080c1040865540420035030f000b0b200c01c102e820800000c03a02101d07140d1074200e0048580c2c520848101070742100c098201c1c45010031107000a241503005007000f403822021034000e06a1190460f48134000d011207442011001c0c804400420b2180e0000c01c3c10b02028400011140f125000081d01c0ba006604280c130355610208004082c845d020004a048887d03a00380300341945000c0400a0030b03d03204c200200aa507807200041121560074509032410000a14200742400008180301001000d8501c803c1e209142440c0c081000e0f802c2c0401141e00503441541e405146550b81e0710258043c0810480d004001d08000b5030800124580349100c5014814a0b900c6a903501002010881078503050310480100c149003031030300171102000100b02c888601040c000481c0c42c00c0d0003e03450805d8001861004020000482c0c075204002c1d0104048007580c0f1151070400c0181a4404203c0e619002150b54610b0900003502c3e48000c640500040d40c1d01420525002c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 105854145 1250 105852895 105852907
    0xd0b0402060409140f0a0519020d0605060d0e07140d021207090207060504020405070e0109210602180109090b24090a03230102120f19060305070302130902090106050d02 74
    0x40b040301c0c0c1c6070f280c0354801130a09080c4440f0044880c0d2103500403a10040921107401c207a100b4501003410a000d40803000d90025000e68590350035089400100001406280c544440f648008090045501c0c26080750180e1600402c0b50080c11988221005006e0051000ea1525900f88900c51900e070319149844d2080c01e80c005008800c07400245043c1e44680804191401c1501c1440240d40c000303803658060248683c207110059034440c010804580302081c1e2040120f414060690100c2c681c024054411800020525040510901c21101c0800b00382d07240440c45a90304107510442d24140c6400750b0001881c1c1c000c00d442803160400c5021001200000352800414800050030100f442e802118901d45000d8403405c03120b15036030b454001448085c029880c0007586000684081001819510064024000306594034201d0406915600c0044400c001c0c0c9512410400c1c1d03180c01070300c0100d11039000c13204215642c004a0080200c5136078040c19000090342440b070305480b507070880e84020300416030074401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 105855395 1250 105854145 105854159
    0x901020304090f0906051608061315080a1a010f090f0225110d0c0e040f170d05150102030304150b040c03020702030c040b0306150321031f050d0b04020604 68
    0x34101c2c44101404001550405071401710160b440007409013210300740ca200500a1545c1100b480c40d40580c04480011090304240703100d100400c54400108900a9183c0022074210700008030094040c1c02402003c844100105903000440400d00414444050000003040000719a4005140e081e40d40c02c2d015082c01c0481d2030b159500e281e898100129900100d408605200940e0501b4a102d8821b8403503071060301703a035105c0e8961103441e4031608443d407890200050920280000340403680b94814651401c4002940174100c2135000403280310303031161038034020039414001c2e50300b040940c10040c1c01560440d40d03582c03150080c03100c1c60030300080c00940715010b22001f0ba40b02d1080c84442602c0b43c40060300c44960340149460302000c4009607000d54074000540100307940000b1010341c00516582c0b4144a40303881d10119080030b031808844000041c00d9500c514030044e1031400745118484080140c40717420300c2c003040a10100703002d1046a401010304d102d030401107040b680e10075038000e00143c0310a00e8070b503031821 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 105856645 1250 105855395 105855401
    0x30c02010212090102070b010b041a070c05030d0c050c010903021e03010f0c0903030206060a0e1b070204060f18050f01150c1e0b09060f0a0209040b03011a030d090b0f090102030409 79
    0x2c3ca50403141d5000481404000c2c891041a0140120400742820b05081c4591a144807404c28120502c5138030115581d0100a80030f1006c2c806800d000e800e48040c880c2181019184c03030b01d030060489460050148010155204501c0310703084030303001002054200c0b03051011038030344940c0c000b52a8140d500c901030380d428001c05014003103000d042581c451391000d1650600904024019204c544618405141048495001401160080f901076007001015002d10180039152103801e1000713400c036051420000701c803040d150580c0c048400c8032082d500000b0b045140c00c0100c1d0304c1102d900344121342110050224030240d04400c4039502e0b050030400f1a55410740c032078104100d03008601503d50700402c4140c0d4100082d110100750000698002406641482c025490701d04000138680d51140c1d501041c54616503a413a044400d2082e0701800800243c2260341e41c6d400031303841c0424418028130070301400301ca400384100340c41800c98103a142c1250410800c01c02562240c5c1c8502800c0341140300c284070100d4031011900c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 105857895 1250 105856645 105856651
    0x105031816030503040f06020105090a02060307182702070201080711030714010c11070e0412030b04090302010509011a030613080c060106020105240108070809030d1107020a08010e030a030c02010212 87
    0x940110386440c50f00e0511106d0f1052500903504590400050006482000034804d01407541110142d85030381e21000120b2704a081c0210070203101c000b143d00025201d4074108100444e01c05003c0050740090428000e0301a4410020b0090024400b03200041c1100d1090100407a644984001e84e0314009154403102d44400701d014030320840b80d564022550455401c08101f0040700d4220b005000c0a0380b0780740510100610007800070f041c9400c50780712511400e209510004072030f000204104608840c906009000b0502180c000e0010f62900190120352180450000020b000060040455a44bc4885061003000c0d9210898585009205690f003401d400e00c6094003074401640000b90a1070031000461610301d5128440451600300398040507943d83c8100c03616440105401c205401d6281d00445500c4c511a40d10031a02d21031900203c11600889940104400c41c02150303641c0c042603c4000720741c00c840c294007d03280306e41e00070041e5011681c040e0f0040032821580f4000117040508440500d10854000c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 105859145 1250 105857895 105857903
    0xf090c19090c08060102030706050a0225030e0618060c0a0803040308041a01030804050f011101060f0f1d01030233120a0605030c010c05010219210b010503181603 71
    0x203002450301c52191a90041d07040c500000d090800c2c40c0040e48034455450003506c5240c030380002603407014081d0104c603000b8041c12840d0810018220503402138108046044000800360005801286000701c1603c2071628900c034042d40082c060010080d00c0c0e800740510240501032800403002042da0080a5480340c2c4c041d4031008258581460005100c2c90087c09101040403a00e005002003040381c025502550402e1b280c22a00d0b183d0500141e60091f03001ca201c42042d820130394007051803007004001da42200e194260702c00915440c0c032101002c0d040321003020312100c0703500c3d0010005841d0800d041ca10303182c00c5200030040c480c042d0845809100b8200c01840311000300040720804480325144c4030b940410480d1040000d9401c000004c0d4462080020181c100000b6401e6201401800e44c100c54014500e240c000710b41040404014094807201c91030001e6403a00304116000807062400340d00b02d0000140c7d2482e1441d590180944011220074480c403660b4820040c114000030400d141a074051406 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 105860395 1250 105859145 105859189
    0x6030f0b150a020601090203040f03030b0310110409060b07210c080c060106080c07260c03030a0c02010b060309031c06030206031807050117180c060d0603030801120b0f090c 76
    0x40c8003c0d2800c601a07100303044c910b204008000104002c407040c912076580c180740210701c13a200b51001919140c418400440118a80311004200c50700040003082101d4000c9004d0103c650f441000a074140910b00c03015000c03500c60882c03806c001d1400107000c5003400a900b0002c0000302607488445143e0084a0321106590000b00144103554004854541c13117000900d103145014207660320300c454241c417081c0b1003800d604211498050f0100d144c0c1618040b90251080300c2d100d18014031a07402070260320321120055441c0a800500a050440440c1d00c00d41000000314604102100c1c0d08070000310305801041d850341e03034034000320061381d03440001c0d4007a40b180e113a014403c443c4c0354281c5041c44119030103a810f0201d08100800301041031000640d000511102c0714071070364030a4280d24103100035007905690003400050704410101440d80400c1c00c0d80d0080c0d4404d08070342e8903410b0f0000150000c40002c0c01071050200002c810394047c040b03440e803002280090300c1d010744002c0d0120304403550485202c407034200d03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 105861645 1250 105860395 105860407
    0xf120403020c0a05100e150c0c0906040501030309060509060f0403060207020a090c12090804030c0b0c0f0d0813141029011e110a06020307110601060906030f0b15 71
    0x903041001d68524802118080f4095260500284500040d41d108400303000100c24a0b111031307651140015000d0000400c65559000c0b00940c190f241c902140c00c081c403031443ca001184480c24244560343c16260b02d902e418441c0d508049081c0c0309038000030552039100c00201320039040d0542d01c90141000714820310340562a6445d6104101519220303070003580b2094500100e0000d01544581c0c0100920502e032030000b40012503003090b0450344030b01d030405003030300081c40d8001a00320010700080c1000d1104400b902c2066480842083c1c032a4001c642040010701400d001c113428805015503104110301c01c0c84103911b40017a010004c1d007446018031101d41c0103540c0c0c680c0005203101100001801c00c4001214102c0c125805002030105503007080b040306080710303040750700080f0340c00368070203248c04440345080702d840040b14503240c0c010b580111890000212200c4031001c2400c0000345450580324291180c05125003400001c4004182e56060100c155495144401580c1c403558005602508640d00e09a5204 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 105862895 1250 105861645 105861647
    0xa060e01020c0d080306041503020406030308040b070c030e090702030c06270c03060406020c1002030c0a170f07050a02190c060206090304060512040309150e010f210e030f120403 78
    0x19070000b809070040c01901081d10008081c01d0403030758060800c0701e0010300090401040b210721003040c3c00094010345407200110038190000686e5205038400c030160380d00390b070b1503101c103d0ba04031000d40020301040c0f0071613a000c8a403070102000c680c4085544101d900304007144017610b2601070309452206e1302411500c0d02c0840e82801071703682580c0c00024001001c015200741d02107030362481c1c02403018000e6a404607081c0c1490005001022030800110001e545900b090b0410942c954044a2260b0200758801d8605171100f14412a06115081c1010180c810b030b913500301c099803950710402c0783c01c085025502030881110b95146a004605001b500c1b01c0d02c0c603d041c4000646440d00190103180036a2091004011255214007101e011807480318004000f40c4440c50b0070703218907842d0307000160301e00150852002c002c0d60201d0061803801090b40c0e40c401d84d03054010140c0e0054110007110444509142420440503d2034120340040c591b00411070b0320303061481c41e40c040550009505101074484000510040c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 105864145 1250 105862895 105862903
    0x70303150906061e02010207050f070509130201050a030c030e3408030a050706020d020a1206140f1c020d0b09010b0a0b040e1e09010f110307021e0703020a060e0102 72
    0x58125114200a280d080c00805080380180920300d016502c4c880f400b00034028800e40603119032541c84412260711840e50740308241c0741c20413070142c5030161103400001890400360301e035905202601a143c0318580319a029045001d00756000d101c4090548402000c03207030b40404c101c40e161414000341d03200c02c04480301201d09102c1003100f12820481c180c0f11004d00035210044102ca8031010b1906160b580c3d8402841e000c00070b40101c940c0012041c0c07003c12241c811940100258551848190080000c149c45006855071030045803180d87e04203d00120900c8035040150700d803494814210840079159016a0006404e12913841e81102d00d14800c000340561400e0034091201040021a000011541405010102801141302c0c0c10b043c45040c2001c100340c8414000034420700d50140da0358402c02e1030400790301d40c045c0ca802040d00007880c0c60000f480c031030040d10200303690103075075154083d041d02da081c010600b034850503c04840005c0d00030b040c80000144c0e100c991110041245844500e00d0305003210000e410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 105865395 1250 105864145 105864149
    0x50f0c130b01020601050d0512040608091e030405060f0408010c020d09080105060616030e03010e03040510181202120105150a1e06080a09140a02091b0301030803040809030307030315 80
    0x903041ca2609411680c012600d2810b40750240c42d40c9403507402c10704100340340010410044500040004000c01d900b94800030851040b0303280011202044101c4a40d15602102c41031917004540060000340200c0ca8040b000b840d66041c030400d51410903440c0d0010b1800c44000080e1840940d009802c1d151645420482010003402600000c00192601d070300890507520502c1c42e450510288241d280f01010300901001d80e82c0701e80078000b00002d40c00c0018003583c0b5441402100d103e400481d02a014041c4140900150110241c00420100d89030001d80015400f0021007281d10a403007540b0001085400d03c18580310300d01070100002c0f12040c510601290602a403c8000e4000c2c1c2428018040310700141d01c182128211b207041855691120581001402c80030340041c01650b000c0440300408800140011069000b115180c1030303034440e000122410303a00c4202c4507201c2e21080c0b0040000c50440006164054001d0880d686803001982c00642141c4c0710003000c90100f95900087c601800e00c1d0000d00380 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 105866645 1250 105865395 105865429
    0x40f0303140301060206130609140610090e0a0f11060a230307020d081b0703080406110304020102150402010201090611030f060603061c05070b0403081c0c09030605040f050f0c 77
    0x442c650416100a485004c001c0a480250078074030a460304021869002100c10f07500840c221a40004c4040f0054030349205640c44450008040c80c041a0791515125442e441c0304908010300142500d43c1d5082d4482005c1407041e078808070500706071380c0070303856402c020311406206a0324411003000b82c1281243c01d1040380132440c403002d82401000007140c1c0002e540b2428102d1402c2071685035884c042c0141b541e030a4100088081503001c80c62100b0543c01130f44160160388104028040b031464000d8003005070000312400303030059002c800312600d01032030340707009580080c018400441c142d0225190407082c1c072900c60040c8000d201c0002004803107100480e850350420380c00c4a4462440c282000000c0007068441e91014801007552406000c105041024000604c040e8044070344a0b56a8106072846402c0a82c0103004004445004081015a0300c2a003c5060307072509e0308010035040d92983c030000d00c801401110003120480d05840410030400c401040501641c1c01030201510b02000c0c4102c0c041c0d4800300e81 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 105867895 1250 105866645 105866647
    0x30a0606020718180203031902100e0c0105030907050a060e010f030507080604020901030b0d23030c0706110a050727020f090420070b06090c12060f0a030602040f030314 74
    0x10141d02806803981c0b008102c0f145001c80e080800d00404c1e111052610802589844001344030400500d03005148107560746507400ba01e00c5049403640c08030540f030025001030519002a5900c080560040c400703544c0203420a000c030392a25480d00081842d6105980181c0d0201e4a84142003000b9130780b1a281c2d01d09404c040c07409200314200108003802c03c00010305150310954001c1411003052340700360b00c5640c8415006104000b000e009007840c0c0e10700786019500720444112440c40703204480000040310140d40e1118024040ca62800d1412100703549900705950715070088032002d101082040200402914080c0c4050082141c0405004001c11841c0501c0c2e40da603006005c901420004c0c2001e8800d0800192404102c0100c02c031900d42a0760109542a98104008540c072010301c5210ae18103031107800c081d10086070303d484042c41c0300d8448c010802550041603644000a545040222910305083c2d0301400300c494240d101c0e9601d20a0360440d410011030200005401c000f45a03000c040914002003100b585 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 105869145 1250 105867895 105867899
    0x190e1302130b090d0b0406020705190b040816021f030e0d0e090c1b0f1014040f020f0402070b100902090901060302090604032301051602070311180c030a06060207 71
    0xc015240d141c0c81102c031010800b052441054640e000114221540700e00380780c000389441d190035002074003e000306644a02c50380b400c800342d0b0100809141191600f0400e0315072241d03142c0e5038180304d650092040c06842e03203480b8074220040e250b69040202945c50020100c0d2010095000242200c1005100045e20350001c90b4040e2400d4004e074202c045040251140416540d072075802d404035215041c1d902500d05401400d2100c0f001c0d022600e0b48101c2031882c2520904801d1b040c4e0481503507401b028540d07000c2c03000c030086800688400c60052040380301074254510800e40c1c8000508036004014242e80052a10082101ca00d00b401c411001400440d0021030a0801441c0455501541401200c041c154001010070442e0388000c1614010342c0d01c03000a18240e01c1001d45201441e00f01800601c9c07039820240400c0000b0768a1036901e070701440c40d034001d00c41145142c43e03200c407901145940e01e8108648050346002c00440301406c5208180070f03c0d5056603401d145c00144101d44042d4014800c5400240301 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 105870395 1250 105869145 105869167
    0xb090c030c01080c0412062007050c0f1c030c0b1906121a150301110a02060a0627020909010303030608060907150302090609180105120307110d08190e1302 68
    0xf035405036508118024070400b4145421340042950f490b5507108e90021301a02910040f02d00001c014061189060700c02c140314801c1030144001400500c41e5001d450040d404000ea000b013001007189034003d140500401c3d6007600d0b200f80d820410785180c0140048407543c4031004802e4080c00c00181010300505203c1501600c0c1c231038070075801410100d82e07500e00070003081101188601040d0b072510010000c120400b44042d07001c2c45070340003881c0700d8050700941d80003a140c20403621851080707681e00510007480c1072200e4080207a01010000002c901503090001c041c158866254680c003a600c2618001141c03400c092989141c140d000340360f0300c1070303502c013580911403c10441000d401c2c081f02e6040240e1644243d81c0066620b01403910000d0300022900e410400400110700e150707040b500155030b015540c0799102000c40c1c40340308403403001d400361201010b000700c035007841c1c44035500e840d0240100900301209a42c01c5d0240717030517035880325002800080300710031036243c0080303551070900100c0e004520381421054 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 105871645 1250 105870395 105870397
    0xc16030803060f121c0306080c130b060d05010b030402040b030a0c05011407060903080a0605010e030c1912060506010305070c030e19090c05030103060c020604080d05060d0b090c030c01080c 83
    0x15405403000c00a080d40c0750304c8041038100300c0c15609064034140300040e03403004031820068402c0800607003412000245440042441c1c03804d8075014112500201c1294100f0000d0a064082142c000000b046284c03c034001a1141a010b4241048c0040d40e9052070b0040205555002d400c043c400d4102541402c000384101224000302c403020b01f0441d0604441d0140304402d4090300300050001b500700740c50302e0101507000758a1031040c0e48100701001035a80310b2004403001c01d49403204a801da440340c1e100e2107003440c1c044005120b500205481d402825111180c034545060554412140349480e441402095a00b501034a60300c003880b4030b81641030643d01d80b0010f00041c80314480c2401000c644800b029101c04148015000d41480c050510640e0200748004250354002d101c1035a08528040c181c0c100d41e4801300d0788501a0741c2001e1101e0078002000401d500406014000c15400300005000c00d00103030480e610f480c410040d001c058820580d4240505040401140c0680c2c1040b604408114a40540e00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 105872895 1250 105871645 105871651
    0x10020d0e0c0603011403010b04020c010c030e03040f0e0c040302040c080f060913080304020315070903110d0302030a11010e010501030305040e0f0906070c0206070c0b0924160501021306050c16030803 87
    0xb017100c4100c90500c001c02c2c0140104200740d5042400014981c2a4100540015089a40550b0100261004114810b0700c0740a94019054800820402004000c100c560b52540218654801c0c0745040c0d642c1d8001401c545030742d0314070b10104130014100408131402400041d0b01040aa914000030b15100b1800a00106004170003032500c0e10100200301552401c1000380c0c641d00813c1030004060178407000240111409110881c1c0b00380305640070b201c003810b1440704002503582c15001503082c50150300003543c01e0406103500945035980c500d498a1000c41c2402118021402920344640d25410001d102d0880100100517031030140041e414032250380000a4100c0c4c0c042d56618040740c0d10b182038400154540300c3e00030040c020506491021611205100081c4016807084801d20f42190a0150740b1440c547d007210307049103d1901748900d240070030580c0f034041c0c00d80c0e01c140001403405506814100d9500401d41242c0c0002e0808a4010101501049034058248541c3c204d80050792441c1d456244070f120007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 105874145 1250 105872895 105872909
    0x9060804051e010f050405102003060409020111030f120702010b030703060c090513061d130b04031403070e010e040608030702061b07090510060c03021009031110020d0e0c060301 78
    0xa80540341440d42c0c294030908484030030312018007650400d4102540c0d00d100b00c0741030040061814400a00c904400308e20f140d24140012841401d41e9200000c00c40285592541681400070b0a80c058032400380a0006049900c08880700f5500e0b01d40103030720742203c490020f200c4010f6a152003112036095a00183c8201143c2d88241d02107480d1881e110202c880040d56400b00350041c81e4000c07042000096034020740140e0f0010040c1102c40c56240384c05240b040d40c2a6002f0b80c0110100884c4000704165031801580140282040502540c5450400825034401c81c2c010f80061000d11000d2695a401031303002215001c2250248480741c100458203440f48140607000784641000207a0b00e000c090f41003134100c10b00041000765103100da51110014041c080c2111041d404500b00ca00205c1c1b501d00400140b04866015801400780b00b43d0000c0a900a20040c107040d400d101c80b0ba800200c89100c101f0850b151610741c0744001d601d8050155640003604c030749030410103054011b001031304200c0d00c030340090f00d04407012 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 105875395 1250 105874145 105874183
    0x20d06050910090c0e07080c030106050901170405061005010201053102030703121403040b18100618051005030a150906060b0403022403060105130806160906080405 72
    0x9141d4110700d000e040605094601e4109a140401e2100969085044422109003421659034002d400c5074001400c907800c018410051005000a0b88514040c02c4c20180c181010721100078441c0304111014001c40f0101c0c1d0325408401000b0303803000d2032084207006000c20300081c00503042010f054149403600200038016900380040340c403559040400040b84058005d015100e01503120308001ca480480c8a509002181c2100315405039404c030001103030301c100e4000e5444001d03610ba82c61803003000007445a56030190b01c10710004000c0c8200c540b00388001840c4800380d083c5c0f00900070f60a41d0a03960028040b809001c070411081101c1d4401103a0544042d600030900c034071200780001204020071120030090241c81c030b010004214801114010070a5038021030b08a240000e038500ba0600020b1001c1305010241002d002055540d4001c4011300070a0020241004d0f055131541e610030703e042011241d14101804410180034400d41019080003e0802e0b4a007414080c68030f51105562030022407071101502d11 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 105876645 1250 105875395 105875401
    0x210105030d020a120309020d0b011707081b010305070c0203010f0606020d02010204140d050f0d0507140a02010207060318020909161a0301060f050c03070501060512070f180209090a09110a03020d0605 87
    0x20b10007541015127640a0040119542c540c20810320681c1d004400e5102c51060100c0071503407100008040d40341d01520420600d01121400045000c2d1030003a00b20024410b0514801006960a01074584207190200e0001007543c03400b50021314051806241c0c20542e48100b0060044461003461103031a07200a44120130101c0091038884e14107480300c2840040d900521200c0300706185d101c0c0042680e5806145c0c02c030050300744c2c04907642c1c460349142d0b0b000b805640025020010b440c025003004c0c94180b04444201e8401915030040b5585039000c81d06c55045400c940c401d62a0500b0b1920032602602c111030303000c007140044c1800100188410300442050024052040c2c012500c604115020362100009494403945180b502d140a0440c501a451052002d032074880c10200300002c8080c2215034200c1c91400340d91412100081407014900d80345030140c5c080100181c035441d41c45660b40036040d0014001030101d000d017800a040421080c42c14031660300f6440400c007590300d03d008039581940105c0300060320b40b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 105877895 1250 105876645 105876649
    0x109110306040b010509121605010305190c03020c0102070c030b010f03020904080c070f06020c090109050903041202060c03340b04080306010e0a0603090303061712030a02210105030d020a12030902 86
    0x6c080d50040f0f990244182420140301100892102c40c510039107003c001116444070019401d8072004c0307441014a1030b4016004022403010780002c003100055040051806000281150076644840415144499030030010010000c1c440700060041c00c44180701c1d103089081d64001482c00c1805400074008400214100341081410301013800181100c03c1a0b4001c140d840401a4884021900c1a8840c007600000011a2001030013151312134284a80a9460305007800006240c6640380f00090760488400d1001c0b6007001010002840f010b04081c44010540804007c0e1a1602e147d030b180d410800414041e072000007541124103e904154407241d8203440780d44040040703804004000d00550f00c641e643d0000901950940c0c00600941c3c0287e9080c8515500e82d17844165103512600c0070720ba41d030320415107141505107400c090b6800484001015140086584440003910402d440c8005000d150800400803032030208210f08046a0b680045d0680006645a0070341c900c02c2004101c041c16218500e200440d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 105879145 1250 105877895 105877897
    0x50a0305062d0a05040b06040902030d050a051209071809021005070501150b0c010b09100902031e090d09050102010b130c11030f0d060501080f07051e12040b0109110306040b0105 78
    0x314030b641c01201945066030621024190981d0305660713410b400d6000c28480c5c00d1500843c0a1030b6009001462882171703000c42107c00e1303803207440440100441402041540e0300411040c0c0c0c007416106004140380c5c2d0811b2407480290f084030140006692502d80540016112101800106040c60505075100c00090034075502400300000040011295231102141c1c420040c006000036060746e00080201c0c29080c02404000c04003550240400700300384508220000240c0c00039a03009a20720000c0ea000901200300c1ea2005d50207442103030864118400504200350b01c500800010315007413009200480ba5003000c10b00c1360703211800e03031022552900045502503004001003144035001c0300450750743d0300c020400b140e6282c00c418440e40b05d06041043c0069250f10500406c2d0103001c11040700000d13600e802c3c0040d41c0a80c0014100300403145484101d40e000036180c006062810083d50000c00d251400e4a0141d0302280c05030401032401d0314001c2c983c9085500801130325808441074038002036a01140c0010b96803 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 105880395 1250 105879145 105879211
    0x30312110c01020a08010e100f0509040813060c0302010f0b010516021c0602030103120302030115030c0e100f020c0901080c0d0503040302060f0415020a0f0222150f050a030506 77
    0x890341c00082c00d1302c0c20700ea1080b140c0d030480361401c01c3d01c083c0d6201c1d12408140420540f052805c103c2c2803120a00c600d280c25804c69820601c86c4600900c2c04101c000b8100d004c941c01d50200010500c0300c90b40704145502800741000e100040c0301d0401401c0c60712000601240103416103400f414002c89002e400319124814900318041004e41a00381c2c0d200c840c50084080e5109000c11039003060905480d01c220f0b0b02a00070750b07050381c00036020300c115403074040c80c11002800c9a0420b142004541900560242c43d0400b4801034240c06503982c0311120f0780031101038640b0203040905800351401300c0042146107404a2240d1041c1400c94150365000c00390300700a0310798040ca82000e540088005441280c1c031001d280100704581000c95800310609038000241d8645d40d07a07110250010004d030000c200149000410050045001c8034a840764401078116201258541c0308058140d140721842030140f090010051801440c00703c5e8440807103411641c030a40c82d10b001900207a4402021900c0300b0b01070004d880340c010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 105881645 1250 105880395 105880417
    0x2030412080d2007020a051203160f02040f0f05090c031f02040e07051c02030408040b1b06090106050a0f0f060509030f0f010b0f0103150b0306010302131202010212030103031211 78
    0x200700340c0f6541040d1284c3d03c5001c0c00ca110341e401200c0051b950921003411281096580e0246050199031a01c4440c5040301190850307a40680c0301400d8016600d507ca90110498a9a030014419403c04102030403600c0151001d5002c1d03100164801d20703603400140d0000401d038209402c11038000654403650190103180c1000c001c0a240d0010030800326485005410803080c034410004100300807070b02e900101c1c403007618058605881080306201a807103d400400c40c0b1005403c1c0c00c01800c0d0011051380c02e140c2c09a65000c2e140e5100c203000c000611f0711103c5c0e40c1c054005482103817200d0385007499010500c4031520504042c4540455080d002e030b5018008903003840c150205549403d00401056402482c6c42d098903071040303200340405002d40d403091140c000848803000b8090511810010081030030307080280541d0405401300212803a00e03000f01e104a00400c2d0034400da02d03070f00728170744000b9040541100d0b0040b0501ba051004101180e88100d84921382c03220400c001522000b00301e150710852262044080f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 105882895 1250 105881645 105881681
    0x221040506061809061303090e0a061a09090a09170301060203040816051804021c050f0712021e0d060518010b0301020f0f0f0d14150102030412080d 65
    0x38400e000c22110311031041154000704690661014680d035503000da442c1103190b4041d000041e19144a6020380e080726020341002d54020355200c4020704110001c42e08241e1a036151801004203140a40f40006601d402407070302420002894081841c000000342040c00064880c04150244407030071103c28070212000c4a0030b560303983c483d5800382d6603034044d1007400d04510a0007000c928100d02e441c0b440342922801407100c100d0784641c250040d2521400340040c2e82c00720810341d1806103010300d10900c15043e849074001e0030400b41020300d480d0600d500b43e8824001920142c01d00360060396404441a00c90b40c03155050b0703000c080240089549500707a4000102181e01e804117014140c0d6081d0184000e500a0000a000c84164038060601780d014014040c008800280840481c00d000840030f810085082940c079410030903608417000c25224401d0041c0c1c0101c24400170f103c1c402500044d0201442000c2c0000e41c070b810b19007a401d60f61890b205802400c0d402c8082000411515103400206034104c00711010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 105884145 1250 105882895 105882901
    0xd0501030f1406132003060112020111030405150703050c03030f2406041502101503050607170402040b0112060305011b1701061110020703090906050d0f02040221 71
    0x240c0000700120005070766046000b403403914800301c0003500764441c03201c0a02e5580d05004641e1a01c040b03030326050880b000c103080d15032000c90f991400c1103441d0080000c14400c0055502c06e00025044807030784209480030f50010401406552250080240141d444640c100d98690310b44c24100d03070078000c0400c11f2460b4040001031280c00c0c00201c620034040c0701c4403030303180e1201c0f84440e03401c0d89501000c40d41c10b03401800c240020025000120703c0710782c40e001ca50069920100c80441c0d40e408a03844103600e403540c03203554001807041c0300f804c0203141c2d0721260303905200089009004420703891481c010701c002c0c07060703464209002c0580d108009040001104550030f000e0151a4640a4040c2410b030140b442c8074031070805c100b4200361041e0090046403001c040403080310b90078894103c58019000303104120502c5480621900340405200038070103180240e0b01c200b400e40c04c00701d00400707a071410f502161103440c081e00c08030301251540355124a80e55044800595648414031900c600d1290040d50030900160a010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 105885395 1250 105884145 105884153
    0x90e1305030705030301120614061f0e030304080304030b0705031005190302060c0106090e0a0c0509090f030c06150a08100c09380423031608010e0c01081e0402060d050103 75
    0xa8542d07c43d00c01c80741441503600c810390762010007200b1a4016840420801c401e98001100c2c0460550f110051500c1030340c0d0060314021074031b076902940c1f111491b0351001508000f0b015450302203c1d003055003807619514505000c20f4103604c0524601030280b240843c450316003880341c110000040155805030000b6100e202c1d0100747ca0081c0560320522022608011300c1443c030540200b002c0151690208000c4031060402c1c007030100ca010001e03c40304a5100d042880300d40300c4810405000403508410040c040c1e440d141031481207440303400c80018003c8100c14800e102e800300100384035421880324900000d0054044400320394a240550000002c01c02d403024a015079941e1264201000c524406100b48003010109440711601c1030b40f044510800004201c00c0c12080c0d00800341c0c020110003400c60340c2e40d21418a83e03107090705241d40200e00320380d0f680340c840b084814240111003900b0f1003400d02e91483e2602568445ca03800920b94045040c6400a0001c0c007155100701c25121205d50301d80782003042e503840b0302d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 105886645 1250 105885395 105885419
    0x204050a090207330b031513110306010e0c13090c02010603020a1a03040212010212070801150801031e020111122a0703060f0e0d050a030c090e1305030705030301 71
    0x60682d0400e0000010a001441c42c1d0001c0303144c05440001c0c3d4003500b0350340020f02e00038140503049540c1400340348507007a8440c3c68445014000d44104039003503072030b41040c6400d41c07410524110f07030b03806604414010400120910705903030b4813004d00c0c0d087e07594130404100032040b001a1900400c068515025201c450958154803440549109031390080e0169121042d0548400f603810034200d0540e42080000c005050034041401605d04040016081240c2100e680100800481d07400c400640074000402c100460b0000c1d403107100d01c6506100f07116506580b202d078070401d0340c81d1200406182c0e4180100469120300a8001001c8841c01641c4d140c6590b070002000c6a030080c0fa00c11190004100c0410904003110107400d1074142c00001460040d00d1680c400000e800303518801002143c0c4c0d00c8540742003140030302403000500741e69950307a907030b40311050f0018040b10351100c1400100700345000140040364600c840f0b40c2c8c124000702c007801041500c5241480c40e603c00c145008056000c088000600041891 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 105887895 1250 105886645 105886657
    0xf06051006020a050a1e0803160912050703030f050c01020c010608070f0e06010c1104020c0d080915180102040b0f03060355050f0606030f0d120204050a0902 69
    0x1a80c864091661020200c0e40c1c0c3da41c800c00500250070050040d00003440042401c01034045035401003c60212585605200340c204980c4c04018000da11600e0007055800765100001d000c211028000401098640c1d958911242c0001410720144044890155002e001a2402140b401001b550303076289904a490280483c2d00c10b00f8420710030300300b002c41c205200130303911000e0f2240110b00d51840d0780c40703600441d02000441e4054889040e412070559168880d400100044400803004048049152900525045004007840001e4000741151800131048a60103600084502c4410007108104030b1840c0c024811580600e440303140000c0c0e003540002440c3d01851203001c04800b500c3c0301e10002e006518010382840800111100003c80014014010600d0045455040c450740e08820014400402c07402d22503076000c2c2e5480d44a0413846055030b0081001560052041d409465641300c60080b21b65502c0214060109102c2c40d00808490301416505036001440e00070448070a8591352001038000394819 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 105889145 1250 105887895 105887911
    0x312331502030918070c0204060602030705070f1a0903010209090f0709060306030c05060c100c1d040b06040312050706110304020907090f0504180609030e0a1409040f0501090f0605 79
    0xc03050240311800803041d164a220080c04140031107441450086030382400a04003014882d0180060b005a00d8074460301d005064141c00450707445100b414038038540241355220108021800f4020b02103001040c480c0e440032030700b40c0359503034940d046000007034060300510365035541054446040049800b40048058002c0c00c40341c8807814103070b4448000301c058070f101d8040038159480b510030402950a000d0f00a160081d000700030b468034844048a408241e45201d1840d070b00041d078903a4a00c2d42c4800382410400804000c48040002d08040d401280c114040d5101c05041d0001c04c00420600502403800c8810a50340100c2c100502e884441410519400640741030b4090390b041c6002a1959004884030707800e075140b07400c140e1040e6140004010261600b41c6920343d1a0030300059220004040740648031000f0300ca5100c0d06601203440051007103d140d207501c840c4450408105644650b02e942c0407440d0042e8101002c1c09a58600f42001070140085080042001c1d40c0c00da0403000340086070344150b000b4400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 105890395 1250 105889145 105889169
    0x303010314060c070b060310050c03011806050a1e0b0a0206010608062e1214011a040e010303050702121e01050117060c070302070b0c01020a020c0607031233 69
    0x3001d04010b5036040300301d41078001e601e01001400003140d01203842d19408200101151103d003840d000740e1050304d034207440d42e00c02a10701000512423a0301c00c2d911041c036a071030307030504220980c0380c0317400188189210700c1290000601815580f100600171100c00001d07003502d1a80329501c4880c0e030340003961150244514000a6140c0740825903601c1c050b44041ca28220380b0b00342c0758030340003003100c000f1555400120308410b0100040342024108040d0181185a21107500002c68562401464506003c002410b00f9807100c03040009000da200082c00d541e066075003520340240c90f0903107031000c905105d044d40300c12001031154000000c03e5030901c40d001011041c0540084c071803642e0342c11410400703010389550f0404a07001040090160441b50010b802100c0c000c1c4100c0b000700e40d0fa11507078010ac4d070020450491594001a00c01c82e01c0341c0400091028a0058038854035100c56510003e0403000c100a0200c00c16413a4024000016000b00d842400d22046d03824211000000700500342101650788120440215 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 105891645 1250 105890395 105890423
    0x20706201506040b1002011a010f0f0f05120f04020f0316060c020f0901080307172b0e0712020f0604030201140d0e0312070e03060108070501050a0203120903030103 72
    0x5580391030000450405002050038a08101c200c034030801005040903041680c8501d140040d41d1041100320720440350fa000040d480c1b540d140a1011180400602c606101940619080d040d038041802881c039080c6140050f1039080411080381e02e8413440150b4000f14130550144480c1701040000c0c030f1700651003107911207000700d0a00289034580b0051902903001e403d5600b0200071090088568405881c4010302160a4050721703400541014000e8110500660000c2112410030100111110b090024016180c0c10800404004003030710071044c03400003560300c0b100e1950745085010303003042d20003100041c1910708654030740f03585844002076103000740e22507242049018001c0c10301c0c0c0300b118141d94069481c19850402552504403d030700220034a894103036070340c000207030f1910140064900d070545030020010508100340e00070080d20700742881502c82d400150040002c04c1307000541000315482820441c0e140c01000383c040c0e0442c014554118052260f110130070660350004401541030b240304441d818400c030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 105892895 1250 105891645 105891677
    0x603281b0809160510090b04080303090d0201020c070614070605070f030c0e06030c03040203070e01150f030e060a0e010209040509030403031b0309030b1503100501060e01020f12030a0b0d03020706 86
    0xe01c0041c01d4280c0b0211090001c0c5c1805003013105402100d0502080386d903550020b150207a132141c2c0c00000300d03800200922004003c240b2881002c0c900c5840298101841010029240e0170319110300700030f10500d160b0714003007450f4210a0b210400c2d01f00800700b00d5890034a80c0079124840658607000001e1828120b21031180c05100079070f2200c04090041c504503a10900903c2d81544050001c3ea414898141c0c0004c0801902c903003240079140f10041c0446040384494040c3c445207550b51038005242c208458030100d1407001400c00d41c1b02c0080341c0301007510048128010700a100f640c404076042418101003100180000008000300c9200ba500e610220780032581481800c1d40c3c850f40100007914402e01040072440510403031360011203003103042159860640000b03140c504120304d407400088d03d400040000d15088074403000c9050003070001d88407091a0031806919480901d6507a036680401101007060700b80d00307502c00740711014050080080d00070542400380d41e0b8205446010300180d05801050b000c8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 105894145 1250 105892895 105892903
    0x6010e01050d0503030a02070c2c061c0b1515090a06210b031207060b0a06230705070b04030c0306050105041104060309030233150603281b0809 63
    0x21030b000005981075482c0e9900c64000384d07014239402e40c0e01c44103420300480e050103552028640000002e0003000b56401c402c07a404410380d40104214441c8a010301da11040844500440148651010b90114036a9070142442c03c0307204908003880e04403000242281c800249600101030307403581160801c81140d9030b49411161290114001d28104e9215180c109804419820200c8001030040035140d002054420903081a004044250760f80b913141e44617581242041140b0002070007440c94400702c900d00c43d00b40c1d40103002c9d1000c1d0002201d00005568003d1110034412100503090006089544c3c50340c84c02c0c403035814922400150340e11072900c4000100303854140304240620650b05503e50510340340180c150011b028008055087d030051000242c0040f0410095140c0544c6000a04810060300d003100d07460140d000309001030003412800e0b02580790351a00140c1340d012024964102c02d0710071b2503515610b9030510420607001d05050500603800240d80ac130700c2210042543c2c0da6a03010f1f907036640c0c809580e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 105895395 1250 105894145 105894169
    0x209060a1203050a03111306030e15070e04021c0e0708010504050a0201050315041b180506090402030c16050a03140702090711010b030a050a0c05190501050d1d06010e0105 75
    0x7120780c4100040003e00690192101c0e5906040014010952103400001ca900c01003010140700c115041c24400d02c2d42501c02c4100714036a0900428001d4240305005000f40c2001c0d10314030500801400d040c409554a4044440d1b00041c0740022030700401e5144144090142c103001d184040c06024804901c128051141c2880380d5000001003c060789076400550b426030001d41490f6400c55407504444082e201c48c0504035581d20701d1a035610001d1200360000b030014051194240100c2c000d05010031141d5200d406881c16200c0450340165280c54030154000140304941c2e200304800042080c17201800400b01d40380050500035103649503804d0102c9405e424510980200030340c440200b41c082088644203107540c0810341886400081c0c504204000030349020803a88080b101ca5000540640402001c1ca8010004003801e03207801904552200c41c40c054402c96000d00350400c00c1c082000c40e40c1d010320750003004c28000c0380180340742c2901035040c1d410b03160710090050b010704a511000005981c202111044a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 105896645 1250 105895395 105895409
    0x7140c06010b090f0904050a03020f01060605180105220510080105060a23040b041e03080a11031204080306040e1216050c03030a05030708070c02181008030d0204030209060a 76
    0x3656802c01c0d100001c140c004201a580103901c24030903185640720090800c1c0154001c400400500d201031400a160440ca0500b41159905000042180603000402d98483c03600b00582d04840e131807000c004071021b003e01c1c803d1080c1c805504a00007002082c021052094540c1034034926081c540614081d01c0300340c02032182540000040185846407442030540210307000500041d90000507040c6d004a816401640060143c8080020100f107000b42192403081300c905c0300100c40200511b142c40d00381d01e034001e400099041c4080304005030b003141400d008550032840020320820060900c2d04240c400368200300e40301ba0041c0c2c40c00010300e201410000310701e0280c94262200d54548115004480c0010040d1501140c11b4403601c40c074100c1d695000e0014015051850390340c9038680c40d051b18001c10103603002d808001445081603210300982c884200f20402400040c800d071165450380f081030b10140d0141c5c3d20070704507404085030071141080542c0040c02224001c4440380c69648812003040000c2c1100d21440c2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 105897895 1250 105896645 105896653
    0x30f0204020c070312050d0e010e15180616080a06030b01120807060f05040b011a07030509011107030302070807050906030705040506060706230f0f0f100513020307140c 74
    0x400146000c0c1c00410310741d002d403400e5a8100b0b41c4c0b030381c8990a403110100800c022541c0424810601000b6201c0c1a80ca0311030000280400d05c1400f4000707803a80140e401309448440c00300c0000c0c0241b4040c07081c4005001b810320454685103171114a0050381d2080c03c0c0c0c4440001c08950109030f10300950701584003600c0d001a1500e5640c2d10b0030400e0b91450b0080c0d003080300d440105020f52004108188218042c020700258042258601464a030011300d0058008045003110072040e083d440c0c0e00101030300d582a506040190741c074048100142e4240300524503900f001e129445000c001c0580c003280c42e00440c2c80e440200c0d5030a50f121020040f400701704030394150300f50340020b4081100e1720b0150000e40c1c0001d80640002e140005a4981c0419611803a9002280401d0011100d940313510034807070554041c001e024140040d0420b80400e4a20a50140070f040c1c00c1c40526000c00c80d591583e010182c02410b004090b100144120240580a500110f61002c0801ca0892100d900f0340c94800c101c03044c81002c00c0c0030f8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 105899145 1250 105897895 105897923
    0x203090606190305010f090b0702070311040f06050306041202010e01060b0d05040f0f12020d0f1e0207080703060501080f0102090a0608040309050409061415010903080913020316020f0703 82
    0x22164440030607400811041c0280700000100d0000e1151503115006150089511040d5048c050080400600582c0c00c540c40b145042010881c400c60200d0468000c481c086081c411107510007000e007800f500004d80c10302030701c003e200c10424440c001c0d00c1d00c481c0e107030000c0c0042040215603908a94181c4a40003201500b00b0000107040e0031a4441c81e845841500468841d101d40d07110701c081040c034410100d4950301d1204102c00c0d1190100401458400341d840c1600c4148400c0c0c0c4d00801c58242100d1f088100f0286810011030580240000c901902c6250110f81056550b401c00300c01503c002c1c402c05031240036078441841d1541c0117000710742104a019040192285c64008100d031003000060080c1c040140a01c004510303540d90380500304605008a07000300349503442c1c082420011601414600107103294417140d11240e6001861041101d801880140e00c030390703030000428200780d1440d1031003023a58400030030080c000790300030080b4111002d19822100b002460141c4541e80c2c2000b03000c0a48440e62040744 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 105900395 1250 105899145 105899149
    0x601090b0f070c090204060f170103020d0b0a0b061801110309090f0c0c030f04091401140d0501110a02160801060e0c0f12010b031e0103020d030f1826010203090606 72
    0x10102d06115000e4904810350380c0841100300d130461741155000a03410050400c1c8a40d00a090395405110042003242952450b1300045c3c81542100c00204840e58140c0014101c2c001035000c5142000094141540c5404402da10302d900b0f80d00c0c0c000c2601064490401d4060b4050000950310941405080c0e01d2180c0ca601c0000400080d000302103214581d401c002c045180314041c00548800e2003c0900c01c5e0301c40d400c00302040286c689510174003002c049424010484102130606015001b03400391780001c64004582007444c090140035800100b41c2c140061014005580010340b0304611000b0307054070ba400c83c0c40d0401d86080c1c0315903102d440f0900703c030480400d1890403503100620035545586d81ca145850180c401200800800b40e002030200c0c0b1000c0200b042e403042180000882c028094840c00d41581550f0002d070f031500381158003a040010305401202c01030b00070040040800741e001c2ca2850300c29643e4025842014428640542080130090102070b010014001d07070703000c0d10011010b408140d032a002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 105901645 1250 105900395 105900397
    0xb04080d03091707030302120c03040f1202160b03010602010506190303031116030e040b04020f07060b06040308030f0a11040501020c0f011202180316030305160c03060609050405060601090b0f 84
    0x24041e01c403e1500040102c0d8214100000c00c0d26520030b8a0158440403c0c0c0c1c2d085041038001040250003031410002c0000041036030781c250181036403140c0c40380c80035034800c01c0403490041070345002c4010000c20380010841100f2480518100d88a544c028000d0b6074400c1c0501c10301611081400009656403001400080e000b60407046401c00c03061000c5081c401f0700b51800c0c010100094042d03010070344080380c0007070905150041e00b41548090b54154540840d40303000c60340907c07803c000541048d5440c214a0420b134bc4940c01c03200110b402c150340a0702ca04182109540382001038601c002168034005910f01603c10746401e503022544e05030003809882208205005040350310b080000c0c1008401d1030210444602480a00080e001c500030381e0004045041c14076150a1602d072040301c0c881a03009040000235030020071103000b03018042d00c20720110194174040410180c01d40005080c5030070702c4004501e9900907804140315034004e004a0703440ba1200001034a20101c1c038041c1c00155841004080c0141001d00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 105902895 1250 105901645 105901661
    0x6010516110d02100807180501050406030b0d0204020f0a09050d0b240307170f01020c0d0f03090210030504020f0f0108010501110307051204080d02010213030212030c0a06050604060b04080d03 84
    0x98000001d107100c030390000c0c400d04400500000172070003210034805566445042807420182d10303101c000d80d041c2030000203441809a44604020151112200416070300c5210007403003156809441035459900c0d1207100d040c42d401c1020b03e1000544e2564000030380d460480211401c45070005402101c039119541060146540e0401300ea0350214450744a03000c03500c041103210014000203c8c11020400c1030300907a03080480c0e0000c403000740e038010f10115400d00c002088403c08012542030125901c410107030706402510340ca03140a903000c464505008a41509a000144280d108a9100e11a81710b00c0040200d8182d41d0954103002880200052000d0b5000c1c000d803020a40b5032004032410642640c3e5a14604484204114414080400c082285240c01c1000040c4201103000070360070141400d1518015031000c1c1f101a2158440c0340d4800c0c00e1403814030450344814450780a5030b40340321160401401405050b100e403402907140501c005441e034602d4040d07606480d14a0050403207010904d50480150000c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 105904145 1250 105902895 105902899
    0xf031b0f1c032304080d14060f0f15030a0c0f050c0a0206180306011211030304140907030f05090a140109030210020d0216030c020906040501060215040602040803041404050601051611 80
    0xb09a680c0d00014407800355510492040c00c030b0b00d540d251b00550180a17110f080f10a000d0394400c41d424030199a1b104c01d80c0d00100281a19045c61500d503040c002074050300c840c581c82c148940f002040c4100c2c9550f50b040294540c5280c3c95232020b1000088045031107100b0003c001c0400e8000c0707402c100041c9050b100030516151143c039003540c10705072900040d09229080e40a0760f00c450419003240208502d1204880181408a0103541004d00d0055a51a0340b40c4109107030748034103000c2c40015400d6000303901c225444982e40b14100481e00d0448a0b030303076a900c00030301c0079103402c400c0c001c40072642d2038140503205425515901501c6192080e0035a08065002004004c0d00c2c107400303000300780301c600f1a41c6000c60098003960b100e82000d4001e00602c43c08400240240d8060303410040148078184e00000d01405001e0044800107980c0c0e150300b8200d0090081d0703000419503000009000410340c5809009541c4468200d40c1002952150b8005540742e204002c01492410b00b0b41c403280d8003280a03055100009400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 105905395 1250 105904145 105904181
    0x1a0a0f09050a06020303010f120c03080d140112020a091109010503060604090c020a0611070b0f0601020709060b0d1b23040f091b2309030f031b0f1c03 66
    0x89074001595814190001c800507030012004028104090340c0d208001c110303212109810394002d0b1141e201e010168040038012074000a01c404142c916503220500c4018070503034201140d41c4410010818680600d42684105502c81c00869020000d1080420f5202602781d15481c20510303000645158000429590f8002c0c028040064080d4660054070010041940a00b40344400ca2030b010049136020f4000203910f100500c074141c006038152070603c2c0c2107110580900420f035502c200407890f004494000103201c90502900180d141c28003030140141f07044410782800300325040400081004000500100084d040c151030300798950000804003014080703800b02c02e141c56198002500d1407906a0300060007647e0318014000c071902c04da04403d41c80c40c01840e00b040121284d403100b110000f80d400c01184103040015201e070403039904101b40703007050380150240c944039124070040b030350035100503c400103403030103106001e44207583c011a010100514a0b1038a2201180000c011401405128080c04400203 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 105906645 1250 105905395 105905399
    0xc0d030210060f06090b070305070807060e0709061805060306040308130602031006090b070c140301020730020706020601181107140c0105070c0b070501060b0706050103020102071a0a0f09 82
    0x54980502c4024041c041d0082001900d042c1c00101848059484040311407428410306001a60003812a03804540051501c1e84424144c1840c2005040d035000d0441e05101301709001070301300b50541140d0125032041d904a01c0e240d81d00507640e0180c2c0c208880aa03417640040c0c00040000e070080c80303101e4004109450414140d01c49980d10001c80c3d200b9915154010440f403c1040056403091989001e401880590360400005a03103039411206140110100c80c8614034417001282c50950681d030242e0b40001000420500005003102540707111801420400e403800405003400b4000210281111415030040c00030380e1900038132402080300031b425031000ea900c0354001c484c7c03030300041c010703100e1a80509580c412040302c1003030035072801c251252040d040c44803e0161401041241410744c0c22244075807012a5181c03414545140100003d4210382c1d00410086042d20a0180560003c2d043c0d034802c1e0221107aaa072a0741840a103660252a403038411542040081d003240d20910202c40782c5800c900b050865130b9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 105907895 1250 105906645 105906673
    0x9070219030305150109060f0822080702210a1506030b090309012c0105130504020a11010506010503010b070809010e060d1509060302100f0c06150302030c010e030c0d0302 75
    0x190160003900060303220000d008100c080d401300e502d298082402c0103941c1500d42000540400c21840404003403020f00304c001009125818040c4040b02038241a8910100983c9000034a41e0445401079005035800c003111003503401d4103032901c5d601c02c0d0710000409100360284d50300c112241d8107038010344240b51110400070015071250240390080c0c0719a0061078035504400001044000301c000703001d1a900e030020802804486140d140d000340a003e02e0007030382e6402001d035420840c24150b44825003061002030f05048095010040740301411840b002800161202c40044501d400207000b020507441c1f003080030000003052400180114030043c100080384141d80340018081d900039681d022107a076110181d5483da090440811009000c0705c2908005680c2160046444030503408030682c14054410518a0356130300408001d0015584810140b01801251030120140d0460b480102c0c028812400303203a00c0303907010709148203030418050002c1c0468070055081000e0300d205101d0560030f42c001c40e00c0700790300c403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 105909145 1250 105907895 105907933
    0x2030a170405150c1504020121060b0408071d01051003050621160f150c030219050a0308070c111509030a0803090c0114030705030a180606030605070c050c090702 71
    0xd00702d404030140d1907540000c0410306110540041c0c40d0710400e82c1c5e0401c80182c0c0c00002c2800d128003401c1d405452400901a508010718050300074039419034000c00c002400c0e100000311403040d59050208040b101c94040ca01da208000203001c8c4940c4145182c00148516202c3c2e40a0f039804a00242003505050581c400c15a490200442150440c2c0041c24000c4561004020f401d000701040003030700c3e6502c0e1078400c03c21910b00c48080040100304034014007100741842004100411183c0d0b4520218206d80c1d41360140d60342c072002900300c0100300312900140150f4020b061280ca00740d00410094500c568117004c01030115036200c1007404402e000c1c071011500741c078200940b804580c42820f54a030b403402d000e00090300c0c281c038086525040210f20101c415405200105803500000c16041190f2130b515031080c0316001c0e242d441103450040b600e4000070b8003804419040b00003100d004020030001030b2a02c05044640e030380c00b070101810030382c001807054101c2e040070b11080e540310010344160750f003c94100c3c9640001c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 105910395 1250 105909145 105909169
    0x61005150702100801031704050618181609090501061d010201020408032d07020105070f020a0314030307090b04080c13020d0501151d1e013b0d02030a170405 69
    0x40042c4c00600030462604035204100e042040300600345441c110004a0a2203072807103d007188030700b00710443c80d1a182c06454070a100280c51007205c540c641501c10003620503210001a0000c1d0984c0b2000420040a01ca5581a1951907850081181811050107a08211583c0c0c2c141150b40c20000000c0208003400030306400002000300359100070040b01d400e034041504021080032a5000c04c500c40060f03811800f01d1b80140c1d4840c00400c1c010010380001402d14180340e102034111002c80030700d40d070741d150302000451003105951511000640c8a524019481c007541c06508480d070f03c281078541e00c0c0c0c0740598241519494400e0094901703040c1c0072014060f40c1e02a07110346004440c801d44000010f410901c5950040709000c0c80140603a03145d000903040002c040085003441c44400c0b030549030f0b0b0b4400d403080c1d2200c100c0c42058070448421a64080030001885412805144501016071101d2401031090503125030018014100320764286c80c4c58200c1000b00d00c0d01800c1c542e040000117882c5c2c455451030388c5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 105911645 1250 105910395 105910397
    0xe010b04050406090e031b030d0507030b03060702010c050d020706020d180203060c07030c0f050f01050403020309040c020f03120601090807090b040b0402030402130f020708030916060206100515070210 88
    0x14456103001e0501003035070020340082c92200d08204d809011030340f0000036101440300f0110745590911f0285241401d610070240507102c120300b40020488860381540100e50100c0c4207408589a41c0c0d10b80204900700c0b0108141200010400c20035914008010340203899440c0c02800014a0103081c091404222444450800b0440c440440a1019880c003070100310382c0080c216808502e031000b10fa80061803980c007401e0042003041c1002c1850240202003003d00100303030038407008201e64201414044d42c0e98004c8440300d480380b81801c024003006031000c100502030b1f0380c03039000660900c284801e442201c0c0100034442c6040200f030b01d0740011040000c000c0785004118589000030306010040030720041d80d04003e222800b0b54010070500006840328510319844440e40000043c4103400350f500c141c003912407513002400810011040c090302d60000318034000b501c0b10a01050700a503640d0003050761608011611400c0c1c00180aa040080d4188441e111100b07806581042d403a28030960300058607280c00e051110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 105912895 1250 105911645 105911647
    0x12010f030c0e0f010603020a09050306130b0c0711090703150b070b1003030c0b04110a03080c0c03010b060304061e1e0c03020415031d0109030f0e010c0c0605130e010b 73
    0xa20032038401c107902824030902c4201d05880c0c12011215802c00600c03590042682c001500c540c102d2180002101a0a0080a90b0070790b04181c1100100d00d620010180c40c04246440840c02c0c008a40701140c0c0c1481c0d014050691941d4071808104124000900060615845440d10305d4035802200416020340120707000161038509030306244024500080101040b6010540140042038104209001c2154055a030303002c0ea075200c1c505900c50202c2008100d80100d0034a0003c02003002d40d10150201d40075140499041103c800c04150903250300c101265003040d004c001207404035409800c52250080300c1e034510510040070b800984110742e40701c000070700c1c190321454445441d070b203540c099003800401614003941014146074004400003c150486000d169403601e540003035011506119450798410002000741c81034905014100042d03000403400020302c1d00001b80143e40c0122082c1e07110540003103950520b00c1c1014419140c0d6444140004629010b08070300140e800c4803c2003d5001e40040d013209 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 105914145 1250 105912895 105912899
    0x110405090a0302070f0513020318030c0c040509060f040807060b061314030c1027060804030f05070c120302031b010e0c0307080c0103150801020408030a090b030708040303050a0212010f 81
    0x24201009074010284245c010203040105540703100d42c940001c1c60030900103940b612075500c0c040d42d40301e9080302544940004201c201a0940101f018079202e0700a48061003d5600c103000c241e02c404080790280300300782e84134012501080401d009000c4940c07250500044030000348002454541000c80e0340840104422000c1c0120b40107000c0b0a0b00300c0100b50024001d01d01320200054200b14441e00b40340030885107245407051340402c102c403003030344010350307241c3c0300c041c5480d9a401000362200311410f40103c0e141c80c08186e0300358031480407980410b0300806420400307424110341c00c806207000300b4143c5c1103100a120f00c51088119180c2920900340c944000111603e000004c503081c151144841e622039004042c0400100d400410324541154003481c001894034940d00340031442e01c2e200e4110100940c800b05000c1601540000200303a411a25110190a1581c4100c014400d01c4200c80c003071700180782c19001c900007a0082d00400c0d0040601d030380c0541070840440007000750030f0090b0710100b007110b50443d003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 105915395 1250 105914145 105914147
    0x6090204170d080402010e0d170a0806011b1203022203110102010b060403020907050c0a0c05040b06040b0904050c041a1e07021f0201090c1212020601060909020304110405090a03 78
    0x800030703007000140054951281e21810140441c000100080d0510400700b14072105070343c0d00e03140780c0d100503408405e00d4500c2803040014042504051840c3c4042004078000c91450b40c020380f40500406070203020b102c4003400c59a41c14028030b0400c0040824140c00f40803020070040c81c0d184148a9803120080c0107215451410100755501038800c4480c15a4500360081050361206011103042da071b0185c40f14205600c0f10f14003150396104503143c039035803405a241d00c44100140c1d568068211441103038184000d100c02401c020b0944071ba445690410041002906413a0816400017a0312446100810b820300b40e0300e14594505ca0703601202c2541c00e070800034400b004900c802e0a40c0c1e9020740c2c1d10741c1d0301e424a8550f038042031409404490190b0014000b24030185180c4c402d410103101e4542c045c14201e40c031603440c2103a03100c80d0215102152954030521710701c0c00c85440092518101d40c01f682c0e0320004245000541c00003544042c01c1030720304a24035030b44280251114007956000c0c10341074006041c40d42c081c0c10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 105916645 1250 105915395 105915419
    0xa090303150b1b03070f140f0d0909050604110412020108010e0c0912010e031303020907020d20160b041a030709090c030e0d08061212040b160606090204 67
    0x398298500100d800300703000519501c000da072151a02203c402e03010005028a0704d103035020b04e010060003020001948410403006a80f00051030002108070b4000d0b1031104040c40d02c0304a44c1e41c00030300042c0b004004004000c3e0b140c000540042000e800000c524502c1c43c5a20402d0303119400400786035200f00440811541d0249030350380103205410100c00315041c01210410280700d408450f51184039280c81ca00c54200083d4016620100440101ca41c0c0315100f0031101c80380002ea1000707900c18441d14000459050005c505094030020658520020b9044030b0396908149281d07610700e00c8503206c0c500a00b0b090040002c6800c02800542403540c1d00d96241130450b502e90b0300016600345540e2414002e00c60b1841d08651000155070180c1c1000c00e469108a81c100c008066075498818603210381140d030303030000307070010f00050241a050700e01c00e030369200e811703141e640c2d0340680303162b00541400800041007003030703801d8001d840e41c071402005140340da003410380329202507072999000340fa40c1c164005030030042c03044804 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 105917895 1250 105916645 105916661
    0xd020d020d0305010f140a090623060702030c010f180b1207050406020d08060d0b0f190204030b01151403010b0301080705010c050a02010c020f041d01050a0e03070f0303020d050a090303 81
    0x119083c4103e60500102e00043d102c03601c03483c408004500340442e0290b03680d010990250600d03a404000d141d6942440c1c1c80480c042c20380401c80018001c26030302da141448000c580c0e99030b401400801694250300011121009100d0400d010807146ca803180040c010940525002002703505222601c901e40c0030f25040c99010b01410031018000200000c210b6290041a400c0440341207003400e44480c0d0719400483c07a648022840203000030342043c2003051003419910f0071401010020050270000c0c0c0541c244808030f2049000c040e0060b0790fa10010002039a550314003241d20203d601d031100341c003140310b0024a990303042a0403803095410080300500221508000302002080d003440c1400e0001d110341c60711912181e0034103000c0d042250794540c540c00e54a48034440d00c8030483c007610422506c01e202c02c850b41c0d02c10308014050046c0d40cc0c00040b9100e00c0044c0620108403011001551400005950f03000c0950b84950003101815002d021046800f00c81d0301c9080d202d085c21400c04640c1400700e140007400c036070b012 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 105919145 1250 105917895 105917897
    0x5042c031b1615080403050a020a33050108120d0902040603030c030e06040e01060302090d05030c031815040e0432010f1401062001022803020306060304020d060e0d020d020d 76
    0xc0c03ca800c0c107034400c00a5410a8050411580d0740f86282e404034104048410003510f402a003907001854041140e130204913001009282d264a1084046054155282885490103ea0000607000e00c0307050620003c2141c03412a007000942c104583d13000c9030948200b940158041100f6481040505803c20340c0c0054101086a05502d018101008031140c810180503940c2016404a01407002ea102c011004052a82060071261551102d8480303a540b980700224601c84414011913201c09030074080c61009107001c0d0010810704160401501c149107502c01401510302444110384080748000300500050100001c40c5051a0407480101103829500c942e0200d40c030f064680555074140041042c031090540c1c0f0301e032400c03802d024007030110244500c0000804558952001a82c560312204120b80700c1c44201d644a040000c92900503829822030008075100c5800020400c009001440d0000d29145001c1c8101400920000015459441c081c1440104070160707000d58980034460307404028413180d10710340b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 105920395 1250 105919145 105919169
    0xb150304020603011202011814120708030a03090822030218100e07050c0316030f0804030c0605181009061503170c0c030d0306090605042c031b16 64
    0x654045515844144140541a0b0100c9805011a0303c1840c001c04000b0080a08c4141a5201c0100007100909814407910900c10444c1440b031000c400309002c01110380201c00f540c00c0000c105015400b030104807000321030000c0d0070443c0c054160400c1c80400050810b80d19480c01050071881400319003414641e4048880c80071100701700d42074140c0c0a10038195025649446d01c0e64440407403d5985005541860030907000c086058000002e0150000d480b0314041d580b1420345201c00c5005544020041e40c0c0900041c2e03600400901045480d0451a00405070403115a032a0b01003c489604041c00307400311402950f15400544240034981c09007e0b404c880642c1d101c14480d1440c2e0340c07460f2444454111803c0020007080315100c00109000710212680b0141c259203016071000001001001140501c100c40e52420f000030171130342014800c2c4420601c001c4419903144000c59440000c0301b45442c60141c251008100070140d040c00344c01c032000708000480081404914010005c01101141d400c21500120 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 105921645 1250 105920395 105920401
    0x304050604030e03160915050d05070b09010c020a0e04030e040606050d09061805030309061e0a0b041e06030204061205030703120603020910090b19090b01030204030b04060b1503 78
    0x80040351081e00035616040c1246001d14040200c0c0c01c003031440e000411807181503040041c2d85011600008064105c441c1990b015a4569081144409003010068029440340205004100006000780300b20130050404161443d129800103100898a4201c0501c1d0f01e01d6800b48010181c201c1d030b00d5080d601044500b07203c510305101c3e00410900a10080c00406a02c0c1c03e0070a080c0421a804100d42404888900121030f4581c1403090343d030760064800d14014400c0700f000607802c02205400507104820348104040545800c00c4a5002c0c2c12004292580a540c641130040c80320140103180c481855107400204c1c8031491801000121100c9502014041d100b03a1b0700c1c0000100040100e0720340c0356040c100f0111a859001d5054010806d0b50030094001a0160a000c40784440c0780f200740032540311000c10300028170704000340044551108a20046080c40c41d1003400368240c10307008031030308100c180f40043c2442e50b00d4440d091454010340d02507a1b4980d40e0800380309141400444000390b481020b0481345942 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 105922895 1250 105921645 105921653
    0x405100501120b06160b0106080f25051b010501080d0c15020304080415020c13200a11161d040809090a1811030d09050307090203070c1403030a0c050304 67
    0x2520300d0030003001441e5982d400b0f2040c2c0c2e07988020341d00071040140c82801855030a18000c80204028000d10021504101c0018a0000398850061085507280c1c440c503a1030714484c0304100001c2000f1080d2042c84020301000300c1c504001180c07a2107010500c000800c003075250501ca1400c0c040300b6100d900400003240710f4000852607068201401600b26038005030340340d99a04080c01180183c3d041540060446500b8007070b60341e400503a00d520707694100c405017144201c0e41c65000440f0032001880180184d0195a40a810080d901071700302d14140342441c0c039070b9503001186203042c021681d9840c0103001080a0500c00e00d101d070b05140780f00e061403c620300110704094035809524029030785018400c000b80c2001500b820703602d03000381c1008084030080c0d1412030114171b0411010102c1000c46070081c8030f1200d04450389480348003150100d80014024240081c1401c04050103540010061020300068805450014200b5414401c1d08180000a15102d0400c05407070001da03018510840c0401809100f070001107 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 105924145 1250 105922895 105922907
    0xc08010e0c0d050106170a03080a050402101103160507030b01060201020f030c0d02040f140306070302190c0f17030406050702120a050304300305011e05121204060e0405100501 77
    0x3040110b65071490000c0500c0d2190140c059504540080881c0e4800680c81e901c00241c10354221b40310340c58080150342c135440074600710361089070041d6000000740650b40c013480c003450b0115400f09a400641e403030114210a85d000665458600300ca0a910001c0d0400901803d010300e103024210700c0c80290718002800341000c0c25030201803c042241040050507030300701905641294001c104034080ca040045c1d580001d0850140009a294040e024420001e00414070a10865034000062180440c01e41c0c1c801c18100c4d409c0c8042042290103420f008a19400705003002c00062658080350401540ca241c0f1b0b26100c420b44502610340419540000d0345400440899170a80c0c80345411132410303588990700e500f03028605886696120400c07022070101c110386448004800703050801c06442c28001c1e43d82e91011183c1500000e030103c003103190100e03008d202501e81002c0404103c5140c100315015803480d02030a41c480da115600c00c2c4080344602c00c8042503800c250141580c08000c81d40b109580b00e14100000e0b1034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 105925395 1250 105924145 105924163
    0x5092e0e0f100f09050105040e070803030c07060b030a0503070c06020d0206010e07030f090c150504030812100b120f011706070f11010f0b0a0b0418110c010c03090c08010e 75
    0x1412045001621402da070400c0c407001030018450100d18240d03941e81010051400b07000e0782e80214148403210900c1040068600202c50025005601e1270340c601da041c214a4124100886102d0744034801800d40d650200302401300b4a000d54055681c42c1e81c0c40c5050000c04650754449006c1d0340201e5082c140c2d158000c128141101ea401319810626a985d0004400405c440d001440c11589400a075100380540410024156480711111041c3c0700c000e400165800e025600c00101422000c011100e00c1d0065042400c1c1c1068880d900096001d45407942500c450300f25901204c00c050300c071420045e48003074500c11180103048450070552100d0114401d103858200c0145036409005080381c24070309140c40342c1500c0201c071040c0c900030401210340b1480c00d0098883c2c80c01252007030480f0f5001041e100b43d50302c2140d04564600e10401d0240c10029140f801403e00c005100b0041c003014081c031030014100703010b0004141c42a5500007580480c61403c1c0e14030b10482d80003c1c215038909020440e00e56030015403544 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 105926645 1250 105925395 105925411
    0x100b030d0c0b07030f05070c0b01080312010308090609060403060e160b12060a051503091b030a030e040204030606080a0302010c0e0f09190e030307020f0d0f0302070c05092e0e 77
    0x8903640d82c00e0b8160003070005c03000f201604c2841d02041040959000300030600e0701e84508078030b07112a6070359402d13256a401545031388a50300c1101401080040c0401c4001c0080c2a0007070300c00350503c001040080d9047c0c100e5841a11441d1325800d04500810062001700da01c012826000404141080d1407000d050190403a55080402e095001c140b29a42c2c81c3c4507031004110040c280c20301807400414400d450f400075200c80603148035a54030360780d0810f08030488000400002d0000d12014078aa24112074982842c801c0d190401e0b800c100200c08560b0070301400020702072002c02000d01e41c00700e00e0024210340d425402c80d002c001512840e1b502990b240c02601850060440e1225101c0d120300581006695030511074110161070182c1d403040860001c4041c5125407000d40075a02202600118581c40341002600c040005151000042c07900f40690b004d040c0c0d06005101c0030848903194400728030507640c25207054611070020b6101809260999036490341900070008800c43c81d0303140c414010542c50018140704 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 105927895 1250 105926645 105926663
    0xe0601032a020d1706031c111002071a150d06060b03070c0201020d2d021e1b06070b0708090a060c03140105042903010209060309100b030d0c 62
    0x50500754101c80c01d64469804100340416408482002039626800400c241010920460140038041e0f2015412480b030800540604404060040c0c24103201e80101525014005003481c928400d8004202c1034503034800245c03005940380d2117400d00b43d51140f0149201d941400d4a5410402113401ca160780c807080d40f0082d1031000220103203251200140200d03800404c0c044a0100030071498641c1b00c105820840d00070303000c1d580f6501215a04aa086186010590701c0d0b00381030a00124040120191408030704280c816280340b030214140c0300005600c07050920015502071022246014000004030b41001c4080321390a16001040d5520014040010948000e00c0b500c100000c0c9608010300082a1460380700c9010000301c2c0030342102900410715103492543c00c40440c000496141001d105000307040842c0041d074052400c0d4106030107245002c8415243d0955000d01400c40c1036101c1c000614003c140b050040c10b000e81c215044901201c203002d85141c4a80d1001101742255504a10710304502900030f10b880c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 105929145 1250 105927895 105927911
    0xc0d03030c09320d030509090a0612030906030e16030f020102070e0124050f19050d0608011a0f010503010603180b04120e121207140118060f060e060103 67
    0x15a20355070305074051488401003040000c10728460380410920700038807102c0860707400c0106083c0040c600c1140070003004071b4800c01c080400347c03500070215030348a4081d17040440e0306074482d0f000002c0c1d04040302044020407854001402010b0305400303032042009040004141c0700c4521a00b07801c03499524030000c0d002450402500042d6440ce22080010b80001d02e801141ca594402c0a180c03102d05020b01c200003a01c840a03120301c400e1082c3c0480709c0d04040020100d05001d411841c800d060b0715040030f5401031000800600403111140d000b0301008102c01000003e118255012562489404620940c0b10300301903261941c540ea00a030035207042d030b0a240340001d00c00885c81c107640982c00e82e800d405003803050b51030204002c0120003050880c0f0100150b03280110300d448582800500c0b210f0411072042c68002080207400e114000000e042c200c0c0c012020082455288200142110074280d4003040b20b208a03075405052103180d004004078204d41c4102004054504042e01c0c400020161005041680310412 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 105930395 1250 105929145 105929147
    0xd05070503120c041e050a0b030a2408060f04080703180b1306030c08010b0d09080d060801050601110304181a040f151a07080a020307060615110c0d03030c 68
    0x1960160204942c02d00b2290a000040c9030140e041303032190391480220310307400072810500109000c088030009052441c41e03509000c00c1c1241500014069258241e0300c4007400c5d00f60442140e09546810444010702c0000e0030b00119608200c00100844529043c40b000c1c0400600104122600240c01d8039041c98403030506104221070041640c88050600408254842c500100d6804501110059103042024401c11542600c1300340007445a0f410b9548140600e0600c61419040403012070f104d20451440d200e0001001400c0310550340041c00540c1d500e0307081140c40d58015801000030803442000750b00b454941160840c0940c076020510501c282c0b207000c4007900c540c9331034410025540c0244184030794026525403030000c0919141b0066035005000b000100c243c4800b00304a04040c00c1100309241040e0b50304c031b6050320b03071021801000f1440100b003041e001c110b0901c0b030000134000141650322000d515900090014a00d0940c2d2a400d40018001c1c00d09a580c4901c280c41a603458180420100c40703a500c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 105931645 1250 105930395 105930397
    0x3609030c050f0102030a06050306131202010b150307080f09061b0d0509100506040204230607020d030e030d030615230c010b030f030901020a0605060301061203120c0e01020d05070503 80
    0x40080092150100c2c00c521008190060740c481c0e1000c0c00c081007082d07503a100709950b9907800c1e0f43c6100811103a410365000304004c000d40d08075110183c0004600c41c3c4010010640e6038005da54901500320002c0148000c4a41c4042c8407500405c003c8606401400e00e0701d03101d511001c0c043c00c2c40f20080c07080322400790512440c00c2030310390b44120391104020074500405a00d44410342c42055640d10b514020000b685450302e07200713440c15a0011003615420945145020780701d5403084c00c82175030112007400084016075175001508940c6209555a054101005c400d0515004015540000785030034410240321000078594008207859451070950014401c0c50481b10485e0003120b1401504280003508070007528054102908005040c2d04955521185c2e0010985900890b1802030040c0c000307121940114900c2d402840d0044d00003800040c0315940d0340b000c01010000c240702107003c81c619088203500360b4000c2c41074458000840c20120b07445245440000d44590b42181500309000d07000c01d0440034070000300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 105932895 1250 105931645 105931667
    0x106080c0625140321090a06050a0608011d120405060f160c1d0c03070503061012050a140a0b06040504090f140f0d05090f10020c040c0801360903 64
    0x5920360225190304450a40301c0d489849008174480c0d0110842d4801c988107103407a4820340748a00588003104590380c4000c06048042d090b4040384c2e465200110700e4030028070420341440010200030480c0320301d654100d07040c900d5650390a40c45010500c8204142d4803034408440880d80c80011140e0b652a480e6450346070340d4040a800f03850301115000101313281e150032400500840d01c08400665554504211034140c2c84116002c0001031428000326030213041108018500721014142000c440c140440303800b0403100c0449520f03d042d5141e01d43c01040505901e0314681200c8420b070b041c0320715a600783c0481c815100d5482400d0043d903449004c4014800c00d502030042d0a507018806c2084c035446d181c5c003665a54040e10f4141814040c4100400d00700f80900221a80c1040c040d2248203a070820f901004104d04c0e8203504038081d4080c09607600c4056459100b040381c1d0002640340c41c1a15410200b603a49204059803c0107810b00c3c000e0701c500440011075641c482c11080b00d280c0070942101625003241c07800400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 105934145 1250 105932895 105932903
    0x6040603180609080c100207020a06030e03120c1b030711060d0b2101180309030809010306091812030204030507090e07080607170a09030804141614030106080c0625 72
    0x20401c0e510070490550f0003017030070744500000c503000603040085e42d00881c4100714002754003000100f01041158002d400522603000c0010a81b81007184035420f000f00d12904542e00c0503203000c000341408014200c1d03c540d0544e8601c040065040044c56070b64016031042004030244120004225030075403205035001440c504a0191256030521044441d1030040c01101c41c1701c3c400c6500b0005503c580c00c0d80e800a00c180b82d50160380e0502058a15112684541e2010419604041c2c485201140b150420301031880b03c04805c00e10300d10250717000c1c24100364000035680e00104140c0100b0040021600010b000c10542d0176180000610040da07528451412041da840f0b000c0a00803030042000307242e00a251802c2c00301b43d5448442c0941d0300c2c410a0421905940e200030080707407087d008500811000c88084a00c00a903100301d80703032900800082e5003202c0e13030f41d407019099480e0f08007858094103007030003014004c1424500400c076841c80e03040060f00c00d01690381c2c0c1c106d0500074504c00162440d00c4540310030800e600 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 105935251 1106 105934145 105934151
    0x301020c07152c01020a08042d0620030706150306051006050a1b05160302010311130512030906070f120e1003020702040905060a06031202010b060406031806 69
    0x204000b007411445031901000010301d6041c01007026000c41e001001d270070000521112038000c00700b40003804000d84490100002e07500806800e05101d000c002c00a140c0c0212900d00d441c60003404005043d0a0030b081e0301c030f0f160024060040090300d0040b034003407010b41d840341c103420f0703e9231140d214800004000704205245580b140c40c5000507020015003e012240c42c0c0d8032040d01d00600117404040701c2000c030b102001150307010b124a0108181740c0c00c500d402c0c000c2c40350202d085180907118035800740061691b4212249000d00446096400044c4495169a03160524810310048070004854a9080e5610f081d0720a018101d1104c080c41d0082c885016442703c2c4400f00d002e5007199000b00d1300301d9201c04000c030001d401403128520070289a140082c10b1707882c50821b00040f9209003001819649001002c0c07002e520b40004840a545103403e021801c0d10300802100308203a00d8100190000786 = true := by decide +kernel

theorem cover : BRFrame.Cov 105755395 105935251 := by
  have h0 := BRFrame.cov_init 105755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 105755395 ≤ n) (h2 : n < 105935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
