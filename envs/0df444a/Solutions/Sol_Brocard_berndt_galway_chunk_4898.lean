-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4898
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:05:28.744167+00:00
-- url     : https://prove2.me/submissions/2aa1b8f9-390d-4ee0-832e-0729ded1e0ba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 880755395 ≤ n < 880935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 880756645 1250 880755395 880755409
    0x170a0c0b0d060f15030203061504091506020607020a0222020d0e0d050a090b1c1a010f020c180901091202010b030c2e11100e19170711 59
    0x200c00314100c0c00280980c1a14018007640d0000d03c1e4252004480038034040070b41d10074800b248124403c060b00000840e50369550810b40c51940d003103001680b0b0340c0360356a89150004001c443e0741c100140701c010200290340b5001086c00e620a0307009070081c00403030716140d003080300740c48803030404503aa82c0e40840301c0030f65403200b807028000402c80200001008000b0000d200e16186083c420001080f50070802240000d0788895210104c0d240025016291441200ca600e881510003101319103c6103041c0386924050584284903a0000081e01c82041800b86403d0480e200c800c1e962580e500803260310300c031941d0380070b01490903940f206032900000b80c0d030000ca075509401c00c0040c040400050703450b00c2c058451458180100710350140d00b242c51035032100007400d12181c104034000d005020308065042c400541800f903510000350002e01819107241c074502e009800001c2034144281710041c811014062180502300c40c1a0020350303004a103501040c3c0c04171164102a61006004071020010000751b00f0580c0c41d215 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 880757895 1250 880756645 880756649
    0x70507020132072307150905091302040f0b0319170a0903030201050601020c100806030106090e0312010510050301150210020301091b0f091e0506030403110f0307020a170a0c 76
    0xb040d400e5032001e50741802440c1c141c14450000344070070f04a2450144100024004003290005280381b40301e0241c0c0c0d401690441820340c0066082140d03041041681d44200052580891003110104400848001d4850480e002c1070802c98150b440352407a0180025480c61101145202d00021412095640360302100f80c0c004080c0c00f0042103868005004054080c00f9182d40510280300a001604d03440001802200340210300c9400d0080000100303003c2e84080d0402005050203483c10b1004030b0700c0840c0e00e80d0301c2d030040300140e8607850840008038080ca040b040000c0241c3d041d0344c1c1c141c2103900b4902407044160706440e1190941c0b02c0c039450b5880c10b034840e0000e180201003040000802d000b030030181002e014900200c480810a40c0b4007a0660980c00048110a03510050085c54042c54022500005034825401c841c2c1c1c0500088104801c060f8800d801c900703818526000d8074101c44141c16050703900d0280b10340080d4080910725050203030004032405503058001d8102207594420b00360b120034238180c030300b6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 880759145 1250 880757895 880757987
    0x13152102030609011802060f0c070311040e070b120c041a07031d010206180a1703070f17011203030212070306050907170114030115080c090f0705070201 67
    0x611800820341c0350600116502600c0f4030000d110071030810014060460380000005c3c8140c10105407030201c1c01250301660043d400c000c086904494490410741c0300b030407002400c1c5210704d08006008035030b43c40200e040401c54a940c0705883c02c1c58010a40340719a20001082c0c504010070610001503d0403c8040e5000d0315031380442800d90b00c030f80b00e0800601c3c0103070150400160700912030441c004c99171300183d010303405042242c40106d507044c0ea030081414041d01c00c0c0007928100f02001624020080c0c03500450082920f40c0740c0c1603941d00010002c0e07940300300e14600c40c00c140e1520790040200141d60f08410340311318030a1800524000300e45542c3c0240751780548490300000e980381c0c404c0c0440c0c10007541d00c6821030380d1f40c00c2c5a5006e4900100d80d00030302d5014060426a0000f4000902d12501c0035005016507511a03001607110507100c01000d80d448070381c41002d621aa61880c0456079280103001c2c1720340540b00e1503403a1407600324903070010355854000000701e10030b080300c506158010012035034000c88400c51f0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 880760395 1250 880759145 880759199
    0x19140703020d060e0606030403200f03120a06060c110621040204060e2403160e0a0c03150b070c090204170c191710061205100b1315 58
    0x10042102c41240c000b500700034601c090350700c18002e0a641c0e0a003178941c1301b13505143c038810403000305008000000c1c032410707200040e1040c06d00da00b2400e00c001c0301400d0920341d5201141c100f40c7e50003000c5c00590365148240d002003040812614081100394484504510740580500d00e04201c3c0f00c0a2090010001106840304101c81c06100071442c080c090706000303002c0343c02a100913042c21030341040c1d031907444110b8003400748203d1500d5550352005c0c040c0356440c1011400b00b00d0102e5440c031107800c01660456501011038503117070001c9006802071054907040b84400018001d410b060102c1200385038031201d829071340c42c0e110311800204040340d80000c10280544680520f2944000da1640780350606642e0010311900b01400e0481c0f05001709031520341110300c3c01016500300f02841c0b1060b81480d81c103030b8003120701500300000403075130355600e00185644900c00e40031102c40b0b100c60f50156040f118002c20b110f61000242240001d11102500701200350240024003140c1140e5800641d40092030300c048804503c22 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 880761645 1250 880760395 880760407
    0x6010c0c080738091003061a070b1e0c030705090a0609050f06341a181b010305060105090a080a060b120c01050f04030218040c06020c091914070302 65
    0x66020b00c400511015148403d126409068503074000b800f410401c4c40c06604285000f180b00d074400c0e04020003c020603004000300e040c0c0320303980345d856034003015051340d80c4191500400c0c14107000c4440c0c1d81c900d429200070300d4443c1c0c488240e0181a6031000d442c00701005000c2c01010565030f10441e40000801740b41d11108080c5185c00c00b0300c6141c0b90740c02e988600c54003061080c0048040402601da00f030154442d01000f00402c000007032000d60080420113015031140d2081d8a01600806440500074226084036400c0c230344901c0c501a0340e4101c071010090018503042480c1d809540203401150300f201050400300d04000c50140450095a020b50005d131a9030321506003034041c82060712a4610f440c0c41035440300d49034503a161405544002200c030460402c000060741c654800c0568003903401a540c010803000300200e010750965070420062b0385c20b0303840c880c2c54400001c0c0c0c00e0001032a031400100c0640088600d40d07810280b02c00b02ea10003000d021410303440e80c04072102100403441d6103200d81c5e2503460060302e03a1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 880762895 1250 880761645 880761689
    0x1030b010803040f030605070323010302210c0d030207080d030506040c020a0c23060c06041202030406021b0a03061104180603030e0d05010b0402030a0f0f0b0906010c0c0807 76
    0x2a906a10103000c94008110a200c01c03a120200c2d0010340e50021400315a90f141e0358400c41c01450005005450201540710101e0001c40c2c0100c1e081c1280e000300e5990318003080c020b120142d20415242c1246003a48132007030f540481d0808003c800c03042d6019005482045544150241c20500300182107000603075142c0c00c105292402c1e10411a10403164401406055020303074800c00c140605003d102d00ca00141d040000141580084041c0707082805007102d5114004807400f156542000c2c2d800715060703a001581040f116100205580071108964002c100078072102000c46121244400c0c120b0b08804800c1c03000c004100c09015400e120600c15071364540e618508140c0d900e5801c40f1800300b000343c0e4184001080407a500c100c9070900020211520f00c6242612b10f8100d004009080d80d00c3d030006c0c004010450b030b1242c10781c0450b036a0a221a42409407854060214089400c26a0a43d0f880b001030004200e076544601803049500d84181e01074500035440e04525481d0442942c031000c4d00b10300703220a040301340b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 880764145 1250 880762895 880762913
    0xd02030f030c0d02060f0402010c0312020c0d0f120b031c120606020c030706050307020607050306010c0f061505060c0d0804020a0e010b1b2d19080304020306071d0607110310050103 79
    0x80421b0a0480c030007818076600013014446440c2001c7d04000100d41c402000d1b0205504480d0800c101c882212038205030910090320941440c0103007004102da2000c9020071004600646810312402006000c441c000b0b480c1041c62880602c40000403c0095035140c24504001d100d0340001d4603582c4c00400e07034075041d1400c1500e085550340241c01040360500c10b01961680000d14503401400b5030900b16140d030f070f035400100c81c18440108042d11403282c1c0e07603403072003444000d40c41140c158111441c98640c8036141d400748041032044030314200040e070210340d01c844014400c00015821600c0100520382155032a00c400006901c2070b0424107240c040000d001e0402503101481d600400c030010094083c14140c1c0c4044404051080820040222100780e8a000440e0500004580308e540340428002d0b205a030500c00516002220224082d02c140004030b0f011a0145036900110030750102d480c260603102c0c1e010b21907260000c080c01c903417010001c21011709907503040c070851425074a4040300141d2589036003403174106 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 880765395 1250 880764145 880764151
    0x3061404050c1f030c05070812060102062a09010309050f0318010903050a1128080f0304151107050d0339141e070906060306140d02030f030c0d0206 65
    0x2091046003074010343c0310b086030542e20000000e0b0400041560130040182d85500c00c911004081c00e00004d500000680249030550154800303a003204c85a646403800400d440c038001d03440540c5030301011240450951000002c202490040c0340128880c441944d840b850020000c1c0303c4605a040452442400000000911801c80302440c0c5145124910380754142c5507102c10102621103002080700d81c0e400d8440e460040894a001b82400e8110b0410345128840c4090b00e0080325158000c030009000c0510f400400e0380e003903ca000c0303440607e0304001c480c180c94065807286080000d001d02200010966507405012280a000f40c959100054800e021303420350400791554500d40d084078460042c208840e60606021240d4420303064410705800c2440e0516003400d810008415800e0380624109040380270466600b140c400c0c84050200c1511200141c042c0d80c801c1c0100650084061594516403901c4c0b01240303036450001e825541d2440e282030300c1c141540c0c0802d80c40c1c24694000b0400708030095040000680c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 880766645 1250 880765395 880765399
    0x60c030510290d11180f0a06050a1e0c15060b03130302011506211514030a12050403030f08060102060411180408040f0902040e16090807030303090c090509070b1303061404050c 77
    0x480306c440780000741440700c0c9170041d4801c002e000304164040c0b1b4058421a040b500c9268007c104c1000345003c0180b031164000b034126100e000d40004a00c140206009070000e445420341d801d400e5503a80c030030300d040245000d4401d800f19900d802048244da01d4040c422400b8210541e035440012800115551058840b05d124400803403401c01041d405c94640789100042e1a2590b00a1501c60422000070b464101c2c1d6a60203015803d050f140841142e400c82e00601c2103910079290a140b0340100041030b518040210303400380c09a0800d40c0024002140c0c100c81c0c142000b0000d0003180601100f2500610300c540490f0100c501200001d0140078100080328820003c0180c1c40f0107604c0c09090040c03000201c540a00fa451901d404081d41c10346942c099104031002c0c0c101c2d00201c40711a507803820000d025182d542c005440d56103032418082040001c1d40200b511230700561001380201d500e0488450000d51040d030498680c0d043d64400030002882c030b40a88940000301304c20511060601e403c01a0070b0a280c42c100318 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 880767895 1250 880766645 880766659
    0x903023406051e0d06081c0f0906020c0906120318040e0307080f03040c0803210f010806041b18090c0e130807020105070609060c030510290d1118 64
    0x412403c0050080ca42000354151031a5244c11540c1a40c0b009000d0f103400003100f40c018072440c1c0280d0400a80450382c045800ea866175050390301d102058507240c2c1d89008203001608451500400c40c00c3c0404030785e4000e000541030040c5101c0d40a08c0794116000100041c000e941555294100340c9000d00a5060002400002e0343ca000c083d640c0301ca580d40700f403880303810368036401100081c144252041d60000038082801541d940302e0f24003400204c160041040b54003c0200d0302c011030b02134880c07204054140c0320705600820440d107454640d10052004020300c2c2c2248c20500380d004c6200c00055060310b506050084000c11071103000e1500301e240b0746464000d0f0203008c0c684820017054110042802ca0082d0300300000c070755260307154001210248110b81014040398184070801040100c640d10602208465580810650b114600f141222000610491405d20240840402124030020701160382c4400b1040207841c01d207032040707880d06803203409200104804000c190340c5102c075442c20340d92103003010841d002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 880769145 1250 880767895 880767907
    0x6100206070509090901023a0b0a06050306030c031f050c032823090f0f03030c09040b090403270815090a06050f090d080910090302340605 61
    0xa026010341c10f45648100c024402043c2d0303601007036040710105480040100c5569101c00406404120403258192000b80f062922504090051282e03040103180103018902c2d05103010f0701260241c1028040c0c9a040c0a099481035207036a080000c0045000c820a440000300541c0364a0011030310001c00000068100b00100000e0040721000307005100240e243c041e440500a9803114000c0600d40324401844040790301c0441c80185d80017003540f0841480d030464083c5d40001e003141f80c56145503a9540002c0e841407010681000c2c8800241c81c10060281c800139001c0b00b81400198801c005a4050700400c0e280e0071035114032900d003517800040e0007859000c000f0461615442c0d944c2c0380f4034150f0000d403565420005c170740300074001d10121101036040349040c05203060020300c5407044213045e100300760303540704560601458a014621242c0301c2e03041c1c035010b080c04070100a0024040c0840c40b4044085020301882070445180720740c00114082880d80541911860700f901c003c0501d280364001c0c40c00c1c0a802d02030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 880770395 1250 880769145 880769147
    0x50d1b1e05031b0a020f03180f0d1208090f060c0d060e070804033c0f1419020712050309030607050309030d0b0f0a08150112120806030a0b0406050610020607 69
    0x20725801c2020a14075561303600d1562030403400c080c800300c1c6030506400700007401110048a005248100c03403003241da860020f0300003010000481c40b03809006100949610302c021015000d2200c0941c42003484007510084419191103a04107401202d10040c49000031a1020101d0a43c1c0300c0e031000f9000c210740042c064100488050b0071014000c100408200d0460129003403240515a860011b80f010129030401a05403804881600ca01d01c3c1c1d80d000145004c2d0464144074030071a400100032030610034030381c0f401c032040382c0411604003407900038410340c415000001561120610100d8041e40504003854858000200301070130716001400c600c042281c18800d1064414011080301d205056624000030040020300201d07422002d0040308581c4107a1003c07000940d0f08000c5489107803440500403c1d55141e0f00c03200882c0410403110006000f803d21030043c804c0084c021030405801a1000341111031200055440907811803003114111842c2d80c1310014041c00303007040d03801280300c243e1a0001d800d0714602294 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 880771645 1250 880770395 880770421
    0x320060c060c031306061206110a050403080c0c0603070801030515240a0b1c0e160e040f0b040c0801050f09190807020604090605090c19050d1b1e0503 66
    0x400c020700000c001022441003e551110350401d1350740120140030942d9504400ca040003008482a501c2c01d040c034143d03d8241d043c5a044410152031901c4031400c1c5800e54031126042c0e000b41c2d400311058490012020f64590329100036521502c83d99407505240d604514100e82460240004215018a03000c280102d16490314001c50b00700000384442c0740e10000410004030558120307800071407410b03400540c2c0402600b4602c8230a00351050f04074140000610108140e80d41c049160011603d007401d00c00a000c2c2e09007203481240c01500809070340e0618015900d696a8545003510112500400d0030341c1007003035007400e010f8241d01111040c0e020040e89450030b4695107490080c5001c049181c00000380c4800c00000106545015070051b20f00d0b1307200c40e19016803800a1403180a01e034496628070b00003d14940509040b580702c8203070160001d403821000c0f50203035001e4004108012006840c0c1400ca41c0034140880f01e941000a00c2d03541d01e0300d80101110f032100c0284a452400c0c10032608000304003030001300203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 880772895 1250 880771645 880771651
    0x20109030906050f190815030a020a0909031107060203040e0114010918020705030d0506150f07111201020a030b01032708070218010f0305070f180917040320060c06 72
    0x403c02560310000003d280c1c01d036100b5003c01011050801950811055000040c5445a1a00443c00415440290425507143d10030f0380000d500c2441c0d01001d04c101c4a031a002070500c1c51081c28100c806c0042508060f00344040c0e6001280140d201040c01c000c1c4000e10109117004080043c0c00608041c0007000080030004c071030080c4150038110500380501440d4541c1113491a41c1c00506407070703c1d601c40801c8403000d0b020554241e8407841c808c03007005036a1003908040b40c441080c01c3e01c04516040103661000210640b940700c49a04c10b02007003542201c1c1c031080c00240b00c4140d00740c2e03001603040c000300300240844450b484500c81001700024a22194810521110000b54021800d03e4a4542030710018802090102d1143c58044800c0300024004410904000c00d480c0b044085e50b44050721140500f41310440d9100e0b21001c260158a0413105400581c0080c107018054445040842e00c40d20031a8159401617100322140d1014a112003012082032240c200e0b0711004840607450801d588040540d101405 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 880774145 1250 880772895 880772897
    0xc0b010603180303091e06060f0504020301080d032406030f11041406030a0908130f050d0206030112020d0203010e0c130c05071209120f021009030c1811030a050610020109030906 78
    0x82c52001d02881b03003c2c019001c00021190141300076158500c0d20303801030308152080d01c00a00500c1c001085900d424001e4a06a50864001305850203107100200c0203420282e8041d600700e10080c0c040e40d070711882000c450014020540700821041080d091100032510b0112440f005c0c2803081c4804d0007025800801100c04d08021160a0740329101e10007680e000304842440140504c80000c0e140300c15000c1d6422050849002e01d1211078400e94500910085010502c0002e5105004000500400d28101c0420360194009450b10304100d5042d0f020a0854410f100032801540c0486540100b0349891502049000d580c07080500c0210703581c820160141c050440f00074407a10340100101c80316031207026020002c1810000002c0e03414228200b080703030010351100c268081c582a1034600140c4e405188102d003101e034826070924403245804420717022885120707444101c0c103881c0e44100b02d10001c03000165015403890400010a41001c104012a54100b025507a040d2790410900c200400d0704100510202c40c02 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 880775395 1250 880774145 880774151
    0x5010b03160216080d02100203010e0c0c0118050c100c050622080a0512010b1801111e071e0315050a0b030a03021024030f02040b100c0b010603180303 66
    0x80000305908224080380f0342c2c02d9203001400c0004494200250841d800b507007540035161140700c107016000c1030b0f10003406a15459180040800d0703607400c04400602c810030b00c140001800c1d090032490140351049103c1d040e2040c0d4044802101c4920b0000390304966181c0a040c504104519a0b42d51030b110743d0014500e20418820000103802c50305510500c14105900c4084150780e0700003ca40605640c2184080071a00301e1b070701c4000300f14000940c0443e844d940e0b0311041c203c1900c074100c0045030034101c214070300403050042d02c1c2219451403c00000449142510014102d020309000168954050b003110445204515041c2000070400928420644214810300403c0d555594004900540700701a0165050320480100d5000d141e4017082c16030785211855000d1201c1024001c103401400031224480c01c007000c483c201000081d00054881604034130280020640c008881e001901c4402204100404908401c010500b08008030b141c00c1d002d0082070508104015205201ea030400340b02250003014565 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 880776645 1250 880775395 880775431
    0x20f0303070b0411150f1206060711040f020d0905060603280609051f1505060901050a0806120625030507080c0a030615051b070e041e0213020a0e010305010b03 70
    0x203030140e1741242894108a6160341e01410010b942603548540c8a002070356420001250040c50b0270003c94001301e4100f13038145c120303180010400c402000191001e807031650b800c2000460b1180035000324140c241c0501c01509081c64940d05143c1484492400c0c802103040c082d074188490000c41c85880005600841c0001d2103660a1400901c1d1420300c00d402002962210032060802003540c0080003802c040551213209e0907902c100784032640c001e9082050100c0d505200309030203e03108560485d8061070041540d03507040c49000520b41056015204155120b080040b48032811100782d10314650103409143c104483d1903c68001491100301501c081c580c0600060364512003032007500501c3c00382c11081c0d5220403003c0d801e10301505c183e02840801c2d02d450320307101b250b6481e9100400c01c94103c0b4080c4602c0c07080c940e200d50f21903800c801c0701040800e4402c0442904409611001d10700b241d40a400500142d0328003003510040d1a440a000210741050b080c50010300c1030100030f0003a20f41019140c43e040030f1405c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 880777895 1250 880776645 880776649
    0x506040b011e05121006030b0907020d181a04051008090a0f061d0706020d0c051b01021c0909050f130201050c010e0a0c052d2713020f0303070b0411 65
    0x881440c09140844c2021018010143d541200d940f04a800a840c1044074540320b4050040219040f648140560024115101c45c1c5005003d00c56441d81e66808201480e0b03120494003102c00e01c1d0142c416440742006c2406e00c100e062501c4039064062481c101400f29142040300d0340d50702d002004005043d04100c80a0301d04000041c2c1003540314201401a182c000b081803406a551101680301e41401441541d00b15560680031301c480c661314070341010151143c0880c4401c8241100e51461040e8114800c0c41030b08060b11100c2407003010305009507610090010310f02580c910665001410846d0758601c09401c2c0001204900c1d000030000790b0a0a10a80b02c4554040550040a10912914103400752245000c10480002c890300103490084413402130701d41d100220003001144410060001e01c8010010f00d140303290030004000e40051040d1080619080e503155244402e4064a89408a0490f02120740445c03905001805059105500860030f101c500d4a500e42980130180001c0d2031442c000e51808065 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 880779145 1250 880777895 880777897
    0x708220b03130201030c030c08161b030503070306091103190b0d0503030105040e0d020d12060f090504031d101d040207030c03020f0604150510180e010506040b011e05 73
    0xe00440d120240c4a10341214080522122010204e00080ca07000e0085e595030b0181c0704040345a0300d1652540031550750f9014090382e100000c615007040c06510360000c036442c4e2040d0049002c29109640700c1d5224100384001400f074481c25000b29000c00c1c01c01c0300b000c1600c8024030642c3d5014030881c1c41003070809901e15901c80100216009250091b03000c07030f607580074000000020360407640243c0b4100403180d4900d86564680c5103d2044000503003041c00b0655034140300b0690300300340d110901c0d0000380d030b00d80d03d80c620015945544e100c20f142c43d403078000700305c103040e00000100f4800004034098241c0010b0340c03000403030303064000c0f0300d9070140500c04008200c40500c004602030721840140c0115507910f802d080280c049000c082c01140140300d40d0f005030501c10307801300740980141e80c012401802045c180c4180d4010f000014440d0001320158540061540c80e0b46941d030440700114000014042003035104a800c0da5402099580a6400d02e4000c01c504c0e44c0c0300042002020380c100e880c0d03028800c0b002d012621 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 880780395 1250 880779145 880779149
    0x8031611010e0304030302150606070224030709030b070c030e04110c01050c120a0e070b0702060705010c082706011509090203150a080105040b07082701051506070822 73
    0xc0c0d03107460310700d0429030300000007041524040d07001c444803454140303600303108154201d869541209080c0710342da0041c01c1c680888600005420190910401600020055600201e640100003294080308205002001142a40040051030032201c0210f0703a031000341241c0c102424060090340c1e40c44581880125003001c1c0d07041500150028861070030002c80200e059040b07030f4001e072500400b490124120880c544070303c3d030001c02071401500849182500380300054100303401c103a800c00d10070403070140090000c0c4a40c0318031040945500a480c106560822445118411517615006090303c41c2d44411a0000318103045801c0b0120b15544503807000303000c5481e8003995000004080c000b0041c0702c0004260408113003106030984405541070780d40c101c0a8280d0754291405008007007608007180c0003902c034a003182d41c80b5200071450100c210141f511411080d410107141130081c1d6580b4280181460703070450b12086000103c030070710b05005003510380f41c240d8400d030003603280000c20700d030540310700c0130b00381200340300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 880781645 1250 880780395 880780427
    0x105030a1218180c08060321030606040e190e0a020d0f03090b0d0b040f0207110d052e1505011e170a0b040b190509040c03020d03180b07080316 63
    0x40120b00c0805444044d000113502d10000c2059400022501c1c28001102074201ca210016803040c1840c4240066469002400c03040d0000c1c410007000c80e00ea0030001403140034414128601d04080d0b03d2180c107004490b501c9407440e41e1900f042e41c1d04c1000d41d990210300142c0c20380241c115440b0001c1841c007a949032507668003070a0301100c04100300c031100a9030750003c40b03c00004d4500381700024065015408a21460303900419089040b100941241010145034058611401c101c4d40d9058a08000880302ca10740c658010614030250108501d0305014080c140c14010b003c11403520140c102070010740900081c030404400390207000c1a44143e288204108148030a00d00d206170403d0a00c03003420009800d40c0c0b19020700481c1480842c0007503080c0801028100748441e80307201e00a90406c01000501031001d0000daa00e4a40807401001599030710b081040154402c0e1a0b081d108a100f4800380902d103d00d03440703090449003d01005001c6800003040b04e9101000d0344165031450399440d010b0b102c0d072490a403503403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 880782895 1250 880781645 880781669
    0x120615031b1b07243e03030c0901091202030c1002030909070e09100506030c1803030f0345161e080a02030319020a15140105030a1218 59
    0x2070740c0b4141400c0340144020203408400d100e01e07185000e507001e03101c0da09006100c508495103d8060b02601c20700d0b89000041e80e11841c01c8030040035445d480c58005072801d40e00140001585242584c11030800c10003011b9450600618108503000207403180d81105171580500411007601408520900c1268080e100081903a05d036400c2148000f4080c0381c60180c660700601070100030403100c0481140841c101c407001002d00e480e66031502c0380303210160044044030741030055018021210703135014400f415814610201d9544c407031401b40f52070031402c2440c0e17411000003411003805145003000c0e4044c1c0c02d028105841d0381c1c529818482c105c0c5240060609160704250010302010a42d005c020010040b25901038090440042e16409002e8039901000300095060380100522140c5152400480002d500c20380117031100c4101d1603d40400c0c0010a110901c1000e540b401841429000350b00074601410702a8010034800f01c0710350303071500c40d18550308001003480341d4120144020710340c3d103203020083c041e45040a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 880784145 1250 880782895 880782899
    0x15090507090803160b0a0e061b0408191115032410020114072f1903030c1704023a050303100b07020307090b1302120615031b1b07 57
    0x5420f07001d03613013044131400c01a50128401d400d03903005d1070f07010700c0504001d8640c0b82c03940c0076105490001038105e46841001404001545075007400b4140c0c2280038503140c80d002c01c0c0a468004407038080031100900c580603c6074a46e21100962007a243e0000442c100c20100511090a070741c01460004440343e4846070b00350394070100c0760703041d08a120f00c06109003040d0040c0c2c8481400340d0b07080c3c4c602389283c1504260313803400c401098905102070768130f00040400d44030180c0c0c4402c0c1a4400c03c00030581a000b103601d5011003d1a103a22024040809801c10005d16541c01c02d9070010300110004103070030350f20141d680c00440d0400c0c4000000d42444039000e0701d510400005107405901c0b50800c48200c22034965907000019012500c1003198050395008029040250812481d4030007000302c181e4540e0080284040d030b0050311030510040806083c40f0582c001c40b46050010410203690030382c4074030100c55040c42440340a903654000180303408001170985840c2c00340f00d0000031840b0801083d2005920402c100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 880785395 1250 880784145 880784167
    0x905010b12010c0905041a0103051f030c0305060702011103180c10120f0e0a1b0b04060804110a08030d0225080705061e060409050307020414060a080115090507090803 73
    0xc003540074060f40304c45650340d60325020401100c14004405114114000411401e9842640084c1d4801d80e1760341d512024580307102420911809d1500100c3c7c1161203844103005000c0700b0024554803554030300c000c1c000040c0e10a03140b0b009000140550720701d950782d04041c801040c01840509540702018054110648072103400910300716803d14a000810b03d04a2080d0316100f090080394110744440740209141c91403551010a59641403c800103419940702020a039060302e000208002c0505a50301145800c081c00c1064024010007443e500c146c500c1f41041040940110035030b07102411140c001a01e512100c90300509100120f804413041d0541c0c43c42c1e9008001c030180240418601420480303900f030360348118100d450350b076080820f050700514000060b03035071411350000020648141c003035030b06001460740442d058401041d0101000c00444040180030704202d00c120000f8507041c0020f100400344034021000000e614000e078080140ca07240000d10183c001e107450030041c0301c001e0459a450f003c40f0700d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 880786645 1250 880785395 880785401
    0x110d05011401051005070809011107030506010605072a05060d0f02030408130803210406061707030308070f051c020f040806010609050402040e0a0903110d030e07060816030905010b1201 81
    0x50745204036222684c801c110b070b201e43c0c1074a000340d03801113031280f17801c000c0c0b8019101d103031140b8500d00c403e10030f180d0044002070040c060700c0d0003020107031100c5860702d40601e042c04884040300084c0c4000300d040e8252300074800060000c901100d605443c020380e101e85440198018114003030042b5081b5000100740020003808200800c1c00ca45040c0c00e00c0b034440d45403404c0755120720814001b500c008820a0f90346113a4281454003d40240c810f060001e080c03552680002800c007a82000c03146280c0019034100140b41e04022010b502401c5441c2000c039004a02a01600c0c40c054440c0c850f4641003035101903140c3c00300c1d6504a905100e50388144039203881e624460766a454400b4003802e0b00040c10000d001803036003001d00030740c4e041d1990f035480780500d9919038403080003c00710075109038104100c2e060300d0a1145c0081c801140011076a0b80e011031903011091140d441d00800b079004500700150901008441410048504140e10880c40d0101c1d0306926814018003405030101e0113640601091025603802ca0154 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 880787895 1250 880786645 880786649
    0x1030b1914041b0801150507302f160b070312050103021315050a0b070b0105030a02010e010f051309050708070e010206070f0909020403030203270d110d05011401 71
    0x11410f0000541c280c003180200d0903c440c107500403444120050041d03401c840400c140c100001e10300b0504010554a0f00d540182c085000070a981030f101c01c21541040940c02044041882ea08100300010340039042845c0c900051120441c00d400c0d042008081064240440c8140d040020444141c2c1500c0300710248a0b68044142280852a401e0b1040000c8445008882c1282d400400c180801c0c025428042d000c0c02d00351518001c41150b041010610355104002e10000e00b41074614645c568080c4c1c03030440303403644043e08035078403d502006074840107030f0b4001c80032400d1030710a1801c0e0340c1c680c69195040c2e8042c0140c203585003c881141102180d09426917100c0740c0b00302a541d035108020f0f00c80740c000b0388600c02d4245000b801a00282c000550f168010500c00e00544520318248200603506c2260030308030381040d0001c500507040040c0300200d83c02c82d9810840d03e1400c8400c08011840e075a0001001400011001416002e141c8a0745445913540d1900002060700a0000d004402c02c840d0080440d4100f4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 880789145 1250 880787895 880787899
    0x332a06110a0810030804060f030f0e0c040f11071212020c0a02100e13330e07050c1b010c12030903020f07082d0d05070303110c06040201030b1914 64
    0x1e00091519505006440c0461750044041840c081c1054800c03070b0309500d00c080c840b042c581c8802d0110000041da00c1003203281003a05c4003800248061004200c2560307900c07480c40e091203003020503404443d181341c0200c510050f401805d00322080d085e01d0b0181d0b8900f2036590140d41c041c1c4040f5a03031a9440c00402c2c007400d41442110b0003c801400c2c0c81c010380b0203100c01010a80c0000c030008202d036640d003081d0701004024940f0041c0301144040141200309440200c400401d01c0f0417243e030204005e100c00c11407a40c1121103802c200d4204490b50710381c00d0755106201c081d41100c49001480316240d9002d512004512608007241208089100c0700240c00703048040022001445078a090000c14030010408406440301e00014260789a618007145c0740e8501c1103030003441d800e07c0c220384154440b4000c010007140011245c071419207541980c10b0103001c44090908601a5140401c8500500e071804242c072075203c0ea09007000900055a800410043d4400d0744100c440c0101b016008a561034100d1001c102026007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 880790395 1250 880789145 880789157
    0x12081e1801060e0a090b1608070804031103072114070b13060f1508030c030d240602060703150b040e100f060e030c03070305150a1401332a06110a 64
    0x240c03100a0094032a03024480c0c00141038403000c278040500c2103c441d60407500030315000c0078940303825034290304680c4a1141245c0d01000e58890100410703d04003281282542e900300780f40c80c0300c0c505010032014840e0030700080c0089603a40010380c0000040010b0061a41c00001c104509403440031008002c01110300740f0300c003030303400d1003000641c2080020480704003000c904065420305d0143c0312500064030142c400d107600c01d81170406a0b2400210500d00304020581d50b070080081d4104140c001c0c08940010250300c241d00800c002c00d102c82c1c039042c003c5500f105c88540d260302c11b641d10441c070350100c201540c00002b420031082c10300180c81c07a031080c8c04444494046060750307540102e0808159079062603102c003c1050b00f08200540c0000e034140c010300d900008086022a50f502d01907004048401c00343c1081003511281d480700000043c1c2c0b91501b042000d070720618626500e80c040c601a00482000050680010240440c4200c0300a521214015035512040521209426041c0306400d9080089100c000500e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 880791645 1250 880790395 880790401
    0xf080c030d0c02162907050a0b0403260106050a0c021f0e0922051f0519090b011e09090b0402011107030803040308101212081e1801060e0a090b 63
    0xc4c80b500c01084441d20411003481014840c041c107103940908483c0c6410010510104012a205001c40d03004544a039018403402d1405283c0034001e0140d2100d010310b0b00d003c3c00703401045c840c42002c560b41518094281262500506401250a00006500250001c0041c0c40c40b08a081c1c02c1e42ca4882030342d580b600ea0401d044079200031302c02030480840d1a0b42241705203442c11880301103050030840b6a2400760050300e000041d0b51244200b81c2880741070074040259144202f00703401d815103200c126949000803088c44801500d0311114a0310750107000e100002c21b02c40c41860003040749030720000300030310202109221800482c248420184003ca506a0110302210802c0350003083c08101042a00d034014092419500c0e183c40c12516120000d1071450203003911103000c140011075905003e25644111600c861240601000420400d00500600e8031051171265000b900826001000d500400c1d508e0b0101d140303090400c0b0b15014040a61040c040c40140e201444003c4103e90014030381d85000d0b940100d0291 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 880792895 1250 880791645 880791673
    0x30f0a060605060a12020a030603080c100c0302030903122820040503060a05070c021f0e010201060f030b060a15020604030e15090f0d0605010605070c0905060105070f080c030d0c02 79
    0x4c403500300c800002404100d00c501c0042c02070ba001e000400010324000904540300da6819199074060101c440013603100c41100e881900c5039001d40100c890903441c00b941103080a115035070340c90050864032000003a00c4c00c0000d000c21002a07030106000191159005135520b080e00b1000100b0160520841c980d1102d00c888924810540803501100c4014000f481d8550b84ea00c040801000007800910401c94003001100c09603598022a514080483c07080f19040b1040f0000900486842c404407419641088001c00a030384510785581c040303c1e0421100340040c0e0b03810700065000261600069020116044100011075001a029210702d11984070100c012504904001c070303c42d000201010406400c00c4644c00c507080c031268510200e00301600d54000c160709540c9100648100340c20440015001284803000e00c9803141980d80140b00d440c0c810403043c1000c0c0c000a180780704140014000c500716001c6041005007150454000007280c800341c94072168030f4440407018020b90b440100c014443c640600c1806 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 880794145 1250 880792895 880792897
    0x806090d020a1421040e07080f16031503030305010519031e050a05070b0d060f0506030a1104360e0618070b120621060c0711030f0a06060506 62
    0x10341031600244444034036940da0103a49030020080003240d0081410618543c4202000300407040e1030111156211810401c80000c0014010400e20400140324107000f07c0182002e0030b5a00807401c44051840d65402100c150054034a220070001030308005a030000500da0316900c441e0684000316089000301004032100c0c100710355203020161035185421405203811101002c03d04403148118151100c3c0302c117a894107404d04c0c1041c3d100c1030104400040000340300d203040c8610340180032102250f0140c3e030300340302c0404e40744c0c000244600200c903502e0b424004070f50440400e54005040090001c0c50300410016922580303001c4500c028040c11803c0b03649040401d46000321041048504028035855403001000c0c443c00c0c04001591a03180078410b00800d040b1034200c000c04d05810408010300c03581c1440f034144030210a070f181c220000800745640224027148080355458010740345508058641c0761a04080001c0d919002c2c056506204030000120071040c08150208224010b81040141c00e943d0005e05c005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 880795395 1250 880794145 880794163
    0x60c0e010203190819050a1d030c06060d06021b070918023102040602070f08010912111e06040213060501020d0c050102161b05031501180e100204080609 67
    0x41d0210310940001004d2080d0003071544200c0d00680c6408a61030700108600f1546c0c140d0700400c440d5242d15070503070389403001c9480c100887c8100c4021894040e0562580b03071100000b03050300303104814100061082c00902e8044d505c030030444840c02c0701c1078407198060310b81e500c8283c070480d070382c040c1011550410b5083e07116001e255540c01030000362a07582851045041c1c00d410030010f40d5190070044468032403122030300c090009084260014034139107051120074034001c0070b507034048000ca80c10200c04a00088035200c07241402c2c4c0850410007e900310300c120490a0041d50111120307044520300d403454450000044080c0658001e807a030882c085d24412240003680d0841c06201d02580c0003120081c0540d1003805808660b41c055030005040c118074a40701c24050f50a040169000412020195440d0441346004070080204800078503010304504e801514610701441840025050542524002c940e1034201d52126500c1200303030b076454807403440100c000750860701031414284190750005183c82000210014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 880796645 1250 880795395 880795417
    0x91e030503190f091a0c100213030b181c11010f0c031a0603060d0c0806090303160314011406072f01020606060d0506010908030a1e030b0d0809011704060c0e010203 72
    0x176010008510064440d4840380c08030002d40300c0c60361300c103008035402e10207403610482c00c0500d070721042e1441c10502142038002c1c001000c0c4442d20030110500c03400c0050410418041c41c1c00f504544210f102040e286418200f0003170740a54200044906103065550242200362843e0b1410802801500d00758100c140b206032600e6003061007000460301e0782c905054100c21082c4640041002c0303546035258107040500030785000d40c1540c40171061140480900081086940e49841c040001500d84640703410444810b1040108800307503054035543d00c0c2c40d00812070300e00e513400848070074503007280301154a5070016080c90114800400d856601c0070358404103009007d444000d00843c20b0240c2c0b2000e0300300401015000c1c0d41404022100050103410600107011540302d0360321015001c08003032800310300c030582c102d01c550205407405106844c140c1c1c808007851140c941052445455001e000016607020007040100358001c0101d208000c02c00800f038005100340000707070b503c005a03800310704016a83c901540369020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 880797895 1250 880796645 880796669
    0xf060f0a0f26010306110d1a09070c030c2316150c0c0308090d0b090d08070c030503040b07031d03090411070c030813120503190807091e030503190f09 66
    0x2017021174205880d0070301e8401c50300e454003034504a1071088409402e4200482c1c3c00068480b650703032a003405c405074800c80c00d042494070031001b0717540107011240359a40101100c4040420650360040b0503046010380030300b5000c071516040d80c0180750042d50300307900ca01d40c007948115207100d0809204007901605580d02c040c10525031400e6540d41002e9400204000340c0000510900d0f60100383c0840e00f090203256204041c003070059211900900070713407004000c0018000301c0000f40c00000c0c0e00000b140e40c8160000000e03155500c4211048000d1b10070f003d082c0d440c2c0654102130340c040d034401000410602178110b070100414101c0540c400341d0307805800d50141519075130400400100d001c000080c802ca018034203d0100c41520b1f1200c0d0840c2c10386180c400c0c1c80991002c541a110344020030b0043c88101c640d8140409513141c58040105040e03000c0c0903078806030039a031505111560780d030101e42c00030b1640501600d40314100031180000c0030302445e031340000003599902c80d5003034540555218800d44040e84540 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 880799145 1250 880797895 880797899
    0x1b0c0c01050903011119030b0303030408070605181b04140106140a02030c010501090e160b0d0b040e0717150c0d0203060f090a021c0b030304050f060f0a0f2601 70
    0x10350303607074120820340340c1c044d500c0b000903070b1040d94008020105e0184081c3d8070075585503446401800c90f0b1655103014003130b6104106000214103600306507030006905c0013002c9190b9494960718078a413020b00040407202e12610600c40303104c01c62030300c11807459070003031b5010000585100040d14401c80203220300c00104110b0104d12030316521030801032a102c40d507401100e240010205131142140c40036402040065551b03000046810414000c2003c0c5600c00200544140d09010b4030724050b10494400c0d140342030b41d50100b9400c645990b080b1b44800784504040c0d841c01e95580d1007107150f080350252030500070b02620f61007550300074140b080c0300d0040740050078560405103040301c3e0354029030000c0c00d5940e10110300c1d00da801090342d40c00040c911503a1041000358481d0407010002c0284104100103200442c00d0201c0c02809840c000142d13801c0f00c074212440c031403407808040860064070a5680d03415020a00080701d21900350003c0642e2003801d070300c0d035030b001c21041802c80c40440a03048607841d2018404007001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 880800395 1250 880799145 880799147
    0xc01180b060918060702030a1412190906050a05071701060801120c170729070f020f060d060608070c1505090c0a060e03060105120a030c03180801051b0c0c01 69
    0x791039021030800f11140c10042d240300100d180150841303e000069000059210b07206a02c9440400c00380341700a20b407800c16841d05280c032032807480140614000c1da01c1b1003210340480c160b6004601000e81144040100d8148500240003410302294008003007021450708061200000800300e0403900240e941c00c5260742400192440005c0b10082541d10360b07681000480c140d66841410b060880048000704190761800581500001c00c00411126081041c912450912944001c841d100d0b40d000c0104103c107691840003c0c103e042d01448079030000b03004039512413002510f1340a10140c62244d100ca0105a98a4404076644140e01c1d80080034601e000c0c1e80d4094004240d0001a004484c00f81a260344c0c2c640d031f038040ba42c0ca050381d1340640c0000300202d600039041d060600595026090641c1c854500d070010900490b620502c032a4002c040001c00600c0b1010325114000e04004280001c843c1000640d40d02c86c21030103050203650140d1760086001c4601582980c14007182c00701d241c07440c003610081c002000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 880801645 1250 880800395 880800409
    0x2070b0f0702070e041a01060f0f03060f05060f04031a25050901080a06031203140a0c0c0f05010f2a030e0c1009080a12021006050a05040b0d120201020c01180b06 71
    0x406c41d160440c490b0030040c0004900c804a000e0a0190303541c208115100c18001c18820b501900501810318106042c4114100d50000106540c0250b8035039940740d1803904100440c2c03250b47c1c4050180364800101400c201100c603200c5001d01501b20401d02d002e8821000c0c6001c458031f01b980b00c0046001002801d01650103451031a52103150301d980042c0140d503d40700c03446400d001c0c0341070ba000240d40c0c0070510b42c0100c3c040e00140d00400c1d4803a00300315140743e1072000b61444c5032902001e0082e81810369564200f20f025045070300c182c2613030f2106000101107400c0326024001320b40ca0410517948070f0500c699a2521910840c0288a0320700c0090134812210020721911150041240c02086104203000c80c0d00ca41c200110b03409584940c0c484218050100c6000b400c00070340c80050529581000c80c1045203554a48030724040d038008840000d61039180c000014290324225000400811402940e1a4032a8041d402750850710254402030050040440402c0c101202c04100101024264808600309062802d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 880802895 1250 880801645 880801651
    0xe0a0b0c090a030b07091a0a030e12070614070e0109050907091a0304050106120b15120d08010315061809110d1101140c0309010f0203130303020102070b0f0702070e 72
    0x46212031a100803a07001c0b5122800c50340055503500072100c2448881503004031010003c0101d680d0106005451001e115101c6c030a15255104141e11813040c1d141000c814800000d0308454060502d554048501d0030700050040714003410482000e00b400604014003505102c0e241d04016503403150800d00744020842025400340182e02009069a000f09914200c288214400d0304002c03183c68403403405182c040d0a5401c207170010814030f04a18031420000d1048840c903a000321082010b881005074840218061510040c81c0161900c20500040d9200340c21000700f80c140d07409180d40e5050303c401c000d800703400e454562250341d007800c2c0c010000040907150b99001d6009580308003070401d4502110300009903406100382c8260b5950801d001c05918968102c03c0d002000c1c407994035014241110850441c0d142e00803500c001341800600414814924400d00c1211181d08200440d10506512810300034001d40041ea421921469600003042d80810588211071007805198000c2440d2030901c062607a841c0409 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 880804145 1250 880802895 880802911
    0x312030f161101020f03010305100606021207032d08100612050901021629040b061903021f030506040b1c080d3303050d0c0c08011104030309090e0a0b 66
    0x3a0b4450b041d41c040c20700040c0074540c03129503295101d5056061041c1041c20840010a8151600d04c0c02c0150540200c1d01840b00d1401c00c04c00c944a1642e030038103503850340c03c0b00100702d1a4040c1d800401c0c4510f180006220001c803030f69070340350301030f40d901042d8804035070301400b4200204105084540703007400300d40c100303e030b2104504002600f458030042e0110828000001d003250442c101c156058007044000002c00004400350f030910703105080c00d031a0f50f02611406840700b0b0040300d2004605443c58190240e0300c0055502a191400070f060300c108070003103020208022000a401c0101003021131806020385400c1c450000c10030380e1034040b00004c04040c030542d14802c80702e48009005910300e1b00740ca0300c58030303542182d60070070b400000c900d5141030b0840459182c5400c03000740305000e043c07011a100141001c9a01c0d56410003549189081c01c1490301004ac40c0d00c00e010640c2045410301500001a0260080301d10035142e03140304a456020b003405803110545001c480364003801a070f4011a0705000b8081e080110 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 880805395 1250 880804145 880804157
    0xb0904081e0d0608010b0108151e0d02130c0306050109150e120d03060513051308030603030d05150f100f0302030414101d0706020c0609012c0312030f16 67
    0xa0081030b0340c160351141d40034040507556450b070010700c4e58001c60041da001d98019210307910014000d0004034000c581c1c14100520105000500341c02c2c1c3c8844043c003141540081a40c03100042e10314003c2d02504454101c003002074248500002d465000f031030b008003591611042d0080000660008540e80c0e48072000f640c0c1d002d040340041307036142c0343c0910480545010b04e51307020030078505040170700044208812040f60020f2800c0c00300b01d070b21070744030305885c20fa107038040e5210741c0e02d4442c100081d1840c000d25200140c0c0780d140c10240101041d4248005605030026560030300c20003040010000c0000c5810001404544100e4130019001d01c07035802182d000d8880e9032181041c4090006651514034040b20341c1c19a25504c03c40b611061840b425400c036421481c0e00207001481c20b1000094490000c48152406500040740111301c0d68000c140c9802c50380716103003458600c21330454501038101c000c2e00340340d03002e8081e080c07044e4400244101180c2c460b003061f074443d504603240c1c25540b445200008a0305410003603 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 880806645 1250 880805395 880805407
    0xa02040504020102151006090b091e0118120b0906040218070212400e101502030415020a021c1a0a150806040209062e080702010b0904081e 61
    0xe17401001902450300c0000d600740ca5802e200018102c0d03080b0303421603140343ca000d1029146d5941c800880c90240c100d40407000f030b151000d40c80140c5030340d18003140703a64428071030300f401140710101d607031212403000d00452900190341c5540680d07503211401950007a401c1110040c00303210600042c03086580003051441200c0b48200c1500358460710b1380000c841034104542c01c41c00015003c44510003c1e032402201461403a134a841401c841a001c030030f07482556005400c0b140058202d84206035004002d007080149038100c0004480000e480b40d02601a000124035030f10198026540b002990040715039020b4015a1b50b81c14041d41c1442c034008183e4200c4907541c4807400700311411340c0c00040728003501024401040d05211201c28004090303d581050b0740680c00041000090b03941d100d03020f42c00400c1501da52041151045d04211204c44406c2d6142d008000119010740b03099000301c0c050700c5060140c0c0200107240010307003045500341098801804108040c00300750352511002c2c291003044051a4030302c1c0c3c5401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 880807895 1250 880806645 880806673
    0x10090e070f030c090e15010509060403030e1806030c090903090301140601020d0c0b0a051801140109060e07020714010e03120301081e0d0e040e0318040606050405030a02040504020102 80
    0x41000c95024000401141d0020754154040c041c180034200c0c0d03424000d000c142010402d10601e18020401c2c8040000c41070340300e09990180044400356580548000e90303603500ca0501504082c441c00896000c2e820010010305011460840320b4004c4600401524840c90640100a2850800b5045a00703d000c00c000894860750248945101010305d081483e042c0d01d06400003a0401c8842000c4106001902e252071000072082200c481e4071a0500100184507141c0400001c58030582442110f11b540c682504501500300c0c12010f03c1c12184212814880141c641d5264404190180c4050015074010300303003032003118840384225100c16010700d04106180c5030340b800a0b2130320640c001c48641e8800700100510034440f0920440c070182003c4800609a1303480d05041036614505054000e0400810905541060780e80d904a000c1840d00b6500712a00d03810382150080b0307180c041c81005842140341610000d12140144107450842e00010007600c000c0f010f90302070001500c80140124118000d514000703035a0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 880809145 1250 880807895 880807919
    0xb090a15023009010501050114090d030509030a0b090c060403030e040f021c09060b01030603231002030a0c11070503030d02220605031914180114280504030e1009 71
    0x900b9540c0341c0702145080055809003102c0303040e08100d0411445000391480c0c500c03c0000c0b242c0414007516012590340340c0d4202124180918500c0f59030500607101c1341424016204082d0303004100c480103031441a0342c8c0b40200011841540300c001c2c00300d0f00c040300c100028a400c3d84550000c0f18180c0000d4900b510380780d9466200041d000c0c500c503400c0c1d9102240010710100b4800c44040320030a007010000d00c0e085450f10502c2c03c42e000030301c6004a60b02d211001c41107105100740782c18005400c2c4195180d0a0030040e02c006840d59070180300000300216040c101c42d840006600701101d030094091460319800da01c82c43c01941c46420342d844004010400c0d04c001c1011014100010000d44d95015200c1c1003c1e6a0192042e002e000050380c110f0901c600c248143d088a488603070094004d9001c0e20519001e6068140500220318152201c045c0c25402c1000d1500065503001c0504154400c1c49041c0300c10400e83e608999090350040c0c0004d0b0f000000611504100580409151650600307942c41d590381c400d80b29003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 880810395 1250 880809145 880809217
    0x140102070510020f160e04080a030b04060f0503060a11030106200f011e0b09010509060409060c05041d01080706030908130f030c06020303130b0a0b0a080601030b090a1502 75
    0x160b0201c2d0b440181da036001d000c10240829081c0810104901d4860490310740032000c0c0000d84101000509ca40c0d00781d0280c0d102c0e8010100181c401e01c409070f50b920010418110610506001e40075072400104108030030300c0351300788514141d0300c00350440e400c10108903208020700c0d504c2c9043c1c511004c801190800704200e00410151200d0012990041c4c4440c80f030782d10002400b0340c0304d0349414800b90208981e942c401c02c17419284140d803e540141d407100d00150161203007000c041c0090380b03004114070502e0ba00000030020b03200c490b01510040504450307007071183c5200748501d01d80c0340c1207a4410300800d40310b50011441e20380540d80007402c05c0c0310750364000150035003540075160f4850240d0007001008103440a18008000340d0010310b0462408031484804120070b41c40c01424031000c00001a203204644c2d0050036080c40107008040c00750b4440301c0b44c17030351040c080c001520070080c8940014408140003468100c01a030182600c0c9244520700031540c00f0703410901d2440048002c082e21a04814207a0749080c0b5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 880811645 1250 880810395 880810397
    0x20030c030f030901020d090f0311040603061b030b010c020d111212030a1a10180b0412050105060d2604170d09090203010b041215150306050106021501140102070510 72
    0x141c0c0e0300c0e0320700c0064a1b00c0c401040300c1051201c540c1301042200e001e40d115400300ca400924808614140d54001001045030350002050ac0c0d18040c20382e52038800000345550b6554580c0c6080150078401c0005589070012058000c2d480f80e0041001d40020700043e00d00a411b5101905528110340c031a10034a00f0006d119188100070003000c801c01003400d8041c020a8404074518405500c04c40805010508412018560070140140000d400341c180800c80c902000812441002d01d407150b40b5142e684510b88000030301a182d030f40c02e02c004600c080c0740041c1c81e030000300e501940648008910170034900b480705e4040c08074003410806000003d180c0550b541c080d00b42d11441400f80c8426a100b00c00a0520704040d002140e407207106000504c600e190020880b41070f01c4203151b175045035601c00d04e030806840c9100701502568604154171a10302200f14140710064074802d41c1c041c0310680c0c079060203d030ba902c0d06021845211042e00c00412a04510080d2040c91020600c1500c0c666501c84001c1a030400d25410180 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 880812895 1250 880811645 880811647
    0x1a040308190603200a03120306170f03041e03021801090509070510030b190b0c0f0d05070210030e0607021612020607120c0b15100302030420030c030f03 67
    0x5a4901c280818080034800032400c1012a00310380741c02c0580400015410309030600719809039001c0d9120742c5c1c1c0300029603001054440807002000c004018188510403c00404501a0442003070030010a0801c0c0c80b1240c0002142090301d0107550603481c0c642d080581c04405650040400541c81709103081d91400d107259181603241d40740401e034004880c0700408804054010b5502404181c0e94006550340780d040b0707071401040d0182e81300300040e45400c0d00d88104464020070f4000007000b80c80070002d0300721903503400c0c1590110818001413075240c480d400507040002d0310400c10a4014540119620155501d51400140a025035215a440e00e041920500c0160340302d0131034070700d50320741d504901c10160500300c210300052800e50340892501d01071500c00034040744284075181100c0b881110f841d034505030880c400d44082d00304401c000c1003140200c80d140c0d026510802ca2040c0c128000d00889000325800020103041c035042c005420030700350045804560601074070311f81038100d503410808070808004000140d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 880814145 1250 880812895 880812901
    0x90435031e090c01112a0102010e0a1203200c0a0204051503031e12011215051504090204380f060d1a0a0305060405070501050309191a040308 62
    0x1003280d04030000c0700c101100e0388242009028403001c07402c0d03d02403200782030401406035040301150401c136003526906644c021103101442501c401500000441c031080c0c0003000320b203120710b00142e1140103aa0003d0800c045011048a90900c65848950080c200d040040c0b514550420240345030752205110350680e83c0a41c20312425072600b4821203400009981e045244150103030007103030722405500e1001a2254001e0310103c1c000c0201400c89050091482c01c1c0c0206684038800c040d4103000d403120a40d10b00d842e00b00e00c016120424480d4900440141c00700c0f021107040e410401003c0c00108004a811589036403480e60305030b55110b85c4806a00c14001c40001d1580104444107206111411540c80782d001c200015500340c450008403902401d2003440415145490b04440d1030401b503503030700c0f10740000342840000103000012580d01e008a00c12000c1e0f6400540e52001128103010564090b10705411802c81800c0c0c17130030785820741740c8014401c02c1030380c51580b4040f044210300c101c111800c0c0c1c00f0400003410 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 880815395 1250 880814145 880814161
    0x606120c140319050712030203040906210807031806030e01052a0a0c052d010b0307090c020a0c120b0a1a0d03050c0109110a0b0909043503 61
    0xc200003a02241030503901c1c81d6000e100003542c900c0e03110a60450382d03100e07121010600a00740110302c003901c24194800b421603080d2034000d55039400342c4075a40310945000004100d00300c8040d0b020100116904d0070380c60303140d0140c0b500302c0740d82c3c4a40401c800b80305404007800084000c00040d4001131500ba1000522404000e0741d840c252000244190b02034094202d100d100101e105100e15006645020311075120240d41c4020b44951041200140c4648101076100000039565040c042001d507042c0300c42c1d800e000d4021100f500f6034000200303d5505800401c400c0c403040700c83e03038080355030b40c0c2c3c40d88101c070400441510344512902c86500303d01c81e44440d00f46640280041081180e0b00140342400403c40803070401782c80341030401155440d82c410103284203a6000c1c144214180d0b030007120780d0402000400076501d04080e40000e03054903a40500b41c1e6500c00a00040441d06886029802400d821010b50313455031040000c1810161014032503264081140c0f00c42c402c4040041c3e4000d041104694074100055 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 880816645 1250 880815395 880815413
    0xf050702071a0408211303050105240a030b1504021c0e031c0203071101050a0c030c0e030a06050a0603080703090f0b0702060d0e191a090f0d0503060d060612 69
    0x314024a42d02008200301510001583c0b40d080700c4031414079402c840341904803c05c20720622142130f0030300643c40c0000c828450190311050061000395003241084a22100d6002c05012511415601041c1c0f0001040400c8001001c80c2e440788510b000c83c0c103419140303c0060102d0b0880c600700e5524800f071062085512900b84150001e043c2241c0c02036007030007800080c008203003001d003150b1002560007001042125000e80004138140c01000d0080c051407074140d02d04001031080d00e03075010009040241c020748041c0078a094a5a440c03000d4042d00080583d500d84101408000d0b0070b10804035603030740340040441e08131320140881d035200341e688041c61440d0948613880e4030b00303d40100351402010001940103036216000c651380500318040200d4045404401b141c202822281807400e100f080103690b10801490f40602100b64482580c8014a500c50b0013006540f1044170200450035030144208120490207200074540c4007a00520003840c10350944d403040300b61101c0e0341c0b0a40c40c05d440480d40c0c6c010050468 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 880817895 1250 880816645 880816679
    0x406030804090c1e0309020f060307050310150f08090c0d030504061211040504050403030906020301090b010917061816090b040b100f0c03050423030d0207030c0501050d0f05070207 79
    0x4030742261400030381e44c4052118580031201409040d55070181e07800b1512030000110040c071009041d03c1d01c030314004802a00350361040b2280c00342001d03141004500b1640c11400b02d205103090341d440f910000310f0903400360307070340d40016005004e50f11801558402559911002c200c0c41c40c07180d0341b150348407850a40c020b01440c80c90400c90360f006080135210001c0920742004e450460350304940203c3d864859040c00d45c020030315040d01800c10381c0000004107522080e50008902c0200a82e0744644150307440202e0354486007805000c0c0c0741034000b900410b0261184190012484d4012400e0b5190f840b0310b0107a88400510640c41548030365140c40c00020103180034171500003644010b640c4401c145441c4407006100700300700341143c000e001c581409a003c1c94030400031754010b00316580f8680b80e92080e1680083c50389a8041c0760b0340c400e128191000080d14400300301e440440340d2010702c020740281440d006441e40c1c0c010400515407140e4171003042044036040d0060a000350300640107840c0031400c041143c0310404000e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 880819145 1250 880817895 880817897
    0x60207140a03020a0201120b0306072313150915030f140f0c0c01060305070e09060601050715050601030f090609021002070e010e07050f030717060901050609090603010204050406030804090c 83
    0x590703400400b0035004107000308a02d60910b4a0002050f0300320413403004128480810341c0600c240010810140d803c41164210703110601d44640c254003000307000c1c3c0b40c540b0400c00300c202c05140b001802c004d4204410032443d48110b442c00d10501640e2900380000020380300718524800a9112040041d02c16924801c800c1c21f4610301c1c3c0b82d0b941c5c516020f4000c90500d440a0b040a00b06000000e80795031110007944080090350f8000b040e04e00b0a507070f8401c00012044191b81e010759030700403c400b29a056005504445090f40d10203c090708071440303500240c00070300000300703040c0c10b150b1038400c0442d40c030400b03200e81f45081d40b14039000a00c1d410203006102c80d9a42034040c92040d5444070000340701c1d1900c20040b481c1124120442c000490751800c1d0102c0d004d014012109006040200601101a41100400c0210340340321110140a030b54403010000aaa820301c03849411200030411940075080009000d54081c8025001510b415901c5000c10125400c036403080e1424000407030300380100720780c82c0550030301c80101d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 880820395 1250 880819145 880819153
    0x8030f16050c03073804050d020f100506040b130e0114070c260408030418020f0304111207060201020408011503030206010e09250311030f0d05091c06020714 69
    0x10201141d07a02e1040d0a1301818060034402c400f94880011100707101440364070300050f06910180140202070810a0720203c44038051030314060001ca01c00610319a040070210010301c08002c0550240c0c000704009480b40350019180c5818030450303212402101211f00d01c0c01c100040c419190540e59003140c0405132050b20000505042c4070080f0b0344a0008000340750003a4240512040700b4003071410030501181003000081003c41c0000306141c4c040090000c488802e050002a120903050503000ca1241d0001c51809100034400718006c05e44030303100d620b4514805018040c440701c00400300d904c1c040c2141e0141c00140e40000e0140312011003801540032203076460301003140785d03411641e011b500c4590500a01e1011030414001482c807000030424041034070f50300c040321003069603041c1c640c1080c100c19000685801610030b0080c03595080000c0c3d105045603828026221840403c0411681c50b8032003580c40c0c2d4000c01d0b00003000403106801c10301c111003512aa40040e0742d051146048404200342021030328142e00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 880821645 1250 880820395 880820407
    0x150f0e0f250c0209040507150512181f021c0506060d0506011407030806010e2e02010207020a080714090c040603020f0c0a1406160c170708030f1605 65
    0x600c03400741c0c2039220541c5030324141e0900800e4044035003001055020b94004a00c000b84002e0000100e581025110070369050b5600504010081e0ba4034812003180c032041312001d200142d08800c406081240410300641559034000e00300030048070080110055102d01540002d080e8044c00040c5080c0030204900c084c240705900d81800018194061000440480ea8480c00012400c5c1e101d0311000c07039115141c20032130740c5179203890500a12918048900501045a0b0711018042d49021010107600740d41d40d42c0c80c1d1404c00001400c0b445401c0302882640c05640d028440f00340184c2d10302c034900000d002c01e4002000c00078507101c0b85800e10b000404540c3d0154180d00300b80003c84a0350011101510b41c18200076a80781c0b00413400d6092440360b90712005150003141048410441d203012003a01540f911011a01141c46284041c00400c442220f030390041028008040c0020300c41c1c1191401320307031540100d00d08008003611007920035801198484070a108140401800d4040e803050b800108602d441c155003009 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 880822895 1250 880821645 880821661
    0x2a18090907090605240d11030124080613110d1a03010b010e01091517150108151011070312200703020d0209270a020102070e040201020d1101150f0e0f 66
    0x1040005d58030030700701d00c000307111180d2440c60303002030360042c0e100320305540c0d02d42e599802a48200e86800c1c55807041c0c11a40d0001101c580b2910a6074000d00300100040c0050011113020002045201d04c0c0d81003811042c0114001d03040184500080318145504000c0305950711b42c101421030302d615007400d050043c81c0d20741c541c0c80c0c1d0f0b0042c0c2450a40d0703031950329051008150039003910505291400804a20090303820407100c0080d40440c1d01744610283c0341c2c10b583e40c075020740345150424208149600302c00c0e000210b41c051849a0020414070044001350388a440c0c417a251892009440e086d071602041d151601180c00607400c2c001104818540400380c03034070074290b03400a6015040500c020f489015081d010a41c0a140c41c882408580c4407180082d0000944506884c2c680300c0a04007039025000e2a900047c4c21410b140c06c80e4482c650503409050003218400c802c2d10000d450702c0304021659610b440c80d0300d0319141d03e115040a802051588142c8a29208007d40c0c0540300030040c03940742c1c540c1010b020f114 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 880824145 1250 880822895 880822939
    0xc0203331017070909060c1b0203030f09010315060e12150a0b040f14010501090f0e0406180f03200d200309031002040e2a18090907090605 61
    0x81e40c803602d0408544908022043c0c40e140c05900038040315858400c0000c1013060130b42c420740d00d12480791183c00914080751103114100000090194254008002a100f1043c40034020001c03c24141000590140300d80105a04441e90703820100c04180e14105000061400c28040103440381241c000b040400c03010080d02c4111800074180c401c42c1610390f65184403039610740e0000000e038000c1c40810400a022441c504070165400e20915021520240b004102520801c50301d000780c4003407854424864940780d6a650042041c8000140c44180c459040c40000b40e443c24040c201c1d502aa0710600840c491909101110341c107101002241d038003000c00c4d4180940c00006086804d007400f20b9040c1900304c84480a81984184040c1940c5402064132020007940103078003400980c1e03461031808203035a407214510401025003080d000355400d070070100c1550b21032241d4000c0c4420303490b0f00040354520321824042010320380250750214164101004c00d002031007091251030b0040408540c0f1001c0d0354240c00002d154 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 880825395 1250 880824145 880824149
    0x4050a0606080f0c012609061807120f0201090b041805060a0e1504021e1e21060f100305070807081303030504060b030307080c39010c02033310 63
    0x40c0700e01e1002e83d41603011070300e40c2a4144111050105805c0c50040c0340d094231014225180a403c1e41130046007030004500048080c00d43c1c10640701d60302509059103460b03140c3c8500020407410003035804400302c0e0070040240604000e01c0c241c03030183c1c21017540341c2030f4600b59940140514000c0344030440c01c20940d205548642c0d04035220604c442191650180468043d10800300c0242000380f042e00308150000c8218018004055e121400c0c030200b4014407210b0132a8826070850030080e10103486c03900710440180201c1500006c00401019080d1031100226007041000300b0800007284c1d8801c00c104075680c00c50f20311a0300500300d00d00f610795490100d50152a1109444018041550b64400281040309a5000d005800c6005049a84504407490100b409501400c5070003424000c40e6400081084c1260300343d000880100d20100314810480c58403103481407220304641c1084564400140035072070a1045580025000c240224081d0101401c011040300d48005030850045860820410f51036080055003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 880826645 1250 880825395 880825397
    0x142a04020904090b090f0606240c0a050601060f120c050a050901050d05010e0907060e0a1703070b04060f150302090f090a05060708040c060c02031c051204050a0606080f0c01 76
    0x284078488000468001c042150b0b000b0326004a501c00e02014400015103a0101c09035502114076a550716000c1c0107030300c2e4070550441080b50385200c00c00c80780d0700c000c000b82c0510241c40701201c09215254554501d408030a070f1103180031400e000c1000b42002e502084030f01407400014020701581103c0600100b441c402ea901c002c0801c84007051503642a8801c00445401d0410124140515619131b400000c02050a0f91002080c0c0f04000000540d24000c81c040c0c81c100500808488040e480d00c0e48034004483c90340c10311001070200f009510001898030717881720f0145002e04400540d4600c00c08100003115001b0b89030488060451104000681d140b04941d82c0c09810220584441d0303c954281c241760240e00b0f1002030503030140380204040d0580c4940c02d20b220b43d010f41c414400403640d5a90a4400f0703c60140065010341112010b104440790244040c1d90003841440d06d5803800a0041c0c008804080c02ea50444240e004a00c1c45824008140601d2010300040c202a00300043c3c5c1c0c011b4550b5850102e5103540c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 880827895 1250 880826645 880826647
    0x40b15090607050a0506090114040b0f0604022118010204031112120307030506090f04150e0f0706051804020405130e01181b170d03021303020d142a0402 67
    0x5100d522032400b07403854143e00600322080c0d8209480c0c541c3d290031080310b030250f40b5880e0620640000c4800c0035803c0c0034a801c0143c03130001d616100840e206015000748440e40007034081120402d0f000d00780b40152251008103106455500b001081d000f003001218000c81c00e943e0040c801070011030f031019440c0c41140c904131086880440158000c03810a81124600d05c2105004010412080e0f0142c21261141e213080390540c5543d43c980101101d610001d07074001d4070044031500241c503517284650100f00f410354294215419824007440c06498559280c101c0340000e2400b089103014030102c7e0700c0212081c0720444c0c06508150418010803910a0301495008a480d19444020f040403000e500c04103c800032840030382083c00c03490821215003c44913448014084e1131000001d0f8040e03030101c800c1c80108000e006007013410040302d421000781d0400e0881d1156410315590002c0141d41f00941203071198460160709000d1447e41c030030542080c01e030400c141c12000d40d1040d0680e5007803480d0004480d03030004071001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 880829145 1250 880827895 880827907
    0x1f03150e01140d1b0807060306150e0616140309030709051303180e0a0912091503020a030b031c020f06070f110c040e010605030c030c0307151407030e0a05040b15 71
    0xa1805007070079010b2044100401d440030445c050041105019a20280c505004082d0b66507440c010629150540d0030005144080d00001442c281c002064810354400c2c40404040b2242c68441071b80144041044040e80b00007003000341e0b814244141e0700201301e035240801103440c04014840c80803401850080410015920090001d1569441130010f0208104000c4030352401d0a6218010718210b581550b02c640700c00ac50110052240c0402c0080e121480b101ca40031400d41041a006500041780b14414161180c10692080d1400c110b220412200704450314000e802691001c1d003440740100e4110703c0c3c0e800210810400030340110742045091068035004020040366a001410208208038650344070b82061442c0e135604a054100d001600c60880a446480401d1010981d03540103c5000c150150040a0200400000e22104074562900b90400c030312a8000400f00740542c2e80b04601c1100440d000c500741d0016414201582c001400040d0742c100050801c0000003605481d1941b1041c0d4040300014403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 880830395 1250 880829145 880829153
    0xc03010e0c100507140c0f0f0a050108090c060309030a080106090b030c13150c030207080115050f1c06200a050d0e1c050429040605091f03150e01140d 66
    0x80740c50b000d0b0400c1d29003c2d9024248450ba88406c00600035901c1410040c80701ca8462401c500340c1d44820788021300d44176046161500656480b40002c0802c06180103101580816480d00c030b006510a52010000c2c680e01c8180d104003030443c03007068004004001d0f04803018001c447c0c0020850f07030401403072105030f516220001026070901e41150440d40c1c180e41c01400d40d032000340c0c02c800d00e01b02881c440d800741c500103904d81c0b605500325450074030f0300042c0400d0703107408028504107420000380d240301c00340011080c100c941d02c448084041d48501122055580d0840d000440f2085684400d44491010101e2500203080002800350281c8070304241c0c0c07180d4a543d1b00708244003c0103034081051003d00c507000d10110700d103409002c1c1d030481d20130303181c480e00484001c103501004c00da501c1c0d4921310101e000300c3c1800d003400301c1115250020403d481d0000c4406100b1001d16070301c43c50198800c540350342c003c104126040c01054021707425034072030303401060001c0040c040502d44091641080d0026680d5801d05025818 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 880831645 1250 880830395 880830397
    0xa08070e0c030402210c090c1c0b040e03040e090d021908030907051f02010b040e300f0a0e030a11011d0901080c0108010803090924031e0c03010e0c1005 67
    0x607001714040d8000307900081120300440d0344d41e080b01e011a001c00c1d2030364501c01c44c01080c3c03042700d049086600c0e01c0c42c0318008020596010030302200028200140700850064244e01e1688103030041c4031070a00360010094003e0003080024000b007014406883c02083d00150145107041c0160002c000754400300c0015a203100c10001c000040c00002c00c54204402a2410110300704000c1040d00015404c0c50384046190806002d00820380c3c540400500b00d910f640002c400c0c03002e10340d41090000414168640700382502c0c5002810300f041d001410940c5d03801300c400024001c0600c58890a0198102510803004034401e1081781e03480d002e0a003814961000c500d0340013100404440389290748507040f000082005040003034a245400700c02c3c0c03149140f40c4d883d0781c0041c0e40ca000b003c9003180d1122041001904c01041403840b444000399040d41e1a004500310000642062040212a003404000000b840480b090401c51181e58000a5000b0005030b03000d0034032191a0314210700c0d610301036000503448200d542d10440c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 880832895 1250 880831645 880831669
    0xd0219080c0c0d11040b040603020a0302060a1202040609051336140601090b0d26070204020706050a0b0f060d32040c06110d0305040c230a08070e0c030402 68
    0x1000304007003000901d03007000e0007180681130601540c6001500300ca00e052511901050725002003032155010329540c00c000540c0c0c00002a107041141001241a104449001600261820f074485401039424542400061101e12000100b07450511040780c440c0c41c04411110f4030316a003000e190802d0240001d4a00c801500d480c0010000c2c044420000b40c0410080341f5941600c0c01d402c41801003041e8041089419166044040d205040e0501c0da0400c1c600b420b91854070b01d811801c102c90902c3e03502c0c1c001804903048103c0c20f03210561904104180701c40c03288640c0c54900411101c03c14400c102d4000b150443c020384d4100e6601564450b214a040c1350b04946030070300b4021403a540000305240b40c00504a100090700c040715248030442002c80c19601800f502001e4100c01d4005001441450034100c000c0d000142042d200354038011800f09125004a5803800c892821940d26160001080240903d400240d4080400340c0c01c010000d00c2129401507000750805c2040d100c56843e0748442c00043c090344060 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 880834145 1250 880832895 880832899
    0x1b0702130b0315010f080a0b0c160f030c050c01050c07170a0606080a200603070807090e090d1227031418031e30030703020405030d0219080c0c 63
    0x40f16282d42c10301c6000c0d80103040e5a003007003030800000e0707031119000e69071142614010503028a940001c2d40c0310701c451014240d9a03125900380312a207a82e45e241e030105004a002e0580004041d09072060034460b04002a64404c107081c41c28600c2c1003103080c003281c1c80b100700d07008404405a498000d03400c02001000f400d0030031500300c10108400ca5855001d1540d641081c0c02c200d0f0f412214482c06645003000c100e9400403480d015001624645e80c0c02411902d40b203004001c0d00c1031101213480070580b01040b52049104d400e0320002804030b0a40281c01030100321b203004580040c1c030300300810100910038036a0420b504800145981540c100d1500d03055803c8402c00c0503860f400e80c80030400789181d0112440c900c04006054054442542181407001a07048511030210803c1c1d01148a40d2031441e85030000820380c400c88402d0040749170f111900385140d1ba00a591100019401160521075880c0c00d024010400500b40001e128581c000c1310801ea4a07204108081c1c80040040740b42c5420380e50500c4911880080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 880835395 1250 880834145 880834153
    0xa121a0a270c050c0d08010b04090207240f0b060c102703021b011b030e0111060a05090706050a02100203070e030a0f0605090c01020601090f0e0601031a1b0702130b03 73
    0x2002d4010825000542109524412066030701d07815405804540c1c140c0300c00c0f07901c82d403a0509000140000e540220411580d26145241000301d02e0410954450341c03041d92200464030281915003d400d0b0764000c800184522001c0180500c0d1507000501e00d030110308000d2000c21012101d00615800301046919905880c40860003101016404100b034040e00030300c2080c0707001e0194010011141c0100a000a584050074001d81d1b4000c03030f0080071491a0b9020501d09110810034031001242001000d54410301c2c8142c882091006c0c5a005009040240c5454074003541403168000d4000d54604040140803d142c1c1d0000200b0b030a24800c0181640002d0061304541f4414800d141c0102e05907030620723096510515140120f200701001107480d101401c0140d00900c4142d00702038000c03000300006903103032504903a2110318400e22101445100c2c02980120301c0009290000c107650000c00c40300401015030380100408103241b4030880000d403050303140c0548100700540c0300e441d01d03400205100c181d91585417007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 880836645 1250 880835395 880835411
    0x62a03040e010602100204060f11070b0c031201080c09010e06061204080307030f0c02070620120c06060607021507060603060e0d0e06040305300a121a0a27 68
    0x269841c0c286040760203a5003110025014941228124040c81c050072001403511040c0b808003d110f640035010701000358080c5c80b20b01d50b4036100169507501c0200d40d50070750b4101284c00a44550134041d071500501c0404068191301100c2c41c0007032004001400340341092511600480c00b15103452060700d03080b0b41050380071401030030b040c10600413603081112444000f0381402c0014500050500445201440b19001021000e0402c1000c4e250318862061154110800c0d4014400b211800c000d9590901c4460094030b5440c00200360700c5003413040040c100c0c1d01506003001b070400180c031684100460310380752859007034958005140c80c501034a015840079141030700b000c8020041c0303000410100075504850319442d00b8071a0b04d6003809040d0146210180198000c40d800103c0d041101681c026214000260038602040b1403103000c609410046803030001a151a220604540e601c1c800c0902030314012240b00c506401240c00903292690301d01402e400c103142c042c040c03034400f9110110200500651030090003800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 880837895 1250 880836645 880836659
    0x32301020307032703050d0e03091306031e051c0c0b0708090d021c0c050a080c03040e0a0b0d1e060912021e071e0b161203020405062a0304 61
    0x2000801d524841030142a0144ea030350540c6540e501000e96258580500700050014000010202070314025418001001418403990710031071034101c01d1806000c000344560071810070041c40c518054007040e201c140f0f50a034201042e40041c048204554203090819050a02942110003540040c0000c101241da40b00307000702e20f1381110480c2d1040344c807802244e5000240c40c400326914941900580c801c6d01c1c1904440103900d06c2030080ca065580103a0071204215600d50756809680d00c6100b071100507810110b001e1180c16210040140c004820240900804030f1050006142111000008003440c0910985800d224000103201103801d070021000c020080250a00c5480245041d14400050140c80480051101203440c105000365001c401481e44500f0241424040c8015982c0700325201c0001340001451a800b40044c111003441e52000d152034019450708031401c0304c1e40558501803500500c000d010796212102038030060400d40b06040c00110f203502c2840c4030b5044448012209000004011400c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 880839145 1250 880837895 880837901
    0x105040b0c07181103011a040506030f07030b06091e0103110409330e042f01031d030d090f0b011d0601020106060f050309010e0f0c010e030a020a03230102030703 71
    0x200c40c0a254501c0c0312844403d124102c0341c0d035090b0009501420f00044c030040c00d80031030210310081c401103910b03c2e15803200001800390308200c1d18a9601c5190004004070b182d13041c015403c4141c02500e0803402c084401000540d02414008082d40704940a101c8880e5070384603811000e59404040c1d200b0755259240d0007075901816400d01034108141800040103001001c500103040480c0c2102403001c1c120b41061a10b07410a01c003e003040d0741c902d08503081b0711054100c8102c03080401c000207182c0034040003107000140540304444100c0c0c43d00d9412060700c2c907201e5000b00881c0e40050303900000144684a51401c0a0320041d0382d00054465039030440046102d140d01d111603903203010120b040c6030316581e03180d0049099034842d0190364000340c0c010818148850092000e542c10110100010032100300c0700075241d16000810f4001100c5901400351007400e560080b000c0c804680058010700780800c01034001c10350a107001d1000030700450740e282d800052020340c4080b4200343d0340990000c0d50359040a020050103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 880840395 1250 880839145 880839149
    0x1206170105100510110a0210091d070801050111071d07090b07030c0206160b15011211090d1e030e0a050105031302040216150c0f020307030c060b0105040b0c07 70
    0x590720706404141c0c110180490300040b101d006280c103141010b142c60488006905034019401e500c90324800c0401651581c0a01c10301055a80c0c44680c0702d0710b040365881080318001911030341c0310f1024041c0a103141c0d005203034505480342130070300c0c12030741503010425403809038035610403000081c0e0419491400c410950007140121520350350025541d8442820364800d20999000401290300842d0140050802c00003404011050941040140300f45860b40c2101900c129071440b4040011144c1202568003c618105000145a0304011000100300c051710540b01d007180c841d12030381401610008010003500b55021040b4440411201d0040516001d420503030160b007483e2191100c4800803da6510074000c0d24410605888940c01c0c60540317409002c003d41c441f00030414410806540d1201040000e007143e42006108400062150005030004001500d40700f00f50017150030802081000c03d9204400247da00e0300a580020024100710050360244103d900010500401240502280d41c01041b001c007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 880841645 1250 880840395 880840439
    0x111190602040e012705070507080304380f0a06081b01090501030504030c1403251202070602030406120b04050a0914030f0f031929030a0c030b071206 66
    0x6031a1740c85003841c411180400300720941001440c6141e8503444060382000c0e03001400c1c1d0800510340310140e10341030f032154401c450a480045014800c0c1104911a24036000252800b20044882141100c20740a1008000e814244a24100c402003072040400d940403500800b4684102c5a0128554400d900c081004404036030125614820024095002e4011603203d0741c0d15a4950030003128543d00c1071170002c458091808588030a1184c900150b84a0100c40102d121280505107030540d989019005840c80b84d18000440d0884401044420b03000007e99040d0351003418a2840c04120310720550051264500043d4042d0600d8203200c904883e6601c9110018010120302460703003080e40e43e03940c1d41c1c420940c030b800b0605810009149401400009150440352008043d42d16005444008080d80d030f030101d080301184011000c1e40e0781060500e410301e40804054001d007010145a4445080d02d24551101400e9000c0e51030000c1c9015114104c400c07191541040104021038071103403a41c5c019260140500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 880842895 1250 880841645 880841669
    0x60f010602120906280306181401050d140a08070b100b1c0605040911030601080613060b040e0a030306170307080406030e070306091505060f010905011119060204 71
    0x21035200d101050418520380409009440d0034610340034800e40703501c01200c0d4030000c207440602e4014103410207550040a100c698010902505006014110342c14011070002001c1ca856040c01896146111040c1103c101720303075015403600c0070b0404201c10304107011030281c1801501100010004803401400ca0640119416060b03540c6000200c418810540121243d0030006e00c81e2042d89a00102174034811540c890010481603076400c00714003900c0c2504c600711102841d90852b1034080c24208021030040444400502e100c1c180480c2c0680c4000d810034015005c21344901a40c00341e9141c0342c1214008007040e504980303161142d810300500034071850107000003103407a01c00c0d90b1142d0000000ce076405c494200325903d1516207802010f0b80201400c18564a0031b01840b240000468154460510080c1c007135a081030303505500c249868100c0f04014850741c442c00c02100d210320607907401551401503c40a082c005125180d10074001d103081d805511a5001c40b1600c0315044c200300803074028100702e42c840c2e00c42d2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 880844145 1250 880842895 880842899
    0xc0109031d091801090602030901020d0b0a0303050d050c07050d110601080d0206240607080a0305101d0a060b072105030118020a0c0602070b040c05040612151d060f01 73
    0x90303003900d105101651161400c0c2c0070400b41d425503050101c03201210000019010019034401060760808c40d2881da02e81d6004c1100c0c41c3c8c4444c81d0082c061010400c03200c135078040c3c0c1550390103011401460500b4000d80d9880000401003142c171000c940c845a0428102d80380c188105400a102840380c0c5804422801800000201e01c0c400141c41b00100c51540c01610726507032000e10264080042d050032800c508003040c804d4003541c850400504495000760402c5545401c0d815025080d650060648100c1282e106c5c0c0410040580e10086441443c424064034440d8072014190300c003510481c7c224941d003200004000c0d0030803e003001c1080700f1110325504000d02d81e506610580d800e010900c20014488140d06200c039807a003195008210405441c10090460203c81d00d4410490300b146404a81100005082c0300c10700194680b200e0080800301d5051280d0b9050140000c207074120060002e1030040011840d100101c4150840c1c1b000442044d00e20210180d004802c644e146402c1c0d41c0811818074400c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 880845395 1250 880844145 880844177
    0x1106220503010b03070e091006060c05011a10030207020310060b04080f070b09240403080309100507120c051b010b1507030903030c110d03030509010b010e0a1a0f0c010903 75
    0x1050700b0000004c3c040c20a0a2501824480350103004140940034047c5141584032400c043c03090101030b200303564441c09076415618045007102c01d00000c060341c4207000d01c0c0d6401b00e5a242803044102c14a00d1a0241e140c3c100d510110785803083d203c12500c0100d0034120080307184a4284060802c8440070001c0318001c20360900001e86541d290b0103078440c0000f00b00040e030603030b00307003425002c0d5240c100000c0c00f0903510744404c00080582064000320b0301650004117101d05d041c010490401c807280c00e42c0c1d0400507818030b080f002d07182110003142d40b98480d80342c00001084a000f0303000c0c0c4075850302c8074000800c00707030030301a0141c000c216084510344501520036002c0d88142064055900c07080c0d06403511442d450540e01c064038540702c101c4040320606080824540c41340c407540800e4803451300c25180460399051082d4800c1c25120140c00e501e040040d0a103e0303001540c3c1c0c1c2c504910844162010480310b1300440c0318481e00da440b9400c07485049240024041000d1001544202000e9000b50b6407151055000c4503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 880846645 1250 880845395 880845401
    0x3007230c1507050d050c0304090e01022a0c040f0e061f0614120402040e0312010e180615061312050c040216060c0e0a0e1602120a050304110622050301 66
    0x8043c003264040d991445580b4001c0340101801010281124100b0790f4620584003540c0c0002d02042c56650045915018508184022203c1c001003d10100d4026041c003229a41e03071000d031000a221350340311403451300321200b5a48055494501141960b45900d4204000280d1400040c001ca0041800300c7d80002d20f2031003138103094240101d00104a16103400040d49850868000d4402e9900a5554400c001483c00400091404040d45089104150b14049072110400002400003950810040c80e40180130400301d600c0ea0b0198056503000d4081d085040400c42c02d02981e0f1f0400b641843d04600415a00c2c0a14400306030030b440b038400c4410044141d82840180d01881c03010780c400004403092440020501e070060040c40c516031911030a80588000020686807269112034002040700003404210802599a002501c90500040000c0c0701142c600c3d540c0c521841d5055010420040041410850001c04080c0341c41c00040903507480d844440c030065054a1441c0b04100d114810405c00251814180 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 880847895 1250 880846645 880846657
    0xa0203060c0405010503183405030601060c2a03080c010f18030302220b0418020909040b04030c061a040b030a15020901090509040b0403023007230c15 66
    0xa50380b2411500c444d805d900915000074016007880c019806143c6400c1c1148160190348008d2076000d0f00c500c1821080d0080400e450f400071402608803000500040340c000b09401c1c40e10b07902107585c444080320b100311510714904552500c58a4013900000106005070200544800d04110008000c0c4c030303028004031800c4a41c00041c0362900d0440000c00c2e0f011070301a5001d0b0404064009020280940c83c680038071080b002a0010240300d40d001c43d040c41542d41d0b01011103410345001e80300f1403820305d640c03000030071600b40100300505110341c2c1000901003610409040108a031701c1a814441d03d4840300c912000410848607880c0580e05d092807500b180d10740042c0034044c0f0f9410038110140040c1044042000e03500006282d8184494818001385035100c0c6100349100e039001756010045030516140080c00c0c00b0940170042045c105426803007820905881681e50a2020040340d155101c695103850145540c3c00c801c5101c00741018408007a0b4160003045488000108886010300c01c1840384113005a40030300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 880849145 1250 880847895 880847897
    0x20a0c0801090f150209150a0e0a03110f01170703060e061c1e080d1a09100603091401020c0706080c04180b061201090f0b040203010b07060921020a0203060c040501 72
    0x90f043e0003021a81da90300e0550741070401c00000d881e00c010748012030038400c40c005200300c6030318000500c0d0a8940e401382d01c2d95003209007154030195651642d10f4298031a266501810301c2011908000c0c0601d81c00b4a60007030b07001d10101c1c600c513003030300d022100907004200c0d5100701070240e10034200103040b42c50203039400751f5202c04002e00265007041076200c510500081102041000e4010800c500100740514041d208017102c2503004121041280342001008081100081c0607000710303030500c0700400c0314600450648015140c0040d803951941040c0103c03445210f61194254030004148424860100e190001d4620940b1803101c80d80b00d030750941c18144950b10807021709120f81c61684110740503a030404004804010210744c1040a01c22640c81211400c0c1d1204100e240c0d0b4200c4503000d202c1c180114000c544017120114110340c5004031241d681e200d4144001c0c0b00c40d0392480c8150070054075001c28201444102c0c2003020180c1c480c01d010f503075944404000e074464402e00b4001800740440404840584e001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 880850395 1250 880849145 880849163
    0x9030f080411030f03181c08030603030f03040f0308091c1115100608071d22020307020d030515150a050c0303160f090b1605010209030706020a0c080109 67
    0x5500400c84000101a000300d415840700002c0002a540410079040d003461084051580c03801d09210500a1500b11040316014051149800b19024484c4400381c003110340040c000c41e45d0f640c0313541c000303420f52040341d4800f02c0c084008814482800700628601407542e200f41c45201e03040c0c4442440c507580740c84640302d1400310024002c0c1c040099120300d031131020341841c0300100c0d02541020769445c0600f0204580300102c1a91402d410005e060b0b0009038039810001906101246842001d200302d1542c2c19071a007140202d910850740740b0918a400508041c00c00c0441045481c1d09118000130744821040107407a00003414440400e044100240c6801c0002c0802006c80c0e140c40346205a605690300010b5000003884028400359410032018001107201e0361031450000001012150050710070001c41e2103400410074001001c1c40340040950032120300d41040001c1d641180b41601e001d80c0680300704c074080d40e018000e4060020b21160000f5000801901c9041c40700801600d4081c0c96003290745a02014102e280 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 880851645 1250 880850395 880850417
    0x1030e0a1104090c03150203220b0c090d0501110c0d03050903031308120a320c09060d021c1407050724050702060708090d05040311010504030b0f041101030903 70
    0x203032035840700c1c402e584104005002c0d0703039a0391103030111b00303d44010400030355400204000c0310f401d0b11072101c11450b040003851a0503016a888103c21003000514545602100080c01c0b0030390341c1d918076241c080e15440310082c0f010742d0044002e442190800e11305594140b14010306107100791b00038014240315040b01c1008504560f40d44030417082c46070540c44207582c6260100030310240c02822070303826407142d4222200071510341596500b40c4205540121561642c800749904040010204540140c12000c00c109158507541c01c0c0000501c28403c44586075060382c400a4040d44401e41501150350194003404100301100d410740701c1401128023290041d001610801c03950303001807404c4040c20003035220010300110743c0500c0222601105c0082e00c00d4809607101c201041076840e442020540e00c07100320400361544600415024055005034000182a8203011002406c180d00c904c1c02d4400540c0c101c0c0c520049400d1443d91400500d8003030750300f13483c145114040810706500074020803110aa0680d9200d400003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 880852895 1250 880851645 880851649
    0x20a0203160305040308120114040b0310051f1d07020c031c050412030804050c0a1406210f0714090a05130b040e1005010909050601060c2f01030e0a11 66
    0x80307507444040b018000b05000100c0840d01d080d001d00f49070180118120b1455042001051048940442c41481a401d091468505d41c40100703c20140d0180d42c88003040d241c81d040c2d0b41d40e0300c01c502c3c900c00030840d88038001d0005000f1607980000c5940e18512607411200d40710b0307076400c076160000d5014164041e070200c10642d05910b45411458040c03102c0c3d1130300c1d07070510791101032611803580b803007409800040320b220510080c0f05040c006050726100848031056107500d0f1480c1354054454800e0800c1c4510350101c1c82c05003544084100c02d0201c2c5200000e001c02d0318000c5582c006200e4144d40302000110400c0c00c0031085400801190b240090003000400b800b03250404000c00449280380c0005610740f01d4180c0150b503111801025a1818210301400f8840c03a807400800413074038160701880315103040007010000b14001086082c1900c3c400e00e00a24009494144003255000e1001c0c054200240d54003416860b035514400d100c55501d00341d03402c2c000a00440303c155a525180c945c0608a03100c2d80000d10014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 880854145 1250 880852895 880852927
    0xe010c0f1706150a0c020a0e04020f120c060d240e0c0406020c04050411030a05010515030106030c090c051909030c06020318010e03011e0b100801030b0604051510170901020a0203 78
    0x1074406182c4082204144e5000c11947c5030790341c0c003038200e101c8144103010462604110310103008000f604e030002e00d4143d071a1100c0d86c40348070508503401690005041c040301080c90b00442140c889000c0203504403961010000c0514010340f00b035943c0400c4c5840858480b1580800300d030129100c550052660000d0700041000070329010300102c80401803c00000701603102485107000f814024400020b10f8903141c2d43c942c0e0b80102140c00c052299140ca80c013400062001c106070700680305641d100081d03c00101006131601d00c00c1078004450b00002680c0701010a0780201c4120940e80324019401540b56112004c1e82d13a402607a00070a04c0303014000c117800d11075121700700c40c6a00c40130050001c40c683c2d05c1c0c1515404e010b010101d00b17001158503400003600a040100502007554040c2c50407010740c1d0b1454072100c00c035a41c00351440b84915181c202041074000d41c40c406e5903625900a251071501000c050029011088009400586981f0300000840040c0f041c030a840000c5410f4018624224000501c2c0d000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 880855395 1250 880854145 880854157
    0x2040905150f04112b06060612090206040b130f1413021215030106170123071215090507020606032806090c090e031b0c0a05090a0e010c0f170615 64
    0x70200300070340c102030448142004907400c0f03401103100040c0f050034500003c9c080c40300010fa0481860a24455400584031001220101d9500c405095200d440c0e4071442a90301ca0141d100d140c03511201c20011800d4500322200c1c901c842c10032140d9525991a01c0114020f0b0b0090050240259001c0300000742c10006804007480704030070050000440c20788805500003405218068030003280e559680c07855090f014403450004080e10f0104032985440c0c0303200d0043c00c99128a1442e80750135181c0d4008500c4040c2070303010340c0103090780050501c940d00c0e240d4402942c1d900c0444d41d40d41302c0e20480c0341034505414107925900002c509280b180c2d8072050303640c9a00c405400c41b800202e500c41441100061851a0303441800000b04c12200616a52003600400303601c804580020408541c000c80c103914666512542000201c0700181c410703481d56520b590f000f10041030f80c4ca180ea0640c0d42881d541300425507010404286074021612446402d07c1c541100b81ca20702021100790741c00c810721100130114510a5000f44c24 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 880856645 1250 880855395 880855429
    0xd0b06040b04060602070e0618070c0519030323070e0d0c032a060801053604030e100c1203020714030406050a08010509041106031302040905150f0411 66
    0x5000c11201e0086400c40d040340d0722200058106003010b00030841503003000c5800c00b60407a2138020008003d03200c4004031001401840611194001090401100740f001c1c43c005401203085000100d02d505000d40a007840b0f01c00c8400c2d4000c2d9009403029050003541441c010f0301d07030740c1d1803060f400161014001c400c2c880c650b041d00e00864451001000175503101002039403031800c6880009044561a107640110143d4000f14140700c2c5e83c400610540e180c8100c0010340e01110b00301c54680c15404c56403401200d03c224809510400da02d420030007499001041c1c0303030400c0c00a80740c00001a20b029002c07078414802e000b00420546040252110a91003a0040c1403600c1c0901c60020101040f100300c0d0f441c60b40294441e80200e500410b401e01d034a50040f60f5a4014401907a05000f58900b59468100b10101901c08034416140400032902c24040c1c1c0000d0302c021680030303008200c03204c000e0030175943d9072001c204080c080f0304080d00001c030901c0080d2110381c02241e003c030b40031901c05200d070b00b00b040b98607500b01001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 880857895 1250 880856645 880856651
    0x60516032003030103060911010206070e10050d0507031505060f0d05100506160b0708360304120b010f05130e100c032c1509010f0905030309010b010e0d0b0604 70
    0x100c0c2400c10b0004600845c410100000c0050081ca00007069001803460281950001810400304680185401400c80c50031150080c5206c0c41400503101030007001c40c1e0251007890b00c42005111505644442613a02008a1104145540350100501d500c80c20820075000b01c0c0030711882000008641285820900c00000c0380103080d03d078008105507800107010510740301c00c1c16421800340050701c8007058104c030651030141601d140028000d581c0c0300901446c070344009941c1103d10502c5803820504104021401e00741c0e503995980307044800324460689015140060840300020301e496502090b641103820240c030f9403514401c1c0c14540030040c48881500e122600820764850040b442c20312440540f6071064500040510f41d008201c2c40f031482c4211030100011804200342c0892070000340d22003070f6000040001c0701503a903031000a80500b0800e050490900e0605600104000001c0042d61181c41000300030420851a0001181d000d03030686000f940000c00c1074461004520030400880e0310881c050004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 880859145 1250 880857895 880857947
    0x61704081b0312060301060e041b0503060c09042f130f0306020c1b010806060a0908030316110a021e040216110a0b1218070e01030804060906051603 65
    0x644101501e044aa4041d0400200c1c80d0309901401201504520b080d03000304207c50504440350050720016002418000d041038407121210352140c07c00c400f030003028040d2102c03424928058200c1ea007000c4081031255041c80d604111b0510400031600d10300c07805041d402148140d0609020700c1c0e50001011400070150180045031014850103250000d62041342c0045e03a03015075400f00340c00d2550440c10080400c0a42107904400d03070748460410b40061080f103c1c03580e6500084402d03111034016500c1144a0702011040007900ca24180364422181c1c00d54a91117501902c44a600c1e48646142c50b009600c40710060079021181703102c100c007040346803010f030005181c0b5910010605021064a4003110380d8054000d0040c0380341001074032640200b501085a5050410580e1350310400c040040102601943c0b089403020b10100402100c4020840011038034110350f1030b4180002030703500038081e0780045482d00d2400202d0314030075400c4078200401e440e0002103030107803a94100c4a0b8018510407001184183d451 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 880860395 1250 880859145 880859167
    0x1151d0f0a0e0c0307033e16050307060b2b06180c0303090b07262205030610270209041e05010b0304021c060207060203161806170408 59
    0x10381c500401d140c020340b0391603141046004043c1e03000c6000c100b000d56201081c0d50011f200c02480302d02803000054420700100c04001a900042c014902102d102d0824150310303d0600a012000701285401207406009140950b000d00003034580080304416203000d0703120380002200120030701041044c45280b010038200303800c1c000d144800d242c0b85070a07500121540000c10030180c0104414008001190380a814000701d61140001914900741c21100700c22841c0e2021074102c0c050301154502c0c901e0380b1407506109000d00740702040b40d03e81e0051500a01c01d141c0807030900f0551028001c216012052500003002d0f880c4034460005071100c40f8020001e4003840540c0c0c2540d2540141024420295680240485206144400c1d074078180c0c406606070804000707120241c0c0794800350400840f80b070500f400c444800b6141450092103026406404d00d0320210038000c5042c829840440c00d420196141803a01d65182e0801141e1185840f075030b0049424080d10060300c900895951b81c0c0300d4080c04c0510308001030914 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 880861645 1250 880860395 880860419
    0x10507060507020c1806030d1101090503040b1306021b190b0409091e26040f1202040e011a120307020d0602030118181104090c0e01151d0f0a 62
    0xb40710005a04900c5142221303003000100303800c401d00090304c6503007503090040c042600c1c1c035407000c00d48041041c0340c0d00826105000b50014003040d94828126540e4075950740702c41d00540c02071814080150450200069002c0c40040d1600d002400b413948031b502c22a41d0010450000c40119001d10b0f0400e244200107a000101009040248035880d40030421200d0707807a0803044112410006085921403403c80300c04564003c001c06414510b038060320901c8403a11116031054019a031040a1420340d8000110741c2410910201115500c20381b001d20050592a56103400c1c1c42c54526207008017602145040ca5900d040a08001c0c640d066001f80d03483c00c40550082036041d410307a44240e40c00c40d000801003061512500302c02030b18659541c030410000f001c02c000054810702070f01d00a03040c92580980494155181e074440100c1da07501c000d620340040e40da009412600c0000b4480e4641c482010b0b26810000c80c040c200310a8440b80c80c200313400d0141c0240e01082108085455416040200c46501041440c281c217 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 880862895 1250 880861645 880861651
    0x1209030c012d0f0e030a0c0504051f0803040501030f140c09012d081f0905151c060c031109060309011d010902210303070e030322030605061008010e060105070605 71
    0xe550f000400414020291842c001c1e44100703030090b4800107030580840c10760702c022010f03108121408602500c820246c0c00d40c030307030b0828561000282041c60004400d50f000000700101c07034081e01c0c140404185402007104991413603415920700010100000c0000d40800010002408141803803c110b01d02445000340d3741e0342d900901c3c6c59503c00c4045002c125500310422550020b1005c0780040022007120410142c000fa900c41c0101e4241c0382d10100b80460311140990071650000f4107200e41c4a6180c0900d4094003030420003c1e40e50500d02000d060286129000710702c1e040480d0700304d0300d1600f00b61034103102e02070b40f00502c071050075581c03540801a40303101d0100003d1946c4640001040c0c44440e401044000460381010442444d4a81c03500c85604e00d01009980e880f90a50500c145a9004100420b085208030031816031500191031080015401080140c0242d1303000d20300800035a80c1d00414040000003011843c5e01152418004101c4205481382195100b001072501500705121907a0303c2054503015 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 880864145 1250 880862895 880862897
    0x61f0e070c02040621060e070b0d0c02150403021b061801050c120c15010501180306200c0d02100b090402060f0c1207020112270201022506021209030c012d 68
    0x180d00e17010140105401203001c001844400350031101d02d000c2d041200751045c904041002500d5003061044c050091040030540b25059041c0003c0346054036000f51541ca460841c0194118001d48400b1340341416010368a101e00141c1d0740006809122006607002d4202c614124001d200e07800800f4512421480509030202d1031300010041c144001d0203040503540160885130400400741d40c10391406a51807030741001c03690400800180324001e02c10b10302a24808400386070303901d000000c4450040700001403480060085038240c407612003050001d4816034100206840d4002d5080303010501614003031005001d000a00440940b403c40000348490522016000c03602040401059141c10b65030060601084241000c000300711050011820892403083c1c0b01252940708a8600a401164020005807588006007400c901c0c81841400c000f0400201d280184001800f41011103101e07c01454180d81034031070020301030100700000f900111060064102c14000080d00c40448412018810381400d07202006 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 880865395 1250 880864145 880864199
    0x3020102090a09181e0516060917030a0f232109060114180a060f1707050603071205090601140a05010c060902030a14061f0e070c020406 60
    0x481c410401d030300c40180e00031222241420b050035404c02420f2807000d03000f40e210305102c842245507802861503004a44c03004109100d11003910341d00c0c1d22803500450485501d07503188000c00e03840e800512484444414400ba4036442886101d03582401400b20845030b19a910708400c0c09040755076009502c408017420f0842004001a004140000c01c06804000b4441c3c0d40200d000c50070031950301d90340d500d01440341604a65802e069041e480c0d4030300481042032079440321064140c0c01c204100034010301c01840358907118200040c000a0807172003020b1480c0c2c0d02e07009102600815152000f801550b0740002d040d9801c02070342c0100e501c508a0b45200320307402210354100502a541c1003000d1180f8200000201c1791040f51441c004004582e880240b001341c036a03006402058030003042c408686001102c80e0000c00910018450020800d8001580d0b403050281e0001032401c10810790610b03000240c0c0b03008170a98040507074009100203020b5078181c032030148003800015025507a5448001009404ca10401103089 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 880866645 1250 880865395 880865407
    0x71a15180a050709050f01110102161505160906030b0d0c0b09040b0301180f150501240806010804080304051002131a0a05033c06090a0507020c0105071b0303020102 72
    0x120b4411254030a180382400f0001609080000745c8080513180c21a04001241e40c2e00c40b0f5100080d015942c2c008090002d2101c83c00e1039140080036000d001c200c11241c20311700400641c107079070110750300304003c0500c1d202e03004039600303200c0100c02501d101415a90010b4040c80b0b020009594940d4810040c925411040d031500b40b881c2c100000c0e0f0f52882d2020b0310aa060111860031609049010002c150b440768025aa0748510b1a0801c03540d03c0041d44c4150280c9490300000b01d1481203442001d0307030400e40300020980003108078151103903002601c5007800100d0070310000b80018a080c000310b03000707405138080b07943d6010301644460503640400004a01441d07844010010149491942040407001283d5142019a00580100b4070b0200800c150500606000c046910401003103501403800560000d5400310380c855206140c45c15010f0707502c540100d200707200043c0c48158a100e807500800c4558090b044801d01c09004403080d400141c42505d41c603001d00d0743d03200b1b407810584036200107500c82d40026071200 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 880867895 1250 880866645 880866661
    0xe0a020a0e0904020108010b09030f0d020a0b01090501030f0b0403121d0708030c102003043002210c060f04051c020d03110415080f0a02071a1518 64
    0x541d0000c41c00b401401d01c2400c0c04010307030308100716905640814040c10349850701d03032000a26004165800b40c4c801c1c014006070a00741c40e800709082c5503031350080c60000305990740e5601d10b20449109203c09000351285540d61000251072640f5aa003040c0240b50003250740309550300000c2101c2120002032800c4214180d040072240302071000c8001810104043e6044c8451003d145071034070498205c00007030682d034032610165640f0074003204407244002d15500e500e03450305181002d079409081c1c02c40c0010383d09581615000340c403444401d10311a812a03000d0542e03c4141a40180310400e102000e060303192080c007219003801c0701080031303d101d030b504108a0115800c2c42e040c5035040c135440c010036111448402210340d500f46d400054031220f03d209490000303450784154610485500441d0001c0301e455410b5407403000c000781d00040c41d50027084803410703074402612454040c10807482500701c010304240c818001041044807004519901c107070302d03403640e0b5420621080016040c003080f960b11074101036800e061201e54 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 880869145 1250 880867895 880867907
    0x4080307121403181018111807020c040516210b060a120e070305120d090c080606041a0f0906040f050906091902151305210c0f01080c0a090e0a020a 65
    0x1402c202c174000c1201142d80f04800f0005000c81ca005422403d91406822140e211010809070014081803030070300701e06040724000c2d21030919071425841181040c01042c0410740310842c0000f42406034440030324011201d0325806a400c0603001c00100e07144e80b01d151440b951070741001407840d0b08c0c907a513031101e00300d104c2c1040c0310844286101c0322a055022041c02d100292000440001081071500415203034540c0400e02000b50508400040003100446000506c4841c0040c3d40ca0040c28115028042140c1d0b5074034560090340303c0e40b212940032091401c012214200301201c1c1c0d41151000c0c02c04603043c030004240000b40c1c3e4068491041580c4103004100f42040b043c048826080380c1b009201d50492041d800281c03c83e14440220a00322500052207102540d50030000001090060540c00000743c0180c0e0459401c40b58030310001c958001c40780102c40070b141c4461602412003050319042d040d03496503c5d80c405250803480030501841150311000c034040e000b07543c9103403041e000c0c0710015035100c04c200001408 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 880870395 1250 880869145 880869163
    0x92702190305010b25110a1203020c0922080d05101a0301060c08090d050106031407080f03192c0f0607121b1a0702060108030408030712140318 63
    0x4000002d000403500c0042e41e01810742c1c0600b03845c503811031500142c20404610603000e034426901c0708441500081d49040e4500040102c0d01980070b45828100079018481c03410f10840b500500060f84d081809580192040f8210145010b80c40e040c2c1000c1ca5078104100312101a1750b001c140040c3d40d6004c002c940d1001c40c081c55400b1070013210710309651510340d010b030440300204002403001d140800c50030b003503407039001050300d0b40381e005002409519500c0c1402c00e85858419810b2011f40201500070680a20004002e20502c01c0e48005528001990441c6031002d10110082c1e010049118230000d14848081c0c1b01d5200602296207641c0b2404042c401c100000f24000700e118020f8109001130000324940c11810041409641400220140c0c0700c8051405104500c8000b000094103845120010704104209489405a6021600c4a9032541212581c900a9100c1c4080680c000c10203400004c00c00300f520391201e20203060484181110103460001d41c0c0080342c1040b003c150070300303101e180c1c40f00030080b05017 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 880871645 1250 880870395 880870409
    0xb0d050112050c040506060d1e0b03010209031e0a0510020c0106060f020613230109050c0301060e0a020c0118050c03071401170c0c0d0c061b09270219030501 69
    0x1c0c0c40840e03566460b1644490342801e0300c04d80c2c4d101d00017265a100c640844006801d20101004034112842194026070b80b43c00d0400c00c03041c60583e1010403030a0510071180740200007401420710350604104541240490a403801403070080c2113401001880411003d50386095500c40540c407400b80b20705c00760841c1c000d94401d80c100030080c014800100e40124031a9080034040310030141d400c0460030880c425a183d0005021010380340c011103507034114103500c8081c00324401c4045e907140342c084a04060903101c07580a600143c81d00381c1c0110f4015211a0f001703280c41e15107100080307007050400d61000c900500d0501e040e682504400100d492a00d07051001310090500c22240c00d41c24094400000c0c0400002d07101c6480121041d8003040d403541900c400d807547c01212104641111103640070003031024041d080d0440c0d625080003110003682c004000f003045849050756031611000c5c600700a8003a100020003007407941e00c03445500d025154615000a00441c040e454084025070518030004044501c1684011 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 880872895 1250 880871645 880871669
    0x11d222402070308010e070c080d060e0f151e09010e010519060e010f09080132040203030703120902090103050609161406131707090f0e0c0121060b0d0501 68
    0x4000394120b0a681c5c151540786400052a40d10f0a01c203885001034010050031424011a42c00c18010082d0418802d84a542c83c1e0340c0c4044c1c8403014503928070036042c0d03140404040e001c0500030300c07401c001215079280e00705c512072000d0b14045400416151a02a0800c0203a440e0700c0740148140e06050391191201e203041c80d00c0041c0300e40780c880b004180b069609425810044030703a03010380c2124424219040a802450020411030141d00121049080c401c02c002207502c0c0d07103c0541c4070079400540e4040c421030f0064041d40c1350480e943d408550801c02201400c0d991a0f862050320056160061201e02035403150005000301d0508074101c910b0031840c0821902e04040f0f459081c894002d81081060040c9800d4138029203d003c64144000402e0940d00401c1082149001044a40d200060050b0886540e000108400c81d0448040c1c3c003903415503001143d0541c0300183e1903101e544915204002d42668400b080042010845400705403503043d401a000340c0c10114050074011074038411640186030810030300d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 880874145 1250 880872895 880872907
    0x70c03051201120b1f03030e060409050f040512030103050a0201080402040e010e0c0118120b07030209060a02030d06050a03031709010b0d08030103140a0b041212110a0e0405011d222402 81
    0x1217a02c410950000034100706034103590710030a80f075442c26a4007502015100380400e280408075950070300703821030302503031a40f082101200e16524a081101e050304d0f0000094202070199030019214001c001e40226042035a600702114500d42c203128903c200741c5640007410070080303034000040114294444c00c2c004d810300c41504001c44e03940310312002c0b143c69101960b070420f80e450301c83c00e400234040e00d07030501d402c11400a54182d9065011005019044282c142049069200c0041c0880489540401404200500f888040240c15000322551200541d000031540e07a0480020900c0180d0320b6000701c03058800400140b0800c81e00d00122044500464020107031410107445600c810407014001900c09001c0340c0541c5121441880d120000325551802808548040c02c40841c2951283c10306000058020711884079510b01401028101d486d151194028030b00c01c00c61940c106d00300945000401c0b08101e400e00000b10b140000d00d69203900465031541145503002501c1014800d58440c200450310401078 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 880875395 1250 880874145 880874191
    0x60b090307050405090f01050f0709060201021608072f041a060712020c06040e04030e031c0f231308011b0c021801080c10020705030303070c03051201120b 68
    0x4003265022940484c180d1661004107041180c1c00c81582034039420101041306005406031024003521f466a94016841e40d1031500b00d00300e0203921075942c11907070f0041ea49004208660f01414440c1e00072290305210380c00d0b495900d540711852640402034882c43d0b00d0b03031811034641440f0b203034156000240007a40e021111000505144118640200040042c0308803100c800e108006404030405c0250046a48230345a03100a1100c100c00c03501200081e00343d00d41030146050119464103c105510049043d00341d9014060350914902e419540c204042d00350403041488042c070764040d0880c144c0c07040300c1d920080c0c80100080742085802034002c507070601e00901e001503c0c203220350451207a00e207042201c2000318070005014050300d6891140001c244000443c8088010501c070f0900072045034010b01501841d201170b41c0314002c921403558160418800100307098045d0740524000c521a1800030320380a11b070501c1c10804031003030b0030804040780184038110410a400b0403464100550b80c07143c075035840400380 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 880876645 1250 880875395 880875403
    0x6180f0c060f0708040603052202030c4e15040b0705070b0a2c1e193203030402101b0302210a050d1107060f0b04060b0903 54
    0x1100341c0c01500c0001d11115580006420707a0350350782c0e000c90960f81e143e9840381c00a001c0d040c01e550080048281604e145844100340081440d00ca0740070700030b06400c201c03400400c14403d1000340300840a400f03540702004944561882c01080049151034070303000403491016010310490300360029071254001d503910503c00d108818800d07071042d409a105441503079032400803245401414402040300040c030b018801407a00c990401d000601044c120702da06c9505d0b1212040000d401e14420f034207541c00115015008456010801f075a007000002252002a000d98035251000e42e424425905410b981c12102c1c010310003010305c06000c210840306413044500c0751940320b480e8071010304001d225148180032601e2082c040c2e41014981c8001e110000e9883e0351034103001c0d40702d10201074482d80300303030350142d8000080842400b6186001382c1030b9259402d02c1d940d004090f000f4442c9010581c0c922000380080000120503010340c00304000a050302260740002d8009000070b9816030b402016440505121244550300e0000f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 880877895 1250 880876645 880876663
    0x10033c0c2607140f130b0301110a0c03110109020d030c0b06030606010e010309110909030a0e030615013014281e020c030408060a06140108060102031b06180f 69
    0x403041d11550711020f80003607413407000b0b02d10741c641040c0341c03180440303a254865000d0690b00354140c0007404092403605422020b071180082120110b840f100301000441c3c07080f0303a009031a680100001555240980000d602811203040440000301100d42c51030810040c69078043c1c0040042d00104031a003041c80002c0c01d0383c588a424281019a2607908000b449400c0e40000180711014004ac02c0754200004403648a40c0224002c0010448010040314503080026904c2e118034500c40480c9032004105004503030070081d480c550801d801002a2841101426095000310019440c40000d1000b1440012601c03070400140b080010003640742c0110240d81a1503186401070141040000750340d00d5800a804400200b02e0794010480d1000c15044a14007000000b041500c8044040303d545944401c000c506030355060040c04030394074020880407450750258030501c1c2c0142c0d050050301e01340241c5803606002040707003440410095004400740b00c196440c4665410b4540d01041c003a003005081c080c00a56100140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 880879145 1250 880877895 880877909
    0x12c150f01150e0d03030204051203070c090905030408030c0304170a020d030f140c07030201081f03024605060a0203032d07030209010810033c0c2607 66
    0x110380140b9229208007140205198014201802e22403c0e0038018001e40040c01024092051205200301c81c040c00000c0d00c1d0410b40c8002e40e09540c5007881c03950303c050700c13010908803107034030007400f0108404ae02800980701500e800c4d001192590301d406842c1c00214249640c03140e050b0008030030715002da11004255000301c0d03014181015413015420003200d00300c44c2000c83e0106850041200ca4030300c4c80c00b00e03000013142d000b43d03140c124513190f941c00c01030301da107041111500009503040200018208000301c40242d10084040303d140c4446440a142001c00040c4003018004a05001450f03040c01d02c180900601001e468980c1005241c940195507480080c040940c0c2d0f0800c03000800c190070b11210000ea1140040100d0b566904010101030040d401416581d40481c000c0380015040300d000f007142c142180d82104480d00050818002ea107aa02201e01443c90013a420101c2e00d4816542c60310783d00c5a00c1d11450b01c881000d0f10b081024100d1150002400c03400d900ea003050343d0b11458000440b401a20780d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 880880395 1250 880879145 880879169
    0x5070c030e1219050604050607020d0504031104020d0f051b0a0c060e0708030a181505030c1c020c0709050a02030f180109060c030e191211012c150f01 66
    0x20100c48540f42894031900c8800c841a1844a08204800801c15038040d034400c100715407503511400003d030380340d00c0c601410400041051204001150006200c0c00c04800007602c0107140290340030b8110183c0d215541301615143c0c0321001e00048025600110395039240500b0701c0e0f800c1929184d00101101c070f000101a1a07240caa880501040c031091181d10000c00c40a000c403a640e9501a03000340c1060090082007240d0080482c000a15070721910700841032107031f80c0d03840383e145564411442d119a0003241c3d0044c200404285440c9107100284000d00074840c20b007006003004c80c82d1038552404d135075000707003062070203070051062020030300c5019143d0742c001189007600c0d6800d20b10441090300400e00714401030241c5042403044c12040341c240c0c0c80f6000f01c4510b81c0540c0d0f4440c10682d1403042c160042c0c0720060400500c462410ba0162199010403038280b995000440c43c000d0350390518040844a503c01c1900005419140fa03020500700111036150030701404403945481c00c1502c00d0f40c5044140321790000180c2d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 880881645 1250 880880395 880880419
    0x170408030a09050c04050703090317010b03270a05100c0e0d140a0b01090b01110a110f0301021b28170a0c05061009110f04030615052205070c030e 64
    0x3d000e0000c46110800580b0800c4549455000203015045a640030ba01060350103508003010341ca203070301b0f0f02e041c3ca03400003040c6e207580c454a40c003440c0012108601c40c07003881c00099884008105022980c1c526000300c006098001c040d410003011581034914507824000702182c1052280c81ea059221115034000311200b0608010f4008541043ca0810b40100380c1c05820002082d03030380e5079510110203d00c0c01c0e0f071020110b007200c820065850000c000080d2138415590100b05644c81c108483d40034080700a0005801c0003441c182c482d603194034110f010740c0d082c2c01208400c80380542c520380b07803040d100003407240c400d2150480e22007400d500c032244110b450243e000100c4009481c016401e01d0801988101114514034112151800103445400360b01c2c0751904190590502c0007800d0250b070340028185000324580741c81c2d596010300400c020034120602d40c50881000980b580c031000000200400480740a030f22203c101d440c1821207100800100034800019045030210b60705c1561003001034015a0201c4141c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 880882895 1250 880881645 880881653
    0x703061205120c150a020304120503091b010e040e07050310090305030f1b0301080c010f05041d370b09010f061b140313050d0b04150e0607030b01170408030a09 70
    0x1383c000b4500001c01030000c01c4c018064a0fa900952069000701c28603022500c1400c002c490b5072005441c440d0090b40914400316090b00d2600000418a0050400c0c0c0303961941e40000c00e0a40300c444e1121b600a8200340410025410148400004003100750f00c200300e404d10554002e030542c000038050210b0321103c1c00014854030b90b020702040e5030020508803a6129a995800c00d541c0340b1440d075120740090b00a100714042c481c0580d080e201a150600c80050070409103007a000c1460200801070300c24490002c01072440c0b503a8050718200d4100010381e55030001100c014440e4156007181030114020003514004002d1541d8541d00003080d50351902d0a41021030360055418030329002c880c0c2c050b0220421015802030b00000000400ca074100300c0380320300c0015940b9402c000c2c848091410103018881c071103001800041c3c06450118202040c098006818045100d125150560441e09900844c2d9185070200040d03030001e1100521221042840d8054030307050360f809a05000c06000c42580644502d6200100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 880884145 1250 880882895 880882903
    0x614130b0313061107061d070501110a0b13030f081005010e0315010b040501120e0307060e0f07271a010f1205040f06050609041a0622050703061205120c 67
    0xd90000c0013801150001031066138594031840303040f81e51920f4040130101a000b0341425500902c5820084c1482920388801951401d43e803150344100e9008040070340c0c00040590088a0141c02e0314140d00d03005480038075026020320004021403061001040c2088000e0401d4809001a10401c0c42c00302c1814480344086454000ca440c50410f0580c201c4001064203c2c04c3c0c07014000702e6000341d030307055000c40046030290119000b581d66503003203400421460010901d26000406080f04200480c3c1c045441d841449045c641d0303a400100322690081440c1c1c4099040036400011100303c00d10030014804091700455400b500130390854180200652181c0c0441e004440c40640c20740078140034001031030285800d0480b4404102c0171140c071403514001c222a0b042804046110fa80d1241500380008440c5001c02410000202100c3e4401004440c804210492403078115000312849404603080c207225601905856a5030003900e400c4480640a84c00300c3c0c2d00103490700c0e0112000b80c0c515901d803d00c0d0318090030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 880885395 1250 880884145 880884181
    0x3030c0a0f0c03050a050c03070909050304050d030c050d02010207021f08040f1712061311030f0406061d090715090509090c030a03091a040e1501030e0d090614130b03 73
    0x24074080c0c83c845c00103000e0041180d143e100411016100002c0d101d0b00c59000f15110b40c003000e007881c1e206201c1170003541852000c0c0034020740a4105241c0d01c2203a5a1031034500341d10f480c42603005035000b2420000314244095481c001580102e00700301c21041215005041da10014801f80c003c0080da4415420300582c80c1099800741e00c0306440541d15803036003011040341034054900a008005440503550100c3d024403e504c4005d04180003546107803100703040a031004d0b40181c020f555440c2d68406c00180c50301140911080b45089a01070026490310744145800d08405603c8000c03c28142e100c3c40c0c03002d03540906110161042118040038644400540600e800e8000e51042c3c1c1500c41c2c511001c0a043d004400300d0221070301c1e4060a009000d001c0c1c040562030085200300d416404281380812100710103440130800300481854001030400004284c1031070108441c4142c404119054814032450750300144000c01c0e8014810f4592514800d1400800ba450032403180802e0080044007090496080e01b00c0014 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 880886645 1250 880885395 880885403
    0x20d0303021b030c010c170702030306060a02010b04051e160203040b160204090f0c080d09170a0614010f05060415051b03040f180b0307060f03110310090b03030c0a0f0c03 75
    0x10312240c11100050082601c1c4821b200441d00c903280c000034012034006528458942030f80a5811038844c041442225005800000195503c42000314000d0300c1d148150303845112210301c15104581d0003080902c26030409400c140c0c1d8042021898800d00b9000002c0364126400003030096585c0ca603c0c41da0103032040301818003c0d481070600d05c101c1d0620040b41815818903019480c00d10042e030b40c0f4200c1a03600ca1500415901042c0b00300007c0003d02e62040b803a19803082910300742e901518203a40d0702c80454444060b0040d40340400c80050001d105280c40d500c0203040143c0c1d50501d018140340003024288110100311040190008060306082c1172020140c90040070f400c1226142e0b620750702c0d140400e1809000705041c41c0b000b10110000380c001402000341c00c800c068003411a40b4208001103d407440103c14007801d068840d4000600c4030034400045100e030049003400507080d4203280c84481034420483c2d6039031090780184440506100003052001100e54085444141d0303e00714a0700c0c3d0840049680090 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 880887895 1250 880886645 880886647
    0x615010e09102c0103030f121b120c1403060a0f03030203090906010906231309020712051e1c020c0f2104090b060f040b0d0501090207020d0303021b03 66
    0x3000506030b070303000c11082d241100a09011030203440c049140c401c002c0c1080d00003034060381004201080c001c40c040f1750200b8461420f0005500c00c2c150706c034251048501c0c10300105050f4102c240e8283e9022107038002e007a44400e428080c0a0350002c00401080d0b0412100c9010395000000ca42180c2e10b800e000c0e0f004100d5101140e11195881c2000703502c0350000000c0340e01803d40300c0c0024100d50b2280c0800c20541c2c00549511444884107106c442d032a1072001079144d0102030402024141b800405160401032101e4400540d40d00c2c0b15280c003072450340303190410800b40308060080050110342c9070b80756001030103000000703038032143d0b006014801c4034507a00b425a070741403001a41c44420300b004112050460b081c8404c5030140e100d005a00c042441022030082740115050000b88a8882a900841000c140040110382000e5148250034007960007540100342440c0c0000d040c0d880c1d1282c50003000e004001c45401141017180607000300f0451415154000c0426600041140024031000480c4040c664140122 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 880889145 1250 880887895 880887901
    0xa2607090608060901180504152409020c030405120703060507030b040c020c0619020a080c0607081b0901081f0e01090e161215090803060a050f030615010e09 69
    0x14210303034040d0049500060708200040c01c14204000b00394100c0303a580c2c03501080744200d501024002c0501034011507403041038901e0b250800c0198010300b010041b1031241c000440030254161104425142d02002c0c04600502103501030b100044159800c5031010345031003820850924403a82070169a41008049074904001d0001e16a85503000c0c0400740c00643e0304201422100c04180e036640c10720b2103401ea0080c0300700b040c410034040302c04200100060302d0040b96040400341e5640d860503041200d000e00c0540c0038608204006510190903078004c600a200c00c00c613030220032002c8119100e001d01c01c0d810b002c1d840b401b05e0508648144044201c5039000319144503603464000241803504203225880c8040c2c2841c030051440703400851500c0050488c0ca034292112890310040801c0354680c40d0042d41c3c0e009550403a50540905801010203091085451a0781c9180035020072103070034040d4100d43c0c0154404a092005901d001581e5031700214042c400d50600003868004030b030240c10f5040401c0d0040744500038 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 880890395 1250 880889145 880889147
    0x209090a200f010507050607050d020d060e0603061e16110123090114061e0d030c0203010617060f0a1803020a02130e0a060c0e270609010b0a2607 64
    0x5400350058088a449038210065401120207024804006e81705400800201d0107180c0241c0050245020540002d41080b8080c90b411040ba881544460038801c1c0b8a400c000f9039103001d025403a408024031100c3c1d00e9401d0580030100c41c42c1130042c0401d43e0214904042c020490250f140c900c07a0a122100a200340710701105013600c45c1b80f4644d0050303c28180c07803000c40c450320f4040c05007002000d00c0100d014003d0383c1c0c0c4000c201900c8480016820613044013074000211751500030911401c90b0003900e4103020680c5910516007162910b6000c03014462081c1c1c4200440040444c94940017000c1009901c20381c1c0f903610001c001410050080c00588125900715000c05070049064a001802150750348480180301d42c042d42503411a02c01c0780b03099080142c54034005281744d440710014950354501503508031114404146180d15001040240310894281941d402d004c48080310340c41402a1000201d5515214850b403031130194003541024480840b44c03421a4110f0f00041821410705052822100e00701804 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 880891645 1250 880890395 880890443
    0x1051204050a1407050102101d0106030803010f080a110d020f0a1e0519060c051501030606181127040603080a1d0105030c0d02071407060f1106040209090a 68
    0xc00700c5100d41c0401d290f0311901000f14840c42240d42c10f070041e2030102e00d800c1c500740040c0307a000d6009507c10b460000034401c2c50030900c6101d01840c400d00c0003964075410f1402000e074028080d848043d05500120030600003604601901420080503141c260310648188001103443e07000403036990300482c4005c40022401070b000c80401900454070352446500c1d85440500401c0480d20203000042d0081d1003041010383e100301c90081402e0300410503100c80351810781d824401c0361000e84c410340704240c542c507044c01006000519400d0350080d03000e04102d007a0046071118118003821030441190700d048282c45a10f20042c4691301080c4600410804c10507449103095041500140355010014070324042c0c5007051900d00207115036a0f41c4c143c40389402c640d41d0b000340001c940e01c20242c00f503c054091220304e0000b03522100010740e92106038090910b45042c10f070014180307210001c07042d04028a02a4540082102003441608540c05543c188400c1d903500900303030714103280e1050041c07640c9600700c40c0f0701403a00600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 880892895 1250 880891645 880891663
    0x302010c06022a010b10090b030103021210020301080709050f2502030706140708090303090a1203020705190b071b08030a0207140601050a06030c0806040e0705060f03010e0a0603080d0b0105120405 86
    0x4400080030401d0303d00889100c0a0b40c05541d4230401d0400c01800507203010003c0181c600141400c80303003c21010031091090741c0081e8080745c802d03407102d402403000303081d2400341580c400307800b0702590300929111a10b8102c441c0045a41c0c81460100e01034200c1003482031040300c00d0580c000d0300030300446110003024000d400080b22038030300040c0c3c0c0310041034552901004407802076000c00020080a03e19445001107401c0716901e080c103045c1d0070810500050000d03c8008a07030400c48078020000d1920317083c4080c0c0104000c0600c070030001820b400809018070002d1341d1812a4003c810540c03299200c5000030001d115541c000b42082c0300e10480d44450160010300c031410380303409881d4074503031590b1060140c0c20b40e4150040d140110700c15000040090078a0b0380401d1210a07080e080700d0510780d882d0b010075400d611165042040503c000300500c10066002440c64200e0141501005480e10f1a11855603902406101003800c90b1120440ca1450303128000313a13110f0425550404a490034285007881d80d8581c55 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 880894145 1250 880892895 880892899
    0x2161109090a0b07050307090e010605031005010504081005041a04080d0c170f04300e0a050108060d03030915050a0e010b1507061d03040303090905010302010c06022a010b 75
    0x18400500e20381d4000c51407610007988500300000e1030300c49403410b903075070303000106280100b14047d00002000d000c23060030f00e4001c1c829520b80341d940c1e00b41000c081c43e4420b00d50304418180b0004000070884160b0018200a150341c86050004a03926145440200400110422030858111605010921401500400c051059043c0801214100e242c2c1031741c00c4040e43c0915400d1106410021f0030b01881c00714041c0e0b10520031805103505e490308480340c82c4404100610403441040b07295a0b00d19041d00001c00d080c0291044a68a50b26842d0900080404000402c0300d40510300ca61031f41c000b0035000e81c02407200ca80d40800881e008120b1840950002c04023202c00c0d0000b1070a002d1401c1c040d01062050400702e0718040c029512011606046110799071001008840702542d550751000403d207640d40d40380c103100c1e211024542c1d031480c5042c000d00171030301500107142e018500801080140c1c2c002c030082c40103c1d80b01c0c81c00740c0c5503500d80070b182aa1074402074030003111a001601d8001d4400e0190701c200345032041 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 880895395 1250 880894145 880894159
    0xb0a170115090306091401110a0201060609080a031b120206371109030102040e07170f010509060a030f0f0b0a02072d020d050303060307060e060d0c03021611 69
    0x18400c10941807800780111240456a00441440828201c3c1c03c01e0040900552240c0240c00c8a034aa050848118428024100e031000c21094851542800b40e10f0080c0100d28042070828103050b4000d0319182001002824071402c4600e68109042c01e01d4182c405a8000e030454061044500d4081e440310350850310590201e1941c4108000c0e03d041794400e094540b6a0a0b1203802f04005800002c001d008130b6140c44030882c800d020180069070240000c1c805040155070340074103414051005416000000081d520501c402d07810012440c0f44c4902590448800300ea0002484c0c858070045481810343c5d820190480a0302e1a0801c1030060150002c81005d106445c131024036500e1408003c00c038001c0d034000031304280d10188404c0c2c101d0301500070b90400c2140b90b4090300c0490303032130303400601c421214001c129420b0f000030082105d10301c0c3c2846804004c001ea41011140200c008000070340501c10140d406a425a54000009a2600c2541540c460b50640c1e241795405040c00e04010f2040010a03000a01c503d0b1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 880896645 1250 880895395 880895399
    0x8040c090507020a03080709051e04181e08090603010b030f0108121606020c0f0d0f0206012106110a0216050a05030a030c050102160b09010f140613060b0a1701 70
    0x5071164a01c1001c00d540075104041c150b03030307040310301060107058402003000500000c102c030380d0346580000b007603104240b41050100302030050100b91a242c0b214003424000c20804040850f94194805420f2031040c840c01443c2c0032140381109081c0600c2200784c1d00b1031404800414001c1c510070065020300750071803400c0c8540c1e0740c400100b5030701c480c442c08502d10f0290500151880e4010040c10015151203109c01504114600c00313010b2500200c504600010b90000300004c40300b580181554007802c1891020788110760605034201d64100c011504a5a112034403003c00f018801c0644c004d643d80000103160076614020f08000030b68072403800050318060055800c00090918001102030201c880c058003800ca00c8803161400c1d00c1c0e10303245e2402030307480d55002c2188040800c861528080300038862200e140303079420180078450845d450703a01503030105460a44203003240b41031184019889a01250710380c41526039844004050704181d848001c100e400812450720b05a00300c0c1c415141d030380340cbc0a203060fa56a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 880897895 1250 880896645 880896659
    0xe0907030f031d0f01050a0e1c050c01080f0108060f090a05070801051603060f0509100305240f04020a030206090f0a1403011415040209010302040513090c05010f2007030203070608040c 81
    0xc211080e243e002c030710100322800d047c07400b449402c06410001491403101c0f80000203804c0315007440040c121005e82094130a01815070f0040c2103140c0114400030180c0e03466051800b030390769518025000e000c01030501400904110820844054425800740a4a9005a40e8003031103010380800e60321b1040c4030910342c08501c54203101e0320820003200d2804001d8440540b0304811f0040080001e024181e84000000010011900c00c00403c0c0442c9021240904614100c0621300006040070302b580605400035410301c030169440d820400d06032901220f00300c0d40c0d800c0ca40000b40001200d0041d1b250011900034001540f40f00302081c100c0c0105d170940081c051807003652004102d108088410b244c100740c41070000040e82c00c0c66809090044810b0500614141e11480000c008042000240054a40320709221003000261454200101002c2c2407440d40181c8580003d0002d202c0c4101e168101400ca101140203035a0410042004540280c02d845d51541c44000080c4803460440301618a169140d000007540 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 880899145 1250 880897895 880897909
    0x42703030e2a010c0804032f0123090310090b07230922020c15070c14010207060e0a0b06030706090e1509070c0218040201090e0907030f031d 62
    0x5880d1401c901402950031038001c2c0c05400e080daa0340d410410a0f541407000a104d401c02030020390300410a0040b4070442c084041301c8041c103280010b0344200e98126070740480c0d8204140108441c466a0001c000481d841003000b401e009541c4200c4d4544038140320420040b0740342c0e0060b04000e0040c15000e03005da0703540000f6122959030030030782d41c2c08070004484081040f0302400038008822000340001100003242440300c040d01c080382e0380b031620503500040c0342502c078904010307218001c41141680907503860100f002605010b064071018003d10103150300100910002c1d41125801e540c014010801d0080c0d50003402c1c0e9801007144122624004003000c96141e140003d0103204961140c1d856505240c1403002e09040400083c000425078500814648003560b5811062841500c2d0765a41050280b15801049903602056901c4501d8441c28014000540d0303001d0780e401d083d603505008210b0706031150840c40340350010f550320250034245180040c404050744101510181c6404031614002c0c100c00b5401c000030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 880900395 1250 880899145 880899163
    0xf0218030c04140621010204032001110606011803060204030b01053a031707051306030204180903020f0a0308010509010b2a010612060c17010f14042703030e 69
    0x11000650b00003601071901c01121703603c03003c601e18040084143c81c484a426030300107801c2103500c2584130300000c204072281d603071106000a003460550b44070081c1000300340c6c417032401410141c1040fa185400d4003962000c0c3c003d200c0250341c0040119907455580c00c200d00b86d04801c0c09030900c2100500c00c418170788031070002104159143d136038541c41c6156a218135030494084000d011000e1050001c042d841d00783c20011003900c1145c09031541a138403004900700c1da20185d46504600c00b4540305100c180942441c8444514661203400d00014100f142c50070140c0ca0400b560503040c102e84030f000145810903521030a40c9040341c4c000c4d00c03916034590701e805540c00c01e030154540300f00c440072400300340305c110380107000c90180c0484e4031034000215140c648054030703a5000a850b055580c0c40e291142d58101c1c503442080c0411030096003115505039414603ca00e1174842013481410524184c40d840301c82c080d038407035200302442d50184200031000340701e0a0308400843c882e40c0c82603010034981940009508004121504 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 880901645 1250 880900395 880900421
    0x602030d09020d0b070201050703230c0c030f04090c1719052802030610030b011b080f0403150e1b090910020309030d0c02120f0d0f0218030c04 63
    0x4140603008045400070161414240e901c10245000000070408603540f00340241001d500102e00c600e03203c9400740503502c41c3c0c101c010004800a8012040e50309410000390403c2c088010309036110754080c803592035070140d240c00403000c25002500080c482c4444d8401c1041812544613202042e415281e0821120f5003250412044582e01501e05201c0189a00550f8000540644807910558019400b4480c912414a0303080040d400014081981b82070f40c0c018444000318074040c00402d40c0c0c0300000300284540800490248001d5020707000b0054640255800b2a60825145e904c81d40d580c1440703021070120b64500c003a80d80c03604155554441001ca490990400411031383c050900f0444140840908000d100241030f016241d102501c4c3c400381d00041d40101c400f40011500d0740e4040c42d082e412035040306100f009541c86004c1d4106941e00070b038280c0302155001d03041070f6280d0700c003444000d0103800000d41a100051002a403200c20101e41d507a500190b5000f0341c105e07101c4d030b0071032000d2104540b0780d220016 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 880902895 1250 880901645 880901647
    0xf09120d0e03070b220b04090606030e0105070c0f0c09090b01090c081510050906040e16020d020c0409060e0d11070e04020607120507080c01020405100203070c03020405090c0d080c0610060203 84
    0x101d5a140d180c5c0c5a0103141541c02088001c0340d444e840072100c1e40198104046d0140c6502007040302c540d15014000d11021400700800660801e0200036108070550140184841c40d456083d1007401a00030303440006000154040c045090700785400240f44c4001d004406120b483c04562260b114410069684200c41d41440b40d0103c900500030801c10080601042c810020200214242511401c0280c401414841001e90181c03d103200240304200c4044c102c40c0856022603aa280035543c00a06034542c050159400540c05050341404000703085a06590081c91240301e5484c10f0b103a0740007603010000d500440c00c0c0d8502685624002041400c1500e010354020024050300b1301243c039900384062440c00c9070802d685009060ba581600c036400603185c10b800c99601180070816801c141240480d440640c4c40990b1074126155581c000c2c000082c04040d00441d503179000620088c50812140c80000401400d0101d1602c05140002d4030f58840b2820325244e00880001c2030380c010030f0244030350507500960059 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 880904145 1250 880902895 880902907
    0x15050a1403100b13030501060b03070e0303133003171503030d050903041a0d060f030f0f0809040f021905030105100809070302040f050406050106051603050f09120d0e03070b 76
    0x444154100c0134042404c006011030001c00141c0c2423050f04010400462039548910b0440c002a005819011040b030081c0c100300101c104585013244030785c040c0d84900700d0059100a01c815003148413081c08560244076001456401d05140d000045800c00c0541020508003565804200142c01302e140d0b03804c0d5406600078050100c4900c920382000340d0000da5002168201b90792000c10104103842003100942007400001e00c035001c501c10707000b89005042180201a0002d14603035807031540040c0c400c0d0182c5822044000302003044125011564900d000500c144610200880c1120095002c40031140d000030744400c001c0d8600e40104252130495074014a0300030038803400740c41035880f400000c03e451580e022346000400180d4440c0f01e1081e1140b107c0350f00254a240500e0150111001a0464001d000050083c140f40034502612106081e03490b02e4602d0719205220700347d9200e030050701e403078980c80074070b400005010311000a00e2803440b101c140e50300c1110030218024940c48a030706019a0615900070042 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 880905395 1250 880904145 880904159
    0x30d0903030c050f0d09030b070201050105060708090a030c06050d05010801060503120d06120f0b09160501050717121e04111e0d0b06010f0e0d0f0c15050a140310 71
    0x80120b905001c0c606480121041c4141c00c0d04040503144c0350700115094013818028440c9070007240d070f8443c04500080181e0f50400c00080d4090048100090162400141e841050b8541c0c0e1020030055500c00c0303200701442d0300d80c540030b025038200d00002d01407140b8080c0005110001402044c080350740160117891000900700d131500c80d980c89020007e142c103448980015281d0318076080d10007031900403c0c10350070034100c1c0d140022a00130040d10300c0842d54000f8841400e85040ba20010044400c2402d0050380c45015203012041841c200780d0f8184440c402041c040591003030003103081d120300703603286a004101075000b8940d6000141a240944084036000350300300c20741400151aa11349200c01c0c11000c00210b00000205225114a8203d81058103041404210750300b00317940c0c0c01120024241414003011803004180601c002543c054154803026031110180302c0120940005000e0384200c8104610344400050b140d6032181035860009150381d00b010180740154400e0300c1c01901d11703070604440c40e85410f207 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 880906645 1250 880905395 880905407
    0x2090106081e330307060f030b0901140405010b1c0c0e0405180c061606111909030201090e040209040204050438060604061704030c061811030d090303 66
    0x180b04480d2805000e510400000c4000b903500c220342c1e9008004203c4900e1200d849030020800c0c0218000289004460065502107110350035100c191620041c0c141030340c40708801030145004d03016002602d071070010485100151013040c00c54007e8030300b070140ba41d0700c103007403192440344802081130000b4055012240b0406600034110304501031a16141140e01000060201e0700e00ba500b00b01410450000c40e00d042e9800d00030111082c504440301030424051001d081903242519000a050903587c008504112000300140d0b05c941c00c040c01c18420074090301d200909020110b00042c0c0c04280101000a54202e414040034400d550207010001c00341c80e03660034080602405007007140c48816048001c00001e00c140000710812000300550702c1051500170b803030040d640026000034015001008280102c03500070944040c8102c02d0b4504002c280c1d00c0b0300701250450b401e40700003040c2d2820124150300f034050b0b61558080050280302e025403800040c00c10161342d09400300907100418007000d07007000800e000b90 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 880907895 1250 880906645 880906651
    0x6050306010518040f050a151a091315060807021009210207091b0912031710030203010921030b030d0e010c060c0f020f03070302070312021c02030408010e0a0209010608 74
    0x50300100d0460b170342804480641d2001c403249400c296403009696481f075142002c14004080b004058540895921001030051082c0307103a25002e01800410801c0c40740450b40039848207414180c00603100e80e1100c000034458002a180ca00c010722500c5e03c0016101114800c240b40c15601072085c1c10400c0308080548210010042c0040550003051000144218140a11110194440280f0f40760200400c0040d0110b01c2c250002004141d070068000c0009401c10454900700e01c84e100c81e020656181d2005c0059544d00e40c100039019424004244204040006207841d015100c00d210a060248400c0403001c031510005460b501d540308901c840d02c518000c4e82e8040c45424185000041030300e46481c0d90040d9a0002c032402e0000300c2d8111b01020300e542c1400007010807040700c00903525203c0241c0300255640c0490101402400800c9074844203180200100103c0d51020b41c1c05041101a11001030349a030014483c0001d5542018403000c00483c0200b00300202c0b5070300810b400c07080e03400d120045540c2c0c0802 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 880909145 1250 880907895 880907899
    0x301030201110f0d1107060206010b0702090402060403060e0606090f0f0420181b040b09060f0d090f0b070212030a180b0906010311060a05030a0b01020c100504090606050306010518 79
    0x791080c0c280801c20b100d074614501c103644451880001c40a6200c6c40c0840740e038406011034106500500c40f4002c0001100c07552501200c0204131910b4500000b4070ba4429503200502c0c0502c0c0401441c003c40c404a080740c0700720421107007007609558401d41c0c422500c90072a07040740c410402d180014001507843c071408a05c010410b0000a0700b0703001c0400f08070581d00410490600c0700e2000b041009003104231000303900c0020103100c004c3c181850b000c90180280125480c061180c00c0c04244611810b0510080d500310038400740c0c043c0b0100c9260b00341114030030322b0520b099540d4009440003400c0c4500005941c0803401c0246003151440c2d89001c1403000030711084c0c9424420a800300b4140000c40d04007140b0a00482001003d850507524619012132807256403a051409a00e00307018040103160000c0540c0c1d8842c941403c081428424200104d040051281d4a694040b0168502c4203040b0b43c410003510030307035981c40c03000c21030a5103410090f1894002200d020307002400401c00409161708031440c40044580c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 880910395 1250 880909145 880909153
    0xc050c0c091005030a1506140616050313090903030606030203070c0b1b03071e170433020a0305060913150e030301090218090f06010c053c070b030103020111 69
    0x21000064180784400d001641c0d440c81285c20401c03896070b144135587c0141040001514100400c0003c10a1070150045035090002d0b411014005e1100508c00c450900d596482040b800301d8070740c00e00c200204194181600001c0c2b5100000c100c0c00e01900c06c803802540c454441c0444400315685080e01084d008007940800365031154841c4444000e48091070081c22140c4424100b07021710309003404500840322000b002c02c1080903818902e41b14202a0680050300311903040e1006c0400380c0d401074501c500610b450091084201c1c0725650348142e40c094140f11069640601c51347c0c40310405c1080002096810a804401e494194400100e000e2240d24041c1c0c0104000304555029003c0d05003540c000341d000760300e000d80014990345950722207030700940100300c1220f0307a10403410401c00020314544000d1806040c403100845910600c58100000342401e03501280d0300d6552000c036170b004000304880b0b484818035885004082900c3e40004165202521100c1000d54196841c5800458009562400500081c05 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 880911645 1250 880910395 880910399
    0x10f06060905150d1104050306151f030b03100209040c030902030601120314030f0103170c060a0e0a08072d0b06130617060105010906030c0212090127090c050c0c0910 73
    0x56174040c54445011001811340c071146080117041c1002002481c0b5403040306261142c026954500d0401c032800c2c041144001c071940d20b000c005a00401035403c45a5040c450303075000e41c01d041950340040890400584040c0040d40c402c0c08250243d13904a10001e5040d0014401413100085030007000c028a8080d1070a08041c3c0781c00c256440300c3d54020b442c030300713400c619801c01801070cc0325444410441c5400404658035110148402d661140c07405008141410f40b1800c0200c241441009441800340d004000107a58150510327107902d48003c407160881c207040d000302841d089105007401041000b508003d04218030343d1200c00b0440d080c460385c0c03070b80003106a0744c41c030201d203146000701010a4070040c080248000e5041400240031051540d00490815040c0240d802c580d036408241c002070405140c085e5a1140c480300010b980000340c0e040108000b44114205088244406480d00120756192804100c11901400308407105d2090000b03542d205da2009104101c90709100c000341d940040000c01c0e03002815 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 880912895 1250 880911645 880911667
    0x150402041103090304030506010b07110d1110090e01091e020f0d060303080702160f121a130c0b090d03111204060309031124040c12080c010f0606090515 67
    0xb420a44080e1281d074030109003441080f104210146c00742c81801802c50400d80c0ba662180f00c02c0c080380404038060003c07803511804204440701e91014103080200408644084001c00070301d092580e102c0c04800d01044800010220441d1044a6048a43c001294016000c902004020b54040030b8460b10900f001c008840c4601142d10940001e5407007a500d41b581800d110780000e18280450030340850807e22401d08002100102c02207404030790401d04460095000c600340000320b5000d500d01d140300b55809904201001c0e81485121602500c502c400c10251610748540580c94000c0e69034042e000042c1c040080040ba02802c410700c0203403480e2086030303d0b20b0300b0003010f2003244e0081c0e40141d02098542c9000020150403030034a887c822a00d000801c00c40098200d44024607400315442440c080c01c5c0d001003414089000030000c043e00c0c090003501c51414007443d050459074810120901e003035117040c4c10000c82d00c280c1d018400844030380d82d40c2c40841a05010800600e5000c02807000506082002040111 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 880914145 1250 880912895 880912897
    0xd171605100c0f03050105220207060504030917030c0615120f030d060801020306030d03270b1008010c0c08250b0402030f0304080a06050406111201090b030f1504020411 74
    0x400c100d200401c04034401d54000d0000d03c1402035420a0505200041c485500c40c0000e078600507941c0304a0504212110440d0310007841100d80103070145040c4000c200034107410a18050171110703001d0000781c0100c100111700e9281c4c0203640da214419040040440c01500c400421181c2410008000d07603d210020208140703001c5800000e520305803c0418010249182485218010000b18000b585140780490004e43c4651002401d0303018103a850900041c200311050702005040d4400811042d080e0349030400b0b003000340040303d484441101d6100b010584a40600400402d02c40d680c81d000c00c803981d161307500e0210350801c009009035025030300900389542400d002c0c400b41e0140148038905c81410280141402c003040030030658201e0b40100001c100c0c040c0000703503242d10302e03070032282c009034546403442c145003d480507404da0b200c0d100000c1f4000c260b981c95040325038100e514907a0100013502c400d0040c56102d00380800820001d401200054000300b1800810a034000c1c4010000604504014a00002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 880915395 1250 880914145 880914163
    0x60405031e0d0302040e0103260304080309010f06050120120a0e030c030607020709151503020c010606080c090d0c0902070302030429031302031e0102090109050d171605 74
    0x500a40c95084108150050003000b02c0340d074480c5803c1d481c0c1800c2c5041640108030600c4000c0c01c41204100c0700740004a1071050b00c2c2e81c42e0a00300201da50b410a4140719141c0d400c00c2d10150915481d0070008403818081d441070b002121411707140c01001207146040030469100140341a4030034002d40641480c8003002c140280180c0e8640e403110403c3c2500340c8203041c40d20b2240c07100070f07009038005002c0c07240480d00050000100c0785010000302d40000c1030005108940a1541b01c6c04011070420f045120385909900a4800700c41c0074002000969541c1e0b41c211003400b07050756001039604081140d12000d05102e0a4001c500e4041d00341000101d54031070149080340d01100040e00182c00c003280031310000f9824249401140b0040c844448141c0c41449000c5c114031025000c00d01c01240e1003140f1007152414020641c03401c41402d1780340e18106040741c0d2640070754440c0641300e0024003a0071011490740391281d400403000740c1109007011041c91514417581c180d0b01004c8100341c0c042d00d8140c8103000800800100300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 880916645 1250 880915395 880915423
    0xc031118090a1407061707020111070b06040b0a0510050a05041a040806071e03020a020a05010c0801090b0306150103200a0c0605070f02100b040f050f070e01020a08120606040503 78
    0x118040b8a400d00000e00c0d95001e10240d100e4104940422110740e1114050740c060789014903000007034440c210180c1c0180b2000c600c01580705004640b03007080c05030030350b0014800c1c40d046ea02849613003a03c074204001120365000b0560300a070b0420001421901c640701a20040380e490421911b03082c3c070350108828124480f000c806020030002824010f5031001c1c407043d60801801d00b0010402c0380b030928100341c0c03071030102c2e220010943c0c08030302018164806c02180e42c0341500032008200d6031141240003420648240113051806003800d0301040e00d42030000d0a148101e800e004090705100c95a40110f015210760885082030f0005240034000c120700290003404907220b203484d017506040c0300d850060203558004000206119600840e0303102640c0126074442c05149034507000400c601004005401001003032003801241e03281c00704108110645040310350107490a6203c0c0b42001214a0049981d11a0620020a00c0d041488264026001c04000d40c1d080f140007800d0f242403a48910100e440c140484101c80 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 880917895 1250 880916645 880916653
    0x1006061d240d1d0715021506010528030f11040f090914030c030901260f070203130b040e10050a0b070501060321080601020616110705040c0c031b0c03111809 69
    0x800703107607907584a68170207000380043c200d02403011883c41c11051000740b18505004000868035880301c410942c50041001c135080c2c0b002c0c9800001d0001300141100180030890034a0800d41d00448001074065400321219000782041e102e080c00078040c050285200d08841030044070412018114060000c0c14282050f40c00a5459145200c00103000750f148402d603881130414043d4403142c05001c060050750240706410507540c680c0711044200d103580301d021440560303400070400200da02207019004000f121801d10403000503448000481c0c5040c3d015119155220018404c2081120b5140700078000a40c0640d0000691640c0c2e0385642e000690885c001034140a5003110a60310340b5005030000e81c2048081c070040000e46020340ca030350340080202e0424020320606000a0120080070888070010b050302400c18081241c039880094500e05034620b00702c1c040f5003282c03001c00d03524044040040c40d8a400c5040d4850852840e06d07082c1d1924080300109400c01c800c200301000e030345400c0d01c1c0c403070098050f14010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 880919145 1250 880917895 880917899
    0x908040324050714031003021c150b0901030213021210180e1f0905070303021501080a030215070309020d080405030c12060f07021006061d240d1d07 65
    0xd0080148011207000340c0500e00024024101c2d406410143d50041907003a095032a2a01c2c448054004080c0d4030080d840504200c40c4000111840743c81c4081620682c8841021108102c400054881d50019150800400c400400144c43d004103044440310013882d0040ca400409250b811785820116150382c403000840808200108440b2604400180e0320a820000c542d80c030b840c0705031110794030883c00d01c240765503207000c2c0e040051951000c443c0f5070340482144c1103550b6900c2c01075118600c81d1111252a0f00790303400015910004241c4030401c952540c043c045a40798905052030400e000342ca1030003090b540354414001a01c1d8038421030011801040815101e5140c4810140b07400a0b9010140c0036005480ca04003c080001803e280c00001d811400f5409ea42d42100413441c00c100001582d0216007001c41c0010401c2c1c001081c94000e001c0003c11700c0500c80d040081c0070201105900180d04940415100d04100a0300c1e40946030840320203001080c081e0a21104030a0b103120707010314840c160419641 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 880920395 1250 880919145 880919183
    0x90c0309120804020121020c0304080d030501060219080d020c06070e0f06090109031104090807030c0506060a03120e010504080708101d1005281a04060f0b0d09080403 73
    0x96045407050741d241c080700500c0c1581c00204181d150000300d90012440800c5584095240d0301601c00001040c0112031303d503a62034078900d0392075030300c0021200420718010000c03070010320104a018404c620343d003607074940c04200d0343d4410139980100c7c0314400c1d050707091001203018401401168000d113400d54820001c060f800341001302c2114800d10451240f4010410000d042c0d8008025604a03904500780e420084c0346400490040c10a60800504014000900100301034108050440fa10f0081c000c0b81c00d60355811302800040801404080c02e8001c05240c100e01c108d1141c0500d10303482406140c2503051641e21281c8900e46562604810596008801414050119813241c14810700c90140f10030b14032010514a581c0321158039580c002d2036a25580000d030095a92030030020f070300d1152040c0c0c402101068210f20014003904015010345a0140700000203071506010b03040c2038400c01012030301c0b9103250503032241c11a40551403a00035503441d0085e89010841c40d10180000358010410741441c100c000d84 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 880921645 1250 880920395 880920413
    0x20601090501051003090809093309060402070512030106020f0111090a3807110d080d2c0102040509072307080c0d1d0108150105030709090c0309 64
    0x100c0c14925010040190307960300420030020340043d040015450f003040c01c000080d40304284c803242e0040d4440c8203014040303021541a06a090040c00300000e0178140e6100114100c0080115551004411006c103002c0d15040e07004050b25803040c02158424190002010f120b50401d174820b201503040000f03160b882170403c0c0103c0f84003e0300020f4440c6485116000034401c81aa0b0041c40c2198040311612001024554601411409003502c425400e5103206200c4202354000042114814002076030a8458144403842e0f0800551041005041c2981216031900804d019074803405039540030704424041e04031300391040f0092941e410025030323501c0c00c1c00c09020202502070010740401c42824410b080113803218170300a4942d40111071160b543e071a1814a81c070140900a1450300d1401814016040d040c0c00658440c0300c589400d8903244241404801900c0000c1c0032200f0032600c840500c91344000350711903401117a01074440d08203480141c3e21281640c080312041c40c1d0030030200c0e6580d8101030074051084 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 880922895 1250 880921645 880921649
    0x2031b0109020603180709150302130506180604020d1d010c0801030818010509030f010608010f11040e0601020a0b130512040303051c0b1002072916081216020601 71
    0x34004981d05034042691807100901480041080c003040c0e041e1540b003405080d0041038001c5092015081412802c4003c0300c007480300724410111051028040314590042038490300000b8950505001003000c4070a01d200020601a48260f0030030075000302641c02d1155a04100c0b0000341040071030b0070301d40031508440d440c1d00c645040c841c20400400000382030300c04480442e00c840c03445480401d8038800585060194505040d0316010340b09074851144415409101150510303002407041821000302c0d072040b130b1203400840c4e034120000c010a001a0b1014200e00350042d506204984150780c46890300050144240c03680b00312407042c0101501485020003400388903500140f13480d45050b00d150b90203402072280e46003c014151040f0002415035803903a00001c95510041c00140c0600f044420003526040c40d4016003070854020342c4410f001c090480e80c0101d9144200d02030f90703e026080d00c82000411100300341182c407504100030001e0000322400c400c80c010304114a0b2492110303210140641008016 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 880924145 1250 880922895 880922947
    0x318030308012117160b010939030b130e060912190806030a080406020708071a0702060d0605100914010f0f1110060e0615030609240a060203 62
    0x10031501e00070424204c40c8103452846102c4aaa84800800d02d160000e41d8542c0040c0c1001e1152000081001c21500300d000e032907403c224820303140840740d04111120005084030503405001c040c00c40414a000e07920400141030f00801019000c0d10840030b0750162811030540c02060782120013130020000707040120040600c502c0040a042c68512900c10300b080380c1c090f120700104800c03074000c6182900e052101e0300c10346800240a82c1d4640d10345001a5482000d440b82c1c07a20741c07103000d000250369410003148a914140c0e0f40c41152034140c09400f0000580c010000741e402030340d501c0c640011039070780d60300d054205081b09840f204540c0d0b2400e0316047c41c07003071541c80e03c03410b0214a521501c5819408030768062414000c3c10700401c0300705040c109900c1c1104882040d440c00d81340c844042103030075081c9110352080700304480000072110710305012001c600040e2001a0403d1600d00882c0c0761030902c140f141503000e10a01c00a411403640c00c0015000101940407101580000650b0743c4462404080b114032401c40d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 880925395 1250 880924145 880924199
    0x603020906090618090f1803040e1b040f0f140405090606061602060409050117160e0a09050d080f0907030507051c020904050c041508030304030309031803030801 71
    0x90380022071001e200e00803100c0d21400000401581d4111840b205040e0306001030a2005a484d0000015454a10039034044070740c1c414210390103070301120000c216019034006400340e00090b2070350500d8031628611400c282660030014400410949440411400146020078543c040075250215407891200f03a0791180380124181010000360100010f05941c02c401e055030f989036580f4640004190007070b552480294801c0f000035002541309610381107d0705070b441200340e44e440340071145041c46e51141e03000f200400600e126a001c0003030251241089034400c2c45d00c03001188001c0d19544460600640182440118803041c0034010503148071001241d000c00030700010420b02e821621416900c503800c0c880d56100721401c410040b15244500070780b24456a0140c00d000340c40c00c0a14025460f03050802e1300c54019850800b1500100c07601049501c03c4400d140040c5145450b6030710120054201d088041e8140a082c0307000d01d209804002510004602a64969181d941041001030114050401038020020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 880926645 1250 880925395 880925407
    0x109060f1107260d140a09050a060e1509151021111002030711090f01060f030e060114010210060503030412060b0a090c030e0106080c130209030f070f060302 69
    0x1400e0700c1190300c1580c1103044034800561401e1003184030541d0303014091000b00c02040d544520444c5810410b46500d0943c801e0358941c0d60110904102c42e003030b034005455540107045400105d1441e9218414900c17613402596240400f2402c1400c8450080e0b490202aa004205002c7c0c01a580d0b0200c0da002240090240501031425003050f80b0702d03910028440c00c4040d001da540c1c0030000d120b440c1001101d80900950b24280b0807540c060b481e50017272601a640002c001c00001500d1928a400038841c4262920000721642020700480b10510050206020b0550b41e980c1d10001401c2044602d0081003600b0110140d41d1214000a0a100c82074504295450030168240540d54010007a1419075691351440301003180d80d070030580003401d2060b1007584c002030100c4002c00c0f04d400d5500001b01c03500c03d44e14244a41261241035500320303801423244104941250720001800e10b458288203101d030a1480700541803100250000741401c8468803080c1180d4412207003003001b03c0507a80004003c200074141141000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 880927895 1250 880926645 880926671
    0x21504170708071e180501050901061e1b0516050a1a0d05040507091b03111207080924010801111312020111010c1709120910021e0109060f 61
    0x3228034040c12220107128003060b50551042c482036401400c0e54445d02c24032411170312220004080c00e00506009411407000400c01d00d00a0f0340a20994aa041e00c2c0b102c40c00c0961000c403208101c06e6120031011440c1d050107008108100301070340350840f40030b03000340500d845d020412000c40507d0b4007241c210155900323140c804149110685a02008a00380454140d81d00e01e0030504042d0142c2201034180e1525180c41c4014600c500c902c5d10400d0251402c003c91450070801121038002c032400e1008a4018000081d43c81c2e20581020303030081c00401c1114607601c114480502c44005803c08500310710f010000420090200f4099030b5903c51141c0c1d40c0314507000c119400c80003c11000d008469480310300b100b1840840e4071400c100e000380340300c40d0001c00c510100394000400a1600700c686103640088600407030b44004003c90300809907141d02d11600e1420711081d0074448086444028401503006128a00210503060b2440358101440203000183c120388071300c2c0030400c85540030f400d03004452030010400c42070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 880929145 1250 880927895 880927903
    0x603010f090209160c0503030721380402070f050d030e0a08030402010909050c030402040f060b1804020d05070c140d093c0f0b0f121003021504170708 66
    0x302c00a8040913103507541401c42075850008a500092807481f0000400c1780c0564818003444441c40c580040d184c040150128000a4481c0c0d202500d900001d03a02d040942d100c506000700c1194481070a210388100107110018049030440c40c000c3e620040182c4001080240601425005041038101000030481d100046541d410380c22000511101c0c001011038156805521000010b10307150710203001030300c1c000081c10f0580d003003614124011030420300022070720789140c001d4900781c80d40c4144090400c03510b08980f24800071200316039a001a407c218005865440d40940f511919080d00c4002e094062482e181c0b5107590000280c14040d0080c01c013040e03421f039104190b0380c01c544a8118902e034001050141402040c207446245103522a9040c11100102460b032802c411901ca100040050a81d2800c00e004c4a101d141494203042900300126413400d1007040c1d05680200f00d8844c00d0755226203a03070200380900710401d8843c00c030300c0c00800c0802c4014a4000000e0f1324040d02c0c0003034071185240607076460351 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 880930395 1250 880929145 880929151
    0x801050a110909310210020f0c0f0d0b0408070b1b1209030c0d0f17060d021207080d090e0105120a11040e060103291e040c031401050603010f090209 65
    0x1284060f000818a010a0306071035004214801c0000003e0280042c4003102c404c4140c3c030100d014800388150096168000300700c20100c0d400300800b40c06401c40d810304110b044028001d4465210b101403408401098a034030701d181c4110b100c1e238003240d47c840c50b0703040400c00590024502c00700712454203210b101e00102842910b1018a520401c44156110110041d0860207200004843d9101c0d55554001d4980d00c0b40906140b49240d46414986c589003d1941c0903261040b200c0c550011141d07540c000c0181000720380004401d02da68140c9203842d03141e081c0c003414010007201e410005110700105001c030100100403940100403c0b583c3d00e41c149140701a59848042078030b80545000f82d115203a001603116900011030919544054981ca0340c0c4910f4403410101100001c101c01000c503c616194170100c06010078020001854185070380d07849034030000000407004208036800e2030075110000008012280110b0b4851001c400840c4030729002d0189400c48107020858034180b03003029150005a100d400344160 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 880931645 1250 880930395 880930399
    0x80702040203040215070309090c030608060f040302030c0d0f1d090403140d1e0b04050402030a06020703020c060705030703110d1d0301110a0512090a17180a06090801050a1109 77
    0x3850365a9400015024031703040f00c0d220404000000d803c001c15900001407415509200f034108500286c2c2c1074100c0c112600d0740200c801590202c0c010a403138a1000c0420707079215102e841102d00d13040086882505200d5118180c0020604201a840025401a00e80035140d0b4600248503107414191000072142000540003400b03000210104178600031a000c2106d900f620821300c14001003540e101d14103c4044030700c081e107070401e00c4d00c145400c81b85041d000d0b460044c0d80040040160a01e03a4480e0b4009503c425000c406602c90900c4050035521501c000d021107a005101551300c62004e0300300a06521130b5815101c0d0103410074100644990342002c8119440070300c000b841c0d82d81c4186807003c00d004040f15001c0b901481c1001c0f640a81d10f039400301c010524001c6c1ca034641683d5440d0070584954a42c000c400090a44410746000007501d031410700500b80c0c522203100d0300309164045202103074511405811440000d01c0c0ba01003401303854001d0280302e801a9206004014040e07501c1c0c0350380201e00529841078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 880932895 1250 880931645 880931647
    0x1a09060705070e070c06061a030105130902090106050d14160f02030c03040f05100e01021b1908030a1701121226011a0a021c020a05100c030501120807020402 69
    0x40d090000c10031032200502807100107011070303040030310003e850380d01803003070485100d4203110011891000e0b0b500070402d00c0c0b40aa0b103090440e4284002c108400100d040746122466440509101594401c00c0050003440d060301c42503514100e415a0031b06940c102020028180c0c004401d100070103180400c00c1158010524290b070302926018412030540c4914141402c403844086404036000c02c040e500e21b001c0300c00803210300058061414081d500450306d5848103016030894030440310f1200c2c08003c08070480714010055034a481541c61214604203080d0015800c03580041a038030b600c550040c14070210141e0211803421190300d003408808a280c10308000421080051081d209481d02400685c081000d1176404051840a41a00c035013203103a0905c40c4107046a03114421886500a180407249100f060b0b038003800307036240240080d410000120030102d0440c815880444046401031101c5070f00424204001f040c0c41c1e1926200500b500c1c81078010601004410710f140001504a2080707a81481e41a0f4002d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 880934145 1250 880932895 880932907
    0x20711060d0204180f14130605150d03020105072a150b060f130603020f07230a030201050610020706020718020403022110020315060904090203150906011a0906 70
    0x80e000e03e42c099004004d200c1c1485a1100c141d8103c9806101c81c0f503003c105943c1d410400c0c01d2440c005450543c103070318001140d107010413910f400c43c0b640100748100c20780d4644104000301e02000301c041030640050351b5890521284030b41c0a00843c030b041d810140c0401562424080f0a110761001a000510440c070501070328580348a55041616441001072070746841e00ea001c51449041d91218007040c4c003181002c60b000c648540a8825690001442840d041c1020225070710030304044084603080040c1c0308466000c4000308000c00074180c129110343d00110341810b0500078484114804403400084d5081840c09110302d55001807004200c6d1309071a1005200e80b182d0600c10028421600069081400303040a0f880310518034824410401d4401c0481c0c0d03a02609540c11403c80c0810340d001c84c0d007a10040300c010203501c0d01c1000341c59540001840000c00c0c11760b51f13000a141060b000c100414403c588402c10102550900000f0f0040600d42e0743c4050901c210750b4420340502ca52560a07224600204103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 880935251 1106 880934145 880934167
    0x3090f060816050901021006091505030c0303031303090e010303030603050609160611341403030a0f230c0d0e0a06051606141902071106 60
    0x304005024609208682940c840004e080c110311907440f128841c1801845200014580040c0024049456050044d20001a503021610940294644420799200402140d60049503030340358411a000620b01a1074280b8180c10011000f200200080201a0540d001c802920f0086045a8640d564070040780d96070b224481c200c003003440406c4000c00c0524090340868140c2022102910b9401110342c40d810b011100c0d030b100c81c40d80300803884503102c9040441c000b03407400703000c4401c95407180126001c00700b80d81c0d2140880000130404001c1407081c0c1c29128104203a41c0c41a1401d15400c040280c4440c0c80c41a08040261811030181030740510031503000e141c030070801500c080c10070b648562400c541941c05070450345031071114800c0c4260703402c00150a840b0f1524034010304403225255040c01c40000303114000105410079168410002200031450007164891200302c02c4800554541031244 = true := by decide +kernel

theorem cover : BRFrame.Cov 880755395 880935251 := by
  have h0 := BRFrame.cov_init 880755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 880755395 ≤ n) (h2 : n < 880935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
