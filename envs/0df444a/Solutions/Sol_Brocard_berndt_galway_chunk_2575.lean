-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2575
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:06:41.009348+00:00
-- url     : https://prove2.me/submissions/a9a243bd-c9be-4254-8900-db9421227f9b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 462949640 ≤ n < 463129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 462950890 1250 462949640 462949651
    0x240606030c0d021219140c0306030a0f0606180504020105070b070e190317030603030409090501180308061e18100b0a05120901020301050a1203090b04080109061a03060708180d08 78
    0x1030500310482c1404007021078458100c1814800d0342080080c0c44047c40344015a23210b0070290588007412900d5507214031507036004104403191510f600007800001d42c0b103c940c9542c1c0c07202c04402c0c4000d04207500041c12138403891402404610020f000280903c0c0505c03260384032420050400181c01241030109892002c0a000c02c440030228903c0080d0040b408406517400f5940c010b01a500d01803500d4541d800821543e4002c60341135407181c041c24018000142000095030180c1c03200121444d02c0c00401c880341103400e2514088000700c0f5a80807403030b02e8200d0300d01034400419821290a443d0344510801c1180b0030b82c04003022000000709108082d81c40000b51420800516a13003819496640c201407d0340402d015650b000301110b0010041444c83d420426504c038003d041891400b5107071441c45409501030707086078113140c0d11245210b003040018403840040005c004103c0003011008000240c942001620b14401c0141c064041b9610254400c4964121100c020441c3d0344801480cd0241c29048101c84 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 462952140 1250 462950890 462950911
    0x30402010e10090e0603010209010207180e100b0102010b0102060103050d030b040e070b2101030f030f030209040501060905010e09010509060f03101506081f0b0c03130b0c240606030c0d0212 83
    0x1017950b40c1414002c0c0c5816000c140c01820f62a410300140030848030416030356002040d10341c00301c410030130003c0c401400400410040407404039900000a825030b1004955203045600400c01040410804030f944000d6804d5031501240d14040800010060401c003825514170707015185001418035030b120000d00140ba298884020603811400240007407400074031019280a015440410000c0e103c2c43c00000c3c1424141401410503d42c0b038003040c2114803d03084480841c125420610817581c014441000c044001ca540008560419011610400d40508402d00400030006108410380c1c00307209280c2c00898900c000c204d146035515204072440410b206003000310b04500301040411a0f00208803084c80c0c84200700c02c180a14015200d40d56030300a83c0300f200a40000c0c030400b403445102c2e001c898001c01000383d0403512442d95203000382c01d00f0304e400d8445c004d0700d4142d03001100041010710140ea01500c11200552242ea9040c1030580c2c41c843e416802d10201e200040c1d00e40315004103003045006162515 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 462953390 1250 462952140 462952169
    0xd022503111c08131b050109090e0c040c05161a0f04020f1e06040603020c0f06100315020702060c0102030910050c12060f0405091509031e030402010e1009 68
    0x5014030b80301e84150100101e00c002d40b41600c1d01090103000b62642000081c030700c0554544040c1c90391030856200c2c0d107090404c41d500803001c114540c0e0114541c2e0203080c20010800c808000902c0342a1746d0f04e441e446481c00b494071401c00019150150064a51a44001c1d05002004074a80b070481001260f0f4103580d4403002c2608082401160340301d900c14866580030b02186142c803011010000c1048a40185000600c500c1a8402c0345442e41000380004000c661400740e203513400d03001014242100d00d64070b01040d5110f001003000c50003814020400b00e9412005c0707861401c1410715444068412042d010b5044500090010741001056000718440d203000001c0d00c0070400400c17582001e40e42c090340d02c200041d806129000e648000880e81d00d0f081300b002459644e0b040810000704050316000c9801d0308a03504194154142c00c8881c804140d803005030000503601d0702956040382040550350a1581000e0f1502100240469010b8058241e4101d4000d001800c3d9498134480145510814000d8008918078203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 462954640 1250 462953390 462953417
    0x70906020f0a03050301060c17040b1c1407050c0f0303070e01081e0c1303021216270b03011805250f05010c1506080a03082a0d022503 59
    0x300e240078003150706039205451741e4a0180202c074a400d48420681d058040848405125944180248000c003507903281240c641042906103400329450b03c035400d40090801c80d030a864035600f2045168132202c07170300308142c6840d40a01c0c22454010b50384e4405070f41d403000205004109401c011807003401882640c0e00701d2941e44440800d002c00b0351444005140d805000f001c690941c8003600580207008822035454105603691b0000307049541c3c00c10183c200c0d40c010000e948000d0603a074103c03a020300ae01280081c142c1d40c60030300c2040c4840d01c03800041083c0b90741e0300c0126503594080d0009003101d461914000071008160405a0322781d501c440714140103030050b06c80d64508003c0c800e4120100c905407010741c043d0528001c010345d114100e850044800404590700b240d1a154503115100240c2030580040440402a1038060300c641b1010b003443d0241500880c504104140299021000e80900d040603512142c06180660280c000d00100c1104604d000c0071900c13500450615290996000e40e81e02c10019500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 462955890 1250 462954640 462954643
    0x9020a2705070c0b070215010b0c010e03390606010c03030b03030a0807031a060d05100b070b0603010c0e0d021516081c061802090a0323010b060415080903070b070906020f 75
    0xc01f00e040c800d6458401080268907020142c003000800c0700000c110b544102d0256419a4010803140680808030320904140d0440602c6480207042100722240302a440c3e420039560b61a8014403090404c04000240402c2521030f030081c00c601d460240890740c44a05600c80517001c484202c4001000a00c2c210034048005801c0030304490604010f0710341d030314164018041401902c0000e01035590400f00700c4002070310303100c010010900315015003618036003070030550101030950700200603400421078003206001c1d4580c1d4507101c506003640d0480e0010341d10030018400100c40d026841001000c02c802c0c0d400c2c44181b040c1c0c41d00421018082e2100c040c0420b1a42c901c22084503c0307400740880d0348601c40c48220b15034001d50700800c200351000301a00300310b5a880c1d4030544001c50030740c207140c808200001590303441e0b01d00f40611410b07a00300320382260400342030850a4000a10000881c4200709808000c518028010310480728a941c00100c422070914126001501003020303842a40b005201d04100040c65400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 462957140 1250 462955890 462955903
    0x605060412061404030c15060513020a020109320307050a0b0a0204181e0504020913170c0a030f050301140d030e0d03030501050f0409020a2705070c0b0702 68
    0x500910990909003021100040701602000c1121415540e10051120440c0c2d03100207842203210359250482c07900e052801c400c04404400501c4d545c01d09213101808a66154004c200010254100050729644440d8013280900038405025008408041100c00c540c0d40c4100001c5024100b0400111405d40020100f1358070300c100c40c40600345400013258000050034070502d503900030820b80000340c2042c2d100c2c071100c2c0c5025200303500901c140d99103880c00c1c0c2864055207108512000c0c1c990f410030941c502500414075a0314010501007000750030080c1d0608200c07030084031150382c003040c2c101551a20005403186907682c614000a401045a40391a0300c0c02c82e1041088034160794054004044200340c807028030404480d03000c0c00b00d0900c2000c8501c0c0c00a601d4291044403214002d542c0440c0551500080c001e1000700094003502480c10710b812070002d030300e620314072008884e152200058203e40441003000f106801c90842602c05040c5000c0c040420b90007900030490a00400b00c02d1703229110303440c05030382e02d44 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 462958390 1250 462957140 462957149
    0xb1c03050408210336150703090c03020112091a310b07090801050a2a090e0403110f060a18030818100608030c070f05010206041b05040606020d1206 65
    0x40c010400144c108a400040100d403151824885030142d41190340201d410001d80c17811800742c0c4c03100302c0c900e0340442040c03c2030390421030504042160704070a850f903050041c4a03000c00b90620228550300d5282c001542d0040100e0340d00031031201c030758003001840f021034102c003030b10803600c0300e6181c40c4107040464032105408c0c035256a450710000045910b54903800d07401c6008103d00140580f85000040486003030184d07500c11440d4407800106030024607090824240342c2c0b10b03200409100090881e034400e801040760401c0e641c1c01a40480346540310318085035260640c1c849d072105409189040484403400145480c02000c62031001e100e13a440510303828400d1071007041c0250028a024012848420484503040029582441920000c0d03040e0600c80c4107444403940002c466502c0065034050051060004401070407400302c0418680c1d00c2e02000030740c1d407600644040e0455040681c0160500c2001c01d005000f004054414401141c0d5440041e403140c40700c016900200e03000d203190004207180d80c800d17441a00d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 462959640 1250 462958390 462958453
    0x6181c0c0b100b0d09020102030f030702030d0c08091005060f180a0c0c15090501090602030115021002030411101b03050301060e030d0815030c0a0f050111150103060b1c03050408 78
    0x34940780544005070285d0345003039040d030008128500302c414140d8005c510541e42500150354500100a0704030444e480401c0e15030421030761805000300c00b1008141c1c0c003600001170001103035989907800010340e044500c0c0c0d0840d134851144140c20840060100c078041c424010007408000b44000e81105607440703418248000c054844c00300582003503041c0b640c0140d0b0514003030000002c43c445259034250480e8002e81081d480d207a10b4403101c018540c3d0410004c0302c40b514400041d0b04500f0141e84034010704240e0011a482100da8046120b01c091056030101902c407450518091224200c0c20041c03d1903000380a040001404106007801078140003c80e28107036140c541d03803200030b40d50b1a030030a0050100c110a02d40d050089000448045c0c1d2003031840300240c840301c1c0e0542c103000e20302800901061490041e00100f6040700351000300011810410750b045070340140c000b01d5010780090005503100803c5900051003422240507806055000003d070050f03030001422214050641c0c040c40008148001c00301050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 462960890 1250 462959640 462959647
    0x302030417071a09010b120f06060d170f0a0e010c02030c06030c1b030a0206090706081501030e0f07090b030a05030706020c03040b0a1d0901060206181c0c0b100b 71
    0xc07048840c0080611078000e014140012104a141a107540c1003035500c20601d0303440d0460304c038662030000080c0442208960041c41d101584111040c0c803000000c06080c0700740040c03644141800581c26603507180c02510b1109542c0c030107000040c15496000b01c008100003c00c40c80144003203500440f100c2441c03540003030050003c102d51408005466100901c030208009080c0140c800c5041d4401202c00000003903070146882d0003c2500080c600000280308148a51001400300314294210000581000092003021050401d20006074060b01906002c2c0046110302c41040c140343c003000ca40c01c4d0607642584c0091103890880d004140e5a15201900609190030800c404c40000e0003a900a04503c0d40300425281065969112120b20303400044210002c55829000c060b448540002c45010058044030040050b504042000396103d4000b007811070501030644841c0d520300010009080642e4688070071030310b52803002c08010a0010380080031111011038002164a031911554000151803009810906 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 462962140 1250 462960890 462960923
    0x903030109142a040512010207060c050403080d020c0313030f0b0606040b1c090b1f0503070b03070f11060c0901090e07020a0f0f0503030a0b1314070e030f03030405060f0703020304 79
    0x3582003d14908404030810000000c094482030402a05001e2480c00141c65a000c5e04080c0250b6203000441010004100004d000042d41c0c1e40c1030710010800c0c000010307200c2c040e1260b01c43ca14401d01c10603022855040d0750010030070401061103013507039200385038460b900e465072010b1124a01844c000e140c041c40302400704071300c0000d110000b5082e45903002d0012886903616140c00da460380060305c006042041440b03900d050114214421001007206900a042540c0b504c030500c3d40c00d010141c154420040d000c40422241c0748590107003c94180c40005951203418943c0300c0e50020343c844420341d030101d0914800010320103041850940b00e10019009852920441d503500310740e0b010310010032039a00c01c229410402055003000510b1061905900020307680c410003080154044d41c40500907051810031200e04841c000300103c5603080000c50418001258902c0d000074140f01d9816030103103c0d03120100c10002071160019030240101d4220343c4d00c070525124140101c09034401147c2c040c2c15810081280b42 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 462963390 1250 462962140 462962191
    0xc0801060315090e150c09100c0609120e030c04050f040b04030c050f1b0603101728060e071220030a0c0302090603031617090603090303010914 63
    0x39080b4800e000d2102c03401c2e0f220300104044400900c00b40350315500071802d40b010301c3c060480d0f454011700713501a090306114006001454044c01001d020040002001c0120200310041d04185200c40d8408803100a030701d076425004003012000302c2c07618464410203a038400c06003000e1150f140610f100c0c02c0c483d21265501c2d1205c0c1d0309448050400c408001e4942403010210f60300b445206850041c06000d0701115829601162031402400c41c0a0310510b410001d0020142c5003680f98001c031661120200718000300080041c1c01d00d404403081d404090112180101080c24010141403800d100e28420000d0409020583e651429540603070300d18803091004040105080d403010b0b80302c00b11720404220b0890240404641803901030300007180d4a00342c0c80414130840c40e00010b441d60291040d8015402c1c041404901d4521f40c00341000541000c0340c1e210300c07040d010007030f4040b00d80308480031303014940c1c9040c0103440c42e13683c1d80b007403066032903491428005080f010802c0240f03e0090000c440d040021280224009 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 462964640 1250 462963390 462963401
    0x20d03110601060e01021e0c0d060b0d0807060f051e04060b04090308060406270f02070210120f09031403070c290c040305070303050d1512060b040c08010603 69
    0x55051028600036208404020041c207806420103a40d0540c0c10040d003c00689804907441552101082ca0464030301c00b80c10004580b42c440c00116070f00300914070301d81010700c02410000000c42e08451040c5c0c3c03081c10b011410000f0a22544a50b00402c03405e511211030b02e04460702518980042c0282c651682a0100031480c1541c11600643c0002442480c010008080b901020011030114892204004403403500b44504402030070400d601c1c1450340c0c45440c1a07891028451a050403442d0348200c881900c1c2580d605548a840d4098407000c02c0031501040a818901c0e01c020101c44e0b40d05041c607440c18000ea50140c440ca40e980b40e16040300d1800251554856608001d042c0b80800000300050404158101000e000e012014a05051076401788180c3e00e2000c40300400700c022000741001704100140d800101c4030100e075090b2800319242e172241d000304006850241c2806c032b9003184800340450810007030844004080d1248200700700c05520a003c1c0420f03517030a8099040414201d90041003224041e0308034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 462965890 1250 462964640 462964643
    0x207082404080927130308070507050102211909030507110607050601090c0f09050f01030e1c0f080115080103121704080304020108060a030b01030813080a05060a050c0c0703020d 78
    0x1490403d8107180225944a0f03184030050341400a0603c48034032803a41c9040c00c0d0300000c0c11002441c2c02d90080c4c90140c240b55000c0d040104224002401005000d000e60584d8210522401e13504450f41110f1606c003036989042d42c499645108d89003d908880b0309034419811001e03855140c45051541030f0719613007466620210003c0d080142044148001481032041c58007900030a01c00081190f075600004000015080714081841440c041c14041c0c0d40d2070400e929007410302441d0200741084e14070071182c2070041d4040c074400d640041e158104010303600240c00000c580c40319079410040c2da9a4149115908070f490a507034001c00c8150700140042401d0640e01700300c2c0205418400e0303081a1140e00c15030042003c48082d02d28042c080706110441d070f0b100c89042d401c00400c4035005000d0342141c0740d540151006101c024401d850028080c2280d42441440500038020030060352016156820300c0e03901c5000450301d03140158502000100300d202117105840685007010028001c00c0e0944c0e00703000102002900 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 462967140 1250 462965890 462965903
    0x60705070303020c032a0304030323041505030105100306050d06270303020d140105010503070806030c0604031b05104107030806040902011b151104060207082404 71
    0x1c2050302a0208002d146c005180b0119054500107040940403125941e50181c000307810170001003020039032200080c4451400001c1803441940b40e6600b0300315900c90342d071010480180c0e581c0081491034120000e14122882640c000b26416403200c4100c08445680c006d181e44191045180c3c004a0b00c2070f848401c1c41c055002d40f003101003013114020403480384281c200f100001e0300025000c8500c7d0701405180518080208480780f6541400c0003e002c81c00024080d800b000b130407000003891a6010001444c0b2498050002591aa04c038100040d1604141d0203041c0c00000079000000c1034200f881c11486282e000d0b40e10b222510112003030000d0014240c803076260040c450003d03011131320800105200e5540c0404d0040aa455681f403501412036040102902d120350300d0020701c01d0140c4d8010764012988070501108130300850040c41e0200c40d841c400101e0306e0390b083c0783c800e02c070101d00e41c0c040040060307940c56001c03544690380e2140138076502c49140b2295058500101500160021000c21403900180b0444 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 462968390 1250 462967140 462967147
    0xc020a09061202031212060112090204060b030916030809010f020c060412020306071407080703030905100e010b0303031603020a110a0b0a061430060901060f1706070507030302 77
    0x3003000341d40c8507400055102411011210841c07034100900103084070800c41203800c0c440b0b5080076062028005001e181844464030384030083c040c495101c1c04446074010410480d86444410810040d0802c540c1402e1a108800840c0c401c10710012040303046070341c0819254909000d603401150040240c1d50712805501c21158204100d0b507071600580042c00074402010a410103d004152170704402400000a0101445a00b0b5405280c60120740f01d03944c10256080da0703040c2d0b6240803001001403140240084c02030386241d103422000da4220680d056800e01c0280f2100d03407140201074132032005446e0b07015640c0d1825911110b0601070b030050b00a8011a060500003002c410242c0c0742404c00c01034046540305440c50410000303a90720310507103014100203542e6103620400f91011400c00300000c02070580c2d85400c100d44050582c1e03002490755903031000c0000d42d07007181010720600b8043d2410340140d0421003084a00400d0003100d0380b403a031400d0f2000d00000e2038251900d160540c1c00b548080c100364101a000c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 462969640 1250 462968390 462968399
    0x60901050c0f0d080c030106080106032304110915130b0d0c0902040305010f02032716080102030105100e0901030b10030b091015150302030c040905010f0608060307150c020a 76
    0xa01000c0d41c0050b42001404000541000050031208002d0420000c5001400140104c55014010a054440030304002802c16400200b10583c441e07454103049914404c8820030040203070120350a03401c0380043e50700c070640fa114140103441d080591510160007004c3c00c40c40400004240e0070003485000003400d20501c80c0300540310516002801d402001025030006000c02c10003a00340701e09043c3c020300d25011070440c200300c0043c0f00c02da85a0344807038180403509040c0b149200c0c0140000d00c0040459004a41000d44e140307090b601070341003403251600c624581082e40030564024110411700364402071100610b45e0842c1d40d0b800301854003400c01c8071074403c5c0f0080400082c45e5810107a0082940308000d19001410015070000d4615580401d40c2c1d0b108c4089003040803442c00002c0d05507015580c2000340e02c960399122068414003c551041c0c10213400c010002038000ca115802c50283e035017596951808e5a0f0f01c00038140e8030011449045a001110000789042c184140d40c0070030603e00c0100505030159070b5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 462970890 1250 462969640 462969643
    0x6011b020a17161211060717040906031104061d090a1203050a0513080f09120d0306060906050f030f07030e06010305070f1e050609030321040b090c030c060901050c 72
    0x30803070b0b001e100d60100b64556420082581c07a03030000c140d001e2201c880100b859883c800140000641c040c0946404241d031010002d19031030460039503020046281e25150344844210241c041031100366000c084070640fa00c143e0400b40500130603600f601e51101b8504082c110b8064850038001d00344070b546d0107034402860000e244803e484c00d00c2880303582c001ca040d00701100040c0440f607004d8510802040c1c58040e07140021101e50031364501603a003010040d1200e60940c0461035003040455050030754042d22040c480550f4060b4464003d036007280d95410b203640c1c2c03903d00c02d8070284100b149218040c0300501c00030300080400c00c0c0c00303075010700603140201d80c4401e20050b040c54200c0a8004a0742c079000a13005000351020103244200628a81d0241511030904502148604d000b90041e076001e02400100900192410400c44122841c0441540b8206092004240202000b07480c111444009200855001c090000e2510000e00e8014003030171050070030030100b01c4203910040b051814030105001214a0707510 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 462972140 1250 462970890 462970919
    0x111501030609110405041109060a03050f0a06050c160b04030e04050a0c110a0f140a020a03150b12060609071101141609030323040e010b1e0306011b020a 67
    0x3080740301003800d08540c902042d40c080311181180c0118074040422012070f5080381d00c0005540e00307403556207854841c84041201202c51f60009400340c4960103800d80c0c00c80002540c00066030148204100903229809451101e20410402500e41c400e402e02d01e10100d00c4c2c800d8003580082c42420300c0f208071242d01c400304080d035808440b8101d0315590790700c1c1c0c030000d207801c800181e50701000c080c050801100345540b10045130b41c0500c00500404040030b14402e8800382003041508a0b90000c00c01251103a41e0b1078007001e8170f050842c8a020b114100704410145041a4240d018548280000340c00346540c0d90080c0002007000805840c1003005007d4000303000e100a104c0d070a5285403840d060b144900e0008401050f10000c030554004005010008001080c2d0084030020b120140050100086000e400c0b002c07080e00a0303420190101c1c0c1c04e40f000160f05803010004000000d1a665140d0740380501c441001c1550100f15205404602018a142c0c40c11224600383d4515510042c848a103da8403400c2d020314104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 462973390 1250 462972140 462972143
    0xc0d08030a150e0403180503030901200c0301020c07030302010e0c0a06111e0a110a120807060b10031a0306090303010603090c03120201060e181203061807020c01120e0601050111150103 81
    0x6451b100050000500c0340078010182400798011403800c6002c03400204040d0b0160381708a541001c1c859079079081c06045c490721454510080083d9100d5030800d651503140c90705072104034099807a20081850503603010800010700340780140b62803803840c03800078242e803845c0c1403111111160082d032044c500000508605005500c00c18030003026402214500201001c5d400e0300740c1c51040e0f12454041092903242c50742c44030500da200029944a200c0ba142400140c0945042c495101014416002c891507141c0d0280600081c02c0058042c0c0307041c000700b895119402070340c00c0006a00100018000c4a0007500040314152042c42204c006135925254030040d503061039054030050b51a000c0410908502801841c0c10054141c1502c0e440c41f000d400203643c1e00410343c0f00c1b14100001100180d8285d5030b11240300e18080000d01754243e07514002600a46030742c00e031a805404a004002d1a00f000c062600c242c2c0010b9450304010601a402d090054560181d2000c5e2200d07280310307072000024100b6101c807a00c1c0c000c0d07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 462974640 1250 462973390 462973397
    0x14031507022b03060b0403020d0f0f0b0108010906050a0b0d03030c050d150e010501050f03011211030102030f0f07020a231e0c101103160206160f050c0d08030a150e0403 74
    0x1074049400060613601c1da030748502c0421400740828005a5a42501110304a40c80b800c2400c0078042c0b403504220301c4181c090f000c0c3c20101004d000045489064005c0618540700c2c1034100a0381d034401728810111103c1010302501b000790821181c000074001e0340720204460282c24600d0908048962200c16200c0c1149540c565000758141081248019000d13103014250034244941441681f04034101c1c075000c14030803000a5280c44030074106021600414039080c0e98094000e550380e1415031003986498100396250a40780d0340440c0001c2c402803001c03c0e501142548000c801d84d15520400c00c0c0c0d06c01d1920042c500ba00c9024038010294481c1c07441000b446010500c1010701a810042400c0040ba00ca501c0f011605000d140340d00c1848804020080722000744880b1902c403d801d000340040750042c0210030755036044040200c91f8100f070002240c610081c55205500711110f00c101c25050103444072140710010040b010a10206e00c40c02c021360004c0700e400f4203d00c4404400f642da050031180e408016901a80407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 462975890 1250 462974640 462974713
    0x5120106051f1205060103020f04060507030207140307050906030f07080f0705150301150c1221020906040e070c05070605031608010506180402071502040f1403150702 73
    0x508200220400c100b600d02030040a1050300c15001c0c03c0c500b00050743c0c11507036030f4903030028820f0b0307010754196001b00d0103d4031880e880703940350000a070080d40410f005802602c42d03140f0002d584c0034102d14188000101030080c2550034a4030040c00b0300c0c810b004d00101d40c9401000303074a421148040103614000d01c06c1c10000e021549035140d03901e05000c4150082c50013104c45d4511020480e00700740440381198105400000348110205003120a82d00200300102249144044016040d5001d6201e0180700021002da03240c8100f501a58412803003907144640d08850144420040c03410b5011607d81d00c80e06504084c1802103a45d82d81c00e0809940760004c4010640110a022080d03806020786280f641490900c1c0501d941414006a0301e4007480310001c03013070707000300d020303105140c440703406845200c2c0c0d11455035030a19640601700c101941050003035141200e90f080c000200340c4040000c02c045544007801a003001d08070201d4400c603403000206404250310a030604010895500c07040f182001251084481c0d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 462977140 1250 462975890 462975899
    0xf031302090901020f07030e06090405010f0609060203160b07051207021c0c110f010201090c090c020c030a0f03030906060302060703021b1203040b0a0e130615080103081b01020405120106 82
    0x20110000d80030520584c03042c070039980162400b0b0304490b8810b8241c1044043c111041e4001401c91280441813500141060300020705000c01c1a441d030142c41c400d8668800b842d4131603c040341c1d68082e82c500e403030205500c0440c090201d500107284542149152510516042101ca0010480f00042d1a04001603111091607680341c8800840d00f8900503461400440801035034072910500c41c030600e5001c3c0320b4640b11003900c01c0c0f030b0300035802181000d41c0b000e400c00e002c9580302c1414000b06032909100000d801b550071900424a80403400151103a44040b0344560043d098608900510382800100d130100d640d003074080056903d8001600200f88039070700401950454648141521441e200010f00a403840c042c450421300c7c0c08002e84082d61079004003643c80741c02481089842c0c00e03000308241d400150304051600040210381200060303c0801c0d100fa01085100d4000301c4142d07409100280012001340074003081d4500081d90300c0b45030b6a5607000075040c03d8940000400f00ca204103014246a07554060401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 462978390 1250 462977140 462977149
    0x10503010b040e0d030c0203270a0501020a03080a0911060301030b06010915020a06090c09141008150a0f0f0c051c020403020904020111010e0d031a030106080709110f031302 76
    0x90507180c00c2e10280150500007074042c1e034a0b21414014000c0c0764a45030300040082c8204141d50305060000300c02c110903100f401010007e81402c05000340516040b21020516500000703600145030781c90b80d0349000e2990f40d0101d0100030030510300300b12404032980380410303000d81da0000030b0750103180180a001e845045c0784c00050301841041d48160031300385018096441e07079500840c140080c641c0003d80410740c0781c034a10302010020344c2d130b40180b80300918185104000c1100c3d01c0c03110f0300c10002c030a4103842c140d484d940300542d00c4001e04400b948040150000a2880c01190001d0140920026000c200c4040e0641e00c0c41c00d4a42d040043c1c0002040401e0300d80141c99003142022180040810451170241907401084d110000203001a050000f83c40142c1481d039800d60084c400c505000b03051713403130580300c1c1d40004001d4004690601e2442c90150f0080142d8034041c0325801c201c40783c00e4014003142c1d160441840103040941c40e554184038041c40000c0070008a040114401c504030b01140700c5030310b410320420 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 462979640 1250 462978390 462978401
    0x9150c020409080c1b09220602040608060114090a0302121005091b01080921251a090a1b050303221d01051e0d12020712052a06040e01050301 62
    0x103e003403503800c08003841700761210030b1110b03004481e080324209210ba00010a08507040303000c80061496100080c0000c0303099110001034040e4400345d9804026180d41c82c20228503010303900341c041d03002003d444200014034002e4240540152142c0681d000380a2180817081211002c0380d056050350003910581100c9113000d10702500c204400d0800c03040506226a00b10f0751400d8480001c40f010100c01201e820304041d9030140c80322403035481e001c65039180f01d21111496100aa00f01220240d03402500e40c0b495040c81c22030144a60030030001844101c0d41900c41e903000701c2c0e00034201010206103107004515510188020000101e40c40140e0021426580300c0c002e09140b903074024425000c040ca0a0400c8d114031914040c1121383c11102ca6681d610392088801d510100f01068640c400c8042000300100b01032850704c0340c40589071f50203540340c1382d640e440b080e004d200095500900582001011920b80c0000078040a0410f143d01070f40700140c0041c4c000319103030b94010b4000464403004c07040104130a1a0034042d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 462980890 1250 462979640 462979663
    0x9160503010212010b07140f0d03050a270804090c0e0a0e0105060a0302210f0402040c09080d050d0e0a0503270105070204020307211e020a09150c020409080c 69
    0x843c54002101449480030b40c043c0103413681c8480000312802403001c040d0401c03002560701c800b9a40d2507404031100c0350b610f004085040f00824101000a01c0101c001d20400703182164598900540860850300382c4007807119201c04a6100005000218030318055110f802040c0d0b00f19264118407420b8031007000b1180442da404444000464001070149898140a58039190340d1401c0141c0c0760b44101d4061030034608000030704403101713480404001d00d81072407982c4940070368000d980800006115140448103140c56024862595010903440f411591258008060720f91009034001101d80d149001c1c1030600c2ea110405407000d9002281d010382808103a1813008440d1070951480707454503840e90003c1c046025561020f44200d9002c0005440307240902c080351840403d503040740c890420580c140c1c50007441c20300e500031385e400c1d0b1410a83c81a15007070f10881d443c100030354817904400c62030160480e880e910f00920303840c1004410040342006032140c0c0030349540c07141300c0e5a400c0d8543d46070811a5250170064002c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 462982140 1250 462980890 462980893
    0xa03110d0f050f101806090f02030a0f0c051e090406030516121707110301060801020d0c02060c0d11120a2a0c1103030403200102060718051c060509160503 68
    0x4d0218a00030383d101e0310101c5402d0003900c05001c80c101d00301801040d003a4061802203080185114002c80d4a40c0103504c03503101e4050800c4024021680e1104560310050b035080420310030010a0180b92a80d24803500e854a4806400e180c040504089000e41d03000f90310482d41a030002c800c49000c10440242c9a000c2c00c40142da03480b1644e0706458000159000240c492000e890000d0804148200314441c01c0128801400074482c5076920b030000c40c000e522040c41020068a003001c103096903840452444d0013810442125030420f540070403114002d080c02d100021340c80004004039009404d02d03100f5144140316240000444107001c9014000c000c840b41e400c408000b10480391000d0a0b6007017002c94400302d8010030700d441448607050129240d0b2055400150400d5003005034654100180449110b02c41400c1e0700f40c0341d85440d854019241100d1000500758424944502404503061402800d1500340e40c0c5a41e0f040902c90507140c50044807000e4035040d01642061686038180e840c03008100703000706010303030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 462983390 1250 462982140 462982171
    0x4030c051f05071b03020405070c03081609050613031e0510020702061206030f030423040501080a06050415020f0d06060f0210090c03050312070306080a02010507080a03110d0f05 78
    0x400070524414003100800034410341d000d43e0356031002c0c22040400385d903000d0300821840c00c188401500c81d540d1140c08400084080001401c060717501303c41c2071a05283d603198540030368145801c0120075000004880d9607080e036104000089054110703050034a081e0300038860038540b981e050090070220900603140109004020400068a4080885008240a5411164548a0b540005e04040780d003030a0710004e2101080109401c0110541034280c60070300e00000501c0e0301c031642800243c175401d105000440d0042c2c1c00540100e585600710942c03161040c19100c4400611603041800ca0300b10904901d0815804105456014254403a841c003a11407811320400580c04c035500295039900d402c00c0740144e01d856a0366107040020440050002c2c41d40942500d456040b840510302e403042c0112007400019040c020f0000d4148004580f40005540603903800d0325083ea01c0d20b80d0400b80c1e004031071002c01c15940b6001c44080c1c000000c00b406203100c030100049000c4014000101c01d483c0040c01301166000d008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 462984640 1250 462983390 462983449
    0x30203040809040504050f2409010b0603070c050111030114030d03051b160501020307080f13030c030e01050d0c0306090c0503011503180f1a16170603010204080304030c05 75
    0x41c400d840c0c450008036804240d59445180207802d10703554925a594603c00d00e1520413600050ba040c40300c482901068113402039640702c504a0076100031103a4190403200400c00710310402e100e0302e80c62185a002e000003160f00000c0d20110b440030380c001d80c0101d00000c140d040c4c0c010340c2c0c45c0031f00044001c0e2100d031400388001d0a016200001000d0210f804219403440010384800c8254910450300610343c100008544900d00103070003400c0d50034102c940c101400c1a00c000a000069408109881641c0550b203000e85501c5a50b010b88031b51018008190600005108409130a1502e000341e03040181241d0700030841c18034003026542543c042000b00028010b040c001445200c00c142030007030f00710880780341c04600c00c1165a8512804000c2c0700002d8020712400c8400c000380117004a80c4c5050a03008100d00300c42d6540d11110002d048d2450b40c2202c00140c0c0304540c4c0390790034403800c801c3da080b04e4010001407600d0380d1000c0562440d031090b40111502e095021042103075107056000b01c146000e800d2602480302030344 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 462985890 1250 462984640 462984653
    0x702010e07140a0503070e0a0c0f080a0f0608190c06091802030c090a0b030603060a05160c081308011a0d080421080307170603010c2a05030f0c01060603020304 70
    0x40c0101c81910380782c40b5503000c00750f44a0028200819014040c0e038102505d4982600b0403440464005100720304022340101d04501c00e182000d07244555984480d11521000c01c0803001d00700030074182139020349030301c0042055103040c400c2070000c80c090581c807052800343e403900100051403644003d0038014442e000b00040ca6640c0035035201e01c0400340c801690795035000350030300380381c050440c41135004405002c2c00b0600c56010001140201012400c40720150342d9800d5807400c0d5481107a9180560507002c14039802c2902a0f40d00d40500c83c070132000b00b42480e010044004040040b0b5000510b10717034484514051050300442e1114014000b6140b0516103006503c07500d80070300c5141318061701d010a095000d4a07600749121405050f0390705c050040d5990500381720003000c234155840000c10200c000c8d404149540307014070400002d0103540d00c9000344424202c080444014582d4030078030030f00030081030242c00103009100800c051049800442e4442d41440300703190840702d20307410030403e01d0310408c1070001150300e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 462987140 1250 462985890 462985903
    0xc030c030614151e0705030c07120804092a0f080f010e011a070c06050403020f011e1b05010207030201060f09200a0203090411030a18080a0302030606070c0308040e0702010e 76
    0xa80d486002e51311400800707510015041040d021891050110b080f00c10041c02000801060303000d0411111040c1c0c80303132100c82d4007140e82d00004007041c004100400c00c05205400038180d200d91004014218083d0f1000b100880010b03c4a41c0001100c840319101c116420600113a0131034540000d102d001e60420b580d05802d007a040c010310700c10040c0c4840c0305100c00b80c51411110f03120b51161a841c286503403001c0280058103c1e0004a00c10180000c0c1d2103104e520070b840e880c0360350900b10352481406a000105540c4808041108680324000d8034450010031002d00041610300d20943c000540c007450861140c000c09429001580e07468104003d40880c0100040d5110b009000502020303a942c1d07150f41c00780d107144104030416030458104528800304911b11005548205080403080c0000a0f0840907001080110000149030103418405280d400380709070701a40d408031028001c5407504100d42c89000c0c4442803644100e03904240041d0501002d43da070000d10b5009102800240950000304403015100c90 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 462988390 1250 462987140 462987169
    0x2030307030327060f05010519060e030c150d50180606060a02121813061a0a0c0f2d170c0d0c05100c030c030614 50
    0x5403661064024410b02d0100e00740081e2440c002448403154134901803005d05014550398440d1890040001513070700b44035030344882d009918140200064200340f4260b07071003100c5109458040c42845903e04143e254261801032810740c1d0b64050340c5075042c900000c4142e44094042c2000d90241c0d00d081c003000380f62420711425000a16104803e92022203c0038420b00f0740e204d42500007550300200707100c5084800000960502030201c1910342d20f503030301030502c28184540c8070340c1c01c01a030180302c01c805240400300240c2840e8110302202d080111410000840c030796441e1125169060b598482040003886205030070300200c1d016960b29083c0458450060a0707039040f000041d01c0300040c05268800c204010540c25249400f42070707030700d1681c0c10b402480107000b8458001100c88507640019081c41c900c0142c161200c164140c001450030995040040f1090009000c00700c819114801c4a9403100e030881c01069030710b9102d80d40029502911100c020150f440c940d0003c1300c22281200880500d40b43c0d4003100b44034a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 462989640 1250 462988390 462988397
    0x150b282309010c060516031a010c140f03120702060f0103021318050f0705010207240c0303020906030f0f060d050606011b17030105180f04030e0324220203030703 71
    0x10a200700042c1e0701d919148200034482480c0208002200304050300507526491075a9007081020070403000c0f15607081c4061365140c045110b0300300c0840065001d13444060011007070003d03140702007a000b110303a25507000442070420003900fa404025000358104602e5620405521a40b00355501d10b4000c0b44842840301510402c07203032140d610180198030342c03403114561940b202c101c50040003564202070301c402c214003855006004248001540504104c44a0541101402c20301e90031500c50500790f0303c80c12081412270034180c00744030850b85c541e2500c02461064800800c95800c91034102d01c00751450000a0200f0310a289032142480840c000092295108500f800d0080d040040e0781c040c002e0205041d85c0042c115000c0e03a40280041840002640c125482503400442007078440c0059050f85204842d010381e9209100005408648a107800c0b01a40d000a41501c40c940002c5c010141020f20b2807046150755203044003408155010380c121141586940100700e80c0300141540000c1d00d82c82a800c019082 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 462990890 1250 462989640 462989647
    0x121d010c11031e0705150306090601030b0a030c03080406030b011e0e0a03020301050108010b010e1c020d02040225210e04020906040e09061e010810150b2823 69
    0x70364904210f4612400440460302480380001400359941c0d005034004c5074022400031407801c4400d020354064900801d401091101c01d50340e1200114005c04001506a6126003d00c0d000004034200c90040d5007d14010341c07500396110300340480601900c004012440c1001350501041015030700f1071a000c0c641080926106200804080005600c000706400c0070750705500c0c01000090010055000000651003a02c0c4e1310324461001c02008011081c007482980e52500440041c00140f0b0304412030a1040c0c80244010b0501d040c000c21444c1e50000c0003441d041c0c80a0202e4401d06006822070820346d040310030300591900c400c43c0d21000700f00c03400c0400081c0c0929004500004141d64140540e0084d0a0f030140c00120341c034060901d03940c0c40000b83da45114030200a48800c00b0f0319900d202c05416160b0b001700a01c40341c550a440c02c0020b0021030205240c0c41e02103100403c08240c1d40005211480a0040949601c5c40b09003600e03c00305021580e103021700403d9000404852550f500d80c01c0b0a102c4c002e407090300e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 462992140 1250 462990890 462990923
    0x1809030f170411120d0801080c0a03050312091f1e020414061309090f1a060a0308030406090507060c1a252a0b06012109170304121d010c 60
    0x4881c01034075500601c0c0c0a4002c0c175603403680e80900800d048804060444000403001d100380141d4082602029010342c20411031602022600f15807607070006500b20403a01c048548100d00c1450740410114400b00e503854640a000803040e906024902104a1408514107450454044071540c5106006805858003103036043e09902100d5102008184002003445102d00d50b1a1074010854040300888940004101e10320034004104074140c0705200242c220700d4080e045490b40320a81d00b00a1003200c0b12503d50003941c0010310203105d403100400042e11500c402200602d4101425819860321081000c0d4030400c11480d0182c110752498009a03081c1c0d2a51121601c11080307039a9481c0d0f0025840e58095220384140d04402c0ca0209107180d030244d0491b901540f40d060046458241c04801050b0840006502c0100341e152544018507542c403585001d0030400c940e00b03001a080e00100c5042d16000d000c81800090540c0105103146030801e200540c414103810302c0006403101045100141101402614801 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 462993390 1250 462992140 462992149
    0x913050f1303020709020a0908061302090106050306210c040e0303060d0f050a08030106020d030617060402132003060103150f120614090a02010e0d0803040b0406061809030f170411 79
    0x10203880c070700606660780c1f03440d00740107080c1030024030170b200540c0306002c009080380c0c030014860b0440582c01031074840301d43d10b0500215400e8102816842d8068100030b4011188010022402450790480010b040c4070781c01c150400c4103c0d1a0700300c52a002c2d400c20010020940c0d9030080d444607140e07119030b0243d202c0d2201d0906078604040c0c0100180000c00c00400031038503640018802403200500c0d034003402940d0310745000c91991903a80f062a1103d9110401040051919801034490b4007000d980008160b0700e420030311040065091000080e1076000424410b007540c0c5809541c981e1007481000602403481c007400e140740f00046210301c3e6007880403441c04508010315504140c0845c50702d29a201c0b4a0700706030020946518210a00302d0104200903c107515504116540c012003980080e002811540e030398803902030000000340211381c05a40c414002ca100d08001d0181d418000350100001480005441d02034014001c1d51014406c4c0407104070310b500d04140c00316065034002d80c844a0421201c4203103001c034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 462994640 1250 462993390 462993403
    0x11040f0b03030d090c05010c050d0305041b140405090312070e040617060601020105010e131709040c1e0e0913061401180609020c0d0828020913050f130302 68
    0x40c1c0d0326002c00100080d4440c9640c00100180c0c0c010b2428009403581c031401590000d1040e07800a140d6045211440201c602a61205621500800c58441c00284080c00d100b50f54601d44c1140c2d009442c103181c0a01d00781001e12589070f108003613800462a2005891040d00f2080d4024203c0041280e20161381055072100d1704000d00901130b00e1b50a200068407891103e0715403404403a80c1b80158a4480001040070000590030b0241644100401c000200c645514461404c11550031040d40000c00c118002a00c40e449a80210700c40340d55003580500381c1560b0404603522000f100010000c40c114010704a03544d080800d0b81184800691174081d420030b01e410005820600e800e848410510000015000a81400643c02112207501040300c2c03602c50041904a008000142c00a544030000083c00140180d00054000022540e1200031568442404e41e1030100c0e81e04042e1b0381600402c03030040d01c4c00c19100d030041c0340650300310a020038900a00202c00040d0014151070601d00707440a5403041c58005d2110 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 462995890 1250 462994640 462994661
    0x120215031009020403060902100f080c0901020304081606020f03030118050901090b090610060305010b040e0403020f1606170f0f07030204120b090c01020a050a080310080a060e01060501030911040f 86
    0x795107540da1703400c02c20f009000441d42a0300686850380761f2102244181c80100e810301440d2501e1065480d080300110b0140c0042c001c0034154030040001148020301041680186130a402420b5225401c0200007030402081704907482182e40203000501070014011409810b5040c06c1000007001ea540c0c00304036002d88140341001e0a005405020301c84100000f0900c0e51141028800c4203945507a1880b04900f194024404e0214600c402d01040c415010f803511510b802a00a2046640010860440324200340c186443e814124007102c0e801c10240d0380151030404403451950707400001c1c2c54144048a100f001c01804081c8140010b000036a00901950507100681450080c000507120309241900450800b0303542880c0740d01c5280303452a05503100095044901b0740c04006441130f195207550303011035508040d00e1881c0301c1d054500c0c00300b140c0310100591021640680c0000c591044085c022900f1100b0305d40001e410503081010f49404107000b04114107000c2402e440c00621a021200d0780402482482c55 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 462997140 1250 462995890 462995909
    0x10506101d010e21070f050d030207120501150e01150801180c140703030b03120f07140a080f070c0e01080c0609060f130306062c070905040507181202150310 69
    0x44080104c4001950b0000d44172984041c00b40300e62100c0c100400740d004500c00a0042c1e00a460610002034100756014506104000115160085808031040301281c0c0d000b5051030309503400100405201030101800921007414001d056504003c1410501c2c01080c100e102140c1c3c84130300e486500c1e440345000f410380b03645050009846001600e402805003100e41002d80c400d01c65201e80701500c80d822012100c00c1080011030a2030194695540c641d8800e00031803095040c001c50401402080318003004102c02d0f2481d00165a0f40d100b2351800020711a80781e00407a005040100061156040c00214204e0340d803400c45545894001040c005003861140c004110300c110f002050405940c00000001c1e01030702c0c070440c010f00855032078641903142e603480d02c180001100745290702c121a08501500b002c0e00013189280907000c9549880c08a0151038066601000240d1502d004041e4134403100205005030440388105035582e04603030005071095203c0c182801c45601d0001c081102641c1c0f4640090040080c0c12 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 462998390 1250 462997140 462997189
    0x1003030c14121c021912060902030c032721130306140906060a030204090f051e0f120a03020a0507060c08040b07030b0a06080615030108010506101d010e 67
    0x101d0009240d00504070300044070701c040c500700f080220180241da03200c00c643d0306020840c030503640d011900e6280c0702004000c03680e504d16020039a141c0a00056206030100c01402d9541c2c00c00b04e040d041420001c0c500702d000b400008500070034190010403240310108914507070034503030001100da6524910030892031858201c40b503840081000415000218030010101290b00d0585d0307141031700c5490b80070482d42241d200000f940213000601d03040e40a501d80c2d5004600c0b0343d500b1280e940d0341506d4200c00c0c81c0074500c008000c1ca8101c03040740d4203724010300c2148090151100c0810401140c8a5001c1e9050003001d1503000310790401e0480c451001d60b00d049030005002e010492138100c0c040d100c0740c82a50180c03410075480d0001120b45001b40100c00940d500035140c00162860700381c0c11503084001614443d4007440b0720031340e900380800440103140641140400041c12381030020401c04040500c04410003804200440f00200704404040340340012000c0c06e01220103035400300003484a5844445040e80c040c2c101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 462999640 1250 462998390 462998413
    0x111b011106070207180221071e120207110405040b1b04180906090203030a2604050a0308040201030609150f06021203150f060a020c0f011110090c120b0415051003030c14 74
    0x800524015290b41d02d800c001c094850275400203400540c82001c0205001c4195004640548d03030040914071b0081c60210294040540000d050f500191000d43e2114112011b11a030840110b80b071214603d450180f041c40d00c0e2410702c1c2c40d60140921110811600c1d0781d80c01003c1804031580150121a500a050740d9807139601240c0070f01072095028011070b0000800b100e11440400500110740583d400c4001010001d8190340c0031159504001e03c224101a25088001600007182c001e003030780c59813800c400f20145030038000c3d00c0c18100142d0740408119441443d8558009400c442100e42015042c41d00d00315100312080451410980b0040e800e401203000150100229404604111044012150900080c0d0000300460301701c00d80d6104007a03140c11100843c0c00950b99503000c2280640706002c960707403581e0746030409110311640308000d4811051034820041007100c0442010314201d07800004110303604050600f02e05403041404003d040c0b003152441c0301700b4040e20168000a04140604072040017418 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 463000890 1250 462999640 462999697
    0x5190803040b07020d360b0918130b09010e030d0b03010b0a0b030a022a0706090b0304080a1d03071e0501091a0a111b0111060702071802 60
    0xc4905403000041800422020b61011a00c5c401c40f500c240e44410035080c0c4080600c0c4080c0501280311441c4101a1020b0343c18801c2d210400b0040082801c0a902d4038480c600b40071080695081c0f140a1111304410015202216540020070540201c03402d052030380c030400442c1c010706400c256414684400b280007015250641c001d030141d910164024080c02e650302d418403421200600035000656002e00025000c507055a001c3d1804204070410711940300c803420741c038014040c5198060190781d00f010b0002e0003c185c00105100041481c49552451841d00c3d4a89480ca40a11400035003000038050740079680952000354404214402010395100369a25075075811106240e1403071865802c61008000781310740c040ca00140489140c144403402c80000319101c048982c1c401017980f014080501c0c07144600f280100461030940c2000f6102c80030a5040d00009400c266000440b45c810303a12200400c41c0c1c943d4045010411030300b0f401c0f4808412455190920041e0064845c100c034041e140f0024079035402c25 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 463002140 1250 463000890 463000897
    0x314090304090917121503030304150203100b0d0e01060e1e0402181302010201050c09011d030f0d03050907121109040c05060705030702090c03011a030907150c140316030804051908 79
    0x30811b25072040f80503074050680f203000458000c1c000b00d0010101d20f5810081e0b07002182e000520341c0da011071164540180e04141c3e001202540c4100b0b60360103d02c03046070000d22071140a058141800702c031074071706400d0f15010210029014056840c603074011034215140c4a24104082c042c480e038003c01850b046a2131751243c00481c000341d0040d1b0a00000c202d1110b418411141b141406070f4078021806800344001c01094407a006071501031052a8480d80b081c4000d201d4041d41c011943c0c2c004c42c8074208103400070b190807010b41011603219003a106030741c0042d20311582d2204d5407005490000ba940c1c0c40f41003044210105030b10044d0009400a070b0a82040804402002424030840e80046a903da0290188041c0002d0240d9580d40a04200308500c1144290185601920880c2299040f40c3c8918a4041301c101300a40c4a010a0148000c2010001505140c0c9103020360300c0025401c101051104800526200300080d080c4800310000c20300303110007400101c084040d01881100c55240c94a00b1990717560 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 463003390 1250 463002140 463002151
    0x6111e0d060906050105091c050d120501050f01050a03150b16020a0f0b0417030702030d0f080711060a0b03030702040219090801060806042406060906031409030409091712 75
    0x51400780c0104100015124a0041e00ca0603500c0c2820710401c0300501851036526003d0503580c46580c4801070000d401080700049221050b80e42d59444920400c1c888107440d4107811540c46007180541d00080d41c0d80c014103898001d4402e140c00714500132202900340441060b500075003032598000420790402c06030314403501100c500c01c0c0e5046a8495070b60142c412040c0e0325002d040f0001070708100c1080385103141404d480b4610401000d8a2502e038641d80041d03d062101000000411700e86501442c0303550704101074581c400414185886a12407c004d8640c5410000708a60081562202c0340480d903202001aa030f440c0768017802c219640d0b1600524404501800d501d06e80000300d5070600424020810b0041e2011a5807440080c0003e487d29583c1c003488643c9c2c00009005054920180440800f55009000c005d002d2620b03500c03a404d0629a001b41034407a15000480d14075035200c14041e40301400022201103605000d000500400c2601d0100702004150501c140070200104040100200d0f503105d0601a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 463004640 1250 463003390 463003417
    0x513020a151d03031803070f1e09090f0204050c0d022205180103020607030e030d090806072613081c0c0e18040c05030f0a140a080706111e 61
    0x21002102000e581d00507080d42c0b5800d60410300200c065641103034190312119800806407030300c058407906142d140002031361204c001880300c2c01e24400003041c0030008001038106808184201100c94465008031042854024040c0d035076000040c445e145502d040d01c0c1814080d2100b95039400c002e405c0702d41451802c1e00c42960034105c916001440e440c00108400d0b002101030b60000c6130307130318680030407510350440001901404042e5201e81c2c3c0302e65090002e04a01561601c404c2d94080c1414041840e00000401703840034485a1100100040182e13070311948100caa0354240030f119038a5929000c0c48103000c5900410300800442c06022080c1c00d002884818040ea117006c004000010000f11a0002401940e541121403109403006000b500700c185d42e442409a6803c901a5955001292501c410800d610b412508007080030350811000ea1f07c4480290300c0e000040c00000020340320f4250714450309d40001c150a5480e00041c100140c240160b0b0701c40041d100100e41d480c2d250300c0c55103000703034010158240340 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 463005890 1250 463004640 463004657
    0xa050f0d050301080a06021614100f2009040b101709010615030e0708061632071a041406100e0612031e1c1803030513020a15 55
    0xc24030800c282c82c121803043c0001c0c00101007544941e8001d60025240c0e20442c1c44c030f10b00b0940440e00219820b800300200c1d078000c00b0141c2d0580e102d007003140c56840e1003044580c104014140b103c40c0c00d043c0da20310a15003032007203030303440f41c10000180052014401194110814280a40703096810944510b06100c03480120f03000c50362580728950803034665024070b011401300740148d442003074884e601404c488207064040302c4050b61a200801d2905004403003840784804035640139400d40b54008864804844008070380703c1ca103040348902e801584481a020203003124049050350034016604000605400150189081403c00342050344040086035a1004030b44034031008500180304d480220380448a8012804d080d17620b034a010449400800d2102c0b44643c403061040240320144c0e0a18803010b440000c521a41d1840701403180c5a8035201807401c8658145400030781c1c250200501c071340e5200360307034145000540d50303581c64a4181804484900070b50800c03019417022441108030b146040403140e00780c45aa20 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 463007140 1250 463005890 463005913
    0x20307021b031009020105070609082208070902130f0b031e0402010206040305030603160e010f0503161a0f0a020a03020c030706021f020f0316090603230a0e0a050f 72
    0x120403a07107149860700741d404004900e588210b00c0e48008040d40c8140350481c50b04030152104000c3c1c0c2c1600c40184c4d01c2d0080011214482440d11a001c42140c0ca0024500e150346c1c070b441000c60300e5038801d205907405a900018944291804011482c0141151200b01132840d43c039a090800590001c450740a0b40c403440c0751281d0211034040c3c80309440303564140e00526550307583e5a82116a81c10107044207070107200741c1d6203049d0400c4c07800c1c06000113000c030005070001c43e62500c0c25591102806501c000d02a0b0850081d05681e212540301d03000c1610f1050013000c1c10b49545001a24043c40361000c1e13007a100c00e000c07600000d03003603003c560004a503006c1d0b800c403200d021740041059103810309131081038050b0340301c00c0415031401e40440c64151607201c030000040c2495943c0314407121070741c000c030340202140100b56003603042e103504601c850018180900d01004141c440a10040c4080d4490016021001c100400205854090f030090f803000303030344ca00a0b0350010a041c40c28070707600d4428001d02c005a0044115201 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 463008390 1250 463007140 463007173
    0xf0c07021c0201090f121403090d060516080403080c090a05040608031b030c0c1306120c031202120301051309050313230906060a1403040c15110c130b09090102030702 73
    0x4060300c02052200c0000c80315a0b47c1c1c8041d16903c0d188401c05030000340705030031903030341c80c01d4401002c0f600444d404a01071420803044200400140035420a22000400b03120200350300c106400c0c2d008200360b04848d907510f02d01e000a44801c2c05a840281c0c05810040081003c0724084080c0010b07288010801c044500c1c44000c0c07580342e0044012118040d03101d0702c80003510385000041500c2c040c0182d44001042900e03004013425100090006403100d01d505413041040100c10009022060802d10151424a840c8840002c0c94032040c46400d00c0b4541c0c4440040030814180d01c08222242d0020440342e80341c031107a03c0a03641c4603051050000e41c400b240b88443c1c0c0860f104092640d41c40b00184040003a569440170000c0e91307004040150108008000320264401003a0010f6001394090901f5610381c034a480340c2450700031035540541d800c0240d401c01080d40c0c00c00000d01d180148108032140140c0303000944400b0028014a840d20f0341c4000d496041c4210414103500841c098043c2c0d500791049005505c0005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 463009640 1250 463008390 463008419
    0x10e01020f0c10030f0908070210030c20030c0f0606010908030c0303010302040207080f070f12030912082206090b06030303040b01050d1a040b0a05060f090f0c07021c020109 76
    0x145015008a40094a103141000c0c04051100c018100010850000700e903045c00c5501702d040403507100f040000c40301c05503d0819411003507841a40b8003030144032090000203000c030045003813841080600342c60303014076801c1c00d1042e6203222201c0421a505424a0340845581c0d071001d4800360b000c5822003402041b526000b104540c25292484011032559103140d090000175400041c0a45040005003c1c4050501c80381c0003c4c0240c42c01490288802180d506002d44100700e2000620f00307244c5864a65000540a00990750f05840203040c100101c1e075914000118030f05c2c22040442c0090b281c03014000421070705504c40d0108c2c60292040900c2695014145a503902c4255001307865074440d0001080585840440004c400307110710441d0b1210201a80c0c3c180180700140c40c200d503105254401c100030304c01c0e58419568006c800700e40040f109100d4030302159208001034002050100e02100003028580580c0c2100c0c07078140d002d015502c00008812000500d2551000200e0020710350180c0080c8544011008 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 463010890 1250 463009640 463009663
    0x60c05060105060a180602150c09030c040504060b0a0330020304120812040f02040b2b0c1208030f090309010504092c030406080f15010c03050903060c0405010e0102 72
    0x1080181d0074801008004d070802400e41080010010701c2903014541d500d55180203201580052041c1c800045000311700f4640140f00b40c0b081c41082c0400246640c1c00900d840b41620141c50001f0756480c1c03410024003405074080101e411031040a000030030052202040c40320240107480c0c030302c1400203c041240a4081c0c0503050001680b0134401400f000c120702d08800700d580d1013203981500d0890304c1d06c903c0b00c403503c04a0702601c0060807499a0410350411340220301e031f4042d048600e07030340c103916003075a100300f00514070502000581e040401000304180101044007800700100c628440d44100d242140e000e50003201c0720700d40b107218580804c1e5a00c40010564401006c161074541c14107040100c440000d01c40b90503103560248048e45413550640882e20101c5269180201650b0740b00e04000c0043c14904000c0e2007465490644000c1000500026598a954117000d107040c000002c020b05040b40c4c9400742c602d6196050143e41c00780240420382c0780c010400c6403000e88800c00060700b503000580c3c03122000f015 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 463012140 1250 463010890 463010893
    0x40b0a1217040608180a0c060302041e062f1c1709030307050d0b0909010e01060f1d0702070905070c1119030602030603070909060e150405030403030503061f0207060801060c05 77
    0x8911030346078000c00c4024400f8000100d4140300d04070341f910820b401d0343d680105c02295001a0600081d5a41f00b01c1f10021910202d54003050351401e000209808510b81c00d1001c6030340011084003007403030400701d4005072401c2d91049802000c0444003d05103601031500c0d640209000f0031660b400e02c0c0c4450090381c442c0c0c0c00200594115a075210b0186c44a074403a428030b4803600c0c0d40380c4540400d0f5031011400c90240f0b801200001d001c0c04c41004141c215030f03060304842601c51900504104014070403444824840d15110b007021907450303200e0243d00e00b100075002041e0385400c2030b0400c2009075000700c00c0d241c50760150003030001000d01c40701031108080f40c04691007000b8060b98420b00201d07500750010b41d041800541121011913607602002e0031207201071812142203171514552401c0110070002001c1c1001548514021030030980d60b1181c0d02d214900c00181804404130000d00d45075503180c800150113030030788101c01078008819002502d69240340100e4000c19454030010440c00c0c0305414102040d40d0200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 463013390 1250 463012140 463012157
    0xd0509100e03061509150303030c0906040f0b070213140708180307050114010608060109090e010b0913050d14070303050414030a020607260c09040b0a12170406 70
    0x20103224005822a00880034400305401440325602c0400c04039200d6010420101002007100d41040402c40e005007540e080f100300c1d005010003680c2d0110840c2d41107a6002c0e85140e41e050140c004c10154000c543c4208c1038141d41205c00194a0100c070000c2c0f01d880d00c21500001c2512480311000219181d813084c074200380e04003a00203220240203034413031074000240003440015038003500c0c2e540e40b0750b50003c1c5007103603da51580c401e50701c3c5402c01030002c1e014211b14107042c0200d14202000912500c000d00c0b414080e20340350780300302c3d41600c400c0d1320015540c1c90251500238985084034070000c000301ca00608680c5881000c28042406100d00e881c4800d004901182500e4214a0740f00ac5018003030250055408032600074030344170301c114108020300c111100b6070060185442d10380d03c06002c080ca00c0d420584080640201840c1f5021a01005070740001d0086149456000110200e00203011004580d5000002500046062040440b0030b10405109034085002502e5007074115140707001d948100008560000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 463014640 1250 463013390 463013407
    0x607120e030c040606050d051b0f0a11060a0e060603010c052a030310081b1003020f07020312030a1503020603180f0613110607030e0f0f220e0d05 64
    0x2800030651001004080b102100c021400042c2250b281d45d0080700865000030b019549000396010b126801503020000d4140319580441084862090300c403119880e00b40000d05101d454094101d0200e00303070328002114254544110b00d28020b20300b400d86003045125074070015201c0d00c2e05004034401e00d10ba035501c03641006032510600e1001e840d1181d101040720180035910a10810810181d07210b80c585a0f281c440f42c9241c00720321428103140540414036441e46048188154964a0310152907003128079005036503003032048102e0024007460f40000e505005400d04090a01c4d00350000d180200200300c800c0101c06648100d800c0349849070300c0025000101480001c0c0c208084031b487c4c20542c031759582901c0450242a0601f030602c40100c5030199404283c02c0000240b1800c0001d8600350380c41551428031300307101601d000e06915200d203001445446400d10340e6900391540382c0c05400f400d0703000c0c02c00070f442c01c19030350346c43c200310104041404018a4601500c508007400945d4600401803500d50901d481c00c0f4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 463015890 1250 463014640 463014647
    0x50a0b031302040b010e030102030f0103061404030c02010f030b1f02010b01020d09090207021908100b060a1b02030c10030501180908030109150b040e070f180b1303050723060712 78
    0x80ba1314440c18050001c810800b02d882c03c0c00194480c01560312251368070760440c9402d600b02c815141320300b5003c2d6208401c11001a811010b0100c0103902404c1405030f0b0119410100d019090281c1c1080e0055441c000e0300d088407506035101e0303100079074540003808650401401243e40309170b40b12100b000681d1501c41008402c4280e03006141c0c0a0004d01036204070516803e200300500d001ea88200032546c0078480e0180410118802d407600080100e899904d04002c003d0020880c01c0c04040481580c1c41440c0420b04565080000320130882c0090611076103d00007040140080c1024864480b814000d0205086180a0f80c42482c0d50740e6031289080d401c503424012103c0090001c6003084902491040001c45c039001840081c000404442a5921081c5031614000382070381c1c42c009110042c402683c03846801340c1c4001c01908192070079108400c1d201d200c007020158010103035602c064558021144003244007100904030740ca05644c42c1140042c540385104c00d2214902c9034030300152074040c0164404409621 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 463017140 1250 463015890 463015901
    0x5041205120301180612020901270e010b150f03010303050a0e0a030f0201120b03100b01140406030c0813030e0f180a1d01020c12030712090c050a0b03130204 69
    0x920071241440d0140c00d10a00c0c0c2da02c01e0700540c141c40030f00c100340c0f40004154099603028124a401443c489001c2d540070846071071043c080d400ca16074613104001042c000583c2c4484121400842c141f00980e10380952900900880c40018000c2400c04591100301c104102211400180c2070203061a581c030350340301190a07800000d082010044113904e100d0341562086600c2c8040c500545a5003040442880003501004d03080700c04c59a15410001c2d01034503540c0104480f07039402401d48001c41d4540014004031100e10003880c0030408064042004035005906511034101001103403145102512200e21102c001c6405100c020002402400c89102c4c41c182814030380c1001501034028070750f8003528403054401400031501d042040b40c2d2a140c1c2030010001c0f41c1c9141348035031030304001c62419804040594440f5030101c00c1001d114000000304000f80e2007503a0704012070003080001c00055005245c251054119072047c541b103020908004100c91085070120782c0102c2d03c1c0103032035888420f281c2c2800040c24 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 463018390 1250 463017140 463017143
    0x40210030902030a050706031e05060d02010f0201060e150a170714011b03020609061b04090b0a05120607030c03060e06010f050d0c020a05011b0f080603030f0403111807050412 77
    0x3405130500001102044504054540b07920045050550507a0b000e20108051a51155040c240400d121041c3ca9022440c1c2c5403a40a28000c3d038440d00340c1905030b015100d250700c03811460b14004108441000303060b4210210486c01c8a5100420341c1e28010b01440c2002c564064045d6000048104001c4850842070850300f0010f05101d08811500c0da003501908009080540c05030f0804410001003160a101013580181c0b1a8082198484240c00c0003029019600a00945d143e80d07003d4034880355204503015000348001001804041d00100400303441c3d010650342200481d05040a8240c0103000b13000318001c0c1d41c03190030030301c039240d9032180110707103024170b10b440740e400d10004100003000f1385014002c00710b00030180d4004154030901840c10f6800c507600700c2c8081c0c2c201a110100e00c5030041e03000c0c5075950f4540c11440e0401007074440c0c600080c258400d600082204400001c1c0010400c1100d00d918444141c1c1216030118103600c51401e11440c0f407088a0060000b1410401800760039111500d018071503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 463019640 1250 463018390 463018393
    0x11a03040618080304120f0c080319110c101e1e18020f0a060e22050106080402041a0303040506070503070218010512030c060a020f12101d04021003090203 68
    0x14112010300d0340820b04484059414000000c100700c18851305c00412032009405280054000d0000c20004040e000340313900041c10f00c0c10010104205c1c00c00b00600780c4400c420103600700304440c401600011658012080647c090041030851451207155202d0b14254000c01401d480850404518032070043c40002c0b851500910660302c440ca52481501c54000c56903110034220b40c0100640c010402e404080f40d8825104007039000052008986c4240c41200016080e01c160346c8507144540505000c0f50b07480030504460740780c43e00025207640e02845040c003407802502c0400900050507207000e1580580d0f0040d5030103601c02c000c00c201c1070604500408075140158107507820b00b0b440c1d50025200e080020116905c1039002c400506c02460800c1780901c02c040a20003c5140c074030308061554440342c2c000c0c00030b0f01c4594042500652a003a9408079101e203400440d80700c110b803800703090200040415021703054107450b00e91907400e104080940c40d14062130300200404508113100f007084010b041680b82c01c80c0c06 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 463020890 1250 463019640 463019651
    0x10c1205070606090218060315012d050d0501051c02100c05030f070506240603060105040905070c110105040b03040f020a03140a1a07170a060503031602030c09011a030406 75
    0x850748600c03d00c0d010b0144008090f0b0344495130702c180c0d03400c0f40c0b40d4503803e4406c000402c14000d100781002080e114201080c03c00c442808004a41500340f10312000348518a00c000000720301503035038424020400040c7e111020821640c80d0014003040c0801c2807001145040414001805450146031084040301c181c50810340d8054540c0d9100d048d504000d03070040c42400080742107410032905000e0380740c0c0000606c0c4540304140002480d203030005034001c221030007002c00101090362640728204036130140c001c00d4020b2005081c0180c0c01400e055208000b0b40c0c00b814031035a410529071054040f81d040782c0c81c140e001405d64455071101342c090003240070102e074070601c001e8000000844001d40d69004512100c058048009039050044601412800c02c43c510b000a01c20003821313a030400002200d04000c5054400320360b6502654000070200d035001076900d07100100c0c7c4240d03d4007904031072070320301c0d0320a50035100320301e4125050044510080c016844a2500203001380310500310f8201031503029000c2d00000c9031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 463022140 1250 463020890 463020893
    0x1e0b03041704090c020105010f17030304110d0c24080709060e0301060f0305031b070e07110c0909030d20030c0d09021302071208010303020d050c0c0603090a150902010c120507 77
    0x102d9940c10b83c04005031f51141d004101d0020341c0400c0200401001d00d22a4542200600454603407000400c0100181e50250f921001c035124081c50700354042e131003162640c6040d01e80e201c9480002d49002410040c1c40b040d405da01103d8450300c1c41c18001c1e80c0503240d007071004d414140250f54803031502071040c0c1c15642c0d0307501c000307001c00c030b800e040a0045002e070015564403024880c0146501600000ca4403895000c00c40400c61200d0103002c00394400d8452410940704013100c50800d0500b101034070466400950761052001c0301c50040000c2644c181481c10801c90410300c560321038140000c84c10a0b041001042c40064140816640103000c0d0380e03084174002526060a0340025024418012401140d0342c0c04030b000c500f04051140d1940343c40005060088440d80f441d5030007580c4641000000040000c04240100140402c00c12032280942c004e000c00e4991074071620445d035590a504064a029002440710f204800142c4500c60050790185d6030f100d030310103841d229007446a1807140d6040800104122020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 463023390 1250 463022140 463022159
    0x20a050d0e030f030a050901050a030f0911010e010c121b05030f0403110420160222180c050105031012030e011103042117131e0b03041704 61
    0x111030142515419040008601414500340c40807060301c603107600c2049448030aa4002c01540c154620920b070040d682c03904082e04078081d003040443c6410f032500740050b901c104500b0b80b00c5806101c40030307642c4251400030b1000458030f0805000000c0d1200c040030920311041403144481c103140f0300b14035640210000703450350740611710391140d5a00030100002041c20700230400344000d403101c1e091007110280700d2601c540900384455216420307001c190200000e000000f00070218196543c1c0c47d0000d050f604514881000003005880340203003120300514210737064099942c0d54002c2e2030b201d42c01c120a46081820030b001940c0c0e60344094901d00480c00d0790500028160000603180d29030a200fa41e800c2c0320201d8001c005030000740602c001c0c7c641030b0814881030040d81c0c101080f0329140c101943d42003c2e0341141d410400704188940910720304083c4000350b0b1003118200e001000007110191104400c40392070102080184003424001c1e11100c107410000705000c51700e051448449490007541c07061506540d090a02d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 463024640 1250 463023390 463023403
    0x20c010219080f0703020c060a0c11030d0605040617060408090f04110a18060c0f1110110708031606020903120a090602060f0601020307030f0207030f0b091b030309010c03020a05 78
    0x180001d402c440070884003494020140780c21801a08055003041904043d540d22490001c00a00b0f101c0e640303500d0140010310480140c00c21014640c1520354910544110102400d11030040d130380124107044002400c41700c0c1e6013486000b03004039000b506060300c40e541c0d0095035034002d6590680c4141d80d0300000c10380c0e56980c464400c1c19441c0d00341c45943c681508c0e5024081404c0c8800c0b500d0f103411800402c00001e074101019441c0643c1c0710991300341c01d400c0780c41c06500d4000b00d15100c5420540841c2944881c070340085603100c0401282003101c6455a441c0c15560740da02c14180b81007022160007180c0c000040309a0041c00340700c2401800d40d4440158030403400f425400403402c072000181d001d5800c0011580500460713401c894040c41c0b000c3d0a107003000004c0d42d04c2c1301c3d180e0014204800f088100f03205038401d2084002450307210000303152140c040e007003951400070181e60a44c0329003c0c2c01c3c2c175254260b0300808101140080a0040c600b002e800e20010b441c00c0e04014000d03029402540c040c040003500a0081 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 463025890 1250 463024640 463024687
    0x6100503060d0c150e1e0a050112020403060e01050910060518060f04050a0b18060906010f021002040603020a1205100e090a140f060c03070203030f130f050106050f0406030b0a020c0102 81
    0x444045004400c06c0040b070808807130031a02e201c071032110300102c2c1d44c0301d02c504682503d0007800c1100580300c045c103040c0021300c2654406065249084981040707100107401141c06031700301408641d0400100c4d01c0440403038000f84201c83d4050540c1291401d00c2082d00c0d00305500840c010003251a5108401c04a02611070451341d00307442c40d580f50800450f0b46820a8600900c0740700704440001c910345200840c03600c03480a000b40b814402d840c20701d048001d2081081030b00c2108068000d640b03450351420040e0194000c4800c013000310710307010100e441e084c846100b075a03c40c0d81c1034200b1407245440d154401e0300c0140041e01e0a025030089482000120b8850070002d00104038040091080d415150341c0c05003017243c05024002d884030100700f0b01114039400015290020369011447c0c0d42030711100c1d8448826203070f48500400007000000f80f103003407020650090046403c01e46006040c00e0903002040100c070200c1c00b008101d0349528000c0b501c456416801390140d42c50000c0014a0b000e5103003101d15840081545 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 463027140 1250 463025890 463025897
    0x11202040e0307031733031c050405041b0c0f02040e01090813060e01020d050a020114040b0414030a0c081e041707050603190e1005010f06030506100503060d0c15 71
    0x154034155041800e4146d91110f0054144c204a0f20000d5009000d02c0009034503a80201815144819a079028840004021002c2101011100e80000080d24a81143c0704443c4030710701d4001740c04c001890380c00c42e00941c251155a0305203402116500e40c3ea0700e1400080c143c1c0c20a968003010170062500344a044d415501801416440d00c01e040c2c140350a034551900300a04005042d56148241d9030002038a840700e880b1401d10b43d032585c0c10144200c0c010000c1d40302d20140883c004080c0018880c04100784ca00890054058101d0417800044460b41c0c0d00c1381c40269000543d203400510045401d8602503e40e080708200d60002e43c1c1a8045010302c2c3e5006500000306400400400e04c0d04594100030050007020b068481604501d0100340400400409880c01c5c8000764803481042c00108050122020031680d0318003c1225503110805020701d03620f14040c880201c2d2400001c141c0ca0328048020301c110716000c1d0f44451456494405000b07420741100000c95503281c00b140c020582007292180031040c000660b9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 463028390 1250 463027140 463027157
    0x306021605010b040902010818010f06030803090c091b0c102c06060109090c020a0515160e0a06030b030a050d0305070306060e0906091512070f0605040608011202040e030703 76
    0x42280c00c50380c051040f44e03c964500041800140d0b0072454459200348001740c807440d10000015540c0c050003051403061042e80c501480401000300003000356000307240c400c0c12640b00c130080c1c40a21100c6001a00d041d000300d01105a02e4400f8a44a070041c82900b103000203881d2034060100980d41500c2803219944010182ca920045c3e03000e400c02a01e00c59054010010519814203000180c00180103010700650b40351114908000d503030007009100c8105034850111500c1c1d51040c0210210a102a81d099402c4920030000910311803050800499001c001800344910383e00c0d000c025401485281c20254260040c150000e020502c2401000d000c0000c83e103001ca05da161055005045601540040c01802003004c00401180c5840f50300d95481481920000120340310400d00030100d09c1c00d0344080d0350001c210fa80e8009200c0001c12903404a81c2c00c0841840c40b25202d04040d1000e02483c0101800200d03403c0041000b90202e407141c8000e01d0014100085260800800303900b1948041c0058010a0740c0d072 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 463029640 1250 463028390 463028393
    0x5030403060c022e020405090f0412050f12130f06020712080108032b02040b0903011103060105030a0b010e0a06020d09060f050919051f08070207030f02060a0903060216 74
    0x9020740207440442c1d1000e0458420000f0b541c000c12449241c0440040700c1c07040380004640740c0c50341280c018003c014002500c928080080050b99041140c0c120380c030b40038116011600b113008405440206130504082400c14510030320500e070406001b02564070b84c1003003401d441f0201e1025014581c0d40d40c09140302507a5407002c2c0c141600303a10000c000b0076041100807001040001e00c040207580700d0a48581103100807440101e08062090b2910081c2000c56100250008164150700010412a10160000d00c50b82a0001c80000140022034110703010642c104001134a1400076480070314138a40504080d5620407140c001300d6050b030402d07045080540d02c4400076046007500400d251008143e80d00d00703d100314018031001000c60044000581c06409284a501500450304a050025080203840d6140c41703642d0085210b50026005215401b00f0800703000314400620226001c3c06498200b03540c02409241c55091040c11f50200740e110381044982c110202c001501c50000341f030fa003030800c800c012415045 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 463030890 1250 463029640 463029653
    0x30203130806190e011b0207080606090f0606030a09060c0f080f011503020c0708010c0e011b0f030e12070305060601090506250f0501060807180c020604060b060705010905030403 78
    0x1900000003690002c41040100c020031008000d100c0b82e09803004c5a0000d50034203040c00341501e841e04906540c013201d00c601059a00082e40d000300d501400c125511a02d45209000740f030780382521044200c100b500005081c5090290095800040e0400002032058803504c407542291404260040054000c00e103c05006074044541034121101904240b15545051a1120f026441159100a068010640420445c0e05000000041003400020301400c41140d1009103c0e0203d2078003140418003101da0301890754403046800844550080c011141c0c440161019119030707011413400399011451002a00f002e51041c000c60b0001d510400c0240b000381040701c000b42041c40180c100f02c0c0650001d102464a60408140700d08240510544000100c0315a0070320745403500804801408660800000061044001030041c00b01c9481400705d40104002da91860241c4800c2c11401c1d0043e40300d400483c3c0400c803264840440070400410b0f03a45000200e503512800c1d28542e42c0d082e01d103a0000b05080060100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 463032140 1250 463030890 463030927
    0x20304021002010c0804020907110303040b040c06090b0f1818040203011a01051803031b06010e060d0302030d0f23011d01050a1502010914010b04060509010f0303050d0f09030203 78
    0x4690001348840081c2c50401007000700c0c0200041e04c83c2002ea00464122405180810000300d82070050366070b0784c5464244a47c1c0104155400c03a0108080382000900a01c50401d100070b4030f031100d0b221890032509008403000c50300b2441c0c552010507440c0c00c844d4459501e04d208160513902d40030700e40c80360349800d0041608440c80c41c0d0302685143c1d0b6078400122241c1e0b1200c2150065418205d41000340c44403440031900c3c5000300b84903c0c40b801e580c10a50744c286640003994078100c81c6c40c44d581e50800c1d950002404195860300f07a000300580d00520456402d0507880d0051400f101421800003480a02c0e28400300042599412680000900100600082c0194420340b10340f2900f2000540d415450080451081c0500c3e208441280000201c6081c0d078920070b412038904280c01c190101c110710140300503e0700074860385c6003080c844d51820b100060b43e41400003d5a04840c02040c210050514545040e91250b01070403030066056614004003041da8110b10410800300d00a600854487c000c2d10101c003440c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 463033390 1250 463032140 463032169
    0x40804090f0f05090d0e1509040504050a0b060607080414031c03140604140105010f110106062a081c180807152f0912030d060e01150c030207031502030402 68
    0x1c01c014890441d41b81c200b00445c83c000815035000441c074544440d004020302861803140d9001d41040c00b48011300c80c0000392803005a00982c1511542d4840714100b11440c46208401810310fa0b05010800a840000c00c60040298002d03040c0e44492500d81c0044410f030f400e032400c407800329030703034860b01142da40d45041307d01d60005e000d6500f001004500c40300540b040340144200c90402020344803450150384503482031807140301f07502c1c002d100498071402c1c0646000140d40184400e40b00d010340340380317692440d408142001c9420500040c6000707005e00c2c01560740e509014040d041c458503660258030042114021640b07003402820302e40d03101c44061034801013907101e0a4413800201c0c145000004000152100020700182281c0b41c2c05507140500d540315000d005548600d98420038401c2411000c2e9404002801c001c203503110304002d084e444801c2d400260400f8003400490075903c140305850280154408544c041c003074012151aa981e075a00c00301241e01d800300c2c060302143c02105010440c20404003030000c51 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 463034640 1250 463033390 463033393
    0xc0f0309170a02031c050409110703080f2509030515060a0b130909020103380105070302071208120106032c0c01030b0f030304231f0503040804090f0f0509 68
    0x2040d554000941d61007005d814140001c814420004c506800303002190010088101e0502c20362030385c005580c006421445080e40821511300015660340b0b40003448510800000807003040e420350703c03a01c0c4029030a50002d02814040b41e2600400030500030444501220084501e10f450b0f0700d04182404a41d4111768407a502c0d0010601c140d4502c404030390907034010380300c1d50000041c10030b10030300040b0040e0154900d2152079440040d800c07140e00340b6804040174003001c210703468580c40c07800706d004490703c2c41503510185c01a002101c052005843e2603490207581800340b41082c1c2481801d074568554054283d002e040413079074400000c00c6010180e0f1070109036003100860301d041c0c0000342150540300c04501c41410704060703880503007105942d0f81e115040380c0350f0704c0542140e44454850111240500d4100c0403660004660300b905980b62800e0150300c0982c080c080c03400c035003036a011801501c9075000980221400300090002045039001ca201341c02c4035007800e0b030000c9030004c0c400034080c084036009803081c00107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 463035890 1250 463034640 463034653
    0xb030105030a031b060e0a030f05031e19020307020d0f18050d03170702100e1b1011060f06011701080622060606050309100204080604020409030c0f030917 68
    0x140d40108101d0b003200e4040c1059407094110706055865070300c40c003400503c0189884840c0100039000a40f00c178201b8829141e540ca0442c070100240c80900089903410f101c1c14650080650300c00c07004102a0300003141703044528a6584c1405c5c480c01741e070002c8500f107006910050304010000e07802030140d610030901c0d041805440f008180b60302c0701c0304a18050303e03015100341070402d0b04143c440d13018216400c02c4221858403600f84000d000b500c0d07001614820300e09a0401001201032500481c241a070503903401c1d170000d05544102e090020307100d041d803c070310113100b011090007000f40ca0074010700e417180d100301808414903d0141c0000d01021403582c040741d0550040d074018030000740d001414681011410401c05081030301da44402a00c0d544c030b5400140710300e0824400044154002d805036000d014941d0544190385425a084c104034000d07031003803501d00e6200c4808030b80903003015402101c80e10b00a2610595003809501c87c1c120540c5001d1048000078020001006011141e00c4e00011340c0064078040c064 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 463037140 1250 463035890 463035899
    0x9050a03080f0c03060d1b0816210b060d05010c120f090302060105240d060f12080307080a23040506070309080706022a0a0c090603080711061e030a060b0301 69
    0xf03040c0001012240203803051071116060194504040d0300c41041b00c03c01c1020ba6440354600f40d00c848131300c5604003109040510100707440f180c0407600092701198042c01405201940c90382c5950321030141c0707103035001000c1000b042d000c41c1c42800740d500b00b83c110b0388801403800c0105020074219840320781510222031070401d090f00003da002c6043c80c11220101e440c8141061142d000d0134074820344058404900300d0010b01c41031550190b400840440381100682d84006030f81d000782200d003e458080c0104410004c00c0059142030003134200301d801c408031442c00111401400d2075101641d4040e010014400001c200300010044208007040d8045070794030f800d00507080f05507034042035405043c000a08a82d000704070f04200e0801c0d03030f61080031103240c078407000702042441068a403901c1d94000c00b660a41e4181d00d001c43c10010742c0c0502c00849a1004559281c55025150110b00801d180d01d403503030001c0100325894a841040300e520034100d03a6284070311b607641040560501100c7ca158400c40e6142c006000401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 463038390 1250 463037140 463037161
    0xf010b0f07030c02130906050117070e070c030306050a0902091f050d020304020d050a0b07030606080c030414010608030d0f050603010c02032a120c0c01081012060f09050a03080f 78
    0x700c0d915894141440719222510028000595004c10342c8091450b00800301c0610038140c02c858120345848400d03c484a1b8404500c0d6210307240c0d0f001d003a468240d002c1c080f801c002c1c0f2640c40c1200140c001e01d40003603000d40710310000354025190b510044086801040180091030560000100802c220318031070407120b40e02c07030046d04c5400381040201d249030740400024151341b554003003c00720315031041c2922905102490221151403003a01c8480010345400804611a8019100f15000e129856042030441d9900c2d43c95600204034840c140701d0765502c0b844001845201007001c1d041c007040d9200045220790b5005030b408101d8900a0545e4441d80c1444100304190f034021040342c260700c1c00c080310306509226810080034014080f211401d21403058224120800300a00f0141c0401d400d843c081c2d0b0020044c54004580044c01920003440240c50200c040142c81c9855031514202c0c4e1044101288500208464808450080c00700392140d4014407801000c01d940b004200340d0048901c59032120302d041020111 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 463039640 1250 463038390 463038397
    0x40b160f0f1407050706080906090d090b0309011e0c1112181804050c040f0504030e0603070207090203160e090411040b0d05010e010c110304080a1203020c030a05030f010b0f 76
    0x703090180b14a141d0380d920344030700121016a80c00108803080ba644d90310004101107402c6038035010f1402034101290080e41d0108080c01004255030f12046601d080c00702d41e1113181c0c00a00890700c10340d614010714000644071039a013070810808080000380000c01180107081401c103400000c00e580c0142c5002c0701c0700b00001c015141c00031207240580c0c2840725441c020503075110444a1102910b5190410007080100c0020f408800c080240c1c1d05109640d404280881541e8082d1001400728008400403826810036402855100c0344510407505913550314a80c20040f80c1c002d94402891010701001c40e00745c1a000031040203107a90607182481c10b4a0103484a2080c18000c2d07200d80c0c81103884100d20941740d51511103007281141c1120081006002c50924180200782d000e21981c0070a0301207203003028004011040d1011680354201504005a0310f139640310b84e080151031000c050590034421146960b1003040034000140e41a158196281440c40781c80182d514140d00078181110208101d800515186094 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 463040890 1250 463039640 463039667
    0xb03122106010c0506090106050a09020a0f0f0203130e04060606050f0313021311030a0c110c04150b120106021011040605030703062c09060405070e0915040b160f 71
    0x6100a072503030001201d4000d0000f8015040c0c0c850481480000b0340c0660003001116800c0300d4001c2d407659600380080a0380643c211100208180d940c005d81042d000d0805501c0c180e5192054a01d42202601ca190342551240c01c1008042110010082000318034800e15000d0003090070301c0c03800c01c0300e06e055103000b40c1300041407560070302034480d80101192928141014550101c0005220b000c50895149010f41c0040f80c2c2d04000303604005105d008030380030304c04075040a400c50000d41021300860090001501d050242c11550f07684000c00008e8000e104000f5044660010300c220b0b03841d5250000003407078441c01821108809150502a00080b61800122070403200541882a00e950b10f200056004080d00d50142420000703444a020001007044118003006080c00c40058441e2509a02d2960700c0e101124000e00640c880c1d4014451221007001c070ba81e00280513001c60b61205400e10660782011829a011900d2211450a00081d2201c03a240010601840d2604018503c0d24030380003805009150030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 463042140 1250 463040890 463040947
    0x9090105161101020408060c19031109042007061506020613020405092d010f0b211e0d0e06030423010f151d010308040b18090405010b0312 61
    0x41815114400f034040c0c2d001080380606031f800740d18098159090340d5015402103611058410018518180203100d0349103c0501d81d030803981060040350031b010003030010f9030041e02101e140d41d281c9010204080000c2100c0d61150301c021800c001c08030030300f0781c4124154000c6000d54101e1410812800102d5030110303600350301180c0114094031a5a0020708009083c484900800418901d01b0350b201880e289007031030460100d00800003148401294070480e0380311606a54099540c90448441c40810790240030b2410100382aa005000c440200b00d4003a22a00700f2144c1030340101d1400402c003074102c80240804c0400790341c0d044c95807819a85104000302100d580d4001106010f000d100018000d44c8002c80100c0c802000300b000f00a0b81c416104505507d02c2801b48401d5003101c1005201c1c09000468104e95000510754209814419a80a1703500a04c245044031140d91404ea00715907a41d02000d8050380c0281e00000f41c2c011110285810003c2d9401c003980c0f4000e0070880e07081d00803045c1f0303034071210b0044100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 463043390 1250 463042140 463042157
    0x306020406080f09030a181e08070b090a12061b080a0c03020307080412030e0d0809060a0207030c0609060209040219030e1b041104030209040305040906050a150e01111b0909010516 79
    0x6111155502094000f04030b035074014019281006003020703080702a1000039042b00c0c2d01c1a641d03040204c051190344030543d00200646000c000040388a42035241261084001083c000400c603040503100049404120000750140244007203000b50344640f4240c000c162409520394900301c44090080a4007402c02083e0540a030381e820709441c440c1c4c3c40390307003070020076001e6450f800344103000104526001c1d04c0000c0c1e580a940c0110b0303920340305842201c3c0b42c142c0c1501d0710400a002d94550b400141112041a12003075020002d041c040c2e80c503880140b601498400100725401c03081c0e10010704495034101c00c81200e901290f0782c1c150340681c003240030303d00074000c07180425103094100d49140c05001c0c0358802900501c6000501c800c264101c0081c000703032110040f04218051360f40f820016400700718414190304c0304480d546c4460341441000804280e2406040041c128847ea50600c1e2401d00302000420100c801800740090034a0000c01c8a50848071400c024403a504203a521089030b0300c101600326007808000c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 463044640 1250 463043390 463043417
    0x3010302062205060d02070516031a0411040606050a120603150c0302040306020f0301030203061608160e0d06050109111c0506210604021011070b0a05070c0306020406080f09030a 78
    0x10140c01a0030040c4c88261202e800502440203034000340e4040b10b5034042c00704001d240342d51101206040341d4000d01d901054103003088640c449090068401c1d00d1050f2a010b03180e2007034580c0d0003200010700d01036458170f0b5100000c60004060812048a0f0b1200030305110080001c03d116500421609425000c0040d02044407a0190028496944014040c600100f480301c14413281501450417030340241d042d01e1865403040c4001c075603c000c141117207001c184040d003c03c840c2141e5121120308090366082900340c1d1411000080c0035402c24000c11034540b500c420040c00400441e01841c1c04807201910194203241141c00384203c603070011031400d01150342d9540050301c16a240e20700740c2004194880314244698480d50010748402c02100c080c1d000380090012080e80520848102d440024428098100c8505080d159000e40d4002030166003003040a10200d0701244a07c10000d0046106880069849150480c0a40b0030350000303240903202481c501c00c000780604040300301e80c13402d040f40c0f800c4400000c1c103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 463045890 1250 463044640 463044697
    0x90606010c15290406080d020d031508030c01050a0e03040501050414010203090d0f030906170604091103030c03180f10030207020402070f050c0f09070f0e060c030f130b0301030206 79
    0x4a0441e125412541d440010100f060000c9003030614106403020300005444040c4555195244c00030540107030700440c684140315100364440030880174023151a8003107540d00c1992a00d1900038019081081e50b5507424400003110301e1040491040c150710103141024640b00019080e40a14440c0031300d13401400017681200e80c424000c0301d80d81c03440101071040541581c01d0030607010925500c114003003426007202003405030203584400d0352490704c0244111140c1e20310040c80060701f038441d0b0403108440711001400b400e58007030028210101d5a10021900c40309074021881c105450707811254015019000c0400180e01e403541c0c2814505024140581d4800f13462011070002c0c840e00c5030281c0f07a442a6640c05c03081140110b90000007c20488090021082c5107003048a058401c0d074103840421581c004601000303001d032224010500c40145224208006005958291b41c01a809002000c10000302440c0740c640001d20140544440b40c1c0c40c0d41150f045a000c0750080c0b00c0c90607190301d1001d06120040c0041003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 463047140 1250 463045890 463045901
    0x2070509180a03110d090b031315180204180302150c09060d020a08070801052b05010f0506210303010b1c090303060513020c1903170403020a020108090606010c15 71
    0x840608894820b8243d0a00810030039408a601c865401816a20440745105054002c2944c911215180c07540c0c43c3c198480c0101040780f002201d440d1000d44079052041a01e100340f180d101c80d80964400015003034810441214600e007807810702014803580d9680030a0380003134401000104a18103204944410012841c1405440381450b801030300000da5a41307080b00341d000350800060030f4580b0705068807155000e13500800c090252079040f1500c0f00c0b03d40c44401e031031803000c1504040c400b0b00446e4118245c840c5401e5035034011955038040d8864007800b1940c1090880b4031210580d200110740800080e13004d80391a84010310503c0c1c03c0560202d14400d02402070106203040a00c0e2110401921001c0d02e40a00944014891548525407450050b04c262400d0f000b280c42c89081c410140540005800004000000d000010f03010410f0814800380b00d003406c80025402507009030014404481d280c400102082c8004084002940194040c0308035660441d40d444115640b05001c00d0300e00c030011161500908 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 463048390 1250 463047140 463047181
    0x100503240d05030d14010e04050d05030c0d060305061501020307030e0906060d0f05090f0d1e030b03030a09080c060a0804030c08211602030306060a08090102070f05160609050102070509 81
    0x100040b050241191a0301045c0d120b00842d00a00ca41da80c3c403410940d401400b1900603020790080d566180764039210b440219070003140020080d0414683c07001304011142c0030b070000c072001d03803003407040c884059880c0f02303d10519203003480290300d84032082e580100003140181d580c074010f90880300803583d5a600e400c00d0b5201d0300300d145000c12480c1203040380c00010784000e8550750800c0c0034807103c012543ca000b03d80c0d070900c038801d629804d00070000b810b0b404103110103414050040546c3c1c0d444404699030148010003140a203aa641084241443d4595041501031084640308080400c51100c0803500064250f500c150181004c0e604902d15017400700385071184c1591200c04010240d404c94100c0701081c3d00c24011041180140d212580c102d01c242d03680d06c001e440fa40d80c80302d0305100300101188600c00322503102000000150404c00e0607503802501c4030856000321986d0308a107000c1380381030000042d828000d141c240740400c104ca18180002c2d445107018014207010b0b80c03120f0300003003902c42d00700c40c0c00760641d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 463049640 1250 463048390 463048393
    0xf0b0a300b04021002030f0a050c0f07030b10060804120c02120712050609011109090424090303150315181b0f14060a030c030920100503240d05 63
    0x100d285461200704a003140c00324407680003403500d0601c01d44000140d8407003240d046a22441e01c00481010354446c1c00080c4c03000d100b0700c25501c0140d0030344000d10044008612851000c0780754200042c420010390001c0d0420310401410904000100b0200c0c030082c001380c02c00c0c1c14070520b440b00078004207000c0c69413610091240d118601c0001401d42c041400d940320780d801380e02035552a0321a01102404d071000540498540501400307801824a40185602d41051180142c4490b4042c0d4030808010007051800b440c0401b9900c141c01c105040d007500840c03007041790075403001824904607695090005034140c0b00c0c002095480040240c10120145030140454120701441c00e11130030742c103208007404110301a101081082c62300001e5011280308450013803200c0289000e0616001d0f0804038001c100e410552000c00d070f20390000001041140c2194907241d040341c0c12001d8109614000c0c4030b100d5604450810400008004001c07a100c216060840800707010810303c04620020000030719921115000a8001d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 463050890 1250 463049640 463049729
    0x30b0a05060f04230f16021203061909140601110d12050601050d09150c050301081504020a030615051c0b011e1a090102011b1b060e07060c060f0b0a 65
    0x7001d940769181c3d441106406c0030380038800041041203841c0c0440444c0781c00c046100740040341681c507061070400041c01c00510305200c074558580c0c2210a030ba03032500812020386030f26010701c00c0550b401103866492540b40000ac0c41c16003901000101038030040c1d014004c003d6580d40c04144640e00c640100c4614a5041d10107004103803a07800c158101c0040200031010b03481c54220b90041090141003581d0481c4c00b0340703000d898070480602004002075802441283c0c8203005000120020303001e80300e0507100e0071101c054000d203d400c00d070502540707101284a840300007000e20201000101640000c6056a2541402000301008122052241ea440303030818144180c007600540c924600301340150000300b100740c3c020701900c50041c0f1201c3c07134081c0034000100002c4001c2219043d04054082503d1124450308001800307200c180c2e121410860329070040c02c00603044d0700c19001440b2a5011f000d25500310140100702007500c0e5400121300380010300c01c0494084080f03480c0c00000004891245c030426485480e85c12 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 463052140 1250 463050890 463050901
    0xb1b030f0a0908010606080c030c0307051c090b0708090705041104080f0a03031109150306030a0506070f03050906060a030f060b0402070b1905070f0309020a0519030b0a05060f0423 79
    0x4020054003410f6440c0d86045000206e0520a0540c00c0c0103882d490755403461500c410003c042d0540c401803010301848402c01c40c50140d80419132415260078446107000072051294035103c40e503c0400b51aa00401000009000c030901c0301203034940840340112000035202c0c4100424041d02d0080c0d41c0114006d0203103541900c0d0100d00895122256440380d41e080008101d036401416260085a2005e84c00003071203409410344070132001c02190801002000c0361b51240c4580e0b1020316107481102c0c150300080c2e40c044001d8085805024082c0c0081042c0041c02039490120003045821a0314803018040d06008808a02809065070105840c01c00c007400c1950346000a041105070080c2c10344032406c2c0c10f20a0749200c030201d03040784151800740c1d4403980c941380c0390407081c2e000b04c0180205031410303a40008ad900000a180d075590120810310400000031400503031640c189070340201401850422070600b00700401040d0703601c0300561990544105c0e400076000105035160031020079045410500495031806122 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 463053390 1250 463052140 463052147
    0x609041a2806052d1b0f0d02071505030417030123030a0b040632070f020a030c02090403050415020109061a0d06050606091c020405100b1b030f0a 64
    0x82a09905101d00e40480d540352003c544a1042d050010318072400180c0c13100410551501014481400850442c100800e6155101d092032031200440c001c1e5100389003a441c0c4920901a5200800940c00a006000d04d845908c0c1c4103140c0c0d001f203080402400000040400c10404180c450b2402580e82d03d43e00c940c3c58100c0203905001036040b4042030306681d0a0004540390000760004565841102029503032140c0c0d8030074010b405004803c1c500c0d82a4070080080c054400e103000c4606103415064182141807141000c0d04450410400c07170115044440080042904010040d8200354103032410805580c0e1030808950f140140c1d00301018010584001d40c0304598150805c2c40741c140604020428815407400c03005820f00c0c0188070355003000b4201001d001240c41c1f640207907402a009400d036403410000c440000c00708080e221540c54180030380c5c001074040d41090301c10560b11800d6400380c1c0340c11504103846007569001e44410203c00d010b0040c05a00011405d009484140d031000800ca92110303402c03034014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 463054640 1250 463053390 463053439
    0x30224012103120504060b150304060b0a0303080708060a0306091a1501020709021b120304111503060d03171602060a0204030c150e1507030305060f0609041a 69
    0x700c042101c103214095903140c0190180101c00d60607140e82c805182094207a034083d080062041d0341142d6544003800c42615118070100000010460103543d03423429161140489420468042c0541d551810920006c1c0e04601d81320f0304140d070750800e4210b42c0e84a000140c41400141c0004060b41c0c10907c089003081011500d001840c844515009200d560f060601c10321111400d800a00503440080204044801c0e50b00070300c10040100360f40e00b036901c04020440d240850320011036580080010401041c4992030390b4401e4540740403124800301d811090781c05c0b022400090007442c0720f0016100d07001c080501800d207402654510090421a6260001c150b0070b444109110f41c00150107200000b40317461840f803007110143c0382c0c00500c01d40003509250090440a041c10015424426410304c003040503504c454100071001c511030300150780e51180740b034010705541000d043e00707000d241800240d1a540d43c1d4542610a080b0040c0c1f80092200e030100b0324202030600b414069500145000205131050000000d074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 463055890 1250 463054640 463054649
    0x10c080d090f021f27080304171c02030703260403030c02010b0922230a020f091902210c07020a1d0103061119020703030e12030301090903022401 64
    0x150004d144004003810f0f08500728801c0000900c1070600341c00050701e60b0303820070540c01c0203c1848201c551035680003880c541c02900200402596811403070b5080e2000c00c6640004101058180451061140041c0d81d81c007610500805100c1c0908102001c118100c142401c40c00041103c12100d090508014004042c40c42c100c0c0d0055080003c620030b82e0034642c03882c5000b400140900c00500701112801a03041d052194111201101e90142101802d114442d0303180c2034403414003614141d141d42c4100510403021211141c0544000d0040014400c03c0c0c9294203403065040d031002d82d1781c00600009001d106c1142505007440d400c504d06010b104614a000703450318510940c1c49906254550004d030300380d1a2420241c1d07050445d0880148001002c0c0d80005080010303902c0045d042041d4031214031a109242084080140e1146401f08241b59000402e401c0031030742a10305031115085044000c1d100d100501840000540741c184a10805200f0407550040c17a00d0340d07040c44038100c01203012a450050a104 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 463057140 1250 463055890 463055899
    0x3072103090623060d08040902030408120103050d03060e1620030a1809050c0a1206052d0a151407060e070807090c0c032102030c09150c0606010c080d090f02 69
    0x80ca1310308140c080424003d03045242a41401e00e800d01c03401c0a0360004008950460041c0550440309100030301d81406140306401410414484180042c100e0b10603510200f001c800e2041441540070760207140081a032035914000311401601d003503948030841000d105a00328440000c060300722543c000c2d03c1d0740d1483d0300384040b161030b40c0d6180034a0702920001e40e004514580204220044540580c0c0d000301d8040c0100300110720650340d100050410307102041200000c3c840d1703403101144c20041410100d001a8100c41c0211000c0c240180d541d0030310b0319900a1428004058018140e100c1c000003a5894103601a400703100102001d400740d0f45442d900d1080711501e01c01d01d9400f081c070403e503000c0e01071250b40d15615030407040401e80307044996030102e030402c2154500440e00381c888900e1f6030000b180b103130200040301540c0300031100900c05078104009112025403020f001d0b0440580e0089078854021800f480c003021310748100d04100b1110304c0341c40b910384030042c903094981040050740e80c058900e9a00844 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 463058390 1250 463057140 463057211
    0x139020117090d0503041a0103080a020c0301050f07030e12130302120d21020c0a03051308070503070603020a0219110a1409010611011e0b030d02030721030906 70
    0xa07480c01c1050082d035102c0c001e070700034583c280b02d071602c100007071a403050248a11003c090031300120455104400e03001030b07030382c00c500040051840d501003292040320241134000704001d24011282d000b803410041c01110806480b0280741d2035080c2d00300068446101c00c0d0345900d0307490400d60359030725102c550b51000702c0c05503a03c04d48081e220800420010a03120480d1140c00d1a0307101c05400310011003005803134285003036080c0100b020b201010403451030700764071a4070f900e1703a01d4640140600c0400440d0b4000d408543c00340005002503100802d411044035898103005d6207950307109a0070b90504c84606000e01022401c90080b20a20041e0f58940040c1d02040d01c101c020a511104402110203a45080a8000000b5801005203034802d4000d44600c41c5084000100a480e0b03020100b100c0b81d42c088204910790701c0f4120311625183c00c1c804060582042e000441c0303000c3c440d43c1e034050070a040c2c0c400d000c2e89110140740d90720308038025040b03c990140e205400300191802c042203110306181e006c1c100ba00c10b01660 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 463059640 1250 463058390 463058417
    0x4031e0b0c030c2203080304060f05090304050618010c02031005162d0e0d08030609010501030209030d0f2f06090c010903170c0f0312060910030201390201 68
    0xa0304980c080d5604a00140c5040b0141300354545030b010f029084c81d1408a40740340000400c50740b1001d03501882c03044001103a0018032036043d2040d5040501074a0706a0401c01040107555503400840f644120029100064050f24600503680010304e8903001c2c0d014000d07180a0040304403107611891041002c900303107443c0f05409000444100c820807114022100c0c0c43c0c250703500040310283d4005601100c3e858010388585a0ba4081500004c41103011504500d02109019061400c000a036000d4030303007032808504003a070303002c00a07030b4601c0341d4903002c1c00b8000e0070007071080814811009500790f5031441d0b117440300b514648003c9144002c000010802c03d406680082107030b45038003142c03000311010140d4840b11002d041d91242d0040c6408541c18a0607a5001c220a05000100b401070007020302c03420001d1900c0b501c10444141d984200140070074410f40c0041c0400150b2100f5040701015aa0207181070001b031a1507802d14441080140444081940e03c501c1c04c018002201d032a45241620030398a1000200c1074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 463060890 1250 463059640 463059661
    0xf0d020601050105090d1b0b09010305010801090f021005040812030a0b120303070f030e15070216030f0807030210091b0b0705060105060703021204080129030714040204031e0b 77
    0xc2c00b490340091400c0161a00a01d0320041d206041e034061380340360155209000d0004403100655120324078070310002c07c2d07500c1e80350b816100f1103005224040007800b0712886552000d801c0c888801c8024880c054825400700c01520920503100a010440110346410907103b001c8103031a00101d500c103242601b01070b140e8645003068076403000c4640500c0011804e42d111103030142d80d2402c0e0a170004041550300d202d07021000303804000c0c1624503100c855442c2020304009000a06004007003501c2c01c2c00d4030300c011003003000502c0e00680744003150b00301250f55155200361030b0490810340310184d00f450389030521b1401401e01160f0807000c1c14224200100440780c65035407104414502842e0806005034221030300410550070504010030b0500e119206a4000040015941005402980024920340c5d582e509050f10344440300301c40345d01850070280d0301c08505032080000380c3e501190700a0050f1003058071303c600219103070368042e10003444c1c2c4810b510f01087d9101400100f02d075029a4250b81403055034021134010a071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 463062140 1250 463060890 463060903
    0x41503091b0b07150c0f200a06061505180603060d0218070809010e03030f1003020909010b0411040e06040c200109021804121b330501050f01030504080702060c0f0d02 73
    0x5c803500c42141051080d1415104102045d4140c01010314001c91a07100f80000d000c4030152900c1920005141410700f0313220840c0c060070360b04480a02c181045031001c9007407041ca01c00c447d11021203c00303507640d46403404201901010b0300700a410440404c0084441d21781c1d0043d00e440789a17250ba40104540e501d09041d07003030764145401203416400800200f03100b410f0008d1019800040301c1030000c1d01d15541c0c0e022031440102145c6413205655a114849028605801819120580d81c00c9031824681080c00d6880580405010948506e607650b203401d00c11f80c000c0c004103041c4448840b01840400e41c4d902518045e02400204911994034902254015545540d200340681c0e00180107010b01d41c00b84100342c41c404207032a9600c50701042c5140c10b9000172003280e0340384040071506c18909042d60b0008a549003950f011064054400d0500c0014002520b95504100030000c00b460302003100d0b1158202054980300c0d801d00079410140c0050804d56441d000901c000f1100030140440d44460403d4100f280c5411 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 463063390 1250 463062140 463062161
    0x10c0203040f05040e030714240610050307030f11040806060a08070608070216150237021203070809120f1e010e062703041503091b0b0715 61
    0x2007001c400384400c2c10945d1022071000e50325821646400e10b603440c0c5441f000a01d0304450360a0340320b140c841521008041031005501e080a403922802e04182e00060700080c03d20b4000b00401001000046e14148203401c14600d1a10241c03040000300109000c01c1e205901900405c00d09101e0540840c1090a02111400845503100c01800d40681801c0007103c4100010323181d0300c110706c18000f0300c007034001c00c071000c21004000301c2031118801d00c1442d1000c2e04100980f822204007801e494083e1030360301e001c1000c00551a003a0040c100705050184001000400e0101d01c5005610004c980d2030b04002c0c0c4400186500700703048a07100095070710303a07100a580350001c00c5d5072019030b0070084a4031039140c089200203854101000011614140f40ca005074034012044442a00030590041c104403141540300e940d000c42c070042c03c041c528003418020812040c2d500c19400c070b41010b035102c10030400d01c02030908100c400b0400060301d1300459543c3c030721145142c0001e6000d0700c2401c48607003103003080795082c451401ca85 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 463064640 1250 463063390 463063409
    0x90d1e052a18090703080c010204061d0d031808120901020f0703170306011b0303050105100512191103090c0a090501051e0f1309060b0103090201080a020f0d0204080d02010c020304 79
    0x203009903030b00091810405800900c0b984642e0b280440090401c801500e5a40102c100050b01c3d1850710400400c103500061101d90444110007410810361103110800d000c4641505161001800706800030306929a81e13030100c015401000000655405000014450f05100345e003210040d02152281513164246844010640700c850080c040e12503c0381001f440d4001c40505101100030324014459410320616402100007075038910044c0282d160507010505038102503e0483d0034280602042d036601035015010202142c55641e12101301a0b1359001018403280b10800750b502d80c1085101c66664040301d000c0603118403c0e4040100e50500d0920600741242c2c40180703480018104114141c0588501c03100c400d4004458135180300703068450030240751070a48440380c005041c0ca41410464120751260070401d04060030190b12a0260381d001300041d07044545200b005943d540042140801361146204ca80d840303600210380010081c1d404104440c22090940082c40030703002c1e5100480c2c403031169010340c1720341 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 463065890 1250 463064640 463064659
    0x20c0d0308060d0204060303020a150203130201030f0e2506020307031e020a0501060b090909010b0603010303050c0106030605100305160506040b160506040f05070603050705090d1e052a 81
    0x440d2041802a4000b5006070000e03c8088890b00450300392a5150026405a031118895000300503c48450810140d0410300c00c509509000b0700050944081d104041d0415440317524440303c5550aa120040710b80f00d0720100d580c000e82c0c64000b24940491001c10303008840038000001040760000c000c41d103459134560340320281001c4003203041ca11420303404c149904600c1520144c10008000748246409000c886041607203e51241b01000003907100240031130b0290341802000c0045450b0202903e040d00d606040c00750f100c0800510301b600510716540054400c42c2494280602481c080c7c10340400d81c0d0007802511301c07049c8415689104140309200b4550480400c000030400e40c0480c10203020043c4d181c4034100d114030320a407503035450450305890a82d0002400300f00c0d5410880f042161000600041c00c061046281c14a00a4280e001d643e0a6a02451030190341c402040400940300c01c040c205030032f05800040e01414183e613a02c050801c0029070f0300c00078070104036100e41c1c0740c00e58950b4840108900354 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 463067140 1250 463065890 463065893
    0xc0604030311100f15090603110d02060c06070504030b07030b0a150309060f0605040b03070806040f0204060b0d050906073e1f06091a0d1104020a0c050d020c0d 70
    0x10702c60320410a1484600410310662802a0540180d180e004024a0003185602d00300c0400c5000030203980c04650341c64034040d01000001c0f09418a6182d140d402c940d04881140c0707500208005100c0c1c1581e1001d04d00411003002091038011002d0f00a59001d0130481d051545c80c407105070125001c840802d075000201171030800010f400c5001c81451280b10f80340201d115840b03a587c08040c3c4540f05150080030307440f000c00303109506243c49000406003049000309905c514103400e0310f44443c0050400782c641c00d80d0b0300d240c105540712504140010105101090782c0e41c078809404000801040d941541140103000c00300d0341c09840381a884189032481d42403807600301070b0501d41540386010915428051052140c5121504405100443c8030060004080c0b4019625171040012a42c607a0044502d9914110295042103038518a00d040d0502c140c403e40c0300c0d14000d0510309014a8000301c0c07690b006000180c3c103400a580244401c000c00d11450031a4210b40844030182e1302d40e409065040d400c00c1c81c9100e00380 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 463068390 1250 463067140 463067147
    0x50a0b07060e10021219051915050a0305100e07081207060609060e190501060903060c0c0605010603060302180603030901230a08091608030f090a090e1e0c06040303 72
    0xc801400400c111000c6643e50301c41041039030401d41990040d18482810006c81d0038070403008036050100620f0403c11807910004801400700c0320512404c5550b40c60030340d081c801c0540c260b0303803014100085c115000f161784d915016540b14114480010f1190400d1561100c1050009400c4103031024040500110b001c03224901c8150b81005406231105611407000140103500c03441410003500b01000c511041d440c0c587c0c0f02c206011f81c070150303c0c0740c414505801000300c0c83e40403a0300020749071300c40008217907244c02803411980692034640c043d241c14030b080e000007111a01580b208007102d200b640c14445024807044014052001285c0c255051b800030000401c140d1303c540c4402000503220b0510007440e8100c0421000305400000811001c2003640d0140031001d4000c00c420700305c10781c02c07400243e45d2030700b000c0350503840b030240c0e034014010308801044c07080a030b41c0c2d55001c102c0503107400802005650a0020166500e4000c282002c0d2841c1c0444810325010f00c010455650311840079000a10340b07491a07800b01c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 463069640 1250 463068390 463068401
    0x405060a030212091c0203070c17011401080d0e091302010503100b0c0d17070903080f0d050903181503150d0f0b06011d011e14040f0e01050a0b0706 65
    0x100308265007000220038006005034000d0040e07054034002c1a00c0c52060000c091091700b90400001035501c00d200002c000390b6072502c4003041d241d289a19000c0c910003901814050545415548181000c00c4004226031200248001e0f00c2c8000d075880806500d00032080c0003001c102610022980503d41e4800b4000d07500400c002c5810041e850009000703aa80c9031140c41064004103090140358104d88140034050768012106503442660944905841c140b107007000c6c210911610004040d105c012440d40c014110440c1511000644914244001d2410082854a0754403201c0c5005681d0201c9440300719608014288115880c41c200f141d628507280d4559200d040b201c140e00c1e0550081c29074849100007144540014000b910440c85215541400710000d0510003c000811081c42d040690401c82a0ba00820091042c20051828a0241c20072181150380108000c1c000d841c40da4006000a90804401c81550440b0b445900700340c0340b662260f0400403210304900c00c0d02c0d80c140c001d20a09000c1003556018 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 463070890 1250 463069640 463069657
    0xf01032a1107030c0306061a030a0f0b0a06020303190b0a03030e030a1e0506070e0d1407030803130b0f060105041814010f14090906010608100e0f09100c0203040506 72
    0x2040a08611015482c80c1c41116001150010881c0714104200300c0d0354051a4054081d00e10891828041d1003580e0b07815000040c207507521301d91600c403804101c0445610400300804080c00c10905507458540103556940241d89607110700b07201e4100000181c00034031030010810401004114220314644044a901c40c1900005030305015021141001a10110038060a100e02607074400b0604000d08110b418603000400c0103040c80f40ca21600040d030b50700e40b9405645981d005103810354400850491514150141c0c00007440c106002091160302e19142c004c246146226132003101050b80c411303190143e02e800c2a12843d010500a020504c5005204125070600c004c1910300050903030150402504448803c1e845021041b1200c0310500a40d026184201a100350607945c40e0980c4c14800b802a584110511a8030100213040d0081000014201c1e0f0740d1005112103110b282d09400c0c48800d0b40e44000c4282c48004803403150340e84400c19440e0500546003500701d160065420b0511b084140009680035542 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 463072140 1250 463070890 463070897
    0x1a10080f071e030c0e0306010b04060c080409050901090c124e021006030f0b040201020f06040308070e0f03100f06210314030c0306100e0303180f01032a 67
    0x6195840e8500c00c0c1120800030070a90f000f01d150140064054210300d070403041180070fa00610014800c1078903500841d006c550341e51811080e0441c2d241060b80083c060b41e002401042d0501040c0000e02c00150030000000707000700303000da2280342e6895582c0b0140780303014001016a5000c10f140003110301242d14000c5000410603c0c141050010030349180202010407001104040c070302e4003446445d40c1048800c05407001c8950030400349041d9100c41001c0b0300082c100900d000b17103010000d07085900c00e000d103608440401c000c03540d42e401d00380380142c0224000c58491000070100d1089a00d5803418002c80e06005001030041d08000220880c40380140a40034104001682c48034000503103c006012000b220030b08903070500c0b1032000646001016038041c081c40d010903043c2442405003140c40281141d0b081031040f103415941d01b0341c07000140c80020300340c3c0140303a040c00080f5200d140d0800c1101c120018103001c0300d40244140c03410300150100c07005001003880c01110f5206500c1d4403150304041030b103410f03000e05 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 463073390 1250 463072140 463072157
    0x705060904062103020706020106060905040c1b1109060a1203080411120318060901050414010e0402160b012120031c0e0102121204020d0b0a1a10080f07 67
    0x10303c0364900c11103102046010040302140c101c02c0c180d0600400d4082d007a1032009001d401d180034002041d8031001e019440c0706c1d507920810500e0090040004407060300e0540d04a24007004241044035100d9840e034078140c02030322000c00152052a00c0c212000c1580e1811070916201100364804071882c0c030700240704540c0c2608100904566039030700f142c3c071314084030303001c00a541e100b801c48403032140c1070350154903140120424000301005a80003070070384040d660140f40d0100200030340c1e001242c3c8103080e1003650760040d20010700f0142020700c008114143e0b90042d20b0450383e50740c1c1c9542000c940c016000e15170b952400078050000001c0c1420300c0c81c000d032424030a22100f0f00b0001800083c1080c00c014107a40303200d880050354940440c5c005094030a0700c502400940041d207186280d03045184a0000e0880840014100040440d51140101001280c010b1b112904900d00860598014141d00c04000c5003a51108844041860907010401c200541c46e55913210300c1e01c60103101c1441c01805443c190611100a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 463074640 1250 463073390 463073399
    0x902030106080f1c170a1104030f1a04031e050405031603050615060406030f0e0a050c130504020d240c1707173c0a05090f070506090406 60
    0x2401036601a11200b005050f00e501040c252a24007031194129248180b0342101c582c01c0541c1100c0756070000541100d0700c40203640d480031032000502030100700c0204a0030115001c000d1008218880c508540b003500e071281c03250320b00f64142c904680200c50050000b02d9440c50b203611000c450300e903800700c0c449078100242803a403900d0020741031211048040c82c0307400702d8284c1001131000410103207810406c00311001201c88400380c0450500d115500584040c962605200744601c6aa580300c01e80c0c0d200804103403014040c444c0f03001130321100f40304a6284600c048504003400310f42e46e8401e2a01a135130040c610000d0f1121a6a0b0215031480003580c0e071041e65002031000c509000c41c0c0540084520701d662102141203c148130005461005010182040b48144001d62510742c4418040c0c0c020300c002e80c02030717228002c41c01d248408104150b400b80f11003800301c604151a40c080480036000304903040c02884583c2d10482002d54030700e10200d52594940c0700c107008200b0b909100008149101003e0000300c1c1c00e9896 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 463075890 1250 463074640 463074643
    0xa0b030124110a121e03141f030b070302040b0c0604210f081902040308030a0f0c020a24020304030807020606010318080906070c0605180105092101090203 68
    0xda00a01d0082640040e00703000190035012152000c14500b41202a401c1e040c14056841c880c1c000300404003250007140110041c0602d815208201081d0b80d4040b40350400c243c020b0107402c80440035055070041c44081102d441c455041350150564041c5140c1c9010324640f00c050b045480582180145913003048042400d0032020010041100064010045d80c10146440800c1c99150a070410b1400045130143d0326650b803100707050009a100c0d103810351080c2c4440c4405d005140c00800c0c003804052002030700004000c0d00300c01840c400c9000300020425841440019401d0300c0c40386041d00c005801c9035112400142d80300e0700d1412121940d00800300440410340c1c111040340d2040c2c070305030301080c081350410090660400c00181e20020a207014002e18a00c140c410401e4071004400401c010300102d500d2505458210a5542c07054101e4245000f45079160b00c0580607902c042c82c1c510303c59240840700c04940d4028800c4501181d070186c1080103a0480300c0c2074009018003170244401c107540780c10710600035980 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 463077140 1250 463075890 463075897
    0xf030103030903030206090a08030a0930020c03030c030703120216060218010e031f020c0303010303030905070905010b09060c0307120305060406050406080a0201080402130c0903022d010e0a0b 84
    0xc41e031a0b00d040d490940c1000386c80c0c83d500401910056018488a5000405000940341c000c000582c01090b440d045241207e0013020003950445100303603904e8443c4810090107a6041c3c40032041c2c003503500f03a0003000145a1203200c1d0f0303404480c0941c400c0006000003813140441200e903010383c1e0001402c0840aa140b80c0e0207103034441064805a40115422007030411010b00e00e0854802402d0204150180a01080d01c8080000c60024190344800380310352820001c0e01114840004042586d6596860b80340250041403108415200c41c82924404102e01d50140b1030309050301c01c0381211900300f81d50b0204100e0558048280c6c40ca16002c180302c10300010702d484500c803030b6040c85502c1c04201480c0240a2200321443c0e50300061266080070410804008003084039020301c1e40a1034a8100755440f0b002244010300c842641c105442d01e00b4514a00c10350780120a00192482120301e185546046504030039140b0801c505a85000080204201158050510f00032080d00292070802055510212121680c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 463078390 1250 463077140 463077143
    0x609040321060f0b21090c04021902070e0c031b04090e070509060301090807080f0910030c021902012f15060a09020f0a0503060a030b010602010209092802030c0f030103 74
    0x5403550b00070b1124000100000c000740984c2d02855040c0600404090800d03000135041c002244107500c0420340900c0c0c24030190b01d1211024006643d1501c009540821740c08140c0c02400050007464004280c400400140c140a02c00084a85045480c1c0b0107840c0045c801045904403032040030800010510918002c18051008110241c5522460903060003242040240503a1007a4505119007000822a0041e105042c1e0004a40ea85034804811021068417841d0783c519803007140803a01409040d459041402020800c0e400d854406045402400b100d011841d802030115803903c443c082c5900403000680c40c0405060205000d0b110403034056424500464181078069940100300f00c2c0381c0c00c2c41808640240114101185410400c0700c00c408030b80604210b038000c001e00007010278460b0340c4400d03220f40035541084c500030265a54400280c004d502515415009900703000008041c010640409810700144040f50401c030403400c82c8403802540004e0100c00000001e0024034041d50300c4a02131806503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 463079640 1250 463078390 463078457
    0x2102071d0a0507050c030f0d06050616050d0e0a090b04091401092603010e0a0902030d1710080712060f09030206010812090a120303180b061302030f06090403 69
    0xe0a21040075000d81e078000b0f10398024080108841c01c008000001107404c5055500d2103551280c002190150151100340d004c03e03800007000c1043e14a4aa80c41d00a4040c540324400301c41e550261748109441e144100d0f04e00d50b030301c0545184204031034841500b084844003c0240001650300c8980e5805402050096501c1802d039520303142001007102d6181c4880308034501c40c87d00e04061610f86002c01091105019055080071001c010402841882d001408190fa00a05603400d900040d1002041c900ca10545070701307200b403284040703100a000e08203000180c40c00540500ad40030b0410b041c00300c107408100c0048501c543e4450500c001844a03210b11031030030303100350b0103000d0a5141031319072803501c0d03080d07072040003091010131a200540e62084019011130f5024006c0140711449800c09030024014007d01c450800c1e0b2110440c810003288076441c030311400b021965400c01000740074502d4220b0004070b0f038152601e0024000b00c0c2a0b46080c200140c1d0103846450448000921101c409685101142c41c0701d411 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 463080890 1250 463079640 463079699
    0x30f07020415030c17060f0a1d030409150506130501080c04050307030f1703090d08040c081b190e0604050c130e07021c0519110318030f030304210207 66
    0x206015186170800341003200001e1440d403c1c400c50b0350300d80000162040031a16a521056140c42e9529003034101c450804038107480d01e660350380060350003800d0042c007030701c01001412a0100b0589000c2040c0c60000001d1007032155614104801550621000f41c04480800b81c1400006416601040984040d520840d41a18032071b0032407900c207903010908100806403100500401c0700040c00000c03c0c45495803645041981522a0b05111031030001a4014404500600d10401083e5407040354002940c0002d0310a2141207106007032015041c1018040e035000b200380040810140d2515401c455040b0003144141443c1150080000b0703004191540410400e0030900100091190107001c07244202c10701e20080b00c0c500d03030740d404002c0c120310a400451161135540b07458804071510820800c1001701840c0c00700e0750f640502c43c103508500d2039440d43d0548030b841b40511612070310750702005036402541d121000c540d82124041d0610007940039008030304214410040000b41c600c00c2c000484104800b9900c54550 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 463082140 1250 463080890 463080899
    0xf0106030521030613090201031401090915050c09061804090516080613030309030e1c0c0b19140c06010b070506060d0b19200c06130203030f07020415030c 68
    0x1540300c0d850740c500034180b810b02c200030031034445540d20844583c1074040000c00186c2880107030014481c20450b00c01c030b07804140011402c208544d101c048528007511500c5580c3e2020000380d016502c00b103911035561402030000c016982004005080401d040b40f40c414001041d10300424210340214400761540d42c407144c86a070780240360803020340140c80c401010317104a02d410768140e80c2e41c03084000e0080030540c0e107584002c1031501c60038603008403180062042c030001240c6600d10042e01040c0800341d031000140f040000e8115410400c4404a910034203080e4a443c040c07210580c4e140405030103046140380c042014820001c001d0081d54041d040801d401038640c211810002e141c4400203110034094501c1640140104026241d003560084007007546001c60421414484090841e40808c520080c920300c81c240c00c0c1245000140c10300d1b103c000122001c0d40c0d25070142210711604540042e40540040007007041070003d003c0180039040c00900045605420040342428980841d4419240640700440500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 463083390 1250 463082140 463082173
    0x50a1208160207030308010308092d040c030b1521070503100618170f0102040b090117010f12030e060a020106050a151205060102070b0307092c0708090f01060305 71
    0x140c1c0d104544002c0c0141411981c001d0070810301030002610480010441c2c5d003503a40c0c2c1900301c1301c001d006607900c4402d2403509036090180a409029080c800d43c24540090000381c440e10914088910050070300008070412401c100d21503000f489041c1000094400c86182425100c04c0340c1d0054003559622039491805030080420a40707260030905c20004c46084030410301d02209500b109617444140c0562402c4540181280340c00303004c4124400d40e500100300000c8803018000a041400b07400c0e00c400f02a11800454048261003d008201e0328644200d020310041e10582e5010000f82e00c00e01303101c1300c1000103400140181d041400e005005070346550041c0301c142001610b450042089400c0102c2c42c001402e400703801600450301840e1050b6840300000c1060f032003040884c0051414884c5665681043c00c2c0040440310f82d4020050182aa1000c0c0d9900d5a00c1c050070704509a00c40c1081f0806840b14541101d44000c041c3ca810141d204030220280d40c20342c01e2140b00011031151006266000d61803040d01c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 463084640 1250 463083390 463083421
    0x711011b0b06010f020f0a350409020d02042727020609060f040e04050c030601120f06110a020102040e06060403031707050d0204030f3309050a1208 65
    0x500000c05865110400034410340d80385034000c4030900b420f400c800c030b45070300407031a001d4148207160750703403184110304003d000100c1c0d1071a0308601840c90340c005000c040204624000000300130111408400c01c0200158081c65025203041407040c10090300e0641e99110303880780d03e44064248405074561201040942c00c1510918244254000040e005600d01c07059001c0025003c9001901824000800c041c0540ea004100e07000075511a540703c2d142e5031140918142c44004540440340d9100c0e01e02480310321319002603118121b84401c000c0f0024056039a890884100c080304044540e1502c40030070440c8610b40302c0c05440c03603040341da0005888925002c1c1003d40c920700640464041c250411050021a43c0003400380c8026020020040c2140c8600720216024400c1004940801c0d1000c107021041041c0480244425400348034460f5448411206038a01540c4010783e055841521099040c9540e25075000b0a5045000d84151200c40a564503581c1e880c0992031010b0000610080802c42960102100d5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 463085890 1250 463084640 463084667
    0x503010f14180601050d02011103121f1202280b0903160503030405040507200d09060e010c0b0604090213020702011e0212090604030210031406040e100e030c03071101 73
    0x40a02c1c0010540c80303075480d2281030083e0780c06030140c4504007040da40521011007220140c0402c803969980c1200f25041403030420780783e9541d1010b103140d05840100d2500f1050055480782c44003c00c05502c20b508114580f201c04103402460200115030590507510285000010406e00f02c900b0341d1401000d00309420041d107590056031451042105002c1070300c0000641c0c064605c1960b001505031141c1c0c1050b20700c12180c1074813030303444194204510407a42010a80003140c9115845080109440c1c00c4c0654200d4011044e890019680b41c1080010a114402d425080300000c0d1000803031241540101d581c40403003000024589070001200421964890210100048454400c01c545c8100c00002900ca0f11040328021710704001050000c3c0503510780f02110000c5600505208d42121161000b41c0a032900b801801402c2c1400f100003421420310b0301484e40780da1750303002c0034154410041000000030490908101c0451000307010703001d4200400c0000b80748250040000d50111080031000401541c10081e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 463087140 1250 463085890 463085911
    0xa0f09050601240815010e030f0a05100e06070c1b0b0c06090a0f080c12070b07030501060e010c0201080c040f0e0108060112020901170f0321100f0303180503010f14 72
    0x104110841d44024143e0b0010000700b4042001000700d00100d48030f10547d104151b150140304048131980200203480510148038a003074503070341c0740c1c41c0000000b220100300751200c00d43c000400007032456104058035801148240010382d0010404401c3c0341c141c0000f500a010821070000e0041c4420714104001da51020500c001002102080e03070303800324046e0302060020407a0501080c0450030034014000b08059100c0e8400498903842c0a04140e481c4240540388800800d00d414008180a8411100d820305c0304d4040e120100c00c0c0c0416401150301c0c0c0d10003001c5d21036000d4180008038038581103a081c40000c1c03ca074000840da40d410000030b203084c108182d00550342c04d400d17030140300010307142c00485c5811200c06101000b00d10001c02682400c220340780086040b40d010006e44184034284941c3d8a004000f080c40d1070401c50b98402036054412030a034010100c80c1c40071035004000203882a203204001d4038808400b008030701d070b036180440d0030350395000700300507445441c1c0802c1070500d0741250415900507240c80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 463088390 1250 463087140 463087199
    0x24170a080c1b060f073e0f01020109050d120b0607060e06010602190f020301090b090601140105030405070b0f0f18040c0305061f020c09040b041a010303090605030a0f09050601 77
    0xb0b0419114401c00400402ea10740307500c140c20f0240020461804405112101082c6c9005401c0203107031442121425588900d2217514000c4071548148a84138035254440000c01440c100e00805a85580200c1c607001c0016031110340c13001c0345071075810103040018440c82d400300740120640721050820b40140c120a086500800e8490409400c074015408000d800c140c50000ca805540003081c00340100200140100c21100c0030320055000024100f4100d1b4400406c0145000021004481d40d100548001d09103901c130190500c280c1100b0301c01004802c2c4400b48403890040c003110080d02c143c00c0b114400c0000020341032128140d05180c02503201400031450304001a1500000180c25001d10211000c04542d444205a00d480d00030032940d85c803220001d00c07041007842d043c0341010b040c1004480c22584614186140c0350499200b01d41203050b680d1548a1502d001c0c04c10740d048800341c0000f01400d40c41c03a11081e50750200a6103115103401c040c0600007070300301c130b60410758418403004c407503d40a1003410038003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 463089640 1250 463088390 463088407
    0x50f0f0105010b190f0302160c051f05030609130b180d03111617070606032003060a09050a06050411040b060f0702010804060906050906010924170a080c1b06 69
    0x1e0f15441e00045071400c20a2541c151404200c00a0155240a2303900f2100303940081d040c44003603510003007105c5044804131103918841840b0302d11405040c0c038030808a081800402c003185816001c0315800071a003022030440000303035102d902d40b19106440405030030010300c003c003850903024050759084880605040c04032114440945099118682518030320401c520702e10020084038030144008224266480c030740782c03012802d0940040100d407000b2900c140d0685410016684034402501c0c040b4030082c081c00c2d541e80d130180032101800a20104031968041c48801500259183c85024090360145a030b02006218206c1840226240d00e189640701d4602800031a030394169010440394071075420728160215481da440c1c00380c01781900c2900141151300300010420b00200c005680f80c100c0d517001c1414882d10302549000c003002122003000300d01c0558400d000b441803441e1340141003403848504085a030001441e4858a050360001e40340341040380c110170180480b1011020b610203020324221681071170038060 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 463090890 1250 463089640 463089667
    0xe0403080103080307020f0304080c0307080703030c120e0301021206040c1e030b030a0f0f170f0414030a020406060206094b0604030201150806060a05040b0409050f0f0105010b 77
    0x502c40101180c40000014140358401d011416250150808803502e031364841c0c4403180c8441307000071058003034460a000060501000181c900481c1d425898110260303083d034440107846920042c040701448450050b01c0f040c0e403004d00c010462007550b1401b801c2d807400c10788108400d80303602d69060000c004020070540f009030b2800305010340c1c800280c280010006c001c6404a41801c0400710003802e910798405c2030348103001d1604080038880b4492506551213111011141029006008407107600c10824007060010540103007504108000c010100c68581489600040079500742d43c2002c1c005030805800d1180703000040141074090000750b00791512a21070007a0504520550300311409000d800d82a50704020360101c90040a80400701c0285c4005190504000e40a82800c0d4100101d03100700201c0080d9079803010500c0c9001d00001003511262924010800000d0021400180e903c40c4e40c9100c031320b0004108000d0910301418450190200003608202c29084a01c16806082024003c12941513a00c1c0d2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 463092140 1250 463090890 463090907
    0x5011d06060a031410090b090903070f08041e03060e011a040b0f1e0f01090605032e12110613030803040615060503041202030f090121020a080901060e0403 68
    0x1607411036155448600700714040c00c0c0a854180300c404d02c84c070900200302c5680040c84c095525101e014041074075110140919510200e40007406034000303000791030001d200054012020782c06112518100354035050103d0740c140e030100d5080c1a2110100081003000114004d6000b044050002003101200041240881214100070284510307620205020703955030302d0451000c0f8034005001030709024101485c006000e003242030305034821204071002000d198802d500183c1070b6000c03651640e00710380711104201058180c3c2d03a8a24407030402d08010004412107003081c44010809080e038110351035030608041750014456401c250141c101000744146485941401104407540000e80c25642e036a00d042c800000d1110441e88484c0c0204440006140c03070317014000e5801140242019403252074981b100340d075070340310700b00d40405616801d020022456005d08005c010407015105120200100c0410b0802281d001441c60401316521209000d04504244605009812020a0042c0074142500d025000c880c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 463093390 1250 463092140 463092151
    0xe030a08100513050c0c06070513050904030507080c0a020301020d0209130608070e0a090b0a1e060632122502060610030e0a0521090603060103020c07032405011d 71
    0x54442c0c0111308a45a054215140721031590150b0347c040c00d2049000340709900000c501425402d5a040101d450b00c2c1c41000c903800f481c0c0c913480f4985031503425078400d03505e07400c04034680010780510120800961028001030244000340280142d440e0448000c01031300703680000616026910340002488003040c00254881910f10b001d108c151140d513905c1c0b045016014035071000b8102c0400311700f44944410240c100180c1e800d11220f04201d40b4890281c52030895000d0701c640b030000f40c0c6c00d818140a09444401d070340500505148907152032408a001110981e1000580030704062100d01001201442400404210f24081d416a05500e0703030820b000b590740e030000d069036120300c0e4420070000c0c816009500900d901890041070703c032015441e0170550381311207195204404408040c1d2418a90b11290000c071000980c000784001c4c11030b251000110001e400c1401107e10922a803070001c00401d40d0b58000309050a913400822140700b024050807030545406038024480b512010642c0340882840104440c0d100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 463094640 1250 463093390 463093429
    0x911040e0402031f02030f090a150e0c0301060e01050a241809090302060601110a2a230126070804170715051003080307050a02100e030a081005 63
    0x740c89500020b800d000e140c5002040700b402c0c00304c1c070403001c2d075041e009076204115004612104e5910f08440c1c1d911201007a4001b800004130340002c1480401c203a00906030f070b030540b10444208a03c00000f01e4211029078108000d8403903654010045032610400400c068082e1141c061b6044010040c20683c00b441c420000b424400c0c082c88503840d200d40d924542004181110b8240001440c0e0700b000307912620b090340d095001074415111420038120004060720341a0303203d90000d40e100180d14081c030303208602c07400842d10907201e041e001880e180c059400222008400300103c14035285400003400d91b180c421040c02c0d600300b041d4150407845040070ba001c2da003e511428000100d5030746181803078210030514007004100c00007282d00401c0c44034042c03088580b04540c80c0304204944a04032051407801c0d06100040040b281080010016480383c40503003103c010500403138584050440001e801c0d50603081ca640819880800c0038101554401307410b41e00f103010349040e469078500b8080130a807050070640310100d14 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 463095890 1250 463094640 463094669
    0x110a0f050d09020604031505390f030708010e160503060108100504050a060303090806041115070b04080a17012102010207080d09031703071707180b0406020106091104 73
    0x1040d42e001030900319802010305070740b144c41b0f1400c015904040841071000e41c0c5401c0014224086003e440001aa14804c400100f03406481d2410483d460a07076200220796410b001c4c85407281c42c0c000140d8010920340d01c1d030441c81d6050000b503a603015402040c0001c0e0303c5a02c501030740c5494004040383c0e04190286440071081da00c3c42110310341480c8980c0b029401502d01001c010768400d5030341c0b100c1d09480c0f0039650810002c2c1c1e2009190380d244820340b4023804520f10460340403860f00c2c1c54030016015455a040c078038140081d58640e8a01391608490940d031a100006240002ca5480900076503412041c2001c240356505265075907410003004d0010b40111560f80603480103680c02000f00400411000d800c80c2c28607014050000d141031240e100031a090b038095049480c4036000c442c00d480c82082c1c03a59501095a03e0403941d040c054038064688000d02c94890a40705c2408543c00b285d001802091802aa481e0301e04034009084a0707a5601c19a4468a007a00b0586205d4402c012681200d001112100d48e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 463097140 1250 463095890 463095907
    0x624050702180705071505060a1d010e180307050304051f0e220e01060519120305210f07020c0a03051c2a1e080306100e040c080901110a0f05 62
    0x22117100c1d142029000c000d4011044100f18142e411440c81084195904203a566403903903013230503214061000d0310320550703e0340041c0030740b00305801003a0b07010b501a055540c1000c07450035148d0569001c803e09407000e41000a003071145052100d54550401551a44040c00c00c040c41070090207141010041c51092032000c42015441e0b206000310302c0d08041d02c203c10008401ca080303c0500030090382c4901780c0220000394106000041c40002007007101c03000b2171409000a4940d504580543c4001e41041107110040c4861740d20190041c8030341e204000c00c0c0c0d8032010031705041c0d0001c0e1503c440d01d040f0314411403403404c0c140001280860301420032880c1c0d1519222903861241b0130b0f5640f803440c1446a00c0c50644107080320103810819060b05045000e0620004003410049a010503900c08500103401e122040002c41d40c9424414001000c800032460100d40e03c3d0082c5001400707030f401580230840000c0d2820240100701b0402c1c840c401080300348106851509210030300c003500c1c580b1400a03400601402042000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 463098390 1250 463097140 463097147
    0x105060c0d03051f0f0e01060503011a0c1006060203030708090c030c0f04020c0f160b03070c1104060503031b070e0f04033603150c0207090b0303070606240507021807 73
    0x2444050302c10b01c1c44031000e1711815241c44860451042c1e1406c00a440700000380c042c00303081200d0596905400789410910104801c0509038458400345800d80718440c81d000c0c0502c1c05d8402d00c00541525805959642080b21005002c40e03005040d4403c2904109000140340e0b40020340501c140c1402e031900d44085c01c1900c009030080c055404d5810260107180c0178002603042c08110642111a801074140d03180d621800b144402d40412034070100400c8401c1c1070000032485c106029004850010004074040351550080ba04603005400190070b191101008080070400a010790070107403501e80b8140b44180307446075152002c00405000a4240062803070811918691041c042c0b900da5481016174a41324031011704402e01302103511003500d6802c10303041001440711907400b0700010b940c01e5030b000301000e03401d0601c04001002da00c003400354140f00c00c2200000280450142d00c00424404002d0405000752004141c42c1504081441e0304001042180340d00580d180181e103024012007105083c090b41e100502507 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 463099640 1250 463098390 463098421
    0xc09030803040f03020f0705030a03050c0f0f06070314090604110619050307030c1b0b150d080703080c0301180b010c05191b051809031c05010e0105060c0d0305 70
    0x40c0100d80000200800e10101c04040c1c044075210303900f00e92510403048201a102e03003c80c05083d41c940c01000b0640040f0b44100c01a1548132201029108071a20002005180c44180f40c64880d040d008001008802c6405200b421800030402114403010301d401015180c940c407005100400800da03140d040d41c8a0313140d5006680191008091007500c5181094000d801c640041b155540002e05142c4550b291354803e00c000b0201c2106040703012100d40141d520980c03800c10081413203050705c01c41180c480d06691100b010312201802a40c03000c0c1d0722031403410010110303100204a041109002c2004204040801000d99095842000d00040502203100102d9000c001360344e0142c03407031080c4c009054440d90342e0f21a11007070504c2801e02d4960002c0412142d080030f05e0500c140f80d8003a5901c2000c0c4819085460001c0d4040550019203250912a41309203410b120804200c0381e030703103a50b08014450300c0c0031855681d0250004503051800c0c01d1540790016a00d0025541354420541c541c40031400109410a08 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 463100890 1250 463099640 463099643
    0x12070f020d110f3001020c0a0f0209010f0501020303010b130e0f0f060a051e0a2c01091802010507061e0b0f0d1a100e01030b0a0b01031109040c0903 65
    0x11000806060400080c0c2c060080541072141c162001d211101c1c0c50500c0c1100a114040042c418000c0600c071400c134103d4034040d403044050b5400700004210610140814001c1c64032860004201015034014001c054105030408403217090b050f4170a0000342e0b00002928115211252025038401c1e005406950703280e810781c400c042401d200c0042c0620412900f94451107078414170b2561300507030f80300c004001075403100b44600b50b003012201c441050414001c4071414103c140c064050b0081c170303980303000c00d42d240d1084081110450600701c0c40c0382007d64061000d180100340c143d20030301403602004269051100c0d07443c0000d050200020f0003c00304549a0401460390480e504800420030807a11208051701c1959041481005000b03902078452078042c50304583c0540100c00c0c20321a05070071503050b60140c00540400404010700100052031038031021054082c51045004d42d00c5800d02c03149003821344007527060007810b16040c8003410080420f403100390346003101d0484011070103c000c00070503100315241d03410 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 463102140 1250 463100890 463100899
    0x140a08030a06170a02010f030b0f060a0509031009020a0e07030e071502070e0118020901022505150702090c22080c010e06190309030512070305060306160212070f02 72
    0xc0101d800d41a50040c02101c1848098010801a180c0341640340da0503068001d0101c0c8600e8000c40e02c082c4070303502464114102900030000c13400c6d01000078900d50030130202d2100095000078031800c50f04082c46044040d2100761405e0098a00c56070000e603a1103554002c401d9440d1040b130000b40079507c0380d0410220204c442c0155130f8400d44038040720405840c0b1102e010054800e21000181c0503205a00c068105c3e10305481100c22170180d90001700203540003021003811481800034070b400c5080c0c055000c04210110850000b1601c2c500024885502c1440140c3c2c4003c0c1803d002140140c1c84027480f090340416a1001d8a50305c101d0030f5a06001d44214110704804140a000d0110b40484c0029104010400c240c80390302040f9070320410010184100c8404c400c49000001e0102c55090207604003407103142c4179041160804100d040300c5000b210046640724002901c907400e1141c0c038103051018075000212900f000c004403a082c64060359a030f0055064002600f80012440c2c14404c1034140310841903402003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 463103390 1250 463102140 463102147
    0x708030301051c02041b02160513020703181418010e16020712050610050f0319050109080f0d0c050306030a0f080c0a0c080d0203070b0403120b0603072304080604140a08 74
    0x128542000c1d0000201901502c1101e5203200c8c0e1104038040d4004851000304007090b0308900b101214040d4000c0c0070102c050150703286d0b00c0e00b21203090a9022024003031850070665035443c1e08040142e450070f0865071104441c1e5040040c00b0890f01150301580c0700c0c04a1580300890040d80408a15004082e404241d4250095000800f04040450303180e000303003d10802c00100940710003c100071350b0014070304103138180c1c09a00080000000c0d2440307105a28041c0d000043e45c40b050b44c17030b030340c804e50707c0301c5007400380190001120b0700300340c0c80e5220303480c08250289029411840c022021907942c140f50308000d045404135501c0741d020005480115481c420a00c002d0754202c80b41031420314416103250003040582d002d00f00c034070090f031880001964400c40d0031082e2402d05031550740f41503516500d0350701c2011342c00c2e48600a0018544840300118006e4001e6a142400103041000130807103c00f1209104466403400c0104024501000500e680c00a41248170104400141c5034814030345840450700900215010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 463104640 1250 463103390 463103411
    0x27050409021206091b090c032a040902070501200301170a1502030103020a06140a0305070c0c0803030a0605090c040311010c050607031d0105070f0f0c05010513140708030301051c0204 80
    0xc40d45006005020324031000c41d00100c410043c1440c0701f198102034030a01480061107001c2c1c220008030390a100120048460060311408a45903032050704070803441500080c014040207024031600c51310f00340500a4075040320000e4203044541c40107101d11110404070464800c00614288070940045902681108a6181c0d100b02c01000e50000d1009a200341c250107000503a445c05940e24404002d24140c0d920b140c010000d200764001c0c5409031103070080122501d150000550309010a101604a17400115201e20307017044928140c840a4000383e0061348004280800c4100043c140c400f9a944810380800034403c180040740e0041c00400064000e21408083c0010150158000d541c0c9884140d00011130383c03d43d0707000b10f00740e0341d06441000003c0d9044d0f4070800500d10411a0040010b01403504100c08075568580c1c03403e40e20305880288040c00315030400c0042000d5025465010441c0002800e070040c034241d4800e0300c034001440b0345406510803070032041c0803011044140b40160385c020f02c10841140b40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 463105890 1250 463104640 463104643
    0x30c0a0c0504050105010f02100203040f12020a15152c01030803090d050a0f0e0a080d030e240403031e02031602060f0112030c0807212705040902120609 67
    0xc600c1150702442ca0840082401e511411076034412025540040194103001401c42d0300035440100156582200c1c400c0720400a54042080103074000c0a600601d0110400e050401e140da0300d5080180c007403458400810030a005e036256030802c070b0703104512500000c495968485841e40005c0214100002c91030004400c1010b10f0003e140100002012a801441465025038451182c45080c00104071480c040400d01c502c50b1034141d24001014020079202561099003c0c075108064610001007900e079088100d14020400030700c042100e50b0220720f603024030b594101010302c12018001808250f03c0d25066140b1000c1c0070100c208055170410219135038608200d0410195007402c54000050040d8400304500c92400040e990507103443c07043c406860441d0381e806139030310124120215200b003424014580402c030074200030301d40c01c0d4100c03000300c21003824088014104010200c0a04e00902e01d0b48918801d03800f02c55103a402c0e17441c203171070028002c2d44600004690004683c44a052440b0703000030044610300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 463107140 1250 463105890 463105913
    0x3120f2c030412080703030e01020a1d0a0b030f09161410030608030906090409020a08070501170115050d0902040f020d0f0207020d0f080408160302150313060c02030c0a 74
    0x202142108441504000c80358407480380c0e1180114801e10a12648080303003441000f842c00c640710f03040000700189210400741c2079030060841d040c08500d4417001e4452985807901744466149084400714080e0742807880001c12408007400141c690709280f0f000032840c0104011f21041101c10074030b943c580c16503910041c00c50908500c401030007000300241e0506058040d000707000a03102c10740040c606007103102e0148682a001807068550080cac130f80c11080d02503141e841e2030700c0c0580504409402400d00344000540380b1190300004001006801d0010405030102c002680380c4080b0910b40306554032403203075245000d082d003090007a502c240390039814200f8500641c001c0c0200b880f0100c09000c010550300c1000200c2c001d41c0b00c007a4001c1428412140066038100302000010b04c29400c01d070416803168036003840c1c014482c0322144010318120b0203105500d05850300d4034404000755900e03461880d00c41e00c820041c4070b6668006102d140c8450610400900a0058070007102c2c040f400c640942c5440c3c10b00d10200e0f00c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 463108390 1250 463107140 463107191
    0x120702160b0a09170c010302131e030203060f0906060d02060f120a0510060518060f03011211120a0b060a09020d0501140103021e03060d0807060212150d03120f 70
    0x30b242110020301040d26260450400002d00045c20140c180d1100540180d400010695000c04e03c07804003140c0600b079501840d0035400000c0c8644800f034154810316103450340180c42c0d4500b40c0c60100401c41520700c001499070b0f00003810f542080c564020752011600a000d01c04001014850104020000111907820383d441112441003c0c030083c0c40e030260202d004000340c041c080014408100c0c40c8801d860070309460700d550a0203040c56142c003c80303003508805a0800e0300540825281781c2040d800740000800165000501114030b18160808000c0d02540d80c0d510480c000c004020000018a65a5031b414201b40240740000007903540340c0c000c201a0005003030900601710b907404504408400f40d403003407090f1280103048081e0f00c41001401240c2c01141d41004107847d51180383c81c1030b0200020183c00241804c988221005a2689041051030243c0c140040031070001b10043d02c0401c1c3d0b90f0342e820021000d00c940609100a00c4802c00030030001511180c207210040c142010105690010031007890a03440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 463109640 1250 463108390 463108397
    0x15011b1209060503010b0406080907030203071502060604060e0a0b010c23060a1b120e0102180f030111040512030c0d02160b04150f0c0209010303030f060b030408120702160b0a 77
    0xc030703242c10b41035810740020b0040721000542444103002e120300800c100c40d040b1090008480d110340d1389500091403e1165082160102460014924482c0d0104140383c0c016504071018440f050410100c00c0400a0003454949600c1d201c6841e0011039018105c4140e005070022498a42007040c0000d4a15008000700301119612840000841404062003440205005400000c01071510160111120300400302d20204080d1b549c44940c503228001d200a03e030411400c0c9904a10442210070094024403855980e40a07904040810390360759070b410b04172420f032601120100307503010030408454518050050068414071071b0144042e00c00f600040e41008040c1d0241c030080800303441b80e44c6d000c0c8a01607886481e4200c0c1d400d2800e04034071405517070411000a46445c21710f6a03240c094001070740d001380a91065000c02d5403105014603440860056401800d80d554170707207186042540e00ca640d10320420007000c4450603100c01040c0750700c1c420300c05000d011700004100600342d5141c0e44401c40c42c3c0e00040c14030011 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 463110890 1250 463109640 463109657
    0x13060e07080712021c0201090b040602150601020a020f1009031a01090b0d0c060c1515050103110a051602030a020a03110406050909030702041d010204080708010608031215011b12 78
    0x25543c2c0000c4003000a501420701e116802e55455101c501c8441d81e401281800700c148800300300340d540100a000200851743c001c021b80d40d4621042c40c4402d10180400741150850010700c0056140c0da80840d641c0e0b9400d46422080c40c10900c3c0444a14005400c014842d9080b101c8180c2010b80102d0458140d881c000c000b00a801452800c00c0b40020f11020300030000003401c8400c01456018081c14480301e400b0303604000d241c444072500c00044811040035044956154501800996810700c0741c2c803400c01c08400c08034a003040c0c81c84042c04a0081e62740d45095002618131748001c54600340101c1c0c0c07440360301905c503490b616124038000000ca24040c03001d5000d145080c20000381c0d86013a4401c50b015845c1000518030300441a001d100203410580c0a8046c2c03030400040390300b1811424030080c001017610f8805020369904005400d402c2d100d0301e03030044d502a44103100080c844100740b41c0144e000400c0c1c4a000c562844410010b0722203440c1e4002c003c506000881aa10621080f0010380b04908420761b82c40310f0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 463112140 1250 463110890 463110899
    0x31311060c0d081f15080703090f0b1006090812030c070b0903122802030a2405240a05130f230d05030306130e060a09050d0f0c0b13060e070807 63
    0x303925014892500c85c0041883c10003c814041e81d0350580084c0d2924021607140125141c42081145100b0100c0702e042e400d00820200c010b13107aa4600107403005280ca801054580b160865440c080c10500032030704140040440c8ea00904081184c6140364000c079109854a0081a5203459810417958006408003140c001025a420159282410340b603500141060114241e002c0000303400041140c2080340e90341c100c561500859480000e0a43c126078580c01c200703402c19051002000541500d00340b1420b000c045a0301d01c0e22072030160b50f50800d007441c2244d1142900010606003100e0f81d8031400284960200210702804240928501080144c2c07500b4030402c000c00c14040002c00200c400351050704144041407072881d11600309070301c20489040200701284007084550402106662021290307545010040410406005a600a8a83d0b0405002c541d020078070141a240324040c1c02043c8800c2140003410000c500c070314070000c4e240c0010003004494088458140e50306610300415846100300500081c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 463113390 1250 463112140 463112191
    0x7050f0601330f210e010b030604020a0e041b0603230f07030e010e0601140406051203030613020d020711010801090b15030c04050607080301050411031311060c0d08 72
    0x38520400d020181003001c0c10a542112904020594a801c000134002e294040603035000114001d9501c126002a10503d450030282c21a40b6486480d40690001800c11001d660351325803180c01c98032048590951076480e80b40054001c7c10790301c00f64100d929548008240250b040c3d21504203a018411100c110040b6541d0b0310700d8400c800c90300b20030404412400600c0d01c40c401e40090340c8000c2c0b02000031400c0100180140c0c00c0902c00d0700004d040500e2031807190b03898038260103818001c00c01910f2b0103a542121341c804585074440200114041c8246021f07100f51030a460381191001000c801c07045440d030030030780791510844600051181c00540040300200e10413800c0e2040c1d849403403000b00480940c80c64042d8014958000410081900d030081c0302c001510b8441e9002809240c0c480e64100d0340c0c960411041004513810564a0500303070301e060003000018000101002d42442d00000c008030050140c400064a03845042290811409842501004103800010450051095544002000d4201000030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 463114640 1250 463113390 463113449
    0x10020301030b151504030809040f050112080a18030b040b16270906030318090218060c0c1002030703090e040f080f07020d0f0b3907050f0601 62
    0x180031202c030040031410044403000780c3c00104001030660071a40f82a10180001c0d600190b009031a0381c00002001c40d0645031074810445002038100d01005294140604a80ca6910f4903500511460001401d00b61441c000c22042551010030382d8120241c540360315104400c0c40099070201e56540446011805c120402085c244401e25203580301ca51200044800d4004880c9140100640b103828140200c0e88401e0382c000c1e1009076010f0b464504243d4112550b02011030803a9100c1e105451061003a4204200350802007019030004644c1d298039465501240b50800c40b0a69105c0c1d0700c84400c5800354103035a000300180044902a403581c0e04081e507203800706c0d1661f1b4811038000340103280c03080503900029011005041d00b11400c001041c240040c0340e010421000300a002940c40c50744220761041000700074040240e106084000b002030307902c00c883c60000c0d41c00c9160641d200201e4a8843c00c03c00a01c1c1c10b003940e034850340290880740c60303090807200244c4030301d009e00400f00902d8107a10b5061004034a0702a8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 463115890 1250 463114640 463114643
    0x60609080606120d050a0c14010207150516030b1903030224130303150801060617150d171c02040f08070f03060f0f15060f030e0c06030a15030b06031002030103 70
    0x4d0102e180700f6220440c0c041e4003401d400800d0001d01c1510300017080038110040d001e030355080c1c00140c1d05c0c1c2560a1402070b804407965488221820718040041c0841a40c1c82c50800704458100816600d04c0a80000c410100e0342c1c4502e662900344560000601d0341c000f1304100c590903e04c40c0c084040c3e001071075698a489080310115074983e0307a200c40c50300003031013503100c032301042411301454441c01d03214000036003914200d500c20700c005003807031200c4c1200039008403045400c4805502c469980115000c0416000310101101400d130a040503941c1e5007090100084822821112041c51740d4880a03921090094201d40a03a101902c00084003048000e000101082a00c1003248c11540062451340c070040a0f103c00b41c100d000b088e80320500f070f140c0c0304c1d0380d8040c1420000b0644400c0d11120f08081008004400c840700745000c040c1081f008024009000c503020400f0303107054a0066403980c5490500018002c0203020252461403094000706001001450a001d4102142a079146510344418036050f80406e000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 463117140 1250 463115890 463115893
    0x114060a030201050313030512131b051c02060409021b0106050301020405060304060f0908042d06140c010b09040c06020c061201090506030a0204050a0e0f12070201081906060908060612 81
    0xb1924440714035006e0070a1501c2468070300e180000c41803400448000607901d4109045604503554100310142d50b0402580004a22185185150400080710501e0583e0140400580e0140820940d01d0314000c40d405042c241c0c10035562030150f4071090044054580000364554a018000b203240c1c6418003c6a0444200402050450700c50780c454500406029046075040780e80d41ca003000006805a0150000301400d0072036040f020944842e03100d40c0480d107104950300303031300d04042484000e0700007a20024561100c0714075919171150000d01f0b4014038140021607400841075040104000040030801300340d40c0541d003555003220300c007400c1c4003080c040c803100c845600500d40014020030003607602c92540302c41c00800301c079110785164000c0b03400c85d24103175058150039444074440c503054a820401c408550311514020000e003c54400440168014000000c1c10070503a880840c1c042804010a2440114041c3d4204803680e40e6950113000b5180d1845800914001c82c4d000070010715000c004600000c80060 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 463118390 1250 463117140 463117147
    0x319030e01051c0f05090105150a0b07031202030c0c12180f03100e06070f0203120a050c0c010609090303111c0203071103160b061219080403140114060a03020105 71
    0x3005484a4000d401c0010414400105000304a0181d00403082500443c8200040c42d00f0300074042c500f50f541c028280c07581c00c1811105211981c992005035030803201c0340c002054494600c1d21b02154459440c0004604041c000b0042c40301e83e511907002007079500d0444044580d14411080c1202c10340c040c595060082e4003160441d40c0b49800d0100a0f10800c83c4001d00f40c49a08090284d8a011104c54110400c01c035840a01001007040c1c2240c9001008003460004509252084015101211006181c604000e44a102050b10204480c0503074141c410607100a000c000d40300c1c540180108610383e01600001d040151144103000010222086004007034600d520000802001002030b60019024030200004190851006103083c409440c841039480c6258010311003508044420701805452b03030b84540100c95440c41800c0d000507400c0050108240101402422030900e85140c0c015a480944a81d0528548581010381940005241c042c050620100394540c0b0341408007001060000034040f07003080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 463119640 1250 463118390 463118417
    0x1110080106020703021521040501051008120a181d22020405070905060d0b040c2a020f13020a0305070e030a060b130e030d0b041a0f03010e0d0e031903 66
    0x106c0703502c01d5401c00d29540030b25100c07502030821420b0454000402c5040c0d03807402031104100c428080c80f500090000c010034210b601b0907020340d4a90504500b0f00071500c10006040c2101c50103014043c002ca80220410004a80d94207080180354510700d01c1b0302c1150b00388074001801480240307100c44950341c91695081c80e4001d01c1c0d007400700801014226100f40041400009816664500105440c0c80c50110128a00d4028410301066500341040b100c00d00081e42d5413220740c0059001d02c1240214840e0741100784105900205450554030b44649030001c1c1c1c8000b503140440d4540d001041c0d00e0b0721980e4100a10b9a9100045a0800044c02c200342d00d0740041d4050b0001c101761303070455240d0200c020311240d0307101440d41d000002c544a42501c0c00700d41d000420312207244c0b445031041b203401610654041c0030204a001c9407400030205170b41124821003201da07110362107403002d501106405c007400c1c04030ac43d001103100002e88903103144c001651203803084441c0801101d591013811410b6942c03648514040c0c8024 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 463120890 1250 463119640 463119649
    0x318010c0806041a040e16050306040b041e080f03011d040c1a09030f0a021306050d060c050720270c090105220515071a0907050301050103111008010602070302 70
    0x291480c490a000c442004c20304075130fa40d8030a100d1103200e100001c3c0660305800c00701706070702241da41c17029200c2e4000508200c00f040404003140c0d800fa5112110b51500c0f100d0a06000399080d281e400945095008501ca440e038111f400000c0d4140c900300c0c804c07a15100840d0102280b05002150010700f80b400b880703410801282280541154480ad40c0c9039141070000d10800b00307180c40b03a6680c0604c181c0d4040c5950400f54102038020004207004004180040c504000125801081e42c50000342550350b1820844801340c4030307002755448203500c201011211180240e003540140b801124036841000421050507003080d036102e209465400a20940100c1c0c0e8845940c171182d50080c03441c1906000040081c0c0519070604502d17144140c44e0910315500c0c09040005000c6680d10300d006130388040070100201400300310060200810510f02c010140c0c410382e518000a030400165a00c621f81560a050000c000c100010382003048141060b6088400301c1c501040445401c1001e204032009604005010310150a1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 463122140 1250 463120890 463120901
    0xf0806031219110d090b0d1425050703080f0426030f22150b120c040e160b03040303090b09010b0307050108190906200318010c080604 59
    0x240101070780c00c00d04100d035115005511001c1524480302180a0480840360440c07001d00641c04480002c00703040c80d0021000c2c040055900802210a0010076803580c0715065030880c80134042c40803903c003064103202081034504a0711072840c8441007443c1d0110144603100b602070f114242d800d90384048640d1540d4003580b8200764060b00556400803080c0d040a4806001c8525900390a00f040041d6902d1601c40721148807011701401e807244250007030400b8860880792880703091b07840b5001105001500481400c00000f0442001e0050f009951003840c0e04a04002044600c40680161418402101c007142c5240d00d440a0004210000005410a1010300013160103076a1081c413a0030005109910f41e20345009130a4103d401c80710a039104d000410351400d0030300c40a00200300c00c1c01d00d80d042c0c1c100743d1240082141003100841240d6642c210740c809100031070700103008001300c422424400344c2019038981ca155004460488080c8004414411444414805d85665020560390040c0640701c007030401001e400c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 463123390 1250 463122140 463122151
    0x3012d0b032503030f0c170903160f050103060e01080613031b0b040323040504090501090c0308030714040303020c0603190c0f020d020f1207051002030703020304020a12030f08 77
    0x8542449045070000302c0740310312000c419880029859524520f4000c004c0d000c4005202c0412040100c400700240c16400d414030420f8062100540360150075002c20b18001c0140b400c2d000c04442400001440c10302400e02005071802130760284402074840d407a0500c80f41c800e120307803d81c0d5480040000d45a070824211000a83c1c424900003030728485903806d103100800a0f50007685c442e95a035041c007040507000302c00c0c078259800600c9148a000c99000b503049050181c0c0c032606015035155001c07176041017130030752001c18415805000030704c5040d00c0c1d08280200c0d070400c407101804140d150180d1020007607110700f070340c084075450350041190f03d21801c144103541d08094828800240295591203001d4618040c2c45542240c540c3c42c881608540c080c000c3c83d0080300c3c003048040d904200d907031024419010030030034900240c02208643da2091454140d00c0c3c82101c0c46c0741d80d038407071012040c881d40c551716400541c003880c000c5034440c0c1c4140c4c840010810f13640c018100140851a07060550420a000303040190740032 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 463124640 1250 463123390 463123393
    0x12020d090b0a140f071b050904030f0f09081002030f0606040807210227071715010915020102040305150c0a0806030304051302070210030606200304050a06020a0203012d0b03 76
    0xd006041c038041ca0700040300454002081130f40c6d400e0304006090394400240b0342182c0581c1503061540340030303080050504a0004000c400501706e45c1a50241107101c00412200d42141c66400e81c2c4600c10000750401d487c05540c50b200c540c042030444c9080d0040c0d4060701c0c4210054040300d486c00304000c14400b00c142007103010620b0034030b144000d80e41d140070950180340d4080041081c1500410400d01c041001040790b000d2100f600e40d030b000300c0202802c82952051200c81c40c400d02ca021140180c0d0143c20303a8bc042f00c0214020741c84400142e40c1074019208032480303002194207000442580307800030036080340c030804107520070f202d5400a42c4c410040550001005030603a4501034460003c1010326958100000c0c6050f00082c0c07010450410b6040d0030703816010747c039082100d1800d000b0300505812b4007209003140c10014160329100c90800340708a40043c00c2c01043d441c0744942c0c41d0406902c84616140a07482546041c0450003000549548120444850104203544000741c030b071464003e00c02c2e050341c4d5405 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 463125890 1250 463124640 463124647
    0x7150b0f0402070614241302070503030103050706020706020d050904020702190f0515070c06180503061501020d0e010f0c060b09010608060a08030a05160f05060412020d090b0a14 78
    0x141c54901c01000001d000349000300d40400504402d92414801034281808050402d980240d40c5507414184d82c10b56500311251942d130700120070940c029004110010308030780000000081081800141c68080341e0351a025120000d585410036615401300d8210035000c10020402c10003c1e1501703500419900d0302c010800d4a40d003940460030145083c00d41c11809205000030828040d904e03103407043d14400d01035082d51a2a00d800d55584e480d600c5140d20485051010030305905241e000040c41d0100980340280841d00c0900d0100e0514071070030801940203026004660f21980d20a02c12a8205100c04060b12200002138400310f0440361410f25000a540083e13032444103007016520444114001d04442e0b1310a155420200100654041ca5a018040b00d9108000065410f5040001d844c0b42d044003038100d01041d1914107103c10507034001c0a0090480c00f41c4400c11042040c2c050340140b0031406a421100c88114000040da80306085004030380400c041880f44210203031140b81c043c04045254030f0300320b09 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 463127140 1250 463125890 463125919
    0x601090504290601021e1018120c3f020124091104030530070302010f050907140907030213120201030c050703231b03040e0c07150b 58
    0xa454030741c00c1c00400c0b01c0c02c0341d00a210a80d0703410804c034550b4100c1e610941101c441c541e154940e40f201010842080d2a807180da251a510750600200c510b0b00e41c005003180d0300b1410391074000b020400003820441e40f40c0c1120310845031514881d0410034040c1c00d605082540c11501c00c601042e80c0e2000b0f80c040c0c007159282c40545500c20107440c1035140d40208800030140309803c0c84510800c0e20540c8100d10f4028100f4007040002c078200141382c49415010b2000d101307480d0489603140f040440d0340800c0403c00d1304002014001c045c0d0550181182d042c80c3c0c1c104004a842d000c128503168400c40c818014200f0720340d6050b80c0c440c6091802140c115299050061034040c0f45510104450401d0380090b0010b03520307038003003801d55816002c0c070b020f100f0349407600d05c0c940001603070b020b41844591400034070940a070201144010b1100800c80740c58242004604258401140340e8a03502ea01a01401043c4040308010509100003641619001603200070101c04100c0e04031a20b9004042d4881c00c298400e68852000c1c0307 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 463128390 1250 463127140 463127183
    0x4081306020c0f0909031e07020405070215010510020c04110d09081e3108011d0c030705030c010f090e1e0906010f1503060509011d01170601090504 65
    0x10000c0a00d6009407040004407010402c0e000c003e20b075410302075124101000342011020044030030700740c1e01c11509111800307480000d4403940100348001b50054070b81030a2089040e00015181080110501c50056580e00c450a0000c030309403812819000d41d100b2101980b162800d50440700a0500729103415003040c111448803030568032420000c0e034520b0340c00909041d083c6044408200800c040b907820707a00d0249180419100c91003a1000c1036540c03080703089241205c070034115181e13004006072802840300c40d50015500440c50315045425489105100c50b4004a08001c0b40540c11203400502500c1202501001502c80000440c541d908118445001140040c410b0030020b0107641510720701c1469403d40c402c2d07610103c0e0003600082c0c0640c00f2500400c40f42d800d0071141e10650b103803500c0383c01090102a0065014011035040981d2080700c070b50020405c0300d400681c800f45903450194089041c1d0745ca542007541074205e4410740c103003a0030410060028425039000705412600c00c50b5500e1054080c2c540c0f04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 463129496 1106 463128390 463128427
    0x1050102060609060d0b1612140c09060706090b040b1311040c2003070c050d151107020301020c070602010606050405010801180e030f090103110408060a050408 70
    0x141c01341e01c0301c46021380e85c1940500400210f0802406110b80000007204071400101312480b161100c3d01d090140c1c0030380a424450b0403000d82c4900b0309503005075014038a4540c110302d08000d0700c40003402502c6103243d00d5000d0035400f0780705c0c18a491718414014020b09403018030752740081d2507804101c2c11b5050900100c3d00300c80016000740300e144140c80d01c54010b00443d501c40c80648884143c0c1c140031005012880c891400e007400e580d228010040d510a40e880041c108071840d204441c2840601d51040710710700c0b0b81c0700059007892045e900107070aa83c031003c698101a009010b040000c540c0901a00014148600b8098100b6040c0000241401d205206a504c2d00b51181c400c840b0400041e886100001d402101f034903624084401c010311540d10000c200750000380390030302c2c1c0401d13002140c003542c0a07140c00c980502071a8894035440b101402c0041e0007960101001c000000301c08152100b00d = true := by decide +kernel

theorem cover : BRFrame.Cov 462949640 463129496 := by
  have h0 := BRFrame.cov_init 462949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 462949640 ≤ n) (h2 : n < 463129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
