-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3490
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:48:48.093375+00:00
-- url     : https://prove2.me/submissions/538d7d45-9c9f-421a-a3ea-cd7f114c856f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 627517985 ≤ n < 627697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 627519235 1250 627517985 627518011
    0x1202071a0c13030f170a120b09010b160c05030f010905010f06031e060f0507050714010b0105040909170a031d0c03062e030c050103060905010503120a17040303090b 72
    0x1802c0c60100301214407004040e2114007580c1d10030804501c041021580114034016152120702800800c803c07124000054001d00c1c1449145103030921500b00c070305894004184034031703040ca4036041032031603400b07081c0c00c0d82c24491546003c15240d80c28400c540c00d0060300740c00801c991400b0f003030150071a500c8110345040c0901d803d0702000001e1001116007581141c00807801840300c21824818080c0a84041b141d1040e4074200070031060b2604400030f041d070107000717840700b05c1070312804889103007240c1d600b12080d80816028002045065002c0e040800118401d10801c3c4604540d0f1480304400d8105040700c1c40841d45038000071601027210300c1c0c0c0315002885403004044007041d801c0440e4946102400e60482400b036000f00e074aa0444110451030010046200030840d181d80341030110004159016450019041900014407080a4051349050710b81c000c02a01e41c0030600200c0d07490b02d80c44840950305121546c0203143741c4c031180159242c410740c0a600d02080c40b030704615060b1303400c21000740207400c2c0324a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 627520485 1250 627519235 627519247
    0xa0b0a080105010e010b07030207031a010f0b090f0f060706060f081627230910020a0203160606030b09010b0f01030903020c0405180106030311010b03070303020303070e011202071a0c 80
    0xd484000300e41103405d01b40344280e4818080c10100d0410355503410290074642401c103410046201002502c4c100c550980040070029169111050b0074800c03101890b6000107074883d0744950340b0305612448502000200300f81e1a00e2002d82e10f030b0703007998040e41c403084443d031445108008249040c8010828801002443c04071a07052103206c190700d2103100201030440c00028020340c46000d06900110540041855025900858420810b0000001c50f80704200c1d01802d83c0c00310800c0c0b9240255081886a80c001e5403e1180c2010400c0500400341019288141c9620380007010442200d0710324003a1081c00004501c95044005200c40c290740040b00a04240c035100309880400d902065100468400300d60124698036880c03100c0c0100c4807106d09140c01546020302c00030406800c8501c68181c44418002400804445020191100700610001d005a00b08100050b0f03041d200d040345010f02031050600300398044c0c01440d507200700c0c0c00401080300d400500851030803030211480700c550fa02006401c04645001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 627521735 1250 627520485 627520499
    0x1002030903040603020f040506030112050d0905150711120d03110403020913030306081b150f03041b09140f06040902060a1d0d05010606080c040e070e180a0b0a08010501 74
    0x200c00d40c0f0803c800c0640c0802c014101c00d0140003103a005042c01005161256110b40f241c0da0b16403107000b070032101d45c450382502910b210700544400003111002848250140035002d044861940182811100c0182a0010049075607c8804030361120400c040144806010100003070204c9001540c03400c00c4078424001000141d50760420039a0100f651406040080101e140507000b0349815003001815010340e480d0700c40140107040301da5462010440d00c1855a09001c00703d802c603032003031503060040700c00108001008210510740c040081407600d4580c21a0668840301e2030121124801c09545044441062144015200d0301c21034000408031003c0044200942c00203001e84960402c010a001080f544025500f41103003000c0d40303103040a00820f00410359464901d008100902810f00401c9150707011070521181102620156910f8545500040e10781520a803042c00080c40c00c1580405000d0306210b00346074a0030030501a4403a001c1c0402d0a411490400503c120a0b4001010581c5403000401c207071 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 627522985 1250 627521735 627521737
    0x5041e050d02010c0201020f0604110a050103021806070515011203080703050709090506150d0b040608150a1d01240b0a0504030605072d02120c0c19090f0501081002030903 75
    0x30780d41c24246404145120b05c01030341046980d660008203030140c40c040005100146040c41e0340700c80115511041d42e0703104c8006408038000c03a410aa068800c03524480300606081005044460048044441c212804481c0303e95102c0c0c02d070098041800ba0403085810582c20045117508440e02d4103042c4030358036150398020500000b034030816224a46400114102d0746858042d5070f20042c81800440c1e880300c84608280240c2644030341c4038001c0749800d0000907500c10100d0360600c0c60442c2501410142c9840c51a1005003a42240c141c007a1a40700202d500700002c01d201d10110700100c4581a803050040e808103109540e4580d001d00c4242e10100016030140c1d90001c1180c0a4076400b80c0300062a4a0ba400204c4400266544022000c8074910654a91308540c2d2010034441115a00315904c030b0055656641080c00340c0b1202001d1a404180c0307a46140c5000080034000d081151204c171030b02c0b66182588000d0f2001e6548003c0780d95aa14018044d031a0b0500402c580061012000d41c55420104a01a13903 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 627524235 1250 627522985 627523009
    0x803040b0f0909130c14102001290904080f092704020307170d0809030409060308030907090908070b0601030e030a0c110a0605030c130801090b1e0c09040e16030305041e05 75
    0xc009221912300502c542004442c4134171100075000f000240f002d01c2c21401315030041c83c07040500705c41e86038202d081032901a942e90f00c80d948c00546213040c41d4904441c031125801c041c12060303100c003d102c0c0c182030880714a0820765162003000e241600340c0c02c0500615050008035001802c6403200d03c2a40c140c40440060658074250107450982c40641e07035204100d085000d503800910409047c80800410b101038a806540251090010b0b200211b9035050088211030840600401b102e40a0241e0804601d01200d001c2c2c0c480c0c018140031130b1003600b00b80710b0b40c11030348206a01d0011503000c003451420b104402c01d04034020032040e242201030a06021010f0142e0100401c44084601d0008220307074880d2007481c1200061203c2d10081c05102c0c85d0f07141010401200b01d92102404600e212000d13a82044103040c14025641048854030305040c0000703120140c0385112031300000740f2881c03442020380018102140021406035440303a88075810301421881403a503a2000044103c11341409200580c0c071031050b602 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 627525485 1250 627524235 627524237
    0x40513030f0c02030a08040e27190203160905070f0513170a05030301030501200a0e0402030c040b04030c030b090604110d0f0506070306031103070803040b0f0909130c1410 75
    0x2d500d401501c0003034500048800002c00684000c20b00103003008000d01c80354014128415966a161700d485581504041500707401a03155121700e2903002c08841444c071103d00c860000e4151007551031202c0c2101c14811483d4004801036a891081004981d03000c41d6030240140300d444c06902e04079207450424001060350141d40714201344c0990000491000b0042c0c2c03084280d100054036160343c1d40c0e040c441d008009440c1d4000050780c200010074403040039030b8212080e050071512840c0207080040d09100003500001e0030000c1030802044049110754020020740f00540c441c8000e03008503811407502100391040034111007015440b010902c000102003e01c035282141040c0d44200c010281c500345503000b85605000034215000706000e2024259168000d20300341c80c0a20507042c10300c0800c406160b030721201b9105d8900b007500140028004650044010181c01142e003c5440c00c0c0750b1140300040c2607090030740c0e03260585d1401e43c42110400000f40141030050404108550b2815003410203c1d0f0041c0c02050200 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 627526735 1250 627525485 627525497
    0xe100e180a0e0d0c05150105010503040b09010e1b04150302030a0f050a1203240b0a081005040507080708060a0b030604020901030f0e0c03060c2d0f1305040513030f 72
    0x28003884020b510900d48180340e1801c485007100742c103601504600060b10281c4180c081c1a110103481d805010501d8121001a91071901e1070390766446242802101400001e811b54132070300503140039101008106400d082a61200c0c5c880744a8508000848001994505c50010703140d10030005a80c0104601a100750000f56010aa40080c40d00604080c441d43d0000d01d0300840300c68003000e5650590141155100d0301c40b00c10800d404030021081c5801c42c502c54440302280401c0640d61480c0f140744501e4020140303406100b2455101c200280540d00111030303000c0011850000c02004c81e600c40c403901c0e040f420076120810140d04000d00c0f0500c03441700502450180b43c00040f10025a4840da0040f20760070400d102c1040080901c0d00082d88900302081001d01ca84942c001003003694074250201d8107849280f100266007818581c2c201d0007400d203481c02030046200c1c14020130182d40044030040100b841901403407030340300782001c0410080310340184c030010a03549400310640010381c208041c0380a004150510ae = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 627527985 1250 627526735 627526741
    0x101d07080a14030405090a090210020a0c1511012307030903020312061815041a09010e09100507031b0c02150318030705030304030314100306020315030d0e100e18 71
    0x106186101d44c0c5d100382d4000814404000c094aa00c0d40009141d92084032590030302c060307841d0200d958010303143c0060b0001503408807c00040c80040300c2c1440c880072600780050b1000c4180549030031100384c08035400c4503580c22946031010078040c1c010254006094141088103c4c030a441c0295a4090f003d082020303520040c02003400b543c0d664282500351500c50307605032400d00c0c0082803c0005100c00142601860a201d08440c030313240e005800014440001e00520031580c40e20440c00c00c001406010104140074007a204125071100303000b028801c80c0c480e1004508140d40c4c1031046565010300035010300300b00305500c040380183ea0700e0351000030381e00320780340041c0d203030b85480606408400c000300224205100000e0710101700302001c4043d5101e130340a910b041140c03101140c10700440d40c1084941c1d09114003015003d2000500135400b03160021100344443c80030701c00e0207000c2480d000600d0010000b081e0540d1505440d0715103103903104403900d05803500380d07188041d040101d0450710b070109030051001140000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 627529235 1250 627527985 627528023
    0xe061503070f052b110906030a0504020d0203190308131e0c0b0705011d0304180e03090d05150a020405060d0e01020c070303050c06012907050a0203101d07080a 70
    0x5076034410100101004c40304c0902c030b09a0020781c0c3da46000b55403041c1041000d40d20300c4003e800f50745c0000f03405008185103590303c61895000b13000c0140300326840340c2100038030030260f2800c1101c100444c007480e03a28010000700d414041c1031610300400c0c9040064001078104005003021062000b140d5501c0c03001e00b100ba10344d142000c22010f050304841c1c0403032800301d81d810900030305402080c9100614421010310b8242049869100d100754007415184610080010000d501183e120400700d0f005202901e040c042003030000340d128041000252034036404614546c8490552110858101c08082011440c01d460040400e00c0c13400342004002015582e44244400c0181c20f404440b082d001c500280d03403105882c0c0c030b0090001e070020a00048240316020008c50321000d003000030740500109002d1040245d1401000090560126908071228050321400c940140c8041000031501e800226010406e001440540001c0c140c00016080856128010400c80c0750404140c03907003116001214030300d50800d9851 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 627530485 1250 627529235 627529237
    0x30109022b14030912070503060601050313050d09030212010506011e140c07170106080601030204020d0e15091b0a0303031512050304150206040b0105130906020309070e061503070f05 80
    0x900588501000b00341ca00c0800d40100c014085240704542c1c41c19403a4003125403680e40d02d4076000d116051752259000c50302941c004c40145902c50706070300202422240700e58417541416182d90703001340858044c1c4414411840c0585900300055020002003200380f510000080000004006072808800f40041c0304610a00c07a408600c04851005080c0b80c1d00c03900100816aa1040c2e0320070a080414410b074600c0b650f450601540b0b04880341000144503503420364007040001c1d440b540203484416a203520a04141c0d0090165550036032040c1c10544480c0380a84455007801c6103204070b0110003688640c071032142d5403020600c0d4240ca070149400038031a483c0000000d00c0800c40e4010360040c0118014030003c000e0700100401c10f90740700c0f80c0c40a101c8064003400ba0795954046d50010110b44801e00180300340e04040881800e04c2c001040c0200710341c43c0359200c44040364400d94416029400115040c403d60741440070faa9000030041c1d440c00c142685a16100c0c3c1e950101500340c108000d42800030964880c4540 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 627531735 1250 627530485 627530569
    0x509010c0c14090702070f1a070f030e0f060c0703060203090139090605030406110d0f0e0c010504060f0302131a0a02151311150f03040c0503010902 65
    0x24140203482c1c030303003104005010601d8401407044080d203000560f41c074404030340c0e00110303841039901c00043d5003000e031503100702c0c81e0f2580f40c0d24100d281400610f02207040503440080d914007948a040e40c0450110a0011120040394454050802084040412040001c1f0601181e42042d40180c0703a81b81d5200d0b01c0c0c094944007034650145a80706594200100b2001e428642804079a0303115041a00c41c40d1082da1480740c80d106d0400803a0301440001c0108049400420304a20140d1901d0f01d420580e50b101d104541c1c0c054140200c15964070f482491280d02000180400d8900f400c1040c249864000018044655681c0b6001050380201700b21010344141c00907140a420f09160820400d48982101411504202414801849248402040920b0000055000d0a0305039007c4022000d503481d03000480d004445103680040f03041e03c1004d903154014025221400c0c00410355030b585c0c05c05081a030307902d010a4100500c640d03d05805a00142c0d900b0040130640030000c2c1002020642141c01d04100c84210 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 627532985 1250 627531735 627531743
    0xe2b0b04020609030d0207180501060f0804050721050f030f070f050f0114042616111201020c070605030112061109100807090f0308030406110712020606040b0409050c010509010c 78
    0x810300425806c1d004a01403090b204841c1203500c98400d00c3c2d04c01016a0402e00c210804507140d1407140c40070511072114240d000d401402203403000d99440c0340300d080500104070600d0b11005021303455010480203001411400c0780c110f005504258130301d100c0c000349205000004240310811000307801044410b010401104220b81c0080102100303540080c0c0360400104c4049400c100341851440c10b4582c4140540488840701c0300c000d06000e4802c0b0701041d00f0020781c1094581441000c0400c0c160381c0d50191040d05e0844070000503864440408045d03140800380e40007181402018001844002c1941e0064141c154000c4800b00b006c1c00d54041c210703928401d008015030813821f240c8405003010740180e040790091200d6612603071400c2e50381900c03010443d024000201314820070404a004141c01d0f820183d00d0035207456400c0d240400700e03900c414401303811300c0100c0007680000040240324605840f0711070100360241ca05018400903903469030748036880c1c660140d0504c18040b80068050b44294840707100e2680c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 627534235 1250 627532985 627532993
    0xe07090b0406030c030e0a030804110607020a170f030c060705130510081803090114031e040f06050f07050715020d060b0c0106060e030d1407120e2b0b0402060903 71
    0x2d03480000c1c050280328000e503011030b080400c004112100090003c407110f415550b0a4115101d541d1000c115030044644154046014803009025a9030241d89034020100740d00c5d01c851401d945000e05045c4998003041414035001400480b00d000004a141c0d03602840d80e00d0f22564031007040d12200c200c03120b82e402003030708800030030a81c4602d550425405805060216a03480a9440f246111030303580c45260307010b41c002519420f94075103420428014541213882d0075102440350301410521007203070b070302180d098840d054020051001c3c8401c034845d141d00b054020384c1a48891801d42400350552041400081a017220040703602c0c00400540d050340c0c003010300b1800501000d07503540c1042515802100b4030710402d501c0c1100024290b03005206041c8841005801b0340b014241d9902d090301c56103034400150b0316804042240c50005040034880001c4050903450b04141d50203030105228446c0e203842074002052070000c0004400594050403605001e500c0540301c0d05c036644178400304690780610b648003078142c41 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 627535485 1250 627534235 627534239
    0x306010315092415200d0804061b08010e100b03010803041403151f0e2e03082a070b0304120813060e3a0215010e07090b04 54
    0x129a4002029161001d10368080d010145000b490762600103203c0c00050010600f694403c25009040300002c60070220914460707103612401140c14441802c006c1000034a0400c1000304000d014030482413020408030b40850008110000508240418010040120501000140085101d007110b1010301010500d881c0c5035652020820b80d690400d00507044a00141549810390b03040c0016000c200010603100c3c505244c9565003000f01c2e112001156104408035a82c001c918141020300d442d01034030340e080012a942d14a1b41d08480001102c850203040c1c5c264900082021070103841c1620000c00502c0d48400701d21210000822041c0101c200103500c0307020f905400151a84484091407085001360981c0c4140e082c0000d046900031011a45514003440005180c00480c02c43c0d480b841c820796200c000c490303081c90004c019015400709070300204034004c8403600001c800080c0c281c600c40e2540307203800201b100d00d04503003104d08002014000d408509a40308005001d2911036030341103009002d0003140c6680c41d5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 627536735 1250 627535485 627535499
    0x801030b1302121608011103010311060d06060c060b01050c0d200a0501050405011d0316030302040302180105130b01120b06090901080312060d0f0b19020d0207110d03140306010315 79
    0x82e00d039602d0030b804d010700a002400d4401801020301343c0350f030161100e16580c290f0366003007501c0005000150300b0a00038440b40381d170300c0403c0c801d89000c0c104a407901031442c1854542001641e003540f0459041180500c0450303d03125001410899401d1107042c0a505085424074031441c424285c10490b100e0320400c0101024000107510130b40c055400351000b400340c000346540c0c07040c1e04401d06070400055841049100002943d80540081c241e10904e000340c6015503e070001145084800d0b00794542c18000c500400c0701d4901071106108075940410700380300000e5410006040103046503010b000494840b50302c100c495641900b100e440301c00041170b2940c2541c40c0c102c0299244c114040881c00d944040002c01c481d0300d84030ba02e1407845907020300c0c0f03403c1c0c440c00c0c1e90741c004510304050191000c000c080070072010300c01ca0600140c8688455082c0058071050141004090740c6680351a0034010150b050081d400301c0d40c02030040c02101102d950b40c943d00e8076803c00403801401d590000c2c0c8500d0120b050041030b65 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 627537985 1250 627536735 627536743
    0x51206120d1206090b01020a0813090204180e0c150f19090f0b040f092415120e030a080916150e01031a040b040902100c1a0105010801030b130212 64
    0x8140c82c00c01c2084034035241c101802c00c84140740000c07400744c1e001451990014490768024400c01040141d5038003096500c00c0d0a000b030382c2140d04824828143c0d120500002ca00510501d41450030640040c07040c14050400315400081c2102000d2070500c0000301c8044002980c03048031110100c40c103e201e42c1030700043d03000b04540040e000d03100c000401c44c41e00003151340020081e034066400150740500d0662408003190002d040445c0a1030b1600c00800e8481c2c101c007810031519008000f8040700180036100114018010300b41c990030200c4192510045100b410300020944082d401d0070f060400680d19100046460071820b00d6014581d0306025070f01043c4001401e050000d03501442e140c0d218201c00c1407005501769601c0690040c50400404400c842d146440c1c1c00c00182454081c000285200c01030700403138007655420500001113001202c0003010071041c01c0701d4106108007503120701c9581d410140020000c000611010304a6040000130949a8900010420090754010081d1680910011486d525 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 627539235 1250 627537985 627538007
    0xf030b15071703190903020a05070308031006110c0409020a03061107020f0d030e0f151206190e0402060904020d020d0501181505090a020c1009021f051206120d 70
    0x694084519009994041c94152070041504e00300320300d40640c90118003001082c07500015002c44c030a002c80b02d800b00c0c0080c01144095405103021954034980803600031030780300300d540c002c408000100c80c02810304034010a05400301002140c3c04244c2e4a4503000083e448102a0406028145483e481071603c003000301c0103100c4140b00f40c4020240c204030700104000d502c01101d01601086600355885ca40d4640844024001e81000b4a00d1440560b8a2000322036a00120b213003200c10b10802003032001a01d00b00100081c85032043c0c1114804504040c81213003040301c00b400003400307090301064030f40e40ca81d29501519080309291a0131034652001c40704060182000384541a60705e2964510031490403258001e0f441121154050342524070310b8507090000002e0020409041c1550910040c21244818040c43c850f142417000e01250900e654010000d980070b04030340564151001c1c000ea04d0103940c00605a03030800000c0030070400e40c0c5d55801c02090090383c58460340e40140c0101302c02070000c281c005800b0a1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 627540485 1250 627539235 627539243
    0x3162d03080106050405010c122102090306090307080a0f0e130221090a03050d0b061207020d0302070b060105031506031029041a0c012c0606090105010f030b1507 71
    0x4460f661914181c840b889280a850b00045c414a0181e011444640c10040654850303e400180550406d1518484030310404911020540000d4244810301d0200300c400c0e000050180610300d401165a920903c80c0314418810040c0040404c44102c92409507100e0001c0d4003001e8810070320718030b84030303036400082d8410b010000da100d05100d280c1200301984240c540c45410110014002c250060301c2c159041e40201101b18040303500e600d0b00c40082d49401000d083d00d10014407150706a400c00700806400c20081c20b440383c040504c144058000305800d403414a400000a00340740b0b60341d8951415080010101650803900301000005101d08031010411410072030340c400919044080039048503c00210740407404840d111400d001c01d20115013008484241e250340030800e1881c14010710012402e4400c0c5003176101d0030500d001800101800030b0344080101c0c2010501520141c03030304900003503e405043c002ca504100c1e5141a21281502030b500c08400d40c0c90040140380000c501c000325920070713032001c58112 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 627541735 1250 627540485 627540497
    0x4020d060b1003091e0c140a050a0807050a09050f06010c020f040908030a0c020102040506190507060c080618041205030a240611060c12040606270c0e010203162d03 72
    0x98017810a600e9000c1c40d50307000e0321441c81d01c1c0c40d05210100707041c1c9280751309a0007103164000040540e42c1001000080c0780d900c02510b01a854a001c11090b0305039031740702d070385980d0030002005a0079080f56100c030740c00039003401d0014070147c980c00411072108a004025403c80e141038400c00c1440020000f95101d4402c541042c00041180c040072400e1340907610440e90049802d00c200002c0b90409800340010010514046040409d5500c48100f505c0407004082c0210300c5850a201c4141040d03030f4000070a282a098040d680e0070107945600d4100d0008070440104400400464150b509503000302208510b19400c0600408114001c4031090503248640b0b008a80c0d1003101c608800b1003c20307807500c142504401c0301e003050f4032000c00740e811940052040716074603541d0b840421045c0750082d1001418450034560707075101c280d442e514000c45e94002002e0f402e03c5100150b02c142070f0b81c00000c940e0100b07646002c903a400c2149152220058080f003094000403600c42d945250400010407111301f955000790390702 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 627542985 1250 627541735 627541763
    0xe0a020406080c0120010b1c020a090207021c0203030c030703171b030109020306010c0f03120e0313030609301d130c17150f040b0904020d060b100309 66
    0xc5a4415041c0500ba000c548150035104102103045e8040b000d09406500120b802e015041c001000c4045104061581080210f034803000c1d4106038103900040c0035240d40031450031729075030001000601d450400c4032015001004110441d2400d0007510501603d15046a072906003a250241032030780c620328540c800f11b00303110025140400800800c2c0150420203403292440e42403401c000b010707500041419040c40405026030002802a0b042501500e000707681d015814204510360000340c0302c0024038180c00e0361040c44001c024480550b03c0604a0303030b00c40d400080004891500c10151b030918a0422400d490100c00c04080e075580c0c00010000721313030790740e26003100704a6920001d442c080b16054168208a920300c000f004180103500520341d070803550410780258184441c800c1002d42044401004088001802c003580d410901c0302e600090400721810b000d039510b81030215184860083c0046e10610741410740b1810300101d50b00000e05040007a01c54044415404800f074080c200001c01180d4058000e104 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 627544235 1250 627542985 627542999
    0xa1e1d010504080a0f02150f1807082503060203070809100504121b06110910020304120803270105042a0504050c04050a09090605070503010b0715020903010e0a020406 73
    0x203041c0b08541c0018003506000020500f00c440d00340121020080d8400c80d8800c40204000042282c401c503040300203180180b6181c0e000c0c0c0c501d5400da11805c00b503544003c6082c06103440110303d596810001e4400c1d01d0400b021176610040c00e9269900c094a00c510000600810940c0030303d041e880f451b03c400484803184407007602e000444104a8018020407400c00e04d0324007940c4646605001c2500e60b0303802c64107080c051b4991100b107900807010003103190000100e03040c0b1401c102d0350002c41c4820a0001e18105858200301801000c4110401845402c00000090b41541c0750808109011080d00c40c1c90284001700c010140281810b94095407000c024406101c03c7d05a8691b000151201204856040525050502c000303000c01500c0740c03141010038400894151141140340b40200505075012070808494207000045880181c0134a0405ca0b0800042c403201106808840c40c0380c0c7e02c0840a000c0081c12403001000b03020311200c146c0c0c99400c1051241c00c29500254114904d4001c80d41080b0099480d02 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 627545485 1250 627544235 627544241
    0xa030c0b0a08011d010b07230703050715051606060807030b06090f0c07020f1c05062406032a030103030c1103010e28140a060506061606050a1e1d01 65
    0x1d02a40d04c6402900107100380361894003e04241131003034207082d21600503185441c00b03102c0c98035104003d940c401e000401c144002040340740010010404210000c00710580c008011307126483d41043c022840511030400c100711a8001c0b00106022002c0e142c00a80300c0c03411000901003585d072648110b040401098421114122150091030290440e0789090056428451110b4812003950b03809117500d02c0165910b05080700300c059541c4a00027802c502d10380004644121030341e50380d041d0202c0c0030860132620b1a869003800c03170341c01c4403200104a8101f1800030002d480c8105904c0703082d4240300003000001c105034000e48451800c62240700208032025036001858222000801c4c00c08465100181560110940500c441c0c04001903034042c0c2c1804500d922107034054042900c10010f140d2110740f00e40e06200c464403400f904080100c50052401011044401d24038a010102034195640c62003c02c0c2d280149a0201d0050740c0154a881d5021441c01e081c00000c0c00309040c50301e03121303c01170320035801e012040c8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 627546735 1250 627545485 627545519
    0x5280318091b020d050406360b04080616020c0913051509011a1302070c09091b06020607090303031109030f01020408010f3c02030c09010905010c021e0a030c0b0a0801 73
    0xc0c2d44c01c0d644080121050b14506402c2c03231041044180502803072010360401c0c2e82c41c0d020300038140a031665185401d46091500c7c50080c551602050308401e5044001d5000c58840070202d0100d8010f03101c2d031904800210080a08440248a031181c0c40918858034142440c0c3c03442040c01034000c00a00d02c40c13080d00e1003640700c948480d950003001000345150701011035010b464454040e420b4035820fa911641100111385110100f9200b2201d40310700150407481850010b0041c0800d8409403805062082c4090301000d0f01d408000e05054a1b56074105401303101405030740740c1c0071000702281c0181580c031500d94000e50003401443c00c15400d00c684041a40014000c03940f440c451440b0312884044003003400c021003502009403614001d50500b181d8640714650019500503200303003000755911100e400001d40f400305183c0c4224140000c404100000d41d507003411056401f40d40d4003062059080100008061600903040100444000f0201095662619024000f03403480b80d12014400d0762298a80c40711b400d01301c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 627547985 1250 627546735 627546737
    0xf0a180509041104020307020c060d0204170f0c060901050702040c120c0e010527091509061203090f03010e0a061d070f03140304030b090a05280318091b020d050406 72
    0x10800703c42801d1030f6004540c00306951040e5034100c0034800000300183e1000100c8905150041004c5c031030303c00404021400743e02014014030b00d03091070000560b1110459051207204a502043e4001030341d00403000c48592640c010001c000f50f034074a010140002500400d20040c02d0724202d500e42c80940525034090108005840b41801c25190340940d9199010151442405a085005100380c544441042500414002402c0b1081d10091414442e11002c01800c442c4200c1290300400c100300c1d40801100c081080c2907800510822121011030301520400c00c040c5114495100340c08207100701a4080c580781d840d0340818410a408078201e00b0b0752001d05010f000308000c0d10000410004a008040071119507807842500c0c1001c0e42e946400e0b000840449540c0c01541050301c2135000c2000c2403041c100354050304001c40032101c2c0b103901d0001031011282401414002c07914414032a408118a43c0802414114018088041d224030342c588186c100c080540c015201d99560800b28900400684040c0c0c0ca607 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 627549235 1250 627547985 627548003
    0xc0e04050607032310090e060414010903080601120902130b09060904080f0318030d0204090c0f0815031c050702010f0503040b0c0a260601180e0105090c0f0a18050904 73
    0x10301c4211072000c4d400340209030b00f04200103000982401c0c0b0702503104100040c4000d041540f03442e0a061001c100652001003443e45807840184c0041d40144400f50448420320300b03400e4564ad20020b02005000c1c03018040d42c0503e02c032103580b28102031500125002042610000c03410740b41c54040c003501050503200281960414080416191310070000340d54001004011480031205600480741142d024500c1c0380d0aa9800040500c641d081d280039441550403e440d04201c40b29401070010600e4101401240040780300b601d1028542ea82000300c083c101145044407030044900d510007906130b40c0b02420480c0821000c004c07c8040c130f406030701540c0c0718903000b140007240c1c0d6582e0400040d2070342c041802001400000b600710f0441001e07100c5c00031304004045c40c2000441c00c2c0380002401c854202d008443c0324440141c1c0a200050028021504581c001d0ba8101502e0311060030000260282000004460601040e040d80e10740d48094850f02d24025403ca1304102501c62052000f0344808130341c09802d07071103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 627550485 1250 627549235 627549281
    0x920040b070807061506032d0f02120f09011107031d2106090c04092105160b0103210203070b040c082b020c0a09050a02070c0e0405060703 61
    0xc0000300045842802424504a041d40e0303a03404562140704540b183e060030000034041c1c40d400d8802c0701001102000542d40d500000c030f008805441015101c04000c6841f50f58610542001d2780545100e15400540c10300383d403400c00342943c08035500b1140c0300b0156080050309420300b44084110381c9000e4166681446c0c02907101040325582149a045030742101d1042640760011608031366801180144002422680c04c1c0703083d8040c03402c8040c98006200b24506071141000818025408582c010301320000c4071000607000069a40313014085d8034410707900b80101100e0030411184000c1d816a03210f22840b424542041406901101303401c3c1c141c0e000b50340200280008900443d92469101c0d104040040450f52070300021428940160880c0c14006915031134103440041c10a4130b003141501ba4802080e0078a0400000b4200c62481e01c108003c96503a4400300b0400c440035011a00000d0300541d00b903403096690703906004d05403400c4809480500501002c100300b90700c203004610482032420017480702c0c03030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 627551735 1250 627550485 627550499
    0x10302330a0c020f240f1306050c0d020f03070204050c090406080a061104030201080411150d060911030402010c0b090c030102071103010c080c03191d1510080304061202130e01092004 80
    0x9440701e45144a420b00900a007d070800d4403000c06409800c407035451907124406904214544001243d030314040d50081d9480c2c00d02401c001098510440c0c049901040355152614004c2d0340c1d103e1154842e80143c10443c4c08104180d001500b100041e01c2648100410350700076174211042d02885c08000d00082c043c00115010400142c003000003c1802400c140104000301c4c1c2917403540e8003005960040d0358407a00f007007105c850343d8424a070490704e180869034603620307040e40020801c0e94a600000d2034030881501044a0042c00c000519558401500840d61014941040446400e80c400311030701c250300307085694074924413130300b1024001e078403041c903040c00c50301e500c2609001000e5212007440140e917200208000074080d00e03c00a00c00c80010054182200d05020040100400510810002440020410280030004219401c071041441e25004c0d0a13000c512050113481b82c0002038044024075000880c01d5405025414100c400c40d610400a1910420414203590f01c03030304030030745011400e110801c02c02d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 627552985 1250 627551735 627551737
    0xa06060e01032304030801050a050a08120c0a0c1d01050324060312070b011a030c030f040305220e100305070e060d0510050402010314010302330a0c020f24 68
    0x101214010701c3e1003040c03c1c4529289a0325044070301303030001500300300100718904107038504001404090310640340761428281e9403580c81401032108031500a001807c02880c0c001071003e080c0c6c2d5a071245058021941c0c0d0941c200300c007000001e03c1d0440d10703449800001d00780b40000d420760f80840e2400e003025401c0c10046e8441071100c0b00410340c540600441d88011249840e010003440c1146c40352102c0301c01c55041002d4448905014000868881c82c2001805408403064040c0d0343d05c0365450881c40815511460221203502440c1101007061100309407080380b201203076031041c0c144e4004221044440c1d030f0300700748001074000d203100162503608428424000c000b0301d0b11415500510107007078160010f1150340d895180003a03c51a96010319074034018002150307414010940c0c140b00c414981d2007154107580006010b1480d90200500c0c0c1d504230021211800080741207c1060340c04028a16181c1d0012107000d03050b0021100220f210751041008000f092600003900c4c000284012404426070712421080011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 627554235 1250 627552985 627553001
    0xf0c0139030e030418060e07080a02090102030904110a1416080c0304080307050303040605010501080613231008070e160f030902040f06030b060409031b1109011202090a06060e0103 79
    0xc06480e003180042c5004100018801000701e0b4115070b211000c4c24000c00101c1d0f03140c0e080801144005018480002e40c0090069040041150010381d61030310707040145c4ca140f04031540290024100307510380c880b402011010b03180d103030302c10780b50f2500d49036111900312041e00c101002400901c03804608100400c003a900945030301955541102e01d03041c0c50b2418140356800c0800111041c9d84004100030410080340940303801440282807000480c01c3c804001307601e10f28801c89100b6919030b0340714160022180c4001c1d20b20303028204176003039480d4207112400144441090161881d24441e140001a0600b641c49200e03110325684600344910441803882210051032003c0710b00205034403641c40d080941c0d510f00c16940c1864030098001980e501d58580009071040c000c010390710480c60400a000841d8201915084486081219000c00e28031031030103240038030454080b41d42002174540042040109102070f0929103000301c0c2c90031803903620500c40700c06680d0640100000165140c0b41201954000c0e04a942 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 627555485 1250 627554235 627554237
    0x6010801052206050306160212030108030a08090309091609050102151501141306030b12070302060d060b0c030a0824010f110609060103030e0105121801090203030f0c0139 75
    0x1c1c4160f0313100b00092928200380ca40115400e000d16085003141d40401002503003100500c1380d1030442d07150040381c68890086034005c0301030100c42c2c4c0c001211100705008442045900400c5407040c3d040240100040314808803003038005c5034141350007103050b60000801502804980700310100b20794518802540d0106210001030500003450194240010b0103005040004500080780071032070b14008006003562120441640540c3d1004041800354002007010000d803501502c0b1103590b0350000c0280b100400041e4071080f490040802d44131121100400101048901036642c0ca007117071201d03c0813010181d61003070910185801030401510950150300240c840061a0410304004080064a5420000c08551100e03407034208000600c20144c0264428540050a10707005041410000c80c1100c05000a02009640f21680000d895425025008041540d03805001d407900c2e5004480540309640010081d600154200b0860107056801c0055000c10b900044002849888050401425003226032040e40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 627556735 1250 627555485 627555491
    0x80414030712030c02090f040530040902070204060618150201021606050603101517010b04020c0a0c0e0601050a0807021507090e090105130822031505060108010522 72
    0x5402c00141100c62a40d60280e11108500030081c410095003041c020300e002e0940010b08180400b1135030011328440a0f0450449910301e94802c1031050780000380c0255505003802e80000c0102d88004150040d2014070700c252024010f072a1550b0003a200d039200a04104015a15000108a602d08010080007080001e00005241c101c13100b404002c0301101100035150507071030320103009071810b040150200a249100b0108600041e449009504100700d101e02c5e40c00400104990b0701114083d03008281a5100400c115650313048000d185441e007207415010b43e104801d9030000202c2080301d05209115080503034442e403030400300c181d0075100480058684004c42c400d420007041c100e8a01c1e441d484c0207010584410549034500100300d0300b0180014480e07c0203905140c00d001c3c5c80440c80c80c43e65030040d0710034007603900c8690042840c0200c021108e02c4941d01d00003c00d00005108040d80e4541824107a19024400390b0384200064030003080030310406030499070200ca64000d00403914881d1b01c01010781c2c5408 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 627557985 1250 627556735 627556739
    0x204031208041b0b040302030606040e031b0328081501020303040b0c0d060605090301240e0402150d0b04060b0702090604021c1406031c05090103020f09030f0a030e0109030804140307 80
    0x40f0b0449000c1c2c221400d640000038080c800c0d07140420a0b50780c000340895007801000d800040b032580364007c800840d040802c10030383c1c0d0303e1840818005d441c10310141501008680e00c40300c800b035085140340300721b41020a1801001c540e0441040e6003900030303040181c0041d4610b4555542d0a115110010100c84071402c0521046d07002011030b01441000b0032803070342c0b039680b68070720b1808250861f5940c0c2c00d150345003040030780402c03965020b031120213044802140c0030a5081d69a800030800d507580aca03e0030080c10500142d5206005030b02ea01003014800d00f40c1d4100704032600c40c00090038611138213101a40c05845400017138080d103415002044410b52150651004600103c03861050b0b841d0307070141240715080c103401c11803a07003007c219400600715200044a004801980054058411010f00380e04240c2c00250005010340e09004481030014090111100030407042c00403501c1d10540c090440004060450078102e0b50310801c1c0b40800e4035040a0350902d01460f22501c5046922100b410680501a4480c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 627559235 1250 627557985 627558023
    0x2206170403270506220b04050306040b0402010e0d051b062b0b04020c030304150603080a0809071d100608060303042303011409100207120c030908030a0504090609020403120804 77
    0x160076942041c805c203070403041040200038102e0203e0f4211402118041c00100040d0340d00141d100e4015070009a40f00040d1a0382c0012a00154032842140d002400c1c03642c4a01040070009000003d0500361040c0381c81044000208500307480b88074000a070030242c441d0401d4084035851019007000000c56000a40341841101003030903a0065203403d40f2541000c4204010b02c561400440003980b040c80c2d0800115045035907103551406650038401c2004200e40024082e698200102009010000c03105c941c0d2100700c20241000c000d08540e074458103034651100050007401059018050b241c001c019604050810945203241c1d035081c5124107000c41c4004020116407000e200781d1282268020400d035191a11800c1b0030300d0081c034085040140380c8100300d82c0c400714050744a0b0300c602c10140e142c41c006144482c02c04440182c516004010240000251541c030030703402c1002081210400701003449081c0e9511841d600f203000307030710014040082c81c80d4803081d00b510540c5100d50103403261141c1420943c1c4500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 627560485 1250 627559235 627559237
    0x60b0d02040c031e020a08041709090414100b210106090c03020301030519020907120f0c08100503150c0304140f01092d0213022206170403270506 64
    0x15181c0d010030703901c1441c190000561480301c81d00c80d044c10800c0d882c1480074a8010b24104c0005c0014100c400b0700001c1c4518890040100c0703140b0100100040c0050400f81404070b02c14501000d040441d10600e183d00b00e00b00518007a8a10640340203210f8594900c80b44030002040c003024041020035580c40101003510641403044500102c41940c0068684d81140781541c5048400010741007008503045408005a944000c00c9a01899900e0100d0780c080140144c040900f4080c2d0f2402045800d1000c113010340b9501118043c859034008c100322010303079174860a150700c90400b80c2d88510350004407400564416445001076422501c039884226400220400301e07070410000380c84055150351100341c01003d03c9a80241804820401c4041d00501a0360300c40c604003500008000900600460072803002040c4258141d6000903008422400940e981e4007014454030040e01490020400c20903200460a40c58440d4910403945520382d800100f080175003000c8038010b01750804004952140c004284e07921054 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 627561735 1250 627560485 627560501
    0x150118090b1815090a0201090e09060106031104080a050a1b05130903020a1a270d0e01023c01020702060a180f030501021806090a06030203130605011508150d060b0d0204 74
    0x813010700045403051000401d24503ca0744102c480c40f4480c41440940d03200441e9a1741140e04030b0034006038045441c07460700c50740c0c00b80345e0050b201401160a03034001c0c4603000c40c020b0941b91040414020519454008000b50768040c0540c43d003141015480b034101003802c3c2c0c4034003802400303401240c1c00c088044c1d50b0140703200b115a403034010600c0e1b00c6092000302c6a07050301407442c0102204521001c40c0007400050b541e501c02c0c1040004100c2281040703007040c0d0081c004480d6484002241610441e04035201d0364418440481d440250001a600105062018030a40f070126a00914940c03421603070b414116540540c41070030b20b03502da0800302c00280034401ca0285100540c494400541c4032940d50101183c04140f1015007406a401001103107001d50301e4000c03200507076400d400c00503246e842d01c00c2c2020700e011002d00d00418107442e140002c1201ca00c0c03820f840000b19401c0c0d0350b00055a035030f5040d00e18440c2c0944016500300300d081c52084001803041c4c00c01b00c01e440d00908031503080034294000505030ba00314 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 627562985 1250 627561735 627561751
    0x7060e060106090810020405010806270c0918041a1f060f030b0907050405040c030e0109031e03020909060f1c0804090c09080d0e030708150118090b1815 67
    0x407a808002d00c103000c5c45044e41c000a2120b0840c102881c0c000081e240210051000b4407a04c405103d100500b001000000304591400c40c0565851401d0103d1420b20f5101c0340140c1e203d81642901c400010304a64103107803085510916000c1c0c5580c0c8660309810b50200079224124600ca00340000ca82d400c071044d0344c40001c0210390383d18aa006440d09029044803209545c00307006044403001c002e4125000012101207d03410f4900107180e03c21010210010041c115a40c201542410059024036a100a518140d40300d1994500c8070b0280307601050b4224414203000d9904045c2d840005543d0b46010340c83e550b04500c000c2c000341014400412801c19a03510b944040320a4500407030103001c800340921031003044603c2e5007040801c9500f000c2d60383c1e40d0b0745002d0b05500100b107500c018a074980c0e1014007101008003001f20032610320101500807014855003d000c1d103003800c0210782d05241c9085050041c0e0f062107400001d031200301e8550a400d0040c02104809000741031080c8040820f4419010a0140c030480c20 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 627564235 1250 627562985 627562997
    0x10c230106060905030a0b39041d07021c09030b241e1c0b0109060306110f19090b181008040b01090b010c0803070809010b0105130b07060e060106 64
    0x28414043c101d800d19400017402a407241e16200001100014140c0d0003103100d01c400c444240c040300c41780c09a09002c0f40d110381c040304082400b00a04c6009001381c0107a540311031280249840d00d01c80c403600028110340b2400160305c138017181c0340005803403955528510240c1c038042c0300e00740c2c803030301c4402049500303540086071404460308900441e420103801c00d1103207070112840025413402c030f88030828910100111900c513504c030344503600000e800400700d00000e60b07100c40303100c0c0b03550303940c00592006155a110070703240c0c1030424550100b041c00e03c134102c840f2030f546403000c1400d141c403046d4000f08800c0c1e0700700c0e11024001144000301e10340d1140d801401c1c0391044010300039030850005060103a2810300003080e0050000303d009100005200004241c199111840300007044488440100c44035807200001500040303000080c000f00e6a802003c092040c03221a009000c00d980d204c00444851240c032901102e09504050b00f03000c0e001401c401000c0c0c6034095407000c9900718404003000d0030142c4c01c2e0300020100301 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 627565485 1250 627564235 627564239
    0x30f0204060f14030106050a0305060301020909090307030801060e0907030c0201060504062c0f01170106030807210c020303040b0d060504020a0e09010608100e0604020c0604050c0a0e01030c05010c230106 89
    0x503003ca10540d11a90301d0140c2400c55160070800303010307800f8141461040c1919540010181d84095054901c816030091101d40f02d4202152001e40b2944403c100341c000030200c400206240b4010946080700301400782c0f00a4003070380c030381100b10014001d4096040442d5241d500001c0c042c0d89501600000d4000084445044004241e00f60040c0240100b08100b110141040140510000c06070030f04440d40380c40c4184000e4890b035844e90040241342c000400003000481c202007486011310058250684d80f441124620203104001e07140342c803641d40c0096044c1c1c401c01090050400450150040c8503c0790f00101d010350f103e800042c02ea0700010400340000c1c01020035602c1c0f82c0341883c03d00f8010b013500d04050206041202003c17080704907a01484040072115408522640c441c1e6045071415040d100c00d82c9c580382010718095072560940c04a06118141c072041c0071944000f0000c45504a80d403005006d0181072500006580580d900c43d42902e01c014003010381040c1c042c0403120030b41c5206000e000020014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 627566735 1250 627565485 627565487
    0xf09050109050c040f1a0d020607050105010b120c091f020106050a0b0d05060a14090705071515090b03031909050d1101022a011d030a08040e0604020a1d01030f0204060f 74
    0x200d0340d40004055a00781b021110b82e903034003030600d001c0d0b202058603a99a50741d07250000c00d25600c90044001c107150301e85000041c2e0364850303401500000849a0510740340361100041d180c094001c100e1601c3c0e20190141003143c0340c030a0704400c44064065400017041c02640c0301c001461a902c6680080b020500c00105020403590354850303298021801c0b10140d1109052000100ca84050981840d00803940d401c0880d403910300481c00e851070740350b0101c09a4600c00c0e0080c55500980401e54910603030030b0300c42401083c1081180544400058041d000f5400c1c845d0a800180080310894160000c1c40556400800c5039140e40b1480720100d409915042010034000c7c00080c5018460145e1000041d141132500c9480c80890344442441c02092030f0058041120300310807400b5204038842242c5c14440c1d0040079003000020701c007500c21203e60903141c01250355000c042c03000340d10a4500010004101b68680781888440007507548003410b041c540064400c07084030401c03040b03a0254105401045103001c11840301 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 627567985 1250 627566735 627566741
    0x702030d09030512030703020d0204090f0b030d05070209060d02030f1e07060f0e0a080d2c060a051806270d03020c120f070e06130b10030f09050109050c04 68
    0x1980c0385003841c4518599240c564071000c01c8a03046003046130020100381c000e4403940540d43c1110003210210364807680d0340c40000c02130512003555201d150424510100c140340219142100024540301c840c64407a10381c0c2081400440108115440140b0404e00e0700035072410016040b51500ba0401007560544501c04034548140025102c400d5a2001c4410710240d5407020050003850518180301a11810b840c0004800d83c030980c02c050742ca84189101e0b0712500e58441501d000c229146080703045420508907181c494980a00b22603500032004002400d00329106d03800400c80945060002c08100350782800142c0d0320360110060b1415000c1d00c012243c144507049840d002006070172600400c180320307541c3c0c000e0b40302c0c031005880c50312844144420900d011414404020704002c1c072030903075880d21380710098200003440560310180280d1055014451b80385652003541078002006200d10901c50001c00c044000d809550001c40c515920b0f9244003000070002d0052644552044004d00840c0030031b20148011 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 627569235 1250 627567985 627568003
    0x20f07081e25020f1f090e04020d0f02210105150603090a140f0102041d162109020907080a240b03040c0b03160905090105131a0a060302070203 63
    0x760700410010190b14501260185070001a10312070300c0e8034020140001303000b91080c803840c1600aa001e140c200c001360340744112940d00c08010f4585041054036044a0050300c40112002500031841c12b0468003c9010640641c80c618030041c000045c41003c2d00d1241400542c2c8050b0304800da440f00c051108150388250a88041c00081d15020304528102c014180e69002c0400090151031440c401c0000c080810b018090710780d0b074540029545c4a5986198a00d510104403520300c140c030101c00440c4071211915400b00c890310701c3c0d0365044d20380500c00b00850003c0901608517000359036a45003640058aa400c101c52255106859040540c6002d408483c10707070350014082000071f550b541080c40c1100301849888284c41a000220351650f03694545508007089a4100c004000e0010080000e107039001d410b807010070000c5543c0e24528035075442c1440348040d030a00805030310001c0c0c000e140c20320a03429400342d456201d044803280c00c44183c03400822000103254205200080e0001000425410f0070002444 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 627570485 1250 627569235 627569287
    0x14280905100f0e09070306090e061006050c0d0809100c030e01050a06152105010e100905073501060f0908061b030712060e0613050105030c010e04020f0708 68
    0x7101402d20070020b241c0014000c82d2071192000401280c2990322030b0b4009809032040d0300041240368200700e0240e60f542d84c01c64100c1381c4594622000309105102d201a684614485c0c001002c45041824058810400003071000580b40b0503954114413800781401025403000c039544001441e101451715950030740c2c1e402004803c8182c24030358200207000741a44003154105151829140ca0340c10301e00354061000e03085030b69401c0c0702d04001c004680e4038010b154060040d400a82c085000595401c6a8400c1d5042110344801142408054803400c12014111070042000f42c2c41001e140e0751803542085142800fa004000000d05100c11515095000910300d0050300c0704400510b59840c0806100f20045100f29070703007031085008008182d03158010551040d080b00341000c20b00a0b20f8898003158400807049444034442c000c04645800308198a1060038180c074005409031080045010041d1036503254642d04c25003080c0c0c01c20a034049001c00c0300150182c14820046076079901644064181030070f00501da40b42e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 627571735 1250 627570485 627570497
    0x712090303020714040b090a051e1510111c1101090c0b0702130204032607050601030318080f0a06110f0909060f04050a0b031c1428090510 61
    0xc0040307500040c072601203408800d5076285007044000840d0140c03c01c00d0406802c01c080b0828042a0311864100740d03c1001d604883d0360707400b1800c0030000d260b54000c0c0c403620f0032a45003c0c1c100803039044c080030b40d030034280c42800c0019124000e801c0da00e1520b001c0542d41d040385207101656404440d0301c9807080000b90780c544000c0c0804145501c0b80d06400304d040c40750188034480007030100115140c8020304500501401002c40d01da50303903414030300091014241400c04a02005011000c1280c0210070b41d0306180d00708009285d940e00390343d07050714440c0c400ca05404c3c000c500d040c00081d4051082100b0908110408060600d0b448203241c8102a2003048070030300c07543c410078003018102247c4201550464502203800b4681e0341c4640c00803d444164184203550054244410401d039801c4a40100d404503509070103c80140b40001c5c2d01f00340b01911049254001441814202e525040d1040070340301030034512208080200c240e4441940304c0c00d1640c010000300760031141c00c00c102d1604098410800015050034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 627572985 1250 627571735 627571739
    0x11071a0609090307022215090903080c07080d0e03090301022107030501150c020607082b050115110708060403021608061306020d141005041803020d08090a0b0c071209 73
    0x2030340c461b2982c04490080303403203403002001018a5030460010f0b0035019045943d800d0f2203a10340d03c00707400505400d4001c91068030104141d41d840400721001983c00c0055141000000241c410141c283c01c00b051100b40301c14480c51440c5d0358288001d1941d81110f50b0340703c40c0b0b1071907800c144901160080214084c1440c04d00104404168484051510101c510300410045168800980d442c00380c040007403c294800300d0300415802c01081400079020f10250703111054030055a0b040c06031802401030018800c500e2120703400f6240070f800d061112a80034820740300000e0315140d00c140303040400c42d07056005902010041c2d560541d000502406064030801603c80342c5007021207101c00801d801801400b42d43e001902810f050b006a200c0c40850352540200141c5091000c0c603504030390780c5800342900c182d203002010100f00f4400c11030024103075855000f43c950709070821415600444010031400c050701070079107100005000120000c1c03041c42020f842646468040c24405041c0c0380d0009401c040c0f069400301 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 627574235 1250 627572985 627572989
    0xa1707120b010614040902070b1522110c03070501090b0a050610200601151106040c140d0606090c0f0f020c0922050a060b0303070308010911071a060909030702 70
    0x15043d603403a401c001d2840003000d8a0540a403003164031104000f44013103014001c021700800c080e40500404450903c040124100300041012018a401886000d04103804c01d00411500000d04038101e1f44e1150381010082c21003941142c2c031443c03003142d00d070355a02402d00400c024880401d0f0080d800d44000c024601c1c0c10707000f083d032001c0d00ca0600020f00c01c2004140c40407001c600760114040c0a4007040d034195581d00c4403220f001d1810a50301601048078403003101c444a4001071801e114030742090328441c5403031070300000c4107200e0700c03a80005820002400358000411524010140180184400018201040d160080107564076050450400150850700212541c0c005641101d1070021212851720340c8440a0f5070541d1075460419560100d003080c484018400c01240078091503006039011300c0703c0da602408064480c45500002004104202e0050103d078401d0361101d241803001d004485d182c20480e03200c00e160382880308180c0815001c18010800c5506120b04065003014910004504100442d40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 627575485 1250 627574235 627574253
    0x2031b06061507150b041803080103031209050c060703050c3009030a020108060127090e010203010f0603020a020c15180a142b0b0420130b03010b0a170712 68
    0x12800e041300e45483d00603840e681d56610518102014080c04001e12006207800340552609100507004104a507002411440c2180252004181e000b8003400390720040d401044207e0b040001e040d0100402072080d000234203820803d900d6015409804908040c603034404054244007a26036004503800140645a85034038001075000c03d950b424242080e441c2d4030803004036061325075041080b454156039588141c11800d40240b20050b5803c500041c0304199080c103046090784020b204189410b03042c0e64041205078800d6024207004c1c0190320523101050390300300019400451801300e554000304d00251040031070350740f80004c811240782032380d00c141083d140400139008461840348036401500070300300003c5c14440000052942e12640c0318801d44000e41c90a0140d40b00300100d80450f035200c1800d010303510703204c01c07803001c2c0300003800c024120000e07001000c0d01e01e0090103404520b1500b42d0740325440410b181d513a0100040103405100d00c108045d01c01c04500178a071402640c0440c3c02c00310004003003008564885 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 627576735 1250 627575485 627575513
    0x4080c160b0a051b0105010b0c010b030a0f0b040602072f03010504030e010318020303030702011d0a02030d0f020f010c0f020d08010302181003140a06110a021b0102031b06061507 78
    0x3060542c1c40d44040c04c1c400e42001e1000c44000915484c0000110304001488042c01c4962541002042440703001001d00d40d5a030305a4502602c0c1c0070892500d100020301072202140e00c1407048002504140d01980ea11140c0b005d2a800c80c0d2a40c41c415105100035a04034010103020807044000380f0050615031400b4000c407502603403650415441b654045060a022100c18030341e40e038094201c0ea528903004030001c1c0240f0f010510403141d402c0b054800c1c0304071480000c9100b603140d0020301811400d06004801d0711540b201040a2095005070488003610360802e03c50058108409d03159441c2c00240b1010080c207045040a8010a00c810400140056250804413404c4201c1c003001c1c0146a49444085641c020074545c03000303003c074502d8141e0481d00340303001c0385418074684105400d001490f82059842141d0003050b081100507072101ca0710f400c01250490000b02c40c0d200600540f0300d040f01543c06000034051080314401c05600c03580900c6401e084c0590100510300501f080141048113640d41e4128142503d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 627577985 1250 627576735 627576737
    0x1109060111073b0c090a0b0309060106030605180106120f050403090608011a0f1813060503070608090d08100b0c030301080f0c0a0b07031b050f1005060d021903080304080c160b0a 78
    0x308500a01b51030300345410300074103154070150b42c491500c503c8559a98000340034400020342405d4000519060250700d0307030950041a0130302602e981c00c0000c200e0b0b01812500540301c209446140640e4203900c1d0340300d102d018900070b6607041206801c01d00b02030100a4107038001e410b00c00c628000300000b101c00c03034103403a01c000745028007554841045580c1100320541a6005030700650f840c004146a0001d98460400c4400079415540d0b07559545105644590080b1100f40140d000100503051303261144902a52100000140908041d12016018503a030880740c40300032a41e000100502c1313424410843c2c0c91803100810700034015901c44001203410b0700d40900c241c000250000c2111400c0500a0700b03200301c88030206008002004041c10403d503501c0890700c0c0c6009500503141e540d0700c02da00c1d6028480c1310360809428030b08802013923800d1040c0c800454140d6480c1100d00070001c000900603800550181d8002c0380c20715107030070000c20580d05105030155a91100402a1000c00c83c0384051416a0815102 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 627579235 1250 627577985 627577987
    0x90f1526160b092b0302010c0e0105041707030503030106030c11010e0c0d14010507120b180c0a0c1202030c06010e04031e0302160623041109060111073b0c 68
    0x10710020411200d8401d04140344400598138201051206801207040640258000d00078030502e101d00750b40c612901c1400394002a0100021310111a5440011200d021075000316241c0503544c4d101c031401c68000380c020f9000244c86001d900440e5510051222000c02d103080204011211203005690740c011280c0518007901401d1411001e0041c0744c419481e00130807640081c0b0283c0380500c0001c181001c1c210007170003054a000c1c040f00b424100203070700e1007100101d526040c449481c4c141090311290003020501c0100402c4a040300000344a40500b407007150450740080d91981e80c0e641141d810302c04147c102904090072001003001203684900c42c440c4206903c004d19141030001c2030100d001e4840e081034407120466214016082001346d901c039425408200c0a42c0090780c03042541804c004509036800307496202c9038001c1580c28a081940e59030440c4050404040c03016119886034200740c5958041d00d08200441c0d014020b4071b6011940603c0d048603001048006000d600840e00c4d16540907040141c5103c0c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 627580485 1250 627579235 627579247
    0x703150f050343090f1a0114130e04050c012d17090a060507030b0d06111b010509120c03190e040e01050118060807090f1526160b 57
    0x5400b002816184441c5080003a5141c40031400712203509a03125000e1407501c0c201403084188064400c90f12a004110381598001c032201c00112410314800d515030f88c406004010498602034824007240040c00002544031003032a10b810040e00b05608101c0440c1400982240c176240e00c030041c054041c2030343d0300204c0f003070418002c0c6104480069070140c10f0301d141c00d84841404803035140002c039100003a20802044c0700e0f42d43c40110842c26941010002600481030000d03c400060300d58202c0a007107255880c0c00360900650410a401c2c2c0c41016a010203103035540c80c14410003180902c00060403984007240586400e00c090307140c03a602c2c4103941c5103ea9424005501c40301062044421815080d0018418000d0344490b2154138001c00082c0304603100c05120203603055580d1114002c6400b1110040c3c0a08816031a280140000d441e01c0c0c40c1482600d6502c03201d0780320003e028100742d0043c10a003106402e60122100e0b0302d00703841e50411500e9885a001621404210307e0b05e40c034900a4038103150383e282e1240 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 627581735 1250 627580485 627580543
    0x50d0803010314190305030603010509120f07081603050a020f07030b04120c20030c1915020c0d0807020310140106030f0b060408010e160803300703150f0503 69
    0x144e400c2d40c5540308080503034204000d159000010714004c80049000704400c0c1c603a42442591404c00c0008480d140d001882090407000268014201c1180541c4a4500c1c0400010040c0d58500c04454100c0220b24049a8400043c0e41000981d1100007400000c1c480e01d425500d8a20340c008004000a007c52040151005054841c4c1e210f13804080d804000b03103803d0015540c5074406405038a411600900c41c90041400c1482c15400801c131049015800c031000c1410720340c06e0500c410f00354507444154030544041c01c119481c1d1005241e1824001c0a031582c45813800c0c810982801703103441c54001110f08007071200c0c2d60000344102541c1140c01300c0c140011240101c1403002c014001c422300013988004089030028501e030041d0400482c0c1d00c071407410303140c61038941c81a07201480d9140c0550159a8402d0085010b075001e610f1003000c0004240c2c0400818500c2d81c0ba400e246900103c40e11000261607a5500c16420035103c080400761800298081001d8181000b081e512000c00c40d103507011000208403c43c0003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 627582985 1250 627581735 627581743
    0x1030f030309121e2109020a0b0706061a03040c09020c010906050f010303030612080d05061c03020706020d02030913020d180809090a050106270b1210050d0803010314 73
    0x3983c015080c0400e5840000081c005820360152094407641d420000d0108030f10650066020803424030b0410003001d801d503583c0d130017041c65160480c2c00421903840880c80c1d524100c0a000e0040c807d034004513280c2d090807460124484030040010050b81d003801030100003040703898490180c0305540c0005032500700f40703518140581405540074001c54600018807a50014007407000d4180c90080e242801507d42c0c03042c0035858040c1e811400740020a0912442001000e150800f0303801c2000141008000b0803001001c001811608030100c026a1101c402000400e8040c13041c60108155030007e141020490408905402c1c00780d20400125503000941c0b0a003901c496101011243c0300c2243c40f80001d40300c0c81c000b107445d0b00c402005886940c04c0e100103149035415000d0a4142ea22641c0c1c0c000a119010904aa951031030110103010b20311234400100d40d05400d40c000d014405030304e1500e1030050805145142e050403054000d58003915001e1502000b0603040011241140c0d030001901054001c416502410 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 627584235 1250 627582985 627583001
    0x203090112061203030209030c0108011805060a0b0f0c010b010906050a1b1b140a0308090d03030b0405100512010e07170c040213140301060302090106030c09090c18140901030f0303 79
    0xf110060b81000c805056140d409028012826401c54122030800340064490160034070503070001907008207244440d1031043d04501c1e00b058000d40365010741d41d169440720305035400c10b48142111f0040420703d0010000d0900034209055002c5c01c20301d04150800d04020704a01c00c080060702401030a06900d203d14280703140c84010a5005a50050707034101c0e0100480030300140b803107400d45c486e1103003520452502c2c05c07142d88e0089913030041845141030045410f0100d03100610406406240d0344402000c00c0c0e03240c40c00f543d48038140c1c1c044000301e40c80c20b00b400c024941445403071580450f854240e080e036941d0000142c49050f600e02815541c10002c480b010a0720b0308004a4440303820500110b40c81301034074014007030344040d43c108160006c013000d410400c2c14200c841d00e2002951200e03d850040050b940203a1051003240090328016101d03d448020a20640f0f2008000380002600c3c51809011040f1240645000c1c0c1035103003840b81da9540c0c003030001d1003000c410f00000d8448a4044c041100f098001d07880804 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 627585485 1250 627584235 627584249
    0x8070c0c030c0b2107020d1d0a0f0503010e150a09082808010506120105040b06070c1205060f0103030f0503060a0e090c040c0c0b13170705060a0f050403020309011206 73
    0x9001030303c4040d0b20078290005401e841d95280091030580b5030381c03090407482d44142801d60050007240e04c095800c4641c88044c05000f0701d500d901340302042841e100c9804610150000c10703500d50205103481c05040c05c44003101f854400c15048041501510340b04c486c0020340029070701c0e10201d1005080d0402100700d01c240c5c401d5241c00c16514107d100d189034200010050742599840e400c2c0c141c0c1c0da59081c41300c14800c1e0721111072440305410040c0482d15055000e5400e941000c0d001500300811603039900d0b402c42e5150403004021082c04032450400000700721032039201e00000c0584116501d184e45c0500b515155000e0031f001e102c4040006120b58681949102c0144600078040d82d01e4208001040e80701d81d481350600340103030b0500e4200140702d40034818a680099100001101d00c0c0d036a0001020840d0403100200e400398032034416091100380344406400580c0c0035074094221800c0081d141402c4928800100178018101402c00010903000302c20364000c6442804d2228000c11500d01460042c00c0c1900802 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 627586735 1250 627585485 627585503
    0xb0f09090a110d0905010c050f07060c02010608010905150105010905030a120c0c0e0702100509100504060207050d0504090b040c05070b1503010c0e01180f05060703050d050f0402030105150108070c0c03 88
    0x83c0f40b02c01ea030014505540610000c01044c2c540100844080c401e40c610b03d05e428004020810005400d42c0c405440d0501d548000600c09482e244800d00307450a440e01650a5803051040513556882010f60600400007420a000141e1078600800d413039516500016010158078503441c40a24040c491001c4251340c07000d01c0e284001c1c2c6030030528281e420f007603034040c00601c2038030700509607094248076050042102200400c00c08514201000c054000140100c44030b80d000c1c07013400c0008004000d801554901e6441da6601c842c00e2550160846110441c0b0350b1046040c0000c40c0390303940e0041c0840e0403c60f08801e180026a482c2030400e0024016082c11a40540ca045202c030036860b030024100d5158a4242e840d0030503244d01e46540b448041c01401246400000d00074208030714540303580140303042480381c200301c0d04000140c2d10100440c0c0048440c101c140c615042080114582845003585c0001403070741c00c003511170b10640001d2120340014680000c0c070400c85000c100380401c02c0c400300300440e03000200b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 627587985 1250 627586735 627586747
    0x19091a031c0e061b010f111b070b0309031c060b03150d0f110f010c020f1c0b071d040c020c0f0d080c0d0806010903050d050703090504150602070b0f09090a11 69
    0x7991205240d441001c80300d510f40151a4610348450054200034482041260b0800b818100011004074056000400c1d911603584008ad9440c6000302540c03040d0010405503480c0d1a20304420f6010348201d8492a8844e0300d054001d01030b2172030840c1a240c102c1c001844111488a008010a2003903011000c0034118410b0b0000d90010014050130320340800c0344c240c41111507541c50100640e07041d00e00e140001d40c0003500036042e202c1c5041c100003628050880300c103c00d800c9005d6803150000040243c032880c0000300c070f41070192010488407241400300041034804008405a4000084d112049411014402c0706001c1012044d03941e0b9174550f04807680c120034400c1c2e964140d00061641d4880c0c00300040041041900059100e6000d1501d00bc21030f508900030780300030000d507072003218560320504040f0288410048040381948552003004901240032102104050078804080c0c501000d03a80310f4001200c0800201000d41719003c113641501109540038451620b5200902c3d0150064440140c080e4202060b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 627589235 1250 627587985 627588007
    0x30301083c0106060210090c090525180b0a052205131e0e030d09060f0c050703030f0e281b14150307110a0219091a031c0e06 55
    0x206504a914070380846d2884048889084142c407402c11015200d220082020081002c139504140e41c40012001c400c14200180d0a001c01d482c2440c0701140300040c10601c01e801c1e01a042c416840203001c1c80501e044c100310a5160090481c8540d0284101d24070600300c00c0781c4030b03079010b000c0c8001a05008080c1103151500901201c0240041050054140e00c1d0b0240711640705918424206006c8158001d1441c02111810781c0d00902a0341e00c0c12582c0d10f40c1c039581003600441512072000703c10320070760f00e6550b1200203040003410f6401e0310490320196480c2550a0384105400560b80015004401c1b0800501c1d090340350202100d030516201400c0e4007800350345000004101842001511341d1420b030710105c0c1101005001c03502022544d4400340e0002040804d514a00a00b140341601d6030301c2040382c0d24011103a01140360060004840c130404206100c060008103881d00942c0d00c120722101c0d07480240703541c80c4000b0780d65516000f0101201805980d004550714810034418002c003d01400301d40c0d4850460310 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 627590485 1250 627589235 627589241
    0x32406020322081c050702030307120f030501140d0206041a040f06020309060304140a0c0311120a020d03110f06010b121609030803100e0f010611030301083c01 70
    0xc035140061181c0c82e800a0740800d20356298140c901c1000148520b1610080b0100c9000c103d1003440d080c00418030140c0c0069404000070040603200b0210008407050125001d850340e404403811805041c100001440f0300d43c0280405211580c048030011510015030011030064880c07500001407844034920100b8480220600a1084034108140c0c40d81c4541d4450302242c8a01906c0c1c50301b9800036081004c24040b4502800c4c0b1000440f01d42c00b07035001c1c40079a64814960b5203055100301c45002042c068842c2c0f610b401d41c0140c01c01d82455025010500c00c41c1c7c00500003604d4140d00a0900001410007805514108083e404480c180c4085039060758640801d40250b40040d08440c020060340070000c0e4849003255018215890207440740e251060842e40da00c0030940008040244203080c60030001a01c0c0d0310100341c01c0c0640c680789078180040d4144080181081404a098000c42c1d00400040200ca00000340341c1002040040440c421880b03c4a00340c2d44400c807400080e007601e4040002075092001c10347c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 627591735 1250 627590485 627590497
    0x51806031203280b0a0e0708070804140312101a071407050901060c05101e09060b0301020d022d0a110a0209072c13050a0b1f030f11040302010324060203 67
    0x301d541404d590394003200c3c1b00c02e031011035403040055005404500c009015000450f0424407480c44200d642d0b100da82020715682101010500302801e02051010f08180122b51001800102016883c4014034015100b00c40c0305507a002841c4048818000d4408c141c00d20160707001c2d180c02043d1818650359448005c203c1d43d90000240c825014180064001c8403007407240700649102901d00c52200340c0410172040050109107020f5500ca600e0380042e004995081c4010f02c0082659000180c85d032400310043d4088410104810800719030101c6000f4890044d03006990240a0780d2401d68440000b0940751420035400050080d0040706c5502800b14043c0c101030401c240c00b0303000304120080f0000006236070009401c00f4002d5004001e560711480340d80c440d44c10003a8044070850010400c0d580d0341c80800d682032182c0f188100c01107004030040ca02d039581070140209000e00b805080c4a41025a03d8a000f140304c1c0d0b01c00281416940c0006130400c40010703052602000e1201c0804480c280d90b140065100c1e8088 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 627592985 1250 627591735 627591739
    0x3150301110a020d08040309060c020117011217070803010b0f04052d010305041523131205070201050322140d0201060807080307060203090a060204060306051806031203280b 76
    0x204d85144680d511810300e032071003140c0543d1189452803070000c066501148400e41681048140003040000c890a10042402441005500035650050382850810208220113012070170b02e0401070303200445c00b0a800c0e2410341d44145142a5110300c0c00090401c02d10850303020503000002c0c0000d5180f618402d80307031799021080c610400304402c11048011411100216030003000d01c081940940d081e400b950b486055000c1543c12103504a80305003145078508036040f0b606c5052107503000f00c200200494440002021500e41c105507080000c40e0340003030000c0c04002c1c80080d00d60002c603002c0c1c0511001049542545800005c8070103003c0541c0112525840c00c980b2404c0558200000041c0e44900062004100c41c0000003850030003a4a903207903c080d51014000032128465007041801007082440104000c00b5103440014000d450801480788400e40001c0c0c8010843e00a020002142c0b008240e0341c0807803061a050641c0c940d80c4986030740743c64010200070310310b00602121031545a4600e50080c030b00c41c002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 627594235 1250 627592985 627592993
    0x30c0801050a0f02030702070902090402250515010e16090302060304060b0306220809010212030a0204030c06030c0f030b150d06030606091b14040504052505190503150301110a02 78
    0x181800c003c040c1d12007910034400603031160380c0030420725200d41d020300726041008002600d0070032030010802d818180005525040181c19070032004100040150f12242a08109a50407a40c54000301c500b544800410401c2d000008610424095200d40c8031a0017a5500030300c4542c49080c603040010050400c00102c41c024480d140200f0500700c2c1940804003d10005585080c000456135a1340700345800c141c01e03081c154828120b14804020154000d10300c030341c0610000507259071542c01c00d4510b0056503401002454034240301c1d601d0303840e40b04034401d086450032b0401084030202080811110009200c2c508070a80d80801c0c0e00000701c0c41034124a003140c0c0203c4041c000c1c5900c03011000100c40c4075074410b0200b0480203c1c02c001c450b0046280c00385038007003221441e01b0113035240c010030180c0d04200c2c2d000d04607529900130306552200590391540c2401940c1f81041c00c00b01c141e074000f450031103174103d01c8003484000b20001d16002940d07903c24030021405002400003030b0401c01c4050700b0b40c0004c40c0c1c0d4009402 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 627595485 1250 627594235 627594251
    0x160f0e1f0503151507140a08120915132a0602030d05090714090a060302040207141c09090209120d0305041205120c0f0d05010f060e0a080c040213030c0801050a 70
    0x10b48464040d1210641300e504034030f042640d9481e038005030080000301e03400340552410403010a50407005010100010340b4105424a041e4251600b084140007450030200009800c0c0700800078a85017540e2050360010a040312940c0382c205800300052140590044640841c1001c540d003640440074041e40f110710001440745480e9880001e8403513615000c0c8a9440082052036000c900e002c8282942217034034000c0004a2a80341e80215080e42e201600c151241407800c560035417162010806a00502c20f20703205850480c0384103000602c0424644507246440b6000b08081ca690350f50000c80c180f407030140c0001c4818400501001402034030040398107907120300e5000d0030400901c0c000d00813580c091000716010085580c4002406d40710b600302c8a2600c0c2035400500c04400311000300d1060b41d0290162310003203c14245070880080401c440401a40c1c06540d08040401c41c001000900c0383c40e11341e08482c0540c58a10307201100b511300415034030290081d07100d00d000050908040d403240c0d0146503c5042801101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 627596735 1250 627595485 627595489
    0x1110a1b090209061608040e07031406030a02010c12170f0103030e1c260d0603060506030a05060103024c09030b06131104030614160f0e1f050315 64
    0x4020f000c1d001da0429410010090512000d803621040a8451101c0c1400c0c1900d4009000848608513040c0010036619907030014010301103012154008400c074000e2a4003400c42c0e000820720f5910f480020900e400c0c007090740704400c0c0104c010b84469001c081c41c0884914142c207104950400c01e01c019400701d11410700e8203441d81450304117100e031408820001316080000d0b5854000316004020f01580c90b5203142c68101400d851100181022041c480010a100d030071810f041045582c00340045109034030801c0c606000503008186c2d9811079404031045401b000070b0780d26940084400020440b203851091060800c3c00100c0b00c5088195800c0d1234811a6000d4840d00030b407940c42c0c0a000180c551580a0000b4070326182c0700300030049111303107140003080048030840b002203d40c00030380040320031544400c8030b80b11043c0782c0b60000b90701100004401c03184503c01d12001d015440308c842c3c5141003001000c41d81c42540c880307140c03000e02c6559241c1444015200810020103a0b08140e9800440c00c2d2400308507880382c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 627597985 1250 627596735 627596737
    0xc01030e3d0606020a080a021204230301150b1e031312050a052d13060206150f010f020f0a0f050d480f151b0c0201110a1b0902 56
    0x781d1004e400034103e101464a445a960300004152003c44c40740341a00c040707001545000e800107107050381005d01441003114800105d2503044800d20f02982c50500710b180d10b8840c42c2500c03030480e189840c10319611452401e40210001c1d102d2142c3c642c0c220000180103820042108440d00702e40580201c0d0b05021031414112614030031005500c0c00241d061059000c502c2c20391a410609140110250305d65503c540400d100c90340040c09003010803000000704011680e010b00411768482940520a0031162020001030680d0b080e0741c08943c1001075800b50141d00714004c015101286960404848404155140440010036003010803a4980501003c501c4142d001d070b0b030703030000d284407804056001003403080305810401c2d0b101d18990444200e003200c04880a41140e0568502805039095004100c50750405141d0b141d0140400b2925910f80803100c000850480103200f403d00451410500100d6140012039202824410504c1c00d8000c030000c10301040034242200c40c3c008000f500c0454a199511081012 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 627599235 1250 627597985 627597989
    0x30f0b0903070807062c01051e061005030601051b2b0801032409060b010206100b0301060c14010c0818070602190c0f080c0102010605040e0c01030e3d06 67
    0x1048018402076000600503009210031800080d030a2646d0788800c42d401003980c8107480790400a941d12800d0050900070000842902c40c41002e0030007482c10a040070916020100e000841000340200119515078800d1007242d000303e08012020403450703c1c01101b16203c2c660820656244005410440d03482c0c3d070340070040040c013840e43d182c1c0405031303185484e24807401c8010140ea008030b402110354030141409910482036a28092100000c158101100180c80d1a1019103800300803c110780003001049030fa40b049a0547c1c03541c0c070300703510b514609141c030740a84180c18529001070b5090481c6d02e220150b200c8140d0348202c50003408654490b15201e009601c802c01400b82100680140040c50800d0030b42c640c0503524203100e03003510b032551590b44040707600c9401507802000e10f0303402c0441081600d43c1c1c24060324001e020121802c00031540b09020003a0b81d045003c0f41d4905141d107503030b03020194583c10300c0002c0b43c410055124002c2d125490b22000880300700480001003400e41c524400461003110310070541 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 627600485 1250 627599235 627599243
    0xc04140403080f06040b130f1a030d030c03060b0a0f03060b0c121b06010f06180b0d0e01091205070204061508062101090b062d1504050604030f0b090307 67
    0x4407500e42c85403616007168020800ca4105031a00c2d020711b0342e9100c82440c5070f8180d2046d0070000300c208400201d0300607140205515842085403c00400180ea40030405414410b010b040004104403110015800740102e54808040c02e18080f480f203410350f412400900c40322403a558100590b54484031000704034000c02c05803c034140d01100c0f240d5040da41110003001c080300000b00f08a00080c0c826401c0b45000001d0700860150035508000300706958000115902800e150154405000d042c00c030340c05907e000e1050f86010311512022190414642903000810880d044088a01d40307549003500680164003403103041780103600d030180c00502c903403505007106d001d04c0d0142e40306952600c40f802000140544001c103100390011030301401805040034855501070034868a160000d03880c245081001207c0c0780f0741000c0891941c1051032959902d8890705050380c440031260900540c5e4040703405601c50241b50030650b084040080c0206c2889110386005240f039124601b00c00d05680c900003150345034060254010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 627601735 1250 627600485 627600497
    0x606031a010b040b0a180308040e090105060105090904081605060123060a0e01090b04240c020a1e2d06021203190f1805100e1509150403020c04140403 66
    0x1000f640610710060014080ca864004080c0b0fa110905243c606c0c00c84d4070840350404001010000c690f00d1203020390b40700c00c1c0203008101c2c510740503001a03c00d1007142552841001c0e00c0b8009410014407000341d0300012810801000d4040b40e615050703944010038015030044014140e40f401c072694002c40600c0d41c12002500c401c0c10460842010340d22030491511007070621200400c0480c00b0303c1e058000d00f000f000700140388c0c102c0004100c001d00c03903603c400c912001000111f41d40503015840b60050081107070028845c2d6481851320207640c0c40c64408540142c1c10180500c2d007025080c8580c5420b5441030b0b140b5070b080ea4078243d50713600d00b83c0c0d403002e01d1031041d0b0140c5014400a000c580d003002011098424440c008900451105551320440700060042804918a10303107800034850200807241c09401c030140704100c1768601f00b03404c0381e54030640b5141d03c1d801000c500000701601c0080c8a41c85100340501d07440700c114103107031401a40b143c420340d402c940264a03085210060600c40d034070035400b541d0161141 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 627602985 1250 627601735 627601739
    0xe06130f060506040b18160e0d0b06011b0c140d030206010b0a0311031f0b1804050a0921030c0302090a03030e040b130926120718030606031a010b04 65
    0x1d4040e0000518040d4070907034505643c071789034540780268580a1400d503400d00c540e16003640c0022850030200011020440030b49903010305500c4c0e021850300642c1e007050300c1c0d90f2190785001c012183c85039003840245101d060700350202c00b001a090707503080a491803022545100440382050140e09001d1080107001030303015000410030310b01401c00a00381c1780c11070324020036016481c40407004580c0c0240c400c14051031506400e081410700c07101c0c2a00107011044170091614904404440d10041c020301c0143c45595030350b000c9010900c180d03100d1341590b9444000714018601e00c10900740010586103640c2c021a05100840c0c4016101c3e1084030503140004114042c01030031510b0451310100c00082d070036081940c404200c2c09940d58107415080492200380045810761181c6420044140000c080c3c555002d00034030315420801480003038a6203403498a01c140c400f03658507101150013520701d00040310040010304001c01444400d802940c00e99002d02c40400040040c06a40b18a5174424400d8201212040c003003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 627604235 1250 627602985 627602993
    0x13050a05030d1704051c0906030e0a02130b0105040801050c0a110a03021203041b080303070905190b2803051e040309050120010e010f0b0d080306060a110607030e06130f 74
    0x90744c04c24080c10444209080b00301007002e0f011000900710001c2406000d0070050558580510403000700e10f607011f4061401e4035030120b0031300904007411144860311180703400c0352139200c0e0041c0c43c01018040000d0102c1d003000c200a400b182d108281d40c1e40002d4001404101062000a06185495044d40201205e81c88050150795981020340201c4001149815441040d00d01c11911405000c201c00915620305000310098110304981c0c3c401030040d8945880c4000b0782d5140d10b840001c80b203a868100d80e45042d4045140b03900700c1c1c10f0340e80c0c81d035040003040b404403800d82c554080d503c1414003031403000342002c0780105501d441c5421a00140001d90242051015510480100780702d41101002e0940d00054140042d0942c1c40189081c0702c96036440b28002c0184503240103030b00c984c080030b4504252410703031510340c44040c1c840200401d000d488009040301000d445500c0840760311040f20191082414004401006805040c1125885205040206010049803030307519041c2c0340d014845188003051591 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 627605485 1250 627604235 627604277
    0x80405030f1c0203070e1c08090409030e0910061209050303070f09050406030b0412090605030c0c0705040c170f070516020d0b070c1a101809060213050a05030d 70
    0x900c94100e080181d400003032202d00c1e8006180180c269840e400300c0c254a44040c0a4a038040d0680c040742d58030040034000129604800700c512030b90041c4d034042040c06403030a054414042954885070410407a004104038520329044c4042654442d95544525410f001a42c405a4040020140070350b082000400c04040c002c54281d0400c0b9800e0900e000b1596071040002e04482040c0c1c02a01d40100500800c41088000f40080d1447c15081c1010303920b10b41040001442c90100422061107c10300003092040c0700c50401001000b42401041800760400502c001840c000d424034030310300d103034486501007215200e040c0034003849401542c0d14030b8141040710400900002d4109001c0e40c000d80b4403007001000c00d41143d00303d4480c0916440c1c00814484c00d16182d4040041d03080d50341088500001840b02d03007141421130034121058400483c5e050304225015400800803a0001059a407001400e0030400c0000703140401110b4048440c4442d10760b0326018103448030749000300c850004003045040000103515036 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 627606735 1250 627605485 627605497
    0x10c05040b0a0c021f0f030b040e061306060e10080f1f0b0a09061508150102070306020a1107030326010315020f0f0703050d1a030a03120f06180c080405030f 69
    0xc1c000b24105058266907001440700a0f030706800a5110a040d207506e41c3c15002c0c111040f0001c1c2c0341084116440c8000c0740c0c0351030000d030038161480714809086003400080d812500190800d41c038030b5180c605103660441d84150081c40b80c15001d0213503200310418034001140c04208a8610190949600c0e40c0d00c6104005041500d07440354012200b0350041101c00f484c0c401c0308050440525041002801100003820041c4003e0900045151f41081d031903050740c1c0801e6100c01c0f20352164001d610b0303110741301055a1482810310207050600c28000d00205044c2c0c410710750340148066015510301c21860140b0404405003d010243c4041c608070f40b07041c41c40d01c3d40c2d8018609002001402800c200d134000074109140d0041c0c000b540000c10114410007081e80c01d1113503030521a0700f415040c114150360b8001c02e4482120300000b400b44200810302c20f8052002c0d13008810481c194110400203541c0300c1ca03101c6103181d480b0b13000c455040e151140c2c8041d21401841c0483c003d5170007000450408550440403aa00e500c14 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 627607985 1250 627606735 627606739
    0x80411091501030b010c050f0a020405010e1902090402160c05120f03070f03020313030303050a0f06050f04050a0b06040807080115050a0e090c060c0f0c0907120905031b0f010c05040b0a0c02 83
    0x6d982800c000c15014050304602141100c003a1121800c540100030580b00c0607006403100118003018010ba009000d1407a1a09400e500005600c8461900006000f80103071981c0d0300b05145078041e6201040410162603085d43c1c400c9520b100003400180229503503801400050f03401c0c0c0c1c4100800340200310200203940941c1e2103441201c4c038299100000d5602a0400d07481280030907107c00600c0b8005100b4003581d0004008004200810391400000400c10040107503428000ca5440b0003080080e425034005400b41c00028100603a140da403440020340d510101c1c0b14140a079407805520000c2c43c002c44608004488000302500030382810501c0c14154020080e1101031a4400c65110710b0302ea44502d4050700c4c641510b0005401010704050243c0e08001000c0c4c111441856074908102040d908803040301501ca1102200081c1c0301282c0c600a4910301c1884008203509102410f1208420380c0082c0c940e00c03040c10031000f130003504107401041e1000c0c05a4018030710182800d12990380d6a80c49203001420440c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 627609235 1250 627607985 627607997
    0x2090405150f1005240f1e070c0e0a15150207090603030f0809150106170702060c0d0e03070b0c0a091202010c12051905040f0605031e07140a080411091501030b01 71
    0x24581c41300c5c459800b0444017080d007076000c907001c000124010a144d404002d9410020300e4103803d903485010075152401604403000c02c0001107444101c0e48d41c817110201c0c11113260b44070441c0e2125100c2e074100c114811224010703c21382202080c0310b01f0718002c050440c4d41c0340d01d4400d01d2021206041d00d903400c00408103017180c0310704509189a140d02c05140c50027440241c8032900c0e12600d4020012448200520440565006c50b051050182885c01118051014648000351055001ca091411071107440c4001e000010030106028581806400619403101242c8401540e41d546000c1040482d229000282c0030441801381000800c00c006d0a0342820140c0b46003641c43c207000c2550002c00c039101e5201520004030085001d210841d020160000a00602e092190540c078001c1d490021101c8040004603030138030034401140c40d80f802081c2100d030301c880300300e645620758040f0500100303034a5007294103450000458440300f00710304000c807500d4080e545080c411500070406000550280c000507a03102c2c10016 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 627610485 1250 627609235 627609289
    0x908030a0b1f050702100f021e100911030f0a0f0f020d0b10030308010f030507031e0f08070b0a0c0e01141e09130b01021b0d02090405150f1005 63
    0x180190100702c2901521025100d81d114010300c01c0d05821800300c0014408205d001000b100d8001034040204404140d851003a1522511540c1c14076a183d191690300c1402d000130341c801c000754000040c0d08000b096086450098400b8900c5581c0c03540c082010348521349000c03080000c590065100c2c0603041c0080c00300e0101e801241c2d1104181038046401a520219802c1d0510815500401303940c01009003008000c0070500356100c0c0c50700c80107940b1008150074900805165580302c04010482096084840207031200168240340c0f0007544003420032680e201000001039004030040c0701c0c0d0b07509410f065407816800d061180043d1900e114210120710346032010701460507680b0100e1486401d07051685d60700c5851700382c000c0c184202d280030307a201c0710310b0300e801c10034441000c0e607001984d02a160152030030f050a031585e00700882c6800b5400240039402080d64410003060000c001100940360712900c0443c0001da0307503519203442d184804d4529100340c26141e00d0821075407030031020003000c40741d01454691a1807 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 627611735 1250 627610485 627610519
    0xc0210110a02090712060824090118050f0c0919021b0d030e0f03030c030408030703060302100512060a05100f02010f0608071505030f01170c19090605040908030a0b 72
    0x402c440c281d00240030461403003240151402810020001c0d0f000405d00c0a01400711407443c51240c0c8d01e20911203000b034000494181c1d0035080408260f0701c402050b0803000b524100340d511440c8918040c0083d00c034118940c0c10b41e042441c052480b4001103405035040405424140307020b5840101039403032500f075000188003610024014424001d40a444c009081016030024a0030100d00302080c0c0c400343c0043c41003241d00c46160080702d90080d84146202d03603c0d954043c003a1b00400003508065002130400a40c50302494000c4014541ca07040b003001c042281d0340741b00070441510a54000d56401c030481a110b200418007a00c0807035a41e9404c0d0001003102130094660070100ca031680c2c072a0300564044042040922411044a543c402c1c0900c0c11520703621f8010744440c034008044c0710721412407510340c01c55a03003504240107800744c40d8001410074140210682d000501d00e0300b50300525440d02d203070200c000360b20b14062080408042c2e00000f00c0d030550391140e0b2258010005c18200c15000007010458180c0e0f6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 627612985 1250 627611735 627611749
    0xf060509010f0c0b0c0d0c03061401050306011407080a08090a020a030b060604030b0c040303030b060f03070c140105090606040506040b010c06090602040503031306080c0408191401020a02010501150c0210110a02 92
    0x445c1444111529400055100010f032030b44400c1c4807051502d03004007400791441902070003c04002c28205159291500c2d8012100c0041116190b6100c02e00030648008000d00c0400610603144103942e001160780310840c510707031240c1e94000001d50026020300c0c2000040d0031100fa00c1d030f200c0390050030301d810207580391a44001d14008544106c24031900280c1401016014400d640b0300e035605540c0981440140c84243e0704511018200c90188000040c0e032408000039120704811079002d010090046040c01e4000d2544c517441034520030711a81c00c003030005030340b4285441948025001650b400f69580c1503522184001c000602041c0c64041d004c0101244946040004048440c2e4403035540031a20300d0300100414400d000b0300f100c0d0040380c0c1003000f0054414001002e81761307901c141d01042005141490680301107007a56500300c0c0c440d400414400021038040d0311043c121a000a15070b44416511481190782d80d98002d002035002d12101046c6601030b11440d121030328803a80801f00d07400c0d200345400190a13 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 627614235 1250 627612985 627612991
    0xc03030a0201060512030a080c16080d0e070e0c0406050c030412050d0e040506060f0919080109020906030102120c1606020301090902240910020a1b050306010f060509010f0c0b 77
    0x140c3e442e01e0b820442818000400000c0c92103030300240d41002d00310407000301082800b905e00c1c0d134520804119002c182c110151a1519140d201000540d218008a02000905001d640049580c02984000258500941c000301d101f401e42d05000c501d06410800e05039619044600604040e20060001140c007801030342c03042c44440d00a000805203611150001400d60200900480c0940d041c601800015120003041e58920503003000b200b52500448004500d090a010107410620401d04a0000361880103502074803a050007075400c80b01030703680c40040c1401c0c0d21804032054258440880080e540218180c0940f03107009800010000b000c0c0d2940310328050360802c1e001303581d51716510ba051804600e0156600c0c44580a141101c004144403503a0005460090345011030040c000100e448140510034801c1121541d4801d9000004180b14032541552603542d0148030b009206030000405e11840c8082d0140442e2601da5070b4900d03010106c00115440c6446140d0601481180c841e1003000980d040c100500c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 627615485 1250 627614235 627614237
    0x40b03060702061323060108100c0e130209090a06050102120304020a0e19060803043b070c080c011d060f1f03060f1b050403050c0d170c060604050f13140c03030a 71
    0x46e103941000011030074907803201e4524036024500310020621607004220b148035a01e0440311703640d0030b40c42407203600d010707101d02d241d0b80b60b1001a90003005078110060b44600160b840070707030894800c8200c00703900e40700300e100a442c060361000440d40100b00c01810302d110242d2010041548103000d180000c0883d00b82c1d0f00380c0d08080348030b030400b01c0c0500000c00303400c01708000d41c140b035900c4006d181103262061043c00352407401c0d1810ba00e0040009650b1a02031801c03a130280b648240503d0b40d444104c0403031402031090741140c498803680d030700000c10190740003e8100e028a283c1d035440199600c51440803c0e65020403d05d034041c88103030441c008041200c0b4803540e0000500c908000c140c041c09042c038200a00c280301d507140180007043c401440818000036010070380000c203075401016243d86082c480c44c140c0745046040031410340001c9055819201155045c001c5105a0702406603032a05180100701c50307400c54000f441e610800d0030b14000700ea43c0700601700da2000d130a42520800351b0000d01003800c42d1301c5410118 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 627616735 1250 627615485 627615493
    0xd02031518160e0a150b041805100b1803010f09030e010e010201020c0705060d02090a03031808010b0906190f1412060f1906090504060902040b03060702061323 70
    0x419a0105202c0d03010b020044212010841d803c0c80e42d5011242c030b001d0811a4202c4c1c0d190044c0110045240d42c0300060445a00382c1619140d4580d80d80b800003e400c1000010a82840701040102c0a0001e805050b5900c00d1030490411004040d1402c5001205405650664a445021144d86518411525020300a030385240b40381c04c8000c0090328490b9452030603411a13104101608013900c0c04106441618001c407801a91544c4404c90358010303000d001659070b0703c030342c580c070f40001055000402000000c14601000e466180c2d01c2070543d080390780016015400c00c816400049040c0b0300f04403109903220403212034500c065104d4400480030032a540118030f540040c0c107000c084520341071002c07031542038200006103250701c0c200b40620b0249901911008400030070300805210700c7c00540221000c0c0ac42400d0030001850a420010081c00101d081a8051850304503100c0041c10b0215a0394400c440940052a5075140e082d9881d079241c2c4000005d8400e00302800c030f10b40360002c5424102017441e155900034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 627617985 1250 627616735 627616771
    0x5070504050f0412171611030406090503101401030f0206160308070e0303070c1a070b0c03010510030504031d0315090f010605030d0e060d0612030201090506060103090c050d020315 79
    0x5130721079914124807405004c038145168518004a03c0c080c2d600c00300c0380405541d0910183d805a8207140302c00503101640c00041004180d0307030380c020b5070740c000c031401101182c1c0c08030b01c1840f100307045031500c080052110405800602c00b01c0c10410700004480d102601c2146400341e9000401c09042c0c030302c94101c00240e00c060620182940c860500b40751900c0c00c0340503501d403040075070700d030124062240319040c210548141e006005051075801c1c1c44203284c10440308107040c03038151035003000d650003405038034072603408904102d802d44d12038032035107200300ea0540b14545000b050784403c040782000740b00d05562511401d185c40704003281054215005080e00c0c001411064400e485050a4400e0794001500981c03180003110b00c56948003e0747c0f803004105407541c59803901c4204901014040c07a80003480040380749492241015815405028194007030015501c823501c50400440135070755a030b02e001e003440120402c20300640c9400301010718118802002c41c5e289200100c01c10195040c1284c100e49000201000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 627619235 1250 627617985 627617993
    0x4050d0c0509060a0b03061005120a1b0507150911030a080912010e0a060203090114090312071b0602251a01090216110a0302031c0201060e040203120705070504050f04 73
    0x1019030031403c00caa540c00003904048034403002d03000040c1328034400c5d000c112500d500503000e1401c0721548100d001c00d990440c6041c022080251180c944040c2c2c071207880c1c80202e9409031181040c0c442e0036600c069803000c0121500c0c0c400c000b8000c1e20600381c5200003454102c1090303a404004100c0e1030782c440e059140e111514441002000da020011020980c2d04180340d542c804900402c28242c040d5101000585a4a0f64101031b4010300f0f100000030406076001062018014000026295030080c58038941100e03641c03002c00300c541001c5502d206e01500c00d0503c00c1c03000a0840d070040c0604040c0c0801c000b55509030700000f5400b240552100761484141d403039903030310203c003185842c3e405440e01260640c51b003044517a03454079541001c400502041c254540d5505a42c1c0c640050400568004044480300d00b055545800041d42c42c3c01c0910240d0311b410380000303450308048021403007603030020003a02c0c0719483c046096006a00010003190f85000c1d0440104443c0c1c0c480c45203c0c05138581e481c4410182ca030600d8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 627620485 1250 627619235 627619249
    0x20d0206060a050303042c01091b030b010e010c060e120306100810060e040b1f09080705091b130f0312030212160e0603180d050301080307120504050d0c05 68
    0x1c406406840940414011078400204603000ca5507206250041310400d1480342204150019101041400580c00026012281e40201c0901000030740b5100d120301c585001038049802080803180800d202c40050a015805807001c400c0c4103001d4030002c900c1c9100c180600b4240901d814464442e03000c0401804024207001c5e040405800681c01c00e90460700b8450035000c162602c510440c41008600107911000352955040b482e40301c0c8010f0030a103a040c04402410341c02c1c118580d505000964480c90001ea00007000800200300d41024000800c0740d1180076621380c0808040c442c030801c1610410101d0350f1940030000c160700034a10040c1000f5a1402c2d032808503100390100402c41c0130580180172100c1301c00d600c0d410094010704150070710a503c14285c1001d8409803c44030b58154029004810810f00780c001d0000d04078203542c11b000361101c1021041c401e6445000070300034041036900c140a0040001c0410005000041c0d20341060703400c10313540307000003030940c1d41303040d021a20410400390800c82d50600b14 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 627621735 1250 627620485 627620491
    0xc09040b0f01081f1d0d0e04390c3302040608060f0a0504020f030412030905060c160b0403020a0308070201050106050a030209060d1104060f1b0201030b031507020d0206 74
    0x40c00e88010580050100813151a20a84c03010360348680484001100b10b01c41c520058190042d21700101c804070700607040070406c020341c0313000c0d9007800c02d429034044030f815902024004080080f0807010781c02d044800000c42210303103181408a00540382000c10070156084981104031546010400045100040d075414110a1491a0340c014803003801801d411140e043d610410547e04040b1a400400000e04107127490360229030801c2c8002501d0300359071a104005c6102d40c0c001c03000400c05510003601201254003101c4040c205402c0140480c503202040d80081400c000c5030f541c541e0001005442ea411a01e80a507800c501591140c42c2030010141c2140e001070b8090724600017000250301d0500050305520468415008140d800200084e2a555100c2a200020002c030b104202c1d0280070140400a0781c028040e40000c554149000b0100740d101e0b1030701010014003049498a440e626500640140c100002d04da54503000c1c007941c00c000c4001405400348201b16560040180190600000c0e05200020b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 627622985 1250 627621735 627621749
    0xd05030c01181131020d060e01050108180a08030c0703020c0f0a0510050409020c0304030b150d0f050a0611041d0f07051303080a0c03080105091e090c09040b0f01 71
    0x404034140490f0030940c180540d030300b060307a07415120020110400441c40b00348029156181c0c810364515118011030340a04030007007449204012107602d989540181500034400c03540054098030002c0d40191941901d4280344499600304c40e61003000f669003541d10b4004071000b48410202040700d00c1415070400008414040945100481c1145a000700d01040900c1c01070074066910000401451441072080300c0041410500440d00c4100443c0c0075912030380b00e403005035110840040460060400c030b071090512910700401c1c1c214020110f55800070051014002511240141421640880c0747c500880c03a120308481c6411b9511400d280e0001030203101c0d40a450f207800032180400100f2031711641400e800600c18104075448042040002c054403406030001070201601040911000b600034a0750a602407194031694010f030b80f0b80c0203104000030308460391000c3c50b1140c00ca402020300d29200054000e0a203509a03070b440350000000c1625290180c900b140c0c06c15140e810841694281000700d4050440 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 627624235 1250 627622985 627623021
    0xe03120903120c0c060402042f03040318150c0c05040f060513061d040c030210020106150507050a020d440a1d060909010306050603010f06061413050d05030c01 70
    0xc130703800403a614800144000d025541d41d4101040108c068103446c200202103250450100c0c02d0051004010741003a02c088011035a800c1d1254a100c8603007800c0c03407c5d1002c04001104010315214220b0700c05201610944242a00c0840411262203034000c0690310b4001d1b1001003142440c21050026040394540600b600f5846c000050210805141c4803603040106070110314000c0d11513003050034113143c0641c4002d40c448401016569181e4064101b00e084603402c0311400740120360b40006a80612405e03000414941000c2580300041c6414009622018002c40b10420b003c00c0b85c44800c91f10907000c01941881d42c14804540481c00d1000c6000c030f54080742050311604000d10000301a080001410055000320b291106406982c0c5540056841500c070003002d2208550f52070034400010b16060f20741d01c3c080c1d42050320380720030501207020b084202d80c1e0366030f25101c000c0041192121140c0200801120640c20b8010006243c2d5456225241c954041c0c4081d43d40c689170241001c4c210341405043c00c000281d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 627625485 1250 627624235 627624247
    0x429090115060809190212030a08161404170c0301020f070204230c1c050a020a110c06041a0705150108281112010603050d260a0e03120903120c 63
    0x1a02103005d03428803203000d58145614441c0d200140e42c5249264a1074013900c00400c03441d414581c0899558006e084070054a80300788124901100e403841c0d801c03005202c00c030003000100882d03d00d0b9606141401c2c201001c0d58058000c1400003426a80319170300d007100e070510100c2c1000551800b441180b04102061100b08851068180109d4032a1070040000c07483c01b40220f49844440d50258030904a0b0301c45110401c020701e84141c042c00250084d203030311000074031100540031142600041001d40a8001008035083c1791800b280406008403240311205190418040a800207104011241d0038150742400209590305091030345240c251043c1c100d2400c0700310410050040c203400e5000100443e000303100101d40703c1000c000b003059030700d810900c54000e42c83c00c0c2e000418481d000c00c5c05040b07800b00f5600d40380c502805c01b2700c01c420300030303503502a101c00b1883d0008100340340c0442e4450045c100b4650107076800c180d810a140c03c41c4604c100d41030f0503180c00004414000300000b02850394000c81115006040403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 627626735 1250 627625485 627625501
    0x15030708161413090f1703041208060310050907081603031416060209010306051f020d050a020613020a08030712030501050a08210405030712020306090f0604290901150608 75
    0x750340d0b0b0f240d658440c0e4950881d0103124501c80c0e82d050860708801d40310300c048402d288401c80d9500440702a1200001d4031303404a012403007001054003c143c010300414900602440180013060702600c00280740c0b0070450300154600c02884101050720b804c030300c214038507461403c1c0038242160307074400d042004071304000a0105003d5202040c00c5150400c00c01612510001c006038010038603508803550080ca8000400e03600001040c402032101c031603a003500c05205d402c25050301d05005034010000940c1240d8009403803824010b0081c080302c0e0004141c08000769503901c0140c00c41d4400d4006070b038150707024104d641c0090380600810b0b00510302034440c0d6414925000d07000b925103c5000300c40c45180f1900345541c4031140042c0c140c0d0042c000040540e50615918140f00341d214000003812400381c025400000d65040e0003040181d00700c03800c0c4d80a401666607982c0c400040301c5800305680072107500050580c0b0020054070083d4481c1c00064000145600050480c860700340c40356220504022441c002c0249131 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 627627985 1250 627626735 627626749
    0xc131d090606090a0f020f0c011506030c0509061e070308101a0301140a05060c1b19150201230f0f0421020a0b04030512010803070503070b150307081614 67
    0x4001134200003901840b04480300040c2c441c00c0d2a0540340840805c44030b02c102810b43c404104180b240080c1000c6a41d5000190b06580f031242d0307003c1c00728505105042440c200180101108036040118201541d0b1344c061900141d0003080003540002c00610410100240b10714008020300080500200c000c0c46c2d9900c4207501d40320500415000d013091504200c0c20b61a41d4081c1d102908000b40100d40f10b030120840980e581c5619052070400502600c11040e090402d081d621840c2100900540d031360034106078003142c010a000103036000b10b66980140160b0b6440c2d001c1240c485810310482000141480030100d1280240035051560401188043c440054450042c840c0c003d200c250031400080040e201c01e07402e016400001806600c8020208010075500c00003c1640383e604000c0b0081a907260f20300c042e0341c1c1c000d074000104560304c104071903030219002c54102c0e50321000580d200300345451050701090904095500c84e40e49907102107003015403d40700a480340d015100940311418180000340018000d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 627629235 1250 627627985 627627991
    0x602030f0a050705010b0a0305010f0605060c0c090702031216090501031e0c02030408030f09090108030a020601030b1b0a0c0b150f12010e030408030a09121101080c131d09060609 78
    0x92220000700041004429001b807003600700c00400200d000b0350340e82043c1d80031300154040c3e5810980340050100b00c4e403401a040d500b8000c3d2841c02802c0d0807510005020180401400000c1948020b203ca091070001031010380d44600300406840001e1400d101018001d594203403c014141414030b00c1c000c0f85c0032072210840003003c05030640800c803052409001da01310710642d04203020078080016106140c0d100c49004104003c4107a50090043c2c2c0d0700c4058507101d026082503140180c10100040012074450507000b03401000f011a803262015503110510965884204910702140035929010140074589080d1a4488201c034031a004000c130000000752205100360001d07200d4078640c014200110003d60111740c4060051040780e544582303c1188640d40e410134440c03030340058298880800c0624000040c010156449040e0156002901006540100000f465a201e0381001d100c0c580d05c1c044041c1c0442c000300350744000045c40740c1100e49000100d40c40200210160340c41202400901c0d196240c82c694 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 627630485 1250 627629235 627629237
    0x160909090b19020f0703110c150f0309070506071514090d0c06241a07082d1c050603060103050a02130204080d110d03050906220c03030e0a0602030f0a 66
    0x90001c00b035090790009020f000c5880f030309182c0105036402016003002c81c80c4442140b510444003000c40710003c01c100e850410680b11031aa90600c42541001c007440007031034020880c4410384540e50340320780103e0599008105c003966101483c020881c01d2031994441c080c41311001140d006420b20700000003907901d1400c81c11010810800c1e41ca2a414002c5a603c0a005650703e088003e407020740c80d0120301d002070b8190140442021002e1103c1c405250950201c1303c0c200e034002c100900700056250780f00100d8007051200710400c213600c1021b5801280138402003012000840e0300c600741e801540444012628001d10640c040d9114000510218a00150014490350304a4546420792201038844010f4000e95020740715510954401282840d0407000501c07a9030b4400c02141c40d80a91480114250307001980d000c8050741103040881d0b0b16028a4110340743c0d203001c5085054000082e0381d94482e400310300e07500603000103144283c0c10301185005400301c0010b0800384002d41c00d18034001c2008141e8816500444 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 627631735 1250 627630485 627630511
    0x10c020102070504231303020d080402030c0a0320150702040c0c0b0a050103030f0201090f080c12220e010602121312060b0102070611070b21160909090b 67
    0x11085a10802140000d4400134205021055912a02d034104c2c16003000c1d1141e1101c0c40788002201c481c031141c0d0003412980c05600505404801310340035200300c0380c0508141e0305030103840c41ba901c0640720384201000440c41aa940348240428181102680600300e4280e44120310100101d410210800c043d039814940460b00000c096030a1081030341c10280811004004000210400c5039900e4154407044c126030207030303c1d10300b40b4040308034089003241c0007003800500b01d8080045000114a841300507015603540203084034039030403020b035600e222a00300c001d094195421060384000e141d1410f1994400400100c10410b009505200c00603440d00c0070100c001c00310756800701d0745030302c88054031031032a0081009680198644a0700d0801d000a80360b04010180580f01e032100005095105480c4e10115540c0203002c0c2c484a0300b01358010a03194012031290b0888001060588140451500ca26004100c69445403604000e070801c0130300000342d10341c8010421882e1400c02c2020564a0740601e500412241c0c0c00e03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 627632985 1250 627631735 627631757
    0x3150b03030c0703080a0f0e061e0903070f150201020a0914040906091b05090613090213051f0b12011715010f090f0207081204061130090c01 62
    0x80391079405141d403030054600c0340100000074016020010080b4105aa8600340300641c01007017a100965500803050f0440c0040158444000e16203180300409406000624540b0300317141c000900c2c22069400c0349002ca00303014002c022103184048032034140603090000307504141481c5006090120144940100c0070300d8103503500c07843d6480350300114590b540328000b00012819030078007200e42e14a00100501212030b42202085038541144980d01c2603c00424211040450481d0080036020b2203004a030041440c06206059405900441e4898003a0406030b0315401c035401c40d11141b102c071580c04001c0c00d09003040b50649400010f85420305482c041c01d40561070342125005240380c030000030409240480c0c804000701d0800c102c0c00c03541003252001403041c8041c3d0360b00342400d4101c0c40b400100a002c4d5104110400c01311843d0740501d907110780102000201c4e41c80310300c03805000e9400000c40c00030305007141035904681200c0401051170708001105140e080e14020218554404130201c010341401009110 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 627634235 1250 627632985 627632989
    0xc070e150315040302120a030b040b03011a041e051302031c080c07030c120e010e0306090303041410060905160e0d1506081903020129100302070206030f07021603150b 73
    0x420506c104031040b48a595000c0460010004c0034140085489207040c40040b020f5440c0500035800410841170510019039200e408001c0102808040e890800f000e41c1c90b11f8000c9038840c41820300c0396145640b804c5500c0801c2c0304150500ca40840310039140c05030044c00c2080140d1145920340e10101010203265103040030308058a0340540c003030006000340082c42100c81c4032a40031140d800100c00a80321142e14000b05000c264441d041160800b11952061002a0108042028403001032040e0f1090740d40307130505210000c01b0781d0300d0350700100c0c62a0303144c20034000e8000f00311440d2480760b03001d85003014000071040002401c032400c118028080000d00d99140e8044010f552010b0000c0489100300c51241d000c0c40300203113500c248010107030302552130594403040030001482d00c811001a04004601c10406a04c03c0204907140b03090801c0c00c06900303202950050300c50701c00941c05805400c03090304007481c0441d0001e1510713007a61a05024501c480c00d003040020701400495050501c0c26a003c07803440f2003000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 627635485 1250 627634235 627634243
    0x80403021e03030a030e0708070b25050d030501031709010c02150421050d020c03071802040f0b09031b130b180708090c011805120a080c070e150315040302 68
    0x30101c0c1d454000022001d84540d015403028410300e950130180c5960564565409031501c138548540088401c1c20019140060309004441c0076a40e220007810b40c96800301d46506150a00c000c00b01c02c0800c0d60b810062041c0650400c0e680c17210b2140580d514034110589000070b0070b038a050a8028060446002c510724503a10303e5055401402030360400e42ea01c1d1a050300300c031955820302c220035a800d0091520451085101280003103441e10054000c00d581c034230300074000d81c1d0500386040c5240003582c203100c0842c254440000c480d000306000d004250301c0e50b100c001014140340c801c3c410040d0020920880c15038585550086401007401900006180304245000c0381903107440d0941152540c90b00030410a15503008200140140641ca0407150014400d40040d107020100c1d1444102e50a000c0c1010882481c10141c2010003044800a81c1e1400c0850390b50103140790071030700c04504160807801c030900811111401050b8818650007150b0075040c42d490119480300e103c009031029407003000000034203140c0200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 627636735 1250 627635485 627635539
    0x1030b060307030b192117031006030c08010807120203030c0303161106070c080309010e060a0b011205060d0809011e030204050a141f120905030403030201060e0408040302 75
    0x64640e507928078110500600138405501210b10581030104040c50a50190400d801959031022065005030003a808002da080005002210320004001110031400e1034440618014480c0c01e0482056034140507024082c1c8480011040800810000400001c0400615401110300c03070001000c8100003800400d0a6100da500050b0040c400002403210b02c4480441020f05105180e64080c4000ca15001d65621810152090000a0615225a030100b0780340b00c0110380040c0e016000013413803060911100c1c1005421218000704a54034448120380756048925020901ca500d80d040260b880d00100080703440c6100103020340002d1000c00e5449503640154900f00064100881c085600380d04514001c0103540507000d001c2c05942520b034002200440300890716460780c402000c00b00c134101100c000c5d41094a0490320041085440c030300741e00140d5940c1c4141106e007402030300996561815800c020342940e00691041c440c1c681e5500400011800c0117058034181c2c0c1d412170b04d01e40086400341c00c1c140465241 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 627637985 1250 627636735 627636739
    0x5060d020406031a100614180d03020606280323070b0c0106090905150a1506020a060e0606150702040914010c03060b130501111501081e1c03090201030b 67
    0x803072404018810842c04d88015500d00c0850b1094958840c03078003203450613040c80780380003040409441c00040c0203418080c046003c104540081500290b4001030b889640405065016030003403814000282021522981c4441007160038110406060200c0240407905100c0a04061103078001c41510f00c00716002032880c1000401251081d9031038952605544d0302041c9008419840c051001070315076042e00500c803405410801804243c80503040c60a14138031f00604240000b592003907118a88241440e00f00050100c56005140071805441c001c5c0c110342c950100e0303059076440340c01005010743d01c0e1003074800b1452180c404180c1300c0c10184041400b400d00c0c54401018420400707c5080003520543c4001040c0c0d103666020b10a0307682c2e40c80d4208152192503450b00200b03002c05001d11155008003070880e500045a0210742c0d4010302d01101102c1160203801c20311054012003510302c42801280ca42d0076408074040301410185400c00d96018030719a04142e0314051588840d8810156030003984114562900 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 627639235 1250 627637985 627637991
    0x4170a020c120a1a0a0e06190b030f010c020102070b0609090607051b0106230108190e071208040806010b0a0804060f0f06030813090902030c0909030c03220b070b0a05060d0204 77
    0x15081307040d042c1c104444030801649081d60811003000c0014031a030040f08628100380b10481e030190b020300036003a14212650144540e01510303079030040900c68485000385541c001a140c0d001303407400d0080200007800992240607042d00b4007000c2d070b10100d4a190000c5042c202280d90b4600304000a030003c400181da00030651030450006a0b12242410700300300071400e41c4080117258444030054076900c50540d0a1203421610095050681440364400c10a022104007103a020300e136202400c6c00c50003c040c83c12207883c0d2000c01c0411003854208149405418210440e50030884000300007000202c1c02030001d4525501c030101201104426803104008222145052000e10f460303040c0300381e4983c0b00340c40007201d080f120314001401d075507a441a00300b202c0d401000303004c21394178007401c000010f103001d421590180020010380048440400040c4441c003c500c0208002c1c03940000680340700800f551201d00d0f01e0508010380b0f00040d003411851907125210200005403520b65001180b945021520000d400502e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 627640485 1250 627639235 627639263
    0x70501210501080a060518070510020118081923070c03050307140705010e03120705030906180306060d0f03030903090510030509010c0f0c0b06010e1804170a020c120a 73
    0x440030550000b113500598050165403104220300e1040588078014051603001450107110900c1d111000785205101d502c000720f200d40d0014101e83c0740c2c40e16444102d40e840000600010351000a152500b404060350034414903180c1e0208000140190454590701e00c0600001d01c030040058510340000616000401c4070f8984540f0b05e8840740600b04400c500c1054441c41d60700040541c40350060340d01c0010041c014200c030030340c12080441c0e03d400107201142d00c0d00051010104030f403030f0800500781000003080c80f080e001070b1400501d414140080d2010780241d00300c0c0c2c0305d1000304004881d0007002036030500c0c0006210515040484000d51107801040d840409640c0c40110310b80d068000b54095256000200002d07401c40d00c00751455035804010b180480c003415501d401250385500307200d038400f006040c000c011034820030002e044080100d00080c001c0860308140010300000401c82824a000b680080c1c0c5400b50316140607580f038180154076485a01c420b08401c0c031100c0180a103038203983d401303692514490 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 627641735 1250 627640485 627640499
    0xe2506051c0603050a020a0e06060405040915090302030d0c02160e040606030b0a1d0316080f0d0603060606030c170a0e1903080403020f0102250809300708070501210501 74
    0x2607844282e00c1240d41100204d2000303c0c0c05231041c055071000300380c2c3c0d00c0c080c60301040c00094500316000780ca604980401580041c4c205000d0300510520a44c007071130782c0e0000c0200f50b20881e101907800b082113500010400e00c0d500c1075000d01005448000b2180e6070320340d46519154010388440d030001804504440c050024105203500a45001590780f885071820100400c02542d0341c0c002c41070b0000f0300817424244c00303011410720070003880c4103079448401c5440c0ca841c008107541920700035441115a2566250304200d00c5516100701c00e050245841c1c4410004e03804141004d0005000c1c043c4825a03548495403152010200448d00358008094101c02ca500600c0c00c015140342c40859050380580074421300c51713031400c0b01803085699590f22500b41946407207000c0b000b8181c2d8496808101e07050001084104082c0d66580c4c06451401c052203083d00c24a90b00c42241c4040c1c0201010701122076102110501064038045000710980c0c03800e20b0025004144100101103c201c0e804440e040301e490f050002c1075030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 627642985 1250 627641735 627641743
    0x1020f0714030d14090c0d0f02010e0114120114100906080a090629060a1707050d0e2a010903020f06040b0705010e0d0c020f090601020115090e2506051c060305 70
    0x1d40c012a055035101580141400300c45071071481d00901105448c49071000660141481a8a0007018500038448405007241c0c0c004651044083d1440c0040c4407004119440400411081030b440580750752800008000303010300b60360414010347c8244420400000c0300b41b02c203540500313007040c1c01403400e0064400c0c001c50308110855100c100fa08100c4000340070500d40c2840800c0791940d007240d540720b61055104c2c0c1e80d80565404090141000c00004102c10480341c866801500c05906c0c1c20300190103000d002e5042620380200f086080925480705440c030740c00603030f000541c410860380c0560306034804a03c40c00020b03201d481070b0b0b01b1690001c1c0011a00c2c9062020550103822540301d2617040b5580442580cac020780384c0c0711568800940c8841c44d0300240b80700d810070700c1c202d58100c4d1046c00049103202c0e0725440350041904035000031070392943e1210865409502000351800ca04c44904003a10144d080d030310000c00b581801d00a110502c1800a040c08416481040c5514520700000302003240c141c41340740a5072a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 627644235 1250 627642985 627642991
    0x60902090901050f01030f030309080a02060718080d1803060c0f02070f230d12020a0b010f0f0e071809050426090120240901020f0714030d14 62
    0x100d10303003000600c48540501c121401070308024500e0302160b10b07603a21410f105084460450405490704030303200019890b00c4c0a00b000089940181c900d0345842200180510701c03166115104440c0d0a204110380b501c0454007080106003840d10716290008094000883d481e203520080086141c04400003d055000b51002e05010256094403080c0b03a60b81005844002903008940080582c64080604403640304003009030100b000e001002104030a403030340118641d118000d0303409608a4081035080010340070320340740580000405412405c6c1007061000500200b030045200d2448402c002c900c3c0c160003042d2824240040c0312500504170340f1402500060700342906c08482071042d0091800c0388942140b081401c03116280b48150070700c211304004550b1390700350406a80744090200340174020700605012487d40803900c0a005005e500c4030780005401007600401c510a5644140b20b100202d42e2003c00310713030003d03420018403030321070307030701a80160852240c0740c17044a80c186020107110b00c0024120040d84 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 627645485 1250 627644235 627644239
    0x30408030301030c12080a030f090b0408030a06210b0916080715050a021b0f0306090609160f030f0201050f0309010b120c06030f0a090b040f050712020108040b040302030c0703060902 80
    0x9606a0305c0a11800000c240346000f4603021050080c0d501c010705c264410440c01200131004900c0e9007141c0c60380800ca640966040c2d42c1a8800800c20001c1a9180605001041003a56080201080e0f5008007990865450010b1100003001b02041c040d813410084403601c20505040c03201b505588481c41c55403040d841c8200f05428a0b03c0380c2a0105a028005a5955410300d8021b021420071441c02603903803851000340550700c03418125000d1603540b03080000d50f1048031040010700b83d07414049041d900c0c0480d20990342007c40d98550041c040c500b94010624204c0c0d501040b240409400d910050381d41f4042c0354080c021441d4084104002d5240540020060708015111451011401d112030f6446a000c819070b541c01440810200e440041e0f00581194840d6038030400107064020b030781e01e04880c1001514141c90700740202400c4028400284a001c0040007442080c5c005c4d81035550002c0c11440c0c0c000d04c0500000d1409002609041c021b0003125240c0500e201500d1a20b501d074504680141410b0006034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 627646735 1250 627645485 627645503
    0x30603020f060301060f0f1b0606050f0a03020a03060507051b150604200c1e0d09080106140d050708070605120a02090d0816060c11010b100f03150803040803030103 72
    0xc441c50410740100c9041e21483e607a0030a01407010001651500548081441001038070604940100c03101e101071080a4480c0102007181898031040180441d4071010051140b40341c20010001a0341d2030b00400100c0c0e03400040030600d0750f1600000d0b01c0c84d0040355000303480d4900314040c40e2902c036070109500a81e10307104040d03400709445070b07020300080320b00d01c029400c0002c016542c0e240c074108108000d40200c000e8941124145408480ca800070410010721420080c2e2040804090242d00000004082c0240303d00801010f8a0041118075001031031140ca130261441126402c140700c002d000c044041c00c0341404444402da591070004001c1c1d0310020707181c90302205600208406032064021074240d184010910341e0860107684403544558440d900306114041c007000d80c800054914001c004424500d13071079001d08101e14800c89030a660102d500c0a22640002804801403034008680230490100c40c9400540e80c1c1e1003043c4078203054460340008800d8440881d00050b20440003000754180c0e4400c0e6000c07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 627647985 1250 627646735 627646759
    0x40312020d1103160f080d0506010f0309120c06090b0c191b230d020303061513090e030d02042309010f15031103070201090b0903090915010203071203060302 69
    0x484000c190350703400326603d800400800d01d41224441c007a100c00c9010b0960106141c0607903844c4003290f07218400303400740240c0344d03c20440c1030740e00169080c940b0b8014bc1402c0c403400700c80d991420612081d40116406100d200c82e2443c0501c0800c0e4400c1d0070141d44071045400c070b03044c0008000050307000f000d26901c1500090010350070541c850401c00511000320440d000107015030b0350326400c1c081510600c0c1815200c40a0410b01c084d50708000403a031640c0f4a030090751b42c9003083c0f0103101c246003100c00e48040711501000700d1800d41c04203061140856030364090004020013441c44e03060451082d81c400316060f80c00858003103000c07400c403400c2c40356800ca0740c06040000703011107051010700802481072040b0003448120400800c1010700400189496603d00020300e80e48449418803940c000380d50a0005039561b6020b50208090140e456400c0030740180154280b516942c0000c1125900801d00d8842a4009210454590081007903446041c2e01c02d450300741d6005801d030020002e02d59480142c4c0f1801d040d102c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 627649235 1250 627647985 627647987
    0x815120a0b070903080304060203090f0a0b070806040c0e0904110a080114150907030203040c05040507021c020c030d050702040b031e10050c120414030a210506060a08130206040312020d 81
    0x520200c4e81e000d83d06900310b944a07200c80b00203400c024a0b00050f401074000710001e40d4001d014140e2464481c4902c40b039035041a140050000c3d40080c003682c0a2464007100004054000220212180045079525072554a0b0310f069502814040c02450300014075501c007080300141900101e210101690784155543c1d11403030340710480b0300526040d9401032489400309032214420380003154014000c401914010b550f49011600721181101c00c0001a0001300703140c181c1119041c00f4003006000382c4028025005a0300000c0d40b00e100c902410740c02d00c40005103036000c40d105c580100d083c842e0010150f60f6686c01d8503032440000c0c800324001c030a080c0241003003418004450700c1781e0307802100c5c094001400c1070150b40380445041c00240c02658231105422084044020800082440017a41d54414007064188550800700ba100303c11100c80a03030501c010407403070352141d03400d0301c840c819030303150002c1d054030b502d14034020300c0c655020080d4028100040c08014410b2402c0600c82d2070807558200c030b95801c80d001d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 627650485 1250 627649235 627649247
    0x6191a060a26151008060a1401090f0b2a07030f02040b0d1b051f0c170d0b0909160306150905090705010212070b01060815120a0b07 58
    0x161280c0c06842804110384141c45000c0c10071850701090190384000e40e07001000810381804840035560051126a2085242080440e980d480c4c8071034200021181042c40000304013410364041c1039074042c060424240181c2c400c41c1c2850061515102f018101911140d600700541d015014014000b02c2d82059a1040c00c06540140244801640608841804c5554405560514100903039100c0e41300c254401c295502e400c410b81c0554403a080d200c1103014407002c0039403025080e40c4094403070b0801401e00d440215070003040440701d45051034904d80d040c2c5185010a0107903640e90001400040104c1e0000c004660750f800705500380c0044815080d940c0c2c40800980e034820b284a070002c1c00c01c81c01c1e42c08000086082e044400b100b01d05d0301c04150456114400d0303004a500455440c100b42d0b000e40000c02c03c40d6018802150600d490b400d402d4548411070b00c50000079001131042e9410002542c0014400c0a0301010580c18502d00610704000780d0200030a940ea2110200c03400d075486558400800c050a01403a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 627651735 1250 627650485 627650531
    0xd080103050d05030a06050414060913030c1704030506010b03040c0e06330a0c0605060405011d07021903020f011103160c020613080a050c030c0a1e0302030619 70
    0x44014802402e4010003214107401c09032240c0384030354507018042141d42d20790003128019001a0000c41241c030b0240708000d40300001400c5002004183c0401c440403903800148640c4e480c2d0030042400c001c4140c1d602c044000d224660014185000c1c00c0c0011402c2c01d0108025409540507841d08050951245440400c00d1025101e1503480304030130034040d00001c3c0200043c503c8007240c0001d24485c12082002c68465408074510340c00060fa80300e107513002c00c12144505904102c00740e0b8100900e40c1403c50600d000249001c1c00d0480b0303040d00d0001001e40b403007005a240c0078446030420b40d80d148030914000c0d6940801011500c450f5080916608425010801b601c1c03058041140d040d4007140101d006031003038001008242c1e08840308201c00504a0744d00d40d0500010602d4100503c062603c500306a420711030100d002511035000041910700b180d032854100b2056032040d900e81c040c014040440880000143ea00094240c00f4050412000040e0304100c881000d901e11414000c01126100d41c80c0514500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 627652985 1250 627651735 627651743
    0x102090108010e040f0b18010e030405060f16080706021206090603120c19051c050901080a1d011b090806060a0b030907080307050d0f110a12030207061b020d080103 72
    0x80c8004000e14040300700404d03041400b401c0201d10000b8603454088500d41d007104e00e0b02d041c8268409940b25400244119a0401c10300d1010714100350808000032001d105902d43d06000c040302141c401c2c0007003032590a0002c41c59006104950721025480c10790041d401070300d6400745109210700011110705081c01564400c01d4010041e10601d40e80062541c07880c0c01030401032620f441000950703100c0c085088411030006004000501d040100a15003000c5221142100000c10800741315012050740c010041c560840030491020611142c0c0c0001e002000c40c010000761001e60070300b0045c2030318880c0c80d02e000c2c100940c40e545070f0843d1070f1941d4889a407401d007607a55580018030350000b0080440321002458103e00754400340c51b01281d032503024602e990003d460a40d0582c00c60245483c809801900400e81000c150800d07a601c2c03441c076149070703458a8490501401076040342424490300c0e44680d0403164880c0e80800b00308400301107030802c0488040c2c0011408003510504040090300c5000300b030079504807980 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 627654235 1250 627652985 627652997
    0xc06110d0c0b070c0c080c0306010b120105220f0f1104210311030c010c0e0d030e010e010e1c0215070c03060b0f04020d02030720100207020a09050c120901020901 71
    0x109a40c0c0c040d2600009200408200f024132030400041c0c0030021400082407100014207204002c0e408140c140b004c1a84648440b460402900e41300c0743e01003400321304640040b105c2100b00d0f1144100d0710500072404140800091801c03846181c5504d03a6800710405555800d4100b100301e4901e4020038880c4143e01488150b9110307011203c00c10100040000d00d002e00c64075098a8207030a031244107245030840004080789075110824000310582c40480d51800400444910f82c9030011520f01a00e40d100718408681008091040e50403940d019041c0d4400c00d40c00500b05020f4610341005907201d002100c0380891144800c00309002c90840c0740d009079200d040c2c00c001e014903901d14580d1540d006281c5600c0d11070f04a2440b85180c41c25070340d248040c2c001d030440303000c01595a1a00400051038129519282122030442414040030028001a100c8500b29814801030303881801c0e00004256108035404422001c0c10708081241045c001c402034244000740c08103160b62611860107032030a07402050700060010328 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 627655485 1250 627654235 627654257
    0x3020d0f0218090a0213030f05010e010606090b030915070c05060a0b1525150b10080c0c01110a0315060e0f010c020f0301050f0910020301030503180105160c06110d 72
    0x207403c15040742c000f0600500140b45c10300444414070f0120301548240c1c0c00220704122101400000e00407002d5100f240c5c0c00800995042c1840940341880ba03009040700f0010200c0001c0b2124010052070010010851030147d43d07203011200100f100320308220480e81c41c00380c80049030304820580243c01c40048020052440549001040d0106800032840800381074041a80c201c51007000c400980711640c0628103a0f441c511800300d09034190b4001c00500390045000c40120314010780d10105054014107042102e03a86c840416080b9405041100300b0324040d0000000d40c550182d4150344030b00b012110007801e80100c00e54540040c0c1d018100c1000031030300b025040c80c110402d503210b400d940c1001c034401820021040c075601d010a007101d40031520350314881c00c85014058039100400068a400503a51020351a540c199501d083d04c074028100c04d41d0440242000310380540c2e010740f042e030310303002081c2031a000600c1507400c104c545031000e03204d02d8010482c2c680700c096480c00003027070f002c01c90340c069111501410 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 627656735 1250 627655485 627655489
    0x70f0215060f030a17120c0c0c0103021e03090319020d05040e070c06020705060f06030f03091905090a0209040b06071e0c08010204140415080a141c03020d0f0218 71
    0x210b2000c2e003070ba0b240c003c003c044000100400031241d03607402d11417440c680305d210700c05009a4040015011000d0084184410802d41c6c2c80007880d034201c41070030b00c0c01581f82d19440900740d4030340102003400c0e18000c2c0040704120600c2c034008040c1100c000e141d0b0741e00381c014500030010b0740c640d000507920b0800280100014003082100c8032040e42c00c0701652400d950344d8095600c0d014100d0300043c40c00c681d90f40044c002d011160400f215007540004e003c401400700b005d01280142d56070700c10220b00d0f90050031403844030312240c91444414001004041e1080b981c03031800d841900c00950002049500c600e140404881090030f204080d80d0015134066a04501e001a01e2041c014031141303c10700701c40d0888080c1000c6007150080c0090001032074503420041012180030200416142d12001090210901880070021814001041081281c100100a2103d0300015035203040040181a20350394101040c0d0901c0510751540c0203000701e001b1004200b04084080360a00183e11071184005440e40302007408007518 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 627657985 1250 627656735 627656749
    0x20a060c1104060b071101030203061e031203070c0c1d15040608100905011826090a030b1608010312030c0309020d05010204060908120d090203010f060b03070f021506 73
    0x214000c12003110a50019800602640d409400908031300e20b010540e0307000c016001412114040c0242025815494101d001c1902e9a2951001c2c13000041c0300c1801d01d080745c5080c4009260070404100141e940e1504100c007070320000c000202240c59003100840050500e0110081c0c290750010340b4050303041034279034100c180d03402408076506507403240d0317101c0c00001e50890400c902d18140500e0480452701560f14240142111000c0c5080d503001c100d030360a02400501100703103035280080c0196a5203040004070361007480754014510f80319001000502c01100740070710240c015110742244c0c030f0001400c01c1a40d200b12001c80007880000d0075244c02994480b401030017a001144101d500d442d0014510b010b40d0001007541c40000c1c02941d182c2d43c0000c0c08c2c0512a0301c09010f2010385480030040603c468000700407035080c8100041c1911440e510310a440440d1b40a4000e200e150050000134488035403a000064065403090b02c120000c24075280800518034008500740c0005032a6115410340f950780d01c2c00384041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 627659235 1250 627657985 627658007
    0x80706020c061b070611010c0206100509071704060f0c0f0f0f020c04090c29031504090803041a150a140a0812040801060b03010506160503090d080c010c030504020a06 73
    0x4a4540c12540d60b50b044402c02c035110081140d0391b0390204040a1840090860301074510351000c40d00f1a008020400150b40e10361003c07200e003034540700096518454102c940c41500c0d8510012205c44905000c103008182d0454a80c1343c0c05004100320004205506845500b481245500410b51039041c40028038000d03810031186203181d0041d11400c0600c10000307011500d500e4022240c010b041c04050001071a040424000d800000d100c842d6a00042c16501c500c2c0e02008040741031030b1410310744c50109900c4641010030b43d654400801030303c0b030501346030580c4e61018540c001901c121050303001600300243d8004170018024054401020b035418400a548209007510384140c00c03441244002036094401c0001b0340c04448011400c41c1ca40d81400b003200d0a55043c0e130b02c0a034800300700380700600c00c4e640ea00d01203913070401402e0580c1d14038450a141150641c0034803242e0552080c40103006c8e0040c803210170003c200351030125000b080f142c3c01e4428181e007181e80507903002e90022000340050260b1030140b000d42c98 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 627660485 1250 627659235 627659257
    0x12060f0307090903020f01050c030c03011505070c030803070f030b0f0405040614180d0c111903050f032d0306100306030f03050405130c052208010222080706020c06 72
    0x7030069240d10072442552041101200144d0121143e5164808280b144c20b403c80741840102d451400c2080400c016800f060243d84544a03019a1290810b0f018904035541d90350b1000c0000c55050b604e0415940c50b4100f103807518085040c2400c3c4942080c46481201c0242d03c0040100040a286500f40001004010803c50b946aa54041d8203030b900700d2600c0e2148a4080f0308006103103a0300910515007440d001304520300600803d29031500c00551301c100030381d620140c00d03070b01c9007074031009003000d183e0102143c0e0014009000b010220b00352070201100038910758039049006540305154a04024442da00c002c5840c580d85000d2000c28054500708030100050101480e01250803902d0380c50741d46046000345811004524001410089810b102003414218041e80800304481e0400d900083c0c10b074803034452007011410200c80b400304040d86c1d403120f6001400343c44000715140c008640045a003103128400f26001816a20300019103a2000911f0b102540c034960b01030a40b0080040500c4000c0e002030b040d81e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 627661735 1250 627660485 627660493
    0x902030703141e0604081e0d050a021308030f0f13180605090a3b071206110a0207060305060406080a060b010806030a020a05092e050a090212060f03 65
    0x404100030408440b50169040003402c1c84400000b4041d00840322a032440903242c010008020100d070462041e10b035900c90136100f552402c800d2101e02840c9202c1c988045110610380340900030742110940c081c00200c9803012030906801c0e1210b4200307030740f0b0103604400094a001005005910749210700900310120f14014103600803502c508000d2041100d02c0005001c4613500c0008101034a0040105d070b82181085404110061403079281003e90441821040c0c907046001800c1020310071303c0601e07800030403500310585941680350780e0f001c8a05602d4107425035403035080480d03102e56000c1500440b0002c200c50b8000f000f82d18a0414190050803000b0700980d4010b03500d48001600000c184920b10545205500004003108040000740105030b000c0d12981c060303484042e400006880d043c2161040c0c4108581079043d60b650701c4040c4501450341607a84c1c04e030003801d030204848076003604100816a001228034040301a00d6040183c101d0003802c120440d00000040881d0b00f9003009580c0c801d180c24003605032 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 627662985 1250 627661735 627661739
    0x609230615040902130e06010e060d0210020f010e0604020a0b03010b041401090e040f021e0a06050c010617060103031103030c0f09030106081b1503070f0f09030506012616060309020307 81
    0x1a85d81107040030303207010050701c540390260050340900111307024003c80c076905e0905041140100e207071006a10700c000e0250400c4a00f60351081c0c000c03c0400c000210f860000e0104c00d51700d001c900c0d20b480c0c060711300302c1c041d4008040c041620303005c1c0000e581c140c5040708102c0b828507250100d512150350380b8410042c1403104400c7d01050004005400601c524050482d00d8107084480c03040c0001d580e005042c0c1503e07202940081d40095450301c005c04201c900903e880c54490203100010750043c50142d000d00c424126400150301a19004946581224040d0319480d1f00070091000864030f910080f2480c120801041010603040c2c03001001030032403000040e0000038010b4890303585928103080b5001071900412105540c40c403034500a900800c04c800030050303079421804e0441d80640707036203000c090903024002e0f464211805207106000800045410600b00c5215594840907580051365041c2c0c1c000701100c1042d2a42608040081d10100514845200045003071500794110010680c450080760b040c0121440 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 627664235 1250 627662985 627662989
    0x606030c0907271403010902010503070c030315080d080a06030b01260d0908010b01031b140f0316031b0806131127010f05070803060a0504090609230615040902 70
    0x6859076030300c0d5881c0b2000f42400d01da0042c0c000c200203038006200381e042c60f03041780060f684502078035040b5840d0300300b11000550900d026800707006c14501e0500000d000c5407000074511000140b0f11608025916118099100c0c0c02d0284d041c0da60341e000150000d40a01e00400c00400300c02240341013844852442e4032100e0158a00c0c1e030802812140000010300824014000220203214401042c5000d080400c81c83c80c4042110300100e004e050302c18244500c820f000603c82d070001c811140400d4007606043d0780d1340380030242480b968201160320800030349803843d0f4907160380018440300c1e000d50407030b114003400d0740d074620400c070300030110301d00c2219410f40b95800d01c484022110060246251003a0a04441011050020541881d40c14840341003140c9660000192908501201d94403a0049190340d41c07a516040456489011540110703007082c9001440c00070303c61158040381110b0b00c282c0c4210205008080e081e68a402400d03500b071a550405804540700100103d07180d206500080c10100b441b41080d00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 627665485 1250 627664235 627664277
    0x3170c0d0315170606090a06150201020a030609021c0504080408120d051f12050a1e0501050f0606160203010902090c030f07020d0e0103090510020c030a0206090606030c0907 76
    0x280c68001c81d4580b0742050b424124a000c8001429000160301d071910090100240c0d0742c00c000e8902d6008410b4a40442e401e00704981111028240d030100410f080e03000c1190090003540040d01c441c000a1170002d011800808070f0003220030500403402c15008103140600b48000400c0060822500d43d201000009041c5030103100d00c0c3e45d07000c0e00746030042c0c82d032004604d0203080e564010800b50710300d00010b100228000307681900c0070580703070b46548c042c4030b1400d246440c0c0c4c54040003020140007000070440e50000f861550700042c002c51311420003070080f61030348501a07448540c1900c5a95008030103104080b41000c80c00c2c0841c0d020381c001400031078244800d40209050600566015070001e400000300000c42450403042c1b50402030501c0105086401c82d0001400002e501021a040540780c010600074000c04110b5070340080780c280011941e403006810701031f82d04e5205a0040015006000000c0d20049020a26a00c41e40004e4054080c0e0080d03002041601d504c01450b210a2040e4500c6101e07010090708 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 627666735 1250 627665485 627665503
    0x1006020d052a0d0e0f10020d0f02070308120a1401030519050109170705160f18020c070602030a110105010509060607080c010908070201030b03370203030f070b010f080703170c 77
    0x44c440802d0640c0c800b052008407031030400c80c2e0707000d440e408076040d0900368001000c03074840400340742070990b1007a890412400e20000b5072014050030700c0420341c0a41c44c0301c052a0300e8020340c0240b800700f100e500c0192980c54060b00911002e403043d08000c0c0c102d150040a4030700350250390303c900000186000c4a95030743da40e90803402c0700124051000700b10001009020042c0c0c03104a007803160050046490281d4000200c0c285028011284100500c410b0740101140c050f14841c648070000d035000341d0385402e8000d6594109034a114009192001c00d000382500c10b204103410703140050300e002400d0f604c040c24000301da4040b43c021184000b04100b9219226400e101d40e8503100d220f5000d16070342c0e1606000060a4914022402d40b1030b4000300300b40440404000d1040e03808402d20340601004000c01025100c8240f070041c4040e4050000294a120b811942802402d0b0b076442414a995035980320484a680f010345401042d0150b4040c030300500202d600300c00400c4400702081074030780c5000030040701e0508102d410 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 627667985 1250 627666735 627666737
    0x9070b070b100b03041e03052110090b0d02040902060f07080408060109020313140c0a0b041701061805060415090e0606040b030304031707050303040b1006020d052a0d 73
    0x40207014150002d00c00754001420042107850440c10b0a8440313507940c489098005d0318162180c4115020907000e0010340380d61202024180c403802c0c1c0300b8808044044401c990102c144080d07180046004104c510607a10078220103041145070b074030242d09020050460110580e4006010702c8542d03c0050701000070003a061048462544483c42d2404d0b4601d03105c0180c0083e03204a006000300f00062640498040b04039801441d051040649105031605041340b40920302d4001d500d404c00881c40d1741d1050010022610481800a81084440200d900b25031050041010800a9803900700000303003075410a41d0001001000000d107101803000d1188131038030b80da0107d0708858031106c160045043c140512580683c0c1aa41881490004c034002a284d108030b020007030040c9071343c000303e80c2c040d0303614801e55001d981c0c0501100d5032420b0034103080010301022254400d13004242203010400910210b605124412241c071002d04101d002403145262020300160f1b5034003802002078100404000300080c00e080c2c03000f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 627669235 1250 627667985 627668003
    0x5340c0816060e07240c0f020f15070516141329030f0a110d050304080f010b0901061112250c0501090e15010e011107060905010f080403020d050309070b07 68
    0x43c0001941c44214207170760b1103420708200700341010150740000e0344220165102443c02c420180c035200141088184035080c54000d503490002e0a0980503000080901d00d0040741143e59102000c0c280700d407540f0003070042150a00e281505030800c1c1c10000d00d1050405d0340101d000c01c405140860310003441840c40b041401d11900c0071036059090406009e000306c1040001c02520754416261141d032400503a060519009000d858882028810148280d4010b409101c044e555400d0f41034555502a100c1d01c9259441924072030000200745000e540c920941084120103052140341c50450558181c00071b00c200714144600381f482101d05030902040000103445602e1a101c000c0c102000140b0318000350b08500300350102c00d01031003260a034101c2c2c410300c03002092a0074410720b07003100c0040300c00b8070882d061a085441003001c0413a04a410490080c00c0d250281d8406109450201d821a45082c095a024026801440c801034669110300c00031030740003029004035500d0581d02d07503448070158401001035401d020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 627670485 1250 627669235 627669239
    0x110c12090a0e040b0726060f010203040b1b0721060c030b12010c120603020f06160c030828120c0504050a0f08010f0603020306010b0d06050405340c0816060e07 70
    0x182200c00300c1d60140c030004001506000c5440801c5415501511036440303180211034080c8d081c1c3c800c0048401920640b01215141d66000350110540c0c942c1e0882c02c2c15500401c1004100360f13240c0240e00d981389043c8240303902c0e42152900c1d21001850150001000c0649070600706030076880307001c01c3d031100b501d520000241810706d00100510000b69000071391162401d03c00c0410140c0e0f03c41d1100181650105c0d8525030b10f90300030359080c0050341d0410300108040c807241000024060704034080d10382400f52203c541600308003d04a002da1180c030f4480303000803441c44201451140344507804540b010581e4107210b481d01f0703280c5000545804a580c80f41361401900c0a060252803800e004146000700307905028066103066600003525001d050080d10b0024101140f03205088111340c1040340103250281c010400b40c10880d218841c0d007526152141d03030884807803008940204c0c5a06400a00842c95550a50450081d90390f0341610b9004020b1a980b1092903102c102c04503d69115850320080442d009090040c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 627671735 1250 627670485 627670487
    0x10b0c0d0305091e150103080a0207050603040b13050a06050c0706140112030807020a12080a0506221e05010e16080f010504091b060f03110c12090a0e040b07 69
    0x2100010303100040500304000d00070b021000183c064005072502141c0702000400120892a0540c8030320f0265000314880000010701080c5401018a42510350945651549640501a182c0300a403802000c2d60400c030005076044a4840b204618544908150303450308429840b16400d03202d040d100c5803040100000c079407040080742d01c00e401e180c4104620a50a6616000280902038040a000340c00d221003d000520014400c0c401038450742c0d0b10483c40030032240c2e40040105588000c881e11224507103000c02045452801e03914202040584581c03c00303401d013504050b040589503242c149003911010a00c54040a0000d0152501a00301e20300c150520b80f0704040100004161114070a05101034601800b201d016000300b150b06540c1c1c00d07500820344441d02d2070b017483c180741103075001c211141c1040408640c080d804000c91890060030fa40502c0300001c0c5e011f2001d1148990010044180d00c0990301c12110f4031980060f08003820f008040c00300d076640d160b6000c08c0610040364120348086107941000407503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 627672985 1250 627671735 627671743
    0x40c08010b030f100c210504030e06070f03030f020d0509010509060105010804032304180606080606090a0510030e0303040302030415030b181f0e09240a090507050405010b0c 76
    0x9280100d0050403180c0f00c0303010071a181c0b00c2d121080842c0a85901807160014001c062400180c40700c0e21000080d400807000c200010001600c040b400101003490340401880c0c000c003610203158005117007030381c080c0300c40d6020f0b07000b4694101d0800e1804d0f0240601094074440744a0700d03200d21a8080085031038540384507501d08145051704058180300f06030013031001183d03002169101411070085051901e0120800d1070340503010f03d91040c00e9100c41e141181d80c02101c070342c1100b402ca42203515074450540700c01007080900d000d1803984c2c54000d424a10104118a000c0c80319851184035802e000030564800304c223090440d0b00c112010380c013503480000c2c00c02c506040b03141001c0b101c49092800f0800c55901b10f0029100c2050f2601c0b28400314407003004a40364a4045045821040e0218070704100d6039610310500c0002c2d507044445800343d008051600307819038081200b0818820001d6090709099440b4090740780100381105003511144107500010850b40c54900c203450180a050400c6038590a10480355464 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 627674235 1250 627672985 627673001
    0x11040807050613090507090b0f1206012618010227041b0c020f062a01060b09013f05130309091e0501030b1e062b050105040c0801 57
    0x40c2e008101850590070386800880a0300c0c0c0c07180000c202d9490f8501d08483c460700b00e07004494446800038031703000d80003a000d0041c0100c403c4141a5005941e4000054030300064142c105010300d0b03e45001c0780e124004410300d19a00c110324218980481010600c0242207030080805043c0092001c140e524201c0383c240002c203141c400440b4103002c0c01006e80302c0404003041c040b41200a0100340c900c3c2d03100310750f40d64519208ac0755010b0002c40c2c03900c4403803284a00184001c80c0d51454409442d200240d106010300410007039442400510b172804407004011030b1080c00d241e010f031a000c9003403001070700947d130041d15aa0a40b200d032240082c60246000c1c00004445000e000340b10641003a8110500181d0450445000c5840d4103100240f1a8511070780071200f050540ba4070201580741030004410050802c40550141c10000391031141d21006ca00201c08499080c2c0c0c0d059481031070b240c200c4803040300e2260480e641500011240c0d00800440d0744160030f54000303a5088412007091481032007040c009104070b007c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 627675485 1250 627674235 627674239
    0xb0d0507120c1d010509040923032703030f0301030308070f0c02010905060f070c0905010603050c04030b060d0c082b020148020105061c050d030e07091104080705 71
    0xb20301d11072502c0107050703d14075400310180900500e0580f00360341c2c05802910f41003240640b040c81070700760300d24201c651941005031040c4501c0d8201503114281c003002042c1c480403000000c09a80010045940718800c0d0603640480c0e50600c0100000e1100c0101c0b28007039402584641c0b2030240720b042000010f09208400000003080001045aa40160303901c0102c003400c9030300984010b552130b40c81001c071311001c0c414482c0140c0b0070320210600042c46c50751a40704034121001590108170341d0300d83c40640712a502c210300c4090048080e10001c107205143ca2038910054034482d03619245103903585c80b881c03414100c1c8001008100702501c0e0f6401d82d40490056401a1522148004c1001150000c003066142884020100410010050154020410314030000012a0001c1c42c0034562603100310007406801c0844605014651501d0584403011500710422086c6a02101a065a01c1c150500b10002c4c04403001e0310110b482501c1000441d602d25200d00080140301d540e6042d9110300f8410024a081002c1d80701c18 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 627676735 1250 627675485 627675491
    0x901030c0e06030a0f02130e04020a050603010803030a020d09023006070f11030705060126010b0109061d09070e091b03040311070504060b04090c0f050d020a090b0d050712 75
    0x603529554042c100c0e0740c050704002c4000b40c225210040400240624074550b8080c45c403044001c03a9103004140007500c0f0714421145440040c0d00c0c0c9051040c42e020a20580c20301d98014000b040c00076020f90090308149001e0000010001c0c055000500a501c02d50308110300281c520700d0103c10800c4202445055465080040416081940008104040070084201000740142402d0000a020302c11500c107241c204c0101e030240c5d6142d0524a50340a00410a01c152200301c6a2a20000106025500340c070007058560780a810310704981a01c0404411388006611442c0d0740e0b1481503592a0030086004e4011951090840d1141c8400c1c4012410060904040403020a180d081c82080c01d05c11030b03900940c58038224200d1003c04003944c1c504080e640240b42c0c03007410141c02003030b5081c103500900203d81c5041414421b0143c001030980e03140c180d00784c441c4c00080d82000b080d042c0782d5441d001814102036070301c5c2a500403039072521000300a80000d00c030010000d840c0c0080c480da031640b000c17409140d000703492020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 627677985 1250 627676735 627676757
    0x41d07020c0d200339040c080906130c06050906130b04060e09220804090c0201091203020c1203060a03080f0901230703230c0c13060311060f041203050901030c 70
    0x80d0181d60b0b09140d650855170502840710700c13100150a0050b08500c400f0b4010310400840741800b5111800444d4043c03403034410000040d5a010aa20f00707001d030160800071a601c0c8a06200382118268001280150804010410501d034689017001e002c1c02400f856107817944890a1800c010800c2c02d01800311803165108100f03000e4030400c6070120494452214009045200d807515000c00280500d03440040e070940f07411000c101c4181c0641104a0040c46401102030890004105500328000c095480c0c8143d44480ca01c1c0328051030841c0155000031006041240c10307551390341c5440d1103a01022100c1c13681e15011840880340e5801c02c002c0008200c0c9a01c2e1281c0b1010442483d00440c001d448015040080f030321090038600c140e02d0b440c10780c503008103008030369545960082c03169209100d8000381d005500d502c0000745000c5140c8945010380c6d51080d0700710b443c80d1005040144a4101400354010020108000500a000d072580c001c4007500c03d07103400d6203541c141400501166a101244002d11950000c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 627679235 1250 627677985 627678013
    0x60c030f0a02010908030405070501020c0904032124230102031c1401060c02010207060503070906120b09040b102123120705010e0102041d07020c0d2003 67
    0x180e035005560101416181c0c00e540d0000c80c05072010340b4000d42504000800d00c4180034000c0b8000c000d6400a030212140759a0300300a2290b418011034014002421640201d150041d00e211000407440412402264030203110801022802c1c204c02403944130503071040108200800450324584202c0074040e05402c000700480081e45902c655600301044403a00034824243c3e01c800e601c11407a910a01c03003480255a161100038200c0f01800323a045e8094494408000354031813080b402c90307100f1007031a40c03028600392800c3c4094465000703078605506207503280c0c44202c1003900c031000e01c0c41c031070781c028000200302e42010903450000c0442d98000c04587d00d0610300c40b8400003000e403403210032260700049050300714101e88562020300e9201e11029225000d100950040c0002c500c02401282d4040c00c020032115841518190807446944140780e014500080da032006141180035080d0b0002c100c0c010f4805481d807050005503078007114002220140c0c04400b0040c0c645e0001c2400044002d820b400801883d968205 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 627680485 1250 627679235 627679237
    0x50a0509130c0801090804090b09060f1c170702100c0b0402060309150a0209040c090e060411120903041401020604200103020405131b0c170a0509031b0f060c03 70
    0x6011600124214031408000c01d028808004290700f00082209075603034500808207a0162007080304160400030f098200b4604060810700130030700201159101e09106050040c0c2c101c1c0c0b16030aa4200d254862000c000c107111001100c0c40c4140640800e5440d20184104a90f83d1140d000260800c2180c050800c002803103503c0c403980054040300c48079201e5846008452070110000c000313001c03030440a4240842204182c01402500b50204d8090203a11a141811100114507100f0405d0b1106d14402084272070905034417203c030b1140841d038405d1814142080d00e400b042d4050741c6c040c00e40d50000804010384030081042611514092000e0300f41410300751590031040320075a108000c107452241325070780168021f604803130003484082c0111208443c00440c003030050114154841004201106a034003180c401c800c11840b6a030b00c03490226480e2285090307525503800000c540b2040c4a41040350000507074040018402c000c120001c5111020810030501070306903140681b060154a043c0644180c0e108040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 627681735 1250 627680485 627680491
    0x1615140403050114060103110c03070807020303040509070503040302011a0303031939030b0d0b06010306030c0902071205090604091e09050f070608070804030c030903120203090901050a0509 83
    0x45000410001084540241440340d40d01c0180550702e8005814180940000315601c03510342601d04000300211480119000c2c8030f17100007148240c00802140740007540200240c182035002504072400c0540780c1020450720102038401501040c808020081050b9090041864500c81c0313100c1c1c01c014205007008255280030181207000300c1c400448850b00c02071202d9001d0702804285881c07101003a407141160382d0802107080702c2440b0396200b42c03c820900d20300a000340b40c0c806c0030281100110308069290544021005022241015241d801c0040495841d20006010307129501005039143d4603480c00700e01d0203404922950601409100301925650390340c069508841c0180e130041107801407885880c0d0740529606416a182d07140809810520000280c001d1000c001c0c2c104480c1c0792520b441c1c042e100e02008594000015170803500080020b441a011080707090300c00d0810200803900c0c0d03500c016400b0b10324111000103900101d000d402602d40200114014242034604010300f906000106800c40801 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 627682985 1250 627681735 627681737
    0x1e0106050d08070204150b132c0a0e06010e073c2d17040f02060c0f12180105090312090312070c180b1012020f040f081615 54
    0x20480e80d00750f45550300001d01030b40300c540d000240140c687d0600c980c0d940100c8049107950328161000319211891113110151311b0827422032140410500d02207185107880080ca64100d1940301c0715034052901d010468617018006040304040d040c078102c03400910301404401c007112090410800803c03074268004c8104100c2c40c6242c050008a0901c0000799100c104100901410400100141800c40085002d0b240111a81c1e038554160540c001c0c000000d00f0419100608000d800d0310584005107000802000b4801014040d11504000c0404050901c6032400b0882040307600003072118040001003015074030b144001d00302141450400710101e540e4459521108031544000545260f4595041044441e40302d0207000840c0d58201c2480d010020b1100e510035900c1030981001c0701000b0342081d0048042c05240901140d14581440300d007100c03100a060a4005095400c00401c80c45024400090000c2c0441010360481e0500d490142807819543e4070892041013840c08003401854501c400d84211816a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 627684235 1250 627682985 627682987
    0x1e040614210601110601030809040e0d0e060a0e090f04060b060408060f130209070903110a0503100c0909020d051e0c0304170f0c012406090e271e0106050d08 69
    0x82c2d000180c1d51044030505103130041c45a4000041004080b800501d030f1003000703440a002c00615040495070b140465801c0b000410780c1e041d6190900d0400c2405031640214a20385408040043c03000b0541440041c0c620b0b0752201082401c01081c030541d8000d180072100d048d560640303401d103404a11500c035031010b4650b01d4507039411404580402c441c41020b8010b1340d001041c01400b800c001501070001c880a100c11110a00310800c1410a450030031026012164082c0c040c00c844464040320000503e0108088014002600004240e0b01554070103400003035004040010b40b810701c0c01c0900f000441c00d8502020003401001081030603d03045003500d030090b911a052a408010a01d89000342e4040d070055060000340208418003404015001400d624601141130010400c0340d4484001e64507050081d8408600144030410104002c080304d558804101116440c03e52811002032303420000c138144400e1a03a0106103010361050100300d111303c0300d80d1064003c10510f4944404a000718038041d202030304401c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 627685485 1250 627684235 627684241
    0x90f051c06020d110a020f01110d091a0702030c280b09150c19090305030a110106081e100614010c0609060518210904050c1e04061421 59
    0x741a4041c2c070381c18410600180702c10072014400e540d03a5007040030791800511075003030f918980c8071041c0700d0040f604119800c806d190269600320900074104000c411200d56012140780d8010071905085580035180c15800b4644d50900350070030302d14004064034044010103012100031440c001c100316144d1050340c400c41c42134891303481c8141c0a0804c90f4449072200a030000ea0100240707840480c0007406802c5818410104850b5010400c507816101800001e106500801c03401d940c05005503072102000e03408100109190340c5414003603040010045812202910b0f03080781000700201070101c04031202c11740104103c0d440c6408500d00c2c07586409944c141c144100c00038400103010623904080041030f003004052140b403c10646105810307900d43c0c40d240d140e0181000e004c15002d40c4140008034443c0404059040c1543c50b001c00008001c09071101403d0b090400040c0500742ca540c0100c0306000442406039141e61900c03030050503901c0c2006800700b0344042040400c8a01d41008114010455001c06001040c0e07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 627686735 1250 627685485 627685493
    0x60f090621060c11030703031d0c030a0204020d110f0706110f12040f1e060b010c03020a02360601091202011d060c0a060b031504021c030c0605070201020307090f051c 73
    0x4c140d40080c03050f18000010000241505604500e03003c10429039900d1030580303002036a80d11a000c042c43c4951503000300d000c0a016203840d03005031500400d0781ca0002800c044046408485a001c00032084441d00080b4440052100700e114841c0c400300011500380c070346820020544154401d0200107040035802c1c1000c1313814043e172050007035a9a03074061801c015010100854060308144000126011303400c0c09000500c0394421036030307140701550540081c4204481d503030820490301c1d079030503501d10800004d00b052000c00a81050344c00c1c0c02d21f10b4441c2110582002000103090207150703081100001100340782a00140d0348080c2020710703001925109075079130800d1400107084d8495401103c01501c191101801840030310780c80613482035021021036081c92990a010000c905003200c01941c400840e0b440010120f840382c01100c6003070703c2450100c1001190b039482000700c404c10390b14013005030740c080f081002154110345840c029080c03201401e0703001458000001c4864400807031401c0c60b40c1c2c20220f050100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 627687985 1250 627686735 627686747
    0xf0d0803092d010e0309060426190311151504090c080f070e0f0106140708070c0e0f0103080a05090a0902030108061e0f070f12060f090621060c 63
    0x3104190b01c1c61008860072030911898402d0300031a100d0154a0281c040d00c410300000102e0b1110900501001c0c1401d00d0200700c011050310304081900d00d0a05030020264440007800b001c2c40d40a41c50541302e02c81c04250a000301160041001090b06070f00850304415084000102d0940c010030f60b4040084085540c40410046d185078480108542d07141d010100e0100350104460002c0e0030043c0850f03402030781d52000f901c043c900540768601256802c03001441f01c0c030f204034030001e1060002040b40d490b1170060796950010754030055080d51004000c02c0103100782001030300c0f06030304074100304012125035040d510b4016183c8250325046080c07202c0003031420741c10b031a405440310050480d0202103489680d5401595280c0404031109002c035801102341d242c050b035070280c01d82c5c000d41a21b441c074482d5550724002070300c8503a60251101c0600682009403001000c150260718060a451541e02070442e01c1d00e01e01c1d00640d0703259001000c8214401d50000070302a003c40118080355000500814800f98610042d180 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 627689235 1250 627687985 627688003
    0xa06050402010e0a0b03071d1c0305130803030402090112031d0a08060103050f06090307121202070b0406060503060901140606131e030210032714030c0a110f0d080309 73
    0x41605004002460b00525011710b2148480e91101e08007503491840b20300500040e2032207030754080d441e4209034001e11b03c827000c40c564041c403070b00b481e80c5481c4003c240140e03002881c2e4001c011a500010400c030031420301e05216401080e0603204a00201e00c1980d0103010b2507038904044200110103142c0d03203901d03a519140c4c2d80c02480100c0c1902d810f541c4030305040c1e40701c08181d801070b407540c07065402058840714000121001d1720380042c00b003012140c440d003040b100448490401803000d6000c0c4000004103000c0704810380550f00c640c500255851414041c5811300740c00030480384099140c170000c261f1341590f41600980c03002e02120b5541d65a403080c0203c000d64803040e00003600d0421024040c1e4607d5001c6080241940d0084070007400611006038100e064a9951211420a905030001240b21320031a13198001031601c5001c222440941c8a03d0142c507542203403100080350307070121031800d00348600c01c0160070600005a9180c1a0a044c2030049000401143da00919001000002410899090100c031708 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 627690485 1250 627689235 627689239
    0x10f020a0201050901060501081003060c0c17180f0604141306170f24040c0305030a031a1504030f0519030509011805010e040911030607050c1c020a06050402010e 71
    0x2403200c0660340001d00070701c4201e4012049628140340030400b0760244807580c0c4203103042a4284042c0e070666a0b100c2c094464600040d043c006207c00050001c7e01440c08205203c1003c02d840e030f226071805036000001400d07003429600030980f0030324242c000d4030743c902110140d40002e40b9031a01003012700d010500141280050242c810300d00100403c1c180c000000d00050090200c00311141064000d102980740c0381000001600da80010443d042452151040158064094a000d09034999240c80e090308681c019000140040d035038400c61050a8803400380105d4071942034804903443d0681d07540400084c4201d00020b41808c241ca121041049000c101d1280d805c4040c15004111105500c0d01408076040b814656000c500501c1d06040d07080d102d005010700b01d070300595850082582850170302000f0400700c0c40a42d518410510407903020b8404002d0320b4003c038440e035145950303070740c054881606040c4454038040e500200070880c41c1c01e203607002840c0403d403a000301d4000783d80d896510040e00d40540300c8442e0340e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 627691735 1250 627690485 627690487
    0x902070201020a0c080c03060a0c02190f061509061a0f0306150a1d01030203070e061605010203161103030906061504080a0f060501060c0314030a021204080702131109040c02010f02 79
    0x417074010301c0400c19001c400070603800c0320203d858070141003098880b0b402c1c004005074804110300e03441030840e00c01d01c1d105600030442e04000c045103840d641c0540c0e0700048280e01e101071000d410050b403d2a0705c07070b45000381410010b0035000721140c08a5203091051078040b580e9003101002042c0565261602903039101c007441e0115680c0c0c100d250001c0c01505a0900103031944007411103444e602d50290003101d110341855900c1e03110010f070700e50800050750403481c054101218001071550000e603003440114050070b10104110030706200c94030024412039031485030b1074240c0c00c1441801600c000c00100503820010840b207407003141241c4907151007035000e181e22065a0340700d24a20035090091540305201594000c002c14003c580e201c180a83d0010410b64009001521403480503200c081103202441e00816241740c05850000c10105080703001d401510300b6103140c2c6001544000314a401070380e1036880046440140189907985007482e2241c00b030780000a001c0c40c0c07108840c8407001d00c02e501031580550700b01811 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 627692985 1250 627691735 627691739
    0x16090e120c0106360c0e12011a0409031e12090605060909061911072405220213150b04050411040305062d010b0a0215100902070201020a0c 61
    0x2a0103000c4501c42e400c6007210803c0b213520000b50304110002c2c025504051608400701e0000d0400041407074414020401c8000110080c1580c0c6001d00303d80521030a500124014134007038010140b00c2601000144102d10300402c1b0380c00030350040c42412a000c100c0c1184103e0300111802518000035003540c10040d2483c02c050001000a260b01107401400d0944000095a41e001c0c080b603a10310080d1b4082501d00c500780f60213200500241c010710001c0110440c000c1c280400b96171844074a840c1500d000d4598015421179104840d40c0e4840e850b80315101104000d16868039500942120034149800381c01208461111000d270b101c59048400d0282e1000541d150481e42c032262000145c00034090248560308040300f920000e0f041c0015501540d8124002d002c1545807000064010b895080d4034150318020103280c200f4604103041c1803402006060041035a034101040024100702d4200c1a146070650310506110000c003a90140c2c405540c1c040c41c2c0180e4680306800141e1400e100000c1c01000e0561007800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 627694235 1250 627692985 627693007
    0xa051e12070e160e0d030801050402131d09060a090f15020c1e010b06040803160f0f15050f0f040303110418090308060922060209060313021216090e12 66
    0x40a1034600c941d03122010264820100420881820401b800042d0910014043d41c034155004200c1c0013050020065111b80d99607042240c248a08000e89035006080c04005140500f400315a034040c030703a01070801030036800d607440e640f600b140701e0000b03400030f03d803050702ea90200c14a504440d00c1c0300b140d008443c500100034003040003090343d83c0c400c40019400c203002406282440300582d41a03d003440301550900c1c442d03541c003190882c1014400c0d110303002150a58404248080c005034100c42c01441e5060242914008180075244042c0030000310949440801c100b84494007241030b00580d25107000704012060f11511071090180e5045a40324040325000303a1140301c040e81c0042c5141c0e100e03889549465a84a04008012404540514007154804010f041c000e00b44107007100300b1803044500504203407580020580a030001ca805842d0560052440e000790314002c030a1150503e40700d001440c1d00302a80c1400d0309040000d100b000d0585e91940b503548007500341030154003507103040100b000b0340311018603103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 627695485 1250 627694235 627694261
    0xc150b012003040509060a0e0a0603110d0302030a1101023915130203070b04060507050f0609120721050d0b0603070509060a02010b0415050a051e12070e 67
    0x9441808610351400d109408458071003a4140410403102850a040c904820b208222000030f1185500010485000c07a45d800d5460b03100340902e0a09000091180c1180380800d02e4520244440c1c0c441c11404100c0d0001030b0707001040725841402885e051360091001e01c81c0602a015000880001414090700c03021105510158180480310017003000b401c1c10b0410314203513100c1c009024040030107040da000107000c1d4801c1038003c0080d14405000c0b20000c513928601107881c1d420980040002450004140b01441010815a5034001004002e400a420007072246075072001942c3c0c40040c5240042000804d00100041c40110804000c4020201d15443c0380010001e40c4250403680a813490610024110b082120643e4821811902e400b8548044482008400d411085000c011903403280300448040d00c69004a0741080500d01c0044261400c02e0308002c40b125580d00220300802207808510b508a0258211005134401912208426500d80000320300303000c61070300950b03206031200c82030001c0d20011702 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 627696735 1250 627695485 627695501
    0x105090a180f110403021008181b10020c010e040e0a0503030103060e1626160303031e020f0f0703110a032c0d11060715020304020120030304060b010c15 67
    0xb0400088588a4428800b4010b90001030f4001c400e5440003002d00707000d420b40a4100e181d0102c003142807414085128039000c980c0d54505040c0307054810000590501a18400b5103c1c05070016000944110b00024489028038000c50312658454400c00791441c028418400d4054120701501d40e070b0b46c0c4078104403010309402c070302c1110740740b04003040345d865a244080f42034291000b496142e0042c80301502200b1344006510000c409900454611401c68424281c110300294843d89000c039407017001c1e01c030310032840d40702054140e0b20b2401000000c07120540c20045518483c0349000d025290201c600303003200e45c64000303503042025205200c0c0320303420706170040319080c0d0085010502101548010b01f4184c185410704480e650001d0042c1c040b100010b492140032500003001401d281e08103c21503c83c550285104088144015030000902007556888080a42800c61110130911000403d000d920b41e01e100080014003480d950b44802c505a80c42040340b40c0805800c18003002d1499a58404d40c00140241 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 627697841 1106 627696735 627696761
    0x11010e04022503090602120d090305040509010902070b010f120f110d03050c0f0a020319030905090c0901120e03120408160b070201050702011104050105090a18 70
    0x1074030300d8188800b9450021424612904010b40074010036006082190400d0500800350118141220180c180c4008002001c2603581802c4440e405203421207170f40485080700000d05184d06c1d401401e200d60107401305d509180d998090618071994070384201004003e0b04002c05010408007800301440501039002c4e40d0703200a0b80000038598001419084010513800b103406541e0ba00200022000f12180000038038221845400103513403560132120682580740141c11080c10107110703042c410000d0401034041000d90038600e404c9441c5030007040340f09000980c2400703451886c1101d80140303004009400003840ca03000719002d1244400c6001481170782ca0020030020403081c0d9100c0401402c0722030003088007200504090300000c1c00c0d20303000b0f4110700c21a07060021411548a00000720760451f542420704581e5241d01d40701140303071102e9940c04058030b90603142d03450209064a400030000101d003 = true := by decide +kernel

theorem cover : BRFrame.Cov 627517985 627697841 := by
  have h0 := BRFrame.cov_init 627517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 627517985 ≤ n) (h2 : n < 627697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
