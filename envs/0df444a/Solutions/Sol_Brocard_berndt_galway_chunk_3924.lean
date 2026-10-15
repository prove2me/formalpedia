-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3924
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:04:15.844957+00:00
-- url     : https://prove2.me/submissions/84a75be5-4a0b-43c6-8656-fd3b3331a230

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 705575539 ≤ n < 705755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 705576789 1250 705575539 705575557
    0x70c030203040513090614130b04060b1012061502030d0908120f010807051f050c0f1e1b0307170a0602030f1504380402040e070206130b010605 63
    0x414030022446440d59001c0410b00c1c1115413010400d060a81002d800302c0301c05680e003181c6100c0e114200b009800281d17004907691039004400d500e150740e032420040b0013440071160140e4000c1d4003042d0f1100a6900c400d0039201c442c00d00c94104100ca944501443c032040294040c00c015800a0000309003034817160303002c4004140075040d13803890251900540c094000080711140d4041084038018044d5010402ca114040c1006882544800203154612070f5150628140c007000c0000004100c06603a5090201c030043c0c02200707040750808a040c0c044440081050b00a1004a02c1508140350185040f14950800361101402600c2083d04080045c40c40001030340b42c03281144a40e03d00a000240984000c52040f0b0380040120143c0c20180c07080c0c100f8541d504882882641001c4d9180540c4490a140c2d104040c8580c40d0348240e04240000d4808140d80118190380c002e00c08500010028030802d6050b100b114264250344150b9950100b1691070280140081c1c0100300346070060007910f02079001016004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 705578039 1250 705576789 705576793
    0x80601050a031b08040311071202061b1b01030f1e0905070e090a1403120f0703061205060103120203120411041e0e010c03090b0a05070309200f04020c06070c0302 71
    0x8543d545100c1914030308041200000702840200302c01e00d0381c4112601e00d0b914410340a0102e980c03825924034159201e42401a124075000204c00d0741c8286180d4084040360941c00c00d44043c520230304004c0c0a2071b0400c00c40740d808203042c282810107240b010311928281c40503600c1c00c028031210060700d607030041c00310060880f594454040c0108040381e8681004e4481d4115400510908000d40b6011240c17410341c1d0304003245075100b0303c040c06a40c402c1100041c0d02107030a80101c469039030750700b0040300507040aa00c0566048580c2c010081408404038400c0c2c144e9020b281110381c240001a0226528440c00241d1024405898003080019010b404043e40e9000001e00101b024080c113614801040150090b950070035035214a1800002001c0c02041e10081c0582001c200c0c1483c1d0303444a840310b0314010415648150746000241c40c007400380d48102510782e00003007142443d02001c0740501d007503c199040c0f11303c40c0030b074414050040d2400f40216040624508080c182c0703034440380720035124140a203030b0440540c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 705579289 1250 705578039 705578051
    0xa140d0b061c0804081006060c141018050606010807210b0a1d090d020c12070b12090f0a0804030b100e092505010e011d03160603050a0507080601050a03 67
    0x140346107401d60542d03501a421842d500e0303141019103450005003240481c01142010000c1204641141c5d4030091560044210048240140121418002402e07021b040581c58401c02c11032440070640810302c0540719000b00c40f82611800010f5891103411030300d60001400b14000b9103941400c03c240502c0b02c03180c0000c0810386800550000f070400041783c2100011000f07120010b11100019050640c0203401c8001601d141c40e903211000791102c00a04603036019040c0300110300200d0b1401c01c4030400a00c264403200303407100d15802030744030003210030390b48001c103403041c18100328408102082207140e85520100c15481d10b4036550f51a441180000c00714207013000a000002038102c406010341e4030800c2236401a11a5140e01c403040142d60241140c005c0d014881920240100d03600002e105051301024207020000e518140154009070607260380d4142c0500644150059408110000c2002c2d0f60451b1810b10070398bd940c2c41c0782d1085541c00c582c2c8200254050000c01c0d10b650241005188075002c9203808115 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 705580539 1250 705579289 705579319
    0x81f02040b03070e0103050f04120302180a09020c0d170115030207020d0501060f08061303031806021804050601050705070b0f13030b040b07050703021c1b030e0a140d0b06 75
    0x1039500112410f001007001c81c0c100c010355680c9403040e59440a1044411602400d103074544902c50030300b0f0420b80061540c00a081a0040342c2c0358071503951600c0040c1240380036071311042000040d40144036801c50501c0307101603030000c150107602c950304030000d031440c028580c0c7e01c0c00025500ca4007c080c050b40a00d136080007031801684490031014201ba0081002068441c0742098034040c40301503074000f10140e000881032003003240741400c0445801e40c241ca0085003000c40803001d00c2180c0358040009110074400a0b0149500e003400c06040c201e14412a001c20843d510000156914865114020050b03041f102042c01120020380240c0300c140d0120074900e003440031007008110040a15042901c40c6103465081004006c003907040c1e076920649030300e842800e180302c40e0f80207036a902c1604014400c6900750040d001d00a803080041107091900c005c881404000e0303d081c0030b882d800078514260300500d100c001c041a004168000c0080807400130b46010141c940316180e03a0201800600001d030301c069000f00c40d00c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 705581789 1250 705580539 705580559
    0x10f0803030c0913050f160e032d0f150703050c1905090a03110a05060c06130f060203070e13020414010318051501090b010c031407050106030b0702010e010f0501081f0204 75
    0x210455655504612901f0440380499140b100d440c01c000400c0903002d8141d00c6501c000c2800f00e8020f8400e0460320551607070848044040100c414180c0e01c500c01c0d61408001d0200001d84185401c01584007030b070190f118007808805441d01140c81c007404100802030001e03c0d6402d9540510f01e074286162460501c10041c0c0000c00711411540141d0301c24030085400240b030310307184501000900d41203803100e14000000000300c1c1c44400040c0f11030900c100c4c0f48807a00c00d1059804509a40300c2d4006011580c2c0d10745078030040c04030040e8503c0d10b0300800403128001810080d500c01c940c1074031a04070071000c059202000440c058440c6484038800d055801e01480c0004804201104109c2c810010324406c56050a0b0b51100729110090781c0c90400a031032400038046500f2100500c000012001031740c1e40c600043c1043c60142600740d10081401020b04200035810360b043d44100300c54000c07003000b0301100c40c0400003c8151038080c06500c240d034010500408002052062080119103e51000360503c0c4c3d139815400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 705583039 1250 705581789 705581791
    0xf020f07020909031303020603040609150c020f1f0b011209030302091801030236100807050303040e0a1d0303070e0a091e023906010f0803030c091305 66
    0x164486004280c0e4400c41c40c10399000382d405441c0c00c00850601142a80d0140b5880f090310001e0b0140000201260502c140c80d0482c880c0b140e04030202d1400c1250142102c40103000d48914500140191500d5004800020641c0e000480b07640f100d0040b220f411411180c010440700c5500c5043c82809040e803001031116000355100c10380251801a2560030274000d120080e880400180340c8c20301d07140c00500040c0c2e5510324540d40f50401d500d820200941c40e0b820305110303800d074400d4032881c001114200000e14400e24190070a03030342084251000310b075650f01419668000c1e4020302200710002400a10503000a512040e825070010f621150481404482141164015216280000c0c0048203900e45401e0a8400c8002048041810407001c0380c1c00403c0d49550001d0700548000e01c0e000030f09103c0311550901203224030050f0030138520450f1070b00040b4a610a001c00c4060819000b80000062011030118401007120206c40145185541c0c0f24140745007540110b42081d0b11071a0302403c44a40070a9200d49 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 705584289 1250 705583039 705583057
    0x209010b0310060503100e0c1b0f07080a02030a0b070504260d090e1f051002010504060c0c030c0312090c060c020a05150a0315090507050a090f15080a0f02 68
    0x35039a400c003203a00c410303501c1d465080101804000c1092081c204801481c03801164502d001318582c903119808080400d120f42004103071758204510707039a82c094801061840c4010b0201040703402c45aa0341d40c000f5110701d43c0e444060347c550454408000841c1880010f19030001d494a4241e10b000d407075407440000d0240b0001d00340d1542c810100d02c001685c0e0100a55000d02c061820b0610000b0724207003003441400300081406001e0104d000346510085400724404016120040c00d203441421b803008024002c00d400c4a00703503020743c1030210308105a8003405201c001e00c1d8040c0e407004041c040c141c4065400126400b8204041c6503030710b4407032012a0710340e00b040300540350642e5195103903002c0d80100440000d490304018858141700c000040f2106041c2c04503450b881c4241000f05281144d440301c142501090742c07021902c3d80c10b1004104105a10000802542000740c5502d017459856022000710010395014030050080280e410341c0d16076004000642d8006103d400104884e40c101d81c0300d4042e03801c41940c07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 705585539 1250 705584289 705584309
    0x914030c030d02060f0c0304171602030111090a0906050d020603090a0f23060c04091806050f04021c03020c15070c080c04062411030d1401030b07020c0d060c020a020901 74
    0xd03c1015a413000c4180c6e008010280500c0c214181074035040e5801c5c01502107000c1691001519031400c0f074844020000c0181c0080003005a040e1002c480c0032903501c504105449609804800708012003544110000d440e0041c102c900c03601c288d5400e01c11181d2000c0d0051040c4c3c82040c08860019a0340c1001c0050907110340030503158007803048024203e00f8a0008045000e800810821590004a20070380e4112266000007046014441c074007000f20f01e0240401521050032b0204000011040e4030100c0e004610944504a4141741d101e61031608034407100780140181c1010b02402d20b24a482c6240203011964075254034a892a5640d980c440d151803540002c07a5904942285842da140910805000340b410a00710902c3e81100d01c081c0c6405290070380b504003402400c0c0480080a0020401e840c641d14041d01c04102143d600d410305040300c0004d1100311040750040c0c0006500520105001c030905901801d00443c07030b10169110b101829102c142d0100710f2043c000d051016030780d8501018001e140440d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 705586789 1250 705585539 705585541
    0x10090501030c030b040203340b031312121415030d12020304031e0c06240b071a070e040b0414060f060f0a180611120d0612050d02060601030c0914030c030d0206 70
    0x81e0402000540c1d20070025100b045c8208003201c400341d00f0102f0381c0c1e544062212082c1100c2a0300b50ba181c03140100914a041c501482d50800b846a164600d0107901200200e11040c8104410141c2e12056501e032032000416461003525821001c3c0c01941d0000c2c42030801400202004006240d000b00c1038800e140002c00c00d1034075900780012445850b041e1183c007000c03926140841100303034000b00e543d485586040300f00041d1203010f108544000d101203650303e001e548407e0820341c4004040c001c60383c0e00588618a4500864901d29040c0310702d80c5d440280c0071840750113581d607070200300380c0f885860700c8590001020040e50720013880305d40040c645100d05485008900c07070601107410841031550840010b000642550104102000507900c0c05c0d4032804240694440030311842c000908050740c82070891200081d0f0f5a0f0070040041203200707520300f00340c0c2220450350791040110309550b185500c0d88042401000c050210030214900c03951490400340481c1d61540182000c00d180c0381d05800f205c001a08090 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 705588039 1250 705586789 705586873
    0xc0d0e01090b01051504230a08071403150a0e0a060f02072607020d0f0204060b0703180e010b0a020a0516150503061507020111060c0310090501030c030b040203 70
    0x2441c40c2c0d0140070305445110100051070000ca03c507100394080d40b82c80d030180c0b5001108022a24655801406010704019103079a070700c62082d551a0481e01400722078181501c1c00c9045410b00140c2c0381060382d80212000465200c10030004004e0940c07c003482d20a000c0d41c110500442c100e402114250003e485c00144d982c540780c00c2004868000c48114140030401058108040300068150303481c0746c0e0100c8034201403100070b02d8075407500300303c0880c000e404c181003800004d003140b80360014002c400d0080d02c0340851050001e4070000204040e000f0f1741d00303016a0800502c095050b00c0040d00c0614038500450f03030b4201e0b498590174a801072444030602c8014603031506101c000c00a5680c5200b98015081003825820603000042d684c5e019265171990200000c1359000039a840741104084811081e0141e441c90b0406d104815103560080b14070960500030942c0004000c661489402c0c102d035004642c103902c0c2421903444000c0c500004d003050717a0500c65a465a6144000c4840703c000d04203250840c0c0010810341 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 705589289 1250 705588039 705588053
    0x5190e10020c090114060c0105040f02040b06071a06120f030910090f0e10050d050609010605030c0603010b0f22080c010f080a05070306150503010503070b0403030f05030c0d0e0109 79
    0x611030400854025074610195034650003081810b41384904641000707001410040358240c0a0400010344a60a220911040c0101c520485861030700a0b9000d12142e41d00c40144241c81c80b48401c02050155100070800110605890b0507802190041001414900151003103180c100b8844407102c40303400000b24400d052030081e11504900c181810000703111032511800010800b40c61090003032054000c00040ea0711000c1c41840303c05400d0041c84207030401200d003402d0760350380700c115090300781c0d503113806008140e6150000d1262292040201040d1841c0c0c00d01c1a0402c840c1c0000c0c6d005089140207202004806030f100d010050880180115801032910788160781e0314211640008506105041100f07030070081d8070003a03140d801141800003181c0c540f03840604034028416a0310600585060000281c00d180d0300000540c1212821412541e0046d200d074182d0026104034440200840c4a0140d180a02c3d4020805564017440100303040d42080c80c4041c0141c01d848200440d5501650f54000c860100105 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 705590539 1250 705589289 705589309
    0x61303021f050f090d09300b070305090f0d120b040509060405120a081f0b040923220c080703060603032c0f0a0f0e161b1205190e 57
    0x5a08010711200d00101400751400c6d13031901440e540801c8280e1a4114070240440d504070701c080c1100c207500a800c0070305010400d108141d40302000641058041081010300146612300700807a007018080d80c401907401507591152040030500750b55110004102c003580c680c456280f00300d01c405c028003070514180c500241025140d00030a441c0c6001130150101c846c4c0e1115005502400c0512010521a800003c000c4d421803241e104440b180c0d000580800e6140c1c2c603411030455020510190004520910882096030b84200d41038041d804005060154070740001c4410303409140249034a0304115215a2914100302e030b1500251140707520341104104041d0310000c21190070010502201203d05c40d42c41c401c0c910321b108010309100303488006c90b80c00207544d1650600000c3c40d00814100e082655a8400080c0e403204507605d0f64003013911500d00030b6040c02100c40c9041d101500c403140012006a07a607501c0c002100e1040c0d00200041807001010010072128140c0031603507503484041c020301d2503004001662031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 705591789 1250 705590539 705590551
    0x3020114030f070e240a03060e04110409080c0312070e09070e01031a0405040f03030b011706040c141602030c0105040501020a150b030d0e031509061303021f050f 71
    0x6410410804003595540b003054009090b841d00314025030322000014900307101141c1e602e22421140c3d4181041500ca00028088000c443d00c050003a156620b441d000344190469020700003000800785516145400c3d8040d1400c00d1040403101e007450544040c09146800c540f09000c0b5000c0604c00f072140003030b0080034020f10001d01f00c07810780c40c03440c01010003840e94049007100c030306258035841c4000405041140c9100607403006082041985010704006611480c81c40c0700344c0100349048000d0100f9449800d5002c1e0f02c07104d82c4c020365016200c4100740801819016000010001c910402c00c9010038040d000349001895185641d082000c00d004250500b50304c0d880060510000300020006643c000c0b4100032250b42080300d884841c1480074030000940780020740c1c144d040c020081c214181c6078000180c01c0507001d0a90454030b44480e4031040d0810103038103441c0355070381e50301410004000104550b03180059034844c8c419288490042c8100504452a03030500400c032589542c02c1151103c812012030345e00274 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 705593039 1250 705591789 705591827
    0x81504080403080d0b010e064308041d132a17010b0108090a02040b030f030309060f01060e0d080a0903140a061b09031e0203070b09100e030d051806040e01030201 71
    0x140b08101002e02c1ca03076000d041801c2d2741c410600c0103440c881404081c4000e4034202d0041441c050000e2525803003541c01070040035100041d9110300030001d40100091482104092507980d40c812041e2954144e4918015924103400da075006480180c0c21180001e500800f1610509840450ac0c3d1618078250755090141a040140d00070400014003400620007441c01c0e01600c0020314280b40402180c01d02000d00618038140c8800001d20466140000710076110342415454890300d81d0b2210400ca84d041c801d0032500398000d10640180d00481c90000c01850015010f081007210103030b80e551441115041e804a010300f54002554400c280305030b60080c903440c81010000d1031049005c9040140100341c0d1804003074a400b800c0068031691400c413010070b1003400d0b001822189616640c0080c8185948140740c00da001c5c801c8440b000b10031a0041c05103183c1d054004020304960741c21044101d6943e00b01103a2000c1c2e0500201e40701409496000051004e400031100d003c2c0290705500014107440803d0b00d043d0600 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 705594289 1250 705593039 705593047
    0x10503010e0a020105160206040906030f200d020907170412090f12080a0c050610050406050609130c02100e01140105180a11120702060114010504081504080403080d0b010e06 76
    0x140c5e4410121400480e103000c411046a1550002c00c030b103030103140c0103c6055854a030300401440310280b40b041301d85114403110b41c0074001600e03c0d00b45400c41110140c0d08040314200b908010701d0050000c07603120070586006002070580404540d0707004404d540959034030b0300000814603006d900c0000e41d0090620741c09010126854403140400075103031490064201c1d540426580f444c217128090752060a9040000c94195080040584201e20200d1284da88658900f1000103581d080c07420648410010007031043c1608180c03140c1034000340036001d600200318041d91a140211714054407500e14024203840c00002c100d611005240e48014040e000346104202070300c031043d0100e03180c211181e4054084035010468080d800001d1410340500c01080c2050020801008001580001c0b2203040701c404041511a8000d01310054030366100398000c102854214880a01013119042d42854000b80704000940c41e00c0e680e03458076820307600305503264290780392542c038010300079a4486000b880c96607044620701d00e4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 705595539 1250 705594289 705594293
    0x51905120a0909020c07050306070810050405090316020102010b1c0b1012060e07030b01081006090506010203070618020607030918022106040b03030f0405010206100f0b0c120a08010503010e0a 84
    0x4070060500c0b0b561440d90300081ca0390b40e005c0090010700010030f030160446102d4105041c2c003404000341122100c030400e002050000315841d080c0a494040c0310120059840d01000c1740704071841d4102501c0590541d901d6200000045d1200341358040b030009101c0c04c046907a005840d02c1d4000b100040d10001c0061107111090102030408144403100035400000040e883c03142c2d4480a04007551b075070020b00034070203200001a6000700803030062000f2200c0001000310546442124086030000c1c0c03420b600507030007485035400003a00341e4000c8118002d450301703010103100603600041040d44071041c110300107111034000308400e0628680544080c0c611900550078205d40f20001c40d05a00c145801503000d1000d41c01280741d540300c90b40500c00060000d02684d0381c0d00b4101c1c0c500c0c3d1341d99002d44502d5005210349400a1512440b6008078401e80380b0000e61451250318044201c541604080d4601c400e03800b800b54030440301d814120082c4401c0381c40e5250807105602d070404140c2140c0d0341d424169095080407801d200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 705596789 1250 705595539 705595547
    0x9090a23010618140a06031104020a023315060a03110d0e0708240c0702061903060509014407030f0b090a0503190c051905120a 56
    0x982250400c110a4005036203048540589030715400012062001e00004030710143c030740c03c07007280e016400c214030101d503c42c240401c1c1120044e100241101b207907914280006c1ca441c0e00200340902041c41152034908103c007241c40c0700c52201851380120329590141d030150021b0108401d500201c0000b560100c0d030295004104144a440280400c16545100401c03100c000341c03040c0c40000d40c5501081081c0c0607508105680d400d0306011b03001c0f20307202d1248508801c15a48404410b1408140480482d980b01c402090714640c00441c01264414020300022000b817811003110f80840c2c44c07560b00032070161b01d0b00050255420040c0c2210005903100800b04d040d01c242d2400c0c0c102c4c100038104200048240c20b2601c00c441220f2800496498061100000f051181c00c0c2c031602882c2c0d0241d90010f803103456409100f40e40c4d104403800280542c0092100c542c4980c10401c4501e143da01c513040070310035070380d8650f5120304221401a080c010148403400702001e1003020068866002290f0503014078108400034054 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 705598039 1250 705596789 705596813
    0x12070b01270c030908030906180a0507050f2b1101030207050d080402031c0518010c0b01090906020906190206060603011d09010906020f041703040b030708041406130209090a 76
    0x986458448995181d02d07803103680141074103500400c00644a09000750304507141c80e01500c803400b40f0112080001503000010502404041d400b50003054020315040612a1801c0103000d01356000d92900b000c49041080002c80407080d8065840c07000540c802c030b2402c80304041c00710720050704251052003d032001860015854010f5840c1f070416102030703a50340c40003030f02e001a400a4800c840f644801e0b0141c5940d0420003520009182e1141345842d50100b0b80111880514054060400c01c0703c03400400003201c450344640413083c012030015180080f5030003c140c9542c00714801440d1a81020840c91440c1e44c103200942e002034045070404d00d075503d00401d0034031400d004809032649d00c2030350011a02248017584041002a4044410354a410403101d089106411610850240000c81072203800e640402008139020340d87c1c0c00300f0090a548441c6c008540008000780110780540f50104072080c0c109041103070b02c2c89810340c820f803101100d045105000f03081c1b20251028400f03610580e0b043c40020b400414403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 705599289 1250 705598039 705598109
    0x120e0a230309010c0f0c1802040504060b0a08011503060906030c0305010506120606040f0f0e15070804030f0f02030c011e140405030a0e0619080708090c0d170c12070b01 74
    0x1203954503546c180003095414903805041c0407050003003400c06038640c40d000307802182c0c400c407400c22003140e45040071200d900c1554041c000099600e40140102c0d00510242480300d03074985000a07416485103c11411100290401d40d8240d40070441001080824014994024020b80d840502c0c2d08003410a595184405000c15204580f1100ccc2c00068180382d501900340404440420302200740d0b59212245c5440b2000903400d00702080b0400a000180900b810b103022745d0b8950f541358078602d1000030403078180302040b003038008500080190108141c82409840d1070810204c10f0b00483c1046800b840c03040303c2c6007901201c1c8a0441c5401c00010407008419180d0440c0c0e50700300708581d60880000101c0c1e034070130703241098000704c01910186207981c0c2c08000c6a11500c0c00740c0703465805031600f4170741546d01d00d100c00714581e00c910b490700c4040c001549070460580c810b0590802c507050030740c0c221819081c1544040034081106010401005000d18039800c140101b8102d02c1a080800220306100704150171f094074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 705600539 1250 705599289 705599303
    0xc0c03020907271706240a090e010b100207060503010b130e0403020a11011e11031b0a060c1e0c020a05060d021215060a120e0a230309010c 61
    0x1e00c40c50054011441284003455050075451010b901000d06280714044c940140500344880c01c0d0746940054602c0c0542d43d00100f0829020000c40010004581488080c1d04141900c80c0001d0480080c000c42d01c031024000c0012420b040c072002031000c041c01032104501150f000c0030b001c001d40b603000720440381074a00b1000069030f59000c42d8106010351313085038001c042c074401d030074204028140d0100780c41030303030b0f511856900420220aa00440b80c40c142c1e1085a90a0b20ba0304140707241260041128881102c02102640e0901c402c281481060148000e000c07501078000265020400600f40306100786081f031410a4641d5100001134084144a491210000c0c804c117010103109550750030070007000a06000b072400e80e46401e4030208038013a401650307420303030602d9200c0c000c100215402081c0c500100009040b29083c2175920a04890710140c5004100020707556108180140d501408a0403605002c0c0903010380410381e4104801c018034000710f180400c2c1d0014000603500ba070b44544c0990813950032200c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 705601789 1250 705600539 705600541
    0x907050a09050a0e0a0807060501090219050c1f140a0c050906030a0b0d08210114040b0f090907050907020318040b01051303150f06050904060c021603030206160c0c030209 75
    0x40004c0581c040314600500ca1012240c04000005c0c00a01d6000c1c821541404542d9071054044182c2c0283c1800c001421031003610f042c00d0a100344050801c800341d0750100e85480c0081c2c5041ca004059110030156030075117440480c0381e10700c010148540c011010800030040341d092030030001c0440c052407500c14861000000421056103003030300000c006800007441703049181264941001c0710750011500d08001038891090500382819255106d0485071082040980c4040c00000c01c401802078000c0507a0042c1c080210200740c0d1920141c40e40720f40700c1c0c00d004100681c208010014210b10083c010021540201300e540101500c0c01103104488502307441c08502d072090400140c80d00e01072860300000a440c800400014041010310500d500e440704441002945039078241c03401590614082c0d590000e46c104d02280028550b40d01c100448941441590010400d19110745c1c0f01410a600903070042c1e0099061000074483c8180300c6204080504002c0f41c5817289580703e8110304824400a0700c01c42c1824 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 705603039 1250 705601789 705601801
    0x1201060923070c0212061510020d080a0513210e091b0a0c051c180509151206040b07090f180905011d03180402030f130201090306020a03020d050907050a0905 69
    0x6298204070b040c0305c083c0c440700c1c82d1103d01c0c001c8241c00645014490040c0c801d80040060000c542d0041c00c903a2130b511032100d6503921600d00041c100140400b901a0900c4400e00045844080180c0e0103a2080d003200d001c801c04400010081d241d0090601d00c21b100117400d20580b15420340d8800010025505116200e14611500b5944207847c08406045c5010340c952000840100c840000000006500d41a094200483c100d88021407a4021250010322000204440e01a9400703164608080180100c0403a8001090380e07080a0040d2000c80c1d000d02444107210043d0b4000e41564054080011880002807811021002c04d05456200d1441e165940640106015003900042800c0302451b12400011915030034440c0e076070340490704000032050901500040d628090003100d01503a000803410744581c4a41010395a80b4201d00c5049041c0401c0a40020001d1074600140180c0f43c501d0701c0c016124880c894854050b164000d0101c206600700840038405a51030141120540740c500c24006641e566803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 705604289 1250 705603039 705603049
    0x618160c080d06060804050709060803040e0408160506041520160c060f140901090501050c2103040b060906060a052104050102040f0f14040216021201060923070c02 72
    0x82d61070051880c10309402103102900240c465002c0c2e440740b811681c005586c0c180b800c04452190250f852607070002c21080000380c45d041300c1c054200d4019150503141040d070401c449071803801c00c0c80841c2c1640010040201384a0b01010124419030031000c02e01076902143e028401c03c230500e500a03500803201240e4003500034214107541e0f0304954000f48000115858080c003400c11041c1440a50001e880c00400143e420307441c1060b80c00c032075010f07111411407506150040d1515000380004408600c2401d429601c0780d9101000c40803a102080003cae513690629040145072081c00a003001e00845128062224940700d040494448500602c0c0094441c10010286c000680b20503c17000e50844c0036800b88000e028040d4018011103244020300c10384d0950301c070103490941040f0b105409031004003481881c1d050500f81c0041ca234000c00c002e000d00300a011a40016010f401c1c010722110140c0d50f962003480b10803441d21540070282c10b140182c039a445e0594911401d0400300074000d80402c044102550115110 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 705605539 1250 705604289 705604297
    0x151504080d110a0201020c100c3302090d02010e060c160611011418010204030c090c0201052401031d060709050f240f0405060313020a060903021806010e060a03050618160c08 76
    0x2003c04031170111100074080009418070a824190052b0907200302c500b0910040c8207d44c10654041c102103a81d16550700151072185102c815240c1002c4100b040c00c01804080c840120403130500084017520508040d03000f00703075400307a845085139a8503003904c124048085019640e80b141d403072030104035030b410341006d0305003e8011980001e01d83c51141c600440c142c4181c0c2c0100c074441845600800151742c88540d0b40452803441034004005401282c03a04a09510a4100260014043d44544241c1e142c03442d00320b280c940200c6108000135210340081c015442c12088d0000300304002c544128900000103c09204140440c0080d152120001091105d03407406d18151001080c0040c0000d80321305d81080e09000318004c0c007004030b1103034034004804541c3c02d015140407010340b90054000d00d005c0854819814004101178203160502800307486162090351400000c013680459545c0c04100c5051400034405144080e1181c086816081c904100610140c0019010070700720a10b000071090089040005403449 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 705606789 1250 705605539 705605543
    0x13020f060c0c040510061d040b100e0103060602030a02280b0103241416031508030a1205150d080d0f020415020105040506151504080d110a0201020c100c 67
    0x301050404990101107419201444283d800707026a5640c104180b103208218004c06000c10b03c001140c122207880b5003004541e54201410000d180c1c0301c548005817a4520310318031203001a15000501580c3d50389801000000c11303143c0000c6040038110381d40a52140c0f41c258243e40b03903003c8030901d4000145901020000f90342c10030704030406540c407810070810000d0800b2482c1d150000c46400000021060301c02c3c00e050100c00c0d940c3c0c0c940d68813589441104aa262107800d000c06458554140300000041896002400908011960b543d40d000014108680c840c0340b242c4070525100c200f2007101046003083d0311861044803003024510f10341c5081e090354040c0d885944001d42c40e240c0900351510a5500400650b081c140b40644280e000b40c104030709030341c01240c008155030080d00c08600c2c2a0460840c401803071000410b294800650451415015042a03005540d940e10688840d07415036000761252020b804d400f8064101e002590700042d58078280c0d07020060281c03000b0703030004500520442c4803100150b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 705608039 1250 705606789 705606799
    0x306010e1501270833190e011a040501030b0c0f0d05101a0306210a14070f170604080307030f0e070f0611070e1e090f0601051002030313020f 62
    0x42c415507020710b007003c440d0241900900c280c00e50910480001180e1200d00311a60b25610b0408612281500009102074020f04d211031800b04029548103140c002d485624444400000f004000040100c103500c5003c032046025610340030040c8027040d01c106d4840c0d0710420300c013a942ea5410001408003681d00c41c0208c0b82c0d400514103014400d00381004400401110000e00c00c100410681a1104032030740700030743d80c041c0c0c041e16400991284100188a600c010b800c24026603241241d1500e03044000032207056044040d03001400f06000c0307641d03005400c2015010f50000d001d41c910b20aa0200d0760b4000182010340b100c0c00104c0050a402c1c4a500304424100c500705041c0190000e0351682c0340e44882500816a0304840403001189091080310030300b1002c44558010501c10340b901c52a0b1030807000141902541212640d40000e41081070890b081c040d00b401c40050142c604113100440c02c0040c1038128030b01c00c24400c1740d040c0030b050340081540d80040086100303c2c940d060700c0c8006001701c540103125540003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 705609289 1250 705608039 705608087
    0x302090702070614040b07020427030507060501060809031b1c03390305090309121606030b091609050306150109080a030c030f0e0a030606140306010e1501 68
    0x285034041000740484195482c1c1500d004502c4c02c8600290040f030044001419080c45802d000d481c00740c004046490100d401c003001c0c0e01c0c00d1a07081c8881000d010064010480005079101005142e21455004200d03900e025103003801c145480340d072280b10f9605e00800008604c45054401802071240d04072100349107800c0c800c200c08224000c4e003c2d20b0307410044200e4042d000491040020341848100501512205640a6603210311050740141005032005086101c14003101d0155244c0340c0d2140c80244840c07004104846030318589004c00041500800300705400c1516400746511030350070ba1604007505466848164080003800c4840c5011039112070350510580c002d11410050440034100240000e0b030356402c426032030320802d60740c40b20300d20170060006920940100100b03100304030004440c041072030402139031140744c0c0003c2c4e02d90525070801d480165491508110014034000c4c10104800d041e000391605614042a020706480d004060f441d00d9809252402440d0f88602a262000340751054070640c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 705610539 1250 705609289 705609301
    0x5030601060c140a03080f180717071203020c0a0f05011b03020c03011b090e0606181c0b0a23070f0507080c070302010207051206130309080f0a1b030206040b0a09030209 74
    0x400030082d204901f40280305004180f40c000e00034903044200940800070210316150000e0403c10140b148200026800381103000325106804d21402c0d42001d0207940108003545c0400d04001c80c201c0c455100c40d034600180e400802080e6000b440502e1503007141c00300e40300d030301401c2d0070143e003807070112518650b05519250400180080c1a0303620303800000d05c3e03550202000d403128007040701c0e07007001c0e075030250b10803014001d4940c819400304800110002c06420781751217404c150702c050240c8150020440701d0804c0714003004220a0765106290315600d1300221206003880400c4410300144001c0c4c125820040544d00d0580c40d28020411110481d6001c40711550b292607500d00c8544800d00c5000032801400703084400200c41c6031034901000b00131070440203031043da2510f80c9001c10034040c1034411003d200a6031000103510341c050120240b0b45880c071010b0610300c0300341d107810780301d0b000a86103079a55400c19071800c0c005a240c3c1000d542c01c1d82c0510000903500d000c02c084c140d41140032580000d600c00c18001c10824 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 705611789 1250 705610539 705610547
    0xb040608150a05181e0a020607030815060322171305100302030712180b0c190f09030605040602040902280e15090a090e0f150105030601060c140a03 65
    0x4402c1d56900010010b989501c1c400d10351218040800034056803090705034511540151214038200c000318800c603103848a040d4080b07040d68010035001d8000c10403160030401c600040d2000c001c400e07002144c1240c80d5160003485100c1c201038454400444d810140c4500302041038070112003d6102c2090800e80c1c580d104801881c40b400390601446004600810068603141d0090094030300411868403081080c607440b4100800800711540030500398482c03001d07a0b50100d0030081d00d003030251812a51559884c3d40318900540395103140340702d01d070030440781102c00349009501c01c6030402a21340c446070200d0325880c0c909042d00640501e420140c203041c80014120400302c850038105c0551054204400b40c40412504103580c5405d19101c4c0d140c01c404104648007820f8100e500912095200803c6030207250340b540d0143c0100c81820303140b03504541c803500c0d040c0303601c00d800c001c40800b102403442d00b00b1807903042c100402c0e1070f641c06100e050144000d0b0741d05141007001a001500035080410111703000c0e0020b50030018 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 705613039 1250 705611789 705611791
    0x50a0b0402030901021c1428020a0815090f011503110a02010b010f08100510120615020732061b0106050103050f04170a0203041d040c170c040b04060815 67
    0xf50500c02c001041c1d1102c0703441c0c081c0300c1411400049104141d62100b030040800d00c41030300007402003c201048c030a17680d4020710260810141650b26401d003403400c210100e0305e0707800015036030348a141c1ca0803c20030020881300d00e460540d5007031003407401d101011382c81c1074015118016030020800c901181b0b10100b01c2d4154000001600241e0719810300c4104001c0940c3c40142c19150034130b400701c0d4a0400c0c031050502c40030a840c01e801e245003a50064140c40d00711021a0520b4002c0c0da01940040c002e81c00340c0794100f012030080d06d5801000d006407a2001c400c0c00040f417240c48030f0100711340101c0c0020f49560b2440c00381e13810000000b001c031300c50b21411908a4000d00c42800b0711130200303151070041240070350384580852003164841c0c0d880000c20300d20404c074104c9030003003400c400071484104404140f82d10b00300c0507025100c0030603004282d00d042c9858001c0c3d43c00c0054100100c85840f802008240c58030000d210400c0d810141c2d0300040c0007208101060190010f0f800c491440c0c402c0f0007070010740c007044403061 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 705614289 1250 705613039 705613057
    0x41b03021e0d05041a090316032606101d040c09120305030a05161704020a05150304020f0f01080f36010605010e0604050103020c010912051201060804080d050a0b040203090102 77
    0xa17942c500b0180c0a102c1d81c04400d99078465540e01c140401c100130f01e0041c148604860203814154040072400c0c58400ca04220300c885d074003c0305944414030400d82040d80e00860503028a060446040e40d14900c500f41d4009840351591207680c4602080d0301c1d0501426513400034188443c0d06d03c02000c920305000d40a0b500c140d510b01a0300d807070b000000d00d0200e000544a00c01c1c180386d42d69102c84842c8801456003150028009a91211043c000012183e444111110203103c40c40c282c00d440c1d01e0207004010003c05200410381c01103c102d1040e902e140e920014540e4060000c0303600300099141c0361044c1c0010600031101c0b50420300400001506e80c1901c0b901c04e044004400700134040740e52190011501c004001c01aa6042107003840188001d40c00307030b009000c401001e14000180d940300c540710500701d0848640b055003c110002079007149079210352461800f600c15030903e135074036081540e076069552190190303004015135980041032070718400f0382203490182001003081d0b440c0d08142a115000798084110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 705615539 1250 705614289 705614303
    0x1e040b120708090610180b030d0c051203090a02131b1d0d0309290f12010b030c07110d05010e0601050117060a0504021c06060804020f041b03021e0d0504 67
    0x6900110020303850b4410f0003030070046014140b6003101c1c2c0081b03010802c0070803106502d410f82500c01d600c0030010841c0e070012030b44c2c4203c80d41c5e02034204030b41000300086030070105040400c1000000100042c00a45d101d9054030100740b0142560500d1000b885400402c05581004e22250442c2aa01400202c1c5109184009401412410082008811140c20003c020620100c03041281c41401c080c0703400542c4001000441480400810075042e45c0032004030303610301c0d0010402d46103021310103d095000d020904606451070a00d0000000c20b40101c1600405140d0028102c0d02c00f0f85811141030420f6a2000003131000c60400300c00240c54a409006032030024003680318610042082c5031401d4002c1e64060700f03040075a414502484042e5000880c8110149484402d0146503200c2303104000c000c20040c3e40f0041390f418a4410010b1070350000c0405c41c0314a0500303003518041d0b0b000d9100e0082400e241c1c200181c1e503010503100c5207031116001600080400c40810300090000554002d030380304510a41d8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 705616789 1250 705615539 705615541
    0x506030604030c030305100f030501150503030408030d0b04020c0303070206180a020f10170916062f0c030a0302010e07050a0612020d1512110609061e040b120708 71
    0x4281560303060110780180000e80360141d610701190096103e150080c9401000540150311050480d600d103485a004840360780d9580b146511000c050000381003d02807c070003031880c040c03405414503680c0c010b4202da0850180c0d2509109840d07a200c1e41200c148501e581301f56a00c92030040c0020b5200c0f5811200400c4a00da002e081c442c2b14030022551800c0c07076900a2800000c20500b000b40078040c0e102b0a806400e200030089a002080c0c8035400440c81100d00400a023801c050021140c00344c241c80b44d2040c1d0a20141c0c1c0b81141131425010244a035003040300c01604103007212411428503207482c40c482e16805000e855a15800c0c0765064110030700e0324550341c0454440541d1482070000420083c41004009142d0080b07040703aa116075001040b141988041c0130982c41d01c0381d6140d180d80b04e400d134061036031513140e40c0058082040810614002c007404852041c00d02c03481c6000716640e88a085c01c00302e180e540340d00c01c0f011820040015100a014040c190f41d445030072000d40490071503400d903840f1010618000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 705618039 1250 705616789 705616801
    0xe0c070b18190b060a1e1a070609210212041503060504020409090b100806060913201905060306060a0207030501050a09020a0e06030c04050402122b0305090c010804170f090405 77
    0x100c04d0800c410506c00724202c2e2601e000c40c030036030122003541b018001030320030045500031849902074041c546019942c811205600005003144207401c124140b0159000704824107280080c3d038099400321000900030b040001d541100032001071040c3d4001030381c4944007240100e0402c41d550b00c40d0041510904d01c140f0561101c4005406507942c610404c00d46510802c00103900303041007950a50002c040442d50b20807120180d886000b480c070008041c024042d80c41c1c0d8039003550b180c035811072120b100a01d202a2141410314020503030500c00105002e02031000000d91041c018401c220352001503412400030420340c11302007120406440c070101d003039224040101010440e400308003002800b6502c014001c0c098000e004040c0000f1700801442a64091641d484460300c802003880b02081c0c40b00d011502c101c000342d4041000c51803100b210101002c1511f0803081120500000540c40c050704001d00300017002d6a1a803810507400c1d100d08454901484000c0b51030340300c10490101074034840f00d080343c00740a259224 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 705619289 1250 705618039 705618059
    0x903070f06050106020c120601060c0215030f0601120c02070312090806100501140a0804020f120114071101090c050d14030412020906040203130b101a03010e0c070b18190b060a 77
    0x447c20700b0350300e420000c010440103008130f600c103075482d00c054584880b004d0300907a2803960390001c450f040032006c10700d410410107607404054019000c0018404000740841d9a500940c0d54003c4e0000401980141a0b41c5400ea0b00400580d0001d020010440c0c0c003605e0b00700410350000c09648210b50208003a00104000480107206852450546a80301c2013240d0740c5408001d20700000080d83d43e00007550700b01c4411180d00a0203140000d9400032100441401d0822009100c0490f107015281c82e170f40b5001c00314000880c000340c0d4104441c03049840c4251628142444e4007000b8254880107418400010002402e20b0480d0400c10034900072600d96200f07503109014001030313101c101e81d10016081e90715802c00005640446e8030341c01c004030020041000703454850095015080400f5419003070008001044508003000c046544141e070f481c070b103908120456032818102380000d4a0f0800019421070341e080303041d50421043c040c04410030111078400f4801c2c10b001c07900c2081560300600510442c040420b8550f41 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 705620539 1250 705619289 705619309
    0x106080d03020c060a18120503040b0a1a060d0f050f0103032307020d030221070606090c020d0f0c0b07030f050601090819020609060f040f1a0409050903070f06050106020c 75
    0x24203025158030341d5060301d0813006010b0011465032800f0281b8240d00810b4008000120028641d200c840c0e482c1090f0600c41c240d0000200101081d6041082500c40000e20442d400b805400c141d401c00e44600c0c88140807402780064642102c6c2080c90300040040030210b6a10700c034101c4e0301079102d02c0245c1c103140c040140e032400307103e4400c406010304101c80c8006080056480c4032580c0603105440d003566060001e0f80043d21412070030404400085403a600f44146d0344110300003010903e800700070011a6103000794491440c5030b08982880302e0038421000aa000e52860700381c81e5803104000340a89030900c0c01500401c4003000d40411240341c20f0000e004c650140c140340041d2050071000701a200180d6040c1056004801001c90704920f00f17102849441c0c8540c0003401466100c14205c0741c0300c038100340644003ca01c040d4040c507100c84440f040050700e072400c081150155500c410300452543e039030f03500c1d852551044881c0100910265525802840601d60205042c0c0310035900342c8000b441101c08203c0707a644 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 705621789 1250 705620539 705620557
    0x503030f0c0901020a08030603031b0105190e070e09070312020d0e091306050903040513020408060f130605180a1a070c0b0f090f0a050102070309120807020d030315080106080d0302 79
    0x2000f400c503a17001c00d01032805907a104000a00b200e1924420010030803c0d100341d1100910140c0d110780900480090318901740d00c154442400400c017484038003a48580ea0101c0f485200f1008031a0b07804180c100350144540d9001c0c6030003e031071013211904420025130311300d0001d00c41d030000b450380c0280c1402032521907504c9008200b03442e019000100280c648500404000e41001400e100801000a01d0303140c0d4060030384c2d904441d103c0161100d00d014031040c14400000c01d60b80d150b00e801010443c050400c0901c0301c8800d07070402c100003041d994003c4100503081c0a21459940d500c00c0703580040811a905030079004200080c02d800d00a6120890140c4030324004000c0105071071080d1001a04d00114091f080303502001c550100c401c1840401d50f0142031011403441510941d400007403190900d40c00c07002100080080781205c00394140603803100e5566006d409002441944102411028584a42c00000381c0145181c81d49101541d506420360003009184070710095401a02100702405009100782c4815076 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 705623039 1250 705621789 705621793
    0x1c1d07061d0315101707030203010e0d02070306090501060f1e0605190c17040b030a05011217030601022b0e030307110d032f011d0705040b0a050405040503030f0c090102 74
    0x19001d808a0103c8200100801c0a94000301070016504560035184403140d52244003034200342e400c6005060a44a0020951000d90700200d038010301d0ba98001414400c42c0d0700803100040344265443c00074050422507012292010220701c002c12003140c003249006801503011510740300e80741e0390302003500d10740074507100c080b904080c0300c0100c4072441c06161004c0006104190103090300300b684000c0001c2c0e402c50342203441c0c105404003c000c810b2483c0d214003805400d80034030800364080c40d952110000c0c00c00f007020300c400c110701001050381a4000c0003130708204268a1078004820183d803c180303032400301c2701c030280b400030f240000d4410a9040110846c1e01030fa4002e0450062042c440341441883c0c01845011410003901c040341c5040c28003200c001d010014070601030007580c04102c1d030395a420f490890603141000520110305100340c1c100002d100d000c031303241520049038984404001036141c0c2030513844280c00c1800d000802c410000080002c5110fa900f00c40181595140d000e000c08e8079000307014110b4050f0f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 705624289 1250 705623039 705623053
    0x433050a0f0c0903110613090603030c0201020d03140c0703020102130b1e0f2208060f060405070206060901030618150507081e15120a062f1c1d07061d03 67
    0x542403c500a151f602111148944080d036111002d4084458981c0150002152180e241d02190303418001407000c5400c600e000d00c00020144c140001c0c120010f061072801003000620b20702007500070340642e0045440c681d410880f8555540211700b040e40000030100c3c0780c201c10f000e01d01e1001190310941d403032580080c4c50f030390901c01c0b400e10101c84180e00380e407064140c400380c240000d42110308000140c0f146a9401020b559400d000091005440740a0902e50a43d000395041180c90b48a80b55100e0440c0c1c3c000e400410042442c00459801c06401e650180040b010b0b14445031246415402070360051403950344e20b202c140c1c0c401540c519641804103607440c0814141703000c05d8040d000015103c0030724000505441c1001d03803c04160345440382d00c280c1120240c8d107034001400d0101124044402b00d010041c12231200d136105070001d545034420703100d20305260400010b21240480f010792102e001060700280c0c0c0000303000100001a40c13058a0321800d030005080a03013068980c6a00050000c0d1180050020044c0d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 705625539 1250 705624289 705624323
    0xc031202030c12160b042103020316082208030f06030703020102251205011401080c030a0f08090d05060114061206011b0c090c080f0433050a0f0c0903 66
    0x40d65010b1002890f10031002c0d098680410fa19450086c022417040e00710300c0c5010080088003d5000103004187e091610502c1000402c604040001e03070007404514000c145030b5101c186200001e001030440a80c0d20703003036562074030801541c0380003103000e050100c80d01b03001c5035900300401d0f55604444c04001e0060b0800620856032500b100c550008480348440c0c42c01c8004e450301407003404008101e80c1039440b60744030803100c507248044480c03880c05802010040d00b0032512520200e555803a00e02c0c0020301482c9030b20010b5050210140a44003010f03001007100d80704101c036003001680c9541c2805000540b00040350840c2aa1521808035050901075180302e4100390b4507070005440701d45c4a50fa640080d60b1803040d0000000303803403160f81001f512001000098000c108500241000401000070703000003001000e00c40070033300010210703225401e0200c208117039851091840390748500c8591062090340c1480244880e40c81e030350300100d0200040c0712041000080b41001200c03552000e12004d01008518032100f03030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 705626789 1250 705625539 705625573
    0x3020121110706051014060c1c0914090105011d011103160b070f080703021c0f0501081603050c060f1b01050402090f04110405061504090b04050f070503070f1b0c031202030c 76
    0x23a5555455050b40c800ca4400c0416030b0a0303220586c10800014003013901440580b1600e50a400d5041c020341340307100e4a604000000c0c2c074030100d281c2540741c0f580701e0b941e0401a50307100d603403e0455020604162510350030002d240095044c5000c2d42214040140d40014982c0c0c0c0c4513118041d041c4500d0383d45c0c60060740390884154020b60211100195102d80700d000c42240d245c1d540143c0441102510001400b903250ae0301203030a2041c00740032041004007964040010900000341c800900c0c4040b2501951030b0074039003105425109080c000380c0003200e40c141d0f5034001e00d410351101e8840e50080c5d030f010405070390380c4400c428465801c03100207251b00b01d500c039140100c0c2000c0e40312580c0954041c107500c0032020681c0100403190041e030311240c0141c0d1a07110080807801c044c01860b401c55062a18402c80c1d0400490181c0300c1d010080002c000c20940c00b0740801101e00ca440141d0981c010145a9800d260031402c1c500b845803850300080d40c45400e105403002402d4030000c1122048200e18003d002400c240b40e907854 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 705628039 1250 705626789 705626797
    0x18070f050307030b0306071d060f040e070302070b040b09120f03072003120123010f0302070213110d0e03190c06111b1002030106090302012111070605101406 69
    0x10003055995500c44d80151010000c150042d40540c5a55262103507903082200a250705c5828180145802d00c0320703c1082803900c0030740702911200d50034a00d29554030b61044009004126016080580c00410300080c000e0b10182903005840708001d59882020210f184182442122152040c849003080010f094620901001c0d000c5221901e44010388000ca82e8590314582082c3c01d070844500004004100c0b0303540f030116240c00e0013001c10209440c0059140003a1101078035003208d00605400259200840d561012140071080802d002000444040d201c507550b141c008075405102d50340340c00c80c60a0660000000e58801c901182080151030315240707001c503101001036000312051603c0e032000c14003040c4220094449111f44082c4041c1e00350b81516001e00e011040d1140c04840e620400040c80704942c82181003042d00d40a080c000341c001d441d460040c0080759100c00184001c0d00c2c14030505030036021440200401070080009118035156420a2a42025544603146035040111648951428444094 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 705629289 1250 705628039 705628051
    0x30105060a0b070c350708071a0408010603290c1608070c0303030c090b0f0921120a0e15040e131212050708090a02040e0705060409050618070f0503 65
    0x1441201d81e102a038100100580b50011503203000704200100c041540761503d819140e41170002c00b480c901c0d10ba1100d80311680c42c00344000c44c0034440c3c00c042840404070211401441f4800080100a5a030709110ba00c0c050301c02c80310310003142c4542c1c0180d68440c4182400340504202c3c892a4a0103402e444800104140300204a0b6030200c180100400f0940e20010600158000e0300c02040030700781014020b00c02441c941100040d01e0041c00807810701e114101c00e5500044040c1d5004480c80300c0c810f4000341c40c80c2aa01c1018440c0300c1e103110087c031070000c84064143d82c100c945035003100f4000c0e00c0400078803600001070702105203000d000030000c41c3d61030394490f0307008140842d5511520000f9150821940a88116440441c108038030034196040144942e0b9444011858505918280b420140e6120341621001070300c140e4540102e600d414070700b4000c1d480144801000079a95942d90311489018140480d0614810060600700314040c0f030325101300134450851541c80803d41c450461040e903068101800c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 705630539 1250 705629289 705629303
    0x102120c0d090b2b060902030411010305130503040e07090305100c090504020c0a08180d051b061204020f01050f0d05090706030903090e09030d090b040203010509070518180d050d0b030105060a0b07 86
    0xb00241c3c41d06c140c40254061030060000c140c400c0705500001d0280c803409084804400c00522441c400720b400807090350103403442124100003980b90b00760200c582160b10f4001a0403401800d00100345032140c1d40c08000e4050203034031884000d40d540d1040100300e000d1624640d40682041006100080d180d5004026001c02d40c400001d10800d207101240f01c9001c96003080b1855403002e440380c0c6142c00c50b0700d58800c1e09030048940ca40fa2101480c5000000c95003e4402400b50318a200808400e070302400548005014800341291a200204038404c0500400e4070300350058003031440b01041c0c8512030b0140f80c08042c0c041e1070b030380700e1f5620f0040786501d042e50081c103410b1039010900030640b42d08668000e014015001d5a00192541028010103007180e1001d00101150340c013802d020001e80c0c582d4511014000b03040c0a110582e42e44d0b4400c400701d440884000c4203200d014209100341c0054000c000351846035072180c001c111072213017182030608a0354160b4a85600c0810b07045c00708914a103000c0200709291243c91 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 705631789 1250 705630539 705630551
    0x507180e190b060d2d090c05060306030114070c0b090a0c051302040b1c0e06010e071d0306040b0106091401050712030f14160306030f02040b0102120c0d090b2b 70
    0x84400200d801d90106030805c880488030a05038807500f40600030514817045000c0240241307a58950240078080c4c80b0b0580101c801000040e440c1da003c2d401312090b0b02103c000c20304035141005c00142240008a0708607140c0d086031000c95083c001c00140e202c4025841000d81d500c4508002c20440710700348005c0e048005907000c05c80803c4240c615000f801c050822425400b24890005d10000280c691392001c4e030f43ca55200e40b0042000d0710341e00e4610303034020625082c450f203c59420242050015480c1d416150144590014070041018032407241d030482d0b60540d20030544a86607a8158007c1c4091303062180050000d2102d42c0100e03138000300c0d02c07225804604001620400d0141c1800c1130b80c00c1052124248030034101000103071881f03e402c202082da020318007042111f05580e60314140c4050280c2c045d009664070003070340c0c7e916402000350034480f003045080c0743e403106101e107901c96486004032038800c00240340d00c0b07000a01d840c800c4240c0d40c0480a80b40446940c00481c98108000d240c400c005010003030b107603a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 705633039 1250 705631789 705631807
    0xc18130204050919060c0306080102090f100e120601060f050301030507031209150206150315011806030b0903072607030f210b090115080c0a0e040507180e190b06 71
    0x11190035807548101000f10b0004004600030b000c8070038030340c0700109c940d0040004c1d5084c0d66074540300b4280b030034040f140c0040e044039082089078804082c0c84502c1e041046510007010319000007440c24100d5107a950388150f00e074010360f012210350100784401006a804901c0501c005a50007521148444803840c003e20b41a5940100c1021111010400401350b000002400b550900d10340c41510f0900d0250000c02506120310700d12034401805218140d54540b001810603c0d401268000d08011a00500181c000b800c1c0101082e45a0340407403002c031299545050140c9025010301e142c13000354462a02d9481c01c19009803001d60310072214001c0101000002c40714160407010300c101080000d4020b05001810712209000c1c000e14400681210258200607044048180d074030481c0b082d0701c611019041500c9030300740001528540b0b000d0348003690050501042092503a84071542d11198010b0300c90000b0300681d9403850342c131914002d07696040f0341e0b126000c0c103107503c0182e5040004100f002402041c135041152b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 705634289 1250 705633039 705633073
    0x110a031d1f02070806010609061107050603041a0a1103071206030b0c1b0c030d11150411030c0f01020c040c09030c0303050a08010803090f09060f0a080c181302040509 73
    0x44803100103603004141d511076a4104503403005000f1004c010711580d410f00c0d0f0302034104501489440200440803000c0c00040c0001c7c411031004020240070039449040030714001c0201042440e81805481c1207000003200e09000b400b5520f150014189840c1c03a64032841ca0845500ca00e80017000882c42d1180343c004002101d40318803600c00c1c10f6100080da200c48051425412600030202080d03051b0340214911141a5004120020000030038200071a084000b03081c00c604021940c4031800b906001242044288200954039611a941c00c030103941508042c3c84c108040500441c1c03409005900840b1b214140e410135501c1014001c400341454862a644d039940c24a142816400c210300060340402d8000c0900e402c0313041c00b80501050703c003450507c6240d401096203c203c0c040f00c18030421244000c15090b0300c801c3d01511040d480942001d600350b40b20002c01e940c072200151105d008a042c1d12084481e500f18100b040e008920400792a00c80102507004c01000e4080505a05264010000011491001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 705635539 1250 705634289 705634309
    0x122c010516030c050d050c0d05040509010b0c1e010204090c1107050909010605031905160303080f0a140403200a020a0b03090c120606010806010e181b1303060c110a031d 74
    0x41a41c40720b5847c0407130441c5504000500e8415024011b041c0018402c0e81c1d18400e80314152a4003001542c0c843c0e41c0101c03120300d4001da038804035030139520008c080d40301d082046d0014020b6030851101030195213021007089504940120003130140b50011b010604c51407601c000201e170800c00e10400400d10700c1c1c8943c006070a022a1096402c1200c800c144800c003007040500405016a103900c2503c015a4556107000c1e1840c10014580d40c0c86810800000c0c800c64600d52002d49821041e15010549103400e19000d02484654510030001c610840c0c01803082c18400074403081b58650203000840501d2414030001d01350f030809840c0e01c5450081d2403981907140c0b01c001c072442d814815a0018180e6040000002d001d0f040083c0c40d003410080211807144550304c0d240c0841100f4150060f58514940d545d41c140c6090a09844a403542040c000918a0354003440e80c1c00345054a0142404110f00344031550281d031281d60300c05602190f03402c65043d20010074040e403211a20f0091103400a0764112201d4001000d80709 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 705636789 1250 705635539 705635563
    0x510020a0801140a150c062a1d0a030807050a0219140301050f0c210108030c06060a0609031415010e040506070c031d0607122c010516030c05 62
    0x6a07040100810702e40d52180415108041d996610302d9814010a01c2e50800d8010705c170011311850301c08020400c48240d011007035031840402074016440030510407990f079241d01c9071071100046240e002101c82c3c03a07610071071240034031000780706c113110f030f4503560321207070103411121055540d402818062005a210455050f401c14900c4604440d501d0803c0544161540300301a514001d83c505001c20441110f01058507401840d880000354955103400708640c01596140c140580301c0d1300c200000108440b00102820112458005445580d41da440a11048200038825000002c0300c280c010004174601040d0821402080016038084804801841e07086101c223074001c42140d07403501e0401061060602074150440203602e4200c0c80455140c500400c0b00c0041c2003205501c0d074a9002030f4416070307503090883c1e100c2984038049e4203104070500c0014040300a502800f00b0000c1101004401900740c0c0d62000021580503180c490401070642c1e10b148810090031343c110f09102c800c101d40c0021810801484480341e07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 705638039 1250 705636789 705636797
    0x10c03091e170f03030402132d0c1407032006040f020108010b090f15090405040f0b0108031318060b0d0c090605090d060b0414040f030e101b0510020a 66
    0x2031504220a00b1180c5140c09640b00340c200703540c00112010003100326500103404881d13981074800b1269914004090503510f00708000720001c0d940d24021424401079031600c030501d404100d6000c41e07041c141c0b0580c5c0c0c01e858460a4180812481000a00503501d46000050041409078814030484020307180072400d0340c054541c51010001d000441d87c1c170100c018050548100c0e0079040c841c261001c00c1400c0445110284502034140d46001907121203400c2e030340c7c031a60041040c802400d103403c001500001c462000c0d503202c00580004034155600100b19204410343c1061401c1c942e181500c00740c20355200014110b200e0703032103c0001501801d050080c4c03003401800c28001501110130f80000c2c0c500702d07041d4021024002c0503c600403550f510410041d06003a040302000c515940b4840c00a4010003800c2040385d01181110140800d104550400c021824403a0f1102000050381c4401c12007040b5102808600148040c0c00503034604081d00c42021a8901c100d013218401103c5401c80c000360f0300120b01c0c000001e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 705639289 1250 705638039 705638099
    0x7020a0512030403170903242a070c150302040303050304111f02030a020105240f190e15090411041a041e180203031e07060203070e12070e06010c0309 66
    0x1b601c0c0034002250142c520b90461880c116944d82900c10b030f4000103100442c0308007443d0480d10140ba098240154202010000c59078940c16807424224810150054000ca5489800c0c031403460fa0191084809983d09600d4081c1159100c3d503503499a1034a401c540d0b038200266100c0d04c01055078880442113840610780285803038604c440002421200d00410800400e42e5090000355680c42401000185100c00d071282c8030f15100c900c02003603800c000500d070440f1165902c480090000c0300219040e0081d40c42850f503542c1d00703624400b0841d8202094502510214110b40c03104003a20f8203900c0b4442244410841014008200b000601190032590094407032004590f1305001d805414406c010110490304d0480b0144041034010950b640210342c4040307041242442c1c440050f40010b400d43c0c82c0d80c1c1e8089400d5669103814000141022600c440d410700070030303031100c004507071850200b42002914290511900c013540c8100c0111803d00b03500c0350a0b0140021701e1404a11002070313030300f0000d0a4111070144620 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 705640539 1250 705639289 705639307
    0xd090201030e0105060f01030903090f060309050706080613090f1709010306050a0b0703050c031603020a06061220060909040c05120604080f0d110a0f1407020a051203040317 76
    0x156102d01164407200e91405007080f01c103549141c04118099005e280024440607240380c04d42c0c8201064122144004070305400003a03031941504000400c610a006441c526561050262050706054440c141c2c04400c00401c1c41c00d07800c0542c044e4640c103004d030344603d01d480c0702922128101c00d0280000c42c1106800907151003d0350b05401990f000745015907002d1060780c5440c000071007038011020b000b81040b80000381840b00708002c02c16188812060035080d403410040d440c02a42d5950060000c4071641c0c24604005104480580907408480e0440d800d10103585a940b050b0030000080ca8070b561307000d1000e1008080325180c1c0b4403040c1c800c6100740c00c41e600890401e410408802c480c1071040c070705a84084100000103030b101059440d446640070029868244002200001d44103448034a84940d00100d291196079500007180c0d081d00025450f5001a01d8414201050030702c00c448000c0e411401a0008000d58182100f01c0e0501b1503410069a040907142e40e038a8462445401241110450200d07a05034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 705641789 1250 705640539 705640541
    0xd0b010312090e0c0a0c0803010f1e23040f060b0c0c06090d1407030602070803060109080f0a020f0f1504090c0201050609040f1b060903030e040b0906120a02060d09020103 75
    0x10081e92581041c10b482403820102070210380004141000d103610214440d41e4070350007603611801495004610b9501c941e15286010b00c07212b01442000e41c0845140310000c01c820806080c1020703104c07841d04440c010000301c1010551450013240564009030b45103440004c845c078a1140b24050006014040d6940140b0b003035080c41d10342c1c100c80d403034800d030020401c614030b07a912002e25040b12544050300495010481e0780207418121940d0020342141c0c0002a41820410751900461065809032600310900d6165806c10f43c1d545260240c002895200b031012101528028005403103502005122000b0444d07241c012400e01400024201040f01003c0780501c00402c040c0591032006c2e505100030802450410000b48100703a01400152489101f44240404d0094000740030003240c2088260b0510030790f035440c00500c803009903c01600000d1455098041c03c0c03038903008030948000001d01c18007940d162076040000008030314225184501c24031140100607280c0902410304a00c1d81500000e03416060300000d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 705643039 1250 705641789 705641813
    0x91c0e0112021615110a110d0f09170a06020c030c07061d040c031821020102040f0b03060d0b010803090103050c12012304050f01030606061110020a0e0d0b0103 70
    0x20714090061000055501d0078401442180e0782241040304c01000e01c004400007001c0030701d03600e9035161001459040041d0007201d104d00d1103100004403401081c08680c00c440141c104203910000a043c8942000801a11591040e0104040782504d038142e02c40c0d41c52404a0780002003e03102604003203200e048440c0140720341801890b160a01d41c50040345512807441c0981d4400354507220726507402e0841c0049200390310402156480030802d0403c21081d05200500c029180b0409920512034401810718501c18000e03942201c0810034a1104141840549809504018805038001000041303080100d04942811f80c000c01d0240091a40c3d03201000004003a98801000175025001c2007100440000344080302c80d04640c030080051182030801d0440400301c1d002215402c7d40b05040109100034006001c1c13040c1d040701c3c40742208029a40c1d461405582c00c04028003c2c0d221504410420741400b210742e0014440c840e16031a000b103c90300750070002074841c01407100aa558400c203200600420501c0f410f40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 705644289 1250 705643039 705643067
    0x6030604030203090409080f030a1d0a0519030e09042604241b0510050f01050a1a0d0c081b030903040b13050d0311010b0a1508091c0e01 60
    0x140409240070340780070f940c0b48101d031040d03400380c0c0d51500950184074081c000c2d03988a07107409448517541e0602c2d03124000501101c0c01c1d40c014040041100c0f0278401c0b00007038201406507000c00039002c0c44203411248602c0460900056080c131602034201c8109030b41d414075481c403803031181c2f0b01516061000300c180910018480c50704040c42c42c040005008013094581030a18058807000111200c00002070115143c1381c01d80700f0300d040ca821840b504c5040000c0491200070f0000b0203e000c011701d0b0b454414142800b035080c440c1542012007000d003404022100c640400086d01c0e4032f507183e840c00d200e20201c2e4048441c41d150703107000a40e0711800d103c0d0303c0516078000303070400310100d800ca419401c0102c2e01e6600c17842684144100100005103108440e409801cac0034004102c01481c1011f9107809050203003c1024007141e1407440d500e821400d0713905241c02200c64080e241c4c809129a08041840015a010a805403058080d403044040c007240e22060540804c08010716a81e0340400c001035280090a11104a418 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 705645539 1250 705644289 705644293
    0x70c0503030f0408010b310b040e1f180803090f03040306140a1a04021b07060203041a1206040b040e0f0d09060201020306060d09031b0c050a170a0803060f090f010306050603 76
    0x90480100600018040c0b804140d21071f001880c1140c80c014020f050620380c0040c1000100c41c004000810b291424400281b00b80308126141c44605084030141100700004461485944002c0307080a40911380c0117817204100c034220050002035629640069204071540798907866400031348640104a180c0007030b0a80014400d222000644c1e5043c404800d40c240e005550200318220003030000d044850f40c415030502030750304484d29410006c1d101c0c0e200b40144648842000b10361810b481240017240d00c11145121f1000d181d488900030840504614150b041d44591221000b403c501d40c02d0000d0a46058524024440041020005040310410340d0000701907900c14000c118039070301c84c401140c00742c44000c0400501462079103015581c0c030211054104020800b01c01b09410826900c0c07441082d2541254211442c0e580d9020601e48268210803002c9241c003c0186480090f0802c0003131904090002d00640d0300040c07640c0401c0304d0b04000c440075003070018241d0041051240c43c0c03140c00c1e00001d003500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 705646789 1250 705645539 705645559
    0xc0d05010b28080a05060a0902040803030a0605010f0c03030209060c0105150306090a050a1217090304030203070b0406020a03180503120d06061806120f0f020d110301060c0206070c0503030f0408010b 87
    0x4040c101070f82c01001c103907909072907030300140242c0d07110b150440280c00c02d1007003151102c0c0c4540701c883d50b82d041240c801c10410b141076804602580203030651110400696609680303000c95a40440194201e502800e070061024005010081c00c01c2c091144034070700500303891905d816100300705480c02c48040e04c003d000d0b802c6492a5400b050f004600d2090841e000080c00e0b0b0740300c001070b0742103500466101020700c00e01c101000f8400b092a000c0010001c5074004c4040f10707540341c0c80b0300c1c14018501c1340344501001359000c3c1c2a9000024011185c0d107503113402500c041400c0342d5640012a041c81c0203054215450000050401011304651040c1409000d603464440381016228294201c950781c00c2c002e6a0501c074107100021510340c05600f00841403918141d051080990300230592010350480d0303912440080c146500d2201c94202103056a04a9140d5900d0003800c0c040b940030b20207680c0c0511425903a0203400300d0003141d5500c08000130400f817401c44140a9071145000b04403800c440ca1004600e1280742801 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 705648039 1250 705646789 705646867
    0x101803021f080c21090a02180f06030d05180d1e0212070b09090a020d0c05040939050c01060303090807080c090a1802030f07090b0108040f06050c0d05010b 68
    0xc68141c04400343e1044c1281d40c4030b1581140c40c0024401c0000e6100c2060155503400802e004841030140e80b0911f042c0007161118020942c9441e10300f2441c10010b20705008034103d60806da8614006001c010380781c03915007101600c60302c40c0c1c00100c1091145000e00701c52907a0450402c80780401018003210040c0c2041400d01021903401d10500505910680011001c500d09148550464a00302070340c400400401c201000054015040b52081200e01890543c81c6203410031a207007007420180c0b070541504812100010080010008030707507040200001800008a2844244183c0d0b01a500940302c3d40c0c40a85008030240c98801e25400c4405d0f1500862880310701c58071018141038220741100f80110300c000003000f00250500c0701a0010703601d0300c40c0b4a1500d01c5d00710045800819204500414400703401c01c180156201d070800d4900825800c891841617010921544c040c6421004c0f1502136898402010086000d40e04281c0240042042c00078070203545d00050200c45851208115a802184400c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 705649289 1250 705648039 705648067
    0x218150405060a2d0e090402010801061b0516050f0109120f020d02091510031505280f1e03020f040515060c10051005101803021f080c 59
    0x621607a401010049041c10515006954904821610843e002c011800041102400349401e81c00400445d03103c001c0c40d0741605040ca01c4074070490701038440d02c0499207405e4007101c400700030520425195088121240c00180705008184202442e5000303081480d08150800c040c1204c902041c90500002a108010402c0c49022100c8801e40041031160340030442c0c000b080000b000203100a500c030480108002241c0341c98282001000d20595002440482c550016000c540c1c03403403800340510800100030005460005103103a1406024005480c4210076802460581156a00419a9581450310a221060302105910590780d070b0610038414040c9140c01087c0c03100c42d4064200c0c081d9846a00050300580ca192060a500364041c0455944080750103035184c0b184c0095541290050528010401c00c400d6602100c05403980144a20035410300280181c818140d0640410101c01c402c040c000003503a20300c001c1c80e14103d03c80c6440400405a104001c100b1480104a0f6412500a00011645600c8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 705650539 1250 705649289 705649297
    0x402040e100e041203050601020a17180402040815090309041826070233090f10050319061d0103060507030501150c03030b06040b04170a0201022a090703021815 70
    0x4c00c0c10005070a81312400103c0c101640100058100c1c180904401c052540c1c0728000d00d10700e41c0e440d50103031000412104200c240c3c41240324a4045e54010801101142050000c05400c0365603001128501102d2201050a90b01110a44581d0003a041205424054440c0b07083c104241d81c140d60003044035010030110301500514802a003c0c2c14102c880b00203000d4113031402c00f80d0348943c40b550701003800849106c8040f13910403020310340141010003150301281401c290b65818001d280c0c40d698110340e10504aa40c041110f8880200000c1d00c8507000a40f41190720240c2440010654180d000c540c1142000d42c183c41e4080c250701d00301494400100326042410030104801c01e100c0c0340c82c034131015507820214007402403075011640c00000024006911308494004100b20b503210000004040d404805071611081c3c1144081e0140e0005183e400d035004c000c1003070200200003200c180000e0030080001c540c1d010b1044a801000c0780c1c3c0003a50900c840d4400100d4030900c01c040325600c0d05202c200501c10302c1405 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 705651789 1250 705650539 705650573
    0xc1e0a030503070201091407090c02030f0a030b06120108011d06060120010f06140a1a0f09040e0312040209010f030f080901050c0a0f1b320402040e100e04 68
    0x804008a03800a10031340000706c1243d08034010020345844144c40c183c4584644c86203590071440c20f0a00300d40c050010055940510340881c040d81802401d075410740c06800b001c010240c4c8940108582c1d011400091201c40c040c01c0c0c000c0001940302d02270700e01094010110904180315612013420403119070380c44084180f0b0384481c420210140112681501d0150112800450703c450600402040c1e50010126121085404540c00400703103990710969440e003030203c00e81002e880010054218000d5080300100001c103030181001401c800030550050864100c80801c020b200310741403d110551905a0304c05000d440c08003401c2c14014034580e2035002d58044202c00825480e408650034015038054000e80f408081804140c440c0404a4038140007100320034481200c0b001904d80b00c0015016101004d041074a002c0030320242d2031481114016041600d50b00401c2c01e2040054000200341c6a90014100804402c1140f25050400810180300041346030085404015031000b000080345014141041c40c0c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 705653039 1250 705651789 705651797
    0x432030606120c030a080913050108060a0c050706051f05030d02030d0e0106410d0212010603061509050114030a120203040504020a0801080609010c05030105010e061e0c1e0a03 77
    0xb0703104a564604001c41c41c00301580c1400b440041000380289800201402401110782015a0071902011006c031003081c09080c03a81c1e408040040e1030700b500ca500103c10100c3c01d041103824180b60307940b040c0c10740300c040b034003c008960b524440c0060040721110101c05408110701805200301115002917882c0a8000000f45042d100c0021895540081d48900c01a090b08030201890345080c41e0307990300307021504a2015084880c40c01d17141c2a640228800c1703107040c3c1c2c014068811191140c00300f21112038162110451550303905400270018040d40b00e1403903c041d1000d44280e405140265080449a05900650030501ea000140c1066507010a4034045564054007440310315001d0081280355004a4002982061001032601c5c0c030389403c46000b5040710140c00441da0180e45284120342a9203e22042c1c0002c074109000602c01d40d030280c1d014850b90b0300050202e0342003c001510b6080038240d8070308070041ea11b000040c411075014080c4104180c0a6483c80300d00400c60807003005507560148401d01400300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 705654289 1250 705653039 705653059
    0x61209080c0a030c0c120f0201050a110106090c0f0503100e041e0812012403110f040f06230409050402060705010c020f0c0d0b0a05070905060432030606 67
    0x1203203090a940c928400e0000b22a041d445502d005410f042030f407001076403048100240014a200c0c0605012445540110824400309050b801942c868001a880c0c000f4001c00791203801c2985000d02c22038005143c0c00780d012800d088034440180c1458201d06550341004401c00c00c01810241d4404280111070402554a6042c2d6541c20329039044528090781d006a1102010f0541c02c3c007030144040d002024001c4040089030760790b01404c00110082c0d000c8070100e00d684561030801c0c1d41c0aa07002e000c11120328210185445c040002d80045644a50410784803142040700500c81c056200120128050120b601000c0054903052040326a000702d03c14145803c0c2c03034100040854271400140c40075958004000d0040241022029403501c0924010025600c00c02201c10780c1d42c035003420407c0846820607500f808c240c580400c6c0f04041c0c040100000d0078403402ea200003c164543d00000d200820440391050300c032000005441a04d0000c40c80c40542619044427204415a800300f0499001407003140d01c2110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 705655539 1250 705654289 705654293
    0x7110102010b10170c070f0b040606170a050705010f210605130906051b1209120703080108010c020106050a0510030b040c05090411030f011703070c1815061209 70
    0xb611207242a103410000001c1d400410503009a1449802a01d80144440c1e03960345402141d101e010301d5001410303101140041001090101510681141c06103101245458445c0b1404004801d88021700e0415407040500d1003e201080c00038501518003460403000000614000a0405549540ca484480c880082c6860001071682c440402468050301c6181902152985200285400c01007a243c0904041c0021000c0c8001018022983d0b030020180c0c0c180210906c0144402e14010036030f154a12804803482803115001300031f0940c5034403035600c0104075818140100c4c2940da000400405580c10801c2c284078075503035a1120004d54005803205c413500301d10014220081e12501c90400d4109203004555205207610400501c044a02601c0901c40c00d86241c00c020606c0c807045030b4031f10010755013500500120301d0000c0c43c686264130220440c0c0c1070000305d80b43d00303071180e9596022441d5500e21140445a40c0d0701c0e401214251480c4894100c0158900380c0060440190002c201c0c0c500d668407007110301 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 705656789 1250 705655539 705655541
    0x501050a0f0e0307090b100e0108011203020c06030c0910090b030103080904020d1407020c090402030303060603040525031401020a020615010207080f2506050a1223041b0501050711010201 82
    0x101c2c03000003001c0343c0303805a65084d04d4000303154070254a4001c001a038030001300e03680120b0070250b4800f01a51804840d80c07802484a4046205000032011401002138064003070340e505015500074000841d20603903400c006400c0002400e90740e06580e051007040c031410400c46058500b686d0450790040a00c598076541200054020300c2141841c440c0203250900c1c482003410a503403001e10400b07a030f40031141c840c0505020000b0329001250000d5050b481080010700c54207140014503001440360045072018030035801010f01c001c1c0040e050181c1000b40120400078045003503088000003004a008603d0003d840000035100e60340200029189607025030242c41592080108000070440001610b40d442840309000d525000c4d081c11740f1b00141450240201407001686140040301e00b542c45107441d2a078940410f540b43f65030105807404e4299200c42030920100040e10658110403002104a1030f4a07048c942000240c83c0c10080070000f0350080c03000d0000e640c01030102c1e1811600001d004c4006a03c94004038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 705658039 1250 705656789 705656807
    0x70e07032d09050111090d0f03090b18090f07050901080403091706090d0e0604180603170309100b0d0201081f0609170a02010c0204050a0b03070b0903160501050a0f 72
    0x5040680750001254200c1182e03403114507200d104400a0110212032880c03c0c440d40201c003100c0f03500c1201025100009041e0500102000c2d1003810b060201c56a5140e02c3c184503000400c5441021412060703111171440d00d1074030183d01030344000416109040502c001000c1d8000c850703103a4140451140407601785406114240b0051402900e610b2121500503060b03078441300e06860b9880d10344120050085420b000c3c9007519000c64000e0b05003820207240402455100f4003010307082d02c550755105408800b00c0d051805210298000800b090703501d0410710185450040c80400160505250200442465655071a8203000c00d8091078012080d842c1c442d2100c0c2032603415000302a018020040000d51150021644c0c02150000b0f124502c803a00240b81003a10307000c0c0403c009000501c5051000010b2400d40d1059810001c4614000381051809003c6032a0420503004045001d00200d0301010500c4c081018180c805030b019007280741c06141a001030414000d510169090014840408001621803c0c840c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 705659289 1250 705658039 705658091
    0xa0b060d081c09080309010204030c1d07360303230f091503090705130c025719091d0106030b01030c2112050904020d0518070e0703 58
    0x1045e42c2c0d050440f0124002d601500c8202ea11409806001440c0c2c4000408106181694403040c030241e59061022600c2c0c88011001b20556481100341c200c15044c0b03541c3c40842156025191703007045045003006131000b42e240c606805d10201c2095044113114810083e00d4100311140c40d030688403030914001600460750103400304002d54000c0f0421050722400100340d0300300c80d025144401c1c0040525008000e813180840080003503404210321510240102c0888541c0f40f0b402103410480c0120380164250001039401060200c403101c0b1050780240e4080d0041c21540d400844092170f0310780d020016440300646038441d0380413860790f424600d80b0803031b41c1c0900103001c1442c52000304115503c92500d05003462080c00280e4160400c1c4d84085000f981c2145034088541b20781d04e10712701c042190f07a900e10341d00c511480e222041040600c081011a01d4600180004e03150400b00480e5a1801403803903038440d0101e01481201c0c0c0d2000200300813107070f0982000c40c0c10070460306d00841d0980581180a00035008a141 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 705660539 1250 705659289 705659303
    0x3070314130209130c150509041409060109060303080402190b0f0703030c0815150408011a0312033102091501021b060a1107170a0b060d081c09 63
    0x41107401030592a0310320016108562100c8242c89624251110344144c401c01405203070240010300080013a0140d03900c41c1080b92a0046c500020305001c6825115100b50410340d0320140420321003007a6041c8540c502400788560f040003910320b1600e00405c441001380c4040e00070404c0b0b00250b0003480030081801d02030806041d1269503882c0602040165a10011f0b00707800080c40c010802211b035110b00c0d403d45c051080c40005507200c162600c00c00c210982044490085e0900400c0005441e46080c024030303030300005000c00c0403100c524170024503007440028400c1813628a02001080200d01410107408200d4840c034140c08500000030720f4080c0880584107001c1c0d4040407403802c10140885400e60800d902900ba0b09a4410181d810004410010a10041c81c3d210606004a4014510a055610215100078111098540d5811641484400c0150441078507000f4450b11303070501945080040e0440001d48661308481100e880e4648a8003c1c46030340c18802400301c00701c817100d04007074211306002608050 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 705661789 1250 705660539 705660541
    0x4020d09121805090106030b0301140a06330f2303150409080d0905071d0f070206060906010c0609020a090b03011802030309120f0a0627020a090203070314 68
    0x1c09400001d440088000052080345880c1ca40100c00200901228005000d2210741d900706003050307000d0301000030215059035903501c5400f065190781e903845002e42d0030000c002602c9410460390000c1c00d03c0104c20034203030001480109803003185040c61034984184a1138518290100460100d501440c40c02c0c4030f480341d164030688060640c8000300114065400c40e07940c201c030b801e88007060005a40c025400900800400c1c801844040d145030000342c1d405100e8030139502400e40724007181d0100d001c847c0c0c50158002c1e00b07600304441440300070701042d00b085490004210701c1c0740180c005441f03050028400c1e41081210550f01c01005415000004036550041007400c0c00d80c1c1b1050031a00900e00d0107243d600c02e41c202018043c000c200200a00e218540280c080d600e030075095414046865041c141d04107051007011003481d0f042c4014410103c51501c41d00d40070520492a415040c3c1c90404c5c47c115000c4920002498001603070b8100701d020481c0c441500140e1a60b40c1e02005400421b80c00c05803200000ca810 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 705663039 1250 705661789 705661793
    0x40b0907030512090a120203060c09010c08030f0702010c18140607060218100306030510020c0708070b090f10050712020c130608010e0a030503151f050711010e030a03030b04020d09 79
    0x80540100e44c1c1c169612600690754900111103910801c5e00690960080c03004a1100f0304894000c002c10001030615501c501025510701002c1e5208940910041c05c4110070f00010b964203008142c451121480c02c1c40c0150302d0300002088142070752040e050403104061074440d00340c4602c42035900d00d582140d01113480340e1807a1080000014181d03541d43c42250080520700100f8028810001034a4010f130040124041d482403040c025806500b406000c0d10a03280700240f40901001900060480d1016040d01d8000302c60030302c031452280c8401c0b41d11404843d079041840316407281c184c03104540c2181401c41d07181110003003641814070001c8115045401100114a080c0b650f1708114100c800d000700800c05d481c025100a0b850b041d8405008001170780030000300d0b0007441202c50000c08088002d20740c103680802c6200c061030032071139022142c0c041040840c0074400e2103140d01445040b4403013070134131400d0410f20000281d240d0402080082c20700d82d480c03900700c2140c3c6032981a11903213010f402c1c023080354690034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 705664289 1250 705663039 705663073
    0xb0a110607141b1c08090d091404020d061502100609020415050304030c0203010e03090316121202070803280306050609040c17040501150f030302123010080c09040b09070305 76
    0xc0380d45141b24840d4610b0b640440f0322a145410840c0c491901400002d0800d108000103540034203915072095444440101740080c1c0ca040030100e60320240c00401048600c1c064a40076281545d105510030b034070502c410003030000440e9004080030010b24100d80c1d20b0b41c951906070b80203c030644000e50158a0030b0007141e032510000006103000c02040702152821210401018005880340c040d10403140312403140440025800c481245c900282d40c01606d503441d40f00d40a892035a008100310f5012111010f013900802c00792441ca00e20060124901031100d00c2c144004940340344a070b0717504540202e541d451900900c40c412021204510400c0050540d14202420b09078040e240d003032030260002c0c85074040000e141d41c03030418540881c0d5040c0c000c5c184003021740140c0e25250b0070ad16a00700f24244d071015221000c142d09801d140c1185035030b407034110850400c0001602c004c1e42c0c81d0009001030740803520801003a170300c12030810f038405c0c1d016105c1852591400c4515040855643c0010014868041000085a20 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 705665539 1250 705664289 705664291
    0x206243705010e03010624021f0902010e031501180209030f03070b0619050402030c09040f0603060b04020703080103141c050d0c0504060f030e03040b0a110607141b1c08 74
    0x266200003c2d400c02004140c2285c14900c070329140c2ea24058001a05015141c00c1c00d800f0070704600684c1d04141107460120584a059085100b403e0740c5c5e640c28104641e0495420b80308400290010041c99038402c102d88400203042c0240e20741003845880d404e02008040c0c04407100c0203005010b551070100c0404005640707403c82c84d400c6455102c4500001c405007803a00d60f1014608a043d021800c075031424040c00b00950000d405100c2c688010400f14107a0f4171540103201d00908002e000090710303450741c1020390484069800440c0320300e00402c101c00120341e01c004801d056039003240312390282009a6142920300b1250035040b80c2c0e50a854400700d0100d54128000e0190400c0494082c403c485110504440d107224034000e41e000703d4050301007400050300c203500c00304001883d07208407441c181d00e800d1503d169800031504900002d0a82c80841e9003140103000c502d420100d41c0c1410b102007902006c180216001e98000b40403410141d401100080d4010403c406500c0c084491041d0525044400200340e000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 705666789 1250 705665539 705665549
    0x1212310807060506042013030c0816090c0c1103070906060c0606120b130f050313060908060108191502030a0f23011a190305010602062437 61
    0x860140010480d007818011803400705401c40c1c1c41d4000c00318407180c02c606d94111000c6401040c102e00d10200001c0d820f12018030103410240c00808520f40c03207030000306044110760000c849482c1010f00f201180ba401c100c136008840d6008909000100c05075000c645004190ba01121945007807902c00100c040d002005070070030310f0044030140040c40c3c4a11f482d00c6400d000c001d00401c00f0343c07a403001a140700d8060b10100c420f607224001c208110306d629164540765800044048010f844180000c05c91180c0183c606c40080c03408801901d519031600d23040d25107d4030850480030b82c04001d1501101009503400524145161195085469082441103640103180c200c140400013450071380403c03071005464040e00940b04503907100c501c6581c00c040502860801120b1141c4c0d0480c41880280c900482140d8090000b140c01e540002c1d15614080c4004e243ca0000703041040083c420485201c0110380700d170060001c5403411341d060b02081da1400c400500001b001e03403000082110240720041c800084540407001c0711 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 705668039 1250 705666789 705666791
    0xa263109020a08010e0a020d0507020610050306090a060c021005041511031b0c0f01330305070b09010909020d05070e01110304032907080108121231080706 68
    0x15180c0300303110224030400e019180480c142000401c861603c850f1003a510038501d00b8054100f00c4c1c805603403170503103a003a5802c0707000d600003604002800e1695901c000017004110000c0c44281003511280f80c582401040240c20f0b41d844241520007035008100e804590010108100094503007400c1103009400c840d00700024503030404503100320303001869003928005e18001a100b0606030005110104981c0200c200c08414068ad1000b8100000c082c4030b9844403640c0c00012201c1901782c1d002d1030742141084480100700803601c2c8000d0000c6000013681409440d1503030395842d6288641030050342c1002c041e41c095500603000141d41122441940c109a0003880d2035198102d90862a07030040d40c07407030082c00031864203a000b44403c2002c9030074484100304084c40c860403403951403501031540144440031112440407514050040085c0d24080040045c2c1001c0741c0c50250a0440c0807040c0404403a01604620b2516800020420950011300c4050b500003420083c01e129010365160951458020080540303805d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 705669289 1250 705668039 705668137
    0x4052404150216090c0503060103150b04090203010503060702060702030a0302071a16020705010e0d020d11060427020708040302040510050a0f0806010b0408060408070f150b0306090a26 81
    0x809014a203028090391b100c0c00e040d5500c0c00e004600600319000c010259004440001a0610240c1c0060015100c5200d0160340c03076041000341844c040028000004540c000300801c440141d001c015100403000a02c2c0c0584d85120034140186102c40c1d030398145070102d0345a02400004568156070780020b10f40d0380c003503441c0d056031080196005c1c0d06008007207811000c140640b00041c40d040c41083c0510340326510000300011001c01150564005810252440007480c0311703041c142c009481c0e064034808035148190301e004559502e200d00c038026440024003680d1240d000c6103c0b0400103c81b00007800c009032a0584003070f03440c284810014551b1145c0c180703e028480012032000310190486094400c000000c01c499102c0341c0d2225425030240c04c1c10b0359540c20b10341c451000281c208034410600041078801042c500d0841c4100360810300042c1600d001070f80100e50000c00102c043d801c00714420031443d001d040718080714064060034410b26010080c280248024080401c9a000b401c0300d264490021001c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 705670539 1250 705669289 705669299
    0xf0309011409060c0d0609020304031115191a040e01050a0b030f0307170d020a05041401030b090403120902060c0708150c090d0f02040203090709050c04052404150216 73
    0x26060076281e100303a0340c01140029080504e400d004214070310f0030715000a1010740e031f845900102e0b08140c2c0c040300040c5a40000c0203144800700002000b0314111003003204181442c004001e5004054440700d090540c4840c8000c142c240411400f944682c005402403040c851000ca446d40280b00443c1c2840742c00e80780080d101c280c4c3c2030000344558103007045801980340502544440c07400350103086050380342d080c1c10000904c10b11410b0002d019400b202c1e03240e15880e542031000100c01c05000903952810189401c0d1014000e9076541e40c503036045078050420703e0030544003503403840c00750100503800303900502c000644c1422040c0004541d011030740158156140450b0f000007040c02d0a8042e0340001c0081d00c00d11802e181c900d04940d0240c1114070451030f80081c1207459010500380c1c3c00c12a800d46103908808000c00000481d409043e5000c4006004189000d040c40f0000c1e454107103100e0880e503c0b6070701a1501151a071003800f140d01400500416851000c6079400c020364500643c0001d64488002c8000090 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 705671789 1250 705670539 705670571
    0xc1104092a0b0f180d05011e090320190506040b0117070e090a0b0103080306100e1e0a0801020f041802090d1202070306020c0d1e0806090c0f0f030901 66
    0x1040e106007041241c50402c441d0354410341e9403c900d11500d07070b4400000200184c1e80c0ca0704031090542e03100700f0004c00c0a8034042586c42c19a902e01001c010710342d040500d05000640c0c85a03182945640c0b821143d0f803410541d0320110700c3d00c0d204100c00c0300b2062840c4108405c5c4940010711038800d6100d2419140140c0e260f60203400100c828807035655960380005030510905000003000303644048103004a81e480c4a803602d034040303292400c0e801643c40c0640082405800d003800032104011403264203090a000d9540c1010030545584c02c0c02a0800012078802d10344a41e54591402000b80700040003035456480c480c031880340303d50051088086000707070005402100d9201d03000340c400c40d0b0f0f001050100d0790030a548444030701c0b1400c0401e5000314055200c010001401c64400b42480341ca07503100400070321140e030340060510010310000d01045641c609028801c01e50001100391b01000544035941d140c0c640d020b01c001240600320000031190030203e01445e810956030083c0d440f07101e80c0d400a010071003151103200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 705673039 1250 705671789 705671873
    0x30702010e0c030c0d170c030714011a060a1202090a0603021909050a05010507060b210c0a2610020a051c18120210060311030f0f06070c110409 63
    0x80d0400c0c0d02e0118400401c041b103240790704500151103040e00d070000e11545542140d00181c002c850090040705030400421091041d1a1442d005103900c000d041c0210000030903c0c09260005010010111800760040140b90103a40650700f0180c40d0900c490340310140a03020b500101c02000e50904148603034410603114500346412568084c1010701d10323504280044400c0e500c80f503829520103864607650f02c580c0d200e240580e407205952031405140041c04550590500aa0f4000c16210b9844072009010009401c03078850f00110340b80c403252210000810070b042c100307020700440844440c40400c0608810340c1200080c541d0141034441d49182c010304a010314101da03514044035544100e04040c44001131410340326031008114900440b2551070b03100c101c100584000360401c0380d81c0001d80c0c480000d1402c0400611075000408800b400c00b0f0340362410b00b1651400c0003001042000010403160b400d000340e11000c80c01201d4007810078070070304100c0d0500e00c0121565914000b4855190b000703c60310405020418 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 705674289 1250 705673039 705673063
    0x1e070503041a040f021c02030106050f0108060d1b060806130c02030a030504110607051f0216080d02040e0c0310050103060609120204061d18070506041509050402030702010e0c03 78
    0x440103039200d07186041d00184003e000f141c03140c49036014400503941c4c0c080440740c0040050543c50310321101c1d205050950314a98802c274010741c000c0b14114440d0ba00504015031050f400d8880c16404101030521841c4a0007049031005a00007c1d94007140c1c0e5940407424170b00c0303003100340c54035940248003a0043c1c0c102d49000d0403150040e0404d01090307900d03a00c83c1e0030042c3c01a025441d04a102200280083d20692012100f15229408004050b05014070320741081c0c0c8680482a0440c00c00d41c140304050094400004010090580018420940400303a81690003400404544482526111100e040d4a40c81602d400c01c6029414000143d15031080c0100ca064880303543e202d00c0300e1441c0030700300311524400c0700c4200d07130241e102c0c1c00119419680400c4407601c800788081c10303042420694059100500c41041c003050035040800c0901480c2c5a0b20204d0b8101e4060103d0300d01c41000f80300088802c85034940006500034000402d03c90070b5941500071182241e448015540030207440303000c141d0303554400658 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 705675539 1250 705674289 705674303
    0x15091203010312020c150c06130b0403080a020708040f030201200c100306030b0a050123031e031608030a0f2903070923150f271e07050304 61
    0x18400600782c03050709000081180121405d80305201d0000d46118400e8040207000600400c08005140382080050f4005114040d50f058072401902c070400d001764001c101405200807071000c14145507256048402a07504608056200e94650724402001d803460720081e4005039540c0e1101060100208070001c002d60200000c0603074262586c10720003002c0f4140c407084285036440c00004081070b129039955110785010000041c242d8100140009a18030f0201d44110807502211000002c2d00c2c0051b0104075840400301d08032001603150380b11031962080090400300241b102c917a000c00c000340300d00514015983d091041c8240e04081c850003040711008542820031190601c0405150b5258107864580c0d440090240e490858448043c9404c0e960700800a0110381010740c0901d1040342c200d40381c0c903041b9445c40907184c15030b0000000a051055003403141ea00ca182c540750350014900c100e0580c480154050b44078401b0600d0540c40300d0010710055601e024034201d8140c00203490900ca0b20441740b0866201031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 705676789 1250 705675539 705675541
    0x907030c0e06090a180501020408100c051608030c09130c020606040e0a11030120071a07020a0204110d1e060501020d081306180501090212010204050112052715091203 73
    0x4203180500941d1850030003171948000c425000c1030b4280010400341c010032008204209070f0400c20000c5401000c4104200300e014404d0b280c1540c11600e41d6103400350440c104036101e458540d5003003082c0c41500b04156200d01c414102c031841803010b0308070040d01c6020707809450356075846205000c00d56030785610681454010042280001f00c0c1a218999050303000303000001c508100d840d615a48118104420145140102d03a000c20003e0704100b1005542001c9103411090800c2803000e50346200c1c01000912a58a0380c1c0280c1001c1c01810503110900544402444030106050200f03600c80d50f2501e1011036603040c02000b18055000040c0b0309441c0449582d1090b5603611884220002440f4410480f10f203601c0e034543c0940c0c60341620f03840818038001c4c0000076481a01d841004070040601c07a40c4242079006100030071041c0e03004200301c87c461b4240407011515a448158a40305120710700307107501680c4050000000c0178400040c05100684ea481008034031500c459940700d5641080244401c25614200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 705678039 1250 705676789 705676801
    0x5100b0a05180301090308160f0e10170106030209010908160e041b15030524010507020402040f1e1202091302010c050f210906070f15050907030c0e0609 67
    0x2900600c0d42d4061000072890b902c1c4180002400c1d0b408801064001031404c01c00d008101e058001801c0940b0003d0410141c541d8030382c44081c10820740702620b140301e548103050b00e111050044005500d07110361945403c03c55a140c00f070150007504100400c60020303038600008240342c840000c1111203803101600c483e80c1e05160000e00748600d00010422620411040c100b07070740c4c602c0c2c1154000040c04018180004500d10303010001e0031200000c2544d1280d0451241152505240c1c5a00003001c45023864101da0318041030002c100680b0a9500410300001c00d08800076102011180503880e04005400c0000e929554001c001c104441110300654000c0441000c00c010302503e10802e4001d41c41810303c002c0c80d07030103074941c0c5007003c40724040760b40700e5004610152038540c084041c000000c41c25032130304c0e400d0504108c04102d817801410801050001c00b40c0780e00003807000410111381a400100d40c140a031b8a0955000340d2190482d11003250303d003202d114003060143c0d200203c03038816078001c2c0c064100c6990349 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 705679289 1250 705678039 705678047
    0x60403020618010c06140106030b010302030f01060f0c1505041a1b03040218090606010f03090b061306150201020a120605010e2101140423060103060c260a05100b0a 72
    0x1142d180d030502c14214128000141607004203580764040b1000e41031a0340c50048007074107894407102c183d41014810800c10941104040701c4d02c1c1528100e282448041ca1110015294000c4001002d42400d80c0340444110449040c5c2110344518402c0c0c0541d40500101e028101c988141952002c944458012803001058240c102555101d8001082c81c4c814a5000c0007031403040c0003c1e180369a59030440000c200751941c00400c071106410491604000006c141d0700d5407846000003030140e80c03060001840030072528945070404d0025024503008101e0704941000007034002d600054440020880303000080c0c0352000740744150411100182c5500d00581403081c1000410aa640b0364802c0c201c0d080722000890001c2403040420300440d00c0e01180301410503052030310342112480d0417001c00c02c5041d0b488250140d800302d0358034116940031002240c005000502503842d03190001004e00080c2e4010215121104d5020140b4042d4074450010081074941c0c005880c20480e0030b009000c00700d44100301042d240fa2007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 705680539 1250 705679289 705679327
    0x1140d080324121608030301050a120507080f030a08160503160306030b1512060717040303062705090a0305090f06040b0c010902011e0c0201080603030904090302070f050604030206 79
    0x40154201c02200742c2c1c0300081a44039010762074409944240140c20003000002c0c1000c02424410005504541c5844006448407a00f8011f01d405030f00e40d45001d80401c00b0420030300b00905810001ea0718926003011465640e0707005001d00400291a0001295603105600e068a0700501c0030755070103203548e8585440c83c41000000188904050303840c8400000b156041032158003030f40c88119a2510900a001004490420541c0e1082c03581c000d40180b2494540010b0f004050304c3d41c459900c000f650315410260010091544840d840c00200c60001d540148000c0d1078602c1d061480400700080d8840000440c0c2c1d441c2002801404940c0401012460340f500d442c200c3c1034050b00a05441c60300e03444200d08403a0340c1082a034000140e4544400504541c0c228001018820bc4200030b01c40303d252070f50000301510071503100a41444030b290042203113900c00b8002c80745000e002402c20301141c1c0d62464025a9400a8400d0041500384400085030314074114044900f120380007000d13141800c2c0303002081a01188 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 705681789 1250 705680539 705680581
    0x907051c050c1c060b0306091e01080303190b13051807080c01030b01050a080f041a040b040203070503030f0f0d1805010f18080a0c03030209031501140d0803 69
    0x410a030003028094507405000c1c420220001c0c0b55484901044a07035980d040c0500d0032141d031504000090218022003415a036201c202100d00c04450f48500b2030741505407644450304425001803500100362160004011400b4010314079002040c1300003000b0060498141d402c14aa0240e03030110360316504407454021075000b40e01d800d9000b8139005c141c40007070300c0c262084d404142141c1108040c04101c0d030f01486440d40c0100c1c03e0811501d481c401d0240248010340c0108000c1c000700040303020505000b80544060440c4028460400751750a00741000303640541c04440c120b00c240704520f0085150f04011094030743c1c1c080c0d40c040080c01d14940813070901c0d103034000c400b41c2400688d945000300e035140268150122010b0150000003034110703240da04401580c0300210b0381203280400c00030500008000350129a842201803814254000b000d15089002c3c2c8030700c400741903140c031820111103100016200058104e9003441e0701d60b0503181149042c440540307040710016040e48403d10014036000d41d1828601c101d40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 705683039 1250 705681789 705681817
    0x31d10030e0c1012050109060e011703040b0f070b0c0a2a2906040902130b03120d140a110a0f092301120b03100b060c01020403062009090705 62
    0x100202c40400d0b4120340c14880d042c001072110304120b00c00700e9284070303043c0034215216080c040503080c40c40300203440c04184261081c54441c2e040d6888490000d0041e00c001d8569403c01e0b40e9604070003000d40c0841c0c1c10814099034126444c1021030802403207001128800b941c2521011049980600d05a0640150300c140d200005d40050007480014003c00541084007044140ca07200d06000b100303080d103800c0300144994040d91400c4503820260340d5501c0d000400703020a90010031100a10307030200303040240503071024040d01404102480e10b003080f900881c45030412074041d6451581c5000c880029a03080e050801c10514080142c1e00300c0c0c5200b8a078000d80d1505605007510659610081600e4502c01c0d20004c6020380e00701385207004a5a8000c40202014085400074041c1040b8203000075181d0301c201c80751001b420b42d5949032080c140c4440081d5400580083c0085407605c4d51790034454054041240c0c00d15100d4203014000d01b807005640151400500094041d445070340e1001c2059580340c1c0540501c481d0350b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 705684289 1250 705683039 705683053
    0x50306270106060c0317130209041e05010b0319080f03040f0b0405010b0406051215070201061706010302210c061608130f150210111c09031d10030e 65
    0x1400c000d0060100a2181e5900c4040080d410300b001031840c0c40e02d07200f03486601031690600c5106802d00302d5240c0c0d5aa0100e0707204069440e1480d20205150101402c00c0248085000c000c09022066204080e044016015544001c501c0d9001c2c140300c035001440140340190601c0801406d400c1100a958824030820039180241c4050302c81c0c010780f0408131402c0b00d075603441d468550407608082c003525000700800e441020718402c0c00c02c0c00325100e41071001400c01215103080040e16551003504014000c01d024a00f480103100c0b8141c255865250034007003030b409101c88150441c80240045403013100c500da0f120161800c202800704201d4140c0c09006603002c44860340c14020007050000b8010140d5440c582007034208a85851007401104072141d00400050000d04801a0b42e90380108000c445140400c40009005c4804128502e1034040c8070700b08902c0329180c5080c400001e0302c1d0b90102007843d010392038401d90140e40c0707000b2104880030001d400303401900842c0d1050a007030180d000303045103000b45420768170a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 705685539 1250 705684289 705684361
    0x903020901030c140402041508040201200609060c040b0a08040303140109090506281d06180f16090f0f020c031803030c0a0f171204020118050306 64
    0x10002a0015203044180000070440d80c0b0200d0004c1042440c1901d0960816103020241b00140c004c15507424140103603040000c046a100345000f8203040e01c103030120440b1458803201c007980c0c0c0c0d0f13040703d00c035103031b8400d01c00842c101481410642d812078030034895151070009120008c0b62110000f40003141850744a0f01c49080908509004c0342c0a401059400210103903541081854a60082e12460508004040d586150103051210441354a402c1c40c001c6543c15214244920543d000d003c805482d004001c1881009000a004461500d01d8801101c4402c00c1c094034683c3c40f041d00c01303c1c0a039110007000381033008203c990004052000482030000d205038594000d14241c0e03001d2511890b0079040050350140018209060215204c8140c00960401c8204500c1e2035490864110103031600d5032400c600390800521385c0410140001407068203490722500340c04c0d5544410181c40480c003080c0303040302006601060041420440380010010480d036151061030760040826180807036480c0a0340501104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 705686789 1250 705685539 705685549
    0x3021306050a1701050108160c02060a03150803040e07030b0102210901030c2102091210060e0a0e210f03010e060f030a11040506120a0c03020a090608030d020a090302 73
    0xd022588a1035a9040038150040078a0410b41601900890f81c200500807640e0148085a1003001241c1404200e00300c407400b40e44403107904c2c500070741c415000506800c0081c0d141d00080c0e0881c284280e501c8a007621922582d03160b01907801120012480c03600010307400b0f4405e400025502ca81801980c0e80107d1036403403561606d000011544003100006500301c107030b5a152080d1542e1400b54070b09610344041d2400040703d00245510903600707068010801c4003441d0341c1e200a4036aa84288821070b108010044140f402502c0d01f03204043e8100746403c0007890510b214011081004000000340c4500000140a00221003110310702c2d465034501030004143c0100c07410000d5000e860180503905803480e0090800c49190484031055001f038001c00041b0740000c9a1368880100c4400446000c1440d0741d4081c0421000344d010300d182071141c8160b200c07500a000040030584190f0b4001e50318000c3d5151255000000c0d99024807031320303060354010020304416224035405096003062506c1c2c00c3c4c0c2c05c10390701d0b00014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 705688039 1250 705686789 705686827
    0x304020d06180b15010201090c05060703091d09192109090f0e0c010c02091b0d0c1718190c1d0a0e0c06030109020918070e0414090705100302 62
    0x11000c640c03480c203002d550301c0e0000c40c4e21000c0c50300348000c0c06601003550f6003840070811446024040e52000c5030303210400d40140c0c0d0031b2014004500c1039011516000d0000c008050086d2403010007030058510780500300c1c10540c0410303407039604104a429034800000300110400308118030801001201040407491807014001c00b5039250b00c810b00880c14110492043e41403020313941e0fa560602061007054030045c0c0715a040240d01038965450580c0410403890b0005207881120900690285000c1010003a50303084241150380a140068030700702a500d50074110354a0500d52000141a40410084400007020520014480e441001003890066460000c00140c007131452423214018002e60030072100850714802c4503074003041c0c400100034481c00c84021441501c418040c4a011a03000129602c80b40c48444040030403901050f03055a203031906200003001e484c07049401e148903a091403c05441440c0c41c0300e0131130050100e0000750818515103000c20050158102c0502d090507001e028030150082840610 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 705689289 1250 705688039 705688043
    0x23070309150207020108011202010c1401061503020322050613020d050303090c150a1b06091502031f03020303041e0e0108061905091c02030f1b0606150304020d0618 72
    0x580c0f182c850b8030024080520503046454500c044058500150703a120286000380c0783c01c1448060a00c0c44104400c1c0504199000003218508007030305070740f01c00d40c56801140305480a8618650765640700d90400c0e4020040440600a90305c40c01c045018400d40d0111442118030003840100083d006981d210700310b400c2200c220015400c51201030729542071642c910203000b0854804c1c580b600203806005008101103c3c042209004942c449800304800d95001510080c3c0080384c4070b102408054070700340030790310880320040111030350900780740f00103a030f440c50809913640100a9400c142c101607170003a8500d812401088100070f00c900004180804200c424042e050400261085e4680b80001c01c18124540f459020302900d0a4100f008042d000725a5940413150408000d147d0000940304a156000d21a01c0c14000c3c50001650a0a9040010740341d4000c0180401c2c1c488541e45c000c01c00003088448e801c0042d0202c82080004c0051425221070b665503482070000181354001c200850201590364401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 705690539 1250 705689289 705689291
    0x60510050a09020d0605030313141c061506050a02070b250803150f010c150f020406020a150c172a0904050a150b0c0309060712030c032307030915 64
    0x40d0080d8400b0b6401a0705c003508083e0019403400030b14a035042e80c6800544550014000181401e214680e01d2424a03407001815889038041c1803924100640108203400c0e00014040d03240384002681c0340542c00f80c90540c1c1054020707141d16880c050010506510441c10000a080d1090002030792a20171044110f8190064070656100d00d88412038849001d070500409118400c106494070160303030f11014508143d80d10120f11101000392142002c041c141140358405c0b240e0001c1380100d29a0780c00201d150080b800b17480c1d401142a64543d151b0115590003c0c03480019a5044941207451600005650801c40704030740d00ca08151000059459900003810700e10340032a001510351500d2805000b10f40e0040c5880d00100030343d10500500d602003c5803881100250900403071b01004040007401640c25108000c1d149560340c031910701c3c007061201404800d260109207403d80c3c1c500c0c518840d00c03854540c8044080c0c0c240503010a07074450089002d0080c03225081549401c01d40340003c2d40c910307031070940c80c4030f0030302c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 705691789 1250 705690539 705690547
    0x607080414011b03051b10090b0c03010e0105010f0210050f0414060f070c061808030103140601080d0c020409150b03071a120601020a0c031b080316060510050a0902 72
    0x55040c00c440900a407181000f400740010325543c60403842a2400c40c1d07050900c1983da60b81616070300b07000000c600c0b98003054002c840c0c80b9050217103150003040305170b80328501c1c800c0655100700011103240020300400502060400040c041035000c0c000c020803800740e60040f90b08403040c201c0e043c2d00355031007140d001102102440600040007260101034016415031400f500462812411099103408001c0058040041e0040c090f01401030a0b4400145095500d9440c109802207041c40c50b111350007071204442d031402c60315a902c00c1c4140416258140c0c0e0f602006071010000c000000c07141d54041c05010303039000c0e50782d81a080009650744d0100300c80451400c03022540c00c0f006020142024899444000100c0091a02c00744121031007003151083c8018050b00e400980352840100e10303140340260000c00503195082c0203c14040e514903090008581401c85485803030300c0f081c0301d649030301500701300e074010781d400d800c452000818682201e40d0100d5103041c40f10010307070740740c0000719482c000380d11403484154009 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 705693039 1250 705691789 705691799
    0xc031406040c020a060203060d1b2c01030f0212010e0a1b060215090715112a0127060c1b0501082406070302030306330f070206070804 59
    0xa011980180215020040d6200110029440f0315003031000400d81c1d6400000209260f5401440c5585030740c210326029080725403004440e03228021402086c0c035280c40c10180200000d04041140050141c0c000d207500700303920b99034514a61000e9464100d903c19800c11800c120000700344543c0c850840300e0002010425001e080200160340060311042000c0c0000320244038158000555100030812104c203c501913442c40c0b081420103190f600044020700300000303189500c3d0f900c0104074445401280c192040c0216021a01451550000102c26030740b10381d4109241c00e6024a00c800b0f5001020218001c0a1390b01001c1912201c91540000c00410f810b00c0c0c101003849844488032001c0081203812031900c504150000c0d050b842c0090007100007110092000403040301c1d0f0395121220450180206031600c80d00d14004e52260030032a80c0b40d010f100c00032581075100c85502603080c1022500d4100f03011400d407000329007505e079002c89034000070340354200650001603c54100070b145107070045d0b00c516200c900300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 705694289 1250 705693039 705693071
    0x9180c0909041b08031908040f0803240613090e070807080f06150319110301110306190302060a030c0c0212061902040308040605030601020c04060311010e0612010509190c03 76
    0x35041000940c1c02072151b0300d0030b01e01000d40004c00d560070f810250903581c1d0380c5c40c00c2044600ca0540081c41500c000c018004403585071603004001d8034428190385100c42941080c0142030040078100c001c40350003030070304200320365481d0b00614840c2d02801c141c69000313490b03646880c6001c0c3d542d07000790026031040701e50040704917062091a41104107175242c1460201100006583c5541f480384824071895601220410452080d9040788440390240c002c0c4000c031040c80090b00550070885606002c0c3c1c4140d4204009001d250780030b5801ea940c001d118500b80f41c0c0c420300031401001201e600f2802e0104090b240030140c2d5030380350103004507034000008226501c0e24201c1902c0440056200f06c1c281030041c0410b03c0091840c00642d01900c4982c50301c02e03100c5da54400100d142000b00b100c1c03d504a03207441000710a100454028520200c02a2942c41c981050182448418840c4001d01c0000d44070090040c0f107203107000807845030001c03002100f04091071003480c2510105c550410004000c030381e86007554032982d058 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 705695539 1250 705694289 705694343
    0x6010510020303040b06090702030706061212020f0d03110403020a03080a1116032009090d020d05120615071e0308070806030a0b06011103040b040f0b09180c090904 72
    0x1951019506500b0185d560b8154614083c100c0e81c8030b01d54200c00100a00d10800a90f10700641090050041907a0303290700c0010980c9030603061700d0701008a0b81c0e898013207000240c41c8001070300c100001d110600d85407200b180205000c90322806c03801e108010020240c6e441d0b80e45180230714011100700e0340d100c030340c00170140c510030b10949a4161a001000c0904c001d9800c0111981100d400080340b82c907103403051142c9400298216004ca602c002c8885c24001454030000d0407070b001c882c081d000c40344142d044c09419640e03401b6010800b4280a1207200144181c00c0400b0422483d11641c054242001107d40d0340400400c40c0d01c0e10502043c818144800506620808498000b4000c3c148064541007000109449280400010307095811002c0440d00e0b59104001c80b064014002d81540d0b11207849000314401c603030061260002c203550700c4c1400715102d2113007002c941000000801c1000d80c5600240d20030100000100b224405100c240251909078a8011034181302e58030400c1d0020030221011100080381e02 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 705696789 1250 705695539 705695569
    0x10b0405060909030d091b0b070611090303040b131d0f0106080c030402040c0e0a090207110a05101b0b010e0702010c020d270b0406181e0e061305040302060105 70
    0x201c03601030201440b4040704a64049000000200e2070104500704070344140e181010000159005100014840d0400d4001d02003185c4611018422038a4041000400340100c01203750b040c3c004000801410390940d0041141d054008017001090b55a030012030382c00c0781001d00c00088a08000100700d045003440c3c403600c0c0500014240000309040c00d20400c101c50100a000901890340e8031200c0c80712500501d812612080024801440c0517250009c10000e504400c00031110032441c1c405030086480c05c048480c0c140c0e80050070b00581c440078000c00722011110380200035190340e01c50800c407021801240409000e030a21119030981828040d10080c00c443c0d0001c1b0400854101c01292800690b00540400c01d2440c483d9035036071210740b000c0d1070754241143c40d8441000301e800091b0005420313801c441d08001c1d080c9254080c003c480e50701c482281912806000040100106450038000e1600c1c1c001e402d500b10401401510b048031902d030b2008111802690b0540261348060010800d61174110340f8034640503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 705698039 1250 705696789 705696799
    0x10819320d02030c150c0d0e1c030c02070e060d2901090b0a06030c090e10090905070f0f0f1809021806090112110d03110703110f1e011404090c02010b040506 69
    0x1b2601d6401800c183c000c0c3e60300b840c021030300c610a80c81260000c21407a074180c0080495141c609074070060150080c0070b03240d03042c03000d4054004001840c18201c01460300c00c1d400036050052071145035850340c05052009503c41465189100c1055000c05040707092800380010720030028961100c17908001e40f0007166440702c0105414203070103e214690104442d000c4407200a2440515150f0080c068204011a004000814a0301d0340c1c24007072010005103001110b0101e01c946c001a500c604041c260390b447c900852801800140040240004003c0b4408100146010010725504aa400200c400044410840c2e1140e202401e0003040d1a15800c4030740182218081684951116650072074001803541c02180300c3e0180d817002c5400e25002d0341806c80c0d42c203410300640342c2080c0c0364541910302d001d02888060090640b41d0000c00c0d9130502c0003240e06500e0781c03181c40307503901c00c2000d00455088044610452419130309000019012070503005031744504065400214602e500d00b02803000f124801021030307100d4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 705699289 1250 705698039 705698041
    0x501060b160609020f150306040b0109060206070507030c02060316020114150103020f07080f070b06012a0212100c02011a100f030b0603040b010819320d02030c15 71
    0x40041d20004515240e0701050100700754032036000240700d0b04d803580c4015030400002200380c0c0080c1810740c0103520881e8126000c00030301403290011202486240148005680000045800d0a000d03030301504000d0310030710705101e401c1c0203a40850345a4200303540d00d0b09400348410340d442c00c054080c0101000280046508503892819200c410142e901400d15036051643c0003c03400b100403081c4046400c15504902500c4d0745159100e074150243d0700c1940d0a888011100340420743d650321800d000c40c1120001083d1140c0741203895200c680c4810b86060880e0300c41020440e015001d0800d10842c0d082d201c0c0d4400000f948904c81d80040c0c20340e240c440401d500d5a041c200c00c0400c13540d40452000407107089161080d130048000320142c0050052880043c0d01400101c20802013186914407141a10301c0b1001f520161524525a06c850460242d0020000346402d200e11142d181c40c8221030000e5040035140800d030b082c03800099030520300c010960b000140c00000c2e41e41420718041000c0880c04d0b0480d640d140c95 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 705700539 1250 705699289 705699307
    0x12120708070f05220f1d01050612250305061002070e04060209010203041d04030909090f02090a020d0614031203011805070903021e040f020406080f06010306080a0803040501060b 78
    0x55030044030710300d10038400c000c04d60b1030328841d42c002082c0029114400103854941c44031411090080d1600c1078504004000700c1251243c003108070402c3c1282d8000d00050309004262100d000c28503001450820426100000078a0f68000880480308015031501c0004403801d04805000c10504d04082e03001c04d40d88180170800c6100e80e00c44040d0351040e0046801a20f90407034800403401d40c0f1540e4032101d034896003103040c510300d90381c071a0000d0b000e2440f0b0f407222a0203984d1031103100c0c00d554245101030a82c100c5811300c0d201600f0005c0c40d960340100a028018501500d50100c51304840c015040030307e0200400110f03088504040008145410844203802d0442d03140294002050740e00030000d61038281c40b00701041000340034515084c091035000f0208013200301c802c038070a508407a0591a482c40f40b0700305200140f902085100b11002e17552150b980c040c2c103a44060030a040c000d03001d00400e041550744e03040010f0201050100ca200305100f0305509680c0d0400d414094203654503038020100002c410000001c1d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 705701789 1250 705700539 705700547
    0x3042006070203060f13050708030d051b0a080603191a0714030a1a04110909060a12020607080906040303050315090f0105090603010e0613050f010c0504170f1212070807 74
    0x107400705c01403c0f4a546075480d407410401c0c0b00c90002d00104039200d03030040410203d0010015001c04280041c0800c071f0f030354440c0c82203000400c00180220a910b01040f00420b20b070302c65450503501410140454909183b10f0049441e403010391141640c801001c91114401030084045554101a0510b41401840c605412410a910000d400b4108590355260301c1c503810200100201442e1100404c200500601d440b41d03824103a001b8101d0602c50880040020214604094080103481c3c1c920f02080c010602a0f09001150f4080c040a1f200d4140901c4259040c2d9600d200400c0a50f00c41d27034803507882c0c0c1070131410640c0d41405040d0325445074206004208040a41002076411103208a44100c010741300c100100e40103001d0001c5058160044808008091802000306041c1a12031380403200c01500d1000b07090700b2526650200d00c0015410401082506440f5013118140d80c0d40c1810b44010034104002540341c100c0041440d40141e0b03000c100c9981c01240c8106040c0d0003441c0781451006071814000041c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 705703039 1250 705701789 705701791
    0x7023c01060608060d14120307021501241e0504080d08040816030c0c0305060603070605270a090f0c1103031306150e0906040b01210201030c0e03030304200607020306 73
    0x1e401030705680100d0302807000f00001581b190344110b0a550000003c0b400107090f0f548102c0b0120054840e801c042c45414589003d0a4121803241c0380082d41000030440c1d41c42003910656000c0c04014181c242c2c0d0105507910301c000500010b1503103c030381d40c075440c0403145030420060400d9901403206800402c80424104412540d81800242d41c00350080a646010348002d0444070b005030211440d07120100401c030740042c0c1a4004c01041381244d9421b0342d02c2000316803500c206c1c0c5202c403349031401c01c0c40303508a038040c0c188020380d10018064510740c6c0d26201c031403040b10002214950b40581b1020310250258101e81518a02c03400300c0c015510314500406640c05500c1d401d50001d00d2507946070100848110a0840700d070240c6042014005141070942c001743d42d07490240c0d8241c442c46032680001074036419251a18600c22404203041c80715000e9600103400034000c0e00b909405000741c95402d401665000e10046200390301c20358402c0400c42600a200c01c0507411560402e024600410129025980c009402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 705704289 1250 705703039 705703051
    0x140915130c0e04150e0c090115020a171b0714120a031404090213031e121206030602032d060a090513020a03140c090411060307023c01060608 62
    0x220b8201d8a4070701d040c4c1641c00003a40603842d80b926103410320300d2140d0082014000b41500300c41d80d0a203a42c0b5618482541440709410301c0240c1c1c011748400740010303544080704101d044a000b0a6050004400303483c44080314464204ca110741081038180f0070092201b1040e5840001501c2c241c155a000000325680e500c107580010b41031240040040c04422081011540680031841c0159140ca44d4140c102c2c203e01070501044411031b0081200c20140656100040c0c0c1c8260040715500460f40d00341015140940f8080c800307220301e40c40301c101101082d40e50000b18012210016501e4582103010f4410003002c0c41c0366800a1080080000e00a541e60b0382000c103c00d841602c1c800007180d841d200c29800100d0304400000750002450007000041c428244203039258126903109548246c1d80381e800f0000c4d1500201ea0082540c56984816901c0e810f0040141d030b0f00c00154012a01c030f44241c0c0c1000d8414415081003041041804401000c0602c83c0c0c5e10005d0592144000034019030303083c000c0c09410850024a2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 705705539 1250 705704289 705704309
    0x602060f040f1b08030d0204081e120711030601170d02210c01020c06010f050a08010207030c0809030c0d081b010209030c040b01021504030806090601050a0c080d140915130c 76
    0xd42a0b221103e4102d00007000c03820100c82e91210034805641c080c3d0001d200300101070141c0d080500440342800810000640f826001e032001d42d41006c0e18889940000c8001e84280b51307040f9403d415504c08200207406030824040101c080e603211000b072407906072840145021500505029610800d8180c150540c00c80c51000c07058590baa86a211390082c001d190303070301c200c0d0711078a4000543d1a0000ba660419584c0c00d48980e00200d48455025089c0c1c030440e2801000510b2486494010410242c040d166008005050b9800c14648100143c8510144c5000f610124000102400c41e00c0d0b040e01c401a1321640800250300b402c2810300025280d415500e903290155407916401ca40e036a00c240003400360403402403c0caa1050500303050052101c0303c2242da10340601c640c034010403003e40c091420b03250983d030b8681e907900400754150f80b00300c10768021420312074020784c58401d45e407141c01da141e1903030784600346210091141c04d00780320300490200e20107884801c00140c0f02d044040801c90300c600c101e041d1160340c05 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 705706789 1250 705705539 705705563
    0xc0f11031002030f0106020118201c030f081602190309150f020c090105060d09080903010e0a0606090c0f050a17090a0201110d09140604050301020a08010602060f040f 73
    0x401e0510745041c01c0503040c14800410401c15062a2400d941664002e44c02007141c000c100e41014051591100040d110171b4821940545800400d080d8550b4900302921520070300048540074200c2503207101d41200130a06459103d0405a88810125406500301c4100801c3c2165a80d0203910b40700014801152091140114030516004800301c900820940c0488841900b40000040c401d100724481d41300140200001007016182060a80b4140c942c0100b4451500860010000040c980c584045444141c24032600f0003554080c070074039000c40c00001c050451230b04245445000c80f032650300288a4603140c40c45401c110b662000203518028a5814020b5a454a280d400d1790403060302038107604082003000c100300b03c6041c0030174522007040c802c1c0c0f140103a400413030410f81e448a0b94207258100095031200204041150002601c0b0740c528007130410b9252584600c042030a9034010418040460503a50041003031990401c41250301c06e80501052495042c00c0e40c5400c20a940c030f9a000d071001d02800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 705708039 1250 705706789 705706823
    0x4020405360c060406020607110a081606060305030f070c1707051011071205060a0c080a090c03020a1712070314031806010602060915010f0506070c03060504061406010c0f 75
    0x4465502c022000b03001540341e90703940e40003c0d030f1800c1c00c4400c503002400100c244e040040000802034802d991100d0181d0600e10030707603200d030070f216441c44082c0c40144c3c0b5048008007042061005044004561a903103545030300c40d04091070001c8041e801107402034001075500c0b950100210391030f019a0b0f000c40307006011180380302045441c1c80c40084501c0240c02101400240281d400c40b43c605040e114030103480041c4e4031072541c48100c0d041005607402284080c000130300c0329115075000d608124440d0140b9840a40ca075000300c2e1507880150480c0002e02804400903404000800c40b1081c00d00e0409c400c0b51400d04165001080c4090305000c510701182e0200101d0418030039001c420b0840d104030800c481a0f582d490700002d540e0751094a07001400c0c00b03100b400e001f052011400f924140c42081a64100c42850101031000c3c03588010300907101e07210323202d00203c00500c0c4c50060381e0141d03009410100b59080700301d0a03540328a0f00506200d0600054407660400110b800d04000d04080c0c020340c10030b1007100070b4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 705709289 1250 705708039 705708043
    0x18010c02060d0606050304060f0b010e1201140903030106140309030f16020603070f0305010914010e09010e06100905360102092d1915090512060402040536 68
    0x100081c85407080c01d200000c90811740c44006584039500800e020b111401d803239410041110f031341c001000c0c0050311801c038003507050070079007602c002d0340e01410700000741e001c84141c4120420b0780547c2c660303e540d080017004011050303100d0710814035807501204140c654200158040d9503846201480c090948000c02c96600720500c041d03c0040158000e00240d07036a2400c01401030241240ca11404046450000040f0b0101414440d4550f4003501c41c00d018480c1e42803440c00700440c00b008024205542d00c5001c0d20b1100002408140e0003112500d4041d50201e0909040c2402d651000b04200b9468010070035030200c18491a00d0b900300b25501051b1010341c1c42d66101454064401c0c2016140c00000c411640c05000c03104140044500c070900440d41c2002100e4410008000c00d80d10701e05003000c1e6051003d01071200c4000920103660143e007400d2202540d14004564251104540a8a150030203010030041d4101801625072140302c00441d504000c55517540f010f4059440c05040daa5030a0610000e40c1c00101 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 705710539 1250 705709289 705709297
    0x601060503150415030503091305091b0402070210180b0a05030114010e03030a0e04060e040b0c1803060103031e080603030a12020706110306030f0a022b0b090601051518010c0206 78
    0x1503040f41102d410740306d0500b103030303a41d11030354105018890703109103004110303c58458140248006405450106034038015202c20309071548003540d00c281c1c00c04c007080042e9907102211100744101c0e2210080c1610454005510121617031024403004801c00410240756448801c60b41552030060309801c0c11b0101500480308803140076401a0580f00c00900342d0185d03a041390000700700b01e40442c0c0a10055488440c41e008103a0182c03402000606000d021a1280e500300001e0000c0784040f0041210444410001901e800c200703a100b0780105241c42c031041c94002080d10003486098460034989200e04040c00440d9a0388560080361040101c11030305100b0b4441c49404403055981c20107418088002c62505d000e840383d0040d1a010320a10035070650210124002c24501743c0c082c2c00405060400043c00c00828121008a4912210503001d12941c800185000140c90059464800030011b0f5070502061010707112030030f0640310107100b080c0511814640b500301d903a42c0820080c41c068031350642900c085012401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 705711789 1250 705710539 705710561
    0x3020f07090501150e030c0108090a060207150b030604030804082d180a0e0114010c02030f010501060e030c030307060218100e01120603020303090108072a050c0306010605031504 78
    0x303030031002815112540015050314200e07130324945806001c64054401c14a020030b856059049030140181c1580280aa181e000015400341e48420041c0d680f9441241d000120842d544088040760005481451040c40340400050f4000d03d81400d0544010f40500c6008000520a0400084450f995455406200c5035090b0044407002072015040800140d50072030150741040c11a070310f1024070149403180b0303540300302e9080f4a0003a01d642d00345220043e030121281d0100f030600c0704003a192070058804012405c0c400182000015480d4141600144034840c1142a070b40302e9809192a08080c0c2c0c2e01100301e82446500c000d0050f9164a80404071000c1005070300305030b5001804000c8856001e0700100c0111601909a0f01c096045054030480001c8640701c1c04041e40580c4180300c41a02c82d4040c24a50b50401241e0070802484444c400f10410381c14102005090406549421401086000c001000c5040d0003240680f41030740c18010b008099000050034001d161003d16801c0015460715801460521 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 705713039 1250 705711789 705711793
    0x5030111040e15010f12060b0a030e0606030714120c06031e07092d0515070203150c1e07020603011d09010b0319110603040b22030c020d03020f 63
    0x1080c00030854020740003441052424071800d00018009100c80000f000c254078140c560300c0b81401c803800d040740d07000c0701d4840403001c00c0d13960803002c0b400044450141801403983c1e5404218002ca1020440c24000301405c0c15002e0f90100c082401003120b40741c901105810b041d5102c03904c000e12110704900d003442e801c28454201c0000001c0c00740c0b022151401c030b225401401e200c64030f82c0e2954202202c1c00c841070301c1030781c89000d1301c82e100500c40c003004503504025412000c4e048a001d9161400103101651204000c8007210001807a0380460034180904400215022019481460300f03800c011258407a64000c0420082201c0b4800714044409080e5150a40c0203050984c4940c1c41c1e070303003c407280341c10001040d50081240700011440c940500a5181d28203020b0301811003c03a04988422600a88a1003100c03841c08200c0c240c40701e92600405140300351b01420043c007250410080d80160803011410f6068260030081609001c203801408101c0e2240e0b05036003401d0981144d08089041098407000340c0031038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 705714289 1250 705713039 705713051
    0x409060b030702060f1b0a1e020c0a0e010e0406200c010f0513020307210501021801030501300f0812180106080705060705031908071b0f0609020a050301 67
    0x114031000c02440c0305011a80840e0700f5a03d50b0082c020611600710380071801480c0700034400e0070a040000c05000c0304500c0341412a416200c0555403620109403010300720043c2c0c070180c90323003100345481484c101c002c00100854001c0707541041004026100c00400280c0110303192640700d01210110030501c008410340502403515415000d98aa01802c0c03024180807281e800c1901180080341100b80146c4156401001060000d2401000c07442c0c3e064050518410b030344030131403d440407410a000800c0c01c0720111000c900b072106450000f600b200c1040c1c2040c0591016229000042c40342c80c1090041d038950000c2240441c100340c60045000c00c1d070705d000100f0b020004030760071340c1d01d03d4815000d1340940c962186480e0004048402e03242203551500c6040c4d13040c3d000e044100301d142080b030001c018007401501603d103000350484000f10701000c078075008000136214104002015500803440b242c42010540c0203d007400700c1ea12072405075000071a010f8000d507940d025400c2103555001c070450041c48054004c4c885 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 705715539 1250 705714289 705714299
    0x132a020f0a030c050d0906120b0f0a0b130602070807030b0a11070605040212030f0901112401080c0402160206031015020a03030b040606022e1b02010b010903030e1302040906 76
    0x90840400304555521941c91000070700c9000d0341540c0301750303211f550701c4d241d00840c01107148026020b042e40341900480703040c0050119442c1c0036285405402031b00521540e032480440d410741c10340100c0c3e2100c1d085400609003401401c10118160301182e030803d00c3d40601d42c0b1070b21010310052030b0b18000280c81110000b24400cc00110343c100f984100e000f211202c0d04081c40c0c2c803425407a131041c18000e030110b403400c003d110400d600a0f2004000401c105c0c1c200e85007130403410046100070200002c1581240700b8000100081c8504211b0241181c0b0f0980b4150700b41129410b80c580d8162a04400034400c00004c00003c12100003110524000c1480c039804806111400d0740284d101d030449501600003034188201d40240d400d00f07002e11400c60749168001c00c2d624026103191500c43c0700502500c08034030b81e40c0d50340403601f03402409a010384218600031043d509503448006801c40b40c074005901d0520102107420030101e41c016807030007031065081d02c10a124000a40d0540e009103c0c540102520a1901c600414 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 705716789 1250 705715539 705715547
    0x90a0f060f18141621020912120d1824060902030411041806050702240f07050a09050a08070f051c1203020720132a020f0a03 55
    0x489040300032070b04514010072401c9098840080103c030780044074001240c0744141c92510b10320790b0000c51070a0b124640c4c80b03458590810181482c1d0381c104540110306074180b8a011030402d074021280d000201041309450441d49854040c20f061750846680da00d215407050110381540480046d4000114800e540046411812003520411420105494140003041107441ea100301c80c001e641010b08040c480405204001c0500203041403061040c240030740460005401d8003c0900901c0c00750040d0078404d91544494407036040c01c0e00c005000c01425020b0010804160480540100c0b261500a0f0788894843d0252500740c0c1c3c562000d50080d481318400035912201061080035141400008c88810359107108000f103901c10701501c0071820710b59081600000d05508049182d80c22036080242c00c00c500c03522540509401000060f40035000300003078100c103180410400030690403841c1d00308050030b25194200e03070200c00e44103840b10301000c500020b84014002c100e00c0304810490421614020301ca840c0c010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 705718039 1250 705716789 705716819
    0x41a040b04030e04021c0c05040f0b0301060f08150d110a09060f06090803030c0a0e06070503090316060e0d020a08010c05071a0403211d0109050c040902090105090a0f06 74
    0x242c0000c4001e03050040c54a800d0084941c1000001c1c640d1103444169600c01c40107061980700142400390800001411176800380c5100c005124010845484c1c1d85070120160268075801e42d04000c210314841044080394140c01554400307001656045003142861034131000003d0720080391a4888198130000501209a1708605e017a0f03072060140d400170b19520541a00e00791001d0155014035041400019250440729000c3c043da0410781c03611642002241001c180030307078008003040d0b92582000501c441e5500b000c1220114003480085941c01c070707a190820080045801290306841007001d400c49000350743c0c40d104558060320a0320002c01c0f0011500002030616842000b007183c1c1c0207030103019a00718050b86e40f5868800da416880701da07042414104240c861050802010b0b0b0402d688015883c900301c4600d00c0b00039500b070301100015141001e0b00700140341500c0000a10b104900340070102c401030f145c8c802081e0440d00183d6014078607840e10240d00000d0504100a402154523282c0000b680401c0f2050b14 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 705719289 1250 705718039 705718043
    0x1209050a2102011808070b07090b040609140939130806010b0304110d050a06090503030a0b09010b0910020f0a113c010504031505040501140702060f041a040b04 70
    0x7084031811821103142250403441e8003800a5205000b0340002c00d4400701d400d07a100448d4a403080d01c46894806611070383c0c1080d00108000b07081400280f01c8803400c640d020141d08011101035840745000e40759035119407000c0300d05854240410b10480c41601c2a03c1600103105501036036542c6452820b07404224019880c071413240648190000001d0302e0400340100c1e030190340c01c4000c05554510810a0012880b00c5500c02c8a140c0300b801f002102103461441040e0b95648110051592800d00c80000d80694560009291040801000402c0800b01351422551091070a4400c105006e4001c84107a0911120010b2241c180c0288001c5c0c0b0100407110300715841020084411900100018450290b85500003030281014481e140905841200010010390384000526140749041d44a43c1c0380c126801d0980d43ca0000243c40d00244001c1003800c0c020015100c1407015690b83c075281c80070000303580c3c3c81c01510000700340040d1000b080a1040050742114045117400c068036060034989000b0640c02012901 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 705720539 1250 705719289 705719291
    0x41112041a04030905101e0905040c030b090a09030302210f10051e0411040b070507060c050d0c0f06180c1e0504150e01120506060a061209050a210201 66
    0x7040c8010001d0403031250003140c26a0328440c4040c1820140004402c003070383d1030002d010134052040c50b2000403144035501c4510741e40e5504503040c508070500c019114a03540000a240c1041c0c0000c80c55210340b42e4160f80300c003100c01d010403a4411810140c000b0302c02d040308040101c0700021b0302e00c1e80301e18000c2800e0040c08c0e4200410442c1d902c503809035010443e82d0045075401802c00e01040b820301d030021203001800304002c00011300c1c071503411002c18141d4842d91000460b100080384442c00d102040c002e50b0f0050116007065070880b05941c2c1c440303894140120300d200c00e006401c840c4c2c0e0148655a9400f110706a4408410060003281140804041da80d8200072554010b03160b0010540c41221800d8100070390196113802800c0342020304000c045e003050700c00a180841c00a10010714007103019000c900030054480118142c00e0b036410603500300350000700824000c0100342010059142e1041c1d40306000705806000094861081c50514141440c1603400351141c44165680660507040c00c451141248003600 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 705721789 1250 705720539 705720563
    0xe1c08070510051e1f09060303090f080706140d0609050f06030c030615060702040c08090d0512012d0308040f0f030206071412190305010506091e04111204 68
    0xa803e9aa04032440b2440d8210a11800508041a00e942d500500c0010420910741c0009803d20144c400c194001d00d074203900c2c0c007010014140c01080c0d08003d4405103012203181418018203550364600c501c546010091004104021105e41c00c090303482221030204140003041d41c03100b406014240980b00780c0fa010104501180103490300050500c25000040c0c042c0c040c1c1ea0310140881c0c01e500368008001c1d000038040000c10016500c0384640e0a00341c41c0350b11402d6450520b41c6000b480c14000c072400000b4030608010807800c0d0324800d6105411607001815809410180c1c680b49441094043c0107001039903a80103001c410040110003070410354404402d54100f140d65010050360341a454031010750004003c00c4030401041100f084040c400503980c048a4078000c01186400c0c1c264007800c1404407440c0346035445002a07600d802100c1c0100300c12624035003000600d1000954111081104d001403894500944290792201d070010f004415641300780680b201d075101491034140310200c404845103e0003074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 705723039 1250 705721789 705721813
    0x3060d02010f1707021006091b05091c050609010b060c12030c07050d0903060e012702060c0708031201050a060206280c0c0c210807151b08011a07030e1c080705 70
    0x1108104000d00ca01500401c1049c1d00c0310144c480b03502000320b80d6001502c0811207007003450b0250614003254440c60042400345008682542160b0941214901c0341904100344180ea400000e1030217188240204d840b650f94807804c1c1071035900e00c90305000501d24000c5640c20300750103802200c4003048031300590040c842555201255800c840004010b928094001c1c180100301035840501d81da4042d10180203c3d1503c4100b60003146016195802441d10751300c0041d000c50310914000c1c0d441e004240c01c3e00c400c5005400c1c08006901c1d00c800402200c16103200042404540d40d500444031170400008004002040104400170b0411030300c4e803416906c640e0910700010b80704664004030754403542910311019040e54035a98810140d44402002d4500c2c00c00342c4409810042c5c0c82c441c2e916040e042c4a0180c609032140400070300a07079030580c4055000402c00500001a40b6001c0c00c40e28503991500e4403060000c05000046c280854441240d102e101801d00903000b04406800140340b81c9014108440100f5074070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 705724289 1250 705723039 705723041
    0xa0b0f060a080321370605090103080a030e010b040c050d230c0c0c0310090209060d03020d12151d100b040501211401090c020303060d02010f170702100609 68
    0xd0252500702d1013011145400c484140d1030b440b600414507084420140303030350500c0c0620b0100721601d10f00920744400c800071070301c03a0544140d41c001d04080d14004082d600d5030f01d5903003140c0204070100050644510005c00f40c4102036114440c0329400500822429448030703001003a94109040140ca02c41c50f01d08221b070b030141000c0c62120408100d85442105a440b96062119600700c100c095281c1c0c420404013141555052018610650803081c2c0080d960515004000e00c0c80c0700a08880e0044459550240129a011030010100c400d541070900000880010074001010b1030010010000310180b0086968021141564000140700c4448843c5e030f03d6030014858140100d01c22006c5c0e2103000c1108011550152081c0003482c0c20002c00b4a000310300e98084a41a1100788082c0f080c00090703c0e00500c124101c600c200010440944029070852600d4404501d12510700b40d0080c2c1440703030601c1d074003206a104041c01c0d0390410650724484024180400d02940e1155050240382e201d50806201050390043d03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 705725539 1250 705724289 705724297
    0xa1209050a03110f07080a0201030b06091e131103040302010c021f050711010509071e1802070809060714070e0c0a08180a050c1e1f020a0b0f060a0803 66
    0x1015009410141c2d80c2500c2d01d03904460360802500507080c09040240003808103100520108018000003282072000400321002480400d1040d070041c804028161a1032543d8040002c4200f11174020a40001c00130b50b0b1001c110022007840c0b03003040b101189000c8000c0c09540a24441c1d0000d00c88480254400c0c1d07244c841c842100c00d0403c0c000450340780b6405290308110f400c2542401c085a242e0b1124098a003581c60071207100c1c58130780c09401c5c100310208001e9401011050103060000ca035a0412944503422080080020a01038020402030284050320301224020100100300554a420030b2038500d070003040c2500e03031554501886400182145908005603c6100b0108c04c0914040103d0400c1d540c078200a42000b0f4020680c40c02c2a40c0d00d0410085040050f005000400300c51444004002000e44003010804207561001b01070315072605d800000c0da02c40b04035a080c0c500701444807002245490423417500501f40702c042c10240075214010038403a90090f03000342c0e400311803151904500c40da00c0c45 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 705726789 1250 705725539 705725543
    0xa0b06030c0d0612120f02030306011d06390a020d031b151d03040501020307080315090a02030f090c010906031d030315090114100507060902040f020a1209 68
    0x40400015401e800040010008280c5018002803010741360700d042c40580300702d8442120ba1810400f000310200e500464070218161a504c021485c40c645a0002010b11840b008800225103011540100340d40d101c40658210000c100d2081d502e1140124140041c41140c13031802e2071010950081050454000c40d4041081d030700035003102990401560110340b0a41e2800e4a251541210118000041c0c07a540504042d00381c100404501c0c04004145021f1503841040e8000042c1c0c41008104200d98010003551401904910f019031030740c3d10030398120709513100704880b2540281d00c10200400f50a899015500900000b490b41d09a5620034082d25a24802855403601007066100c00700151480307a000345c8107041e1001c2e1109840840c1480f00380c078540080c1c8132020a6402201e000000c2d0405011a9005001c503940d0f4030410400c400102e000c1f403078101e00180c20410005440c2d01804a20b4200469865016204021458101c0c064100a4000005920024007005000c1c4080440383c01003034641c0f5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 705728039 1250 705726789 705726799
    0x90e0f04020111100e011e2307090b1315050306011403070c08190e03070e0c1e071b05011812050c03060a06030c0f0810050703061203030209090a0b 65
    0x51540d4006541000300108910034500c1849801c0c001c0700c13441e005001c2224448000403500f1a1115040c02c60303070f10740b101c1c080520b038540041d2014000044481003010800c014051180303481e1000201c0308800c0c150001e004610780020250009018894100121141800c41c41c0e211801048200c4041c4015100107000400300003400740213002c400d00954004607541000015003086645440f01c0d50010030340b0844c2c28a03140312410300580c1100701007070a200c1c101d000c2d041650907c6c4007445410301c0070b09405030311032002c01c05046511111109051600f0040740c142d03201c580c035280c040c8a41c610030340240202180203000246a5008000320401c07203c2103107e00c7c144500b44081c0c12078204c03002501350b0707a5101c0e41c0e0141b0131070340f4207019039400746000751000702c0c2090560900301584440c1d40d001d0300070720710700e2401080000004100b00c040c0039100350300840e4640380c4540440c040e00d811b40100103040d201c481450201f58055004200d412400da6440300566030f403098040480e140c446101d9081 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 705729289 1250 705728039 705728041
    0xb0a18060b1c0e0102190c021201020418051509090f16050d020d0804030f08040609050d0c060e01020a0c08011d01060302091902040b030c091329010302042301090e0f 73
    0x5020b03401c840300f840903034800181480c0c038840e1241d202d011030945100204090744136250035070070580006c0d0002c40140009502d00742c5800e1510240e40d4441c1400410f0b2a0380b0404a00c1e000502c2c02d4000082400400e44031990401203c0795031199003442c41d10b1260302c030303050720304800000744254103046450044c015080700420f80c00340601d0060018080352241c10802000c00081c0f0000c000b005824003c1401c980c441d0308005c4090300703841040d04814800c0c82d410301080c0002c0c040c40f0005041d200036280071010005030000607031030003890420090081000c880041017400d0154022645180e8aa4448205c09083d8054508944890001030740180103180041c2c49160b9100e84181a50300b200c20051610b9034640340741c806034106481c0c640811100040c200203520b840400601c0700c00100d0b208001d0200790007103881c00145006e2004040000e444d19894803603000b98103076401407010400c1d0b200b01864803042144209001c100071030100c0d01c10b0b40c01043d49181045800d2107245880005e03051 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 705730539 1250 705729289 705729337
    0x160306050f0d0501021c0615030501050d1101030b040507031a1804060203060a08070905040b0612060105011d04090b250f03050a0209060c0a0b1806010504090302010b0a18060b 77
    0x400d00ba00c2400d840c41e6400700100000c00400f0382903607103206060980002c0c00e5007801051143c1c4800302c441003040505120060015640380e95401c01180d5010303241400c000e4510005802410310844110307031003490001007006060305608a1a0000d16504256080618a2040014450b01461581c5040c2225800079001401031760003160030040c000c1c60455459a00d0061314907007180c5030008000c0300c2d01e903402d120800110300d151035041001211444a001ca44540855942005115550401015280034200700028803081100b000001d032003400540080d0030254400b4400359894030640e220101e10b0502d40d05615125042e00019941b4510b0044000d107080b0b01410000d044030000950821030b0b41c18581e031b818010304c0600940300181605211600313040700301540051104804c20b0510300507040c04040400d025064032411038000070550f0107400c00328010031150343c0e001c0d04916041c0004c01c10200040c0302e4182e00d00110b000f409004d4903a010f4000034059403800841145d812800b40395 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 705731789 1250 705730539 705730549
    0x10504020f160201090b0a050c01150312120626100e1005040206090603010e090705191e0302040501080604050f03041a160b0a0b010e060403020a05011223160306050f 73
    0x403200380140f4105c00c01d143c4642905500b80e000f444058007107040018031056100d0280503406000c240003086a11161840d00c41c1c20a04521402d8003041101001000c1800040c590046014250b1059002c2244031085c42000980e40486601c0a0510903c100591000164050302403c07004e001e001c0c1080d040c50050710406800040d0080b640508240242c2d056070b21040041c2d4000c3c1078a28051205080082d00d0500300451350300050300800c2590500c865aa05c070800140403a109180c88902e0603490183c0c4454402c0382d608001d608c50304080c00015083e0000540707078000e90141c01a900112081c3c440d03d0b59a00c00d620559181c1569540c441190911040103800100b8041100361070030081c99842c034001000444407041801e58a400340051544d01001900039140196031030761806003940c0001e1000d20043c45441c0c10401218104100d1000079007007114101160142024400c507010a10359a060307084888000c03501c50440c0355001a403003409094100d42014160502ca2a003c005100f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 705733039 1250 705731789 705731827
    0xb310c1d060405150c1c08070e19210611040815090703030f0c1406070e0102070810110f1c05090a0f0201140426060f0f070309030c060c17010504020f 66
    0x85ca03075008180d564070f080000684002e0103086aa940d12940380344c0000003401c2030281b8204203001e150044500080246440c2d000015580c014060708081c4070481091031502003201d400402040c209050039080841100282040c1c58040c400e84e201c03002601100742c0344500c100d465a01d1a44000410000b00307000c0d4820a8280943e0701c3c0004600145445001c00721408010020031680030404210a1692101801038007040910103040386514000c9400d030703141c0c10004441c00e041c2d0b5601200c0e60100c0a001114101580c6a82160300e52901d80d140c3e82000a00310741c2c040345107003048006080201c02054031300000f54003800f1088030074141d400440d05882c000302d40c401483d804102c007041001c0700c0d5102000c20502d588184034031080341065141406000340450714a43c00300410f0160104642c40c03526130003c054900002d4010b42404c2c11540c1c0401c3c200c1c080d00d6a07103040e141c58081540001d088407846019035480d85266601d10a2000324400d04a2816012805101c0b84c8904001501c841e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 705734289 1250 705733039 705733057
    0x5130302010e27010312020a0206041406090d0c1404020f0304060915020f0c0f0c03120f0f03010608090d02030a0207060e03030c070b120702010b310c1d06040515 71
    0x2c3c407424010100d02468920800a8440c0035541800c010001c010340702884c400444c281c0d101a103ca00040c1d400310ba143c6c0254000e800f05c424600c01c5403c0d0075101c42c01550300d5101c0003480103401412a0400c500d40219600440078080700200080d1040c0c00c050080f1071814507071440c1586540e84a840b5071008004c5504122010014a519601101030a00260402c5441c810549503100128698503141c010400d0380c5284942050003050029500410911002084803011903654089001540e0041c8610300c000c60b40070001000210740c3c0d690200c1a03500c541a481e040320840f480094081c1c1cdc0d44c1c019501d802c001130b8060300f0244030386441082c08013224080902200d042c07104c03594006081c030300303a41c119044190002c60740c841500706012195401822500003044140c0c840c1c0041a664813600021341503149103003201401e00c440040000404000080c4204680c0305c11101c0184020140d40700c080d12040741502d00c541c2440c1c408103c80446100800400055150b1004503100790004021 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 705735539 1250 705734289 705734299
    0x20a0804180b03030a0e091b0a0c11090412083103020f1002130f06090b1b0d05030601141315021501290909040605090c2e05130302010e 60
    0x41d0340ca454508201401c5c07885196155940c4000c000300c24031509286c000e00c0d80c6010b00455407840b0020004a08a407035a514918218a01000d01c0c141070220352050001103401811480c01c0005000d410700c01329508150565400c00251624003a103010410054909100c03420540e240000702010540a0b040081c82070040c0e030350b01c042481140f0b0900c04101000c284950b000600240d020710883e0202014200081c040e02029042000041034040c0300d000704c0e1081d5000040c17180c0900845010380700905110bc04032900134031914001003041d003064626501180126111045098081e400c0d0b60300400754a180250303051420840c4513103041095800d10642c000c0110244802400301206400f07040214806190700c01c0034007a00403644455421440b090b007040c8900c40c042d40e2102c0c4c00c203801c19003000323002c1040d40300c1c286250f081201c0d08660316400462148603881b0020315280d4010281120100c2d10003d144049047d209803003450081585d06904101c02e20044d800b80103c91416035000c0c3c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 705736789 1250 705735539 705735551
    0x203090706082703130f03030c020d020f04050a0606140403020f1011030d09030921061a0a060c110904050d03091e030c0203060903041d090f010c05071101020a080418 73
    0x143c0102d40c0344411070f4440c20ba410000d0700007100124010800000c19004006c034110038a10380340140201e42207900203209010200c591720555590059629a810700280200b1081c140007100000624851080c140480c0e00c01d01e2403040e845900042e902203a40260100a1441d1144104400605100b01050620103440d103000c1c00c4a00c20000f52041201c0103400081c04050380c00d001c0c0182d400d0390b1286030021020141e24001007603807541c0d000d10580c000000300f9441c40c600c004800501d9000e11080c4c101c810003c00140840d8007000100f040780c0210744444441071710b0340601c082034408032030140c460340c042040d10340d0040c42036201800b514002c2400e240610f00781c000070011825814000da00044452254506503d424091181c005010100179413900d8549004440caa442002030320308a0105407000844049080c0604080c01d0a01030003001150020103020300039810080040c0d40070042100a09003075400000c40e000642c1c2c1120025007018542498004100f401c2169071065039120b02d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 705738039 1250 705736789 705736831
    0x105180c130320101b0c1e030308060609030601060c060e010c0503011d190b030307081605060108030906190215040b0712110d0207080f07061a0301020309070608 71
    0x300500700034600c03460b00022041100841286050803800c01a841920b4050010000381c0c0c0200780c819900b5503d03810030381c10034807504000701c0c1090789a005240320f0b01c01c07641c03e5420104000e41c241c00d49200e5229043c1a490359010300585004008005416030711000c01800324602030301d00c4142a40c410180401c0300d0110030865802d551200f50000089100031005000024882403846200403861410140519001d06000b07410f611502d10783c160b050fa204550021500c00f881126a0640c0000b0142d40c1d8200c903c0d0b111400b503852031400d0355280151000822121404000c90304107042c0140b03524108406000e9554822104036003143c1544552141c8041d1418100c82091103a400f41c81108071381d280c0310401600e484006c54140300040d1414034103c088600c0701081d508020b5122100580701c0001c0d244c105401d100d0260304240e584008160345c03040099541222621f40115052440355110400034507081c0c0c00142da020141c4e0704034000a010861260940350381c0203c907028440b00c1e00140d9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 705739289 1250 705738039 705738067
    0x2502160303200a030302041d071d040e1204050406050907050702190e18010513050307080d060812070c060906080411012007170d140c030706020f07030909050105180c 73
    0x50f00341200407079008181040138041030031a20441482c0b104941602d8982828010a2404803100521804032841d80301d4640e40c440381c0c001c0841000d11401c035018104d00382c5a100c12500180309a84c441c81c04d107d0085228141728105074021005900d9080c14013982d90308210041c07440741c0d424080c0303141960000400b2082e00010780c0c002c00b001c00c5c001c4c08002c01c1c0f108a03420340b1002402d006454994101c1200010301c0001182d01e001e400080240d1180f00d400b0a1402409095000032034521440f80003106400e246001000f01512550150358029601d0a05803540075942c824240810359810014010403070071702c8000340c0c1200c1450100c000030601c03907100000e00000080c0803d103a110b1017040c010510701c0000c845403003441900138420508416401410f001003080740d00e4206001085510024400300140c0302c5e0315034041425512160b81d607140c0603168101d10720540018091100001d00c0304200c7c0715203410380e900076040a110007800c1c5076240d134444010303150341c44c1d00b80200000c00d00c1d4807071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 705740539 1250 705739289 705739303
    0x21120a1e020d0507090f05031002030405070806040b0a0c0e210c06030c18030a110d110d0303020705011b050405060906091503040213110d1112250216030320 69
    0x254400001e064101004d00500720b01240d00008010861078005010035a0005400c0304111130b2072201581d2540c0f1071800d6418801d466110f0744041c400c0c0c506000800c40076017045446010b444030100708041c0c802d00115100e010a030400c98001d400d030004101880080340244481c003103e042141d5450340c140000c68056803003101caa500c806808a4440d904200e01d25403440c004408400900d0103c540d9113440301070f4900074070b005125110b411801c0d01000030390300032280c4e540002403003924190f500337050140180d1700c040422540d035442e00c1410391520035801a00c50000002c1d585640c242424041030081d2a402a0203550340305105001140c803682e1503000c1d0320302d0000c100c0d090070740300e040600c18400c1c4000c1e03480c512180907003045014442e9809000981c0c0640303180c00804a262016070b003070350580e44110500c02c010b14403100d01f080b4409510148800040c41c000d0640c204c0c2401460040741c1306c40600406074050a00b01c1d0042010920600302c050316401e40441c00320074070301c030380226500c3c042c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 705741789 1250 705740539 705740557
    0x6080a031b1e1b29190c021302030108030319150303050c122802070b25051b1e09010308030703062103080c04120311011b0221120a1e02 60
    0x107a4a6080720809500402032919a6200c0f900c501784103070f1603060604103a02c0d0710020100046504d5030819507035801c690712404600c4600071076a0303584890509890758810ac80b504108180d80d501da80340004284540c02a007800b401600c2d81860441e94110b034594442417840c2682e205110454405a00880060883c1c0307540c01a00c40e000c2040f61848030903420307440d0bc08000e640003d4401c00a0307801c598100c3c0c0b00b0341c004034080c90246900c0301d0260fa0042c00280b01410500c61644864400072000c0d41200c0c00b500101e40f01c0320119000e807100302103907540c2d01c1d596030845e00a500400c0041d02c007801854121001e4200420501e444140100e0580740b00b40d610120110004003610505411810241d0494125200d0700d2915040c01c00000c0c4469501000404228504402c5003000400707500503185940d03141c12a851b40610800e0007581d545c00c20909a112606140762201810180000c9507004000b001c80c01e101661000328030b0004181110a40d18071268201002280c9002413000b800088 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 705743039 1250 705741789 705741809
    0x9010b1009180c05071506090f05041a1501180b0c1c0305060105041815150207170c0d0c03080406050c0606031612031206080a031b1e1b 60
    0x240c036184502420301c2d004803140c1032492a003c00940419408000c81e20142e8021800384070401280b1054002000b4546c000000b0b10318020300140c01600c1d42d04564002e901482821518080402081d454102d084d1021440b009460412043ca54000c4110203001054540700786026941c602c0003558a9009880c070402c01d40003016010031000c41d240fa0325440d400c0b140786c20407551403c800060860f02c0b65004610345010340849101035a0f69682106d14880035208881c0d900694803418084000c0d480850400580500c0d003000c100c00c02c81445103c20920003500a100b404c5100b418085e508180c481e0580d4101003c49000c070104030b5440003480100004d82c0c64a50f5801a10515400c0c4400500500e1107500b12034800d031401100c01c4400c0080c6c81c800100c1e82d200452a10b001d0340d9110124030200070795420a02e00080302c40f00494000000c42c007030f894095031007401c80d9000c00c020500d650700501c00c04101c484103070b0820840e8003034a0103e200305144809006441d2038054030251a41c4541101 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 705744289 1250 705743039 705743057
    0x1030e0d08132108062d04051816060e030a02060d02090a0902030c030f0105030d090e0a0e0a0b0901050c1c020d020906070605040314070506060f0613060909150308090909010b10 78
    0x1402c14210035114411b904240411780d107002c81202d580c001402844500c0707192542c02181903110f0865080070721079003a4084501c00c40782540c2030f41c00b01d20b182c4240030100b0240a0358000e03a0038007003a981000c9038002c001038036000c2d001901c10000d40010301c0454000b0900c020103c0c184071117100440c05101d05289454a9150104a00808400c160401802500610590164550814001001d80b440c164180c03506588055080e001020b0b8002c100015114110b04201484020703804640070750070501c001e01082e40c403405044d24600c41d90403c408100061450b807484503142d075020741140089c00368054504407010000500ba90805038040d603d05558009000030160020b0b248030014000344841d5040840688801f0303141c60004101d00d008043c4406100b40503500c1c60f0403510209492a87d425660b51a0b040c0240444628000c903210386d45441034800d082012003130304c0811a03134840005e078501001041400100328029181307013200d641742c11451213240d03102e4040d005d00d0f4070191750700740c40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 705745539 1250 705744289 705744301
    0xf070f1209210209071d0a1205010c141801200d0f0810092019020622060b12010c1106060d02090610140301120201030e0d08132108 58
    0x20900209000341d2075440e00d0200182c45090350136901080d94100080400383c8001d81c0010300341d54900003035210461000205450a80d020017000d041c3c05039008015030b200600c801d42c1c29031904030301c0c001c910310b007803000e241c002d101d556a460740300c0011305d801030b00e480c0c000c140d119900e407201c520500d05401a90441007c15408401040400310614150b5004d0601003440f140c2400d5600805050a403216080d401003981000000400c1074a590440e90b030f07a0700c00b8414254800807080181c0140142400b04038410034804220442c20342c42d540c00d5081e01215a2280010301c0b210070360035000395141210fa110390320300303114020120000d81c940c040d01c08082080d01c1c1c1800b000801c003920400380e076855480542c46034401c0552091050301e00e404000d880c1d40d0f06844441000c0490060842d001002103101801003245400ca58402c0e05c0620030030844803600d607103801c810071600c400103141400180070710b20050a6072205901032010710700c0204100c1004041080081c0e81500800c02d0982844a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 705746789 1250 705745539 705745559
    0x120c081c0206070e4209010f02070503070e190603050c031027080d180c06080415051b0712140301030519020a23030f0f030f070f1209 59
    0x5400721a502d0050100203500c2c0c0026150b000b00c00c00101400d40e1109074440701e00c2d0070390f008802c03004e40c28020b80c0030007542d51554170294401118240000c10007105100340500001c2e542003910f10040103865054200803036001041c00041c02c0105846031500c1921600000c0d20419014600803030161580450306800d1500e0140c0a80c040d0846510701280240f0002810390b40d00040200c0055100b184002030501c0c0d40e407070180740d00c5104480d2400d400070f050b07118005521050184184994250503542d5041a2882d07441100e000e400c410140312594642409580010b6002800491511a21140401f42000b03900507000442d6100078070030f2030038401c91304541243c0040d150500c07424910360565403001d0f15825800c03443c0b660b1400320101e40c0c085548000b14200500702070070389001f6800702c21503010214000d0740405c1b03020b030050f590f900002c0c81d408603680c1903003904000158a801c1d4040e1420350300341e00101c419180441450000c4c4001141d504081a0b0300b1001c0e40d424902c03504018200d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 705748039 1250 705746789 705746791
    0x4021e1603020d0f02030d020309030403080310090c03090807020d05031e120a060b0708030a1103161e020a020d020d061418030901082214010c0e0316120c081c0206 72
    0x1c051122a204c03d000c402c1e400001c807000814014400b40e202d07201c000c000c62440c062500022b040840c0272040001c201c880880000440381d01580c01c1c0f140d03031403030441541214190040584501c40802240e0050b052450a18410318031903411a460862643c1d0030403010040c81022004039040001d064245110b04020690480035001007040020301c1d004074a0624400d20800070240d0354040b0002d2400d600c103a010800394910f0301c180380c4d901c2c03030084043d07008511446010000b0451402da292000341c81c401c00d11229600c290010501c035101e0f5020801c401c1a001822070340202441c0b0040c0000340300740280c0c810b86100c50032000b03c908180d8080000c20310501d182d800c8542c010f10500f0340316a80200d800f03400c50202c4030880303101c04030541d129010080216005c0c000c4072145810111882c1e0540c0104034221881e598140300c01411000c05483c2d10700c0900820b10001d1010342448000100b90700040d4807481202030410302179440c850181095000e1500a03900030401d11080c510640600c069 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 705749289 1250 705748039 705748063
    0xa0209030c03150f0a090210030b040f1109010309050309040903080118051909020607051213090902060a20060c04060917060103060c0504030807060203010515031504021e160302 78
    0x1d448400c5441201c4410f54000904020308110481c0c0451503003903095001c13007003490300503148220344408040c1c00360151900841d0f80380202e180400c0c40240c030f02548143c145200301c418031a460300c5610401100036001d003900c291460f00040040c49865520b07032061024540c071940b10324040c2c1d894100b01d442e10032042041e44443c10300f0b21041105081c11440080c00f094541d00c00000d4038102c84c00403600d24015800021b1851007540032080000046901034294003118000c20710728a5155231504007601c0524030000d401c01800e000c01010a4003406084001440f82c03a24160803010304040640f03440825149890310b03c8000600380b18140e030010442014002c00107080c8074441e0780c0c1580b04da644405100c040c182543e160210002c0c0c5100d0000c6500440e04580400c1c2c0f50040350a00030000d40c000c4c410644207503050000642c0340001e01068034801d8880c00d5501911495140510003e94854050080030103a801120001c030120722020701040c1c0f00c5620785400100d140d2030041c0c41c2801403c40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 705750539 1250 705749289 705749293
    0x906130e0a050903120432011b031401050d0204110f12060409021018150504050310060e010306020906041d0415110f0f090406032d02060702060a0e090a0209030c03 72
    0x9100c210b4000c001d8203580090b1f0292801090180c071480b07094201e40c455000c0b0040004805c0e1900314080c05401084191504240c8180d14000603c42601100e1071a15001d000481200040040f49800c5942050550000c0d101065035500b070601040b10394042410300d450f440700030400c00c844035100508294420701c107881c2048414942e070006114110001c10030b1701085140540400d56400d210102001440500d1103001c0e40d40d198200508150020b001ced56003e445840012680713500b0314040c6d0380498142c0000311400c2d03425030711244060343c4008045600440100000100b4081c0c2440403a20b401c2c40c0c50100065007060301c0d105503028551070350144814200300c5046c1005202c0b10448024444040e900d56a4070200d809038400c9000d41c1c036030654060314204000060000300c1c00c0801e8070314000702d005c81d000890710400141f0501d0000d0043e421120070311124006040540060640080074200050386046190009220070340032101421003c1e000301d444840f5007401c0044070b0303080307900b140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 705751789 1250 705750539 705750547
    0x140f100213050609030a020301060914060301050c040e0c090901060c03030e01050f1518250206090714040e06190c080603300c1501090c0903080906130e0a050903 71
    0x31145600c056000e40c43c0310b42d100080380d44655408000d0009865800345c020301c1080d0b1b0754001d8500414080005000e118180800500355280c1031052900c21445600842e05080c00e00e100c41000c00d60040c8607101c5040c0030030000205944108050303000385140c2d99404004591403500030156007010702d44151a83c180400d02000240e40c02c0780c56400f80c00604c1c441000502e080c0014075900e0802c60b090520800c843c00d2214680d078210001c0c815600140c40003490b54400c1c1000c80e941c0800320741511039074001180603c50300c2d491030310040007200e004101003803240e00840302a04004050319510100008188210722000c014056035600d440d460500e501a8038014011070b440d030031a542c90210340301c041e0940a0314a007c0741d5208941c80421b100050f101c000147c1081c0d907400c1c90841c42c80c0002c0070b42d00000f46103c45030060524040c03560765060800d520b103039515042a080303180301d10ba001c04107024010101a08440807002030546054454040c2403402509084820240c5200c000d604204 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 705753039 1250 705751789 705751807
    0xc0c15031803081f03290c1206090a020408100608010608030f092103040e0a06090515010c0611181206130f0528050d110a150207140f1002 61
    0x4100513840003240c681e507030040d00c1d4020700652011668000802c00c44030891000403401201c0482c40006150a1945000d512501002403036801424011880410301e900000c903241820440942c002c000e03410050b0410791200c10341c60400a0b880240904180d03610010000418240641002814000050740c6498443d1160f22114400e84218500a156400c100c40a05080105640307010001d80c050700c0d21180c5441812a0591080c0d41009105082c0745001c5074507207842c862280105841c42480c01010860401541c050111020940314181d5815458400c0244500242401d414111400318084522400c024100c00e03c00c0c240400e80c0e22030341c10400040c2c2030f40701e4400031b543c024030300e003510320030910b0241e180c45e40f01180300074041181c01415107628051840200604d109005654884001d004102d468802c00d01c501c400541c400b0102001140015081c9003002e0049800545014182d85454900d010150002042940940c4a0144044051094140c83d84010a055280803040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 705754289 1250 705753039 705753047
    0x3111327140106030b071403010b0a08070e03010e0a05010e0312180709140f061012020a110706021608010c020a080a03090b01140f2704030c0c15031803 67
    0x46004021803046003588503040c054450480d48400081c0002402810b48a140c684020318003590444042103025070140415980181664140c488818645061441d052030446825030090700c9a07040c0811034810030b9254400303000300b0503102000303c01451a40720385e14020382141c0703c0180d00710035500140003120a88101109903900020301c403074940710210b07803450114104070b25540489004c0d4603081a072059110040c035914480e104038400171886039558000e00c0840c4000b0f50307140300003902c1e541c94501c800c403203035000e401e6003401450010030284a000c070309845c042c029001a40540e11003c011412a180040f20b40090500750f4020b00c15201c251801a58030030045200411401d00440c00d4100c0b5446584400500340e00000e00b116a540c0d500c00110701600c3c207688071401080c0e540c48082640c18078548007a280303a85a41c0f2036240c1040b841c3c960000d1035000d4412030810031020354440c081a04002418054402c4003101080c0d0400c0282c041c0456800341c40281c3c051500600f800c01107604 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 705755395 1106 705754289 705754331
    0x20a02010911180406021e0d141006020d0c061b0c02030705010e090f3607060c051005060312040f080d170a0c0203090a031113 56
    0x108070280807110442805401203c4003150110b000209254020040200310410503544905900c0c07105c907140d0700aa001c8d100d502e0b141c0740f94142c1c0d00307040401a500200200c501d03450840c50440c0c060340b51001400da144c240030400202740c0130704c40e0682000d01000b0f007644021084900407803010304404009901a4040d01c200c0002081950051145481804006082c00c0c4607950740800e0054800b4001c05802c0400203c0e00c0c100d09030005d0a1031b502112440803000c407200030340800e950749008100d074031280c20015070b80c01200c00b041010a102d04c01c050315910202d2035548503000f107440c1c0b45141c52980b03004200041c000900780c00c2d45280c0401c0d40c203090269204420401c1048a501c54140914001c2140c0d5202044902d03081d41d00c03030140d084190042e00e04008011002900c1014654816641200070146c0c14030f2525049000d4215084042020000b12102c0b101407179107005 = true := by decide +kernel

theorem cover : BRFrame.Cov 705575539 705755395 := by
  have h0 := BRFrame.cov_init 705575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 705575539 ≤ n) (h2 : n < 705755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
