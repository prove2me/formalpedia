-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1679
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:11:40.945969+00:00
-- url     : https://prove2.me/submissions/b757aa5d-84a9-4499-812c-05ee25c88cf1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 301798561 ≤ n < 301978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 301799811 1250 301798561 301798573
    0x1b020d08040209040201030c09090f0903080c091f090b13090b010e010815010207080a05010b0a06081009090f20030d08010b19090807140108010509060907030f0204080111030405 78
    0x1403031064065078822600100701c6000340d2100d400541c010300d9192074181c2000380d41c18000c2026505805084da0310024034100040120003404c0c0180f02c4000500088080d400802c400b01855840300407a4400a104030422400c550a0b6001500ca12120390f0000100300c001041003080e80b800f000b40401190b08480051200001c041c004403100b00c0d100e44420f0101d44640007203845204140003a6004440600441b94440c1c3c42d81340c414682403142c00202ca03161b443d00240401c1e41440e042d40001400f95040c900c101e401c1251502040c00c0e07040c051550040d542c1d81240c0c05014400650010f00d940058404121040200c1d07001108494842c2440c024410040c044400300e02c03804956040750baa9130762040c2041c640518280803884a407509008000802d00040b03001d14007442a14000c0603140c5000e0b007441882d80024058141c164800c03442442d00d50100b0502e03486a80f1040d5000c1d03194900040c0d00c10f40801c85500074003447d0007411056107030403184408000700200440c001c0c3c0c064411188 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 301801061 1250 301799811 301799833
    0x131505070c06020a03020a060b03160305010507180f0302010311071e0203010518030405040507110f0313122a090603080d0e0601210c1a07020a09150e09030405041b02 73
    0xe40c40b412450b00500607400303041c40070040b800d5a8441c42d11294002c041e1051844503040e400361400d2f07650000c0c0c2d07080c0d640e02d091103485500303c1d50a000603c0c4806221004a2906215482c070f0340e60780c400641416200c0c04400702940064041310482940100801c480040b0100d00001030115020304a0296213460049903036070308682e1010501c120f048008614082c2800c0a1101070311010300742800744003502d05400f900740d00c00d12983c0f900b4000e05008640f01c82003d1245c00e030f6590240d000c140c2c0c001702c80c92340d02d005c241e8002e114150382c290408441c01c9848900301001c031400550303000207403ca00c1c103c0040204441000201185c10790f0440074003000302d002020503220203082c840c0c001201000d203000c6410102c00c800081c0b00c640284801c1d10380303030740d200f184017110f2a055051343d948030f0000550340214a172400d500005410140000c022410454141b60000034050080c0d107544c007025000180030001c10401c540c00360001600c01e010300c0244071548401c03150b40590320b20160040b400900 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 301802311 1250 301801061 301801063
    0x4030c0c0e1003061d010c2c15090f0604090609050f01080a03140904020711010216180905030c0f0105100801230921030601020d0801050303040b131505070c0602 71
    0x28040c0341c44900151040d40703580c2d1513400600349210344018960300c411a04010000a2050a01c0c1411740c2d02c91840d00075448101c1401c0c148402022003030f130898030020380e00f20b803682e865440c1d4125140d03120540c0c6246690009060490400d0441c0d800300e40001c011030031704e81d5608400120b135036103072050080d03403100240400314400034014400d450f80a60040c901103481179460340010b200381c00c0107a1425402c0c4010906030b03842200d042d1f500482d0903400300d0142d64104242190a0040202201b4050500044030b050000c000303882401c0603201c03100b102c1840024030460b204440c00708212108144911842c90181100303c40702880a2010040055035030018041c044052499040c80100220140100d0070283c1002e451100c1c035119103443d040800c07207000b64490350b052010150b25120701c1c0034000207240c550703200501000c1104410040005807400815502550705154049031101c0c00da0360ba49418a06903032080b40c02c0d52048590700360341600880100490381c02000d10580e03141e02d030300f410303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 301803561 1250 301802311 301802339
    0xc080d0e030309010c0c0b191416062c0615010903080930210c06130204090516050f04020313020127030303020d0b03060903030408030c040e04030c0c 66
    0x289406030020080a0020f41c0b01c5d103070300703450f49116180340c1141d10b40798441c0300802d40101040c0e080c00d0403402c41c00e03480260408240301000c3d042c600c1071450300381492217080c181d56007540010071450b1107102005081c510040340c0724004c034081105a0b120040380c6c040b0356452400303607907100c403442ea003001c094000c2d442060003000352a0006078052078100d40310b007032114a0500000081e285c8180c0190404c4004a01f0340d51305505a900c4014001b003915281244801c2c1c1c441c00f981d8151880800c034503100c1400100343d481c1d0013503e450404c3c01c07482e01400814041d14414000401034098000b0003a8038a0409102000359a0b0070348540010307150b1402408220311040d246108140d6012540c880190311400600c45a8103802c8140c0440388035010b8000060300a81d0001c0f40842e401240076201150309104800c51510114010003050070014495600c0c0e00c0060400b428442c0c002002804454201c1c0c2100e0080a00d0080c001c0c1c41d2429060003040310300c0c01ca200f05d41c1c2c42440c0c000020554544165 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 301804811 1250 301803561 301803587
    0x2607030807050c070b16020910080c0111101401080d1418010201060b0a091e0f0e0405010b0907080105090a060609141516050f06041505070e0307030c080d 68
    0xe0024a489110064030180c1001040c0c8030306100b41000410070328201000307805600d10548103440308203064410444030290040400c9541d5400103005c2081041c0040d550303180d0082030811484258400001604104a1303811000a907400c004040d41c030403407989102c6040307440e10801d556181071005000c481d00401864100c103005018025060904540901c41c441d444050000045641e03543d18003a09640020058001007011038504203e001003030941c2c100c050380178111a0401c0b504051400c4a444c00310701404604265140000c1e04010095000505181006022030007034035260000a00b05c81c800d00501d40610010808142481c11a014807070550f40603880c0e99046d14180342481c41450920601d07594022810b07141034054850940041031f009904070200400405141850391504245405203401580b0035010040890716480d01c0b101108001ca00105082c0c031416022500030f014502201c1e458001e1000c00401c104003e5162000c0b00e10030000e5070320140a1410030780d00700116900b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 301806061 1250 301804811 301804817
    0x150b0f0d020f0c3f16030f0909020910030b0a0e0c040302010e0103200a21020a020706080f060f0d060f09111801050d050f07080304030501290904020f0409260703 71
    0x41131030748040c0d0b040c3c000c1444d112060000d90514080d0502c01c0c0d40f82da07583c00d00b90003160000060310511980510003001811040b00158507250441000c911115880e05400e403c0698814003e03002356a40744070400203004002c5500311904081000507202d42c000d200490200762003038a8000036500a00513215900389000c0c152241c981c0ca989440250b83c05071860208104402081c10520301c2205400150201200401610707402a104040e00d025040c1d080482807145032820080d907504a0020990300100c10343d00441c00c2518900070a203088803040000f40210f06200079602c0c0107400750301085625020f221840c248d00050001e0044039a011016003002c0f069031f00051119082015203c50b00a10030800c80301074260b40d018503401c003009504150380384d400002d010020301109010303100c10b258424451480c003044070031491007580c0c15034803814024100c100c002000e40daa00c00c05003e00680181003808807280303615100c00303040050102031010005001a40c103092418105441c52554561 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 301807311 1250 301806061 301806133
    0x1e040b01111902040b100c110d151107140a0c05061e0c0f0a12030e0d080a0b030c03013803250302030a0803040303050901150b0f0d020f0c 61
    0x450710225442c4a00b406a8010351505041d8000e902c03800c000600003c060703610405103002d50b2400c0c810b840f080b822000e118131001207943c000f042c035401c1c0f20482a00300c0440020b281c0f201c0ba011011900034248082c1080c6150740340441c10540c00700703480c00c2c414800c078456038103152075004020381401107004482e090b03100303141c0b03603041c042102004100760031550045513440d041c1880c0d800c4c0b401000c0c10044407035240101c10b2581141d014060902ea0000c0074001c1c00c0b07403c01d07400c002002500018030f070840b49602e03084507220035201800001031500018000b0302100841c03a141041d101441f2101940c8428110f0400365a0104c541140300354000080c0178102c4201d0201d140d0580a01c40c0044c50141100c1200000c0140e07010406050068410030a154481c80c181c01c0180843d40028885400b60b4100481e6009554040b220902507c0003240019190140390038025004c1c081c9410b041e40b280e04c00901507414040120240404c17a2140d01141d50403002d03040c0b14070300d141d600310100c0450004e81c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 301808561 1250 301807311 301807333
    0x3030f0e0a030b160c02090702010914070303020a020d0206070c080607020c04180b09030c01050403031b0305061008090c061b190c03060506180f0f0c0a02070e06010e1e040b0111 78
    0xc0e600144c0340350502d14105440c0b08694002071003c1409881201c0580e40d02c1c00f0366410011406000071070180044080c0c041a0324507100030f501e0320580c3c1c1000b4400c00c1801c80d40703c115516202a030342c00340d410696800c1d015446001c52aa07400f4142c0d46580544240c11305900140b0f882e000c1d4049002c060340d5070401074101a9624844014050f104003d14002400311200d0b418092044905c240d00a503004510300e080781c041c0020103400381c42ea1400300742c240070402c5481d8903903001941d0501c001e45070840301a07070780b02035640c10010006583c82c0d11100001e04083c6402140f00112201c0300e00720b0540b85100d03003c000d0490062954480141a102a01010800300b82c403a8070840d445a0041c042504030070039060448021030307088540390800c400c2c5405208009051410036940204103206291404a141030060b540c0c1c2d00910174001d45035120400a045640304205401c1840c201a1400940f50a98800b065113250000c0229000390300d84890b0035865880f0b81484070801031440b0140c1158181 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 301809811 1250 301808561 301808581
    0x62d040201110a061415030d0f0509100c140d1e020106050411030f09071202060c011404050304151d0405090a0c1508130c120309030c03030f0e0a030b 66
    0x4106a040c0007446180b4038030080c0a10030200f50a104100025840c0082020780f00d04000180c001c056041c00307030f800030400c0c0d140011a044841c1d420700305103414030700c2c40900302c80a216030160160001d500104c1c0f11b41840d000002044c20b544598200100071854150150382d90041c84020700001d0800c2084102c040182484142110814800859425112030106054810001c0f074008192000010007041c0210584541d41000545000d045081e14021018281060715013020380309140015803981c10840951040503186050b007000d1a440c030303003420300d40d40f40c0e0864441c1100880b220110950013902c81c01800451402403121084480c003048207200c0180402064909203105035030141e80803072030100788000103201d0902c036002d40b00290600185800f9015182141b9406c1c003204201c0060a000e05050543e200304000000e0004c03581401c548090040e0f0001c1c1050400754400300603d0f90082c4900e06402994407450150b003d0740050000c002914403000e45183c00a401103203800c45 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 301811061 1250 301809811 301809901
    0x1031a030a021003061520010c050d0f0b0409030f02100608060a0509010b190906050a050d0813030f080409062103030209040e1006030c06080c030f04060216050c0306 73
    0xb0503c4d00040c42d40e00c0303610341c0303903440d94140b013010204100030002114804188500040400444024840d699400d0000340541c01885041900701d91244c4000650002321b500c10407505c04018000d04c8060310506000e09800c020700d90200050044000c0d050040d41786025010071100880001c001907a110700c4841c00420340075100a14554031603181c14481d40c1d65048200d90604c04403034505200703203041320000440d0041c0d40136600401e640e00b020002070761010b42c00842039800c50b81541ea00c01210004d1301881f20550802071040342000080c030248120032019001342c85810a007000343d151108041074003c2e64410101015107415000f9200291180c0c000c0c28542e03070060004070700700244403074990030300355600946090719984110803c01d01c05075860400050000d0308103200340e8240b41046c00920300c40106a01541c9890344041030400032141d04031141c02e001102003c0c00701c0400c0c5413081e01c56040b5600e25101c2d00c50040410a4509034091400510f920b003060307015002e10060f400b01c003010f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 301812311 1250 301811061 301811089
    0xc060409050a2a1d041d0105010603060e13050f0d030e10022a1e0f0d09051e06040902030405060403022503170405060304031e0f1d04060503030d0b01031a030a02 71
    0x3080308113268250b10703180188031440201880005001c00b01039440760031280140d2115040608180342080052640075010ba000810041d250a1004180c03d001d0314003030844800c525a40714014603521841d0f072590100b01200c00104c143c40c0991000d4290405a01800c8209180002c880706450038200160444030303005081641660764190040d0400000e0034250781c0031180303c0e0452511038440c0c00c001c1c4002400481a03040c6111302e54209000b0804a407140300701c900203428a0415456aa6140702c02d0b02c00900f49601d00759500c1c506413508549600781030300c040f009403040c0411200344200d94880e00300b1900d950320003038107004c1c515282c00480000824121806110410011855480b0440254071490080d01c82c042203100440314281c102039485c01160800c201541c1c6940c1c0640d0080d20241a403c3c0f181c1c680c01022440000540180202d43c8025494840060030041340e5805400c0101c3c0000241ca041000c46800d1800f11800c503152602c00c1d605030001c900707441c01443e0001c807824441c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 301813561 1250 301812311 301812347
    0x103120e130b1305160806030105100b130509010906031101082e0302030d090f060e0303041404020c1507032405150c030a090521120a020c060409050a2a 67
    0x80382072042e1084a01c00d440c0381117000c40701c000c1050b180b50401307481500040294000c014038a880c212141900b101400750040031500041d9031480c140410450001828008003000705550b5510190002000c1d07520003281c1214400103540c84544c0144641031081202030301089140e890005020020a844a404001c95000d00800300141c1c408210610f42d200858807541c50355400d2036030604a8000643c03148007040013455000013652001300551f412241c1303015244001c2041030000402a009184a1070000e1103a280181303910010301d0f100a001e108540c80801075203c4010082e0f00c0c0d0300c540b4048000031804007104124a06204a080e0424104030720a80d0400c9041c0c0000360465000c03925440000e451500c041c00703540740680d004800007441c0e0080d010004841e550362505c4244295118160f54000701d80c0034640340c0203200100407031100405255980f038403640d02000030203050b2640c6e1201460300145001803a09010000a69210601c40d82d48540232a90100c50030548100321103a4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 301814811 1250 301813561 301813579
    0x70c02060f1309020d0e0307110d060605030a0b15010c05030415090509040807061107030f031a15041a0705100203040f0606030822230301060305070e0103120e130b 72
    0xb8200c40e42e407a10241042000140e41e4101356584001a6660940010741c150001c0014000040a4207001048440141c995461000701170801303000030401680900e0f05809080313100340030015103c00491041011000c0b0800c507071315208c011656074a00640080241c1c0c0100014040c1094410307960310f25600318501504c98070303124800304140c001d0139a002c0769120380c0800d40604000490003080700803003000010354200542a200200303201c4081400000f41691007880c1c285903101c075510030f18074120280c5072880d050107060103110190f000d4428544564588540407059818040031107070203a4018000340101d00390458804001d5101800c121950031001c0e40210008016000d030000450150180c20f80b41d0042c00d102609030303603480c400c140506044450604c612801c0f074140c4002400e500b140c50410720700d9180800d00401d01508003401e644107040000510a2080b183d05060341d00c1164100342c5000c02000c1a10030700340c0c0303c2080d54001c0304034584410400003540040b00c0b40f1402404002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 301816061 1250 301814811 301814827
    0x7090e0c16030203040905010519090c09170a030e09010602030735030702150c0307120f0510050111070f0e070c12030203071709060105040509030c0105010e01030b010b03070c02060f 80
    0x801c4061010440140c1c2012030100f207904040d201d483d0061000751125012400c1115003c21080c5c1540586100d15548201815404e1310409051000c3d00d6590440c814002034000655503c1c0c0048500701e0005003040500203050515804590407900c046d0011410709001d5512200c806811103050b1001c000c071800540b40740100d40300d01a400810b01d441042c1c0c8c80c10302d5840241072410741c201034900352205c5000e01c41c0c4014040100c90703004269103007c1840c003900800031310182c00700c03100e805002c50a00e01881000c07170743c0c0c4000d0307001c59600b62280c250443c00310321a9502c0f0349040c81001e401c0c050b042e030304102c000518407407035502c8405072804140350140c585d9036000c241195418a40026404000c008030071340c020b4405481c0c1d070402920210a4642401d20641d90f5005004081c042c0d61218081000a0300803c00d079907040b1781080080c401503860700015094043c1c24803040d60341c01514400005c01716154021640180c10650340e440c01e0a010741c0138010747c6d50100e034602a40303500c10040c0c90 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 301817311 1250 301816061 301816087
    0x50906061e0d06062a02041a06030907050901170a0b0411031b0f01021527070303030c020d0e030613020a0816050a080106061d061c2307090e0c 63
    0x12442d01c0a28800045040c2412001840581c1c5000c9a210440104181d0f240014128140c174010940c1101c010950882c9404201000040074075143d40201c3c0c00701c00c0c060403001c040707540000d44a007550144500d0381d0726628150900e0000e0040e00c800c0d0003c40000c404146000c15080c0d2180c0900c40c580481c20041d80460300d070007403003d40300070382c00070098400b529441d280b005545451030910040a401130400452081900050f041c4003070b4503001000b40300c94008841d1070748028002c5030180c0b511b0641c0c1e403c020b0050141104c01e00018010701d078200c107007240200400c2883c1d00c0054003c0c022583c0300700c840c03811740c012040305a900000b504000991502d01300315841c4140d104070144810300e4942001d1112610352500110300326410001e00707001d0564080d8000300e502c1c40c4503200398075201c003190101d81a48034441c400c08140e0220803415008180d107400040a038510345103102004409005050110ba0042e10003c00140213118100304e40e14007814601c7d04040c0c048a06490803850201c4d030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 301818561 1250 301817311 301817317
    0x9150a030911010905101110060b040f1d040210020c03070603090506090a0b0f19060f180c0818071d010e0a060503030910050918180304050906061e 65
    0x3501c452003501044400c035000318280e031082c24240100380c10b20f40003032100d5090b4000c10b810403001a10780b5a01c89001c0107003080001e0b41714001c00c08035480e0b96010819601901400b280c2c2c40a2a60004215041805000c2010b0058403451032549441e4200f204a4280d03428080462144108a51080d501804030000900171520001410404c520b4036600b01a001040d203000d50300400501c0d00410081d41c1240d90003003241007041d849507284004810301c44070001c02140e00c186440340109050742441c0c48041031740d41c0000c0f00c100300583c40c1d0071070050700c08810000c03000039000400b240700d000c2294540200a24050700703903900d582d103c204030800d1245440f8070700c07c0c002a1f803004102c000e101c00031884d081001103409002d0f1a00740380c04241e69205541800b401448007080d055a0284a9401e95a5040d8018a28110080300765103024442130242d44090701c00e41e482a100f0003c00000084070308070b035009400c504c0c195440c10100045500203045450130f003031000313100c0c0720945050307002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 301819811 1250 301818561 301818577
    0x90613090606110309100c031e021e0d0903020f0609060705010902190627030b15041506090b2107082208030a0c050d060f0503150402090109020915 65
    0x10005030705152007002440c045801c40d4440e0075030001c1003101d16a40710250b80e408264100d0078045103409861030200d4400c0d540c1c18a88068101010030150b000790f0100782c5805c5028080b0301c2d440803e06180320b00e03445260000000c80410f910b0602000142003c0781108a10800100b0260400d901f4030b000c104981d02820084030340c0d942d191608802c40ca014042608141b5020704841000e5082100c06030032806011000c90780d148042142c0100001d03c0c599140203154841000151402e1003501c8007664601035403c079101d503090021111101400c0c2c0a0401120115507070740c6003052801e40d02d0116640041480c0c80c0b03842f1800c0d503005c4240203510b0428041c19041d1313511100c600d088041c40c0c00c0c081d452110900da217114903116001082202c0207480e0000c89200300003030003410310b0300d082c0c40910403c3d000100c0c01d4100300b03000509007072b100c241e2012103070203030203545000c0c2244100d921000e03000c41c2d0095010780308200502881c1003a40c050500000e003d8040314452001c0c0740100c0e020342100207 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 301821061 1250 301819811 301819829
    0x2408270a21031503140309131e050c09010813020d08070b0c13060815150702030708010e030f13181d01050420031606030509072306090613 61
    0xd03030715420111516155101d44042c50b0400c424049000c041440805a110140c03100074102c03481c445224052084440c1040002c082c1c0c4654035141c08000d020f003001c1294844c0c5180b032211a42c425100e68001c1300e04c49d98800e0082880c05010300010b4a03107000242c008401800141100c01c0143c480e60180d00009010300101c507100c0b4454039045103601c10060407040700001c18001440d03840d04070491b42003942d201c3e0401300350540e101c621220f01c009810b6040c81e031040204800800ca56510001440050f00075002e4800040d10384008500f03071a600704800c180c0764803c004001080b12a0005885100c031312843e2503070301d2a40d86050400c6d80014000348051103507542d20a907110b881c6442d2078540489210020b00c040e180c035131222500b41204902d050020a00141d040b85595014410b0358100001c12541c120504e03284c4400600400b0300700c070243c4c510702c500d00c0089268800080040000c085110303440c4982410001404190740000c5e502c80d401800502015150b0402c101a140152280e89 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 301822311 1250 301821061 301821083
    0x2150a0605031623060903060103031124040b06060d0c0e011b0b060f0a05120d030518031603030204080a1202010b0a0303080a051506132408270a 64
    0x40109410480541c0c0c0082c0d809200210810104d43e450000820036500310b05103003000c1d00c00801080342e80c0301c1e0300307085541401802c3c0088100b5402140040c50002c001007201d03411300006c01c2200d10369890925101500007030a000a001810800c14a0f9111201900c0242411404e040c40e8050f41e6230100c00601103038100380d4040711564003650f00c15419030f060704401d1310044903488841d03011002a09043c064000705640d10016103032201c8080c014100a803508a01080a0310440c3e2101e0f0080f070600002800c0c000881e80780c4003c00c00e101d4818403980080c40c5481e08200340604c0c00518004120113158013400000349002e414410191b03c03900440c0c2c09004000c540c40000e085035054070516109100c01d035014408282d001515550255440000003403d89501d44218215a03403880d60ba68031000c0090107640e0343c5219801503046030880f580403c8403409900040d5582a8424001350004421000107180b1903414001504112454140003540c001c01000d040c2c01d000341e0030070a03140b010041d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 301823561 1250 301822311 301822319
    0xc060708090c15090f011808010917040e0106080a0b15070b01150504061b0804060512060301061406031008072d0501020c0108100e150f01020a05030a0f02150a06 71
    0x500c09080295801c80340307144049480c1550f28610b02840c500c4a01038079103001c1d00001640075141224508640008070b969140e95180300c607000e0440207504075000e80ca808648a241204403054800b40c039403600d2410980d0f82010030032525100300500c850070080c0c1b9101c0941e00d40d220482ca0303000c0c09101002290f42c444060603d200700c41d4069100940510b03c0304062215940d221059400f51061840c190310201d2001c084200300581480e805030140f040043d00213211030300311008208000c07850700101030680c1c1d90000c25080790440c0c8034075840e252444800391303202d10348032000315403000070702e42503a03021500c4507070461034032480790001d0070802244005058190900703000c0403d10300741160008502070416000030b442d00050901c48d41400003000c04200c005141d90100000b900466451068511702500200345000c04420010b000d1340f00c4194904d0154400304001e000740e90808002c41c076182c440710301200c014203156407100031401100000c001c0e41e1002c0d41040d000382c3c3c0354a400301d010780c10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 301824811 1250 301823561 301823563
    0x191104030b071707050705010905070806060a1e03030e06070b010b0a090e010518040519060f0b0306100302060a030b03030705030705010501060206070c060c0302040503030a0207090c1107030f02060c06070809 91
    0x4080d02038003c3c800000360b4509048480004103910040c0361901c0c076140e0a45191141c003525019500400c00c7c002d4850100e00341740005601846024200ca01c0c6540a0f9141c1c083d45002c280ea4004680c0032051000c1400131038002c41407804900009040b080c0741840e1038485001120b82a08807140f114000030345401c40550005d0320350058142114080001d5240030009100010070b500040d00a03486030001a0034410b0600128007007015800c0c0100740c500c00761802c000284840c11054501c03514102e59a85641800500c0510500a001c15079080c80d003075800b0014103030060745140c0c2c20162a146049640d07103040c0050160386204000850325210b030b6140190a43c0c0d01600000110341c0320400f006903659000401c03042154020500064414051038106c0c0079120f41c2d000542c0601c800100c1c01000350b4002079150450355a42001c00c50142d038030a00301c0d06c0e070017507802620050340006028004104140b40b61b1015a10042400b890b11903000b02007810000201da424003c11103103801c100d00340d40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 301826061 1250 301824811 301824833
    0x50105030c010503040b0a1b02060709060905030a110a090204140310020901021b01020106050907020d0f080106090b03060f09090604030e090705070b15151b01061d19110403 76
    0x801140603059039000040002c0840c0401080907186656900120380090300300c0e440103980914201c1c06a80780c0007150000395580c40c09503004400561208c1000411611600e42c00060700e00041c050302c07106106071142a400410b18507061b0b4841c3c6e04903400192a4040d01c010801403500c404040c030903206910406050001c19090303ca0307070030300400203281c083c2c2c1d001c00d00f240b40941001d0400071030012000101d0060415400131a0080401400d00003481c0d00012900001101a5221140c40c59005404c550b0030b0800c1c17003280d0100e4440c00c1c080c800b90045001a40d032103d00a003e07a21115280c5001840000007540e48101c2d580040040c0f101740f40c1d0002c458003d6060036580031030302d170401920084c02841004006012070b5000380100301e81981d9941001045080105407100784050a1601c020b90750040080c03d00c0744103001032a010488041c0504411507141c5014080d0b0480c1c410804848500000e029100f5072060070b1601c440081c0364481d440c00c1c0498a00280e45680c1540b401328a464 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 301827311 1250 301826061 301826069
    0x6030203011103100b0c01090f0f0203010c090503120703050d0c050405090c0403020d080a030b0d0623040b01060e03030d0216030e0d05060a180f063201141318060501 73
    0x18500f003042000085860382d015040740c03040096690344415024061f0700424814034002e2240c440026410f003400018419120024001c900822240c024128107440d800124840c82d501900b103005120000003000d00503151490080c20722a10f0407a0a004010890304000c0c00d10000c1000420300b0300c03081c1080004194081494006c180c5081c1c00c680002d200c04003095070080140000003901c84c0200d00c40d800115032001c01512403180900d03203250030800342418441c00103419040c60440c01d25848008080d1f8040e98122074007180710303400e142e4111040d1551441300c680500c410410b528502c0750f01c0c801802e00c0e8a02d030080344c280c0022450001d0418002c0260315200d00c06841c66640403030302c04030f015504080800d00000320111510305200740060354a10140444400c0782c13103a0f00b0f208003504409580000c02a8003800a4170350010030045925050802140e0070f01c0e0b00041c803441d0294140013440e11802001c1c1c140ca030401c1c52194040e51110140d08014a480e40d10160400003e40a03480c090 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 301828561 1250 301827311 301827341
    0x3040c0e1510090801050f01080f010605130f1116030909050103210905120f0606121515040f0c02010f020412060213030203030720030309090c1e0d0603020301 70
    0x505011120705203003241100070911031030703148500032080303805584078074002c14903840240400c0c83e1100840356150802d1140d41318902410400316240d080c180b28110550b000100300c0c0030420140114040140b183e90884000b0030f07640c0781c1c09080036102c1d10240c400340c90398080c070304108202d07894004c1050010350300242d1000d0608005000003034036880804981884024a0740e410882c000302100c00c08126402581c101d00040306a040c015000705490405644000880300c10391a2507081c40b580b4041901c9001c529085800c2d52404000da04c2c034120f412070590380a0072203041010380040d00301e5003d000288042c0c0d5a5442c0c20154a0702805568030b001c8001c13000310309107481c001d148821003005140060120780d0000305040c00c0400d08a01102450700941181c0c3c40c0c41e5540f03040c490b4004805402c40c07501c80c1030282c880203407900000b12182c002002e000c1c08680c3d2102d49440202d40c01a00d00c80c0300554045401003c5e82c51440054603c03080b480c6404100545140103160864030202810100c0c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 301829811 1250 301828561 301828589
    0x60b07051506090103020121050a140c070803010e18100e2b0f020f0a03210614060913090c0f0b03040506011511010203010801090b0c03060f090a0e0a0803040c 70
    0x85507070ba020604d0440ea020b007040c02034030f4414856111161075042c0c2c510034440c6800280805451668081401410a1102c007102920f4081500220340943c14004003903000c1080144a4001600c03800c5401940c030a03612521400c2c032484032410004c42c00c508110503603446a174049104002c1101803440c0d07408410f00e010102c90901000300d00394000302444240301d42d0034912201c16200700114850311100e10300b40c400c601d856140080c40d016a40103031560700b80c07840d0f262020514061140c035044030300f4205018014141704040c0102e0380c2050a03410b51001070000c564051501070b0081a01d842d20429451201c903003081c07007801c84108640c0110207249c20034410040041c10000d80c847c19240011030402001e442c11204403649040140200d04550011000140340101500030724000f6204058401a517501e0000504144c002100c9555025000b15410b4400c0e042006090f070b006031030400007040c6600986541894003510031800c46400c1c10010401003444421804100546587c0000305a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 301831061 1250 301829811 301829821
    0x4050d11221505040e1c14040f060801060206092a04090b091209130b03120a120b010f020d03050c1e0711040507081504061d04050709022706040306060b070515 70
    0x59211540c0381c4200401c1c03514891000701c1341c003d42d0a810301c01100b912280d500c0342ca03880303249d40824107485448085150a000812614004502c1d9445540104000c040c1030000480c02009480040c0e4952220b01c204c804031070703507504e0728029050103078091038080c1c900b400d10002c0585008501001c9007007a4400b4000380c1c40c19a01d2284240940c0c8143d40082943d0035458002410b00389405041c900d007080004508081c5600445041c4034002c02150400c40c4855480041d10803203c20070680b0016044550002c4043d40030340c0c0308980140c0a410910b04250043d01601d1490f243c03440e554016400110f2450b00b044940030080e40b190001f96400d00281c14040400b500c44d8001810300d102c4074541c00240380b035039100c90744544c005105001130030101c11180541c5602d025410b0f00c043e5000d0190300800300d408645030003150700700b8280b000b002500c0300c101d081c00b5100d4405844030300c1d03201a00b000b000012803290f014801c094580e4216403035481410740340091422502040314280f55040004002e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 301832311 1250 301831061 301831063
    0x90f02070b06030c012709050718050a060503010e0907230310060b0a080c070203030d0506120a0512070201030915060f0f03020108071419080a1104050d11221505040e 73
    0x4580c0b4540848007180715641b4004c035200280fa5604049081c5203880100210ba9900c4110100d00391030703140400c1f500c1c1c0d40b19018846800403501414000c5007080004210680a1040c42c80d40082071200b902c1d09280c50b1801c400d102d982605a401d20b080400c1c031090300303502d8240031224501900c0d42040040340e1512003400c5150190f40ca640092040250000300119103c0701143c58040c1e0003001c1c0c030b5650444900f000020079040d02d82c83d005002c0c10025440e80240000d450462a07000402041081102c0c84240f90f25408803070100d04160b100c07080c8100150003000b0184010340f601f803004c80c0140c02c2440c02101e080072a48880b882d111407540400250342c1154146401c0740b82071800ca8894400d01c134680c0103910035640125803040c070030070b0b96aa03001c1e4405130140c00317000543e40601c000d40890303454982c5801280030315680504010400c4002401d84c8155090100b005041c5940d051003040903034004040f46400245030a440d030402001030186145000003400c4100c9080001c600d50028907 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 301833561 1250 301832311 301832327
    0x120711070321051e0304030203070b040b2401080a1509020304050c01020f031206010503060a0308030a09030e0406242604021c0f14010b0d05010b040e0106080307120306090f02070b06030c01 83
    0x410130709030000220b003d0500c01d00881d4103041d00911030503102e0400d0702e02280d0221003180c009800c500700090110b480c070101c0a1203030444005a40d0320125864030308458008008076060010780400240340092104054000b03148124000d0014250b604014000a810b0a000107007003240c0d83c00030002c0400e01040d8200194000100f032a0546e1070395212004070f04221000d42024020a038040100a48655213402000460380b20741e0302d07081e039103540c44107100589080703000d4101c81c02401000600610500b04181607160b00601e0b107c01c85000d260f20346001048401c403100104480c200804c01542050015080a0811000800e0644000d43c480085c4002d0b10040142201000449803810b032200b500240101080100005143d000601d0194000d20b01c01d00074601840c2405080a011383c018407031001102c00f017201075840c01085680b06c000100c1042c1044003803654500020413041d906201c1c032404040d20440050b6521900e040004042c01c3c003d003a5071095200c040c03c10030b070340d07072050036 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 301834811 1250 301833561 301833607
    0x302060318010204090e0c040c1b0b040512210c120a0507020a060204060306050f040e07030f0606120b010611060603070506310314010501030812071107032105 70
    0x9003a40801c4041a16000e44102e40c4401042810500503001c040d801080180c6441d408940030004030303400090558105000c3d543c200d10031452081c101003c65048049540c0c0203100c2e200340d896551081c4080032680e040278011041c840000080c0d003a4100c04503450f2a0040141405681009071a080a0190b0480240800801c0d51104003141c2684e0003089100c04da1a8490800d544943d15018010010402842120b1080302e2140c40f459082c2850320a01e1042414000035001684c21605c5001028000a10881c0d40594400c2c0000308003041d807101c4e02c0c1c10340c0301d140a91381551400d280240200d030343c54800d110300c0c1c02c80001e01c03c80380d500080000031240244d40e450b0f02d845410f5414603083e03218807884800701004801031a60860110078000549200710b04115902e0354921006088910900004020341020040c0c0e07040842d11911113a40110145010400f6040c281919814402941d00480300a5a01900a003a0010a140a100b51403851416906101181034603409903030803ca8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 301836061 1250 301834811 301834831
    0x2010c050f070b03100f080a0615080d08011d07090e070302040801110409060f0e040b0a0e03120a0c02010c0203090d050c0325050f0f1908120403061503020603 70
    0x400c00c1000d204641c41c1007900300503604029919090000241c0c0112010030140c0c00c451404a440010411102c0994290700c0007020404416038812004002108214180703141c1040e000505040c00c000810400601d5034900045500d130503416480c8000342600c0515180700103003000300c155488280d0404460b079140f0309010946408905400a00ca10f4201000c0c80d4207001e030080035940d142005004403490010200030755039588001116082c01c0d400340e00402050710005c01c01296031003031041d41001c51030300d0010340340ba0319007200380c9140c0c0701c6042e0142407100c45040200409640c4208202e9140d240002d001c0e03295010300003500da100e48000310307110b01020024981802410031030201400805422140607107100181c80381076205203a03d940002401d80c4011940b82011494900e041c40090f05820720f4580d150100441c0d600d0309038150244030a46400000c0c1e1900030003c540490031720b4070515a4a0f4294106841070f160401d4501004000c00801040140c076903400b200d511012540e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 301837311 1250 301836061 301836077
    0x160617010902030c18041b17090303160c1a0702101a10030e0c04050705030a0609021c021608030c040315060509040305031302210d080103030e1309080f131706040201 73
    0x1c002130b0040c546000d41411f070090072400c10150f40c1c1c00036107900c08021074011488a640d00c17041e150742e403444211200d1080070203286807440b10b68060000749104c03d1080d400807001610300404a0030403001142c80d880164498000085405010700c2007240f80811101c0c0300c942c1030041c0021a00348504401346204240e0f87e000c01c00c0002005001000391240e000f81b043c0941d003000d15000b40590000c1c1d0b021030340d0320701d41080059400080e1080f50310800c14103812202e01161f900d242c90081d04603810001040001555000000340540c00441c86400d000c450380c0c2c0c46500b903050201c070740031946405040d000e10b055030a0011f65100303c11981e000c2ea046c40e06598a43e40c0e91007043c2100e41c02c0c0360080d0403880c144104001c4001c02281c48078090195030841e040da1500000882c1e0902003032002801050124030386132060b040903884445441c00d0715030003161400030342e542d03d40f25611421003444044c4020444080b40301302c283c6040d005103240f40d031300c4d1650102907001c01d450303903030140000341030107580 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 301838561 1250 301837311 301837357
    0xd0b0112080d050a05040201020f010219050702030f060c300117073b0f040602030a02040e0109020903010c021f0b01030e0a05010f051026160617010902030c 69
    0x4141102c1e08201c0c030503070502040c10140c40d0140544000ea800303e0150050a01c192111a01442916526920324181284124038401c0c01da446a007d040140c1c0c05014840c4040c112000c2080b4450003100b441c802282d803880b241180003107501c0c22141c0b040101d035070201a40b60408801070341c1c070f064481101460358141001c00f03010313103000c10b1039100d0031784014100355044007400d03100d020118038407072981e0344800750005130844034170304600321403c2400c104401c0103d0046100c9d540655441304400341d00504c1c0ca911021401728500c1c00764000c0003080c1e000201120281402c2c0900c805030f6210340000c00c4280c680e0041060b410988004c3c82a90390798030644203682e03071f01c21b400c088114907014043d0f41c81d1401c2410628080c1883c00c00b81c1c1c4107507040c0808075a82d0419030001d082118030055241c80c03100c12010001d09804d1008010804a114800c2c04144656140244400030151a19118014841c1c0f01d940800544140e1050076018810300c1002071007141b070011a0351075110610100c4a101d48 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 301839811 1250 301838561 301838573
    0x10060b0433030f110306010f08180a08030a1d0709020f0d0c030b03070b0301060f18030218010303030b060702061605070f1805150102031926150d0b0112 67
    0x10044007808050110141c240a5405903c81003007055400802d1110000280286045110956080d400030309034040e10740d01c1c14406c4030034036006503d186044075908882e4040c2440d2003203400007074440c06000018800310741a58806c0003016542400f004071101c44000b8150388810302846100c0000380c0001e03030054000030ba002115205241070004000d00490150b008008110301c81009000f880f0310030000ca401c3c0003040c00d82e03040314499514076108810004080f5019100103200c50410307005140007000690360f20745440042c0d50090002445503241d07003001810b0f0b8443c8481d80c0e000310020041900540c46080c21038941120348444e08003841605c2c91710314a0440780c0da0003034881c000001d0012400303a8002d4034203400700c011820140b10039100d002400f0707a000c001c4800d95015030f104000202505d1000020070308803004900f001d51002d400711240300c581c48840540e1015a5018804012075200c9921040b403001c0b805403119006481d0640e604d41d00c10406019150310303007001c0c1c0140020094 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 301841061 1250 301839811 301839869
    0xc01080a0e070f1418070e0d05010e0303040b1303050304030c051e010b0111060f01030204090f06020d0212072c03071d01080c090906011401050702040207050703020310060b04 77
    0x19144102d0720300a0352101d46041c196418026020783c0f007918680900d0b28540540c1c6044c44400303464500010782c0b1410400e451068210401744c2d0490080024400800c40038419000300c500c5a40c065a0713603242500c1c20303150480c401069401903505100080c004030f503000068a900c281c1c941005d042314031880c14520325100d5000aa0b00944140710407175071440381d040d0450110400280c8070320021313170801883d60382c68541c1252100c22001c0d41c11300410240c5003941050003100d01078121540d001c0b07125164441640d02403540804c04640000d4030100074800003801682c811260b240c40424154040059279100c030444201500d84141101244002d607070034402c82d00141248440f003071280060112109210754248501000c5018042c0038648900b0b1607022541719042710405000903a0074001d2080004c4201181e160401209200350310040c0c0740c0d4030060202d40e0046009210340d070715520405190a00072006480340604010b020016000c11000340e50940d041c0140040d9601343c40c641858980f4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 301842311 1250 301841061 301841081
    0x1b120403030f1719110c1009020a050315010e010506030402060703031a270c03060112020703140705010b0301050c09030c0f180f0f130309090c12063201020c01080a 72
    0x202e4241800203120181000c0183c2c1c0004d440140700040120f4050300c180d000e10511513401c0c1e000400044c1d8421844d6100c0c01c0c0e45803004064410940e00c80000c289070030f50348008070807194800801400031543d0361a51500409080ba0840d1441c503082c0c2c0480c1040c001c40000400381034681006038100c1d083d40d100c81e0740c200b401414402240d085c29603440c68801340b080650b15003080d014007140310f80000c1412a4800e00043c0c5480c0150600101c65400950000005600300a00b03050360514802490004040301e0f80124004100107003d08101400c4800181140d10780503c10891080a620301041c000e40241c02266500740c0322042d400030501c491944518002c41c21524001c000c1e0041000520074007540d45040480b070103507940c514802a41c052604054081400900f0400c4000c5039030b000b03140c1024403440c0100c1d428580c504401c0542d0030340d030440001040d902c0c29101102c0540314442d0080034401c41c03c00100201480040c0d102c060841c0f642c1e0412016000242502446030407129950f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 301843561 1250 301842311 301842347
    0x70609141f0302070218070210060e060f1302090303040603020409141b07060e06040503070302070b030408071707060c0503160c110d03020a08040311010e0603041101110c030a081b120403030f 84
    0x7070300d0451f00094440401450310080c0d1840c014000ca0000204504a4424240a884411715090b208204582d980715230103600320741c035004c000381d030b409440a001420061035280c40140e01c80d810541840f01796a840e40c4441c85603030014041200f029100105000c0ca5086681030580d1403025080450103040c140003990118801c26003400200f02c800801418014082c1d42929071054075029107103a98881039070b010340881c1c001d02008000c80e0038510025500c1d002c0d04240d61a150031a0756003c2070796001c038945030128002100700180b8016040100e50074400900e08403905c6034140e900c2c030102c0202240910300402000650b00c0c20075008001c01d90449420014103500d0700e5480c60502c5486240400715030008400c510825180c2c1400c500b628003540e8020522500c1440d98401110000c408034003070105c03449204401181911b041c00b074605000c0c0110071803a56600f070b0020860354006001428041c90340480400c620003185402641c00b540c0d41840d2410f55007014400c111041c0d20050349030303014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 301844811 1250 301843561 301843609
    0x91b080702060630190605100602100218090a1d071d06030703170309010606030c0c0b0601120614030c15030708040204110301060816030b01021b0d05070609141f03020702 75
    0x801d02c01170300000d5441e441613105010035566110040e12500042c07140301d000d0fa00121401000c07468580240c400c807070286026038007800d492070025000e40c0c4d00740d40720200c0c0d903038545410000342a03600502520200d4030000388803503480d2000da10200c00703400f46412400e10345080400c0782950140300780d80081d500406031000d007042c08204a5069881036418091540c60070034000b4166000b80101050102da58070b6001a08016850f11554058000d101904000004035035658804c807078030032003000e0b0601150501040e212001403514201200c003c282c41504180041040c2c1884401245e5001c1400d142c9500c0507107482c40424041d110461070102c4041020001140140d40b150410b441002034120038240560b480e00300f94111182c100b0402d00681002020864801403881c0d01c0d0009100945550440c2d140c0391261400c00d1669049080003d070080030811001c07403a8040c1c152684001c8410a140420081008040c0d0094100031003d140c1c001c1804800d660b00c0d40f000300da82100650655003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 301846061 1250 301844811 301844833
    0x30f0b15040f0e0c04030602090d050607050a0917030a120204030203102903100b031006090903080c040608070c060b090a15090504050d0302070507091b080702060630 73
    0x8010703040303801401c110460081c0300051031403241c4803040c01010703071480e07040c5441e0840d200c0034040d5008401e0b150700505113020802c0050000c2080034400e80007591410380382c10389400b00a0816005a00210700800c031440c800c80c0101021048030402c1c0302034242400c982d44140c0d900000390050f580082d61600459070b01310a440c800d0307005000c0f440401240c41040160214422a80c210003080341d580660000461040d04000c0354002103003090010f00711340352481410303007000980d0001d4000901a0f40c651469508041d0000c200d2a0800c07610f4556508140c01c010700109880740091115040141503201030342030080e1a4800e02e000304015002c08803d20380103280320040c040110034000078620000c0001007180c4613214040c016036210300500012080b0300c00c100d02a4101c507000351480d004000002900100034400c0c0c000444c2e80340f800c1c40e1240b0080e58003408812000b844401503400840400c030a41e5185610198605203120307840c20100c542090300c1041e8001c91000c80254820040401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 301847311 1250 301846061 301846099
    0x70320070c15020613080c0a060510050f0d0302030a0c0c030501020c0f1204060516020f0a081b090402330a0507110a0503060106050f091f0801050907050a030f0b 71
    0x1074156011440d42d1003181203000412642c4030000c6510001560030b40c020a800900e24000a080d03e0b01104125022880c0e140c413404200d030b00960394044090004c002c01c202d242841444e08102141c1121440c04415168030003039200c0c414941e52100700800e1071424000c2206028070403020316000301c000c64807968000752507a0350391004800340e00030f031288181c0c80100d440238108a17803c1d02c0081e036525051418000e40c194403542070003c2241d204a0141041c1913548810020788014220340004054603560844540c02071003c40700824001c035032410801016807562090810048940301e10710b60403d000300c01007040111000c4002280c11340018500401590110140032164010714203400c0c010007010810145144074401d40d0307007581041004000d400d008001821003c0348604c0c030740d1b00c0e0075940f80006542c510401740d5090840c82c0ca008141030f0540c48a846809044252109400d074200050003605030300034040710404044c0c84102501e0050f240da00001140f000241c00e1400d9140148516 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 301848561 1250 301847311 301847333
    0x60912081506030c0d0b04020417061012110f041508010903080133030608010204271104050f0307050a030f021003060b09040e0c09040c08010e1507032007 68
    0x4600700300c140079607548945016000c503400f40c02900071140c036151084620300003400389820800c3d4081d03800e01c40060520307081c0b6409001d100c03540c40503056518013041e84500c0d0b9040d030b41160140e10b9070107582000194209149105000084441c003c0b80031900e00003402a02030b030001c1c81c0060804802c0003070034140542014103210310a0b111007e0aa03200c601c1c8409030840c2e04680740131075030854115102c40740204400001440549800324140c0d8481c0e4420342aa40560300420004420142400e445d0400405802800040401c1404800c941e26441c09850140d0302441d071040724402124982c0d968100200001003601030148801140d40e4101029400202041a40220310901503440203621130312480302034800c1d0348034643c10324a00f0404c0c0801000c0780e1071142c603603120304180f81d134171a07407080b600e68810b82c44dc000688046003441409820b4900415050b00c09034084000c1e114803d803030801c800c1d44034840d40740000d05200504000c51841205c034100c404140c4001450206002c42d42c001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 301849811 1250 301848561 301848571
    0x150c07080a08070201030905030f1c0b0d0b070e0609150a080f010e0f060a03050f1c020309091302060405100e0306070e010f08090111160210030908041206091208 71
    0x15a20000d55541046849860010300100000340801c601001980a40d01540300c0c1b038007810440e400c0800310a01002c269001850100c0101100c1e400301c40030070480d0007041c49085040c1c6102c13500c40850364030100c581d100504140c0070b010b0380f110010910380326642a1f0300b040e0b00c010540c1040740341c03480c9405d109a1104608100181c01038000920710200e00d2012412100c806040d4034465480428034440403402405480d0701a01d13103140000810010001d0802100b52071010345a0001c0008400b05010390708840203040d5042403020203019511407000340d40c4600780001d4140e08503901e10028041d4800c640150341c0c41000034032181e003010342c086405c82250380254100e5807191207c4c0030546900d80e003840d00500150b840321420200d18031500c60150000046400030961981083c908181c2d50070804032500442e00d41c00c102c038154a00070410f502d800005041c2040202c0d0b07547c4800b03100317209600803000343d884070601402c104403139503000344003094101d591140ca800c1103000041032241e013510 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 301851061 1250 301849811 301849813
    0x50a180305030a0c03090803040602031b041d010602120f1e0a051e070b0a23181e030304120c050303010626010501080a090606180519020f04050915150c 67
    0x202e001c0c942d1700a2240441c241e404c072443c0b0f415a51180e4a5101079400108803404007009020490050f100c0a4051b001408104501d2142c0f032a80341038000401e08160300000856002c1c244030b16103507401008440c0140356052920342d0741c0d00d15819022300042c0040c4204006070000980c0300b01280d100020b40989500700001d03001c10200500c00684c507000700000504144140b4022030700001c0e4a52000110384002c039400d200031000c04c194510a11821141424600c80c00020301c2d0a2040500681c101d40c40c6e01e660200d000501c4012483e540e010085c4010444400d079800490118011385801c4140e40c0c1c0281229500c0d038440000500110700007502d1845604818100f4008444041240341030311070682d9180c1c41c96a808900001070b001491080e1000c0307544200c046140203244080d5841c2d028889408a0725050029107400082d81e80031030310403914418481042c4c0000e1501c11142200c2040f02c150f44951912070f030640030309580c08030403076004001d0f100d07803902940c0150140c000165244 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 301852311 1250 301851061 301851071
    0x203070608160f0e0904060f0c0503010503010e0102040f03030e032a1e0d02041a03060f07020c0307060503130602160c14010207120209090309131a180a050a180305030a 74
    0x900540e010f811036940280410841310b0980c00504140914030b0307100c0e00546001c82c02100030703107a110072564204207800024100000501581c1824090101c0010700b5400842c80c052802c80091690750142c04014104258940010680e039010004181034a642d00800c2d100c00107101d5400c0d80c0948064141c60007945010030740001c8602c024090810440081c141444003281c0307508000c014200312441c1d8401d0101c4d803802c111070f510100725452080f0a5a0300310207207414201c80192400510800d0329100e50f000036001c0c00581c0e88142074980080707080000d120888518500342010340585030404800740414690803081c001000007007012070700499136650200319840c004a0f21200030f40904840711000207071300401030406050303241d4882c4141003a00e08001c4014006443c800d9280c0038054030544880b58a5605284d070444180035800441d0f9896040ba59000300d41c50f04240104190107055a440c0011031356901c030b4209010103020303035805074503020951601400f150000d0faa0080c0f614508 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 301853561 1250 301852311 301852351
    0xf05010f021914150f060f100806010c17030412110c13090c0b0c010b0402190e1503070309030306080106051c03020c06040902041514041a070203070608 67
    0x54404000035008650140c1500c400d00c8601221140e601c1c00700f10786a16481c41c02400f80a0b0074045480d0050008040c074003e8144070310b107482c050368003400051080740780c400d400d052a950036200078103122488c2040390b2a692004016100f180c4031203000780c031040c00c440704d8409401500d00207510a03441441c4c0744054141007142210b00480b846d402a9a692015103290104e240001601500c403041c0c41000c69462190754840051400903400036102c1c1c02c000c910000211b5081c06550b60040c02a0740444c205202d00d180d0144d0250203400113018003421484810035515011030002c07480301500c0d8030750341d03170700786140001d00801c402c110942c0024908880410402018010141201c00080207055003040d10b2503442070503c0c80030421030541c8691400c0c40c5a43d100c0710041d00c0100b80c40e200043e00c0e9840c00250301c0c0100755010000c002c000c000d5400c80c1c51003840314242e03410342d050341c4912810356084407100c0082e0b216440c0b0195151080d03031000142c1c141c0c00001d040c821003005000000310300700 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 301854811 1250 301853561 301853567
    0x307031a03120c12040602071809020901030b1906150f0201061d0c1204051501051c12030b040203340503070810050d1a150a090b0612010e010f0501 65
    0x1000040740d058000c40700d00c2021206880140c240c0380b82110640744115415407400e038056010390700c10350142e000480100054001c02da44440004001e41083c400910658002128404140001000000300b5004540d420401e02c131341a0328228808000c1181c0341c0c98a204400f2034015000000001d03926204110304c551060250204680115071551041d025056613101e4008000302044a40d250174041c3c00c090619246255005a0082010b0020b10400200040001c0b205070041e41c01807104409222540d168458902c2640c0c2d001540c0701440c0010388070460107088130042143d4030500100501c13507000882e151508003c1c40203d14501217458a9650380131001c0008540d1001c01e80610005199a005000307281c3e011407041c030a042402e854100181425007c0c210681784e030402d86041d04924030039a14100e03080303021408462001380c4280009480307100c0c1400303600205901d448420b1025210300303095800a01d0080c0300c3e610070f0f68441550300401a0244188142400104800503207940 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 301856061 1250 301854811 301854851
    0x9061506050f03090f0a0b0906150d120203040807030c0e251805060403030206090105010b04051e0310050c07060f020a0f0309030c060c12060902130e070507060c05030703 75
    0x480780c441c82c2c18202156415081600b00900156180c09030380c495041d140014402c95180520400d0700e0b860038108040d16500c1d1950050100d40e10b088103c2e000d1a0980d03840850a80c004e1740b000b0344088650010300100c3c114040d6510161040c81004404000c000c44080c0610540d01c201095120540d260703030002d5441d0041926000b101c200048135456000d20503080102a48122500c4000e22603903080420800da029a0040c1c0047c0c10207810b012185c039081c007540c0d0041980c0000d031801c0a041c54006250070b20141c8100803080c81001c2145840d031028044d1180001c1c42100800132454400c5030f00390076900038034003192824a040c1365400030140078070035122004d84035900d01c061401100829401020350a00c250180100c43c403910002480301e015801341d40300c0aa403046030031601001d00701c0550700e054110003809030050050500345c011a1070040d0480304191088031450f125800f041e1502d116460002c0c0c0000e050945410b0141c0d0004000c40c000c0003d9a400c0100280d960b141215580c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 301857311 1250 301856061 301856069
    0xb0906090105060d0b06040e040320060c0d0b041a010206090307030e120109020909010606090b0c100c140f04031106030402091602151302090603070e07080c0913090615 74
    0x403552006020341c1c00c200d4040c1100310303100200005c040c0000c1e0002000c5402583c0010441d5035528200f00c2011f6101c507820b06450b0000c0842c3c240d07619000c482c1a258803004143c80c2e10000c001c6161440003207940c01020104001510800c034480180d21b8012030b914044807094054423950700460380f01d20000048481c0f1540540c5c404040340200d10402500c1349400e4140c1206640b10710400c0c01580d181c010750743c0681ca64800019480b850640702a00083d11035110314420b0105110584608101144126207070450400000e0300c00c148400aa4010307101c0d4444c2000e450740401d500c12103650f103100810075a4050860126040e55001c00c10407a440704a400a40100c0040081104010b9110f1440e02d01040c03801510140d00005000d600c411a040314042110510300d8211b0047d410281c07800350300720b036050300503004c01030404024407989500580340604004244e4001504490786400b5581e44c01001043c0b80850f500102010002c1c00000c441510380c145000d5134802c2c01030328001c19008407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 301858561 1250 301857311 301857319
    0x1030c020318010e0607060c030f0b04060e0c090d0c09050106020606040c02031b030409110424080f070e090403050903160f050f0d02030a051c0e01140901120c020109060b0906 77
    0x2481104004656138800c00514640040c02031003c0703000201d05009403480c0700556507000a00041d0121410f050f699a41205400b9a2511b913003400501e40300d4140d594000c407a0094a551025050041000d41072080809090190810404140c0c4521600138504032043c542c00c490b507544454080004980e00b0320b13540005039108200c0000081060690402d0030306420080d00d080c69519002c0c9000c0d140c440c80c030b01481400000c0d0502440388002890080488000480c01e083d00003900080e12228010380380305400540c000008004611400c3c2d404007645000e8802041400c2a103001f070081d408c45611540f0034094180b103c00c88003444d40404080b1210380e804802c007245008103024000c1c20b400300c19900311110030081d42c09130310104014070361648280e00400031021015054107078050000002c6d800c02004811080e11681d003e00740c0c5c8060003641c2c0c811aa104038110040c0d48140b107003458500c9c1141840c820042d03440d010f5100c1c1d440e4032301500c802e00446082c20204038100008031295a44 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 301859811 1250 301858561 301858597
    0x3060b0702010f03110414130501120b0a06031e120c0302060a0f0605030307080c120c1209010e04050a05150612012c1303031a0f0402030a02071b0501030c0203 70
    0x558402d401ca680d883c4400c0c14000307181443c817503d61a003640150801809203c00c0582d500440c24a002c1245101080c4842002030354180f42c4142e408140d0000050448564040450190031840e80540d00840d4090030481d1440300c040d07402030394a0400340302a01d140c000e500d21540f00703074021120301c072060368183d015100d03c1c2e45000401e402040380150004400e555100e001c0b40c241c03030400041c000b40d4024041642c4504002c1956460140189041d6140b00d0003030101600c0a074000035407802400200020304d86408607800100c81000e500d4461a90107800c140900080f88110b40c071890213900f004241c0c042a040082c1407040c1c501c610381d004131525492100400118180700401c2c101c00c1f500008282110382e104001d2601e882007541c503a0000c0413505405402c044d0144201c09900c4101d10348000039240f580c00241003101c64000c02401203400000284c1814420390440d00d0841d80704418010601c00e942d8280c041030042d01843d07010910f41424211402d000000740c8480740092a45155 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 301861061 1250 301859811 301859813
    0x1606150b0304030e06130506032a0a09050d02011403040c0f0501020c3006070215100e06040504060b0301060b1b1519090803091b040501061704050309091e0703060b07 73
    0x10341b0f0f0b00155100902c4200781c0c0d00404d8030340c2d030746000b14061030401441c030001d40000d07100b2407c8455529130201035420104021055141c10800c1c0c0c0e0212041142c40040c0780900d1b000683c0c0c505890031030341408030340000411041000452940080e90750364100411040d803542d00680e81c0b00360202d00e10740e200000d15031506d041d07180c00c2ca40142e00741810070b018211245c50042149022802c2d5110000350b0400c1803d0700140a20342001644240325507422405a490b0444540c0b1489016180341e0056480380002018080705402403004010090000c0224035a10b6505401603007001002243c0405418a000042580016984c0744104220809906501c44180b4111407400b50182c140055445d82e01000100d10210007a600c10030321748024208009015a0760100300040d00a2144620b1404005219803644086054610210417445962545440c1407081c558002e01c0c410310390081400b0204007400c122045903810221007280c03042d0450300e034010280c0070f80e1094001e038071180c0028041c0070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 301862311 1250 301861061 301861069
    0x9140105070f0f0501020a121b0903110a0f120209060405090d08040f0c03030c120f020c131107051501080d0503070305040609050105070e0a06080c0d020f1606150b0304030e 76
    0x840610624500302c101c3c2d1596265800da810440403a4049507031113459490b441c40502507112003c12500780038014082c1044040e00b0406c0703602000e07100210607000ba546c55261101c084001d0031240c0704a0440940d40c03180707413060340c8005030102d004000031030200300c1038142406401c1c0200300500292076148101101200c0e00d0a00030004d41e1041510f0121a000c10100b42400000e50300030750300e26a040d110750810181c1103201c81000800c010186800c0e06240d90b01041900c15540c048031b005018800b500801800b9001c0d41c40c500700c0c140e030300040a104000000801426115103400074010766a82d41c80b00d2611030701042c500c6004602c08000041d8513601c07a41c45107900ca4481c2c0300c000392050301034503205c0c00c41c1c000303c0d400b00206800c2c40004038149882212100100000d1504ca501454418803422090088100104070349801043c200303480d005003025078908071700b1118013040c8017440e41080005401c0c082441907006c05e0080c008588110050b040340c2c0704039055100e038402202d0300001c4c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 301863561 1250 301862311 301862333
    0x3c02070c1401050706050a090b070e03061f03050f070501030e03040806011517070806041127151201050f0a060509090c0d0f02030609071133040f030914010507 70
    0x1d00e040040811400c0c0c000340d00d6206042c0120b500e10310025000e0385d103207810324103008080c019006009a1181c4a201981c001540d02e0b408a0310020441100071040d504221600040c1c20090040c00346014801800c200062508200c403000da800340507100c120489507859120358050703084036030013040040c440407468980c401c05a90b040e18001d001040038000c403c0c0d100e0015210100002c2c0b034030050024500e064000d4000700241115298a04016240c0c0341d1a0701c0442d1003071242c490202801c55801340d94044003822020b08403441c0555601b80a400c04003450801d0080034400e03a4601400c080909000400805880c130307d03141c1c035141030000c3c020065008801402d441c5280410050824110401e0060f103d0114413840c02503102e00b0080b0401982010003424101040761042e07036120349030b0300000c103441c0c1c2490030803031044001c140c1c04131900e60741e00c4d4035408491138402c2801d00c020456411718840000d8040d585440c00d10b900c8041a5150100090501340000c00c00d212400c0401c0d015914 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 301864811 1250 301863561 301863599
    0x60a0b0712020c0a063c08090c120d09060315090504210207030303140702210d060324110901050c0102040305150115050405030a060b03013c02070c 65
    0x4076091100c00c070001070414213031600840005060082029170311150b489a0920b0102618542c4e81e112000c0d002454204032a20396a42c00c02c11400f000c21001c00e0144404005c2c02d01c0600038807020440341071182c2da90070035043c5020014041c5e800000e1440c1c0300744500c0703401d1240200104445880e0030080009850080e2099850004405c6001030f50110942c0550a01d9185c1e0041d009903491420003404943d9a01005483d0106071420400b65540c0403641030194040711080b0001241304041c0e01107103024155000582a190260100600c200484a1240d52041212084447d81d44c942e002c42034601d072020481008070b06000400f8a9030040f0003900030b14044000040c100307640c0361655403070002d4103900107054038010342c010302003850318020140c201d036000d051152900345040042661082c00040241c0103503035510a40b0705907a000c1d00900032070b9091480c85441006103400c055090000d04080c256031440c2d40f4015508104c4038000d42c0c1620341c02904a891440c0b030b1038030481d84c0d6141108 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 301866061 1250 301864811 301864813
    0xa0302010f110115050111010207020a15051603020a1203020711061c1104080f0703120c020406051807020609070308041505040f090603110406140d0503040801020c0102090306060a0b071202 83
    0x2211400c400904c505500c0c0c01c1025a00190b03149000009003405030051031551050b4010000b840141c1c50316940f0f401210099440480c1407842180700311483d02990400c0285003082200400516600203810414980a81d42e041c61a20030000c0640480c0705445004151324142c070001c134510b184ca00050f150303c0d04520105600e4000183c4c620342110a10201d861690401180620022904005805000e50004003c004441c00c0d6107801c1181c0203c1c80e0201e0130004c65000c03244c210f464981025004141c058000e4a5024103084504881c94044883c0401449050300090000300b002402c1030440740c103c01d0041c0f80030705282e101604100303680010f20501004010005601c1d1040e15000006c052581000405a09519110801d03411401c40c2511031400c00e1424071245103003696903510301c00c04950041d103440c414540507095000d0746d80b200556502c0443c840c401e00c0019001801c07440021401c0da146541c402c0c0070400c07803c41901804a900d4070034000c42d40041e45118250000b4071140c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 301867311 1250 301866061 301866077
    0x414010b030114010314071805060d0b04030e01080a06120b0a090c0b0c060c03060a0b0d0e070612060503030c0a200603040606031101030902060a0c031b061d03090a0302010f 76
    0x80101c2e081d00e04190301101c082141030010814481c58585c0040403008041c041c01c100e03071500700303031040003001071259020b441c0d56a0040b60803582c0d912400420542d0040c6000d810b486c040c10090200707400100b41c140890307002c400050303d0020300d20480044c2c1b400c0d08690f1202c416aa111070841460045c41c8140c0d080da6080d59501241c191030101004200c49a005562414240c100e40c0c205500608411880030003841030142d155103000c0701c081603030070130b04400f41c84a5130059a10060174080586100078050403001080441d8030181c03286013869032803c01e100b6543d5500a03d55039100c0c0f0f1150840c0c0d50090010040010502002e544100382100c200101c083c0302c0100050080d40255012991142d540c44200200000b000200c1c080017400d00f41003008003800d401082041c4500120041040340c0c00d284841090300076a8824204415003d01c958815054502032008200d00d6840242165002001c0c00b04605c00200710303058104058a4254598955801560b40c02c03080011a824030944d9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 301868561 1250 301867311 301867331
    0x1d0d021f060e040c081209090403140d0507050409140c12061302120f06010f08010317040f090603020a0503030a090e0a0b030a05060103061a090c0306010c0507030c2c041401 76
    0x1110b42805035005a00560a00c0c0c0b5058002d0304c0c00c00e074aa0286a2034078140f100b0b141c0c039507038180c406500c1500741c1001400c04920ba45100e03004d02c288110080840e01c0c00301401501503200c0b010700240c0c1c0a032a4100109001014400e241807802c031a0391092503800c01c0707980340d820083e24480340c1080c0003800d10418000320418000a07a08522007180c140d00d40002001138840300c40c03d00c81d410982c2802d00c0e000301c45820800a008820500001d8524010f2514085500003400d044030010304040c0d42e10a8410344401c03010020f40142e1009911654141601142070b15000c412150540c8190701c8000c0590f240c00030440700b00c44014500f48003242e0f2480180c25540b0140400c02c1c070030b0f200e0405007660790f04500d8140c04840c0c42000c100c0c4042d00119481401780c07140d0349440e8102c007407021032035243d40c5d6100048424003422040140540600b550000810181c850828140c03551321903a0791240245c2c0b860b08010802817500d00406c4100217020502081d40304800d02020000c41e40041010130314 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 301869811 1250 301868561 301868579
    0x20307051c17040506100b2502270912040e0a0f021306080414030313020402030402031603140607050a0f050315120c0307080a050a12211d0d021f06 65
    0x4070f5040d503081d041a030810402c1e5030415081030140440245050918070611a010060814079000383c0b5203110f081d56000c15540d600070b8810007102001a401000c460050492503601070503551840c091051031003104000000f0400c0c2c40030307101d07800e2015100c0d42d244140c81010303180602c0798070714013035007000040c41d220014000b1901821068841c038040d41418507001e0302540c80d1008561b0b240d0000d0051103030030041c40d841200c0c03003a01103401503100c1c1c5039800000d0500c4490404034000b00c901e460300008028517500e400200300707901c4064511503030b40e611094030a4440c0751500c100080a080e5601581d60042e006150444122103070000740d041e41030b021590303101555080c0ca100740e10a0041d51032a02c0d08000e00030184c00c080d0050403d21046980d00c0340c0e01e08040c00001e0214030407141e071030310b514441c1040d005115010010307000c4220115007068000e00d0151031f03d60b50b645016900511442d40007407001c410030142e82c01007400d007401c811405031505524040361112030f101e601c0010300c00303d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 301871061 1250 301869811 301869857
    0x3060b030f04120e0f01030e030c030c1c030b01050415050d0e010204090605040204030f060506060d0507090509010b090d030e061303050708070e04080702010e010e060a081006020307051c 82
    0x2021401c4101281018100100c0b00c55003640780c20300b00301400201e60026140c0742c0344034060541c20300300440e0710311000240b0b03820750040700a6903641e4440441e250302e01f902c1c00200c1203280001e045c02d2012000300d401d001c505403007402d5503290208400304403c010800d6040c0d144410002149801ca0410074001005020ba0b0101e090040c45a17402250a2000d03140b01d100f414001d000448085241030300d10354031143c0707401750704001400c003940d01c0000407a541c554504451050030030907020032103407070704140c046e041304071031301a050003003400c140045640d03401e1800711840c7d400300528610344180e0580d01125443c0d1121485504143e0521003159202085107481001d90310841c081e040303807801c0810407440c000c00c035070000300c220131080c0510000c102e50790112003984c1d1702072812074a03554415005275003520700040201d41110340001c1001c1d4803a8801d01503030143c06d050006d0704201e035883c05c04030394a001d094405006a0803111280c81c8001d4400e89508a0b070501c0d08040d2003c003498125484502 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 301872311 1250 301871061 301871071
    0x415050904060b04060f12032f0c0915011e0203040f09020c01050a02030906040210180b120c19050c0a0c090b0f01031112040c0306051611030f040902030a0908032806080a0b0703060b03 81
    0x1601502c0417010ae40380140c2c0c040d6011641303940c0310840703001020008041703084e20100a280f1f001042e09844003075100740304403006001c1103100c40b0456030390350f001c5070004d501041c0d03040c095510301808651254480d000b1603004900e10b10060a2948884d000c00c580200004460020301034100083c4070304080c0c0081910040007218003050f210424600c070386100c050b004000c074200160400904880100031281250200b0380b41c588070340c94940180e0142d241c0f04107140007404a0501403000a841d60040e088020010015030300c0030b1a4680c641c00550580b411044106010013003448800c80e10b950382514190b00a02601140034800d5507615401c0031075a050700c0e07001c1044000c0042d070031820b030445081120081801c0003946002d054406012080c0582d000302c0c036505130000003042c00164203030845a00300d500120b40070b540f8109440c5004e0304003405d4107148003a880e903030061003004059100c1d09040b00e60440242005104030307030310360960302002410744060556521000c40c0500094002e5072240c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 301873561 1250 301872311 301872313
    0xc0c07090f0b0f030c1f030e0709020c010b0307050a0b0a05070b070216120209241906020d080f010905060d052a031b0415050904060b04060f12032f 65
    0x3100a1105001c0c0c8603900501050017584042541480380e00c0c1c00d101c82e200301d0856160500e0300709200100701d014104040c0054103d110f07021000c50202d0090b40100100b4100c48003c00c042c0c40e401c8181510340d40791388070700b580c030111801e41000092444e0000381030240e0245052840c0c0910f41c0c0e1030f84101c0c030060b04c110300140d1042c03440c03108404030000e030840988202d0300340c3d901b10b0031194006031a07100010003142c0340300180841c0031034101040341d0020140a0003810741010b02d40d01e00c8613603410780c100e22034840148034401c03240064078050a900d40c0204044000c400440c0e0038101f40c000900b0000d812940c200e4562040d01c00850401c4c41184544680005481c0031002e41d8100030541d850300080c158800c2d0400745044182020a2403a01082c260590380030078821410002c144c2481c20300c0d40000e0b08034201c001040100302c0303558000c440006080f60104099601d801030240a8802401910601d94880c0c491001007400b0f1403104a284080301c100712920754651849901a041c14201d524807 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 301874811 1250 301873561 301873571
    0xf141810180b0108060919020109080a1b150e0d020102070f0e071205160806031e0102030f0108070b0a030b040b060c0307061a15070c080304080a14010903080c0c07090f 74
    0x10080028249401812004001d003240d05004070801d0707c4103104045070505000c0e118840046900074044d6034010302101007650036150403400c04405801c01d44100c1d403446081d4440c045100d07004100c1d0348440c01100c0d0360b883d03000c62085081c0151215840707400e90640c400c40c2d80c005500c0401c2d9007868040d043c0005070517058100502c015181012100902682c0c0d03052100300500340c00401c0382030030000c0c01c41c40d000300c1c10344980c000310781426941d0207281008501c400c46044418015002107001d60076081c0c481070140c0e80e4503d01502e4915038050700202482c00c015070540e203440f80d0000c007910a070040c000900000342100164260b40700c01040c8083da000820710030207201c2a44640b81048113000d8004c440c030390742000080c5410440003051000c0c00c00100d03414091000000d01c020203032100c007044039038494440820541e1f880480300116620f01038010040500c20701802401301c0340d81c0c1500e84490503147d4480182c3c06410059101d802882050310009090415001c2e40780103100500000807 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 301876061 1250 301874811 301874813
    0x9020c030d0f14040b06040608010507090e06100f11120a0c0b2401050f070501020307030608070f06020d080a0902032a04021201030f020a0305011a040f14181018 71
    0x4240c850030011002d48501d0324a1106001804543d051352017a0b005003085082c0d50f9220004009040d150022105503107000300b0801c180e038001c100da1056981010740012a55501000c00c0342c00c0300ca92201030001955541e032000c1c02e0740140c002d00030758132102c0c050303400c80e100d502a000c0307107908840001c9000440a0215806010f9180030042e0040c010800e10407240d0190701e10002c00001d81600300c1d040050000d480c18100d64140c0c10340b60f00310380c00b000039596424502c10080c040d00c0300e4021407185002d2807400240700c00801149004035845034029081100c955030307069a00c010300404405400f601e421509006039400e215000300e48410303800c140000580140c451550294548102e80a64410003000048002610b102e5044030342c44a0710024240d01c41c0301150451109500c010171940c209030b0102c042045525400b038a1002c00d980810075125035650040035120f8007440281802c0505001c588032501c108550b09952404c0320807107903010100e0b50140e0031610b2064130340d005c104205e44954 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 301877311 1250 301876061 301876087
    0x14030325020a21060612111002030906161e031718030712020708030a020a020906060c16031106180d0602040f0b0304140f061503150f0a05060909030a12020409020c03 73
    0x18001d4a5569898400034030306c3d548486910b09520b003c02c1c800c103025902030910a01c00c00c1128550783c400b03840c8503114003800a11135000c0000c1501100d00400d03544682e011000100e103031202c1d05070141e94a03a00c86c0710b032a402a0300c855001d060041e05284100c4404a80c0c50108001d01c451442000c1d008d1410318455030080c01c010068015030b9664100304600450170f9400907030070070f8080c1c046074140c0c0d242c0c48000c00a070f603622800c45108424016039161013101ca260341048805c69000303034003c0002021100c01c001b410711a0b0022420f40320780030318281407141800d080d150211407049200500c0d1a0300d8502100740b841d115031001d81070150000402c03040014903101640000c3d20b8030020078100307003049051030310303500700424550855920203207546241d0b5041090f155444da100545481a0526207848007a070101100c1c000c40340750400f0041021820308481c0c8620a01040c00034504144000f4011200c10b40040c1c1402c0141c3c0e020b00001c03440c12858030042580c400420004c60b6200340841001c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 301878561 1250 301877311 301877321
    0x506070b07020c01050405130509190b0108070f030807060222090605011202071e08040e0c070b060f0102030405010c02060409110705120301080d031e05040c14030325020a2106 77
    0x11604101c0301b4041008552a01150f4501e81c0807005d00100c3c20359262021300e450314162554002c2c0d000e105090b01c1d001d100711014018140c82d0758a09554285403118100c0c11013100d10703c030007080d0540420110000c110701c2e41c003030004c442c02101c5c1e2030501d0801c240f20340b400c14451f0300540e14881d03807200708000c1503801201c0703000004403d140039800d1440315220101d40b01410703c01689202c0e4005940020080c03d1b80c2100e001e0040302035032503007901b0126003c2c811500070080841d950f003030920115902d03191003c0c104440c00c2c0140e0007545003508000c01118101841c0f041246c2240c802e01012445521501800084070300c404500c588401c11420302602d40351002070403003060b00301000184410300021810205e020110309010446041030458510007456000e14151070f0b03440d110900040110364100d8074100c0da134004040c40f110881c2001c15840e885145207100c00860072010a4103855108500601807a00007010010801c0c0d0311410003001140b40d84420760070410402d100c0080088a1041c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 301879811 1250 301878561 301878583
    0x7140105160804200a030b040501060905090c150a090b03160e01090f1a041d1914040605091c1e0906020a2301020c0f0f0307020105030a0b01090506070b0702 69
    0x4203401c1414903440760f81405040013424110000700c2000503480b5142d030308061004662205815802d8074180c01c08034001e0001d80a0580801d080c080440c02c0342d40c001540410340c240051080c580c0750740c05219a5200d0f4403003034400c024040e03c00070000e80c403051a03004d14840c00c821000704040045514005003403005000c401814401166018040b5950200e8030708107070b4100718072040503810000b41880c00c500450748031600c011000885403001a075505c0045008510f04900e00d1003282c40202000b0541d100700a4a484000c10480081e02052094110700c3d0045415001d8421152a603600580d04c084480c8803880401c414440000000c4c2c1c071482c02403803040803850321481c62810030030029116000e0304400340c440c00b000c0764031020300801d4208400352000c481d00219660a4200049a11038003180700103070305030181e034900b11180e0720080115000c41d9030594605146640c0d0b541d01400621007800390740d04020151002180c6030f144d0100804100380503902031041c5241285c0000c4c076105010b10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 301881061 1250 301879811 301879817
    0x705040219080606090d03030902010e0306090c040908070605161103090a090e0705030706020c0414011a070302030f03010e0402040e1513020d0210090e1008030403030e060714010516 80
    0x10480e00c401d80025400611401d191602080d1078403410006442c07030164440c096804450240c141d400c054243c0d02207281c2034800e0302d0741601210108205600c50004a40400b680c1d00700c451011604c0ca07040d8002c8891074403901070241071604a40341c080c1100c00403240d9422441307885012650058000005030000d40c3c40078029894000601c0104001c12103510075800516103405504a5403401031100c0005031102400301e4103c140d5982c8000c0d592100040070900403850002030389421031901c0c190314165101a020705c20051440c040c0c0c0542584484800d80450009102c0911424030100040d40241120790b840304580c2400d0041004454040d010b5250580c040c0c0d0b070102c010308410300c0655205594510114500b1814008542e8401000700000c0d40103d00c052405c200c29045540102560030191003040590b4924100e840c40c0c030305900403008181c2c0240000c10000788981c1c16107801d6580540902d043c00c010b551a06c0c08145c10b0903030317801c260751140c04101a1030b00d15652201101e0700c82ca = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 301882311 1250 301881061 301881067
    0x20d2607180b043203011103192f0f030f0106030e0616080a200a08010e041106180402030a09060e03090f10020a1401051005270714040f0807050402 65
    0xc02010320a4408044c58450602c084076100000d0414003030292040b0010b002032000503400301d414041d541c4216801070201810303a0900003d003003130303201e203180184891803058400215540d01c101c080702400b400388103092040102202070440100030b10b021740340d42c00e00031105505184019081d9104400340b00507030742c020410002041840a1315180c0141c60781000ba40580320b060b24030b809400984c94603100c2d01c81086142c080410031100410343c1c0f403515500e4400350f0344c0300c0e01900745100342030394060311107041658060098a010030042200181c0c500b500651205a900030030280e80003119480f1440b0768a2b07100c07500f40951800b41c03c0d2098083c0c4060340c40c1010041c002540c1d20ba59101d000c0c042c0c4108400c0400c030b24020070001c0b02c000c0c3c2002c03544460b070b0084844107001c3c241c22a0bd0009080c0780100000716820900c5140154942421601102c60440c3c103401c2d01641d402000441040500c00781651800802e10080010700500c0b0704e11629030303050040c21458089540d21441c0514410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 301883561 1250 301882311 301882319
    0x3050604050c0607050c0d020307120c0314060714030907090e0307153e1b0d0804020d020108090a1205040819020321040513050117060403020d2607180b04 68
    0x205164540346c0c021220780075040614004245046055084103480415480c000800c0c00000560360b401c03248600105144144503d500f281c0303070b00c0b041d0b0f45c001c081481010b016682c1419000510f0744694410115032245076a501840155a50209188040d80000501da01880b580f03c000714108035084500b80500301542000740c1d0785124940c110702205042403002d04400c5000d031403c8580040307007100136442e841481288030440c0c2c003540c940d00ca43c0c0f00b2030300201e0303880d8083c103182c1c0d10030383c0c00814945104959400540710264001c083c0403031030250f1540000020403100c0380c8414080b00341c0e50ba03a11641080700d001c1c54103070b00c50562240d80c182065250016600084c0d40c544816601190780441d80720140c43d81d0b03041c0200d4109951012007080341c0441010340d50300241c100d596a003d0762190540360341c0e00503114070f01a1400303001070b08804032005c0310034014a41c0d20702c904d54403100008c3c036014030103001580b080d09840040000b001041c3c602942d5424103d41005004004545441c1c40d00d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 301884811 1250 301883561 301883563
    0x30209030f06090c13090b090309120105010b03070c0614070e0319020a091e05150109060c0213052a0d23010303140702220f110405090a0e0703050604050c060705 71
    0xc0700943e80c0300d0317400340022280c1440c40341c0003140d000794841c40c034046a0502000c0280c8a030000d2101030b020760340514198941000500400d812542d140441c0381c50364894040458469541c280262005610741c180241030020304d10203540b2500c40e503601c0c1c428440a0004150902d090701400e04035012403020401c02503950980e56004941c0b0f03200c0005070340100351109442c2c000040756030703007074035480c0c03104000c1008060240c4415aa03000d9940c4540ca5880b0102661921741011010b03411011a08000b11010020762059400c600f500503003c1114100401580400f030b11400c16200203c0c0115028102050500801d441c00c0102e0b211880204008000010845c6051101604100800054025040b100e41c01c44014980140540ca174400c54500b20108418a07041030500c0b040ca0214600104101e07440703580050704d40d426900785072528110400a0030100503040c407038543e5580030b1710711030f403201040600e006521607005800c0320700d044e062003402c0030764109801380110401c1144c0300000d50 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 301886061 1250 301884811 301884823
    0x1f08010b061c15031203050703020a05031b0903071e06110619110c06090d020c010e060c070e0906040c090203040804150903020301020301061715090126010c030209030f0609 76
    0x1405010102c07400c1003030342c075102504044604207072442c034060020040c0040114032003001c0186403018010b40e00c400c2c0d422412032184030301700d5002074024400315461240c1400740980704204a0021070804030b20500103401c000c0340364083c801d96090589030a10501411b030003003006040b5800c24071035400e0465025501c0303c500074202c419000e51007061844015250b40401e40c14580900c44a440701d28802d00305035544010342d14040140b2540c0080c4040c01e20000d50b60385c3c1c001042e50385018100c0110180031701d41d00000c43d006258068114086249035403807095a2080e101400208138508080c01d102e06607070010b4008001507801041080085100241110120760031034101d009012240b41040f06c0300316007600000d5155000000000d5015403103c401d0f000e0001c54000800c1580b604460800310001180296070010a008010054031070720305541100320032088201ea00c1ca2001b14003041c2112000c10402d00403076808200004c0c1410100454086401395100800203414250000c0381d69035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 301887311 1250 301886061 301886077
    0x1103070515030a02070c09022d04260105040804150e010905090a020d05090c0126040605130f0303060e13051c0509040609060311011e030c050c03031f08010b06 70
    0x5100040441e0b140581135044440b000d800c6529070440b00e0b00d503810007029512145501402c42e400c48180880030505e4481070802c2d100800e11a40340616042d010b1a085e5080240c14035800c501301e0000008510070700580740700b0b034800c1350300545d244c0c140650560000f007014400340400102c0090141c299821071072030f8040c1e40085032040340e50740e98190854040c0c465482003020082c180014020011000607620b00f5602e4262551103050410890f454455100268018103104054000c10041603032684069013240b841c2443c40ea0300151038032092000382d400b60048002036520001004082d11208044c1e801064a080e5a21404801e0b00c80d6951010701c40d5040014007424440312107071a0003001103401c0010041d00078008a55101d9418000300206d12082d201c01841503262081076204181030305240c000e0f412450340b16190250100c0003458181c0c90341c01480810031150300d034540104050340c0304e94000e881c21040d02c40d064007500750301d8a2907400340c420340e030402e00d0008240d40c030300e02a6202c0e9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 301888561 1250 301887311 301887349
    0xc0b030702030a14041e0509060402070515060406150f120e0318040209270105100228060614030705030304050609060d02040e0403361202010c050708030711030705 72
    0x60701c03000d59410301c144a0f55101d01b40815403120240d102d41c1ca103854200071a80d04855600c019650082840705a125503e4014481d4100d481c074016031040a44841d500700902500000302c01740c480c0c04e8003211000c3c4a926401052aa020980d21641e101c3c1c1483d4050f0a048400d02100b058118010360f02c1c010080c8000d41a44141c09040c0c01d0384440d419151304100040c0079001145100e58010a00c240c41380c4080c1005c0c2101001107024200f11000b4088441150b000301890000c08100c0030b00c00102d80c2082d45c0301c140b0140c4060200c1c5090048101030700064162400c1c184007201090718141d0150b00c918042d4105000410940e50380f0f5040d54003205082d00c0481c0d440075090703034510081c415a00003030030f144c06150510041c5a80103800b0004d900c0020808400303110781850003c801c210310f603c240d0100103402d5050202000320600300108501c181041c07202e0310a682d4607103007814042d4105034126407010419405101245845030483d07542500900300c07850070312011407940c52520100b0119 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 301889811 1250 301888561 301888577
    0x90207061103070504060305010b0403020d08030901060e0a0203090d020d210e0106080c01090603050402090a1107060c0f14031501030902030f06010305100608010513020f0d060501080a0c0b030702030a 88
    0x248421600141d00002031101510303030340c3c80c1058010300160058040c4100081c07400002080c0c2c100d90800715010303a600104046a850310542d1002c05075400245804100c0d521100000390a402c0300080701c0c01070307890342c03001b580340d01d0010700b4540381aa000e8109011075101c0e00319205059005007900408013051000808030301d01030200034004d08100c01003114190b103004000102244007013001c02c50b9040982e00e60910307a9807013804a060310019540a5449901039001c02c410004036445182c0403c0307802c10321414841d03941c640368126049488000045003c9080740601c3e15448801400c01081e20380c000c5040d41482d006480c1048a0300c2d502e64141995402000c0542d5020000150350303451440403a105980c40f882c003282c0703603a020b4004003815818524046104001030061920a00140c02c1086940c1090380030041120707103003a81540c001b0088801c80d0049003060007003030701030210007000700340c03c001034940300b00c00202d907505ca12841401030082c400400c0d408000c03529041c4403803409442c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 301891061 1250 301889811 301889813
    0x1e030b010e0303120907050d121211160b06010c0c030f26041401050a170c0f0d0b030d03090b04080f040902041401020c030d0c0f110406030302030c0607030c050301090207 75
    0x180c40640704485039040c800031403500d141d140c4072200f6034030640750001903a541c0381c0c3d5407080c03064014940a00401d00e0550018143d40240f044008500b080c0759083c01003040c210a050010703081d03228001100403680c2141a100a0101c1c400307c0c180c1114080c82d00044d0182d00fa103c500d52400c1d9400001d144900380d00c000018030050703800350703150081e034481601c403600c00748001c1f0740c2030380e0041c80345100002c0f44c01c140380301943c020300640b0ba00c07400d0b035110740e040d10491950070461414000c12004a0035824454142184130100c0586003c01e40b0403070020320003840c001054034141030a50600201410800c0350b1000450400509400c2a80036020039252018801c000c0c903180a6500710f10041d900c0481d000403005859003401140403801c0e02a00c0081c0c5c2d040301030646401c3c0d002c2c08940842d8032481c50000183d000c5990242650245070340b10b03014140400090140c40d101d0b4001c0e001a0f0022640705c40c0140c042c03001c69042041400c04201000c607040004e40103000501c92242c00c2d6501080b220 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 301892311 1250 301891061 301891067
    0xc030302040f531c090e01050a05090411150c0709060b07080a050a0e030d09030209060405070212090607050a03020d12020702090703091b0b0406020d08010803090d080c06070309121e030b01 83
    0x40844241124000d04c40346102004014040c1c03440342001180300040005103034142600d007901625000341c42d803069943c4075110401700910402c04aa04480504070f00c080c2000b100014103403181481024240d140e2500035041c1c02d89039503800442016904026600015100c20b003241c1411025081081d1980303038554040c0c40400e64092015058015224592440d0382c0c007a007554182c80c0300b210006256214402440100c980031102c1e4000740e80700c0d10602042a103003801602c00c0c5140142020310f4104d841da90b150501c0918407045015030700541c0c41800c0560040004d0080110803103045003414500e8000030b14928010f4046004d0550f41e1081009100f098010b0384003520741c40302c20100700307696840030300402d81c0144590001030040c900c48100803032055403281e0488207100d00441c2014a4402003000491781034108840866040145a09010040c00380070f129641c9510001401c100034142401021502510981045620542142000c084641c40325415005140001d01e80c011b0600603 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 301893561 1250 301892311 301892323
    0x2a06120c040f0306021201090b01020c190f0b03070906020a0b04020f0d05060708070807020a0c050906041d101b020607030e0f0703081c110a0c030302040f53 69
    0x1c2c0301c1040c00701c000441480300743d40041c207207000102d4100e00b15a80c4d0b40c10741821212200c42e418010b800140582d02141340448000c0726142444012003250755590b8124010400c0707941c061181c505020003040011500591218003c050ba4000740010012682e200c03011002c0081009118a58101050f12141c5031485400001c0d81d0110882d441e03810b0101c0040c0007440c08031424000a070320440003400c524808944241059402200c02240d6414041005000800140410b408c207542d200c03c400414000030f20300c4064401007015000404c261440c0e4000c0d00c450012003040840200070400c84558000f4031180e02c00b481d807030b00041e11810f030750105c0d00782506503409255030b11070384502105001c0804002d00c3d0703c54810b4106c00c11440d01c084600244d03000b03001001141d11081c8101480c140c010550307202254480e02e401450305441d189116000c040a8000d6011a03c0b2824580001c2a900c45841381f054003251500340b440f80c985100042103ca0400340301080da2814194103000d00e810058 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 301894811 1250 301893561 301893569
    0x40501140a200c1e0a09051b04060f111b010807030905010213090b09010602070b1b011a0414010e07110c0604120c0b0705280b092a06120c04 62
    0x42c1001c40000486040e030300d40901264610668904505410b50000b079032154030140806040214202c0c03800c181040145401801200d07807100744041d061125100f00d000f131015040302c0e19615103c03003910a00030318229441c0030513040f9a014450b0307203800303041d600c000420302c0009103060364245d940c100017100a0001c40c0001002d960020451803180c5041485081c2910000041040720321458401c001100c4002e00c10200582c00c109014440d0303e5141c0c004102200c001d400e11518240140c0340c5070300310351040501412000c40c20401581901d020f0181208a468200b07024141d0350500300d207500c01c1c034400f170510000d0001c2c0383c0c10391284080611103901c45000041615440b2a91707004045840404036904503007100a041c808074500c038820742030741d034040d0b0040010300b1940b0101d110820428034640300503030303400403400040c1c0004c2c1d40c0e03802c160320401700da0020b080d09a42c0364021050152078550100305650700005c0b4007500c3c1c0c60f9a42543c04200c0d03c0058481c441d10b5803e6200018030032500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 301896061 1250 301894811 301894847
    0x903080402040e100608010b010e04090803010303201023160e04090506130203010b010206101a0408030a120506030f100515060412020a090b060304020d0201110d030902030c06040501140a 82
    0x4030000f08a01b0640c000843c241003030322a4100481d03640b0822040354140c0b0b07401040c1200030b10060002c2840784a5031010560241c640c600404110101d892400000751594442e00c2e4442d20320f10703003800c000d48002c0311100100c1440041070400391203903040e45000703141400800c190040176014079680c9801420308190080156a000e040000c04511464500242640203600f004801850b5520001d01c071032140500c403100b100d07182d04100b244441d80640c0004c0c44049502488003180044050000b01113800203a00c40c2e81900b01c040740c5800517184002e117414071030f400a0808461400b00400ca801d0175460662001466585600d50408004a10540c403500481d0200300401c15081002c100b00d403160080b2040701e415a61082030b1400d54000041440c3c101c0002d1000ca001810b280200520b001d2050403c0342c1c45203088401d1a14001d03005130042c0000340c0380c0d80e01c0000e60400b40070700c94100c84241c540324030b41030800f00045e0060042500c0880720b9030001694084a6109101e007078600501c6071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 301897311 1250 301896061 301896071
    0x6180803191b0201051015051b0717010203040c09050c0a0c05071a0c100b0a0320060f13090507051903060b0d02043303090507090e0609060a0903080402040e10 70
    0x10b807000b4000c040465481101c14490b001c04a201e41403510f00b401c0542003030382c2d068900381c013142204003d8000902c010a0034813610300b01080d0050400341c108410300580c000107841e45050b0900e82e500409552109075000d1400080c00501c03085001212104d1040c0c1c01e020355001841c2c80d02918001065114090004112034149800341050008001e03004560044034240c44100710008100d038000c0c40816800311040b0420000108040140306410094501562080ca580404a0043d5229511051500900040f02c40e45141480210707009081401d1003006107142c2907801421070701c00d1840d100c0c0841c04c83d208810f00240310342c0240c0e0242882200d041e450310110390f00d900c00794006005584c1c4402c010003502903051001445d54281c010601404c03441d880c0e4048081d001031009103010b4415001e2100b0105407600107004210880c280d900080c000c600e49009100c1c105000501600c040500346102880400d41c41b102850b0003940403500060741144103806140f92492084034142075071300740 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 301898561 1250 301897311 301897361
    0xc0d0c151707031815150e06011b15110c070303170109050f06011101110403080a0906080f0c13150903030809030405031209030a02060f070618080319 66
    0x12a0121003480740c044901c119100c1c00400d81c00d0300d881c03900d020308a0301c81c0400203011802c80500501482010311000071075900401040e02e11503680d4001020142d41c2009005507035a1000c00f9a402c032203820b0120f454444290f69901e00101040049041591644881ca145a03030486c01c40f81100028401c0740c10300d590b2454043e100250780300198609445582c0001480c0100740190751040f035400c0c0c0040d81c0795a0f144c0c015200395003c1c0e42c07065071700d41d6200c941c00c4155101c0001000554000c030300c890b4880051700d40c0181140c5080d0094802c0040e00700604c440c01c0c0307803854540d4100708494109601c84004841840042c0110351291140c0600c2c4e211064906410072010010b40340240d8401d040f6503a01146203903a407103180b260030f8046d480f4090080c84500d00401034201c103040241076410404090300003590a4001e081604400100054000c041043c60311035846046014003030401403d1140c0c440f01042c3c040104450555030585051144144956000382d00e09942001c0060001d414 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 301899811 1250 301898561 301898567
    0x1203020a0606170d0f0e0d0b040611090a0312030902210607090510081003020d14010b090c040e09011119030f151203020f0706080601080a0b030c0d0c15 67
    0x510800341c0d103082c81e0400100d9200c2c0008125841043c44000030030f402051060304481408000d00c41000304002041d90012641d50441e5407800240034072243c11079030401d4100300c0304448036654140204002040303043c0302c544520221748100d82c1c03c644184210b603501306043e000b9010030200258004c03a602d910424000880c50030008a04640c1c00300c510f0f0b0f90f1070000070741f8402491f0240c254040141c50050354900d00c2400b070264055011f010000c401039490740070071062841c0420071501403c1c0c0f001112340364138003441082601c1c50125902e100c50300700a2580035a900c518050400c0000c0140700017098602e09412405c014000b8031501c5a44042c6100d58030300f1200d01f0001400040e003480d03d5034080d80305034040d070070020f9950b40d41800c20a00d02900242006021102203080d4020034110a040ca9000d00c0240014111501c910190f441d00800040040c08000c000303161103440d008010429840009500c60320b48426181503d500d8000e041c9680404da40380c4c0180003140c0329641d0702c154598 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 301901061 1250 301899811 301899823
    0x40516060f12090b1b1308030705060a0605060409051e04260f0412030c05030309031e19050306030f01331a0d0209040c08040c09060f12050304120302 66
    0x105a9495009110082d0b00c04410703520b6891000d0b00742c00d00040814030f000c84250944850120300f860f0649006110b40d12503010010550284455070400f1512005005080c03000c030364020740806c001c00005d410701000070028000d0f409036000346982c50000a02d0038990410040701c8210380c0c0584985480c0c580740610300314103540c64818640c10081c1041c103044120300c0c00c3c1c6070044008102581094140000741c1480310908405900300070411800002003501030000394001d42112001e540c1c1ea1400b51001c108050b920302c0443c615040400c6a09442e40b0041c0e2030354440c040526280f640c9803070380c00020f883d100d0640c0060140e035280203400c0c01040c0c0c20070b000701820521002c00c10034810000c50720b14005d0f0001c4c4580200c10764400918100006504000c0c039841216200060411300c100e40424101c4090204160100700e041c0244010701034900075020080c0003080c0240201c5040c140d00203006c0b403851103240441c1e000345422600300f19003803082c0c4015141c042d001d803e5a1040341002550343c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 301902311 1250 301901061 301901087
    0x2c040b040507090b03030d020c0a02060a03090b010f0308090f210604050d0804120507060f09050102030604062102010e2814180f04020f090a090b0a0c0e0904051606 72
    0xb116a920024190700140a01801200700801842c01d0130303a003111000282d070000c0004d5500c3d004d805484401a903816025206c00d40784c079540041d0082d054901000c0c9904185c024401d0701940190420000e00004115031a1140a0b10441c0002c00000041381001d116010400c04046035038020341030507500041c0a5210741e02410850391800c0185100340c8001c10709440107402c4403052030701c12000c1070040004118007481030100250881d0590b0754502140d100b040c080700d031a50008207101080c40c2c00d01440e0081e1001072280034100b1004100c0107006401d4600090602c0086051840c40c0e0740c50341050b1141c404941d03022142c039101c1d0700d003040c80c041c80c50081c8a60380d082c2400d940030301e00300f04c1030300c0521005440540c1e54070f46824021206440c0010000c1307900c0b43c4040c010740d94a48a880c8054000c0084400119110a80345021200080c0c000c1c80740070302a2401d001000c0180c1c0c040c1031159606025614048507440b00d0400600700490508000710640b40e0100000711150302c251115034003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 301903561 1250 301902311 301902313
    0x4090618060b0d08030105190f17010b011d040c050f0705011d060108030304060f1b030606090501140d0506060d05090a020a0509100e060105071506240206012c040b0405 74
    0x1100c2d29000c101e0360042d2200b001e0401501800180030078180304410510604400700031b050040d90300c014030841c00c81c1c00d80003509086040410401800024045c00251400900700030070ba00040e14000c4a040854072000e91281d9161410071000601800c100e415015000000c9c9960b2500780c00c00c10b002e003600d131800e1042e0545020300140304160220380c0c1d0341a502c031040034603e0b586464481402400e81009400c0750281d5a5881114503408064a04500d42c03103503e0118800740b034030304041c1544446034445418415030b10103248141c0c0c20030044a0036269070500025a039101e100115555014800c4602d41a80c0b0305820721098070300001c0c0b50546184201c0700141345076155000e106a40b0400c3d03c42641040300213009014124030001030b40e80c02181813502c0c506000c02c82e201c484850072a44c5403603280d1580c54405002c0002c0c4010f81680708201610340080c4040c096000954890051040c0081c003941c806081d100c145c42440e10340c0784180c0c42710005486081c1401c118104100c10b440031282 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 301904811 1250 301903561 301903571
    0x606090e0d0801080c2b03030c030606091202040c02150f010e01050d05030901030b12010c030501051e0105030f04030c061407030c031802061c11030a150f0308090409061806 76
    0x100381c46070400506841c10307200684801140001488000618610503100c4a49888002c6e60540c0e5a03103810400f850003503502107082015144044d0841e11103402c12820446200000d0040c80c0f24206200c5200d07505940001304100c1c83c1c4c10484c10802411400020103841500340320040402d00e42050607547d2a401c49041a661441004454800d440005143c0d0700188130212566001e588047d4052802601d80101001050b125a0071149000c1c100c0d40808d640d1001800203042203101d010540408c03600c1640054007040000c1e21031b000081c112081101e5000001e81098420680030040c298445818800d02141c00c98400085e02e00300c80c0040028603003c4072200c42c503c60f02640d5104124551080e030040351603000d000c0254001a01c480825280d40c41c4140801882c0c402c118a074040d00000c2501e90600062040a440c07215407150303480c0700b141c002400700c0100d0084841c02c070395002c00540e542d101810041809004180c02c06400580b50610354681400c02c4000205500c0c403c40c01000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 301906061 1250 301904811 301904833
    0x409020c1006140d08130b0c070806060d0803010b0a050c0106060f1206210812090a021c03080105060306030c031b04060503010501030c090902011b03020309150a0e040b0604030606090e 81
    0x26041c0d40f0070181c1d0059404048401082e0184020500c03000b6001d034102001d07889070b4028101364400e01c00180761b40c0c805901000040d405020b0f1541114085404400703070841038441000da404113004d61111b5400004030703103400d540510304951110381030b08020b0001c1696400c018040d8402c07101e480000c1920b08060f40041c0d0340070300c00c41c0c05540030348402c2030600c031420080744004e0312549000c55001008100d0291514501c12880c1c0c032814840005203100c0101c0e105200200845000c540f076081c0005604c07000003504014102e05491b000e07210307203440750399000000c0d00d0084242a842d8150182000518203440c1b10001325214820a440c203010455840c0245801c84000340b0020b042e5801585041c0300c081000c1d0041d60b106801454a5090399205005400000c16540c00c04c90141e840054035042604003003144001d210a61840107040426800e0054200b00c0c1104d19603100340e9a65102442075620081910301842d0008800c00c070a603101e50501008140543c1007810034441c0102c000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 301907311 1250 301906061 301906079
    0x305070c0501020c130507120504080c070503120d2c0f010b150d020306010c0b010b1e09010206060f060f0f040f0f05030703140c04020304030f030515060a050f0409020c1006 76
    0xc500c1c13003000f40100c402203901d6020200100400380c80c0748108080c032a200851b10001c2e0091900a90141814581e103031000c0f1070031864040c0a5001e42e00a4001400ca006000d0001c029210764869000c8042030f409081500d01928550482d00750200859030010580181000141c021025021500801c80c0601d0b420400035001c4010300b003084d049604000e060050719168000d140c00036010b0400a034610f486075580c51440703030241c105000c0c290010a032803226550b02480c0030750030481003c84503d0300e824500000e4507841d0007048140141e42e24441d0780542c0e25258210b03108523103014200d5496a8503882405040e500c1807142810910b01e001e808580807811409400440da070040c02030041e24910303038402030141c0000442e10b65a00900b8981021030b11140010351145101c0c0e80d500380c285540910103421140d010702600c1048030b6600481101d0380302c02d803c80740c00c1051030400c5611000c40c801d4882e204d1085403c500007503030020855024117900013a8108001031840341c10b01940740c5418800c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 301908561 1250 301907311 301907323
    0x4f021203031902130503070b0309100501030f030c1b0603060519060e010f020a0c0b03010611120301140d17040f0905070207031104020c01060e180601050f06090d0b01030305070c050102 81
    0x507001030361140884440c011550051210400c1a08084c2c041a5103100080c107001e03107540007204240c000000c1060034070050090b00100198000d04210550450b02c40c2c030b07544203240d40003c0600000070760304410302c0044041e040000c604100055000c7d0745075140200903150910401d40078014030300d6030300780224034041080140d03407042e52681d1303ca2800400441d0140b5290841006501400220401082c5000d013400c0291140e41c034482d549502d0801c00401a01d1410141041900320b81c004210000d0440100d0341101c00c0101004001041c02c0d0000e055032818520080201940a035040b03000719180000d0011200c070581c59a0700c00d65117100d40d40c00d580b012200140140c00000342840021840500001201300c0a4401410110415a03180c2180c41c00d4002600a00f81f5100b0801240c42d0200740700c44106481015217a40e5240c000894180359070604002e1042501082014090702c600e081d100c2203a0700301800e01e0030381d6900d0802600c994452081510001003080000c6800c0d4000144 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 301909811 1250 301908561 301908571
    0x91103070603180f0206070501050403180603200a270303020d02030a0906080c210a0e0d05070f020312040303030905150103021c050c03010606030204080c094f02120303 74
    0x80d110015805603982000c2044d000402ca0b8070203c244003510200310240f00e2203110f80d1007074550841d4585800e0200003070714070591018003050704021034829181051900c2218054403104061f454003044da030159510a68030311070b10112044000c00611410080b0804001c5078000d40a4070f905404241d0202d0f00d034441c04641d00003040782003d04000442c40350240aa224079403420302800c0142d584401c040111b17940102106030300d021028041064550721035810721205840003441c2d4034280803070142941c040e40383d024000003e10705205041d0345040c080040240201070790039903103680300e190103401440e492900b5904d0f0302c20341200b001c00d0502400e409041e00d030020998800c04051100580d2171840c8008100e529000d480300b4514561424068000a800030780ca02503181c50030100c04c1454113010100d07070b5226591070810320148840c400ea000e901541d0320700d4540d148000403107183c03051812840c0c8000d05e0129003244c8280d00e0f49003a0000500324030840d80300e01d65190801245940b8041036072 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 301911061 1250 301909811 301909841
    0x5030606070305030603010f090b040210080702190206210a0e060c090d030c0210050a120606200120040518010e15010e0a15091505070321091103070603 67
    0x200000102c1e0003038014580c4820010b00108a8202c2c284c01c440942e078101c44200c81c02d0310404140421498985a08100c1645900c0c09601034503001038004c0d6200340c04262150410340c016500c0c0c0640d110003080301e40c1d06007201104040740d002c0c20241550407000300c4e82d03d00e6952821980404ad03510105085010350581d0281e141860b8041c02040715400c0305242c110244203401d00f2507401a1a110320036040c140650322180d071603444886003e4010300d0480b04940d0003c2c80c00c502880040d801510854504c16241c02d4066840c442c80c220900500b000c090402074400381108802c41d120a00f00104180e400135191847c480c030300c0940000f9202070038019070502c526510001000540d082c0f40390603100b0f030140b5040e04030491700004101c501c074503500a41e03d00d416010384000d0a5400c90b660100034401013060810130070400c20000d103035000c1c100c801810030000c3c1200e0305000319260450040d11701103510401c010403007860540c440448403401c89020f8054a80b000a446001e4070854009d10450b42d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 301912311 1250 301911061 301911067
    0xc031b09070e010e0a08010204050117042a0f090605100203070507061107050d150e07030507030308100801020c070e060f010c0f0c080610090612031e0909022805030606 74
    0x7100039100380c1d203011902070410010003220b0007555940781d15030004000450006981d10300b000001094007801030f00d000d02161100050200140304110001040010380d044821104200818034400c0841648220300100006002050300b1459500007000c0340c108550b0104446554041a1b0700d0b402441350207045904104d100b04101400b5001034841d20040d5020b603145140c0b00c0c0e0006007110391800d42036454407190840a031b00b840c024070076070341d80754043c00c01071025510315602c05951f1442800010108504140460301a450801d0b5410291103008001d40d1900060302c04c8594030007042c030034130740280d0350b09011400504042441242c881d0040e91822030f86115a01d0301d920071101102c044590707044181000908030410310040780149124011480007626003c480d8040c0c030b841d500841c100104816144e400203402c84000140300038141c0b140121041d2150080d251412a603010301005400040c20000d6540c003410043c030200040c480815a500514408454500080346c0b640c1d000a010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 301913561 1250 301912311 301912321
    0x9160f0303050909060102010216080403110402040f06030207020415120606090c09030615030503030711060c16060e010908030c040603050f01081e2404110d0506011203050910020c031b09 82
    0xa4184d42d40090180005890650341c150710a203810201c12042d80c04500218080c010002000e4102000c03640c02c039415814682420f0991100602c184903201c01d0550001d0703d40b08545494000e4140107244105c0009541c1c0e50316100d03543c080b22900c04843e400c4c608480072890102a101b80c104103074483d42d07591842411951a4030090088049000c00c08100550000001d00d040000b07503c90407441d0386000f034180801444a00d40000a0b1100e61003c0c0d091011201d03c04011180c4c8260641040b00400c0700408128064010402d600b4080c107074171000800c1088108601c8014003c0341d20329a0200680d6403800c50703c4440c1035003801040f0254000300070f4442550f03507400d025260001080261140e01d4030590541c01d881550020007a10701001004010030710140b402c071030038000c406503000b0690031000d590740d54071051f05004900d28800c8205c05841450300c2501518a2800042c01080300e0016164002c2e584d41d00380800c003403281c860303015152401c00030b01212a0b940756000d491490ba0b5215 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 301914811 1250 301913561 301913569
    0x414010501051b0105010f060215070e09060415080c030c09040c0b0a05040b0d0605040c0f090b160609080702030601050a240323060a091e0207061409160f03030509 72
    0x701611615039003810140c0b029580d102817003401d00030a8480d00c02e441640c505003003c1d040141c0403002c40100c044440030404a0364020000411001041f00c400e20f003950798100207130040c504200d51400350703492142c001c9960240011016604101242107600c4508803104105404008650003080c0550802c3c01300500c19058000d441d454480c1d003061414191201c00c0110704c0c0d0810a034a01b0f00c01c1d03d074841000a818580b0548100a202d071809450900c3c1910026102491910034580c0f0885c00007030358002480d00c00144000f85d40e000500f4001c2803d94100070304550003500050b40b0a024404c000a010b14208041d541194a50b07980018980d40c00601d101a40403440001c006054035520340f420b2032007007039204281500240b0140c0169051032018007107102115000184482e1600009000c2002000d680c42c6285803444009039035150320386001d0024040904c0c055400d9a05481400069000400d0315402d10011035000c0104c10768a8001200c50071580c40041c0100b8400c104c03004040c10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 301916061 1250 301914811 301914817
    0xa121e020303121009060f14010e0a0803040b0d05060619080718030506190608031b0a060227030309010e040b0d080307090501120e030412060f0504080c0606041401050105 75
    0x10004050b41c0c2005651005540d0b5003030101c84c48540540c403903106101804103841103101800800d00b060134038900b800c41211003030541c44480c0e0b043c09030016031444640e413200c9c814000340450310281d940395941da040c0c4001641002041c0841c00f4100000901b003420000144c83c1100d250403400c14403c160038006940c00c5601400c003000708080c540300c400342500051a20070003180311740001c0003280b03005900400450385025210288070f0903c03808001d9101c00000340c0b110800d0140c1c0800e021b006407e4040d107050001300d401030005001081045200844610000c0201038a506146000502c0010152a44101074071640440c0c218141d0301e4543c00c1c2a8059400744d0301c05052949000303580c1d12441c186030411282d0b40300044114005110707550380028021891800c0c0d80060241186003c0055200d000328019a0100c001445445043c40b480e9004604147e8030000308002c0303418103082060541d400040c400050b8461b02010500e03d040601c0303114441c028540354000356034207040045510358 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 301917311 1250 301916061 301916063
    0x32e06050d021c1406071205090105070f03150503330103020a030b0901020c06100f06170a05060121091a1314030f03101d010b090d1502030708060a121e 67
    0xb44d82925841c08400400c5224018039941c2c44440e21000c3c00b40f100d0068803070080ca4542e90341d043c8000e00c120301d90006a1140480240c2c280418a41441c4001000c1c070141940300c568103220703840c407441102e416000c64000c4101d5500410130030340903003880907104007000c1c40700035081401034000b00086034070101c0e1560040074810002d483c2103001200709180c094140d40c0d2803000408100c040103031070080120b6030001c2c152810811201c070303546100072641c140000c15010f1104c0e01c030800103100fa8490805444003080c040a403d040c1759040e42c1040003026102c800b00c66003100e01154000c5003080300000c41c0700d105001c286c601c00c801c8a83d2500094500c2020022a03031000740600c410300881607028603c1060003100f070344081850003585100340250803051a041000e12401840403113404011502450300c1a155081d86822500d03041c150f0165411152107800c0c0b002c0107000402d90b000d9259401803100325140d951850f202c500c8440d40c1c110108004281d04031000e03104c400f8050009010070300c5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 301918561 1250 301917311 301917323
    0x120203160c0618081c050d0f050109051006140307180312020d1b140c040212040213021c090c05040204030303021804110423030d05030403140301050907050306032e06050d021c 77
    0x8000d0107c0301106503644520565242030710f42005022408c0d05118155001c1510150a040d10340f03003000151032542c0c0c940b40c20603410b8000000076099402001c0001e06807507000804d050490f41d0303040a20316441c07464040001401018010003195200d012500a0403d0b0544003240810305ca07074500300c41040e201c082ca0241e001d1100d046035280d4aa10162a00358042e42e001c01c000d19041c8104040122480c1c045c8451038414440080c07030326a0100445542c0c0700d460790019090760b45003040740580c942035120a07030081c00000c0100425a054007d4840c50f08003d01610300480c00300c0812040e80c1002d000ea451a01080c0010007040e8990f200c0c000031000c803802c2c401a4007820f500401c0c149101c4001c828003180c0000103104c10150b1020078501401c4058520385c0c190b5061800007003006a001d0040c10400c4030101c04212031355001c2c00010880300005812020b10303011914140c1c0c01c20140b8034201204ca10f80400007031903003408140314a5017627000b0103522140e090691231245042203c4019240 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 301919811 1250 301918561 301918567
    0x8100e10121106040f031406040c0308311d041709040207170a090b0301080604081b06010305010501140a0b0a1b14060114100804120203160c0618081c05 67
    0x4162240c100604c058601c060803a0802c904504000c0204001e2021580141c1d00c440c0070000891806100141660351101e08035a440940c03d0010608206030141c00960710064500340120b442c4511501049034469402c1d1490280705030420342d0014412030340500712030712505951041c0002c0344000c0c101500028801400d013071050b10f40306440039592103008460680011a1503109802000c9400100741c0785034500d24542c1400d01190310343d0380c0604001c1071200003040c0c074801e02c086001e4950481c50300c170003121555a505d0901c81e019103401e224800d400d441c2c0001d2a0a54108a030002d0b054494200360580380c0241c45004031824500010401c110b825400304210000da034000c003048000c1480e600400c06541400c1c841c10504140000c01485480700c40705200096403c000c980c0d40c840c0d0001c00d840441c41c82520b06034258480d80c01441150700c29035800c3e80800040c040500241d441c41c0c1c0d200e22407400d5201012826240e03d00544103154420007404000c501d003241e642c0c14100040c0b40441c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 301921061 1250 301919811 301919843
    0x70b030f1005030316030c020a0314160b070803040b04031b0804050a060921031b060204080c0103050f1906150f23073008100e1012 58
    0x650000c0d126880c000c55030100740800002040c034208054003003140a10310f0400c0740301c003080000342410030003030038401024a11819980d5900c1c01a00564105a203c01360740d08001001d0f460300c0110101050552a501c00454080025002d0700ca20030761084c0600e28603110394850350b80080000344114100403000c0c010003880100000c1007001103120300c20241c4c413141400c040014024550700000100110804100400001c41d402201d075100b000fa10302d0410003140c01c045503c1c205540c1d64401c41c00c03c0044803000c0154941c0100f044540240c16100c02140b04001181650404d4810803c180303000d5011a541d2000356104980141c401d80001030920341c0e0b6440c80d000c40803008022404600c510a88000f09500080913000784044a6046400c0c8004c00b8002003803405040c6014050320310013a4580f154050a12041c24907103079918110600700300c07002d00205100800c492140324071089540020740340c4000c404c528003481100c0c52402049007400c10401c81c0c41e103001011f407442d90440c0d0f0400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 301922311 1250 301921061 301921079
    0x50f0307030501110304031d01050301270e07030b06040204050307052b0b25140a03060801050a02030415060b0f0f0d0e07060f05040e06120304090606180b090f1207 72
    0x50b8800c2404d2409603180d01e0700d070801030700e0450845083c000007045c19042809a0303038040c08070b9040d500d5401907810002d01c078211540074205914070040800e40b8094907686544000211542100e1281c0784800b12942c0c1d00b8103010680c0100d2150340d03055804560284243d1078103000d070200105240880c5440007220712114400302c107041c102660618081003c1c410010300132080100c0c6240700200c00321040d42640c000a141c112060080180000c000c11740c0241c0c54469000b620041001100901c000d04110715104025407007501d044550761942440c0340e00381c0d00c0500410046915900c8824203243c0b03036a80300010b82d481203c1e8030307481400420a080c080030780d500c15044007205800040207002d080080140031000e0510444003480014001040380c291001170b8a80d010a05903100c006580c03491807100c0c654003070f94002088050603c032010803081c0d80040f0650300c001118400c2445a5554101115030b4420100881e800407541403252a0720b007401305030301808500040454140b42d03900d008036 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 301923561 1250 301922311 301922321
    0x110607060f091406060307090b190902030106020c10081b0d020703080a0b0f0a0512070b0f0a030f180219211101020f0a0b090705150a030c03060f050f0307030501 71
    0x249030042d5620a501c090010305034568140c011940010815030401d000080e540f0160391103803080c0300e9201d090b030051030b0300d1b10102002d01e00c01030803800c12426100d05403040030350030034007900005103d03070a601502464445800f0b00e085000740c899000b103032990b1004049442490700080f52680080000320001469403005140180c000d41c4e404441d42003411090054a030b0f4102180e11074031003100104d6143c4e0710010444202d44003103902c100d5000503900458100710055211805a81001c2400700240c0f50007001004113421346c3c0d504000c8992519a104103c482d010b40030643c40e0100b8040400500701110114010340648044100c020381e20442844100340c0c804510483c0844001c445041000c1011b41c510f6114007400036103c0741882d041e05903501c401d903481c06003900c1c102101084e07038800144003000203050050107030840c10740001104100d42c1d05c1600710000182c41d0001d0b414003284a031080c4400c0d42e00d0b40448802540c03502080005100d52980e019625005401000001138024865 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 301924811 1250 301923561 301923581
    0x2030a1107030f171909020d0507030f12140417070f060201140c031509041505101503051501030221070e09220b0406090209040507082811060706 64
    0x540e8044a041c403401072043c2450340758042d44003d12003d10174040100d40740d07481c1040f07402900003001c012500001d80c50b2100c1c400042e00c0b034040d16001206100c008050042080e0040c46000c01890200d1811120003444010440b803e0380c041c0414018407804031900c00f406000a030883300030780c0c0c03284000002040190f1080c000341c1c1d9103265501e001c1014035025940507848000041c03c52600340415021110300a10031817007400d4200014042041c070800d900410500c010301000146495214000a14114010307060f8456907411381400303992180c0607051182130301461000c12030710385038011340c065046130039030356505404018006045100d10010070b110b03042ca075851411004800b020321a124402401c034079004042d840d007615100007c04003010f642c55102d1407888242c1d0f0b690829800a00c4000380080d03001204906010500ca0f00003050403d0b181103205a5003140c916038040b541000d068074240101100380084d03507020810800c41c055032001d02405251802100307545d004c0450340c2542c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 301926061 1250 301924811 301924817
    0x15010f0e012a0606060801180204030f020613090204120311010b0307030b1b03150414010312140739050906090411090915060603010e13140f01050105100801060504060302030a110703 80
    0x401082140e60014041150741c0000c4004c4ac035181c11511498a00c0c1d00404020b406458001001290000c2503480c0c04010510040c04545aa031512250b1030f08184001041e0001103002d45d4840c00707440b040c0b04440840000600500085245a8a203600e06030010031980c52501001c004035002c81031900214803d00ca1245190a5141607004220403101c00c085100203909142e401840000c460381840803680c1c400b0700700605207101c11407041c0700328440c40d40300810020082d800d9021582e411603050b440045201ca0078100040025201d00030051288a09980203020710701044182c10000b0313290340c1040c060b8509481810300038010030078154065401400c00e07400542203094007807041d06000c0e000740040340ca0b285194500b20b544030111101030700030101106101003800c02c1044400341e0484108110068030800754404512600926091103218000e00d0303d94202c0794010f201b0300c8014107a9180e038071030134203060a0810440c000d400042c076001d50b007591a640c4001424144d005042a14440c0e9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 301927311 1250 301926061 301926077
    0x6030412031b11120f0a030b040b04060b07141c030906060e041406010e070801030201050901030e0610030b0a05061f02010e0a0c092406110a0b15010f0e012a060606 72
    0x861409420314684c9028000c1807080080c0c41c040203003101c400300040d16000c40c003600c4020009000308405688603500c90f1038400005000029080600b0349203002e1441c0342544000414560303112402680780030709000d084880021094001e50104034158090200010003d40380c40c00c002e6200c030280c4040e00ca04d4841507010040e9580bc01165000d400312229848035400c11a0014024050601000781404008220040140d1003036116003800300d00c8008951a900f44000502d81e900001d00050f14074584010001e005210785016240c080c55003d4200c503080070790441100392401100b14910115520b030b102c01c00d1401d50030401900745a003c0c002074241a4540150b6404460303034503c1220a44000801035420302308035801d124201c503200e003080050383c100740381a0b900b0104080c02c000d10039401c410a108000518818400c10b198003a2210804007c0e01101900d00d102e40b010300900041041c81c2a40c60f10105004540c1002d4221008082601e45550351030240d0300b0581207600010000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 301928561 1250 301927311 301927337
    0x304051002010207050c1002240109180807020105070510140f060d051e03041e030b07083903070221040302060f1602030f01060608070503010506030412031b 69
    0x15030400086144a800210f242c1201662419129604681c400d4494410b070803003004082d00900c9445454903400b41700c42c0901382c4604032008540420b000d2088642d10342070150700700001080f6218030071500038490f581000c0305c65004581d154080182210a4015026100948841401601980d5821104400a6160040711024038990040446114000380d54011001c181c01085203403681050a220140382c2c00c459034103a2841c130032544900804000310600546225281304c1d1001924400d02d108001d6848041003210603450503101029082c0c041a07060b002403c070300020540e4200e001310f40d445c0f0944141d06140c51741d0401c82d24030340560041f280941501d0501314030a01c01d400050584c0d800e160031500031400768010034064203426100000d000c1c10282c000310040700302e41d130f00038202c4410035443d000751400381c0040c1c45000042061140030811550066080d0b81c1039450280c00c1d14150b5440e92541c2c580320404002c003e00b45541d504000320000c54940c4054101180d41d12414468403c1e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 301929811 1250 301928561 301928569
    0x13050901090b01080a1107030806061608030105031c12020c070e0c12070f050f07110307030807060c082415030907080616020a021e060a0e040b0f010e150f040602030405 74
    0x1415140e031345140060b2080340c6d4607440c1c01c1d04e01151701072030b03c000340b41c0d2242c000c6503591007540142881c0c0205d0800280030040c014000f18107a900503011f4442c111030400307480f40f50741d441d03540c50004070390000309981e0320108070750280441c0e54a0004688002d07540d122074500191064032010703a4004001000c40c00d1100341c01c0b41c10781010440c0341c10461400410002082400307400c10007004410002841028400601c03421020680b0050603201d283c0d03520f01d40b00e45150b100034021a030740c5081071070007509580514211442090302e4a040f075000b2007014403a83d244001208804d900401d008018a4421108800780d40305220310b2000705122400c211501d880c0c0340008104100551500d9204c0c8509035010410000480e8183e81c00001101400c0c100302c010840303d8035460304850041000705c1595400172855103c60302c00d403020440030002c0400c1c46120005c035418180864001c00720030600c1e040c20786103800080420305d4110300303080d440b4980301d180d039220f40e1154006a001050230305c03203460 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 301931061 1250 301929811 301929827
    0x90b10060e0109080d030905070b030a151401020d0f110106060f11061014010203040b070606060f110d08091006090606081f0905130210020f070801090c090213050901090b01 76
    0x7400c00480b00c601d000c4e41c00c0c0e541c0200b00f01c0d0004150f140c0c4122000c104040040e2805454003c03086500c074138103000600d0050940c00b09646200d01010000900e000c4100700c40c0032070f204183c0c05400722004c65042510408009000403041040260345414500700c03c0c1700d00c5d00548125a5104a8100d101c407004001c0082140c0c05100c0750016400d2046031808110914116452205100d444803c2880183d04500580d88211110100082d220b03040019a60091044d541c0c180c54154501c441500c0888001c03200c00302e666199809180840080d43c00741d00180d50141d050303030031609250503c900304030a60f5056401840015160482403040c0c80d0480702c03140c0d0020545040300900140c00d10034880b510b60600c601c5420707913501d1010030207c2c00e2442c007a224880d000b9004070040c50210b03800a6440c41e201710551854024940b02107000c6206010300b44581c1d80214928aa81c1d0400613020300962100f1b2080b000c61142c11800621900c83c407000e40c0c0200200f038800243e1182002c00508000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 301932311 1250 301931061 301931087
    0xd02100c02072711041215050c090909070b0a0c1202010207120e0402070204091110050307020a021507020a180c020307021309030903150207111f0c030201090b1006 72
    0x14000c00c000f40802d80d281450005821036010840d01004803d90011004112082e0551001a00083e02290b032641d09940b050302d59204810208036902644212012600300380e071240c01a140420400c11580341c00d42c1c2042c3c00c5400902030302c0407aa0750b00b503a960303180d02502e03180c008241040c01810610035210005492005503000a5117440141c0d80d071402c85a000d54445010b01100b440303101d48035111035055484265010784208481030300c50030b0021440800401080c8a070344410030559503d44128140e0380550f6058000788201b20702d50342041101e904484091000407400c1c000c0d100942e503071a15040050840d16128401d0044e072a40391801d80703200c0c1610f00250341c03040000c000180c07110700c007651840101020018401c00549070440e4001890751014000345c500c5118202a8800c0c0d600418600d440b8075203e403070b02d1040d04240000d80d00c04101c0340c040c03011210720041003240140d0b40326443c0381c4640b0000601e1942130f500e600703903640d0503643c4030764003a10148107224040d00035104480030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 301933561 1250 301932311 301932313
    0x150924090608060601050304142a01020a08030613181b0b0702100e030a0c0f06020d0305040804030206032211090604020c100b0102031606052e0b07030c050d02100c02 73
    0x11900300b1580c1c035610700d405032445040010010001e41403043c5040b9241007440c104055900344400c0701900200560b40741d066180c0d041e00b058410015600000c1e04a96555220300d5041c15036981e6001c001801242c031103080740464480301220084441d40c00012006d034400d20611980880b640c595040d50351503074024108120080110b4405640d403e030498604075102c0c40c0c140e42c02d040c0c10f130100b4140b40140358010408517440368003080d0401300d450a2000e41c0c006608413170440758064011410344906a07800381c42144108810720140c00d00400455004042480858002c1c2c1d130074003040b0043c42d200e0820365006517055989012403030140c0b242d5400c14001c0751f0650501040b90306041c0c44040304248515442c0d03413182d8055407a4000e0003504d40f04002c44070344008540490900c000a481d0071151406000140c14001407040c0b080f0340d8101401d10354001d1040094102200c070307e29940014815000d01003588012400218104404206001940d02400360840d8860075441540d030890381003429 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 301934811 1250 301933561 301933571
    0x60e0108060c0d091b0303020f010b1302073207060503090c01180f030c050301051003030207120213020c0c01030b0616080d0e010204081b090708060415092409 70
    0x581100251081d04100800c2d60b00e540d801000c004a00105070440c401485240130200c0710300e41d094400f98070000c81e0b000341c0a5400403031008070442d00300d691007031059900c1200c0c00c44241c3c0000082c0d010b0411581b066003810b01d000a8030b8603135045000e00f091041100e003001c0116407d07101c420700061004100740c0c10004c0c11401c0065480c0d0700c640c6042102810050809e10b84d01c141001440607400038600c51150303d00c26500c0381003042c071a52460099034060b600b4000410300740c0d0400d0340b04804494041c0d01410783c1e1802c01c0034500d1801c0e07864109980c0504245010701104e40c103480105552030706000180b0819480c10b0002d001c0c0c1c0da0301000b10b48100c1061044190b001c014100713010140781d20140d150307650040c0036101001040c80a442500c2c1e98070100300840d84c5040007400c00c6000d60703441c1c1c5a5038508440e20800040002c211a07620014060b50041041400c0c1034000f0152a82c1c03003807d00c00d07029292480c00044951003550340c0c2c4074000c45070807160f041007105d2500c00a4010044140f213 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 301936061 1250 301934811 301934819
    0x605041505190e12030408160b1e100825030c0e010312090305120a1e0f0210110901120216060507170c090d030903060606020601031202010b01020601060e04110d020d060e01 76
    0x4c4a0200920181214a0020300c84030303e01d00c490300c2c0b8102181d114260100034202415901113800000d440481c0680070b03500821b90144144d801e6004540c0007000074800001c810060703920294415150710b481e682d1320f9002100080c00f11414002400000103c80b19641c5942815500340600d55862024400c0b00b14040c40458000704240303003600b00080200c0e82c0d0b5605448111205518400110360201c5581c013010002035200210741c1d400d01a0b542155401e81c1682c1c0e4445c00c50709985441861307102d0801c08451194025520242801030a01005090112004d61709146c3c900d1503c0860303071569901c0400140a400491504626841e12511a030500e0000030400403841290501482110303010020000c252150801c0c5000e19800038041c0042951075502955800f0280000c440441c06580b1030302059205102d580b1049a0580c010000741c1d280140607102050303039211030b60b0000d0711001c104207003c0c4410000c05c017224513980d00603528200120550200c81c0b02c0c1d00480300c0540d030000100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 301937311 1250 301936061 301936093
    0x1523160812150607150b060405040905061602030f0304030c141c020d0215060f0a150201060501080a090b1602011104062001090b0403030216230d0306120605041505190e 74
    0xc1017a00f800d40c000950112890001082d5008507445264058280040710082020124040d4012003107035060900200700018243d03180e0050040d640d408070f10600016011034481c0405041f5070340030b4004c400c04850b000503007a00740003903503070b8031038031904100c00b00400b0b5641080114014101840a0b000350004040411400e91000c0c100b244502000ca0602d4410f642c1c01111f18020103049000004d2804000806800f9150b0342c0308440c04035034540000707503100700f04c1c1c003a110815600c00d114a81ca6540c026a014007100306040c3c0c0011591303100c440d00c004003100001403000d8140c0e82c079080980d000c052040d0300700000007624080030ba4106094240052420440c0b2a0403d0703050038056110b000300c01141140e1450340d50007400717101c030807054071804095406080809010b034005072090f14000c104150305a5001e446041401d2103d20803090204105500c00e80e00035200304113002490000512002c15900292100c1c40944a06504243d030046144100142e0b178010030094000144064251 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 301938561 1250 301937311 301937333
    0x212150909300a080a050717070503040611130e100f0614070503030a06061b0803070c0302031e09090f07020c01051c060e011523160812150607 63
    0x45200b041c00310401200606042048141d0030500621807529024108001880004155040034000b85841d0200320340602c150340740c1240c0390f0046011a1a03490f40d400803691603000a0003503520b1079850050000f1040440300a11000c9204200c040015040c040e00031508840940020040000d00404011203148402000111035640c2090400b20540c2e0030581d43c280300b92440144140800070802c45050050360241c01035a40b03d9a49a5040100070482600d19100c884060310b454001c0c0009580396110f4180303001c10903c0b0740b06503420440a003c041c0480d10100301c0500c00702d8804915a0850b081030400544d204841c1140d0760240e041c01d000103900c13004030340030301d604114001840100d50420700c583e10346045403840302004010364030034005480c5803080c06031403621454405a06000c81c0b04010b58900f40599654190003543c0b00800281c00b40e001010a9049a040d00ba070700000c0350542c00600120703c44a0b0f944420340c64400032896210f02c05410403441010306020302d0001c1540b001788 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 301939811 1250 301938561 301938583
    0x10309050a0b06060708030c1b032107030b030304090903030b09040317040311060702010e0f0304060e040e0f06011403011b020a020904051f1410061209020607060212150909 76
    0x100b403a00d850300400c5491181140103800d445000007880482c80f0707032000400001141140303610010017a0300701a51684202941c2030807085642100c1644403024801580e041182410001215951140400d0a42e001684400d01c040d030ba034030f00700c0c05158040c050000260021a8414001d28090780c014001e080d00b410101c40000c980c900140c209401b862050001d614004e0441d00c403490003100003030180030883c011011900841100741030b210000030a0342e054a0241e00c131100c05070700541c00d000081604498801080c880c13407411a003480c1c0c09000a50281240298108400140209250944114810319013503210103814400d002d56000c140352601c2941111400107a4880b400d1481c9001c8094ac5d96012030b03c08030141100e0350080b030348940448400c14944001e10755400c52160303018030341c51007820003044038082086d4600c0900d501034405030b0700c01041c00341003a0315908c40b881280c2010856050400c1c0d030100340302603503501d0503100440c4038080301c0d5042103180054116440b2206010307 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 301941061 1250 301939811 301939823
    0x203060306060f0a090b010311030a0507090b0f1b03160503040609050d08041502100501080d030f020901050a050c1614030c030c10050c07030b0709061b080a080c1c02030a0b010309050a 81
    0xb100c001b40d43c1c4039410410f0003c1a00461984038282666098018101541d90358007103412908002002e0000000b541c41e001b42902c00c1c1400d003000780c01c00d00d1008039240308100c0c841c00200301000030910a0b01c090388142e4010002035480d5418010040c20386a07031608100d11403240352400500190505044806a820ba1580c0c4069120000c0099241c000d40303003509101242400008101202c0010300b00595240546c1d041c494004200c00c80c1c012403040b440b00a0000c0c001308070343c0046500035001855001038901c100c4d118203000d403c2c80030143c3d0361904a02480b0340210117500c0c00d86010480c440c0302c03071011805440c3d803821140000792983c0c0150b5100d0b0a01101103188660404140084c800039a003000268407240380032400207009448500410001c40c0b644c805c9128040e800ea03209800171680800881d142c4540080180c540100042c06910078070310800628080d0b0300c050080c0c00800004020258980c10f000700444207031480500c650341050328105a490108070300180703810907130303801c40c2c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 301942311 1250 301941061 301941071
    0x60e1e13030309051c02120c0d08100306050705073e030c0a0b12010e0910090c0b070516090b060d180b100501020d05091e010201020c0d030203060306060f0a09 70
    0x850182c01401c03c108001c1d000d13002e10f90340020020b001107000389045800e5800e484004026801d005940d002d02810031105500050f000030f281c034081e4141356040024808140c14250792a41c4130020760b1801c40d888000150041020020002c1d5151046940c80d0b040b200c0c444081e04400202c820035038800145040442d46038104891520140846098020007804844112361628000c4a05a000181c0c0c0d11240d0100e000000b1850300320301c4106d0054100d20041c0c041d15100c1c140302800780002c0c600948a41050307003000640400c1e000c5c02840301520400141c00922003145030b220600140381e0044401d0760400c000d1700019500c0c0c00845240120355400000c4a080c5611101d03010800b00b00f00800680c0401e09010b812170400443c0c000f210702c04d81c22600321540c1401c00301c03618000c840f141e070740101500303000c0e44002d04403c049000304e204c18030006080400b1000310520340001da165800c0032a40c008207102c40790400744881c0d0703030084046d90030201c03807030b9008082020314a95220310300701d482e991 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 301943561 1250 301942311 301942313
    0x6060d1505150604030609110a050109060c02030c1807020105090304050303160c030525060504060c08090f090709030510020703050a110a0804140306130206031b04031401060e1e13 79
    0x2240302040d45003006091a6141c5031170345080c100415294006071a0041c0180058405181c9081024240d400c1a0350700704045151500a42c0d9407500344034103c0e410301030301c502d49645880b29091140c0000e51102400c6050418620290071120094a00d0300f0a420401041c0b0550301c00000321501d18650b01c00f2255103100310b0800251900240d04010180d0096040341080d0982c140c003a803400c4e0510600002100d030b600c507070a40d041d100f035100d981e021a203601c40b03481c04141d1a01c05446501d40150840c40d0b0301c41100001003c000e0704480d446d0225540c09414400e009040050509040d80c0c2c034421854008507480241c01405545c5084c0200030b12060894078400c018802c030010180d202e62079949460b160708424000d20070034030400e80244156800a002c1601440d0070203100c40d006040c50b0b10f10340b5401a483c031501265945044490720400001000030f546012400c21030002a0000520354200b03440c0d4071603100c1c0501b81c900b6402d41d815548030858142100903811401201d100c4001d4a6a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 301944811 1250 301943561 301943581
    0x30e060d0f0c030605010f09030506071d0a03051e0615240d0f2f03090309031605040b0102070b180d02040e010605040f0212012c0a06030506060d1505 66
    0x40506024a141400c5180c00b200780c042d005002914001d8030380c00020071480b4400c4911469034030015015911160205107018000e00c001060a2074030790004240c0c0c6240e90100720ad008266004840503440303c0ea03083c0406200141c00c1c6c100c4140d9002400c3d01c5d080451450036000d484c10019072052240762980105024940340e00c40012824004042c0c0346d03150a030f0443c0c01050310909540180341054165984052410302c200a42c4564582944141c104040030000940000307103403120318407081100c26550340d000c1000c130071101c40c201d1001c0625400d0100384410388004220050556101d000b0600002c101e200076a102068905141c03800c0482c0e540004031030a0000101035080361400300c0c03c0c003640d41d06411038000c1c0c2d4402d65040c010551104145812441201150340402e4004c1d00103001202c840400703100000d00284200c0d00c0007596540484546000741c4410003041e07075031442041005401d010481d48844200d0b0710000502007502ca0f00114001c4d0008440d505589400180c3c0d10b500d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 301946061 1250 301944811 301944821
    0xe0a1211070f031a09100e120d06090c020a0f060c090b120901062705150a080318040b0105040e0405151f0b070c0b03040804080a03091809030e060d 65
    0x103205011205119a540121200381c2101d0105691413840c00c90380300958400c4001003405184030900908125550b424072200a1044540480650165030f40b10242c140004010340100050000c3c00140c091801c2204011510030280031000c0d0f410000c112000305040e4090141000e4000c803001c144180d228400712042c04498009805206004c2044401c0745143e48041e441010710708002c001140d2030741403685100c85000b84442480410b00b040f10131030711040d0003e030307000780d0f00c20483d104810a2200050440745141c1010302e01c6c1d40003203180e80c43c0484000341a01c038084d00b03503020020035070501c0008055100d03501a001c5a21140f0001c2001c002040003540c04118091442c1141790512450003040c4050080c040c1609100303005000c182d170034007003088600c800ea100700960300e00342c6041403003442600000d00035610300c001800001071071441480942d8503203103e48d483c04449410304a1280b039040d0000c100001003498501c0c0e64000941101d40c628030340d4003c40b100781d180d00158071640050f00c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 301947311 1250 301946061 301946087
    0x2010b40061502060f010e010b071106040605090a061404050609130c02342112020a02010906050304020d0204020f0f0c07080705030a030807050a0c020402070b15040e0a12 75
    0x241ca418030004500e0490101062225543d909603220368988802e2009130003400c1c058601128003c1004000b402041001032400302e102d01700c4032580d440070310000742c403641150307110f0804101300047c0e0410928100c80c41501522890800e4600700c4509003178240140524010680500b20000e060180c960380da1404110004d0490824444c456030414004d44070110862655034200d00242c03198003805030b09044800403800c01a03414a0a480d01d5140c0c40b2012080c0d0030940d842d419490418042824980031240302c18a0380c0041c59004054030006080c000b041c2e0001040110078024400140c0d40ca80c02856078a40403100540c90300302c18001c6058a20400400100890303001525620f14140440c1d44811603e61505403450640d0700d009142d1104a50316006000514650000320307001e001d84007612044100746000c080c00d4002d540854100e0b4000d11080d9081c081020030414142c00e80e45800000580990b402d1180759079071241650349211001c07008100d62801c020801d941d03842841040050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 301948561 1250 301947311 301947439
    0x915020304030e04060801110f07210201050f010b04050d11010e12010921170403020703080a03021e0408030735030405010b0102060106140d06090501060e0102010b 72
    0x10341082d02e00a481030040343c40c3c50b8002c07420040002001c08061258600d0700581180083c40e126002c90511015031200c4070480c0c021000404145401c888840c100305812240d8000003075909214200150101050f400444192003c200c148160b49a5040c0c2050304e9070300c1620101e200c44040016210702e1400b1340f1068014030141021808020150003222000d402a00501c4007040503413010242c04003a805d0380d0010824005000041000c400c8a09a201780a131042da2070284e01da0740c0c0c0f00d6055102c0074690002a402081d18005d005406015243c0e84404401d05880c0602e4207180980728092140007400901c007140100c1c2654a062420980c19000030211074442d0705100351004d0f8540056a09440c990310b0404c40c1004d65000048050603154103403500c02980044405049031a80483e40013081d4a44034013000801c40030b01c0c0100f0b4068003141d02e5100c81022094002070840d003101034400e101d0760400c0309090100e605902c80310718000c003542e40c2401d05c3c1d599240c0c0611150b240c8081ea010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 301949811 1250 301948561 301948567
    0x20114071e200a03090806060f0919112106090a020c07030203011103090706050403020604090b010507120201050610051905070302030c03040f031406090d110c0d0507090c1110091502 80
    0x81c0c10100c0d0f10221103110b910f841e001c0640300c410b80c40e0307108000c07250a42c00c00424140003807203181040101c2c0d40006905161510000b00944a2080c0c40408410310038400001c41c080310001c402034040382c0074131000444100c0030b1414200048100d14082e0074440321660014000643c608240f0441c005187c021300284004540d418640d51180e00484402c8900e0003490b40105a42e84a00c0c01c442c2282c5d0000c20441c2080e00304224000208807a42145051102c100724070741c00210400f400071422452a0000540751511a060241d032148002030b40003044410400e080406071002c805030b500280c40d251081d100c4415150503403840c820225408454403003c10005120300c403071000101079a100794408507a001108003440c1d500c0034103546400e17280c2c20007006034000510507078040364131008810803503199040d072074041a00411100d00a45640d000a4406d001e040118001c88009425601c0c21070b2500142850b000c0d21449034400150f80c668692403814207001480307040611030300301d03190f00719a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 301951061 1250 301949811 301949867
    0x3050d18080415021603030e0d1a06030606100804121404030b01050f0a0806040b072c04180b070806032b030c02060c071728020114071e 60
    0x50b508180b0501c401800400c0203040030070f10104d05045a4420104000040c90a698080d1042d651100b5501d4110070514218000b040a1440b50b41c06040250200b00881c280002810b00303120004210602070220b580d114a07110b42d003d154558400e4119501c03004120900004650071006264100796500000c140403007440b4803090720a040f503508803000c20607041c8810500695a500e031140d409190040300015010800080200c0d910611070707d405d490010440301c40d511075142d0700001800300c00908002d88691304242c802d0003002550401080c01e40c400d155644021502c004055004012800022a03030320f0300c00308141c40712415280b24a600080044800024403101040b1840020b4208070b00030003030500100e0303000e01400c155211300c0d1911515072245071000c001210007104064003006100d00c44035100c5042c101403064231481c002580840c1e4002030a494000d5080d00c05c0c17440f604240084a074200410035601090402c0111225051085c1554590f903040500381c112a500c8110f49 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 301952311 1250 301951061 301951073
    0x810090f02070f0b15010c0c090c11070b0a02011d1f0b0d030f0f170601140712080415020405060703030b190305061801020412020103021605121e09010c03050d18 71
    0x40c4590702c0b0020000007403800c3c0004403284801141d001c0c207030300e08600049c0074042407038100c1e02000a0905126180784644000c040c03400704070384d00080030907002285111401da420301411008194184c00b4610b24200d9621031038a869400c40740c0c1c0005004240d0709200030001740c1201d034681500524502040c641d50401401161707a400c0c1d01c500090710b40c00c090b40f40c9030003800412030662207006165000e0361740c04019030710041d420301c030741080c3c070341c244103c03030015003281803c0040500b2651100000c1c2403900d044c0100e010284031500c182401400180025104c1c207050756003550f0907190100348640d415021800d00c1c4400b8840c01c461543e803c81c080140140040d11a0240e50081a00039603080c900e03260f41e080303006a0251001c01d021320085030003d0343c400c0d0041c1041e40c0c9080c0d600740001d08180d84ea03510b4400705650350340c1d8204002c42c1e401d62602207003000c0001c9904550105107842e100d10002480007904000050501c030000c200031542c25400e5100041103009075000d0040f01c044e80c2440 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 301953561 1250 301952311 301952333
    0x11b1d01050c1b22020d110703020d11150c0a110a05060601080621010b1507020d170f0408010515060708030a090c05040e150603010e0703030c050309090703020702010806010810090f02070f 83
    0x883c0103041c0802e0247c2c9000c0d50048901d9a9010f5002d000f41d105007000450f118408000e180a00d441004401c0701580300503401e80740942c00c0c2c0620b155031901c8400e0040c0401d28807540410460308a4810440450400702d401ca0b4402802d1900701c074a5520200000c1208452102c140808018600c900740703c400154007141c859002100c6c0c1c024010051103461200d4031900900a40100c8409540c0000402100d0500c1c0b91420060b41c544c10840d100c07403c200745810541c020007880c0e4403031051120300d09600300d03e50884031003a42c0c45464404c00e500c0342c070020b120241c008119540e0307402c2224f090044803024030001c0c0c0300003030090002240d0700300c0c0aa5910344071302080043c1c03683c00010a0b4140740500c40c0c3c1c12913030005005444070764595141641d0b0010700320070985050004002c100c0d803e40e40e214455204401680700182c44503018000140007282c0180811305004255007070007902030785100114100c501c071241c04100098050380c800003078000d0200c002c0104145d848444c0400180b8890 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 301954811 1250 301953561 301953577
    0x40b2503030906050a02090307030f0807080c070f06030207030801181d03090a1202010e0d03090806040b01150e06030112020a080111040503120304080f0c011b1d01050c1b2202 77
    0x8188160345401c1c3c105001c0b44a10551154142d000000810005000300700c1070700745901600c126370802d2001d4a81c80c110303a01a205d07180198000320410700c28000c4999102c00039046501c0c0031403e001641e5006006000180611180040201c00304076106040d42c020182e05800d881c40c80b2242c107070200c10359940740c03c1078100030f2040380600408106548403801c0401e290750140e40d06142c14242406010f03002641202c188d00b040000d085c045560401009400c0c056841307502084120b40c5001e980030598664a261803003045400d9058002e60355508040e01d041d108241181c820f00040c0740b001071340e0400d00d944250244d508100d5a084800040d2000d04100d51065082e02d0913031219030134044403440220340c000e00d8200d003800a00d03d0b2560742006006081154000001c1d800e0f61007414506182a01e81944002080c0c102010120460f00d01d850900030001e080c000c0c03c110008107030503110580d00364405107400710715490400d160380d031120110600b01c046070007400788801d1180300c8000e5406082 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 301956061 1250 301954811 301954823
    0x6030b01020d020f030a14210105040b0909060c09060c0610050a05190911040512100e0c03070506030c0f030709080c0a030b130602091806030c1005040b25030309 71
    0x1896625180c00482c0c0c140c02e10034140041c0d854406076600c00d9a81054024144885860034000c94220800c600b451f0708e11201106000324035503141070204000c3d00c40c40c018540c0980101c9040c0103800318005803081d040410368000640300c603401000700e01d0324010707848288000d1142005100d1502000300d440025141c0a07107000d0449a141c00074810001544400006900942c0b0420080b071031032980b0103800c5d518410340a901d002e036580c0c0010b082d5a4240944074154104a02c0180401c61500c281c400c1d134002280074080d41c202c4c03100081c0d07c0e543c0070310800d0701030303200080050320629501d0211030018940420842e00da0400c5e8078014081485401000d0701845840009841441c1c4025000c0071a40e11031030903401540d4803540c4804064070100110351250b020700a00903599145060540c180c41403124142e07161902904040c80c0031824000b42e4050145001030f8141c880d03008044a080d02d000c4480c55546140860220820500103104250144c01c00403421080691503048104a41d00400e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 301957311 1250 301956061 301956073
    0xb25060e0a0f0c120312050613050c0d0b0423040f140d080702030319150302031002120f010b0a0f210204030b07020d0509042d0b100e0a06080606070c06030b0102 71
    0x130000462481d00c044018000c07540c84031072600b10a0240e0403086d4130140c040c03c0c03480c80d07180d20000c1c0c006556087d60041e44010000c680a00110001e03c1192200c0790111828819402c0302c0c4440d01c181103d8103600b001c00c43d0880c00103410f00107c10043c00c43c82e60f02100d88082c881c035005007640c0312802c0070f500c0740025001c80d001c03c50340740c070010a0705d001c2c1d42070002c000b1882c41075440071401451203100708020510b8026000000d664184050200e0100c07800000da039a5aa8030b100c115002402080c0d0b4401780c50740c0c401407003280d511605480d9401458240380c104150403003010b843d102150262201d00c0350398541440e01e503400c503801800031a4030402624495407034044099885000107800d5100140d400c0c06003035244d1801d50400554440042d00e80488503480c22203280d802411182550485919520700c00c10a0a0030b000d40c42140b501c51602003010180400090b42600e018801c03102008034a07404078081d551507200b25400c1c1c550003a41000615a242000380192803008503d6016010714 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 301958561 1250 301957311 301957319
    0x1e070f150515060c520b030405160603090606090c0c0303020a09090612031b0b1b0f0c0609060c090a0e07030b030312010f0b25060e0a0f0c 61
    0xa0007064000c589400382c11195882010601100d50825201000d951103840c0030b0b00c0e002ca0982904095081c440710741000c1c19111121450400300c03000c85031940b40b914624083d155178040c1c40404040c2c800000229035a81c8030b0342002803410a0355208a40228040c0000180351909a8881300084c2c2c8500c005129403a52501c01c0411142031954050100f02c0f100701c02c00000740b01340d0042a440900d8240140003603180d00c58801203440a81101441c402c940b000c2400345908400070071081c40301000726101e5041a17179030380d0713007900030203007d038039640c450664048402030490040e00e424105202d8425203641d4206603d0356074a40986404000c0c0c0106000700d00c80c040940c0480743c01020141c4000c0c0c01e80e2603c0f2441034803a0000340008105039a84102558559080c00100704142d0940007418141d4100110651034480a81c0200030411082000400901d0300081044054028128014403090f45040080c06056003408002c91342c01105001b2041180044c02e50005c140030702ea1841005841e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 301959811 1250 301958561 301958603
    0x2041a090108011a030402010f020708070803040503150601020d0e0607080315040e01181b0b03010f0f060206070c02130f0608010f06080606010e0904110904030809010b15090103021e070f 82
    0x544513040071070b4008000040155025040c0400682d042d841190f0500341e544d46081c0c2840103607080b0100c1d0781c2001404112616040207860720040c61a6005c0100d800e090001035982d90003007944005201c591410107050795100d0041c1da05151308800c0b0507079640351401c80c481000c91100e4129200b21301d441c0300c6e03d00e580d02c1440740554051000700c4041d2800e4154544811803a00003400c1c525400681c80f002c25108649000785000f40720348040b40b0162420180e0701c83c1004d81d143c205104541c03120701007140460384240040c440c0d82c0c040e9080d90034070000c0c9081d18090132507110b903200d4190500c4030000d207600056004512310005924200445520f40c40072039100c00051f1032050000d2129100030700c0340d2510007101c039001071142c17007100007801c86d1502040103400300f2501580807035159410419404400c0c021802c15107011520b21500d5a41c80c0da4a1485014212503941003580c04070b1121304c503484120b0403092070300d0000380c041e40f907101501d080607400c11100c4040710700078400c45200000d00f407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 301961061 1250 301959811 301959839
    0x60f0c17070e06090f0406030501020a120e070b1c0c0e0406050906180c0d0e0313080a03140c010603050f031801090803181f0c030906020714040b0402041a09010801 72
    0x4460390741d48480b18490040003910b42000410950000c805602035100d5a030b00d01c618002584240000740e218900c0322009840440480f8800355558140211103243c24004a80780c0c0a030342c0c001180f2a101c10b644400701100304803029850f038005152030440d100440d04001c4a110300041102e060141d107460b1001d012260000b034540e00c3e00020002d04a0804c040000c96040e400344c01ca1540c036040403500712203002903070300141114100e50030000f402c10758500d2409403000900400d1004000800191381c00030038940068040e41d00c0080c0c04110400980b000307400190041d50001d00b11101a104001815240d92260a4403c0c00e01490660040d240d40a04d81c0c500868400ca0050750030321400c0e1101c80f1141024940d59944040c559211089001140b20001c0c4640c00341d954141c40c104144c54007404d90401c079007240003550304c80807040003a5850f8101826855030706031030200b0060345040110b00a40130325081441c0860b400701a4204400c4910007810302010260f80b00c0405990742c00300000210 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 301962311 1250 301961061 301961071
    0x61e0e150c09040b0a060c0605011505070b0402030c031501090e0604031409060d05040f020102070803090d030e120106060f02070f0f050103180209090304031704060206130609060f0c17 81
    0x910314400040c02000c804000e0098400c01400106103035681d800018031a084540003840481d00042400c81030005501c145805070a40c0035103140c1d40000480050400e0040250040c01809800300107011502d01384504007005001070700b01c1d5a06242c4c28020010720703000340100403056140c030294a034071140029074907000b01e805840d80740d0b034035503a0160b06403523510159420307420220420000d14500218800c00c4e1240380140110000c1c2e410074400203082c11400d034040880c0b0382c8144a100125511148283c1714682d05040924542c0628400720300c44840c0d10368041001d500e8030302d000400381c2c2c1010710041200050b609840f0125150243c050140340e90f400313052401064104184655402588130b41060140070582c540c46002c1a0300103030300c00c1c40031180c8107082e802c0400d0810800041d81480c4c0504115007000c1804d0500349035009580d010700805090006448030044010711680358042008503130030940134400e044156603080c01a20b501581c070000514036a00e54031a4005111a0038015 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 301963561 1250 301962311 301962343
    0x1101050a09030f0f050d030e192a050915040e0615040e100f060f0b0f07030503060103020c25060806090703051306181703100501030b18040f17030714070f061e0e 71
    0x510f07041c600041a1020820310450140301c03840300402d0320b654071b40d80c031407003229801c05800c41d07480c80d001484150fd90140c20305040d640b1507411710450403844004441501c0055400060078102105202e20f003481d20041d03501610b01d8201c6030318403600c0390340192040d2003041800c445d03075941c1c810601559100303018080c1030408040c131040000034421001180c00050500d8003605000020320403c3c10101c8030388411209001c0305001441100e0b86640602c0184a50300340190145030441c081410004010804810035684500044041035130003014110650050020043d0301d068103400480c071010710130155540700c40401d5000e00011002c04880c8220004454650020303c0d01c0700540103410480c041c65441805c20074802280101b40c10524491801004000d000803420b041c190b50743c0041c0c00380d460074280d0801c10004880d03006000c0000220784501001d6441000b4100b004141a00c804018001030801c6d0403c15030058220b80d1748540e1801101c204030030101040855134035090300303498a02e2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 301964811 1250 301963561 301963583
    0xb010f0b1620060a090602060109060f0311040908070818040515090c04080f10060803040b0307050a090b16020301051006140708120903071101050a09030f0f050d030e19 74
    0x10481d81a041d012400e032005001602400800a1101e400083d0000c00050017003c00300212941040740d14010103070703a0810405242000c1c03194045201e40c1c0800b41400d080841100b0243e00c851380f010040303030f8200c43d016803120914500000e6560240f01400d46c072011040c040c003e149014450a8010081c0b500e0000c1013074281014051103240c01080441e1034030007400000b580341010b001c10b5100040e03100240144c0e00c48402d2600c11180c09800440741c03688280700c03c3c00100e20b5030703080b203400600c0c60502c4c0e03440341400b41088a0700e4010750404528144007080b60b401c2a4540b054641d02c640c822002400203039a5850758444d134911501c5030b00000344d188140c02040105980080c158207003e260704c1c620349104001c0d01d1b02c91101c1501c562046a1000a2280078020100d1014441038000d00e091403412100420041c0340ca2002c0c0005801001c1280c010030030000b210303000b02a1280c0c443d065031403c1906120140080410500700c51540c090101c40078541007200440b5455030ba84103607030140c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 301966061 1250 301964811 301964813
    0x20c010c0b070c080a120e1504081e070305040e0601030908091c060c08091c020c060d02122404060b03010b03060315010806040c06020105151002010f05040b010f0b16 73
    0x7042000503040c00d051112a16103140850b1049000f015011855150300103a50303420081c2c0011a04a2190662290060b04152200380184248035402c66040170b2400e494099200d01c181e6403600c40203841c04444c2001404a01309508107018001300c58441403018a01d40d145001581070350703440b04000780402020042c01c9100c0c607009648500b0208540d2240c6007008440e0390f114112000c00000c807012541c010b017041183d0004102040c000c2c040c240304007843c0347c514400a9940c02c019100c15120705008603244100d40000d506442002020a20720b42060400380f035038903000321949070b04c1840822060006400d40c00c086c02410100c44410110514503031800c110492103410103044603030306001e00c900c0100c1b11581c0300c503110b01908480000d0038260800f4030746910840d005901840669051404100b511a0060009010300c003040d1511480810f003090101d0050402a9414119524040910003400014810141607484051003d460342c0e4851486030018000e80045201c0ca90030b1580d030788 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 301967311 1250 301966061 301966073
    0xc0201030c03060302060d200703050304020f0609040f0f0605041806051003050303040309080105060906010804030c0c1d09010606031e0209030307081b07091a060f160c03050d020c010c 81
    0xc0100c10389107400510749490394001b07001031744480b4150040585642d007140c0031501c2e80030460b206060b08030b00369103046400d541c041c11a02006201a10032016510200201e031a0001240e100c404001c10030404242c3c803405100041001c00c3c080789200b0b142000208107814148070f40c404084d04603501e0004504c20781d40d20005030034002e001807a03c61940e80d0000000b030003003024601541c865190444028140104c036400c40344010400c0b4402c1da1000203001d6140d07008105a6005034241c03030b144110000a00b000088030381d49500c51904108416100411050350020840c01458840024000079030303aa6812820340781d026601c04402c142d210561810141607a005100301075014041d03a042c0352142c2c651a001d074000716100302c06d000003401541c882c21001d101400c043c2c200c3c103004100a000c086414182007800007401c50155900040034206901c80c4419140030720103032516040064042d24249007050603500c812609480b4210782003003680e0020440d040e2804043e0343d00e58100142c0e403105 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 301968561 1250 301967311 301967321
    0x50d0f05041a09030106230a05090117011d0f10021206090901060305070b0a3902131121011a0a1206030803090705010503010506090118120c06030e0d0c020103 70
    0x450350010341000040f030151003c0c003881d401803403410740391010440080541d01882d18807941940c800d40c14404103002c1a502c4000560640701469080030b40d501604030b104e801003480351004e1600c8040070381100341c5024000b42c420480c450344000d981401091810000c184e01826917002107e036003807000181a4286240c005034090710070b0b400820516a41e032184d40c21304226810060303030a0b20010310042010341040d2201003001d0990598440c50000130814020110785060320310403560410f84001c2556140e51080c40c82c2001d1400c01c200503030390041072440d15405840200f6814200e1035144040c09404882603049540e03401c0f4810b80d4409038a0294078070342c4005021000d02c0716603045140b40e00d1481c410f02c006140f05d2800f0640d00d040c5602d850740391129541c0039a04102c410070050080d034032030805413400503000382840c0200d000c2c0440c11714540e034920f4000600a00311074000001f8818011030407801c07100e407038500b086003401c0710b0000c54a9142c00945540480c100c0066480194400c0c1e02c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 301969811 1250 301968561 301968599
    0x415060b1c0b03070b03010f0608070e0d02060d09021806030f0303070c03050307121b1107030525051305040b220318050a230303092101021207020307050d0f0504 71
    0x95650403610b030105c02c09183c000f03811820103240d08140030302c1201d8100c420307950040d0305410035450403102d450014030303001c4c0f0030007000380601000302c3c100500800300d800038280725900401c4484e4105008007800058201213840c544680305151b004800600007004030f90080303140c4d0345c9490082c00983c909490755440500001c00700000920011080c581030b1050700842c00c851500070514607032600c002000840c0742c042c4508580c001000403c00900c00195140f001030b105039030381c0c0c06e04008da03004285c42ea00d01d074805030300300b550420065140e100a82c4150703c41c0d07104000d401c0454a54010b60026102e0020b002c112615505070244082401911400c140f108100d0150280b241c9900216101181fa548958110a03510700b86000700a1400c014107100c0d03005400070741c1030001c114009201d002c014042040c81403a09002101650001e404072082104043c01c024114246413a000f940c80d03202740c00c15500f900a01900380da42c2485650110307807091072940c03030034285401c01001d4401071410040d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 301971061 1250 301969811 301969813
    0xe010503031e0702041404030e041e090204090516060314070f080a09140a0c090209060304021207030c06092303060c0c1c1809020f070f11090415060b1c0b03 69
    0xc0800143e072107005011400c45991106a111f00780703483d01031724154010040304d00c40d03030400f04030307503c001180035100c5d038031070b460500220362056039001140052484000103005401200c10211011081481b8842110103a540030011030001304000100c011317050b102d0700e000a0a401e500c1903101d00c100d0b103180d0000b120340000a820711090380d07004806035480d012035009800c00b80b00c050921951002c804000c00600303005624044440c40016500d00c80240000e00c0381c02000b60150a60f8000c02154000d15840a10260601d40324003000e854490980318042d024100548613000d0b1440ca010442c00c0e0080242c0142130984500c044041c00382c010101e82c0b030b92440ba03215200c1050900945001031882e09485090b00d80002d40c08400e9058203d8100300c410f0350040106000d8201620304030f80b2010740190084d00ba009003850321101e0328210341c10a070360041c000c0043c0030501240091100d030429941c1c20800c8101e603079101e03112050140459400d0300200c0c80d200401003405a0700039001d0850010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 301972311 1250 301971061 301971067
    0x210203331006021501030c030b07050f0a02101b02120306060f0304290112020108281b0c0201051c0207051501061d061b01020409060305160e010503031e 67
    0x8240650441007100c50004210800d4010010540c041c04110840c1d01a130390342c1c003015811600d030729180000030b05c4002c0c14030f0429000510b28900c5201510480088154040e50310b0010000003551a11140f030000c070550b1900c0e0241c07640c40c501e0348550580031603503005400340c00740b03c0304103e01076000207208030f8016204110581c00c1c0101c030030055204034850349501d900c02c054010308000808500101e501a90040c0300144103091149a8551403507509180c0210142d8032806c1400c030200500084010a2401000301c500c80c0303200381c019031a150701036501310b46806810003003200c4031f80d0400030213030109800300300d548000704045d101d243c00c603088014050f240100641d503207894070349501100d0b03c070f02c1810001031010715480011a1420b504609507002c4103402840050414842c0c810300202d04540ca00d08001400030a405441c01080e65810400c4659038070f0400c140c4a16407589404d02001400401042c4101c035901117505940000d0001c60400705420504501d50b00c100750135000f03100f424 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 301973561 1250 301972311 301972393
    0xa020616050f0d05011707030c030636050d0509100507111c0507080c0f061e041203090503190803040c0f1205010c020d0e0409021507060204210203 65
    0xba00042a4590441c00c0008140d03151110080700e900800f1700d201c516400c2680104082485a0207040a41f03800c214006011951030b05841002d80c04100400200709850300d81403c0c40041c40b03000303500180118140c0d1024800060111342c14400c003900e071680b2440509810f4071a6204d0805885c00c00d204d091010010a03800300050030003030784481c1b8000c88078140c0100904015051160740001d0000343c00404902021400050709100a500441c2c004c902c0490805c89098072404a90407010700324580d640da0f00c0d164100255141001c101c180c022400c2e069000919041c00149082c01e40300b80501e100d1100c1e900ea8810519030b0000d8004d640e00c08038034102040404403c40c154005001c000050340071301a0340c1c039105094403a206011010b54116080403902240c003e84040e901d5507041300c3c001114005440001c41d80c0b0b11889200200400c0441c030401040003035402441950700c0e84010343d0400134401d0341c00080440030030000703416400644003070545c0c60a10400010604001302c01d40698010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 301974811 1250 301973561 301973587
    0x2120d020d051c05180d030203010e0f090109240606080603070b1e0c030406111603022b060203010501090b0705030403030503070905040e010605090c040b070f0501020c2a060a02061605 81
    0x1035880000e4505c421a8000c4502010403580b52160f015003015801c5601d450b48503011044000c04501f60400308000140700c824080d40501c9085a121901031500c1c2c0c1600c4612424100341e0300b030414140e1030311001140c898081d4030754034819440103000b004030b6424150510303240d80015882c40044420304d403120811003c80c40240180c003d01000464449240440040196400c02c29084c1e0507008485610240c404400c6008240c0c2c0e0140d40b070914a1040164442140ca40c1c494150400c92103600385404201c01600194105e85090340c2d070b024080e4403031520001c980300d4030400070710903482008208006030148010b590321400a0405041091340d03040811700b55503000100c040c0f01d035034a50b0309100d43d2504400451300440c210702903d041501b00b51400555110750a006001ea19464642e0400c1020940440d000010780e05d081e00c251800d4030b24049a0074018003502010b1320b8031359107440c00034281082500e040240940c0202001e460f001c1c40e80a402d03000c180d25908106042000400f5410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 301976061 1250 301974811 301974821
    0xc04030503071e0b0115020607110a02040b19030308060306070306060c0f020a0b0409050406050f10051e0a1d1303080412020c060406050a02010b1504050907110d050702120d020d051c 80
    0x4c06c071081c46005071309604024100b200c02008a03040c02020f50311104807481c00903c0b40c44a82d81600c000450440381c030300041040e110307410b1212007112928404810181c1c0040c0040c0108004d81c102d5250f40c89400080d015149540640c0c400a181c0300301c088046168018a009120f0020f04500d16082e260340c0c0720307141584a50008103e558440080c0000c002280c840c01d940100c40d841020581d08241c4403264a1001c1849090302c0b44c01001e01c48200411320080f2070320380c200700a003240f03030142d500d100b05080540404032154a00000400055541031010b001003d5241d0541d21400f8a43c0d540c2d68001540d41001c46401c114483c0340301102084e00c03030704000c102403d200d8889689826a0210003400e41d102001c00b2401280d030303010000304440c0c182d07054605440c0200e690070429600c65000715022038a1214480d518881c0180d55070440da0802c00030810720340252814500c40c4904440d003952403052100d41c0006a10180003101482d20440252001a46010b0284610341c62000580e050760 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 301977311 1250 301976061 301976069
    0x160c030206041401020f0c090a020a0314041202070602011104090207050f0f0102041a0c101805010204031b051915030b03031207080112050624120a06050c04030503071e0b01 76
    0x14500c042ca0f11210341e0100094a551152180281ba850701c00c04007188500c4009020030314403580125445d05c10038000d41060015108442100103d0f00e01400c02c41c9203114500034890150040b882c01148651043c001c0d54150030180c508140381507d07120040c40203500c540819075441c000e007101041a85d1040c0b2200e1141d000040015031503500f4041c0c6d0b8030050320721400342c2800120401c000c1c61f00410100b0340c0907482c5411400015000a140b0000b1215000000000c0207940f00107408002c00120030a5403001130f2008403002c4480b502c803805d11a800c0d4601c0507035008000000010040400302c0340c05001a140d5910b40800c8859455012900c1e5410079102070f521b00d50070108202c6c081d64440d8216006100c520174800410b0700985078207841c7e000c06008907544410f00742d4001510300980010250000018150502202c103d405850b1a18529541121110b041ca40860610240442542c041d2500480a90701c1e00c912070703544140340d1001c40f0746108050317400d40350f10011501c049030303240c020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 301978417 1106 301977311 301977329
    0xc050403151d1221060d0204050601090b070b01030213050f040609020d080c03180a0b18120a0c06022406090a060b0406030c1107050105160c03020604 66
    0x2101041c21080240c841ca600c10010300c0402c50040000c0c95102d203005a2410443d0b08a41c800c440645049500c1b183c0040c4050161601d6030299400c250141084001c2d10740e42c01107013829400940d4155003941d10070004000307504010000840b0410a0407080003280703040c0054401c040d41c081c00140c900e66540740404110340b501010941b010f03410888031900e0b40466100141c1e03a600c50710b03058001c032680d04481c92150801d00c60324000c0d951252042400e0050100300c81540403840303442e045d402040e8000e4503222800500207280c05500850400240c0303400e0000c0a0f2414040345100000d14203040540303154403661034506a0080402c640b40580c5403151a0200058003d603005101112000100020ba06416900c218030030582d41d2100805442c82402150b103500c018407941d404508100480300c89012565a42d94240d0700c6202d180c00c0c116160f80100c6d9907a0881d4000d0165 = true := by decide +kernel

theorem cover : BRFrame.Cov 301798561 301978417 := by
  have h0 := BRFrame.cov_init 301798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 301798561 ≤ n) (h2 : n < 301978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
