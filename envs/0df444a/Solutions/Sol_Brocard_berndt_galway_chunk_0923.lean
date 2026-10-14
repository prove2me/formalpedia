-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0923
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:58:24.893561+00:00
-- url     : https://prove2.me/submissions/3def9e61-8d7a-4996-b260-f148b9155c52

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 165827338 ≤ n < 166007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 165828588 1250 165827338 165827353
    0x180f0e031306020d0c1e0f02040e030a030e0f120a05070b04030824091603061a071205070503090f011e021e37060f1415091b210108 58
    0x18140c4401040780c9006c1d014001d1000c25809860011007442140c51241e01500d205c44103940c0410305880c407000740c00130310b50801304000d032201c1d506104141d10014010010000040f050b5000f58480d400c800a0316103240d00011519240350003601203c0120f58032603ea111540303000d040c014200d9100f914030b819407042e20321014540c2c000380b132504c1a0a0000a00c00161070702e40520b841191490441044181900e80d1000181401d42e14641e149120845060310b9a952491601d05121001d110f02a41800740c140500350103c0c10000a44010311410f0781c01880d003024500042e034014031031088820003001841c800016490740030840104803550900d150700c920800b10402900c4881000c50b1000e142c40781e6484c401a00c0c07600600300b034403450450000000c1c03d07198035050305403001540f8161f00c1e01d0300d40308044038444104410f81e520540303a20003003507402400c100161502c0d40186c02d84c00c801d800ca26084003a10a00300856003050b6070707080d00180c604840ea89000c3c202c00300b442030302d109024002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 165829838 1250 165828588 165828613
    0x60606120903021b040906050108030304030306121a040606080a030c060e070b090d080c0601060f0801060309032723040b0916180b040b030f0c04180f0e03130602 71
    0x1e10700040d98503030082c00351002c04a031810003080600070601c1d4816124001c800214001380320f03c4e40600340280c003456492515040244c25204507501c820805111803107502d003c0396480c3e01007681c003074500386c001c40261940e00b007250107400700750040b8006004083c1c5c08410180c00100d009025441642e003405403c880d00300c500d0311440c0600c200c3d86451000c001503082440c160020f0a009813040e5001d07406e2055030390031141b41c20801d030400c0c0042542c1d840501c0403590401e40050062030309140c00e00810301c1a5500502e03450b1140601d0b0801281514580816a000c110000241540d81c0313081c10044144510f04d00c0303150360419614000e9207048900d0010b070805412441c07141414809440152040400880d50b503005051024900d0950b110081600006d5400400090085200458a0f800c03c201d0a0440500160205c81941c004100410401141c003280c0001a2a50080015101c401e00080740240415501c0b031040d501002410300512000f00b00343c0c2003510226800c07100c00c400c030903 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 165831088 1250 165829838 165829841
    0xd0f0c020a12033905070f0b04080625050a0c0b0a021b010b010503070c0f02060d0c020c0d020120150109091505070c120c06050c27060306062506060612 67
    0x400302521040030b070001901c41600f141820f0010b41700d602150a41652211416040c07160394204601c03c0000050402651904001c1d960b0001ca50240d440340348180c60394007410f00c8130780792040c13401d106000c02d8900c1c50500801800300e000340c001413414410f140640c4448020350000d586000f60030268824094036810511170307481c1740c0c8411385070b0a20b1519442d100380c400c0c10085404540782021042c1c1100143c0b00c480141142014140340441c00032507505001e4141915448182c1c081d402140080000d40e038006030192035140c4030300c2c0107021801c1c2c40c3c180e5810a10990814522025100000540070b0219406050003a000f001030b010301d070310040c00c00001d17120151415000941c040e8003050118400c03107403404807002d0b64140b070344240030f05a40d0001513400032a0034210000004c5148503485d4018042800680c89407000103400d40203c02c0003a51070700001d0700442c020315000c0351200d80c034000c2000d04056141c05d092081200020380c41c000c1d01400180c081c520000d113141003049960041c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 165832338 1250 165831088 165831137
    0x50a0906020609072610020304060b0102060f0408031008060c130f1a030a23090106060e0d080306040207051002030105030d0903120305070e0a030b090c0907020d0f0c020a1203 77
    0xa190103042c4e030500e005000540d801445a202e80d45101c21100f103880ca01d07040040d9003100151040150f02d034034281c14183c0423078001c2100d060564015004100c0c4000f0026401503100d6404043d0a0316501c45410108490469410460407442107805012400708007501602584070f4105075803805688851a522003d14240b02d40039120780b9040c41910a9882980034650140c1840c4000441e00420000310706181c0305444981c0e040c0840320244401010203001c0c0801910035070504140301e808000125052032411040074064031400f001250302039413960101c0f50410b811100711082c100440550030f00a610a04c1007521921445103039400b41e0b805150307164101c0c1d42108040180c91070105040d4040c01005003501e04000c20314010b0340c0195103001410001c0c5010720100c106a15101c5000d80c5450b1815106500c80c8207510308210740c290b4002400d04010400e8900f203c0c904071030244c00c1d51038545a810080d808903007214082a040020602d000b40a8020743d03a541902c1e0340d0a4041207000346 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 165833588 1250 165832338 165832351
    0x50c0901060905060f0703170a0516030203090309010810030206120a060602060712020a0e040e0304050301061a03070c0302070b031509060d03050901051809010f171902010c06140106050a09060206 86
    0x4040c048280440c5c90300780074080b814040d04242c070741e912a03040c50400540d0100c920700c0806a44405010f4040302e59030408041090a0038114514100aa419552806200308050400a00000140440aa1035030490040d64090040750321410359021601d000303141141c1c0e00d01c5403450514001038080c4000b074064010951034540d031000d8000686204041e5210961060500910181c0e441c60340e21030f031246004d0034a20310003954031241001c00301030035102c256000c4c003291303a00f0b030502d0309504a202084a8000c0d141781011a5000098502603050414035800035559504c040100105c09500842070326900130300b283d1050042d541c40d01040011035040c2d8000d00091000e0061501d15401800109551040b20080301c0c0039008003800294000d034241c10803401c4c075080c0e0301e04005910b48484840300c05820f200c05048000d0710185104410703014224003a0401910524610a104082d4040396070040038242000d42c80d80c445601410f240c2c0003003c8030703000414103030380010650b01c0420301d24007520 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 165834838 1250 165833588 165833599
    0x10c1b0204060b0f09011119200d0309061d1503060a1701020703031b0801230310020a032306130209060a1805010c20030f0a03030c080a1107060c110109050c0901060905 74
    0x34400d07181c400001c003003100b003000301c0c030680303108240c2555034600b140103031703500c240d071044330751420000001c2a4400ba448045d08201150007100c045d66610309800c020b404c0c00c0042680c07240e888400040c007070300440d800700c00012203490862200c0c460640043ca2040d01a4900344540d4220342d80103108082d125100c8400a002e100040c040002e00c001502100106000010002c00d4200002428070006200b5182c03182e41c002582132005406016945141c3c29809812072088040e0700d0035110f021001340064410b050101404251500c96811742d0180c04d8060021525031030720b070001821140342440c1d807076909040c100c1d00281643c0b0401c004031480c0c3d40a96601001507550041038510031031750403010b41c51702401e41141b0b029201042962400c60103680e01103030b003c6203508054400e40c0301404c0c04e02d04c0c50601001044003081d440444030b44540c8000001041440c1e40b01c111041a60030782c1c010380c15402c0122480c1440f40c0010850072001045500400c5a44c0e540742c00e40b82c28419203d0150440e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 165836088 1250 165834838 165834883
    0x60b03150f060c0307030e040605060f1905160b070302120405030c010b0f061e09060c0d11151306090b01060c060b0405060901060f0504080610080c03010c1b0204060b0f090111 77
    0xd114501f10b101500700900007143e000e4a4800113403254022000b042600500413804001c0e04000f00700c0080c01d50f00900f002464585019004210284200b502410182042c004034000300c0c0b0030b40c1103030095a500481c0120b0b908040c034003151a80d11241c8a02142d6081040b0100306140940e95206c40301001001c55140603a0303500c404203888089011000801000c1c804407000340c590702c0c0145400710340d01002c3e140c549070b16400541174078107090409007190b018801d44040408a5040240c100070380880b12018440079140a60181051300c02c0180b14002110000442c035810000300b40704a0f00c952420b101d41070301c40382480200d8030100c80040c2d212100400400ca0f01e4092030000d0b00880c21803401900d0b19031160701c0305c1d1810708140c8800d0155420740004200021081c044000c0e417030800c0700203018400c0d001e44c00030800891100000149890740100d4403c640d0750760700540060441380040c2d03844128076070b046400e41d080022443d020400410f0140940080820000701081d030412500048 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 165837338 1250 165836088 165836093
    0x905101401120305040b120f0112151812030509070b0705060408030601110109050a0c060c05100c120509010b011b03050307050708090301150303030e0304060507060207020301060b03150f060c0307 86
    0x200c940c800b070140c090180410000c00c044520740000c210385103038084003451a052007040701c03600d004140d206081c11508165003d0002c0c0070303007540e014441100d0f030700401c0341015a24000d000e000c242000a0407140d8500c00c3c2e101e51500764000c58402c00100c42a00c43d4655620001c44040c40380300d00041c01c0e0341000d400580000c1e409005503800210600d4040a500b1400c407005003115120241071b1030340d43c0b208010104004481c2210b0b409090b0a1911010b241e51039902c032540d8400441c82c00b011681c4415451000500c5103080d0380028125401c18000c41c148031004030300814003100c41c603000900c00e401340303c8001048040b41803034544c07682c1c03101d1444d0395901080b11160006002100c15200410810302c0c5544c00f4041c1a014056044031240a1455480c000d01121074138400d007880b81d0001c0c0f00400490303401c041074520f503507042440541c0d94042803000274010480c0d600141c904040100c180b00c294400e1136810b5140000c142d5040c0d00c40080c950401420f80210440d0000c154410030441c1c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 165838588 1250 165837338 165837359
    0x19060b041d04061808070209010b07050d030902010509040c08061201020703050f0307090504020c0f0c04270c0f15020c04060e01060e150d0b01031b0818120d0905101401 74
    0x40c000d010785000511000d0354007103d803200c021340d04295040c01000c10720f00b0030361030300c942580e005000d41c0e44220b01d41360702591400d8542c0c224248010900d55500c0c142c20569010702d044a0142e10000c204201c1c8841c074000180854100351216030042c41200303c10800c0c0d0030305200302c400b4140c06844036401c002d50784000003490740c00144148104091100001000c1e00c2d00d0000d0a80c400c13150000e020803070601d44006281a44005c1070a11950401d00b2140d01d6260070f1011001c1c60240300849540c108560a0281801d41e0950204203030a040700000107842400d81c81050035040707641e0960718000300807820001910300da801494091000c1400400c0200d0080020100007440500500e4840899480b403041641010001181b400e4441c4031498980d80d06104a81050f65801440552218088001010b100c8018609126041032013488401c0c03410400100f074000703840740310441c0c0d581c8e071200c1c0190280c92221821920762007140103a901c4000f190003150001800f00011020aa11b0080c1c140d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 165839838 1250 165838588 165838591
    0x40812040b0f0a0c05070b0a080f01140d29011707060f0f020109020d0b06042d020304020316030f03081e0a1127030d080903090405180619060b041d 65
    0x388081c00b043e013000a1030030300c011001081790b0008145c9031918400080d144000003040d410340f1038030101c014040807440340d0703500024003400d5400100001c0c0c0e621f0000000c1c00289808045000f00300702ca41181940d69001d00e06036807003010f038600d130034002039061503481c4180d000b81404038544006542030b030b83c4105500c00c030012541c80041340c3c440164010481038004080c0507103030030200d18100805400d09000710300d0f9200c404d4ad58401103158090b0544460301c040210b100000c2d070000045810742d60200b048520b004070568203101030540d603183c40c0c2c012f413a0201d42200403800c2c03040015540342e107210f1045100124034481c0a001d0360b50180880c020000c840440030505404e0110821051080003000b2945c01d058201d40d0700d090b140010980340140000e03580c810805100c0c100400050702005403203200b201510b01107101e880e0b498440070784032002d10743c2c00d8081c8503040c204805030034040721865002450300f10800000c2e886460381d003040d100f00d014071041441d184000c0c3c0803181410750288d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 165841088 1250 165839838 165839857
    0x30e040c1407060b01020601080a0b0f07031409150c04050d1101020304081e160501090e0919080d050f07170a020903030f0c0c0103150e071211040812040b0f 69
    0x510034091880081c81d038000395402d58029596000403005075804100b0706003d008118000c180b618015600c005407401c0c0113101d034607002d00e0080490003242c025008242043d01d0034542200320718058003041c0c2c0d02c0301304000b11101d440208003ca220440c0103400c0301d068607800343c0301021039450b1f900e550b446803c52500709811403008100c0012000e009005c0e105407003060b80400ca0424210400300307841c050b61481c040d4008030300e1013000c101c580c2e00142000220b600b640c4d150449035403029009410a411904421741c03050008880d4400c0203030202c010b051423080d81204000d147c6444091a01080d411241c807030205601140b035400c066055030226501044c4081c0c013500d8400b40c80086800c40c1c111010f10406854041018400e1240a0080480c83c040a02e001c000442a07500700350701d00c800c94414046094900301c04030300180c0c4a114419121441c0d42c1090100e00061071000c41d03aa0f02c140f080da24580a151162030348502040115412295108100c604100d40f002c4180400d40c017045c0034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 165842338 1250 165841088 165841097
    0x3051b2a180f18060a0b0307050603071b03020705180105091003021302070f05010903050909010e060d02130902030a03120b010201050c03182104090c02010504020a1a0f04080102040501020c030a030e040c 89
    0x518030910f00400005125501041000c02d0808511042c58078000582d04501d1269105004004400340d1008040312440f47c0e845c01c98078851080c0c00c0507400c02903903402c0240c000c03141c43c91207086d9200c07640c6468101d4505540c0300450382d5401c020b04002001900000394400c007440250480c0054a030007400500f03016070704920390300500d50786490031280c1450040f00494030200c0e000f109807501103540340c0104801390240483d440d000002034104052803000900c911009000680075419960103050303441d501808032201d16100b4200a4403000303000216440c1c2d41c0c03c155411505504c18001c0500a49000c1001c909503100e02c4c221140505045c214808248902c8082c1030410820b0b084c20785951a1b0110300e240e4450a1010b110141c40d41a0b65400c15603061005010058440404600845002d20580d12561030405007443d402d129038030725603007640c8006c24007140e5000d0660062013111026002c50303c0f818401d4091603200c902c2c0c41005004a00e01000210050402c0cfd0000074028400b07150 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 165843588 1250 165842338 165842371
    0x6040c050f181005160209131515170703060e0c10050307020118050d1107090f0f0f200306040902040c0c05010c0905030a03051b2a180f 60
    0x9010303001e800c025031034006035001c001d4542e001e007408072002c07405800d98503000303182840140d088818480c020000901817045640010504040c0e000002d400e03d5110002d03190303c0c190100c003100a01035400c0c91001d0f00340c01d158005504000312000001040c08400034210083c51038980700c0c020210598881428001c1e10f80420540c4d8440080302e0410b0640c4c0c884545904040400a00311002c030f00d88010ba40011140c0781000c500b0006194180801328034010031000b910365081824000780340d00c8000c41c03a0500e902e40215902e60740204003546003000e020800716811251a0f0b05071424001510006116820890000f0000740c00665100030042d00c0455080340d60750104d01120b4002038881c00003078010381200100042070150b503400080914049a01e10308000c0025190f0104010040034040700062588400c148424602c3e012018841514003c1c1d111118a1038500030f0b84005100c907000d80590301c9100d20700000d00710300102942c90503042d25960300702c41d04d02c001400f600b08191a2201f09 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 165844838 1250 165843588 165843607
    0x40807180209120303010906050402130306050a0912020a0b1501080c1312080d0513030f031a03030d360311011d0d0f110a0b040206070b070806010909021206040c05 72
    0x6102c11210f500c8600115600e6240541050440c2d403142c0091384502c2c0100400c00140b1074403034030107040e0381d04944002040d88460620200615000748014010040145a03002668022a070340100a0003500c0240703c90f941d408070f04181c41d401c5004903020403000b401003407840e0841c801604140207400440043e090701c400015540784004042115035041c0080c43d200c00400c03d001c3c4035013040d403543c081105d494081e9400b5024501d00480c1e0402c1540e20b1442030301d40c1c81e003c1414180d86901605032036403030f9240c0d00c10b0b10252808802404000c0289e010358074a81104941e024507910703800a10601865072903800301c55160448110503125921034504000c0c160203100c410303001e072203542e00500c84d440c2001c5015145000b06e515980c10701800755078000ba0004049425a00c1d194840e100c0300380e41c1d590f44005615400394400c05044082030204002c0c0e0300d0307000f4505901450007601e400710459a1a1103a030182d11804080a6481401101013031a5081c29004220810200d0030031508225202 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 165846088 1250 165844838 165844849
    0x70e0a0b03090703020a05030d0c0b0603010603021e09160e01031a0301020d0f05010501020a0b0103060f0912090302013e010f110301090501171209010e210d05040807180209 76
    0x25140e4050b540c211003010011450080001001080107a01800701540070b01070240c9140c40501024010309051000218075580030340c480405036900803c1d829150840c01c010100031114400058026a801400710300c0e0300e2000c0c42c601e0000c0b4072a9480152001d903000045025000d200800307a40180449101d01320341d9000e0028105109682c0c00004011b402420380f48241d810680c0b0480c195006440b4a03c00701d0210b103521419070341c0100c000b10300402c0e403800f000003d00c0b00040103070407500061220f1182560221082007128001d90350501d07484103102c9000544400310003400440e1110110801d10004181c255402007081b031000022001d010b40c0c10007090b0380c00c183c082d00d50305c00e00000601c2807203e1841401d0141071800e000000800001ea8503640d1141c10000305c009805003c45e40d0081d503032254036810713001000a402c0300c41a6405540c503219210004101c04420f008003401c000c105c80c442c409a90849200342c005000c001e280002074814450702e07804810400d42c00b00010040e0307403982c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 165847338 1250 165846088 165846091
    0xb04080306040c030b01050a030207051c110c060306100f090f0f032a0303120f06090c0f02060f06120304050405160801080109051c0302070f03030b0f06040e070e0a0b03 74
    0x141a05a660703207802410001260980084001030515000c40141d0999000080c1c50b00d80c4598100142c1d10216030809900d030007902070f0301c156181c22030b000420380c456000030300c044507040d403400f168a00e4642804201e00d41c0021204640c104001f20046010f49120701401c1c00c0004040c00c16000240e00d03070078101482c41150b049100d00e11a00b25081080010b05004500c509080f80403282c022501c050251001c050184806020000c1071010540680d86583c0b282e04090f544840800c0566170f070f40046005445080ca0010118400c1c0002c10b41040c004103900d8812643c16003485140d40c2c4940802103e140086001c039001d200c140000704094440d07102c3c190240b900000c03800d000e41d102a10051503030005030041c150741d03410000294002032000034120075401009084030750341d186104088000b80940e200203041546840f21a03018150507501603c04010700b61204100350a42d6410701186219034424001e640c2403110000d03082c42d01c0383e603400900503801400d41030456039548030107403030b60070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 165848588 1250 165847338 165847343
    0x81806070f0605150108040503071b0f091407020312010506031e090703050d020d020706120906020d0906050106090305100504030201020f1201150809030921030d050a0f060305070b070305070b04 85
    0x981d8000d00500d0701d240b84c1010542e15003480e14100600e000c2d40c40c00d84a00a20800900548840716043e8002030541104000750640125001c05103594614400141030300d41607102c107a900d41804590f0207840802200c0003480d4180c2c000e681c591810041c000f07143e0008102c1c9140c01342e6030000d10700402464141c0d5004400c6507000307091040c21810500d0605461082c0c1c0410341d40006c10801119801080840c201d801c02e082c0b54403100020301c500c10250802d0a0700600c2c85d403000800308411185640801da00c40d000398020051a81c0754101540d509036a0b02000e003a070742c0014401c0c0094401070700040c0c2c1c0244280300140c24014800907a00c0c82d500a20303038400c01184000010302004001d5202a005030b916443c090034181005a40b0684038420241c0440c0039183d858414040c1c0704603a040c0c020814171841c21a955140c801c1200002480d003a40e21038090303414041c400100140c40e007d2907040e00e80246c0030309000c43c0303400384420190303002c14021000d002050003c4000b0030a440340140c440d50 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 165849838 1250 165848588 165848591
    0xe03091905151c0509060a0e1504120914012003040e010f151d010c050708030301090209030c0a03020919150b0a18060f0c030309050f01020702100507081806070f06 72
    0x328403c2a59100c101190195400140341c0010440b800a00041240e041a02c1d84d100180c0002001195401c2c6214044408140707a20101400b0800600c2418600030760701d01c0d0b5941d603900b40c807264502c41443ca034000041c0080c40c00402540040b80100159030ba601c0d03020102e80c5400d546000c03c2034084001d84c00340001e07000f07909080001c00442c00c444500381016140c50000e484240003903a201060f4000d0842c104200316083c401003040400603840540118812652250b0750340c401c88010703502021815010340101c1d00c03446801e042c0741c0420700c140e03680107015410a507150742c0003030b01100100080a114684507903503440704028510b0400c025240d58030744640d807400d10b51000740030a0b0206d0f0351640740d0948824100314070390b07000c40b200b461300c200d619005244151500342240540340121000d84240561075601d140c80c0015801007031410f209981c40c41c16054101e4060700ca0340601080507200c01c10802005880600380f000485000f00c00505590138240603844540305c0c01200b141c1203070143d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 165851088 1250 165849838 165849847
    0xc1b0709090501020c10061a1c0f061d06030303161202130303260604020904090204050108070312021b040f1e09060f090305120601051b07180e0309190515 68
    0x1c940900c02d01b525525100d000307024561400d87c03203c0380300b030b42144088414100810b1034291850000c2c61121015041c00d03081c8500d074888403000e8010b1001d403040f080450b03144040d0148400114007100d12840005000c0c505603503d0744040944000c90440301d00c05c00142400c201030380840380c400780c1705508510001099950661070b020b4800002c840200e04007019100144000c5c0c0306911015600c86010340d40940c07104400b4005c540907085218009500600346000858901400034413041240d00401018810312018041682c8030700c100d006a220b40d02211172661440d00f05a0022800c10300c1c42100014440604104142c40d050070303400e1007002c070b92990860814881c00703015038810f210010108100c80c450954020b0904e02c1420362200240010340700045582e80604190340441c1f500c0c111a20a0b000c0e01a885520360005004050310038040d400c0c40382040030300b4890540c0085405004601e0a0b081d14100207256000050071014032050307100105994403400364074541d4204000031281c68 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 165852338 1250 165851088 165851107
    0x60f0d0b010911040311040e0309122a06030f041a1801060f0b04030303051f030503120f0708060603180106080c0a05040b010c140106090606080a0c02060c1b070909050102 75
    0x261811062aa0100f040c28070052011401032503003006c3c1e2403030885000502041d6072a200c0c0c11400b5a80f14a94405502c601000c2d0040000c034440c007504500c0c00c00c40c0016882e140b1000c50b052007252172180c100d0400e0001907160341482c0c00480c2c220f030180c8204a15140050141800400212240b061600c0c0083e00700d2079900d0240a01d0001e084c1c44c049100751a0300308100140180a82d10000d4101601e500200c0c1c2c280507000310b94440d201c400b030300350051039880703060440ea039601040c819030f80b894001c070006058861109806011301b0040d0344009041d25500100700c0e06405c080c00b20040d014030713000701c000511000d105640c01025000c0c0500b440152603400c1185101440d40928019030903c140394005a0340034003c03495039a0302c0301c41d86181d15400c4034940e00608064021011b0b01e0700e407102c0440e28640118400c0d104460421050165980c500c2d0220303261581a20750484a4909216404c4101e502108415114401d07508031031f02d00380d0320781110303056a0590030150b0303d40e51b001407080360 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 165853588 1250 165852338 165852341
    0x3102030a060906140115050f130906030201022404060207050f0706020f070e0405060a050903040308120a0b0402070f030e01020c0901030c0306050702030313110114070605180c01050f03060f0d0b0109 87
    0x4003040380300c0350703050940c500702c86d00c440707002c81c40c05820400c180040c4c86007002c50204203031103c1d60032011001c080c60303455101c010024046400f0036400341c030551001c102c0143c00950000d039a20550f483c0b80141c0d40f1070360344100107500310240840300c500611900909680d01040b58030010b00156004143c1c1c0e081d1a05854240040c50304130740d2103400c0e00b40c00c001c0032810004146801820510f4002003513030f180e0050904601a907040101260000610401140f01e17440034140500501e61080001000703c00c02c1008900c2503041c010052240e0114620200307000302c01e81d085465040c0199910321401d9400241c174104241c204503040f0101c0a418824040280b2070550701210300c3c0002d514504001c40d08180780301180b10028882405141c6142c0103074030a104107000c603600c00b124152119007500c1c0000103020112460043c00c00010b50400384007500140c2059540c2e010384031a8900301c044501300c05a50300007040c00780c2040000f11101c2903a21400406c404e9a130207030485c02400c0d418215802e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 165854838 1250 165853588 165853601
    0x70e01060c03050403110a0812030702060a09030c0605060105040807080f01111e0f28020c01020102030705070303020c070302090c030412020a0209010504091704090911093102030a060906 82
    0x90410040d800c1c45400640c0110489060340d4212842032a10384600c000110501030035002003c1900271940e120f043e80d240d94015500410042c0c00f07603841e543d9602c064108550400c40040c002685100004001c01c0c9180e01158001c1c1d410f142003480c2c580c40e1640f072071030040701d80c0c00a16643c1c01854103205880013031141900541d40102114640203006414084a443e80e01c080703460004001040408107840030201d480c10b06245005001c200c0b02c0a0030034230340b000b2000b014005406411040d581641c418401c403486009503444030750504c881c58900b14000d4000100300480c52049041c0440942e03261610544070386445550031b942e130301d00b620349558035805840124080d0742c4620707a0440184e0300e100e861815982c00340c40001c0c0500d1241003040d801d10304240102518180028003180b0417805d508980b4400340100445000d018040c000d02500300000c940581d141010540d00510708440c44200c402d00f40e060030900034824101c0d400107803c140e540300003200c0b50343d0795460100c01c01c4040c1c0a9803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 165856088 1250 165854838 165854849
    0xc101401050a03150e1b0315010b03070309020a080105090d1d030601030f151505120c0a0302011809020a0507020f0409050a0605071106040b0a050c07050a0201050d1d070e01 76
    0x144440e524160100d0300e074114501004120700396501c00b0399400e40459210142100c01141100d89448080250400e084500d8549a000c0c2c0203d83c0c140142040011025040701c00002e1194656a10305030120010f003410b9400b240e118114540005404100340211400b0b1401d410260040c03107240c3c1c5002c0d007401480621150139142d448500f50f07440d41e02050f640e0449421010504208265140c465080b211441008590524000c0b04191488440c0300401c240c034019207086402210080a0560701c21410a00f254803c605480a20065204101d0030502d2003074140030349400b945a04d24030301070703030005407030040003640100341c3d42d0562401d50880ba031081c400340c4081004206c1790300c803103407501d45165001d042140c03241c0c041401d041c440c4000c100300d8032002c400e0382c0c91401d0a00c0c1150007000150368032000141000081791004140f03404680c5055401001403d40100c554015107c603088500459000c135581d4a0b04403402043c400c01c420840c03800c0015040d00d1b81000c1900c129003034182c110 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 165857338 1250 165856088 165856121
    0x5010e07090e0403030507050909090606031905060c1303080301140102150c1e09120c1e03030a0807050d09030c020312030c070f060605100c03020105010506030708071d0301020c10 79
    0x1002000301810b103694000340c25190200d126944c0e07240c150b480d84a100e04564202e0401420000100d0713020684600596044055079580340d4003100c0d00411001600000e841c580040c4086840d00e108980240350714154940c500e104690380e900c400c0b6103904240d001c0b14240d403041004022035a0706105c6054181704840c3c00f4015420a804510074901603030101d10500424407890100d90601041070311040300008001200b00051034608a884d02c2d800683c0c240a10b12011042c91110303502101581c034400054000d5050268000e402c4603001d1025003140c0600c4010400580c01103200c0c02504441030003515428500780380c902c1810f290041554000035210010700910424a4503407040714411031b00003040b140b0302402070415030018034060740003da05c10150709540690300c2d04248080070441c000d400030800c5030307a6202400420301c021683c103030028074840b0002e20594050000403e820a80c00c05c1300f41209510700100c0e007280e20220114001d40e101810f0006c01d145a0b000b0050700e00c1c0c0c44c030310 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 165858588 1250 165857338 165857357
    0x1d061e010b09060c070306050a0f112b09021806010206090106050a05130f02161401020405030d20070b1308070b160312021204140309090103031d090a05010e07 70
    0x1030301032140c09841c480601c5043c0008045121082c1004644051608442e04022a00703061442100500c3c0440003c0485c5050100140c8030702c4241c07050320a10201c81081900c0b030444a594640c0140700a8400005181d07900020303c09a100ca00b06445442c0c0020f458401c1c034148240003a18003000205480803503814200305010a84884500c0021241c00f5940002d49800e000a5040034088000304021424800324500801c01c40207500a100c29001d01201e1940786040c02a0030b0a0b03114500615030594072110307082c403026204044c001e4424000d081c01d050645041c1036164100380c010b5224040401010590681c2614111a09002000320f00018101e01e032406a42c83c80c140540701103690100807000d061310505002711101d45510560380c804550f1281500c03004080980182e0741551f224100743d80d444900c1c0400800c403100c05a009042d1000c0b0b80ca1581c040390030700703400007152600344441300512006071500010140203c1040801040c198103010345c0082c0f5030310052000041004060 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 165859838 1250 165858588 165858599
    0x2a021813021320030106030b060f09060d09050102190207051903020d03020705091003050606010905011b050c1206240603070509010504121b05040b1003050a1d061e01 73
    0x40d56556039603816155406070002d09030000000b0400b1070788240054035030311502c9407198843d0707000314165052a20100803803204081032008900451150522100003008004290f1401101501022320b41ca50082060302039603840d2403d90b0002295130074a00280c3c03480421241d01806010007508081d1b40351185080f400c581c620320122a444080d025850b2400d842c0181032003032180c1d0005d040050709003181c6060403d03100328098039070310080d41c060141001084441d0310924a810454205070358102c400c03a40d0450000d1b50740d01c074440840d81c1d0300c620507403100c80745c2340c415092101540c0380b00584510314010004c00c0c9030169008503403502601d03144042c0b006548040c140e0307411084515102c1d07102d02c001c1c4010780d21449503401c00d4000c08031088803d401c10550721078032000d072005000004019070756001400155030b440e11071180d124660407048411548130303030300c0554070030320f000008500d804ad00d50140c0c04007001d1070940719158000004004c8007100d100c0944040c0303000081d80122562502 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 165861088 1250 165859838 165859861
    0xb010509120709051006080106030204140f012705120307020d0b07170421140d0e0106170601061b0804060f0507060f0506030d0306050f040b012a0218 66
    0x3485160310414404001c42549403003080380340c000e0441841c2c1001070781401504009540c407030b40300b03a000240d0301c0d10020602900c03d00030f40e421100451400c0003010103200800250f168500c001c24108620b0030b03919660b24450f01c0e03800e00000102070454920714104014401c0c01441074a0214650740708000480c01a02d400b400c0d050029048680000b07180c90b0008100c0f404052000300e40d160785a4081800144400c0d899000c814016400c40c2042e0a401d601c0b050355550840200318286150500035024420613941042040040340000083d41c2c40d01d8182c0c0c5480c10302036848440d1594480c50060040e941c0161003100c0c6244010416101d40c5880d41e02c0c02e180d403007079003d1002040200c000c020803550003482600d0126500181c140b080260a0810000814045a01500c01d101d5a80d100d800d0034040d2068005842d40509a245d4800c00c007010310002d4015210203e041083c0041d41c1080c0c0c0c0d15080605201d40d007441e0310604541ca0500401c0110000d6490780d4002d8114074040c4842010300 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 165862338 1250 165861088 165861097
    0x21060503071e0b25110a05010c0b06120304080102070606060f090f0b0d0605030a110901150503161806050d0b090f07121b090305120c060a05060a03080c030912010b0105 74
    0x100c10140b41d6907854a182040c901e82c41514454880c1340c11840402000303501c01590b629000203551740c04200d43e4820045514000d50540640114105000704245007800900300410030004400c0340c2c6040d5880302803d00b2680001c0c0291900f030340e503a000380f00041d44210044941245441c0803080b50303040000005a2000321700c108404498000b880302050401da4000b14020400201590414503150401c0300d036112045074098400c0424500104200c0780583c0c01e468840c10036983d2070b055984015166000e0020030703031030005010700c1c503810350b0074520182d400ca00504403954607140c444101c0181401664801004035200b09601d0081016461001c100b03240d00190074a02000c442d02c0300031010000f8880c44420152050070741808408441d000380f41a002c076881802120000c5501e00071400b070078024200a03581c00d80000011400300d076103d4010f04d81000004151170211552562440b1141d80059410040d41d000410000e010b460000702045130069090001d0022010b0500004d050307108 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 165863588 1250 165862338 165862349
    0x60102030d150504020a0e030105010503030406020a020d020409051905010506090714071b0b04080712050a0f031209060c0e01020d020c1903020409050106150e0f01050a21060503071e 80
    0x1640c00e542c044080c61050390800915024008666500042e9002441c8a0000300614020760a140c000121410004101c400310b0704a50302074080c004072030f82044000201024280d9000d07440751201e8011a005000202142402002c1d00400e414903181003030a503407005240900c1910208100020160004000000c1e100503550540c0d07904010311341524081500d03c1000d001c02c40d0100040307010314102c40100281d0b90f1000454500c0d81d0380d1092103006090b008001842508544503050018940c070580d007096921904003a001030601c499803504440b18100b0989100341c640c0001005240c1007070b001e189200081c809081e5400f071801001e5030300d01507031078600e004003e41101c110800e0305040c1030360701456006000f0b114640d01818224003800180c002c80041e42003803661440124000e94864440c0030700a0100d501143c0d44000550301138100074a072806002251352402c41000021020b0b008480031803c0001e60310381028145860b00109070810041611440043c3d241d40c1c030a007510a04880 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 165864838 1250 165863588 165863591
    0xd02030f0a02101104170106051f050f16030e0105071a060303040b0c0102030f0f040b010b030402010c080d1e02040e0a05040228090b09060d06090305040f0308090307060503060102030d 81
    0x4500752401c0780307070004141d40c1c4541c0e203140c00c0601c60321814481c02031044402c038400032140300c0c2800d10300900f03ea4280c8101c030f80c00b03440b0002200400e002c1c03604240840d04c103400c00c80d040030307440d001e0011075600100680741c602d00766401c05010182c0210b200b400c036020a182c06410140e29644182010802d9032618000e01c4000002030b02580d0104101c4024040b020390160711041000c012902035002900d080599170b01c0c000002e40d009410401d550f00c0346400c00900f064507481c0c040c2c80e2313a1070781c4050f000780e04004202450402180c0341d00000e06a105028000103410b1aa01007001e002588520320070081d18010007041042d40c10040803160005204c0c07600051a80781c030720010303403c40264400c04404034801c68881c544004140c121030110f840e030034000e11400200008000b01c1d8442100c425034025000395001021817019440b84891921038100a45060b8032503c0700100402c4030380c01107840150000d8018128142408903030010300403824803030b056040120010b510b0f030249004201085 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 165866088 1250 165864838 165864847
    0xe040311070f120b060102160303030902030a080c1617101802090405030d0608031201120f0537020a210c060503040501140402090c0c0106030209070c050f0d02030f 72
    0xd21040c0448001404190142044265100311150200c44811800c2d00c1158500d40051134650000c149008051202110002d1150039a50103800400e003100050b40c041c424044104000394580c8020b107030390a24000104069081007944980550842d00700e10007888000d0404c00c00060b0000d55840400400303180801c00140b420810ba2107841c4108000e075001a100d42404240038001c001003020842c40c00040c009281c440c10866600c0c032910000440c5d003100900100191140590740d00d107100e11034a41c2403e00b500300d880b064070340081c2e606038821428150222000c009241e040a4aa01280d000030315031502280d0005400a001481745030301080c0540e0070608154185602d4507082603001c081510200d0f10f03004018202d400c1100c2c00c541a41c41d00c0704003034448103003800c0b082c03240745d00800c2c11505549800e18040c6c03541141c40c071545159207400d030100c010307500d40c0d4099124080550304d0301d4000b03001303040003880c02d6200f500032a40b603004161051030301a804801c17918400c020f419850b40e80c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 165867338 1250 165866088 165866117
    0xe0c0d02150a020c03060a050601110708070303030b060c0f010203010501021b090112082107080604020711060f0f0403050c150f0301050105070804051c021002030a0e040b0409150b04060f0e0403 85
    0x62000ca01e104c80e03818011141041180c03209039102c103010b64800e03070b100740c02a860741c0c1e41c0c596100b0f064001d00005a0200342d0800000c1e00c650400441030768060501d9091506242c4035901d8542d040100c074155940100040c400c559041000c002e034111102c01000507100b940c4046050201f0602030424807503007001c1400701780440e100440d40c1803400c0c20440f100c4000d038582c4004d11310100b82e4001c4001142c1c0008100141f03000d000f0341d5048c542104c00c0d03140d1044010200442036000756212542842c09003c038210340001940500001c500581c05090500d045000700414841050710b0410084800c3c0440d014110a00b41620305480c0d081c2003940d51918681001659409598451035101750888242d52042845000540800b80b083d107114000902c40d1200b0307a20b0340a81980c002c0003840d038172000c3c241d43c40c00e9080f14601090182000406100358bc44030709240050010035407140781c07100c604108608051166500400708600441249401c04680800c0c0d1200900f019003001300801c1003c22 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 165868588 1250 165867338 165867343
    0x200d0603020a030f1509050607180b0f04090c140313061b03020a030f0b030a0f060e0102121f050f0d0606090501120605060306060a0e0406020412060e0c0d02150a02 72
    0x9150020506001c0c5543c0c0c0ca07050740e05000030360b0f04640c036400004400042100c14086c4100030303540320001c0c15590380d464070100d81e081382c07410765403903ca01100800200c400c143c03002003900704514400c8551303550811565a094414400300341c0300f00101140240a0306005030290703178126814114013640c0e1080ca0502d90043d1044000701000c80540b10704107402c11350164002c1c10113a04a403018003c1c402c140b4044011185c49092881d01030704a00a11070008801840c03091601d88503410014201480844007400c98001040c08803040d03661406010721652101312690440c2c003022000e0741d4490511003c9401d050030310881d203000d440c80c031000d03004001d010340085020b08507a000400003981d650b0148260362189400603990103203400c01152a504001c1a40d03841602e0140ca01c1c0901c9180c04902801818010f005550165090001107030110800c546414400d00840c40400d4800128458906114051354124400c1464004941c0103850f40103140020b000403030400313900c0340c403031070826070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 165869838 1250 165868588 165868601
    0x60603031914090a090c03050a110d0b0310020301080c19030302030904020c190305130e040c0611030c010509030a031a090c0a030f05010b131a0f0d0e06090a15200d 72
    0x3135100320070510200c0c101c0f00a034819008054240c0d028441d50315042c1c105800c5502e44500700700003007001c21010b85001c6058000c120048406000c0340c4c12075003441c5402c2c1c00c9030000c1e004880030350800c0c0d40d412110300c2d003002002c2e9450102c081700c030704640c99a54082c3d41d9110720001240900d4003c50140000003083c80707031403a004000a0603c030408814030707009000b64000600c8038492100d1000c00f1403a52040c6d10020310440d84000e1045030039040800540d209400788115170410700c8100300c42c0341c0d411800c2c01014061500c85000b1502d409000402809580d0614048040792408541c400529076800c50380c3d03900300313107912007490344e442230200d0072000351070400411041a403c01000140d100254001400614190843c0c24000c584500c080201444006448840c0780402c0c42240c0d0714205542c0281055a5042c80020302c0c4011408803500300b0104403108240d1b034003d400300405108840c04805101c900c00b0b0340c1088a0b4440c2082c1c40300300c03084c601c280720f941e003c0031590703c00d503070f07036a500c0315 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 165871088 1250 165869838 165869857
    0xf010f0807030b150d0e010f020703080c130f060302030601030b042306210307020a060807120b180a0209031b011205090c0a030f1509110d03021507030905060603031914 74
    0x4e036450901414107405400507003510340303580d0f180c100e610314049001d10a072031074150b050b0f60300819900c032026560b5064218404040c01490b00520015001d11510b0006000300800c0d00c0150b100d00d008070001d0b0071507c12040b0107000b242000901402d9404082c2e002c0d001c0303900e1042401d21511248003064502c0c580100b08010040203415580c8a40400005800d6603071003120b075060020303102d02c0115601c40c401e40ba81000316425000800d01c106041e008113081000141101c000c015290a1482c070246051320400e00465001880c0c0d1403504003406880c03540c8420b01081d0105402a03000282110408803945010341d594102280780700d030381441004076114004105039865904d0341840da403a40b806180455060003412540f081c840c00c607004500d1001d40009030f01c090005842c042c00b5035202c02d00c030700314214003950103920103101100d002e01c5d008509664002803c15010f1420340c1c43c150300640303450b200e640240b007400d25171078800821444181c580d00c3c00c80307840d01204810f00000e01901541 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 165872338 1250 165871088 165871129
    0xa030806040501271b0c051e0705010807020a05060c040501030e010e0615030c031b09010e0702190303020c06010b0418050f06122e05060105130501050a05090a140f010f0807030b 78
    0x410f60310b075121b11a4040c8601641c2550fa64100b24401d910b06800003480e006d816030404202044030358000c81465a200010703006462640526958241c03d1580498000060b01800f00c3c052199513891b01c150900454400003c0182402c1c14008654609004100c1d54041e071741459401e030642c505000e210b107408d9001d422a4040405982492141901d42001602600b203c400024041c001caa115601400c521b80240c1801d03552155801c1022103950821780c2855000c11025140180400c0001c1c003d04902505944907828282040c101d40d8240c1d03180074600d41010240646e41490514460300030804550003514518641d03d218141000d200103094070120082d00010016652049910424400281003001c0d5645400548043c0142c500400d0326070311840b003d01880d406a80100011080390914500309109400040c0ba0085180c00030681540050b111281d00d04207413010140d808000d08111b10352a1070b00711f0040a246004250300101602c680c0200c1300ca4880c0b1035203840c1c6d480340808 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 165873588 1250 165872338 165872381
    0xe06010320120606090f070e0904081209010c0306050f060f0309010e03040806040209010611151005040c17060103090803041220010e060f0903040303051305060c0a03080604050127 79
    0x22040d45482c422aa101c5c014510b010000c0c0f1250701e81d400440c0b0030451519109521014601446070b48640108211201003040048042441039590341c02d204007242030022601c44091480101070b20302c4d5500ca03901035888242c0340c14107030f03039200192101000303003460694980e5241e00005001d4109924654600c4c0800100480c10200100311b0744d21842c02510f86060990780d8070300841e074069400014407401d802c1101e944055104029116800001105022565070f840301d00080803038106007890404980610b91070030000c4602060198400e0302404d040000c94034a0719900d145210040000300300aa4030140c0f1300285014411186250000d46082c1c2540c1c521050030a001f0301c2041d0201200d0322400001444004440d41c00c0c5100703145490203181003034515a0280c58507000164004d400030340d4400702199944540c00076040c1400c1070401410880900d04000c0c014940c042c2c0818012030400c4014444045030400d509441104040401c4003181d003245054003c21141d0344074810500b0400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 165874838 1250 165873588 165873619
    0x1804050c040303080c030f04030305060406051c0501110c03190c0501140a051302030c040f0e060403020622030e01080a1805010501050f06031003260d1508010e06010320 74
    0x20241c0140d038400c0d2525407240d180e000c40082d03103000031038a5000010303440d400076001900c40c1c0c10450308414068000304407152601d0000e100305460742201035901d0032501c688000e2007000d00848a10040c5031308030529001c007126009880b0320601d0880001c500d01c4800010056100d02e04500423590810007c014030035003520200c407070000640302c0070000d50030400440c00801e00818944441c6500400600e403640c03101d014031014180c0f58882d402100da881c160219450801d01c00345115510940c0540042e240c064805403856204242030300f40f000131702002d480040d4110b146001c141000342002100c03030f542ea64050001c0d110035000030103280c00c012591010410150007860681f181161310080088100084c0803850004481c105441012031100f08003190070300e0907000030301500d107100e007602c0366441c880d0100950280d0180e84402c0c1c1d850320356000c0c071841c100320a0302415400009114a14841e0401d550b07607401808060203250050300280303101107000d61451305c41c110241c001e089090309507 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 165876088 1250 165874838 165874861
    0x8090715020c0a050306090a0204151a0901020d0f020c040f18050c010813031b030917061506070b0711160909060c050301050a031e0206030406150504020309070b180405 74
    0x1149203d004000e000d8011a03a03150202d20984518008002807980395000d4080001030070f001188103010225150010405d400060b500b04020011418401d0352031480200091601c1c1c01d8011038001c1028149103070202d41e50100381d11120440498021910341c000040010081000303c00e070b00400c090f4010035604000012503200e4021000344c0b01e094040d0b48103614103e982d0180880100000d15803030740032128003a042143c2507801c3c000c1ca041141c1548a08041b000e458071400d078080140c0c080000c2120700d08091400e000c00e9038003518403e0030004140d56101111002401100074800f9174115001c1c000740030420300050021184a558500341c1c2c800304030004190320b103003d841850034090a14400c41c0100200d90403600c01400020710a451f548038440364441a0308400c8800d0980e1086a0169a600002d1070080f40541000585103054a0ba07000c4001c4103513000e10700850041c4200302c600c2c0c10224002045802001203507a9032052001040d1000018a00140c1c2c400e19050501901048a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 165877338 1250 165876088 165876103
    0x804080c2416081b18030d0801030506060a03020906012613050c0d1205160c0b09030f1b0123040314061b0306130b0409060c1b050d0809071502 63
    0x54002c602d00145820203c0d008003085408000fa03400004002043d40143c0380182400c0b0b4440505400300c0e00040000b03410f00c03048410310800a00424014024440c00b03001081c0c000004503007030303440c0501d0b55022405400340209031720305202c0202a031049641c40800100750045030008566950b140180c0f1050741d1490040d07007690a441010030240c110708000129650721900100318003007041c1194800c41d940e42c4000004040180d1703052101d000503022400c2c03100948003001d4000e84842858060610f0400c52088252255204c906c0440001d407007461540240071081c600502a28640104040c3c032582a44a216000300c00044c000103200d882c4a18680b00c2d110307041521200d440e60407140f01080103481c240da009210400100c2e5a030724000302000c089880d100c0010940c9050000001c080b180c060f041079035038940301c0081080141d4440c1d8030190100450130042c50030300440d15441d61720302c03840381000180112503002c0760302280e08002c0e01000b002c0000c2e01c045400011040292034400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 165878588 1250 165877338 165877351
    0x804151d030c100603080d05090f070b090111160e060d0b090109030905010c0c0b03100b070b0108061b040b07080c0f01150b0c0c01030c0509030102070503070c090209010804080c24 79
    0x30104001c041004034004c8108a0340c200d0b4034581000c586810050040c200030f4240201403058042c0701400d107205001040c024803405c11265291841e0b00e0000d40b0414101076003001030713004461060468100880e421040c2c80340c41c2041544c80e0f803458042aa807000296018014040c0d0b0300401040c490150808900c80f442595816078041d079410046d280d4007800007008160403000d0a081c840d4000d0074010751b034001d40318045c4c02c43d02903940910500560003190281c2d1100c07940801840302c2c140c100005d0b500310103182140c40343c07001620302443c0e65004a00601204201c0060f544052100c0c2c1401c1d0303a00641d03100142ea500c10304403102680284078840340200304840e581000100707004403200ba201b0460b20b520140c102c9400220044000300040395050382444000d11500c2d00e42e480900c050409244214011559200030741070214a010295112458143c010080046540d9110b41c0c0f082e00550700408082c0c4801005000c5400c04100c0e42401c4080100186003001380742e81600103078054074 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 165879838 1250 165878588 165878593
    0x60605040f0203060d08030a062409050109050121020d021930051801110406030b03030903190c03050a0f03030e0601050306010b09010203040b0d060807090c0804151d030c 75
    0x410304a030300c0c00b0380c0421229542d0021842d0403030000300701840004d5511030a440f1002a03401c1d10381c50044171001402406d02d03070f0310656206602166030005042c4001e4203007420040b42c55071812000900e0352652a154250f01c00d100c0450344410340b800e4068481c90b2003088810f40d04e40c0c144411012590722802600e5002410103c40070024190500c0318440071043c491801d40c50405001181e800380c240a080001c80d40c02082096002c00b03400c0c414440c0c01041c41644a650340c0c50500001e09558203407600b94070036003041012403095a40003a80c0c42001c1c00301c94030f10fa80c140c01e504180341d500340164409400c600030301075078400300599130200f841040e100362420000d013580f4440e01560b4000034001c0f260984d0000c401441890140786c058001c0c418144105c9262917212030f40380e40d4035082114111501911941c050011080a0003584081c01012404200d03a00400c80300820303240000d480903003c524002c040c03800011250b0404440c40364507032603011080301002d410990f40d5120152201c841e0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 165881088 1250 165879838 165879851
    0x2a090402030106030c121103060913170c010e0712030e01111207060513260906040320010f02030f0f0c01050403020610080d090302040b01020f070e0103150b0303180102010b040906060504 82
    0x1e86d10460f40c007d41c072195001e003103548030000c1c00a0304074040c0049071625901e814a0f00003407009040e0000d80461821404c1c0c60340c021248150039a00d2104819105801c080001e10254003480d80038080c541d0540380c04100c03d608400140c44414140300c0c0c0c0001e9006104294034100180310003002c000d0701c1844200700399035a44030552040421414010500103910360718a001c0300c29400c031144100c00703205e081407800d0841000651039034401d80c8121002d00d80d02400f0318802c0d551f450000d41203c820700b0481d0b0780c2844890025180d00c112800d0010008004c00d910201c00c43c420140c0b0400d462190080101d41020306010355155000c8a440001112100010540c0755001c5400c4071031549a8585d0013103d41154204000303080030103400d034118401c803162002003010401654001303100440001c0741c154154100a902c4074501160360080c6801c11952450544001088a640010901c0780548420200300101d01414202c045c950340582001e0101003401041d41c085803c0b030340101ea040084 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 165882338 1250 165881088 165881117
    0x30708180c0d082104020411092107260d11070306090f0503031e06100c0b06040f02030a0213120507171515010f02062a090402030106030c 61
    0xa41064008941d8200152a40d61401d181191403042c40c400c003807103420402c50318903021500e0b01180030340b042c590400b000d100c01d509141c400d540c000381c940030440d8038192008004c50020444050300b215080d80380b60703011182d80800e01194010300800940a00c40c0650080e1581000d101003400d032800c1c2c01000078180c0e4043c000c09142880d8000300002d480880d2550b100c44d0028480084190f0300c0a001e4545040002c900380011480b0341403015040c04203204603805070102d00706c010000d074080d0a920344409411a0001c400d12001075100d210301c02d0695840001c5406070540402105205002205108410744240c0140480c19410b440150358183c1c1c4521100a0102440001e40036030440c0f4000e0080021803211041c2c0a40484216009052002002c08850100f21049484940c101c0040725081da0f1010a0080401652004140c1824440e0b144800900d080543d080c0c4a2080c145010780d00d81c001c4103503071000030014000c54480d03940d0900a006820030710056000100c0c010a00d188 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 165883588 1250 165882338 165882361
    0x50708010e1803071a0f0109051308070f150e0c0103140c0f1308030306040615080a1505030a05070501021c0c020d03030204030204180c06030209090c070f140102030708 74
    0x48481c03045030484252a9144000c045182d075140c001003a000400490000ca80e14203407030130b1102440c115008803441d05071402c12401d0300c103030040c021503401c00c0c0c00e2160010b90314500c02d020603003100c03001d0780e11083d9140055079190400c400400b07050840380d4643c0b0b04030042e4000601400c00700c007502c03c030000c9130300114100ca9211050701a00e0201d030010a40c4550310f180640700c1c0070004413541e49024040c40844603010703001d500010142e0704c0001044607500f03040c007032030300101205004450400e0400d0400f0b80711600081c00c5035a555940e425024a0a01c40440b060041c4000390503201c0591803810081e4451000340036150251142c4001d400320024002c0b00e48441d8000e81d43c4110924031640c1c20130120310540513003942019024440400561340e03d108079054105031244c0d840100110b45808081011540e000e10140f61044c0000d1000351103441c0455030203081d007540260703186010b02c0d01e1041801420390141c0104541c003262014560705500940c050705141d103920115540e00c00307500c0c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 165884838 1250 165883588 165883591
    0xe01060311030f06011202010509060d1a0a050d030e0a0506070303060e07020a0f0807050a0b0c1e0c070311040212070f110d0f0f02100203090c0a050906012a1e0204050708 75
    0x803c20360002004004c60811001c00d010030b50310500d4401e141001031400540702e60042d00c044405580e0303403200e08400715211162220103000581e1400440f528000000700308080d00c030405420700810121691441c2c0d075120345d9501506c8001c080a40711641ca0800078002d0055008040c0444250000706000324000219480c1c05544180d49240c2c030052603035240159080b00394103c07002d01c030381d12540340000c3c803c0c142c0c1403044c10f91456150721008200e41e130050101e5844c11407004a0f01c00c0140c840c0b40c0d0740228156042e07a8209074019407400884000c50300078030405d04107140788174640c401d103c2480e510107511704d0041c5c10f55a59026900361031141031303103c0300c0581138035003c14041032960b40813600403c11107690980e00e0045d160716000124150040c0ea004440c0b40d03126070080c0d40a284186013041101024103400d807482c1580d4030341080040c0080c034000500c203110007201d403404034024015551511900350b0050012204051040c00b00b044c0fa810800304070320490030b24000561081c0b2424000307 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 165886088 1250 165884838 165884863
    0x90b0702060403080d0213150f0c0507120804050904060b0a0b0903030319090b0405160602070e071407050a031d01032c0708031204030207081f0510090e0106031103 72
    0x2a4900b51039a5a200742503886031200c04001074007488440034205200081381c000f0200b04a190000602a440c010400c1e82140f00030f10500c29a40e0080c80414030015804090302c3c0b035080b1300121440e02e03013000c0d0f02c18012a0300440e441800030b0100010002c0c02d8022603400e0200f6201d24800365101c0800600c03e000b40c013a00368042e8014400120110040348419480e000014070001e1200c0940c1c49408444004880c05d82e03055012080d0305030462000d003620f000400071380c07000e802414100545000400400760001040017001c4003030000360101c1502b195140d5500200b10381d929036991801511500010819000b4201e0b207040c0c502c4a9402030003030310040410000198104080c0d110b44240c2c0c44d1200c204800e40b0f10403814041106a4200018900c1c4051301801900e00e140c01d00d00246004040e4004e110217400c620701c21004484046034058882030301e0007001c0343c1c66031a8900b80c4005011036018a1905040a450450194040d40703d001a64010311000c0e01c040002000c0c95603600200d11030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 165887338 1250 165886088 165886099
    0x102122202011d03010203250e1c0302070806010807081501080d1d030307050c090a0b010804060c1403010b0d0614010504051c06090b42030c040e010903090b0702 71
    0x4600c01584a03150018070040e1074000e400000451001003422a001100c041001400058110901443d070300310901601d010791070a01003c6034040d010403d000b4142c0f12001c10030600020603c03c00d0b000744004e034003174071020049a0035580e48261980c1e41d10440c1c8035191650040e0002d09810085d46801141a11a00c90040c1405512a20202c4500700131b050341290b107030b500303010b109101e40e01400148141d44c0680000d1900031400750803c161441d024040001103480e094040c002643c000103560b41c03203601f0110000d00c2c815580c60940382d90f1002d07017185022210000001c10525882c41c00b078924500031060410600381c44081b1000d080b02d03d044054045541800100606d140401620582c080d0b40f91400c02c400c03c4681c0c17600e080e00d0000b002200e050034001c1c1000302102d44540203c01d0700000140030204a040e4200011001c0c1c0c40b01000500c1104030240c90000e905d0800c204044031001410401c42610040c44140c002c0446d10000c80c0006c4003240005a07064402003540d030244c0d0000c20 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 165888588 1250 165887338 165887401
    0x106030c151701080c041d06011715040c1e0b04051210110912011112090a020d0804060314090d180e01030f0204051305071a0408010608010212 63
    0x18600940180c03891400104a15080c0c800145801c000582d802018100001d0041c03013088402c100540d0000084284181115540480d05560001c0d007541128030018a100d000360000c403010307003000d1006900c1106820420300380801c0001c11050f0601322000c0140b0310319400f01d021004445074005114004424006210900451922240702910707a02150200c5180007003000b8034209442d940a40c4904070007003c02c01c031040f401c11a0f070784072501c0e0350303100200480351400d14015200c0c05140c0c50002d01c1100302001441c548000c210024507140c0050401007200d0301e03842d040e00d80d07602034043d01d40068200002c0c01000000102000d0080e030070000502200c01e04004211019907400031030b101304051072480069002c44c860302040c080d5020350102d0428805a0040c801a11009000011000100080c2ca40854804150300d4190b03040084c1240b007510041d05102c0c014080c030f800844403546450000200528158024203181e00b4000325032a00381d0311541014840c05808840710180c440d2942c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 165889838 1250 165888588 165888599
    0x4030c020f0607060e0703030315061209140f100b0a06020c1003060b03070306060311041409060f040f02120106020706020d1101060b0a080402150c0309130b0612180106030c 76
    0x8074a0380030041e0140c01103081011648501003501c07004d446060311a0800707042031091542c94020402c41a515101131074a26240040048c103c50582c0d0300c560b0341e02c2d40c2c0c50f1303244200302c51400d144068000c1a01100c100702c03440c40c221900c820222034410320b03031440e06050b64050b0805260460442c1c68a4025000000c0c0d603030144101c0e8030541c08604201607844401003079000f008400703035014418940d030001d00756080c4a4003504070b540001d0741903000d0200b0f00c010070002d02e40b140c0f4024400030544c0c0d41601e6407a240c002c204e0400590307030b9580d8414103001001d22050001c0d03010342a40310600100e00d1499903520400d07238550b0a14080c180040e0085a02004600e000b0400c4201c8041d81500000d980340d034520703001c0500c2d00300540031400100c071202030100b5850f0001000303648107400c4800c1031610781503107940380d42ca1044182c2103000750340700050b905811115912207034038200003070b00d01c0b1741d00c1100f80d0359130104000480d50600580c2c43c03648040700201c8140310b008103032640f10a008004a0810 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 165891088 1250 165889838 165889849
    0x30f0b04110f1c061e290a020c0a060e0301050a050c070305130806072d0516020a0b040902070b070c0201170c0904090b160201020906040e070c080712080a0504030c02 73
    0x90a003e4003080f01c0d4000b01c4001155841244000d0040741899268001c1d02680c0c41d8411046500c1842100c8107510100590743c00020302001c021400c404007940d0303440001c0e080c0e00b0820074001c61540004190000241c0030340026144030090800c500170031690743c8290220046400540310134568460520060000a008600402d4070b14090b950003401c07940d44003d41840c15000302c0c0e03020300207020f1180001118800c4d15034402c0d0300142c298916107021032a4070040081c051401e00c07100d5400c01c2ca0407070041d034845844060150880d20741140d519a204c00001029600211040390140c92500018990358455003410000f9503050b941c0340340b5039850901112040002038104206007000300304e081e00341d40d0b4521580b51020300c1090592541e01e0b240240f03181840131003500ca03040d6401007040c8440c0b5560324040f03d0030f540011050411640b165039080700d0407d100381c4020f1007001d0000e404000d00c1518605c080806c00d040d91000c5099913401501740540e54181c6004002c2043c01ca000001443d00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 165892338 1250 165891088 165891097
    0xc0306060906040306020703030f06050d17030c0d02040f03052503060504110303031305070f05010c060e070b04031406010501050705100902011829030108070605030c120403030f0b04110f 82
    0x5042d6400e194490f1680c001726417004c2e104901003aa00c04201e14174842038000c03900200703004c84441202c107102d6254030400d552004500c0600040c0000051442500b41c803d94510b8060340304219141ea40307480c5046c900c42d130f060000350b45a02c2a680701c41001e280094442d00c0622140401040b5540381d40d440002618004d48200c2d0440001d00c004c004076101000503501c1502203000030700a1034014104242418980c0d0080f0400500c100424011660000c285122840d4403e17000509910440f1105081c003e940e004003040c4080060300005003c00800c4004110003d5000d071400c507603840c801540c0a01c24094020b01541200c01d100300d001e0129806400003030b006040145003105043c7c0c0c4505410095040640c0e481c010591301601c0c1c43c440105405c04500144e442442c44d41000754060ba100010322030b00040000020010b100b03110144142c0300d40c10007240c40d58080c1d040c540f6024014200d91800002e00c145444404091454a8080c2e15034ac0229000d0040c5040035206d0207160301d80c007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 165893588 1250 165892338 165892357
    0x70909060906020a0806040b0625060b03030309030a0f0305060d02100e0a08011e1a0d15090605192007020a0e011d090303100b030a090515070e0402030c030606 70
    0x7030760054600407407100e0000b0511071400e59290030071413828408000c01c840c3c2003480103018400c1440b40404c005a144000041104002842000c01c00300e4a484001b5000040301c558043c000881802001d0700000302810b01e42c1c002e030326540070f8942d00303502c07c41c1103910454001e540240764100f15000750600c500c401104a50610b0500c0a440d8072034003080700304031950701c401005e0303558030608510054400304a881c0015400400d002e894040c0d040c0342c003110f44200006214100c000c4a402c10007115511400b0701e508540e0303040c0320a806504101008280882c0c05d044400088840850005046d101d00f2450466058403002d1201070000072005a40100204a0b0810199030340801c0f002c00d8108500c0c020803180b40c5401c03c0e00782d0002151560706001c0e08190580e0700c2803061014007d802100c42c800c0c1c91074096000c0c0c5030b90b90701902101504142d0f0002e4524017440d44c00889000329040d806114a0344c0b0345528107013080b508144000c81c03104507140d41040e04180082545468804000c002246 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 165894838 1250 165893588 165893591
    0xf060405150c09120115030309060e010c020901140105070f05030a09060c0201020d030203060103020d0e0304030c1a0a0e0d140c0306010f030c050d1407090506090f0403081b0c010c050c160807090906 87
    0xb11031406c4554000d0301c0303400641c04100c45400170481c2560100c2030ba5007448082c41c1040407242c1c070340c4c00310f02518418000c000c800c0705400c103016082d0740701d00c1c1514404da4104005000000315414695241d0b441039a494000514440021407440d0052858004190307040e4024260300b0540d26003100290406003540741007540800200e0f0042b11240a001c1c48851038401460390f542c41c52a00c4407100030f096020380c50f0505250754403484c104000064030302520040c2851200c410380480013801c450b002200082c117943c0e04c4259034001401c005107540c0c210038294110303411642c1f42ca0704010b8003500c40c0300081c00001020424001403e105042c1c0f8050b920404d20030400c074035000c1300380d0304214454000c4030710241e40da4100401031810030509600b2000c1000c502031182000d1710001d100c404010721085079200903840846507a56205c0c00c54100c820b620001700540c0034603910091940e030006110062910809000070316003009403a810b1f04840140707006044040c58a9182d40162004403020784046 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 165896088 1250 165894838 165894851
    0x21c051603480f0602011506020105100312170a02071109150d02150a02030a18050a0302101101020a030e12031315020c01020d0207050f1507031d0f060405150c091201 73
    0x54000303d240003901c02d5400100e200b1202070003840e580b45443e4408011a0306100600c11b842d521008000140d03034104622b12070701041c08400351442452880110310303100b0020100000e05000d94050464140b242400c0100801e4480802c4001c0c1c0b02070714040e1008031840c051212a241c410034041420f071002d1b1041e00c01030300c906080d5800307400c04589440560030004802e11000e600c0b4003101920a03924803803205241c2481c02044031504c043c00002c3c00f601203a17041048aa0248000c00b1400c10004000d540d500b840080c01006002c4607059a0614461150082a000c5008050780e10405116510000c00d03001d90b01c0710300d48074140404804003507908203c5544405802e000402c46415040b4000da43c030321580c5041d41c034050b000608607403190081c148505100c0c00314008140c0000ca58500854410461814014000351948094507948103003440402c2d250f00c04112544224042d0041d10311503003080040e84001c040484895101300d004221f030150300d141450241c1031051808000080702c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 165897338 1250 165896088 165896099
    0x181e0d03110604030e03070e0c0301090507031b11150915040f0c29190f090801020d06140907091a0702030d0801031518021c05160348 59
    0x8261003643c082d80022640d01e42c02205080030881c0380010700305604440540d01d0300c00501c03403050206000d9008802d80341d60205801ca4440e80180c0780034250f044c1070300c2c0100211031020b0700884010009058501031b699403002c407441c05400030f03807080705600c000c2d0200780c504c7c07040024a5a00144112600034070000e02d200030030034014060700904601e0100c00041640320320702e584010121251711050000400826130910410810031120030240e081c99034040440c03101c242c0b501c4d640c0d500002a20361000c15103000d0905250840411643c4d40e0403540704108030b40f07040c8a80000200c0d4070202040c501c0c0717403c20039160110300b0f000301c41c01911152030422285500080c1444107805010000604140050041c0100c0c014000030402140e801000209881c1d0150139000c900d480f400b0b48a02024081c1d007107007851104803206620360101c1652856180c0440390043c202c0d031400161401800111076040781c4403050600b400480d00e48000c001c55410303507003400f2080c2030140d442400c030403800c4d28000b0342d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 165898588 1250 165897338 165897343
    0x90115300501050402010210020702060a0c0c050d110406050d030f120f0f090201020c03070515030a0f0e07031101030b06030c070c0306060b0a0315030206090904030216030305181e0d0311 82
    0x8840c841c40011805042c40e000092500384a2900d85a110344104586001655000c1c1114030544050078000d0102105003400c10501102d6070082d500030030001141020006040300c041780c01a0115420001d2030f48030814014540c880714401000f00b10440e580d8030159002e56410300e1010000407010900c0481c03048d1744425940e09012460005489080c03040031036030144200c0405100640c002d101030b601e0400080d10742c04000300032615091001001c01c12542040d0050f0085529040c428000d20010101c0a91f03219524442695140c00d00e41801d20b50358424054107003500c0d0002c015074110384a88140d5495984002c0301224002c800540002c00100d40d4099100240440381e10303030752a0388100c1000340645035148034100082c04504814401079130380605480d400041503e10404c40d544070b00d01680741402c11041000c0000c1e0ba00c00c0001015845001029003111020b03149140c0703004101030000b10100b0b400b5491510404111000c07490a0421505801a00914188989803c80d001c2c050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 165899838 1250 165898588 165898679
    0x4170c100c0b0a05090d0323070c030f050703020c0603060303130f050a050f03120f160c0f0605090a03030e150f0408060606120703090303110c010e06090115 69
    0x100420254003080e8248038100ba03400f070f032215251505001a00d415a8070030b440350000e281c02401d240d0b07502c0419202840c000b085c803208048502034042c417230074100c03005404100b1901c412000100c0c83c4e800010804d00c21403e803007650354150000d103500d010990400c40316410061080390103100038854201c445090741d09100041c002003c03043c0c905400c1c4000d004807002150482c1c7e00417454091503216549000405142c0541c5110307240e504d45103a0419040385210758110816800214002031003800054189001286e81c03214151007103d035076280035192030003565074040d07100009070340400105c2d000d0400401002e00050640c1c0d580620070304c2c24034850f0400b1070003800c0e41c0300102c1d060001e100d00704600340c9c024004585081c00c14142034506101074a0003810103007016100c010305d204250282c0c024405800c01004881d445410b1640a9402081c4503c210440c0d4800ca0010492041041c4070350040807003c200504142c0741045940c084924810b248003003000780c4280740c01211402003a040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 165901088 1250 165899838 165899869
    0x112082b1b030609090f0b1e070f1b0b061003020d022206020c03030d1e0f050a050a15060c150c09090605010521041703090106091d0304170c 62
    0x31408151440d0303000b011140c05401c1040c60320701e400491808201c605000010f1250300c0b110030f941c1c070740d6003900b9151503030316400c41d494040000c9420701c011640c005013a00c0015442e0341da00208d0030f40b616124056a010750802624404110000c00c901d4142460070010451440c28050703c0c1c0021000000204d0340035207407000030b01c9100e911046040740142c111100504086c801440b480f107009001030344a210320400050229078500340d541c00603150500b49072840c1c03180030040001d00842c440c0c00026100c01c8031010ba545117400000352803d0914450703011f0002c03d45c0609000700d414100d080e40c15a0001c0c2007036030358450100003a0071144481c05003d03000c0040c1da072829610741c33400e6505010788039240c002d5814007205006189185c062464241090460200780284c0d41d101d90401004000310001c240e000b00c0000000c00241910540088049580b640d0301000b203100b4408201910f200c3d4815681800e0700100002c0100ca4a8003518008200d4504140d0300b200c0c10780c1c8d0010303480c0030f600c5810 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 165902338 1250 165901088 165901121
    0x70801090308090304140613030209041a0901050c16020a030b04081902010c14090d0f0c05030705010305010b0702040504031103041e1707060302030c0405130209090112082b 76
    0x3a403040580c050805904003420a0055003468141940402482e0501860700d0252401107840c006910000e40320380000c58020340381c64054109410829618050700d456100c592021001040c440c91051140d40d100d1504110100c3c1060300780003100031100c55841d0240c0e8800d00842c80803000c60f42d64044140113610803402c0da07540c1e008081c000200072035000007800075a49072002841d04a42c100f1040084103a50014140c1e80b501c04800164440211500250081c80d41900d10700800411019890649a0403822550000d07501e00046080d0345c001d0081d5503e0031400d00000c0010304054219940043c442c0c10002640d56601e40c10b6841c580140d03020130891540420030750704a01c0343c048410f0141c200c500207401030000e030008190f40c0742c000e4402d0400b015030000001d23a221090509840180c2070041c0b1a4595200d03040c3d080021f50010115203125400610000981c01700810582e4201603010456601785569014101e901e400c03a0201e01076038046505040700100a40e00c1742c4102c20500408 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 165903588 1250 165902338 165902351
    0x60c0706141b0f0607020601030b0f1801020a090f050f0114070203150421030b1c03020c0415030516061b030306180c021e1b060c07030c09050f010f0e0414070801 71
    0x1d284e00d001e40207800300065401c150014800306541007542030340110328011a52440d10b0320030b259030f440c4c40f010442c040325520200c0c0403419a40d00055402c11616004409000c1075200c10400000000d55aa840c1c04071740c0e110030305110710340013a024080c0c070b500040641d000b15915500301d03070600710b040300d08440000c625555000c0da007a050741c100c0d20080161600b081000700d8240400c010030400c140c0f05443c0e1290744a503000301442000100c850b40000341007070000f1840c4a1100b1004c0c8400d00044030140242c44609210041817402c240840d0219a02d40c1580c001d00700705203e031480c9600050b41015110a40804c4001e8003070312003001060180c20029086040d0000241000d800401000340b9500c01a0030403040c110004014850981242019041c000107400007421b0b440303400708005440c09004400400e20260052030030895134054014070031359070741664100000c0f400340203110904110b040148041003400f0303841640300d8480e4240c540750841410503549851200d61221185a46508 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 165904838 1250 165903588 165903613
    0xc0702180714180f0a031707020a08010b0132031005040e01050c220f08031e0f07080c01090204050103120f170402040b0d0b070f0905060c0706141b 65
    0x2802280d0907008520a2818990115541c0d90030882e1443c0881c490045401e0102c0c1d60b9540030071400086074030000c1004180b0a000d40c413981c80d003002c0d8069108840d08640080d680006000d0a5007241d0140d482030015100300c1009064100600080341c014404140070000042c20540210b000d950181d40052489280030304000680340000341844542e410007050000208000c01611490401030342c0c0c2044100401d004506002c09aa00c40030317a0600c6008001450a000310081103103d1440410040300d1030304010003102031250704c2071503803070500801403507011401e200c0180c45c102038603200200e86080b558000806448082e0003d072031450b09200301a200f9074000c030f2400e004441c20300f800038115560f0380002d0841c41c80200064081c0d512081160050f90350070b46814009a80003510380001d050024004040100e00300800001c5000640003013070614249058400c540350342401440801d00340502283c008c82c0121203550781c02002e20000048040c4414640300a0018200030b00740d103640070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 165906088 1250 165904838 165904847
    0x9100813060e1e03130b0306040b04060b09090f0408040605070c2408070c0308040609021c05030703081b0d3206090609060901030b1902041d0f010612050c07021807 72
    0x30041940640d004112505480280003501c1c42161008000c2a0b00c035518440490064250360482b150310501c0c210f8040341010286001e8080c454040e1075240742e9030fa8040500f400c80b8019240905920f0b8107000411260744202c000b409014031402d0b50078407803135807040340e02c01d6040e0400c01c4649450140d40811040381c0e1185107594080403c1c40c100c004400c840d10007400c00b8130050000740025031520301a80c203540b07941000917555048500011510103071420607503240d401100003180026001004540307a041c02c0050751880090800e801443c0070840c0c5083c0000300800110070b4101d03080343c650720f83d41003002540082d10181548144805140100821082040003002103118a00f07100602195807610341001d0306595025040c0e9040341c98541c81c10085a02c0711249003421800002c0208440c40040c214203502d10070184520129107680c040c00400e90707400d0081e58001800d203400950742c0300c2250071045d00003071072480c0070b89042902e1300402e405880c0005100024a010028040543d610 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 165907338 1250 165906088 165906133
    0x140a020a06020d021b010c11040209030a0b10060c02060a0f09080d0201021309050c161a040c03020108070201050c03060f0112050a020a020601090b03030901031a0d05061b09100813060e 81
    0x4200540c50840174000000e880140c86030b00103040a086101c1901980d2035950403103800e24030040884620f9003891400001520084030035046001c0341d058005542d81c0100c0795200c8040d40101040e0410000841c12100c00c0f48100c801000c01c0701103500040d1a100601081c0c0400100354000740e41c45000715142ca2051340c2943c4003182c06442d1004002030240024190780d41d0a0700c030210300200a2041c1807001c40e40030710075540710948203114280020806150b140720308a91007a00c030070007603540700901607080300d000b1112001034901c108001412890140c0810070031440504200350648800e81c1c140040720411603d20000660000310070b500c1a030101b0005005005944060244070360040100380c8a0044901082c141901d90b10310060310082502c2502c401000034040c881ca000d41410326940e04c00c01031b1400da402051030070385000d010381408100c40c501180a012030081d10441c0400b00c840d5007006103880400da0300c075035404d400200e560103131a041c1c0070381c0c030002c0c40f1a05508100100010a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 165908588 1250 165907338 165907363
    0x207120203031e0603120c0f07060207091a15090103060e0f07020105010e040c15050c010f060302040f0204081509011d060103210806090606130e010306050a020307020703140a020a06020d02 83
    0x1503108104d80f40c2d40014030710751680444050365480b0514180c03011300d00f10b80c0c401c0c20b54990240c2040491120b85c0003881d8011500d01c0740c014406045441940208020f600e0301044e00480c21504c07482c2c548910000078821440180350020780c03584d50f4580807210200641d09c1d10600050721081c051141c0d03090180306d0140c00e40c1c0c03506680d0303420143d03a10007900300a803103030b143c11a488400d05d0350304a00410a81e89070300441c200074801600d02d0a8000024040c3d800128421403504450b00100f0441c4c0c82a05c06a83c4400001c100007000100900ea14102c02130160585640f100c0340030042c078400c0911420000b80300300c020007580d4150300c0c040c1c0d00805410403602d1500080801c10708402e910520054020900f42c0c0c10034140d03150b0201143c2d56214201071207804001c03080c800120324222014150481e4040e190801c01a15030204101c02da10007550018010380c0041018008291051040d048629507042120410820b0358003107520221598040320240c1c0241c00e126078107580510035401a00c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 165909838 1250 165908588 165908641
    0x370f051309140903163002010212010801020f0a1d04321302210708030406030b15070312060302100c0605061002250e010b070c090e070b0904020712020303 68
    0x30361101031043c8000005051900301000e80044024801070718a04564081d144109442500c04082c8c003030740c001844004003480841c000a4120010710aa4402e50074952808c0e241945120301121124030281107889014413200e1500b00c07070b554501c02c41e9071a074411030300001040489103a50007050000c0d0215800b03445407000b0066403018440b060342c1c03440c3d4115a004240583c0b243d6801e403610481b01c3d401914800c914010410060000240048804654040c0208822031050084040a0940e0020881d400740801c00c0000c0c0101ca41d07040103225007600040b4960b49030006020b100c03101d10041f010417185041181401100d00445138001c070f098610b4543c2003481000250f03a10401c1420202e0f280303018001d1520b107450009900002c0c0740c030f42a001c03960350f1106003200a0398000501240c1e41100c0c41000203604816014100c5403c002a001d04151480d0203402e226607800703040880d911135400c02113080001d400d0102001a0b400c140e0045407030b45042200d5a00180a5141012001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 165911088 1250 165909838 165909847
    0x31f080a080403080a0e100909060503120406200d05040914190c14030a0b030f0609030a050304020a05120705010e030a02030c100302070c0605370f051309140903 71
    0x3046074040b181121352101d11150f444050200c2141c6c038200030b081c2d40794000b8408440700c2d803c552041112042e030f0008901000f0b0340361358204055484a9804000c090000d080c081007150b02c3c0184240e074a00d10300740c80d842c0c021340e0941d00014101407203664000d000c039201107000c0c4000741c414821160002d8003490b41c41c5d46803c00001c071a05079910741d400c5030002a1102007c05809108241110030b0a8003042899204d0908014040280410301210f03800317845010045001c001c5c0000d2900d01034170161780510302c4c1480b8411304031540d0f80014416031b040b0103803080010b040c1d107482b4512518004400301408019040100041ca03201401407803910980c48906000c01607503002c90b1301c050350307241120354180001c002d460907006401000b0780601010b1a5a00000d03582d6001070041030364446202e21083c0d01e03644c010031010406403c40d41d1800d1502c1000304c008403203005448403201d100307282c20880d0820039100f00c802e60050584e00503509454507084000c0c959440c0300c0b50143c100005a0156082 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 165912338 1250 165911088 165911093
    0x403030f0e0406050d020f1504030f05010b0d0b01140a03020607050c030d09081504021305181005010e0621031803100207031b080c0a0b07120902091603020c03031f080a 74
    0x7805a05d007400b034032400182040c9400381c0e558a4290002909481c01140c42d0f603070700d0811030341c500300c07108068805500702904070006141508a01140e1a03012204080907402d05803000a0182241202500203107054000700150b0350f40c001400f403203482140181961071828040c1401c0c034009503101400d00c9903001061041d030a0200390511100ea85080e0000340f55100d00004901c1401000821225880d02c001e000785c020500303035030040c210882c4084030400e50500800c0c4080350024410010704580c62000f1078044e00d01020014404403c412070341d013417106411425415a40446464000c00310503224050b0542070a00c0303424020130200c0c000314140603a9883c0070345100721030701007198408460340ca80c20400c4038a1054411200c018021101140640d141c03450015009644031400b1805030480d0b252800c010740070b0800013680c003a080c1e150a80700d080036041280c0590703050005058090240c106903400c10405984506144100300b020b0701c50440e00d030a10b28202d0b0b04400c0882d0405520b1401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 165913588 1250 165912338 165912349
    0xf11030a0c140301230402090c030105100c0f050d08060f09010e010608060105040801020c01140f070c0311030d180201080c031302060f0412060920010215060d080403030f0e040605 79
    0x201d450041c202c0502c1072040000134010b00901111001c115050003210255070445090948035501c26a03180e00d0300d89034400c03504000c0c0403d1041d26070012800c0c003460302582c461070412800300c1c4078060050000c06580d480d03d04042c5411108000101620304102c107a00c1c0160056001031030a032881030140d41050b403925000381050180da0180041c83d004030352164401c00c110b4008003041002103480d26041200f680c064070202490311000710f03c59000c106c1400030582c0301070150b615515074101d031810a94040e01c00a20a0060804a02043c4000040b2103514040e0825a49000d011110f0284080c800500001c002030046e003130071001401000760045054a00081d01501115141d07210134886140c803045e40300d50740001300c8120200b0b05000401c00c203604041000c80c0f0032955100d494070448041414298000300d400c0c0181c0c018000c003213070002da030510f4941000014000c0308401c61241ca62501641c004d52045000401100d101902e21398491002e10b0050300440741400783e01e151030b000a4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 165914838 1250 165913588 165913613
    0x71401020c0d1e0b0105040501090c080a0f020f0c070e16091403010f0e0f070506090a0501200607020312010e0f071805100f02060606090d080d0b04090f11030a 70
    0x602603969244030b8024030200390050300084801d07030701c9107121400c0d501c1d203040d03801020310585000d1810500082419465401a4111061a43d440000030742d00c90070b00f000a40f00e45030312042d01c076500b0000c1003001d0b104d110040541043c0c0e08000c0003d2841c001f2400c181c081c000b00000c040c080310310412000b065004045500b22441e01d0b091a04a80000d000240107080001e8402d1940c0d02e4241e0100f004200170cd0281d000c0d90300c6209481200355030303205000141c07141038411175012400200c1881a90302034800003c0c001d0389800824443c1151004462030900180c54000240e4000701e407843c0c420b0b000201035405080c4010782e10b00c9908003003088107d052000b030181801c0c0581c41c044003d0142800003404010417004081e6a410030340b0f044080c2c400c0c4840b400c148018000c00c000103d41d401c00004449a8000150a428502c0342d0f603256046150480b2620f40380450300c07407100380e07019503e038001d81103000c0c000c0d04c401442c0c02c8a8540511428648000341d4000e17040001c030f04020880058020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 165916088 1250 165914838 165914863
    0x6060604030b010e22200315010b0a03060b0703180f031502090d05060c03070201060f0b160f051510150804060507140d020a2d030c171807140102 64
    0x98a00d03440c1e0560003404603a00e02d9a050300c88410f17a09540c04e1000c941054012054208000b0f490b0741146030505071600010703400201c03544110380c010481e03803090034001c001d03141daa031030700099540d01c031100b002183d4000d040039000500d00d41000b950b4204610f56078001440080540440503207903540d248000c1d42c00c0002d0740d010b6503001c1903119060f11901c074001d80310365002003a903403189000d142544040c1c00c02d5441100540ca041800700e00b00001c5108176080c2d608034014036007001040c002000780d41140381001c9440e41601805000011020488cd030314031641780002450302d02d080d00b06400744c1e24030355010aa920492a01d0b4424050700018085c2c0c206400c0307507001c01c141e40c9031402503488210108a00c8036914001815a5000d0201d40c050000d4002c10f0741c81c4451241040d4601c120b0066a0400c0a040c064000c888640d55011b94411403200646003000105240c0316840a12400d904035004800c4204a519042001100b884010090044800711194108503080000d59800c0d090b0f02c903 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 165917338 1250 165916088 165916109
    0x6030203040606150c03080c1614070b0a03020306030d0c030c02010c082104020a05030a170a02160305150a0213051504050916020c010206010506070b15150c06060604030b01 76
    0x85018000c043d040003000d031455000900744035000c0540203018000c0030b038040d400100035030040b8014441c1e5200700e8401e00078480d0380390306010441c1c90380d501c10301d00780e18162124403d440c000555030790303084050011710105840040c0c480c50050141801c0c40c0700c84003042d00b0800401c0e000c80019400508e620081038081c64641501c403403900d0503a0380d600c220300b030782c0c9144420400d0240011000c4a00144180c0c0300b52460041e42c2d07517a03000d05956015800c801801c04240701c0c3d406c40752000c1d540207003062812500c12161807034260036030300030b00750002c1d0400e9406410000001500c4d03c1000700c0e880d00002d0a070400c41c50442c40c0301740c0f81c204a0450043c5403140b84000f004820b00740d0030100751005404014603044460609141071b80740c0c6130340300e40c14002500412000d206558004603849040f200c000d0081840c20721166104014220018051301f20358101c28202d941c203407101700c0c4110043c0d00b08101c1c0303070b59140e05c3c0f82c0007031070070800811051141000300014000240b41505050449001203070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 165918588 1250 165917338 165917341
    0x50301090f09021905040e070617101d0105011e0206060d03050c25080625110d02030315030309181306020f0d050105100215090a0510050f010b0c060106030203 70
    0x91500a000c801001a60040145851040b013110592000c030460744125401c00104c0c901240103501c0d8407041c414070005c03031070307080d152414580c122500320340c031007118059400119118600c80f520303412149040d616001621005102c0355800141d50924103903803041da5404030002c40c40095440d240204018022410f0302104810103025400b516030141d40b41095810203201d0f0408501d160f0380804141c4220004050b0000302c03144041000ca001c0e05003003046801e07504241c010003448401c4001e40790204400b1a81d12040c3c60420301c141114944640e010b169039042c100b14101012002c0044c20b4480d401c20442405a82c4d61030703000c05c1144074000c400c01c6481c1d8915001030490194628060603460002400a104400030002000041c582036810401ca03606c920500040d0f42c9110544005030380980294041364030402c500550041c0101c0488024030019910242019221040b46070300d41d41720700c14825080a80356265000d8100c014206007420381d0a18041c1d035400041c0301e89002c0c581d0000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 165919838 1250 165918588 165918611
    0xf0302040c0305090a24020c1015030c0303081008010c0804020a090b01020c0909030c070801060504060609050f09060307050303070804080f1207080a1b1505100b04090b060c0d08040c0b070305030109 87
    0x200f2158240c03050360001c6403a12141c2000c0c4d600c4142e0382710100201807400203041410042c1e680000c0035250044000030007a03003181c0c1e007030341c24440260007001301c80a50b010015a1060034020303600300003200d0342c5050150505d03106020f21154650040c10307069040030710129007030764006031400300c100d0308548421039900d403007006600b54454007100f02c01901030444c002c10710b408150480811240d05580070003085580b01800c84440005009495204e0038100d0717464203174545500c0c0140c0141008050782d010640e580700181c55030303002003802c40e440d007404101041514414420848140d100d400904006916948858800d01c90490010981c040c04104000503610900403040d207c030300312040c400c0c1e492940c00d10599801003640090581c5082c00001040070b0104503810040300c810041c041c0c1418200203840015117419800ba6821080900075110886030070415005010a6a01c82103100e0516080003606224942c0108900c10720421040000079840b81c1101c0c1152560540010f007880030780d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 165921088 1250 165919838 165919883
    0x504020402090315040b0f070c080705070e130b0604090807020105071106160501240504020c03070b04060e100c09210203120307030c020a120507020d0c0f0302040c0305090a 76
    0x740d6655010b120b02000c1040e00c0c2d02a808042c0114011b40c403018090f0b442000f00c0b81941c0c03003110003400040ca41d851180026010300e018202d11031180046c0d03504140c451005134001380c400c0b07698108240031034549400707000000d03a000d5009002a2020310068101d0b031503a008910aa5500904110b00040c4600500c5014006900101c00c010040340c0e0302c44000e110080e01e281d8a0009803015468213a1420040d0b054083c03005000c440040c903290020f280204000003508405016599800304108000004102860442c440c1e0300c00c3c4da002500560148041d03180c0401040540c04091900749422807094000e18020f003150740c0e10f01c44605e10b0003803a02010b04a20400002900f40c807850f2400c40108921401031881454596420410300e804a407081780d6900b000400a0000703c651003200c407800c0d2151004084442c005000c01002c2200c90f030b6076545860503076008210b1441941ca00344110301d07050040c5000202281350501c400d040c01c8134690385500c10410014100540c0d42c00c484c0852056 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 165922338 1250 165921088 165921097
    0x3040206031803030a0506040605040905062707030f0303060821030a0e0115050906030a02060409020c070302060a05120703020301031a061f02010510090624030908030925180504020402 81
    0xe140999881c1e0802d0b40c05c100c050402503400e64800e50500b800880c050070544a02040f00381c1050040080307450b40ea032080c4406104541c802e0701c0019182c609800310741d0400c4004021031181e0803600a00c4654100202150159007000c016900030103401d458031a08120203400d40900303a21620380d00d841c2e40785000c0003030901500d180c10a5091000c2928041040000c0a088401c15035840714036544074401c058580ca08030400950024003400103114407051a8040e10200104504860010361030ba000910550000000140080c000050600d004021030240c0d07508810203040640c21035046070386940040d81d49a5140c20b12107140c40008031103a40c1c20740c0340140c0030300040b5036601c0c1462105000740605421240c5084800c051400066030010510885080f00d0100c9180d126030112440c9203002c0c10a0101414105038589c50800d0110781c9840040d030090694200030003d40c0108101d1210303a0214000700305014004075410030040043c69030b08030081c80d100300001082c0d40d031880024024000e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 165923588 1250 165922338 165922381
    0xe06040909030804020321070b131407090608030a090b031b030a0c0908060c03010303200d0905030c042703090b04091d0102091804210203130603050c0304020603 71
    0x18101107006043d008064280180c1c001c0e801c0c1c81204010744540006d402d5003a41c58605908100000e0011504010500d40c0014604940400c1c524a42c0c0b02c0400c1104030768189040740c1c111072000c0140800500c241c00040403c14051810403914800140420b452403160350254500000043c00c44690b140107200c00d04083c2c60765645030b00742032805000416421900d000404e000c1603000c0b0321107000048403441001e19a910324616802c41e03800700c2c2c00700202c81015041103111071007041805003d10444480c170050341e45001001b4a004101890809000e4001e4040d9181c0130703191694500c200d0ba00030500c04460110b000e40d06461608071031015066114001848022030042a0111240c202c404004100750443c15010b03400000c40d8200d10a1240d12940628410030002150f0100300c4405d6100d40074190382d0201d4500982d880325088031900c00c48005800019012000111480c0e07003201070304052500300810329241350205110720010348041c3c40703503601200107210401500845e480c3c501e03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 165924838 1250 165923588 165923591
    0x40503120415060b030112170f120402100c020109062307110103111603080406180b010f08070e1503010e07090c030b060f0306210d09080d030510060e060409 69
    0x1d01410080300c010a25040901054240100094400c46850641e81030b50f05055080440011603500c031406102d036100201c03000c0d00140501454849020040c042030000b0203243c01251919104100400390502014418014909103003005030742c1c003041d1101560400c0c1000703444042181d885418400041070403941d08400050313500d040101c1c040c2400c1690f0800c3c1c80510000e03184060600c40c6010b03860441d0150340c5280b0300507004c6031041000d03a8102e800740c0c20000c3e6070b0804003102c2e610340c84824426600280c0c01e100401a40c11808003200c010503407100540900e50400f80715400110000d0201140d16015030014443e40d07030298070501e003018003801155911503540c80240081d00340e0302119008a0714002c1a801c541c200311085031710404c0a04a1b51b860340ea105400c009a9142c0d2242c2c1140c0145503404110300304104004554004406444501c002031610780014940410040340204050800080c00101d482c003464a40503036045042215020644101040c000c1c0507980c00502d225 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 165926088 1250 165924838 165924841
    0x10623010f020715120b040513080306010507020406080d0e01020c13050c04050901060215010909020904061a0a0f090b120a0f170a09081515010e0a330201050402030c040504050312 79
    0x2542001d8500b1710388284100a1254420510800c0101d420444010072071102070340d039090008000e80700940d88014141000c3e824030351943c02260031241c19401801c42680705500342607803940c11206888142e01e091004040303811101c1d0225562415101030740c1e00d615250710220b8080e642004c2036401401340074000064940e95000f00950701d50360780c0024542803032094004070310b420250050180c025000303890803619440340e42c6d070000141840200300f140042c5c281006034607a601c0f186104018000e49002002150500c082502101c0c0b103c10300b1441181c00045000c0034010226941042a40016841c1c03428030040c10411240c000c855070101400100041824149400411480170b8804202c22100c1c41c07903859a010440c8201070b200003141c10075040c0e12900b158855010f60044001c003409070032030103a07543d9118000b24041c1a0b05402c201c12551001e00c03605503d00140c45060941c40240030130704064021035122000a0605800740b07845000007803e00c28100119880e2109449408019 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 165927338 1250 165926088 165926129
    0x1b07090911090f0403020a03080612010609050105010e0a0e0c0f190306030c120c2601050f0402090f0705040605030414060f01050301050106030b011b0609021908010623010f0207 78
    0x9a0803020000d034455100e02e80401c10500308400241d1140e54160020460b0180030b0f1000d5500e107500510055105424903804000c20303000b0b0081100a12109001040d1941000005020405551103150050074400c60410518030803603103050b000001c0c09a020340e03800c09140b08031307814840c203641c591400005100c01c00070554160b02c030300304580c064551700403416110f110482003210a4103014215000307041d401d1252154030350541b905904c0c01036805a40c004804101c500351001124408028198441040b042d41400003103a9884003460150019078070b42480d001d03000d030050740a4030007008004400502003000590800f901c0c0348a0000b200c402d40b034251a000110b040c00d0248501a5003070a00006a0368001c0c001c103002418147c4503000c409200040e0b8404901e20074600f0360b07002d07403500c25240c0540c850040710482401050720320741000c0d0610b1707109800d4502d15030110f13452901c400d210505e5210604c0c5411504002460082c48051718110100c0c9028215004100d40b4500121031200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 165928588 1250 165927338 165927353
    0x708070807020901061b12051603020f061812071109011203110f0a0206070501110a050a0e010e0d0201030209030f010216030216060804020d03030f0903170906010b1b070909 76
    0x20702a02c00c075000322481c0e80384e0208481c1c40a0400344100007043c42031504c00000c505030b0603401120560716000e410440c1020b51141c9400c0300002c181c0150b04149681c10400070140491070f842001000c01861036000805826030311011141c054080c00000301c2c0308020002d140c00038241d50b0000600045455840d031420b07000d00802400c080f0045503800c060040a1400401d08a903a1101c050180a1003402502441b2155020031401c491079503071030030b90b5050001c0301c0e0041d0501c002c0599825807220909200584005550400b0701c0c10300c03d03015500300b500d41e90f00006c4110f40341c1c286070240e1510b55000100e880c11900004500c01940080b032110755841c41220000c40f040d010360300701d416210b041d00001c5030f081040d0181340300046d110780c002405410040140760b1128800c3c5000a003980c0e1403551442121b081c0007046000a58440826035803610803082d45800c00b02d444041e00855260100e903022901c1a02c00c000d1201408040d0401182800d0091000400c00c000d0306110b00601841c1050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 165929838 1250 165928588 165928597
    0x2070203011a0102100b030606130e011805070608040528020a1e090204050603180f06010b03071715150418020304020415030b07121d010501030c1a18010507080708 72
    0x1e005109001a46040c5001740c01140801d00000d00a09016103504080c451420080040c040700e50303465698a80407403000744240c0085654010700011201414035016081c03000607032110082000310b500b0300010800103d484405005440d50700700784026001e120b0100c403401d2a6002e5403041c5004000a0340301401c202101440b000f24813404203403903c0c1c000b5003040b4007503801a00e030002010b0001541013052400d1b00c41c0410342c0c41080311801039002d81010716003002604040070040b03002c018407019035001401c03068202e010404000f05858504034400d40c0e031814840340d0b403240600e400ba5104c07800309074003254080d14003d072a045001c450311038408043d40c000e4408900942c5800b00b802203071105a500302c07080c1c962001d060714071902c03001380490320343d0100405014580d648910300c020300e88400306500003880090b00042019850760401c1c800305080755000890070604014548642c51548084510f2400c8181e1a2100001ca400040354603014110004010003400110082407040000103007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 165931088 1250 165929838 165929891
    0x411011d1e010305010b0a080f0c04051002031e040806042a1212020c0102100902041b03050402010201060f0501140c01060b03130510060e01090506010309050615040605092502010207020301 83
    0x10701c060790381c038140e0303010a201d095100800282c2a401041c52700221072440e6821056007115182800d45500005910004a04100f03000d83e00002d80805c82200a0310411100421845007a080c44c0c5071408040d250780000303000610141202c4d0002e0485000b80303510554002d802030082401039202da000e1006400540c03800c0e00c0343d0016903946d400d80340c400140c6600d42c04044c0d001d0100b2034035004002010303207042e44003240d00c1070322034220003048210242c03000c881400300c0c1c1d4041014202400060700311f5100d9084104a24a8614188226600808000348014042036040d944440002d02c4c94014403103500140c604590000c00d102c01c801509030050b0701540914243c0d407091280c0c82242c03040781c6da144034000401c1542c41c010041c0b00060703485198040418100400c8140c002d640b040d0501c007045403503640c10022003e40b4800307410070740700308005004292201c60305401c00e00c0180c222641e140c1400606116804c04213541c00e4404c1d01510380c50b1340d000d00203101089480701907004d03060707031401d16 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 165932338 1250 165931088 165931091
    0xf0c0c0506090307210c0206030c0406180302030c060a170705130905010e0103060b180a051512030f0c07121a070807090302100311040f0501170411011d1e0103 70
    0x2c5802ca900120480b901241e1044107681c0c600e550307200d044c03249540c0d4000d540c00c0c4081c4411b0400503880b40d070010351058000f8000320f0394407400c100c005010141500b58600b000f402c1c1c1141400140c4000a450760708090071148141c440186440461350300c1719262542071491451414040c0302d80d0868007030003000c0500c204880620352600200300464074240310364040c0401302c0b001000440c019505c140c00407040605040103a0006062110300a0000e4544c4110ba590780c1c420000000c2c07120440c0c1c4d04c1c1c0581112003400004c041c0041d2540d82c000d190085c005000001155008000b0030407400c8011316070504880604074441c10a80c0c13880c40e0f000d4202038031242100014030058400c0d01007601c107202a48800c42d6650039902482001104144100181660381e00d4a000500e02c00001c1e2005140d0000020360143c10100010801b281c0400c07080454105103040c40300080c03400144180700c0e1401e01c1c04504900310941d80b0419440d08094180d004500b103c0204c2c201400812810040c50b402e0f03c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 165933588 1250 165932338 165932341
    0x60306152c12031c0b01051201030f0201201e030a051b010e060103030302031509010803031b04270f06030305030a09080d2a0503010b180303091216061b02040b01030f0c0c0506 77
    0x1547c03144144401114451201d000500002d40c5c4651340d21205401850082c3c80f09400c811803200a102c0d200c040040c661012030002c0410a105240d4200040b444000d0350500c4800c8401505500030204e00406c01c0c042a225481050000d50040d4803010f2a081103035010359590070040e0080d8000e490f00840c2c425240911740590030b0031281d0f28101c4018800441c03942c0d56000b40140c4031841500c10300080b0408100000d41c081c40b001c6500743c04035598411550031008141910704a0340782c05c1500341694145002000030070b400a065075400800b024020403e034a042c0391480c40707403241c104070090107440c042c1c1402c0b034103101421540588042c52030101000060900135513460209105282c6018400c008140f84000b0503a204201c007030303000e001c5a060641050000b0065482144044103170780c4182d403a403619204010403040205800d0810b885100140200c0001510750300300080e0186231512500c131041e904c66842050900c1d010307001084a884440001016211503281c180d581c0e02c603200 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 165934838 1250 165933588 165933611
    0x105030304060c02010507050c0a060e09011d01030f0623010503010c14091002071205060f0a0c120203150d05031c15030b090307050106060306152c12031c 68
    0x304807415202c0310b4503403903404031250380115a0707a800030004030b0751801030542640741c644a808080c409810142c6500028038000340c14040103d805911083c1000b001c85001400c4001e010040e42c10f42e50031002989600c0b00d40d0501e60007602110744a82d2042351081030504100da00820824140d8000303d00a021445c0e04020032503546d1941c00441d4010801005100380f103250800030048801c1b0a030060310b05441d40d40c3e081400360b041c20103003603401340c00001c04c1040c02c1c880d51201c154015640401000032210f01c0d2030040c041403e100140d03150030b07030002c0420b003c00302502c40f016a083c80204110608811440c00e0358a82d000901c80c0c0b0345e9001e60036101e40105420303003c1d41c0350001d40985c0c041c050521710344a04408041c040d140c00f4480c0000c100d1680807900a000e048050103064602040d018545513503281c06002007507a181c204007404100750390404820344452462030414842c0340030440490000745062030f51403917110300f502c000240c595203107643c0c00c3d8107554068080c604000000024 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 165936088 1250 165934838 165934843
    0x3080d0f0b0108060a061d060c030705070f0b030f18010e010b010305010501030908120601050f070f03021c1d030f1006080111030906040303090f0206030a050610140f180402040f030605010503 84
    0x255051030340000321501c20300001e40300740f0010902007d2615001e02c0c0000010100f00341764020143e800e09034000080701d0f010b0200c108808802480e2000911103001d00d042499101400043c2c22540360040e55004210504495605060401d6880d0000c011b850400e4900a0082200f0803e45010908040000450798024842d000410384c10034007080c0381141a140c83c419601e402400310b81448000e1000b025000700d03020107402e14602c2211083c401c540d00781006840c00c0045808015030034811900300301c40550000e5407001541c40c03d94642e420740e0603140002c0c28005004001c03000b0f032203569058040e06940350810400c80c0c6000c0002c110661581c80050005c3c0300c01c8800943c075921010110300042e100364040518103015580c0650140d009500140d030a40c01070b07505c074030f03003d4840b401d01c00940340861070201d25485604252441005454244c44540503d0050f500040004110002c0020300c9800c8481010b01c010b10465a640c1c0b1018880c003c841507000a5400303502c1e10001088a0900 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 165937338 1250 165936088 165936091
    0x30c03272114070606030c29042103020c10030c110c1f120609020c010f09050606190f031b08030c0c060a1106190e150c0306030703080d0f0b0108 64
    0x480c0c1e642c41000590041e0640c190b800428200c60042d83c0d904004007082e9903404042c0505110500150441d00385070307200300c0003c1802418030300e05400300401c001c0300840c0258030740d0306040c6c503150030602c4019003016418101100d0b1055080a44419440441649980242005061a00c800390700001e200c2d43e036942c854190300e81c1508a209100348601e1202007454401050383c00b481d1242c2151840309103030341640e90b1980072485a940100b40007548440078003820740152242c01c4204119100fa846d07040da148006400103005928a0175001030201018081ea00070b05000b0001d180311954034a0840c850307007000b0740c4c03074100f002d80e540700812210004022256520a14401000c2c1c070a5542d00b00045980010310400a116a00c07001c035841050034040140701d290099860b01d034000d0165040010f80c0c01c407605040c4a0382140394403189801d11078103041d800414400b281601c90340c0b41c070003082c03a005007900003074000400841c48000803140e40d0040c1c0041101c1d0344080c4200c107403740064030b800da030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 165938588 1250 165937338 165937403
    0x3081e150607080d1e24031103010e0303040506010303021603150218030a0506040b130b040602030c070209090f0d0906050a1107090204181b0c03030c0327 68
    0xa20000485860140050011140203900044c54107050070f019000319250316107106503064111020030b4410815208146642d85040e031031301d562803c181886682401725000081584031181d961000c592003d51042c11310f100c1b0f08080300e55a04003820480d56401007440200c0051158004d140000100c0c002c0341000c803036004000c0d414030000100c241010b50070802c0c00590250b8044140122507804000041c0309900400103402035080c00d05041c4d14006004092083c030680c0020124006824a030005034400c4c4c12490058803503ea692003101d141c49604c0001e0b500000390002d00034140408150484010108001c440c03101c4412041a41d41c204c80340b040d079001c079600340a0448114002e501c0f07110a60462810f0b0f80006450789107a800320b0300940c000502e8140036000b8642811000d01c03414404001020f40511014408030000b429200c1521000341010340740c001a0540c90301035008252080001918580302c0500e440f00c4808501102006580e0004900780e101c0b0981d4054061044021 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 165939838 1250 165938588 165938611
    0x303030a090201020120030f01060e0109090207020a0902040803030f0703090804050418021002150907050a0317040503030711130c1d030a0506090a020112020a0509040b03010f050403081e 82
    0x16100d120000c000d090410080e4159521034400c1605401141400c0000c40a02c04000343c40e03040c0040507402801050300700b8024480d00e00324100290387c00015141c02c0ba201184003581c0c130509072010803801c03000c07548002e4509001040c042070380900840994801d03404403000040301c0e900c400c03044050741c41030640034000b0f850400043c03046d030406402c98100728140e0400c15030484229404540c0060003050a2801604004003100390407204403515a00300c41d1900051030110300313160000e2955a00751200400104034800c000c41c0f0346201c0004d840050000a00b580e4454005013046a003c0200d003c02e603104841c001c411511059a81c0300c4c81c4424292552540045203002c000e4009002203001c1c1d80da494410f4004500001d0302c1000144d1091078100041d0081c441d1038030000d0507180c1142402d01c8594010b12a4800b49640701095504000c41100c001c2442281c07000884d0060400343e0310400040c0c10b050400051540041e565409501c04841409001030070001e001000c84041e43c4804082 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 165941088 1250 165939838 165939841
    0x50d1409090a0923070f051e0a03060f020301030204110c0604020621090c0a06050304030e010509040b1201090318030206070206030705041d0406060e22050f011503140c030303 77
    0x5040c0201c5240c1d01100001001403500810348602c80403070f0030a1a1101000801081400084800c0c040c4800500800702c060640c24103000004128030000fa006480c00185420f20b083c00340e0324403040e04002e5800401c104040c401c0061810081d6000340001da0045007407041c108440c0102e2012a13301081300000303003206450f50760802140d9400264540300082c0c074410300c480c2c4031144c400018054002c05004000780070090051102c26019640b20f02d040c0802030041201083d0881c240008107242480c0207940d5940140004004141d9840c8041d005025132084889207001507000500c083d00036180d80840b807507179046c07822408034079003c000c0d0040018801c03140103003040005182c0104860420301d062a071280d201314010304042c66084d0040340c0d90000d000c01d001c103921031a00600038075104000306251081d008102800d000300d10000c42d1003454820b81c04d0050501c0400c001d0303102c040091101000030b04019840b031026010580f0114480301c1d150161010001d4805d03005c0f0303000b07000346085 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 165942338 1250 165941088 165941107
    0x22116240c1502040f03050d02030702180903120408090906100c08031e0403050304110d120c060905070605040303090b0316140d050f19090201023d0207050d14 70
    0x4990790741070485200500080c0085030401d80d00103000584040c0051000940c51802c1c0b40b03160031101545441550001c00092003da00c031500200011000c040d01c50f81c894882c032131030350715500c81c0103032011101d6200011300003008070b0714004000001c3c0845d038861036621004100b010b01e85080703141074003103095010300c0400958144040c40e0700c01c0d092650f107595075066a44510580c0e1003242c0c00c40000b14004104820081d44180c0c10021035010b880c03003502903050b0b82c0c07400b0368013086580880601582c66041c808111036a0081202141e01c10140c50034242d9450005d01503400501044021440750301c40850300400b01003d0b07a103c4e1000301c030215400a1003440540300710011074170300c2c03600c1a020450244140b180d070103141d0142a80001d0f242c03c0745841003e003411000d1484001d4603890402c40d039440943ea00160750080c503045d2842c0b0311078050501c504038004410f10050382421940b0212043c101c0313416a40600010b0b80100156281440d04103000c9651102d51562158000414040d080b030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 165943588 1250 165942338 165942347
    0x18080304090e0109080f0306010f03020414060904020d06091d0610121b06090905090c03150c07020d050606012a060c030f09061a03121602211624 64
    0x1115500700006035158198a40781100e900c40c006407151601b001040c00601c0d6440425001c400d00585411030805042c50f0800b040a5104040e0a201e110042040541960f4aa0442c3c000000646d000c0001a540d440200d02410800107001000324442002441031140403820358031500104103010413850401d861451080d100c58816030314181011540301203031807044820001f81420383c17100780344246042e0f0f210b403ea9000400308500c5810600c5d2141c001c3d180004d0740c88001e0a995100e4406aa540005043d540200c22020350710100c461140300a03c100416058000d40007030f6503000c20300d11901d1140358507540111381c0c2114095407406400125110364481c101a66142c0b8003ca006030740580114290b4404540c107131040d0342d9a00504d6084c6100c228900b1000d103042d005041c81904212003401d1500445004a480c404c480a404003156100e0032800b031008441215100d0619903100031954a80c20300017039450040c007003640441c002d001030f001044000c02201c03d121400c07a0040c03040700d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 165944838 1250 165943588 165943601
    0x3020613051501081b0d030c030e19030b150a050d08090102030f1b1015060c05010905010608030a09060801030c0302010f110601150e09010608041e02060a050403031808030409 77
    0x54650140710b414120400740109890700800410009011401403400d0380d100c540c0501200c0d0b03200c2c0e4064900800080d820408899031203400d81403c0e01c14075411000719445298100d003c05600404500200030494549034082c011020348030903841e5804040300740701c0000d40c680078483c0e108660710b043d0390015600308005c107002c0e0b01c188141ca0418501c449403403403075080440e4609222a04d507802c641e859504104c801c0400c410091305020901c0b541c1d401d000380c469140211010400300b00c81c1c03601070040940009a2042e40440204503180d52002c059440303402103c00400043d100301030010f041c52141e507200c0d050f02c0d0091001040c441c6164015265114884a24001d11114407c001c4100c501400014000d1100c1010243e04501d5454010303c0c0903001001d0504c01e4081c03100521030240e00000d951742c45584401c03400114a4900040711045402d610020b500c003000007664070400d80c0c004049d0003180d100752a11218081030700d000710b050203081c1c0248421540140810007600d9510303003080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 165946088 1250 165944838 165944843
    0x605060c06010e07170a1d060f0a02071a0403050a1107051c020f0405040302030405040e0303010f2601020301030818030c010f0302031f0b12100b22050909070608060d03020613 77
    0x201d640340c01c005d200074005d0303204681402c0e5440c0c1c2c8030b05401821103003a480e40304009000002c0c080d141703803140100b20b1a10001d090728800540c007068071000c10102801c4891280801c1d1141c61a600e043c2c41c0003400d95001c84942c200168940d468281c944d540000c10b40305540000f8400c080c5c000c410b03014850700c0204844140d81c41043c6100c0c4a41648991160f94003a500907400386035101c1c18141480291021109018480c0c0e208000400000d105e18050b001591404400142003100a03051b0f03001020105040c2e401c9948000300020810002c0070003031001d052904034482d0000311900070903844500d041046408102c41c0c010211005120341c0c020f40d840890b50b5003003228421000901d071605400fa81045c9000c0300f0004014076101030100c08140e1281c0e40c48030300110340d41800d00141c1c40f0702070704d8650003c2d40500300c0ca003540b0036106183d0b50050302c0003921a007110300e4510005551900c4921508002c80c04820101f02c960910140d203070000d98142e0010440e54a405600c03125201c80031605 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 165947338 1250 165946088 165946097
    0x8032a0304081f0902131b020c0f090403050c1906061205031608130306050a0f0603080f0f1b0a0c050103020a0e0d060204260123010308090307030203071205010605060c06010e07 78
    0x1000c010781d01c155090880c00c2c80484001131061061070341f02450008085480250752041c1104030940d901c42c1c0c0100c0d81c10074117403507a195503111482c09032954012548015201c0c051b0001140c41c0c0c6020702c9200380d44078002d1001340a0a0350f10003045d040c1c0815480d018155410402010006039001c010104041d8413503600340e840c6c00903988000c18441c03001d8004a8001c0e45500a014038034007540a03c1d01007114202c4100301c00381c0b5640c2c900f0030304c1c4076842094442200200f00e40e048244210b056070340703c04802c07000c122156038841c0001e46500020004a8035038031a102d020a01e94424402c0d129032400d1502d502d2480501902040b5018070b042100f140c4c000d0b020071010a86120200d40424004604181c41c1d4000c041c01c0c400318291681c4200290002000c0c04614100b100e02c003080c0e81c11250000348241d500c003200b03000704c1e0521032140c10207034040c070449070000303450f0410310705800603a03000303000130440700340c845c0c0400c000c1d849940f4032000340c0c0e8001001072004201c0b1000054011015050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 165948588 1250 165947338 165947351
    0x160506071110020a0606230a0f061103090a0e06010f0f140c030d09060e07060f021002070201231c05060307050402090a030b0a060608150a06110708032a0304081f 71
    0x1202011b407050390b000501401201110b01e0f1000d207003000c4415540401b141c21121a03400c00b0b164501d00c43c4940314a40800200101701e4000034014000c856200798060f1400b200161240030200000300c003a94254002004a880407a115114040483c0c0c881241d40c2c4034145490444c2b258075540c1c108034102e9000340010440410149000d2064001c132610900d030201e42081580101402d0401c2648044203001d11300240000d0203030302107001122020030010068540f04c160004a482810b041c8035503607194210f94500d10006c500902800d000144820b52141010702d42c0005026030700195046601644040e13010300c40781c03900b0303000f5194412018284032259070741c0c2d855940e0041000c0d151108296920b24092241c2603008100390381c810b80d000c03a00309400304030f03001003506d059542c4500300801203100003400c0d00d80824441400282080c03000c0366100e0280a0800324074500d00c0000214085501c1c9103074605102c0402070f2000c03911090082c0000c011342480100200d00c0100c003000342195a200c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 165949838 1250 165948588 165948593
    0xa0201060801150f0503070f06120207020d1a06010c0308010306110c100603020a090506060909090304080d050c0d0801030f030f1e020303040302010b0f100e03010b0402070302160506071110020a 85
    0x10500000445031600100340c04d00e8102920b104601c1034000c18000c5c1c02c20202808203106c4040f1031000c998031460460202d00e4142c01120007030240180007540501a003002c40c4c10f01c03400900700f841c201c507060084903640e12801c0041d1442e142c03076040107001c00c03092801040841d400758031680004088616007464818404401e9080207c1194810300455032510148154100105040d001d0711501804100906000002500c0b50255078162403041900c02d000507524602031003a0703401840f24104480c215408458041c1c49078000c8908420140315030310074400054480c0b008036040326005441c6600d0742003280c908880513480c180c441804d0101790440b41d941003e02c0240d0141ca503050b035001c2c1da22420315182c02402c0d21000c000f400d108003102c1c0c01404a41c5e840440d0b40817500701c6810824001c4444101013400b501100c5550b0b540140302050312001d041d0042801c0c4200d07009409900511a221010402c260181d98005001c884c00300003600c03043c0c281a005031600011600442e260f00045a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 165951088 1250 165949838 165949841
    0x140a0e010503063d05030631020301090f2003180705210d02010902010f030c09051e09010608090a031b0209010902180105071a0711010504030302071202011a060a0201060801 76
    0x5403a0321605980d4041052000d020f01c00784d00220340c803440c00714a1814190000b17503040400049803000da42030014041000c3c810195190f420392000c00d13041d0340320b60703440070300d1402016150b941d0b641c294240720b80406402050015003620400c0310b40b00504540300c3d0307098000340841030f1918088900c1294808074165484100e050020710601018503030801c1400042030038403c0d08100b00d429607040c0010380c1e0040c1e0b04810390411564040c540001c0c894039098049030b010700c0503031001d03410000030242e41130280003014041f00206030640381e2001e540d80c1c41c0422100b903102107031103003030b5600085c2d07441c00000e10400d5224148039090075aa04080385d40e80014440075800c0c1d2021714400c0d40000d0075007100c2030480784c407109003409090140c1442101d881c0d0f003010340062203c1c1803608481a001581e227501980c1d0014401c815a4002c12045c50545800f40081d80b002c04141c0c2c51420307889103205640e105001d42c1c44541c04004100c4240c140c2801030003a03c0d04207c9400041d5500c0c0c08002c5580c3d4403d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 165952338 1250 165951088 165951139
    0xc0e0c0d090f03030c031503030f02100f0f0516090504020313060f090203010e0c0102030d0b030f03070b0702150c090909010e010e06060901050a0b040b03060102120a0e01140a0e01050306 82
    0x1420b07241500669500d000340864944420308803d00d800c04900150b00100e5503078000c1180d4040c100075100c1032040c1e00490502c03010b0800d0030a943d280220100002896a204411001441c401008036171103250100b025050400320010008000000c28005424290007071500010b02c01c69285040304c03107965480c2030360012140101c2e001d40d10903c06040d49000d025000c1c480504a01400a11205000007074491185180c589103968441e044c5e0f004945007000206a401c6207442a26181c6609107011008200c1c01e0302e0340401407040c41c0d440024951900c290758050044000d00524000400301840803c1e007005205404656030383ca08402c07410300c280205503800f025100030f0140c9190201c1040740c190b0b41030b00042c3c0035550780c2c1c0c1d081c4488107801e000ca80640d0700c1d0550080e260381c4c4007030040b4507006c2030506510300c5000100707118000640251007401c2001c1c09803181001e41d40c84025400150188400e03200000358419101d41c00e55000740000d60700b0030009001c4401400c0c0300c1014000c00100c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 165953588 1250 165952338 165952343
    0x1e010204051e060f0d24140405040f122303060a030f050a020604150201050a02131205100c03020d050a0e120706060b0705030405090f010e0118090501060b1c090c0e0c0d09 75
    0x40301c1018141c180802c0414070301014541b60380426481c1802140603401c40300d00c11540c000c2d90707290301003414406c1b0215813032000e5074042d9a00310a0300088030001c0501035000c0f410645045001d030f54007600b22404090b00d21940d03015100c0d0349000d103943c030b444ca1041005a000d440d5401414100c1015840d807078000e1000d0f2071142007264050a41d103070002d08580c1c0080c901e0711064414091461081c10544221003124440c5004104008490130040d00340100c118400070707201c0c0b505c0e01c00e154480d00b54001c3c0080540710030b030402072030313559084950a44403c2d01c025855030300f00888100c078400407400500b00041c0070b0340300050000e847d82d04401031984494011358059002080030030442c0f5091000342d41c0180c0d00d6007280035651420400025428040c050440d81381100d03002100034203060381c4452042078000009015040e03443d485140a40c3c0100c05006403e9103428114104d00034a002c1c00c52403030740c0240680368162800300102c82442028064040030001000005401c62040c014100601e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 165954838 1250 165953588 165953591
    0x22104080a020f0604170a0207090c080f0c0a020604080d0b0402040b0301081614040f110327010908030f040c0305070e07030605090402090a1a040e1e010204051e060f0d 74
    0xa10707203400a0314150a806290401c3d42c030007010480003d414591341407818044000207034940841c4441a800c1c01c4081c0c000005441c5090140101181e200c01518010050040034480c6600d5080304110b2138800c109807400540d0000c0082400514040000d0482d000807240c00540c808681000400341c0c0c6c03003030b400440503540100052003081d00500014074a170003d4008030113141c0ca000d203403120800100005074811a9074051840c141862900311038200300000419030b5480c54130040343c801340b003000c03440140c102a0790070000b400f0010512803200d0307190704041c58030b0859654000c0c210b0340707200082007110b510010100000c00240200465006040b048100d200d091402c0031008084409035400580702e03541030340130700c000758482c82207154004401041c00308280c040e1030002c840100090f20075a820510302422201c0590000c2010b00d030101061000c1d4140003c0850464281d0195025580d4064020414040ea100d00314074004007000026101ea03040164211112503503030070180640800c103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 165956088 1250 165954838 165954847
    0x9061906030501090b0d0f030c0602070f0501050a0606020313090518010903050315100503060402092107055b030c0e010306030c091d070b0c1005010e0a02210408 71
    0x2c4e16405101c00c403c40644400382c442429445081e440050750710701600740802003281c102440745070303011a090b240d00040181d40c814628035219000f04011200805103a03d0245c02140c264804411542440e84200c0909005401e081522005020142c60042e4256903c0390900301d0080a020f1941440d0217903e4060b200e140c44017410380c405d042c6101442c411104050065001754012013030301c1c1c0210080e90016204c0005601184d0455100c400001da200f0381e40e000c14444410000d0701409560041d556081004686030780c241100a00c50318101c0841e06108529100522a414001020780f50031034071142d400803000c4115042c125144014006038448400c4002e883d041020900440003c1c6070400503649182c46400c20501d103070159500c800c3d100d0002e0800d0b0b10144c8500e0300101c04400c00c3d12809030340e0341d4a002d0280e10030f400c04a00e60059a413004040c442c24482c10381218850140d5045a98510030000001d6005c1009100d48800300c1c201280d02c000b03100c940902c00c82c42070300500d556 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 165957338 1250 165956088 165956099
    0x1e05070203060c04293a0c03060b0702030606040902010c41060c09060f031311031501060507020a030506100503010609020a0203040902250b010e150f09061906030501 73
    0x8803020107103c1e900384003510400d5601505040100c401035000031b82e6030709801c901c148807040c02c1c68100d4403084101200c002e10105165140d44803d5081c1d90f16201000110b44d00c054420340e5003c1c0100107075050b0490030008847c0e0400c0c0c3c01100c5402e105140c0f068022486a4400000c80f00e2000100058075a281a010803000e82c807003014805901c4000c9590100381e410880c40c0d442c0c2004207085076112002c100301000c5d0f01c2d11000c0d11400b00005805076242e181001c1e44140c600b0011a080d103030700742e010480c00c0032420042000c4210b4120b500e54183c89a0900509035007540c80010101c2e088686c00f0700001c08142c06110741e038014103000300d50b88505d9203400201030a4406542203525a2441044200c91140e000000c813011a4801c0b0400341c0c540c6986440400b000a10800c1e084000a07a000d00d5000c014810b60300c941640c0c4100049005525400c1d03d13071941005034000d668100d65000c00c6103215160020005a0100c2c000745a100c1d00c900580d4402140416684010301103030301c500c0103204 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 165958588 1250 165957338 165957359
    0x9060d020903060109090809040c0509040c180f08060c130e0c0909070201020c0c0d020d0b01120303060807060e010804050a060204080f0c030d02032a120405040b0d031e05070203060c04 81
    0x52044480038031980c04191101f10303081c03140d40c80c02481141d41d207600c0d034100c0d402403043e0361a043d030007001004424410307900502044001c02d140d00c40b40708082c8000c999005403100c44410b840d1144020481551854111100c0c0d0b40010740d0078030070f41c64449000809007602070a16101c2c00c0040784050f250440d01050104080d0003408910959005224600d092034001941140c80e940445160701040b04da8000f285004074074060151100c9a2840041403220f049060104014407a41d01000f125a5a007802500d41003140600c80000e03510308030181032507119220300b0303400900880a5400350906540e410341241d1199001803010340051550342c1481700c003400880c4003603034207038007400d400d00e07000100945138410100302001c8105d0f00030b205070b03032103c06200c4080c01c180c0e40f108a5000702102c402c3e205481d00305200752480b844c1002c041c100141004083c0c19541c6602d0f44414501030b00c000c421401101780480e003102002030900c40f00c40580d4040020343c1c081c1e03049030f030310725070321350a00070300c60f4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 165959838 1250 165958588 165958591
    0x1309060605091e10050d0b03030a030c02070e150603070203311e030204090510090b0609070e0907050d11030f060906010212030f100b0c060106021006030302030d0f0209060d02090306 80
    0x9400c40443c4100c00c0e040c0c4501e003c05412102d18a0302c0c1d540d84030900000b000409030200816003500c800b04038101e6003a0941d011780741c410b21a408540030603644401c1c0b10441001100c0300c19245440d880884a10301345035010b15041012801234a0901d0804140784070918800510b1080401c0303041903520070404100ea113107003d0664401010382442c50b2002d58890601c407440005d00550352940d00303000f0b0050900041428600d983d10910070f600050030445018141600e01030700c100c01050218818500034a003107081440c0140c1030003600d0f6a100002c1e2190f130812000206003a4848116101880c1580000c52040b0301504410445003810300030311450100003016641994451600a282810b00d081925030080c0c01203580b880079580c030400c80714130708044da104010300c180102d40105208030100b40903060324555070031a0421490500e4180070340b0068840900036070802c1041140c4049070f070300174404140002c08003500e0032600703001080540d40074401c0300003c15404126040a40b4081c808135 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 165961088 1250 165959838 165959869
    0x51801090c050c030702330a17010302030c010807030f02121609030506190912020c030c01090b0d020c010e0f1b06030408030a020706270b160c0305130906060509 71
    0x10b6042203038200d00513640e1702c10040068424181440074410405d5060811038603040d81c0d01c00c108207006140d81502c0c02e50810303c00b0030003040004040c1201d14801c80ca00324122a0010010110410ba00005442004000d002107007016203580203400c404440340014000000502d01000303182c68510503240d07000100114032401c000082c181000800c0c0b00080c40c2c0e801020f00300c44400d801d0411048600202080680201040d4608046070415600403403904440706080e003d41c1c1c140105c00b801152541c0182c040c0704c00c800014803407a0b10300c241683c00341450005400000520b0200000039a2402e1907600041c0d1043d801848100000080d10030320740075149040c1d82950443c01c182d5124a40d50000404021070f055010803002d040c820140c221481d206066058207844040410070081c00780c0810074240c0325070a610000c6000f504040040035451601c036901c680156031166012101540034a4a40880c034602c8140031800b910244190001005140c0300c043c0d8950301002131000028102401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 165962338 1250 165961088 165961097
    0x3011428030c1223070801140423030307030207080c070b0c25060c0318060e0307080615060304170301082a1012180503030103030306170309100504051801090c 70
    0xc020009010211400d445a4070446071480700013041e481038039001850b48200015804c0c05442c1507600301001750180203a0050500700110b00401b44103800c210050646814039610820018080c94441e50151803424803034090309240c01904100d15280103025008215400000a0301e44905030003084078004e24030307031200f1100141c1da0002441b040296942700741c1c41400f80c882c030503908042c4105201290040d8400c0510f1040b51184001480d00b8580c072000c03806441a03004c0400c00000004600d4807800c5140b06071000416800203102058201800032644401d01c04820104218094003070340c042c01485004102c030b440b510a0f1020380c7c54100d03c04500c031039040b034403200300c0c1d131100d10322401001400d00f0710495507940f03400c42074024100310800f00000340310320100b00e04104020000318100e03800f0f40d0307051025a882e2001006000c8244d02d00120310707407041205d00c0380d030300f05039003040d0206510381451814650b8850200f18841000e1113001400d66201c1c00500400c0e8191141103101c800e50300c0d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 165963588 1250 165962338 165962369
    0x5060a0305070612140708040c06020c09041509020607140606040902100f020c0a090204090605150d1802040c080708091606050906041509090501050d020603011428030c 74
    0x11407588a80d160300502e410010f00d001540c14124207500200c030941c41c0c5d10100621450114401006804107a8044602c0030001c034000401c0703840010400e0701c84c1c800072319624960300c0d143d94611205503800d881c2d0710a603032602010b0015a07120400782ca44280100340541c140082648514141a8002c2600d07208900d045024000340e2294001410710750b8039810100d01d00c1c050070009030b14000d51441c1040e0711040c0040d0100e810300094010300100e541d24202800711030388580170010b00306002141d5501b003410601c10303240c0034080d03500705000c1074410380341b101f28203101c903004a03099424100c00800495020414051303c15440010980d2021441014100c0007450120f10964060540310360810040c01040485d0596240003c40e80100004595180080c481c0480a09441d441d071081035400c0380780400001d842e0070b00c81c1480d040c4c194020003452450382004070044640c504021003503040b204803411000210244a00600c10300458003a40c1070340c3d442c510b401c070703401301d5285c0045800407012030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 165964838 1250 165963588 165963593
    0x9130c080703060f110711010309021c0605090d05270913120207150e0307050303030406060e0c03040c050603091e0106080d051303030f1106010e01170f07032004090c05030105060a03 80
    0x5440c103030f55200d140b00094161000049001e8110312b6400781d4814014003104a001c07411140014446202d00418003c51351450005a1a070b0f98131b10751b48001c01c908100036050b00d41c10802985012100c40506c1506050342e101080c0305003812200e1203111291518481d080c40070300016590340c00941d2000f4a00c2d141072a800d100000310108024042c44900260820305640038050480940300250031681c0f40d03d41814080007400e6140304102000c1c45030404540c1d801048030403244500d80049100031200d01d0402448419800200300b19800c0c01014a243c11034081080542c80c44a191000031400504100081e03040c00311200010f0300b0720908001c07840801e042e1070001422203030123041087c0160700681d0151800f050740b10009041d4050f03800082012607807001102c0c162500c00203050005d125220b07055035500501c01c01c0ea4980d40c04100d0400005e0503071241041070030340c500481e55518640a01007416a100e681c000c41700c0e5103010303070700b4002400c003481582d62144040320031840592943c0c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 165966088 1250 165964838 165964871
    0x403120b010905090c04030b09010c110d0f081503060403030b130213050f0301020c0f010f060b07032f0703110f0a030812040f0206031303090602160509130c080703060f 74
    0x24425203004090001c00030b41d14903001000d0f60002d41d0042440c0c88d4500d0000c250794020410943d8141c04188114140c107000000001d9413a1913164544400209000300720b03060b0b0700000e0090015843c102c0303101d10602c2d9a2010f007d41800f46129860200e001c000356010001c503201192026003a1a00c14450b90841da01c01c0031481c0211141990407050001c10180030901a22594108420340e10a0b10600786022405500910310811000b03c20031915888420b886858032840501900040c0000c41050f00441000000c0354001424010401c18030580c24203d820014182d10075030f8001a00c070091002810034540915901d8001c85480100c1e90440c0d0f600240c40c061071709805120011200001c0030017a94809200c66160010261901e0f03190819101401500c40da0040700000c810ba0b00c0010040c2c0002960041582704003600c0f807040c0d06013000c1c400d040c0d8009010101d12030301d4503190b0000c2582d0b111001c0150a43c0c1e0043c012203815400c00d03105030b03007403040c0303060b10546400440e048c03543c401d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 165967338 1250 165966088 165966107
    0x50606030106170c1509060a080f09071503020d140c0a0810030302070308160204050a0204090f1407030e0c04020a030209030d020d0c0611070c0602030d0f0603170c15010e0403120b01 80
    0x407500c982170300300580e044c00d00ca800759175280b035040f4100060508005402214a0340b041c450a400c9100300e58a440005850f0fa40610030103030300070410aa48898180250098075084180c1c2800041c1e040c403240504400e554140c40e6280d02c1c550000e607104070a5400b0382520f82c401000301c92520b01914641d0029920b0300343d40700240808402280303212081206500300901d00360005d00a021a04103042c0c05070007580300b40b24484015141043d80c848146103801003000700381d480384989442c2d0751107131029005440c4c081a00702d85030003506280d90341030b9102d10241205680316500140c880481100781490502c0c42042c85043d548100f2602c07031303226804028000f04aa00c9500840c0c4075103440f40300002c43c01500750040c030701d035200000441c00a9000004e4061703d2400001800040121a003d1045841c14000034240080b41c0039140e845000c444000c0409094410072662003141c840e50500b140c020a800100c1c407100800d0501c07040c15440f034418454a11504400c0201d030305508d002030301c100c0d034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 165968588 1250 165967338 165967363
    0x60307050d050d230c03040e0906071d030703050115060f091206020a120f09030906090e13050a0b150f091501120e0f010209090f010e1f1205060603010617 68
    0x31344c01003034a80074080c1041250f90b441d0204481d403225820300e03155403070740c01030b01034a40014801000581080000148103000d00c16070344900303c81144240200c0700c065040703807410f41c052098200010000f102449000312015144002032052424181e00030f01d4001c004074440c0c20015010020300c074050f80e001ca66114550700540040ea641098001919500990380c00c19280c24030301060020b8001050b0440182644290342d401005510b502c0e081c0c41040080c0540748942e004200001c58241202d00160082806402120613018a0381d079020890b803403c035905036401030b082d44000c41506001001404c074110803562101c003894903002481c203100c2444007150402c21500700f0724104072001da20a2295202c1d074000c0d075542e24001030ba001e005c2d60110402130300800c800c2d4001541c0a52a0110606030744802030103404c2500c1ea11404020710004a804904a048010000644d40e00c410bc002464610840c058101460064201821500a58019421040c103150031401d0100c010400e100c00070f0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 165969838 1250 165968588 165968597
    0x10203040302011b06270c08010c02030a080a112205030105061309023c040204031a100b0403061d0a0b060d0309030506090604020307060e0d0f1b030803060307050d050d 74
    0x102c1810420080d1043e40021110401c000341035100103d1b43e001084815801101008100d9a603030302aa403c07242580180001600203218480841e40b1401c00190030504884021491020719603e00816500550550b05000c4148054886400c14000a64010003045000700304a25100d00422a803115402d6102c800c0c0c1e42c0c841d900e0b011503a40301076942000b00400a00714040c40d10003045d5001584d800310441594030b0311041c0310f909140c54022141501d41c450090300600c642c40c40814800d20700503120030000c00601c1e0300820790b0401d42001e40000e41c0548008030b0410000603902a80e001c1c0c980c00100c00d50440200000810201c40e105600484250381e6840c015405090454181300c55801c02841030040d501486400e5400003416400381d40224185c07190603580c1d0702c00b0344155041000c107907000a01e40c0c1200c0d0200300700c032584001c1140200c1950741e21400120302c1c401d280030107410480d20b0003000700c00d0100c0d501341001144041e010903110b91459028540780c09a0740d80c0c46030f21050401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 165971088 1250 165969838 165969887
    0x70203030f0f0702012423100e01021c030f0b240d02090303210f100b090d02030102070309210305040e0702031e2221081611090601020304030201 64
    0x4900c01d500400800e02d400044682c241d035001c0c12440d9212580c410200d114051700c51a400491f184241c2c1e004d40d84000b840c0003d80c6001c075809440c0d1880c03140b0b12034154050b68862400b04114429107842c202d00e15a000504460030486000454205800080c0a600b41150009400c010018145c0310421815903442e00c83c1d440844900c00b81c40769612943d01404041070b01441d03a213400c00900d8105240d40c01810031503581e03200052003000112413154444100305010840d900e211002003020190183c03040c0d07000070700b68001c42c0c2a80e000c84800c400062400c1c1d0200401e0034807a038840300303a85400e0041400f1401c6600e004040e1b00640c0a100000a102c0c004150640d000300110340415213420300b0182c2d043c0c0e81c203051003415000406920060011808030400d1550541e45280544401c108020f15442003894682c020f229010401c5407184820000c1c45401845964185000c40c400e0074106114440d00003030006180c0c0c0030740164159031082c4414001030382c01c410020b42003007104d035115014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 165972338 1250 165971088 165971101
    0x3051c030504020127090603060b18071205100e01060503090105061c03030f090506010b0414101b0311060a0207030207050405010302100c06090812070807090509010b0d0b19050306070203030f0f 85
    0xb05c265643c030200328145400800010000207070018110071000708e41000d0006038882c080002d000701241d540e00040c110086000c2c440c1072071f038010364002008807124110301d034a0f070026445450082e00000042080401000018682401541d40c03215081e1440800304c4055404060b0f2000c25101c002d0600d511405480303010a0307142d200d901d10300c3d0440d0803140d555a581c42d00303404903802030017800180c074004c0350085100c3c01e1045250740c6400d2241e0303a00503054011080c1c9150901000011020040005286582244200591802000130f12801640c648032841c01030f2412a1562020f4000c504200041003d60307103040d0907440380e54040c00c1000350302d4402c2c40d01800824035403200404042000c1070392102100c010100c90700c03408540c0c8400c201500c0d280000d40303078480148100c070b0707125100100600ca034130440c0021342072810741020013240c0f92907041c0000d9005140400d803025101c0708030f1001c0005143c100030301500200c031800554990f0410315480c903568500140113072100920700010460 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 165973588 1250 165972338 165972407
    0x203061e0705180d060606020d030203010506030105150d09050d0f140a030e19110108180a060f0b04140a0c0f021c0c0b0a0b030105010b0f120414030403051c0305040201 74
    0x3d510002000100750310210702e0032100074142c0f0f010b02c800611490740d040984600920849041c1c81d0020318650640e0700c0c0c1410000103a185d510a91001e10080c08000f2250b0558003504000ca4030620144c40b0100100300002c00300989200020100425003401003010410107045810b803201034a030114081240104071450115050070301c8442620b0501400c0903c0b940c5100c20019000c00d0340d600107107440b903074003810140c2403000520181e508032941c1d510000343c1c50360040c1c4c1c072044028008644c2c10400c000150440380101d050416880d03249082025607060342c030411100c045030341480101d2201c0b201000b0754581d0742040759007231103a03c1e400101c04d5070b001c1e00101390701307690000800701c207484c01103070340000b8049048120340a0340c2044004102203100c0300076038a0b1820140000c500b00740d1007422602e01240c02420907101003414466141c000081032005102450280009289070f05c107d11240c003240c0c030840191010145418144070050ba48030088401044681301900c1030030001081c50f00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 165974838 1250 165973588 165973627
    0x212130f140c0108010914070e0a120b0a0c1b0b1317210105030c0d022403040506010602070608060103091113090209010906030305040302060a021f02070203061e0705 73
    0x100681c00034a01c00042110001d200c08184070283d03264103003039036280072070740542d40e042a00500c58811100010042446401d40c24450b140062071803054981c2ea01300e00c003404e50311100542c1c0c50b403580700c00c0184c0b44c18940200f640348809841c0240c840c03031440041800a070728002000b00b4140705200451a600100400702000d160000f0101042849101880c500c40e031101c00f21800340b165600c3d04041d00010002c00034122000600605030000208082000312070381504100ea0107004100c000c0042503018600440241d90f0108895480c00c01c0d00b0f2040c41e180050384107808640c4108010311003250f00400442d00883c081c03d002c00e10a040380b50254410320030108064008642c10280e0404101c2c3e0b800c85d280b598020350f01d0f81600e980310030703246040e148140070150100e50100010001810800010000c001c01c0b4030568207001008021042402c85640080c0310075030300403950b4019840c0c14444190440401d9900349004000f01d030a5525081d0014404000e111010032410400040001400c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 165976088 1250 165974838 165974843
    0xb030105010608070215150d1a0708010f0f150807020c180109150b030601050f0408120d0b0306240a030203030f0a0806010f09090b04090209180f010212130f 69
    0x388203942e101c1c54001c1000d502201c10030018031440b6021248602e035892050302920b80c0c45000ca80c103510720340601120101140c42113030170050710901e000c102003c4640320f5000304255039451007903503d0502e21182c0316000750805180301c0d03a40d40b4104150010604000801405820032100c04da65151060f03051a03c0008440c1c1c0040300521b0240f4126104800355043c0c40200008120a05103515508680182030080340d600c1d04c010800b0450079801034001d03204400c00e00700c5161416440307040c1d060a155503411104502c0300f012403104c5840005029100c030000f0290020700c054034080d208280a2400d03019079045d0806554100c0b007094640c0c500142c050750700502160307510000c0756440c05056205a801d04001070680e000706910350300c13441140049007069642c08048500f8041c405005090503000c40340c0c015a19800c510058a5200c0103a01c84e8411000070380360380c90851034450800e00b20404120041e44100142d00724903030203100c825000055400740c160084203034a03200c8988140440017 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 165977338 1250 165976088 165976091
    0x6130b060705010504120314010e09071503050702010b04020306060a11030906040611010615020a06110409050c07050709111e0906030c040801110a090902031306020406020c19080303040b04060b0301 87
    0x840c003440b00540001c4d0103244160320b80030030582e81c4102101110548188565020076540041120902e01555590452080070550b481d41b0741c0c4001401d4213199048507400421b80b1790040200c10341d0207124860701114182d07010b40c03641c40c00e00300049031071040d01c070300d04148030302c65074020500d03c6c040007038440103400900304680e650784400001d00020001580030f8010760030a00080b41002c0d100d0a011012090381e0020200454030750385200c0580525410888400030621000074860307058064240640607071400c1554420803410302d28280b81598006008050400601c10710305242d41088035000c1e00c040f07030140013660b400100d2400601c2040310711a44a1408814407203140d504000801c201ca500344000c000909520440384441c1c02640c024102080c2d01d880e0400c0024095002181d000141792044401024a5910041240c00540150005a0140b60592040d081849488240010000c0018451440d1070300e0540c0d02d2000403c0100707016220300120f803c02445403c00d01194000600 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 165978588 1250 165977338 165977347
    0x11b02160504020c0a0227040f060c090e07030c0c080d060e011203050f030402031507050d06091107060e190503070c1e09111b010f2306130b06 63
    0x959460080606000301034422a00241d280b03010310031142c0c0c001030381c0c016084514043d02040011103591042c0a4145841030090a102094400c0180300794401c200c480c0c61081141441012206044d40f00420300c40c01d00e0701030202d403d00d614881da00c50524900400c040101a0080354140a040c9000b40340020200781080480c03256009036007900d1020b84041202d80e0303503030102d48940c80301d0640500403d4041104460500c11100210741c860f001030100c3d000445054a485400c00d41220300d0f000294011460043c54113a42c060071300180102103090000c81e800c40c0c0803006900c10410014901980d820401c0400e0b50103111050b0b0a0020b0003038113000c4030140c1452501c0354000041107640c1c074a990b8000c1480294071021240881c1034480000180e401c0146110040501c903114080f03400d03041c845002c08620035466941c07400c0c084000490070007140c4500c181501d19101c1340401013244410000c1c0e6180c280d004072944504100c807602c184c2d00041508000800c0122502d40d0070142c00103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 165979838 1250 165978588 165978641
    0x803090c03011103010e04080d1b02010b04050610020303010905041e0c030219030b0f04050c0d08120105010504060c150f2f0c03070f080d05070c03080105150d0c0201 73
    0xc140a5900c4150003e00c01e205404a50810034070090049000340803803031000c03402040302070014068a424271500050483c11003007040c100000013442090060b0346406c09039015003058000c84d5003046d03094801030a01c103007498010391280070500500200030f07034030b0300010240054010b50402d00c01d04440f0103074006445040c4207082c485507000c140d0043c1c0041840c405080c1d10b410044003100c1d049000e0600036101c24102c80d44920005e007081e80d0314030417a02814603990703130300488859552046d19215035541c1e10b406d2030840540140c2c00f590512105001c1042502d400900400255500240c2051601e500800b0b00e0020a682c400702016507240c844130074600d640e0310039480300d4401489034428509503d80074103800c0380700e2040100526003061204400180b4000c0ba550b0030f0500c1650540d062400c4012080c0c11a0f104541c0040040c55020b0014107050300080c291780905400d072211131f4801e241d02c00902180c89810a05141c11384d4840000580300d02c00e5200144c4081d401041130fa142c0d4006 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 165981088 1250 165979838 165979843
    0x30b0108071415070303090204020f091306030b040308040516060809100e0d180b0f040f0801110730110f01140601030c090f0303021b060901080402100507080309 71
    0x3401100d000d4800c2290114401c442070b6504456a4802010f80d12000c88403007201c0a0340d00503410440505844030b2110006960f0b5001420903001e0300b1035105c0c3c40301040c07410003030f1000881803201c290030300e0a0800d101040040c0782142d07000c0d8050901481c2d50721585445880e103640d0f0300582007421540f40c40803400301d80c0300d9105030040421104861a070351090403071108460300b03e014521268004007011002038011900b0041503440e4200c0320a40c80d96403980360806078410300404418410025041c082e000100031024060079015000308080c10b241411860284550300740075100482d8103652000c901070314000094501402d1089105c0740600c110082d0600d840005164071034000c2030010210440b0521418402200904000110f5120200194001c2a40030000c508001d0b1860001c40d00070044d000000085110390b005004810b181c5000c0c00f44038030034072844e0b440340d0b804021003a043c1ea03012101c1a0440d0b01101c5801c58000f01c00703410381e46803068420003040c0010210410200d420003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 165982338 1250 165981088 165981091
    0xf070606060215040b0a0204080105100302120a08180607050a062a0c0b0a02070c081623040b0f0a1707050301050415090201050909010e07090e070c06020f07020901030b 74
    0x1004284512078807028166160407149400e904a00483d00000e00410b4110030301c01d40248a02c0401841c2c6a00e407425142594030445862200034503500040046062031a00001d01d0040c1030040c10394403680796900c503101e2150070503281699009154914407555a481201c001e80e50050807180039100354138200001e80b000003002919000007060001ca20900c1d0240c118003c501544d07a108550700c955074030328901da009821360400715800e20103280017400a15003500500b8000000302041005643c04c42804652900801102185408510000c118100d4188000c400440d004281c0c581100c0100317516214100b01c0c5a8840119480010200b07400441e4180188210b4191400151540d081c1800d0351b900366801411070004966130b040e038458a42c000581c540c070501d0058689401c402c00100b51120a80042010a072000240301003603030404604001001d1000b20711246161030080a0844480c1e02e10141100c1c1d00090040346c50030402c811110b0311a4010118a001d58580c141001614030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 165983588 1250 165982338 165982343
    0x110612090d050a0c0206130e0705040e0a0b150c011509020c070503010b012a050304030b06030f0a03090b07030504030503070f0213020909131412090a050d05030906070206040b0f07 79
    0x1601c030340c0c0101144900e003203c0940c406a107034210300110f03640c00e00505a00c04064002d80441164012603001c0c140303c0d0700707801007645030754054541e42448000007198030b0240280c08003500c0e003010700c1410384510707001c01000360403c0d010944030140024600e0240c03a071001c006060440603100030840f0301465000c0c0010203000d06c06c49000c113880d80305260884220614150100b551501060505002480120900c1d003040071202442c50703d507aa10381c95034103e038000720340b00c0010108010307444c10108640151034240d42c00505c40140e0644002c1c0040000f4020030742102c0300041c18006140c06a800c440041d6800070072240e88015a0500300c111490004080780701c0e43c0d605942040c284054005d56020b64002000001c0b6034903038031150503c00e801040c044401101000c1c43c0e000c600c00c10701ca0070884038075005c8041e603140c040404001c1c2111303c60300824416030301c05040b070002c1480001650f500136000e407003051350340b038080c000a0020f00903507101c00280e240001d0341c61540340011014100951 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 165984838 1250 165983588 165983593
    0x2060307030b09071e0c02130b18091b060703140912100f1503150c0e03060a0507080907030b011802040302120325020105030703050601200f07080601060503070c11061209 75
    0x30710845c1c0c201c60440b10504d0181d8001001c490000c040c5034154401d66605500514400c41c00c0980188800360340802c41d0000c00d01d4101e0712210307100e210244c00c00c0b058640c04960040c94079110313640103815210391582d071030b07200380011886091a403221240355a401148000b10741443d1001c1c640c0402904071890b444014030700f00001c00c840d0110301c52400c130581e580800c400c505015404580001400c2840071a03042144022041c9056181444094004c1141e01004202460140d201814200c8090101151940502000c1000c1290310341074a054030307582e091000c8a25030001c509406806180c05c0a544202c0d40d000b121030300c1000000508010f240d00c0107190f030030174150264941e8074840c1407020340403c20410000c0c0855100c4e5004507404030050401441d8103045050540c80103c0c19a0f070196160300a1105031443d4004202142c024001d000082c4000d43c1007100007009404040e1040c01031242c20b80f0402e041101032205401083c1001d80182e4407148080d07880f0005840c01d607101d08050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 165986088 1250 165984838 165984887
    0x602031602070b0a03020c010b1206040303060e0601050412020f040203071701060302040b03040201030504021201150303121b0833011e020303070c06020c0a0b0f18070302060307030b0907 82
    0x324000708460080394030380e20026003401c200d4602034002c0d520a05444516550351000d04007550b40307070100c4801d2541c840005000602d410702d03000c1d00300e44650f00120b980c0c003601010482070380c7e40102118180c03800318018910f400e00c54400f1038104007112240a07070060022041084141d4400000c8400c0c141c0100542d4050f60303501026030417440340d4003410581c818104001009540242c101c9904a4409444184100c0b250010300d42105d00600c040e00b410700c8208010010f0580c0240c4440f0043c0140c40200b11aa403a6a86541c42c06406100d81e03090140500004091011450702d054000c40c0d59200e0300c8a5100c0a946041d0000000c8602400b04c0c000c28410740f0b00f000154003100c80c0c440f50b900218074544401030706880702e514602c800c55400e6001c0250300403981007489240051881003000e004039081c0200f83c071340143c00041c0601c20040c1444d00d25000d091000945c14102c0c0e40603183c0c50f80d0380d207480108070054044e003d440741d0010b42c0d04080c845100d60112054500e000c5000343c01561 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 165987338 1250 165986088 165986131
    0x3010207060c0c020102070608042003031308070810140106030b1203040311090f070f050306030a0602040e0f0112050304090c030f150512010e10022104032102070305070308040302010b0d060203 85
    0x441d242950b001cbc01c070b010111803912004c1800c1d02008500d0304000d040300e0030418000d100c3c1c44120196000b8040541240c442000320000810442c46d0340e05a07450309119562131880d00f00001c01d01445510201a02c039010350304a41ca8030111442e54015101c1a25507460301d038100314031a10300200245000c0e00c2c2e0780001401000030351425900a14482d980d0760040440004100ca440d08090101179141c02001c200a0000300244020f1004040034031840807076142c24810309040c600141d100c00c0d80260901e200b81c00141c1e006c4116000d54407124000195410031040450003001081e105485076854090624403600f0914200030842d001107030302507100c541c1202d10030300b07031603d07100fa2041640c0000540700070441d9580103440c0002124080100b9140d0314441134a10f50001d90781980820b10030180e044140f1b588400000d94048610070652514990303540007403a034400d8005c00b50030083e4940208080501c00e400c4071006100050400c040312005052410003580295502c040308a41403400030038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 165988588 1250 165987338 165987347
    0xc0b0414150307020a1106130f080f0f0a12030f020a080402040b0a0623190f032301140d0b0a021b0705010504031b090504030509090604090804090b03010207060c0c0201020706 77
    0xc075420361360103880e5040844c2d0765000464120621117601c000140f1420312940d20042801008103805084008124a0301c003480381070100080c1d81c10404d41080002c01002000010780c119956440700030714440b10036071070049004240b4524962040c500002c3c940e800c440d80056081d0049008a60030090381c840d42040041b29200c9114207404580409513406231484441459988100d45210451400740708082c0c0343c0150304965040c101044503191003990451341403050001422a644000030401400078440320300c00d030144188000c4a280e116221a19228100d401105503486032207120241016006030000e034000903480c010382c130722881184903d036000080d100102e41c010f0712030628003030441c0c54491542c4480e044601081c1c0311400000351070681d034461a842640039603a0507880b8a0303010200504c0c950007602c02c41c40780c1d0500c0c9040300800e030100125070840ba040358002071401e94900200e030290013100ba000c2d1400345002c00e501c0115030081070202d1414400da0039030718003c1e1203410903207 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 165989838 1250 165988588 165988591
    0xc040b090c0a0203090406080616050c07050d0f150f18121103070f03050d0c0302130501030c0e0a0306020c0606061e1803031303120c08090d0c0b04141503 68
    0x3503014844a01051900c40d0740c400604030740d403061050340c0c0b038503c494004c00d0684005a0143c2547c4e480f2804124883d26041a54150400c40d80f034024a800c0064600c00d5483c43c2500070075108096071a4510100042c20724020f0340c142c7e1040e1080800c1c3c0c0c845d6404402052145031000c1c0c1c80b8108061402c010030711203405c0560542c407189041500d800c110302201c102c0560700b168902440104881c4010854800340424000c2c440c1c4d984660310f10402860f0419243d030f50380c508080c035005102d000c181038505510103040cac8e9828600012010484032003102c2907041002c00d16000300070600040103200031500105540c910407001c5410035110340d03050200c2032150300020b500c0c665900c282c0d4016024160b0042005405d401c00701562014200002821548103034802024101109010420452061955104841c6506116000c00896224850343e40b0900f20681d11402c08c0d01d10b01c00803c031f0405480170141003881c001d070762150784544824103060760b10401c56105d5010406444510843c02c82200e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 165991088 1250 165989838 165989861
    0xa0c09060903060209121203190605090414160b04081b09190b0406080d031a010507150e030406020d020601140109090b01090b0c25030819110d0807020c04 68
    0x1854442c90354440304001d4024070b0003968810382602c240244600c041280351250005400750943c1ca080c10161155100e87d15030494020760b0505900304401ea603003d0b042a4019040640d542402c80d41c0068a0705040664400303e05061020501192082c0c83d000604107644d03000d4111681c416400c82e00c080b150301c0d80c6a1903603014101c00c2c00101403901d10601088c9440f000700f0301181000038840020169000d94100303a6140e030240440a104c5940341c00b6007624023a21080101c078003003202c40000c02600c5089070207050a41d075030200c410300540c10b0340a20031404075841980d03116034451000940b900b2283d110304006108150010400780040c100035014041e05842c1c050026140000d00c002600c1c100c0801c50620100c4a00028210b60318001000001d544001138403003c018000084041c0c40010a51001e403c007050080c00051191802c4910342c000b41040034500d07405504040394620b440180c01c040900800841c0d0000a403c02852030180c8419002d070354070640e988051108690030240c01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 165992338 1250 165991088 165991097
    0x90213050405072102030102030f22030e010c1e0812180a02040e01020c070b040f09050c03060103020705070b070b010f05061809130c080a020909030304030206010905100512060a0c0906 81
    0x1c202c413074032552200c08045805401807842c0803154001038220b0700308507082e1555032428000c000d03600044c004d080345241c24030340c0c0c2c60202d00d400e524005c29101802201301c0c1800112401c40040c0300840080707680e42c490004004003041030900d00700890707403c580c80404603070060b100410300d008188008d00c030284a00000034074094006808000240c00d03c610210300795507007003000f40d01000d0184843d2000d03155415005645618218070540c052031a035002e0311002c0e1401c81803020140303c110449400c02424a005a1103d015040250603c00c0940c40040c40c0030700054100200844a407009040380d10712100700f10200d41c1c6000780f10503407003078800d4101490903848048056150608071281c00c10501c0030060441625940c400008161079001200c041c9c0c00b401c10142180341503034030107602170b042201442c1541071540c0d01a60703940041c010407100c0307a203410000d00304075209070f0940300511004248040e005021304405450f00c0c0c05a0f5450141d600781010012810b02421034002100e030180d85 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 165993588 1250 165992338 165992353
    0x1101020715050f040b03090705010e060708031308091e0f0103060503062e1215090b040f0807061b030c091a0f0409020406050a02010c080c2505070801090213050405 72
    0x1d04030b0b083e5200c9050f08201d44002d10020a60714a454041c611414107000100141401c3c0000900003c81d600301c5180300d000d00b0032005000407112800c0d250004880040508208128039004071036000c0d008085030400005880401d11070106104140090002d84000d40c0071407030080114160b8417140079264140c6d00c05408107182c40b01170760349844943c08004000183c11040311901142d250340e84d20041c002e1800c00c0e603040520a41c18090680c210f4454020404a2800c0e924103020040007000941311a184180403014003a414044501d865881001085004501e03030074080180038001c640c0000030b180404015203503009603019000da5080c544100c0c2e0b0388a8070000c1d444954090380710344640c80750600000074003a0913030000c1d002510b240d448407034480d0040c0030000d00715000070825008000031903091202505021040f06e089500407943c0816203490711040781a200c0d048a40148144030f81e0038005000078040d4844400e00b4070880f001011080814000c5058610666022340f15070041c0070b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 165994838 1250 165993588 165993629
    0xa14030c04050d0c09110406050f280e01020708070e0402100302040b0307030501080d020f12070204151716050d020405040f0b01030c29030609100f0303020607030b0102011a04050a09021c11010207 86
    0x401800550b030000c244019410700c10444c50131036460308be103c0c00200d19250301000441d0307014070840c0041d00b60740e402804510724142c501c08030103c0c0548040d0086918014a5018a220381c04950142804c104402e41d06c0c1004003000340104024858030486000e2000701c243c0b014804075190b4403c1c11040010802960000524400b81d03001c100c0407a0320607960503001c0498842000910300500a910500c500440841601303805d140281e195681c00801040c0d05001c036549a40d04c880d032054060741d001a00b592a450b00602c031801c000703009002e1150110001007003260900d0440140c42e04059403480340201c80d141d481054400001124502c0d0040c0009540381c20200d40180c1d0010b00c014011545503074038841007010284640003034006801982c02c011095816004071700c40b1100038402045180043d2902501c1070580c0900b2600c595110310104072025190740080e103242d50001c20305001c1c4e841081a11000e51344100b0f0803a0b045550804180081d0b001180d041c04981c65001884414400306 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 165996088 1250 165994838 165994867
    0xa020a060506180a0c0e12060408030406020d091b060207050d0206280804020102010c0905221d060118090c030b0601141908010b0a14030c04050d0c0911040605 70
    0xb024541c02040e04049901451240420203004403007581c00003c3d0301c190000024180700d101300030345002c2c0b19490010704800b00d0008203554495085102c00340c49466620f09100a80f181c5582c5851032400d03d002d880a002340c140003142c41a000311140070aaa550f02c41c10703a1100f160b482103541c050858102d610150800100820702444016807002000e11095410480d0074414105000051582c02c20001196024451000c03a000242000780034103140400003499810310304d0b5140381d2041e0503507803c140311606d50444c120084011240350b80070035007520340c0c0742d0b00c1c84244a544141e0f04500d01c002c0b410b101501c10390031055000106070010301e045454040e051440a0301300c034108103503030101c000b9184401000e03010900100d00944900c040303403203000340315080c107030000032055004120b8031040ca0340140346105001440c00c095620781d6148101941d2500940e4005500311401c148403400700040e5081d00002d8598403201000401e1401003c80030328041c50203a000403450030030944440341c1c2807 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 165997338 1250 165996088 165996091
    0x6030c13020c0102040609030c060815100c0c061713020d030507030c060501150305071d010c0f02120f060a1107020f1f0806120606031c050d0515040f020a020a0605 72
    0x100311015141541c0c1e80303403060072a48a03502c070000040310781d04148201b00b00240924002d02003441c09254504000300100310304081551001d1043c11803050f11000c0c1030007040300355040d0b6003142d0714030092036440300013411780c0c14081c42c000d8001442c840010100031710002c0f1150320b00d8010303180401450480e6400d848075031029005400307020405803904000358050040a01a0281c010442c3ca0002e0414026060300c1000d08440280804001e1a0a0a040840150020140034600154402906d040006030b130181c200e4061341001c3d203112194440b000000f03c1a400c5421202110555503c1d40b1603281107406907040050302d05402c204502c090302d4114924000e001c001080b400659482c450700c0d48030f421a2142da60049203c0314100903191502440750a0002c000710b02406407440d10000186d200d01191702490840000c0ea08446c0404e031082094403c0c44041d004100940c2c1050340795100c0450b011501248501c1c1480d44451020030b00340262048071115400a02c2d0201d40b03583c811000c1c120 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 165998588 1250 165997338 165997369
    0xb0417040f060306051201021228020309010501030506070906120b0a12050606100c0c0b0f1306020c090a1e0c030b0402070b01170307030207180f110904050f06030c 72
    0x80610000c50303030501c0c000c45440101100e8500041244c81c200910506944800001049074810f2202100c0c41040e40700380c950000c0403501c201c0d200c41c03280814003105111260752000d02031000c01000041941540712a0590740140e0071a01c695807500f108039116002405000c0019081d00c08000102041d50844e040300c50006009021164441203813400a448501c000d45041e40f010702400030a081107114104240210314003100c1c2c80210340c0307034006a9205031081821100b8005541c100541005040d00d020280080540208603911178000b580c2d140f00035803141c8180346060210f04401c2c840e205807403260000b0358a0a06c2101c842665000030038201c20903009040d21011680e885075540e100805203944911509080395040c904080701c42e0640c1284c5d40c00c2644100403240c0442d4000801d401101c0303041700300510354510500f810001d80088189100300500300140b05d08800014000f500070020140c400704103e6a510207015440715080e251030740c140d04519002c030804d050210013200d8909 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 165999838 1250 165998588 165998633
    0x503100b040902091311030601050102121e0c0708070b030708070e030a050d0504140d1109070509040606090e0609010f060e0d080406050301031a0601080c0c0f010608030a020709090b04 81
    0x24503d8010810840e07007211059141c81210240b01e080107070031003c44e41e500340241d00521a660605001075a039a8002061019203040419240f9001d20380c42d00440c00000c40e114041d80354030f0301d02a42c654800340350244948070300034154085030240788901900d201d140140e46a4810341c0704e0345e070251a0b15500c9039842d0741601465076814042041004502c0803200c507a80c50315661480c04040128110390212020f100d441141c0c3c808000c01c0d0340700360b442102c407012500740390380341c907503c03010f480c240301c1e103405203400034241000001c0301034100c00000215120300c14020501e546030340c01c00081800c240107200b4814001c1400340000c81c07082c500b8006420001d005112001141d0300c03070700c205070480d50002e0300180340040107200300f240c081504094900c102c0100c05050412000113890201c00a200c8807050002092101944800b0494401440f20700c2000300b00b415250308029071280d00a000e81c40c0540314000000035812882d100b15095140c11110b22900307511956225040c404078215200c0404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 166001088 1250 165999838 165999851
    0x20a09060f0e090a14071211040509010e3301090504052a0d0204080601050a050306070215040303020d0203040f060b0303160623010807090c0e010807030902010201020f07030504030b010e010503100b04 88
    0x540e400a03166000d0507182d21f0b4108486152004d4400703403507030104641c50028060008000c261501d04030107041d2a880e60a42c01705684031292504111785148840c2865031080c2800d100030310040c4a0605400d10a0366074060042e21001848182c81e002d840f552511034200000d092803d00c8280d0f002e00981c0314281c074038580301000d1101c00aa800c56005041c4075000b1000401051408520321002490150080c14081ca00301401175203c01000c140b1811140c28800000c0801d8841e41c111007141328050350071034072400c19040c000340307e00c00803000300c07107036460903564840c103160000079941c1003038025001030001d00c99569040090701d13140820035000c0c4510000c09074682c054078495400b81000c1402403541c20701d4102442d041d15220903142080c4000344c100d41071140d0b4452820750b813000907400c0101d0305403440d20040340203120704203030441940310202e8028101688200148126030044010251a0b600d410034001035034406c0c414258160310000824096110326007201c2481d200007040020034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 166002338 1250 166001088 166001111
    0xb1c050403272907030c02061209010218030102040b2b180b0718050f131503030207080c2808060c070203060708010602030405150c0a0501020a09060f0e090a 69
    0x159415152040c80c01180322200b030004107420381e180803011043d601d0566804030707455010280f6204060024040003891500481036441d0102102c0ca0900001e11500e0585802070071340e07000390003040c040155491061904c02e03044c41c2c140280ca0035035981411603481d109442d60741810030b0340c1c94825200100c41106610b20058820310952291a0f0b60303145415010102d032900c2c204a903002440381d41400a003004903e20060051400019524103540714104040d12800065090503d000000c4016040c01180c0001070740185441c1c041700d02c2170702240e0025803950300454840e03811041440d006010710410400c00c0c04050020306440b084010349852441d00e64a0385400c000d000c440c0a04039050005c0c42c0c50460908000b074942c0a16a45041c000b65410044001c0d101d1103140724803445042c0030001c1c3d5441d054110211104c003201c3d40c0450340410403a00d80360340030750071140088000c6041500000b83e4140200740305017013501c0303c0d540c2d80304200c2d0358810810207640152211508030343e204048000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 166003588 1250 166002338 166002377
    0xf2706030a0e120f040509070503040c030201140c0604050c03070503060919030c0c0e0105090903030f06040b0102010f05040c0602120f0a03020a1b0b0405010b030d0e040207030e03030a050d060b1c050403 89
    0x703140c43c01380090740d540b801c290a001400f0805896a42001802c000704000300b0009002c44003070b1b0b0340c246003001c5005548203000c2264011260405041d000b42c5083c001008000595042c041b50145e0035202c0d65660750b010140c03502d00841d500185c5400c600e400c04894102c2a160174000c6200781841422804561103045480505401042501c200c0000503c51840c100125660000f0220011855440d01c5120380700b0424000d0501400341d03445070140425a0b00030741003645481d00c6084200302600d0700e403d20034003102c00c900c40c940142c0030300e042c4c80400c2d46181e401c179803198120742c80c010b00c2c010384854105c4c002d61044a8142c20401e000004171074a000307040c1100d05a5008200240040c203103428154210f444100d0458400c0d400000f1103031510b0b4210701040702c100011100161142c0090400756170756100303290400d505010025501e8452078121001c0d100f0303e480a5802c010300c07601da020540592280e40c0c030b40b6003004000889000c592940750441d03075000e48685851080240d10008496 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 166004838 1250 166003588 166003597
    0xa0803040605030709090b1e131e050603070e0115030f06080a020307060201060f090510051804062d20030a02040918020a0312090b0f2706030a0e12 65
    0x1400642d0000a02442590010003280603060400d0304028604901d00016030200c11030004011540280201521955030395580c3c1c00b000381d02041c2448520b0790b44d5482c0e070900e9069079076010407520b0800800d40900380044d2440a0303030b811000c01d8503140d0070044010a00440310740000105529118440e40d503c90a001d0340d0000c004800050481c3d030194410181803100c144c1040c011a071505c407007004050342c0140030808680f41000c0014881d114014840d42c0c0000541080e034000521455400c0340750080e5032640c2c481e84c05110200000541d0440c0e041482c1010001c5000c44115695500008242540b002d02051040e541c4040300000c0c032250b210303c58001f05d4003880600d40c0840c013000411214040c4400c0e010500e410301c04a03106070360004031551800e0202603c844083da20f6402054002c040d040042e110428007070b5100c0d07141140178515a07000100c076041c41c990034100503000034080080c09440800040445087d0743d81c1026040081c0b8141f8480011317403240030801c0781024a080e0091 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 166006088 1250 166004838 166004849
    0x90f0b040201121506030e0102091005031e1608091504050304061202121528050a06050a0c02091e040f03080106091206090309030206030a15090b0307030b060a080304 73
    0x84018602030002410b10070003c1da5100c20786007010b524000589060007a04151205410700055207501000428024090301100340c1d000305c1c1c0c08005039421a00000518442c034848400f00c5600d0056040864640006981080e00203261007850861140111142075008200500302c41c0070740046031701501000d00a99041d07407903800c0002e0038004a5802580442a80f0501c0020351030014418200c48111750000d10901404038004409034041d071361301e41580d502c00c5030300340440868081c0f09107000d504c20080c403d051085200710380002d80780b801202520010742030780d128864003260603002d218804d00d000300b0201c032036001904000d1181020011813030255006103049407080f030b13951034041e2240c201a042070302070014200080052004d02189451b06541c00013011619103410314060302c1e5485660002035200401008000150724540e0184401c0701800c0c00350404c250f0b86804a00890310003242841c2c2582000000b400403c000d2003045400c808040d160460b20f658030350040d070440c0c1058011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 166007194 1106 166006088 166006103
    0x1080610091e060e0108010302030a030804080c0d0c11040b03120708040b0d0c030b040b130207020303090d141b0109031203060513060518040209060d06090f 69
    0x360790080c801d038807405010b0003104101510700901c90050070002807851107420841e61003410b020781244d0b0003801a001c401400c0d00e04843d150401081038810300001c200c9100588000c00c2030071000c1c419a62400700c589030525101502c06484c0412501c030b03905001d83d00302c96035008240c60303210415407034843e5900c1e0818940700360b46020b071360f02c403004981011800c041500354a4124036a00d428941c0c003046041940d02c1040100c400d94510190007400c42a2000e08003131090b4000e0009600003030071603040c051000005402760702c044004a030090100c0c03102c41b0311101c0805c010000e03c0002c2c01905c4480d45c041000030f2140d825840082c2110140b42480e481c3d050103a408040600b8002c0c04413500e211106400d80050247c0c2e1081758090480100c5111301c4240341c2d82014003071a1b00904040c1e1580b03418040100e4100c612900b0b580440d07031074410b80001340c182410411340d02c3c4a1200b = true := by decide +kernel

theorem cover : BRFrame.Cov 165827338 166007194 := by
  have h0 := BRFrame.cov_init 165827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 165827338 ≤ n) (h2 : n < 166007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
