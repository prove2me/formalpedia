-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0265
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:51:09.37552+00:00
-- url     : https://prove2.me/submissions/7a3be496-c6f6-47db-93a5-a21778466bb9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 47482018 ≤ n < 47661874 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 47483268 1250 47482018 47482021
    0x3050603060411061605060613020c0d030504020301090210030902090c03060a030b060301180308010312020105060604031b1e03140303060f091806040308150307051011010915021b06 80
    0x82035480c00000c00080603041c0109400f1900e40d20003060f10030f021400303050240080340510b841511140c0941d03003240a80450002015085035600a403944011080010003c80c00c400008402500004e4001c1e03130955a50307001c1001685580c40280940581900c01140781d102070f10610003500340090006607542000d10a0128642c3c844000740c08803604200e0140860700c0f40c030b00207401441204200111101c08400d05810580c02c17909060403680600118080901403840030307400e0b078104031030055110b44108414000074401403440032601400009104425849040c40c150384e0602d24010300d88140000b01c204100405004060404403002c80614158240040400d551504654180d80b1a522110008049007040c01000c024030b9401001c594042c20f1a09000d01603e00c01c0e2030024080359191041141070500003070810407100007030310700c1c441003900c070004865205110402c4025552584c2510011909040c8440141441200c0051391030b45100903210300030b035100d208031103580c11080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 47484518 1250 47483268 47483281
    0x20708090f041406010e061201060206010501080708010303080c07050a060c020303090d0c0c0b16060207061509140f091207140106080d0c0210090e090c240d0c09031a040b070305 78
    0xc0f50550841030a080c14240b5411800c0024494025107210070400d40300d10b800040c1c0d2540c00105039049903001e898004031a1904d05080340c0b00002400040d011801c1c1d800071610310701c000c40003401400d000e0021b6410340b441c0c035904c0806031803a103008880182d2011041c07050741803042c001c4076040300c26403d24580c41076036561006114009886204880c2c5c00210307005041d80d454000c5c0c0018030740c4c0144110354034043d82c50001c00424020b417140d0743c5c1c1c007a40c10011603a8030b40c40c030a03003e03103148c40d0800d50602c2d41c0b031144002c80720200401c4241179008100d0411840b8041001a1491902c2a01c0e00c541d01a40908042c0c01c4a030b13203503c0710780950300100500120941203281040440e4064a0f1041000c441c10400d90707550703400d03500c030300031180400702008815000841d00e50f00c46070003200ca5501c0c0d011102c00001c007280d00500d0140c1d41e49000c00a441c1e5940783c0381e11401c03801101d414148000b595984451041d04451003041c40c20000100c108001c000c00000f0fa50741c031111f103050800142c10f04c203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 47485768 1250 47484518 47484551
    0x61e0303020606040902011404080a1506060c1101180b09180705040303030c17071d0102030c0c01050702150703020607030522120c1b06120c021c0909020708090f04 72
    0xa040d46014170390383e48100b410340e4031900450480b28002d50742d2942e00c55030348400300d40e81d40c046801130740c58400400300c01c0400800d03402240102d03007855a607028103040c05c1d00d0360302c9022000d0305624103004485108110040380394520f000206144100c2c80e846812490074464049448440703540c0c405040420800c5094214040d82c00350381d01460000340c0c520014100355008906004e82600c031038801001c011101d580242c008411a00c15408031194803405c0c5c2c016a500d00807031300c0b01442a000400588078551141c0050010140020422242d03809030903207542541c4e01a00c0c060780160020b40411050b00d401d806082e0300101d003a07511002c803903001c911440400050b508001c0c00c080c0340600d00245241701304101d0800a40251000190582c941f801100500c42882408040b4244405520314408684100c5a2818030703078018100c2622110a61040131619460304028031802c80404110200caa1010b0300300c1a02c00c003482070b86c407079201c0d04200c0722003c2017021510039821b2a18481410000d13 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 47487018 1250 47485768 47485771
    0x603060b032d0106030c0e0405190305040504090804030609050607020d0c1106030c0c010507030608070b1606050402031903020a0309050904170c070b070b01090b09010305070501050706020d02030a061e03030206 92
    0x10204020389140c2d00b50721082c0500b0380750b8001703010a0008034001c50190001c0841e40c1c0558842d42c04c41d40b80201e0072117100c0e02c814120344042d02055091000300442c0c02d06800170f403e03003449000d441d0b260649a0ba88c4a0848002c42400d40b0f843d40b0140070009265010050401ca80742e85041240f4035858a031340d081244280705895034010788021012558404800c402e41c1d40309031003a0000c0c800d5191582000300204001d10800e2500c2c4241d21000034000707402c00c100d9413408006000c109500da01034581401902c1d01401c100c2e010721035070110f45061520099000c4901d8400d80c090300c80a66907080050007144117801c0603110f412010103100008800340d45000d01044041345094680d000d0f141e00c181842d0455001120b0140001007003420043c2000401e0305a41c141442000303002d09141c2804900142408001c2c91640300030018000e40d8082d41c060500c4500c10b400c09440c041142c003507070090340c0041e42c4008045403505814410b85a042080e0301c00040c103064840b00261842d18020f558190 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 47488268 1250 47487018 47487073
    0xa050a0f0b0a0e120f01110c1c05070203070603050a06060e030a0f03090f0303080f0a0e0304031b1a030a060e06010e150c0a03051306030603020603060609040905100603060b03 77
    0x300010309091640c06480c58103d155070090000700c03002e1800011649910521101345401d51921031041c0d00070392404162904042d008004000114148804c28484407801082005004081c4004170040e07508102040191895990200d5641801e280c40420703549160000e00a01100750403180c00c0d80c078006240e0142c1a04403039003c0091802e801c0948035072215420480f000e40700c90f00044145500040c0c0c060144101044444d456525191030104a5050003010703c80c0e074104020070004610900e503500241d1007594426001255200c1390f0901c100c08501411414070360101c1002580c0004c0e12a0000604140075411040d28015000800c2081e841080b984600c41612044c1921014001070f109a8868074003158820143d5007005880341d0000e1040003030040344c1d42e00109001e071007401032204599014101ca0704586a400400c1740981240288a800507a14048003021500c1001a40c10413281c101d800a0040d04600300001540d1081c0340c0b040c001d521042c007216101071a202204c82c400c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 47489518 1250 47488268 47488289
    0x607141803010501090905060f01081507050d0516111b100c0203010c0201060e070f090303050a0c02030106030303050106030c031404060b0d0f030305070e010c03020709180b090c0a050a0f 82
    0x90041400c6244040442625405610705000461032107211740c48000014090000c485080d608d0320a0095041c0302402845015005641281070300e03c10b1030001c2d500110706051590504403d200c80508a034400c0702d0404044000c250710400c01c81d0002c40c00490201c0c4140541445800036800500f05941484c80c140a16180840d21640c50b2060214081d80765008000f44032001070810028040c004c9401501c2010820310007003400d841c0a030310b528010f00c4040c0c9030482540d01d5510180c6480d04080b00c510203200c0504903550042e9021702c00c40c0c000d544a03440024240d414840c00804450402c0c00c000103052500b0714032544103c40d030341030b00d510562180c008504600700801003810140b442d00c0c000c091050b4180c021042680580021340310310340f240c1e2003181051002c0b0045a00485824010300943c014000c01e06c41001c2d540c0000400e540f0340d0300559482d100d41e985400689001301c619920713503000029000710034907021002c0300041004860340d68503207007041c4208a151425201e0a90f440 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 47490768 1250 47489518 47489527
    0xe010509030a1506050a050307060e0607110907020703030801120f021014120f06090c030609040c0b130e06061c09020103061d060f01021c080c0f04060c03030608060714 74
    0x255410003400da81203500c652580f8030f4406030580000641501d0191720302c1a040401e004c030381410001050f504451990b6500407510882c8000c0c0007840c2c1c0010025928241151000c070b40c16211070b001e15000340c106d0303402001610301c0c5080c010306075601070b00b01d000300075801c445810119100b070004109450701140d0110700d170740d030704070f000c1d541c2008040301d1400070314002c2240c1180d403d0000140d0300c180420610010302e030b45c0b4001003200105040700c40111503035050010a02604003c4144c45e0f10510401c09110101d4444401c0b642c40d40180d4450580095414010320403008440440c0e42c0000b4142c0d0b00714200790007199041010b925042a0740021540c0308142000c1d603104c0c1d0002401860003880204c0000600c440b00d0a4280e401c40b0001d026000c030300c1e041c03c1c440d413000440821001ca03060401a00c24400c2c00304403811080038200001c600000d003c001c0c81130003080000e100821340c5417a26070101403c0e2501409a486035803216143d41c01103003c102035580c100c000b406500c1c8116011a83e42c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 47492018 1250 47490768 47490787
    0x61f05040509010e0a080c06090105040b010902090a0302040515031924110a030f050f0c040b0901110f060603070b040308030a020d0e1002030711010213271a090c0306010e0105 77
    0x144032110b4040007a1080071710700c0d024046150300520366180c0c8941607448664410b4107060a8030760540d0000c015005441c01081240c500354046e0014000050a0000d8180d8a4002230152071080c1d5007040780c03c00300d1440200a14080000140c0d018003882400110105a180c80c5264021407003250280341c3d6410364a864410307954041640a007428031041d48901c0e003c2d2008008110306140c0011003440d110228850400c240c0d0628030a000c040701092505007400980c80032600613589540c103000314140c90504028040c0580759a4410303400007000e440c6495000c1520b445020b80c403c000c1144100418004070f0341a408581c3c0c000a403d4005d039031090404013000042c8a20141c10380d030341c0201c0c0c00101c2961040d4004601928003980c03600c1c0c9100201c1c5c0c005080384a048114003c0c503d201001b002032031724442d9154904690001450305040440814030107444180c0c0c0031050b680c0c0d10038070300c030401c4c902241c0c04c5030400341550b119402c5280240000e0000c2000341c070007a05010011815468 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 47493268 1250 47492018 47492021
    0xc100f1107060309061109130f020405040203010b070309050d0c03030311070503070b0105130216020f0a0b07060902040c030501060804030c02060d1802030d0503060d060504020f060a02060603061f0504050901 91
    0x30625004841e5116a00d41c0003d004014030301d001c580940c207040701600996080410303180b0710400240001840386403001850b004040e5424103500b1107400f0300c80040c440d82c0328800303107000b45485840a03507588a94a001002d66540340c0140f072240d0030140291001c01c170070000420960340c0c14140014007044d05203c0c5103d42c0141013004000e4400050b0100030802c155100d80e04840c1d09132050804407101915003001d80c02218000c00c3c01d0b41210010700003520701401050f401c0f590260a10b000309854501c00c54503544039000035541c0d95200c1034010210704061103460032905040c64208027650421000500000d0042c00c09000c01a2040380f200c159501c2c1d01c100c4d01d01e0340709110201b0602c1c1c40c8605a003000805040306130701c01d000d500340c071480f000d0040b011244038150041445648804998492000b058003420590704810a051626040d445034402024501c0454005200d0f034581501054981440100304202e43c030080074002001400c140d4028040e0352013182c3c08a0b00e99034108843e030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 47494518 1250 47493268 47493287
    0xc0f031e1503070503070501210207080f0301030c120c0302010302070302010b06030a09050f15070f140f1224010e0105071205071a010608070e0102010b03070608060a06020c100f 78
    0x3031084501006000c915010031148428038a026001e80784520768400806881314200e1140c240458000000320041e100c000b00a90354800344080300609001954440d5600d0b90030904000d00d80c2c26001005106000050550400070151449090700340d481560f00c5038140755840c8402810b241d00418024201070007908503041c6500c0c0901f001da12850502460405043c920b04140d03001e0040b0100c0c1d0a0b150000300781c520750302842026040036601c0d1007a0440320001c0109600007000380e80e0042c0246c00915000404c1881170350140d142e1580b1856407000c03500c90025207226000050200f07205820007442c1140e0001340800d0805420240b00e8074016540e512900e04020401040c6401c20311000ba004409810b00502900e860800c1c11215080031503600c03403e000d07003004140d0450000b088107108100c411074407901031002103280e0254102180c40d00045802203404540d00c0760401005080c400c002d07a0041444d880101b0110202e0400b08861700b140751801002c01a0f801d441d0403089000d42c1005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 47495768 1250 47494518 47494561
    0x17041a1003050a35040501030608030906030411130603030504050a060e030a080307030908120a05100806010b030a021c050105040c05070206040e090106121202060601080c030a0f0b03071215050c0f03 87
    0x245020031044c41c40700c0f142d8040c0c0030340b0340030928001300071608500000c1598150440a00b6030761a54403107413180040499000009640304d80d600f10b9003501410b0314080c0400a40c860f0b211141c40b28203050030442c1d2000c254210404121020440c5111a0b0b000104c2009441d008610b095807070b1685a421005040d2041d07002d00303440400070301101660b20031948a84035800d4840104070f1600d541001e500d00720154801e0300c005a001030014000080e801c0021a004200040010700e02501c04074030301011240a50401c040644d00d00040040e07040602030190a80054905030f0300d800d01d55030005109020381d001e0224000c41442c001864244254410005440b60041d00c0d03c84c038005203800c405070140f005991005001b1080070800c294044d01e20940180203002d40c0c41c1c00d41e45c56110310402410010200100c6a80742c00401e64251401c0c0003000240400c0c00a00d0140c040030300340102046030081105204d24500010010131300d0200d01914584e660351b120095481e101c1e006080315466a8040d076 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 47497018 1250 47495768 47495843
    0x503030406090806010515070602031909030f0207090c02030409090512030f011e060c02100c060612030207080712021002030904020a050408010e0607021b0117041a1003050a 76
    0x101d1816045000d0400711031152046034810780e2600c09014621010303c01c80d0b03a000c00c0520444000072314071380181d0740c0484a5030341d0b004000b005d03298000c280d03500c42400354040380104010340c0702180d05001c80405000340800074041581e400324025600e110300d00c2060800d40e519003944003001414801c13a0a0f0032040c00903241c6a0900e41d24440d1815000c2c403844040d0070281d41e245008000240c908800c45841c1e0715802c00c04400b170307000d2102e81d04c00301c1c4071103080010500d400400691984203640181490010060110b0001e24010345041155044800b441c2c3c0724201c00c111002080107111011541540c018105030b910640580c03a40c010303180d21580c814004207001c400180d20602030811034010100a2290260500f00b06443e070600b501c45d180142c100151000b40c0111032074440708103000614000c1c1e800072071a652400300384400c3d07138216408062000c40101050070384080b541c000e84080c0c03190f06054030710740c0d410b80e8030408400000c181e030060925501e0665141d61004000700b900c0b181 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 47498268 1250 47497018 47497027
    0x24060a030219020703050c010f0c12081602010212060d0201020304031e020f090603060414100e030703080f0108060708101502070918020f0f040608030a030b181e070504050303 77
    0x50041d411240403400303410b40440000180d14400109101100e4106c800790030b02d425000b00444d0000c0880c5100340034400c80310011000200c40340a02ea05200701941d44420506080c0e101c1000034003500041021a0300600c00b007160746114104064111608440c5400381000510060b0f00318060383d440607000851a104082d580c51104078840d207858403c545d52405102c00368200202060280c65558160f4000800200040d6500e0100c000c0c603407200c01158080d460b901c070200e05940c0b162076152400d0304041030340d0003011340291903950013010b85004c1c80d2040d03040c440c14643d9180010240b6040003e01c801280c805180c80041c4405040014900c0c5554000b2841c00795030b03805c107032050b00d14483c03504050707103040240c0c0c401d40301c0722540c018080c40c00d80328580108007800c050715501a500c039955138070000d030783e010030401441c2c800d503651030200d8044208070411410000030740581d403480c035080082011034105001e52420161490311125010388a00c003040f50305010f15000a81c041c4070004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 47499518 1250 47498268 47498287
    0x1401180909020907050309030d1104050a06020a0b090703030c060c120504050609060901060501120209060c0118170a05030408030403090e012d0803040333020a0806040b03062406 78
    0x1007100c01001d009a80408050311101d40c03c440b0ba20003160048031942040c82552089507140c0c01c60300300007002c4109a070910b0f403204000b40498403250321100159000403001c004100c2001c002d2944a002e05c0081c0580a2950710b024004400c0e110000b410280d4440d00150f0041c001c4180c400c462004c914104040e00c1c1c40d1400b556500c0c400da40c0980e0300c1c13140c440000d9000340c050080708142e8030182d5601c40a0103984d00e50401a4100a4003030351b01c2081030000c5003440509100d820380b10302a14a1b054801c80f201e04124904030001c0c51010b090300000c104841e042030300901140d401c40e45c044d0580c0e90b42c2e42c0d20308045030040030582005040d4808040001900184850340c00f4208078844040e00d105032929081d145c04006912842c54a500140b0080012810494072101d211043c90305240900c00c174103030b004500b0200c1c240c400058030741c04250900410303403000c1d03000d0f4804820740b8100300d10647c04000a588140040105015280a1094192680d03108003802c1300440c002d03100e07549610111 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 47500768 1250 47499518 47499521
    0x10e13080a091404060f0b07061b03090309120809060304060e01050c0c0d020610050409031103040b041d0f060f03010b0d08040602060c030103080a051608070605070e04060b030114011809 82
    0x500c01c0611290070400d0f02c410314030b080d1080c281102e160003102400c1900e807080916250f0884241543e640c3e5079080035481e40d1105800d18a24484180d80000740b101c0e541c5070207840c0c00b0040d0025155040c0c0c0d19a0348002607118000c03202c500a04071011501ca0741c80d4030380300000e45aa441c034410b0035402c010501034004041000b504040510000ba02c004503602581242e4030a821900482c5041a03ca82001981042d40c49482e20900038075105c1c44050790211090300d560702c190b011f441e0000000608100c0c0402c0164060001c42d40300103018124140141d0b00302020308090112440b46c03500100300c900d1070b41c00754080004403034003501404a800160604142c660028814040075001e0000080e03440b040650480381078030740c0b00e8040760801440080c00c48264012003d08400d076000400000003180405025014403403040344081a5460540e000070010000841c0719400ac904040702400340d44d2880c01640d05507031081c004e40c0300303c03101c00004942134031201c0004410070440c0d0344041003190a6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 47502018 1250 47500768 47500787
    0x12070c03051906110708070204110405100e011706030c0411090415090509030304050303040803043e040c0203040902160803091e030304020604030308040c0302031e0106120209010e13080a 82
    0x4100804c845072011010940790f00c910307400105581d40070040c02c001071415600215043c150005100d0900303440d4008a01250b1080c2e800e031000c5000c407404014590b9003e8062559000c140e40c03001c00750b00700080480d9580c2c1581c0410b42c80340e51100d5929183d041c00509a030700c2c1248c020300904c8010001c0000030840c0e8180c5c05500d50303450401c00018204034000048a01450f0301600075861076407107803119000344e040030b00304580e03a107030b40424041b0b4059200e425031a140404c2040002524450f4140032500d081804600e0055080c0b0f0588821641c0102c256003c07108401400369480034111160820203616600c0104441c1c0c001c001e1240200001540d8020300064000c1242c20401106030349a8902040390001d40c0014208014000648201380040e00036109032224490301c2d450b40d001074181511411215503e074246d11500340d00306003d02880000749008021400c8400072600850714546050080c6003d05440380e000c80c014175011101f96030120780111805464038090b0b10010304443d034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 47503268 1250 47502018 47502023
    0xc0a06080601030908430305030c0412080d0b030a020603010b18120307151e0e01140a050709060e060403080c1906090606060e0306060907051b010c0801060203040812070c030519 78
    0x4809401000340250703c29400b035080b06d5014905101c0c0d40e50308030350541c401060206d40e60428000048c040f51003004140b241486640d45d10340380c00c00101c0203002c42d00da010b41a40300f075108064920250f141c00003128191040b0300700c203c2d640c003604000205c00c41d1141c02d0032500030744031701e00c44000c450001c0064102c041c4100c4101010340880101101561903241115810b0301c5a00202c11000f00194466149400c04c8000404c100d0071001c3c5106548108496502e2201c1c1c0310020401c603194001050005001c0c2420800c000701c1144001c6107680c041c6000042c1686800a08440700e4003041128900c919030701c040e1242189a9442c00d1005400e10b507101701d50203810301c0c1001ca0014083e541e464000000034004000c590340b100304000c4840c1000d8482d1007808810008002c2c0c0e80002030f900000c444104001003240d0790018030060420300160311807800c5400502c81804104c0000c100d1024480808144585070407090925958039541940010082c0c032404c505000c1700c0746c0140c540c00d410350 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 47504518 1250 47503268 47503327
    0xd0c05090708091b2b0b010605041a030402030c060408010f060b03070c0b04020406180204030b01060c05030a0f0212040801150b1312060b04150311030c0a06080601030908 75
    0x45507881d050782c8030401070f503602056800c00c0200721803148245420070100c85000342590540c002d01380320200148055802d0f502c0a241c0007080806024850100c14010803092402620713140c1b402c80c508103003610042c0501c40c1481c00001140565808102d00c0c2030b07400000744059a1a503845007194020a15084102540c5003080c100054403002d8000350313449945603464400901c0c10301d0703032108034a01c0010822a48555501804680186995140b080c6c2ca0721950300141e0721815400c012410500503400802007000303e10004000403001f10603200c4a01c013504250121088008080e4102941041480f000c5100400c0004004405400482074101110049d101094640300c0d002290302c0355000600c41e20a510340100807a1215444804102c2d0040c6400503c518040380020262181554142c410000d00d410500c184200c0454007414040c0440080132840f0760040401da5140c0c0703900c81d00c8203106044002803030f20b034002d0700038584482c1d2002c3e6269581c0c000210141c0c0e80480b10040c980b110 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 47505768 1250 47504518 47504521
    0xc0809100606050f031f060f0801090504030507020904080408010f0b120d0f110307060e07052704140109060608211305060901090e0a020417010b010e011209020d0c0509 74
    0x480c80c030803282a50440e99405140c49440b0705038040503400134000601e90110001c00242c0c0807424000c0d0000303491140c0c3d583d6689a81c44000400e1140182c2241448519280901000a40003801c031140c0590540740e0807010742d964203022500340650382c44a1907650070056003052413207456000751020102180c801c0000d0f0380d4080c0c815951140c0c0f000010100e001d0b080c144a4050084103480718a9842c1c40490f807808a2a0b40e43c0000c0e25041d01e00945980c1c00420140802e182ca955000507100504c181181c0498085282e1040900301800c003402c1c010500c15107050040d0301717401810046c0d8000405000322541c7e0004c06070b5803142241c500e94000c03c3d54519040800c19001101c4403102140e000c4041c00e41003204010f03440c1d2000c02c299041c01003003400010001003584449204826000005858603e070101d2280c40300d01040c040f48159242c024503584503a0054040c500c042030a203810760002140b803200000810210b00003a6100741c00c20f111404028010341c000060b00c00036104125076 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 47507018 1250 47505768 47505793
    0x3120204090207060627020309010603020d120809030f090409080904051e070c050304050411091f1d011e03110705010504020f101b08040e0c03060f0909070902030405070302040c0809 80
    0x1c1c0a4008204804044800038280e41c0b90740e1b0740c0165400248040000070441e58982c00580034110049044030002d02e0411501c5600e60401c080983c0704400c1006140761601e13403a085d40d01407095a401d03a2203165070380c4c9041c080c81880c4040d50035a0001a00410540c2004156800301f401c0c40b00c4490500000d94000480882c481c00c0c000020701c0c4c1c450700541c24030313007040304203c041e08a00e518070740032290501c101c20541c0e0b84c4030b9114417082c5211460035103a2980b180001c0581406444060814030443c4660586036400320f00d8110bc82d1203880341d0040407100c180304070007410103c40f40c2c40200b0008900c0030305111041d4403ca02441c400c80781d800706100b10314240070700a40070002e8940402d8404001803440395130406884240c910404e81e543c501758803034440040b20b200c1500c11020b051000310810556050210340415a07103800c440c9500d044c9082d180d65950b6a903507008051103103802001080030080f04018a501440e070040050160b80107411006002c070900b01d481441908c10311070f00448 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 47508268 1250 47507018 47507039
    0x7020f0f010612060f0207022101051e0a02090112020f040609050406240203090603040b04051005040b0105061b030304030309150b010c06091a090706030c0e0a050409031202040902070606 82
    0x200c0f80180980340800b030701615203800615136030140c2680d03203408002ca98016668008220043c001c046440c0780084181c40c00030f421198010200811005d8400c3c0b541c4030600c0d003c114035403203408070202603514022240105c0c0c4402c48803003203030006400030400548080342c110160054415540d50304150307075500e004000944081d40300d104c1c5696080454300c400080d281c40b410b103908007280100c0749400070001c040350f896401114180d82490540d01400100f160034084409039641540c4207101c9030604c0d446130b02c81c1c15810711559100d0710000070031509a00c59400008804d00110056039264646800d0103005030500d0201141e120144940e504460500740c030411081480c180c0d11086240c3c4078ce40c5900040c03003400002c0e2030902c10000e100b10001106070711203200750504e50241003110701d0b00c0c0c1e01606442980b10700c0414088401c841700301640790592100210380c0e0413500864a81240d04054030151100c95480c0241800060045070070f420540003049020b21403d42081202d0f030b940c003840c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 47509518 1250 47508268 47508281
    0x9200f070201050703180323030702011e02070305070914060d1a04020f030607020a030e01050c0c090a02040e011205100204120f05120c010b0a0501090b0a030e010f020307020f0f01 79
    0x46100512403680075501c0b43e00039140d0144a424821004065100082c04070311203503000b151080710382003181e50039800210f11140044800f00080d400c1444e1540040c005078040007501034500e0141030311160680c800c00140006503004000d5410998071089980c02825030080026007642242c002f0038401d00b0200f030514007660700100c605034461800204080541c0c2c0241c8282d905c4080b1652150300355405018440c017580642d0000e148045807403070042c0a10b040a881541070203000e00c209020808041408000484100e6401c506030303888a81e0704000f80500e8002c3d01c0c444a0100000c2601000c000c640d0387c402c2d00030021a44c007809044550b0082c1d101c0e601905840c6042950150f000a2140d01002c1d1110302c00c41c213a902007420141e8484c600d0b00040e10b40318190791a000c4220280c00d00400d03c101803c001e01c0e000f10140d0401c1007043d064494800e01c03404055440004200b0090203501054001c6d50a040540d40ca0804950080d0b90350b068120100306400b4807410405011030510824 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 47510768 1250 47509518 47509537
    0x1b0f01050702071805150411090a05190506160c03050f0c06040605090108070c02041503060506030102070807031101091b0503063301050d020f040e0109090206070209040204150920 79
    0x100c8108494540d1000b030140030780491006c01d41041c40d0302503a070311401072030700c80b0390107580e01920303580f10305e04125515a075230380500d00480c1e05011050103030740506408025217400352412651544160b602041d8045500c0f8003500c0780765078400c0402041030200e0300d40400441c0104803004184001e0402806104510808021820070001d8031140c2d4041e4131303e40d81c418603d00b811112400e00da0007290a450700c07842201c0c40401305c04000c0c000c21201d80300f01c9030828810360003181004580c1d56500b10074407840e0409002d000105004118bea07009400a200701d507440210142000400d081030f4107507841034090540329004420025016640040040907240481c0c0300c10100c0c0c0b9034007141c482130102119030643c1000800c1004081c4800d09000900942040c1c1007081c2c0da45107031403100140b0341d0040c0c21604d640c45c1401103540150346e4a000ba10880c4d03404451078602911a4400200144144201d020800084075000114201740394001c112036404503824001c01030700d0b244071401c588111486c1c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 47512018 1250 47510768 47510789
    0xe01050a06030c0c0f02030c0907090602010e121e0417010b150c0a080a03020d1b170c03070305060409150c0f030908031305120403080a02010c030903050d0906021b0f0105070207 78
    0x41c01145d13910311500384085c0043c2c10b84155001c50004181501e03421208680412150041001007070350921803410f25010300c6024025000060a10510343d11482c0a00854124595001c5403904071010840d00100310300c070100011704120140e01400785c0b6094403000c0c0302e500c004110891951400c800c0714510642c200140071420703942d581d1801c00350441e84a460030154280300c81200c0d0740080c86209501c1d80070898550143c003020400508007440d01007910040d207018028407402c921910180ca40103100c81c2004990313a80d6a2003c64018205600040e100d88a1a1940d00304880164801360494207aa60381d205024401d0200b80c0075509003040040071484100001035249400351944805e051040041c2c510114801206d01c05a400030b42040e210707070790002804031070181c0901c9001d9a81000742000d0021500c0c688002e8840e019a1803070403500c42e200ca00c403900704074182e411200d511190081442d0340c4800700c0c2209998400f0280a409a5860000454040c900024580f422149600c40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 47513268 1250 47512018 47512037
    0x5010302130e030c03040303082a0a110120030a0e0c060f0705070504090305130807060801090b0a090f060815250207080a0b1509070e0f03030706060e01050a06030c 72
    0x141c07200401a4040307a4445020034010000c0c2c0307a03000d1000f4802140603655055590a00030009000015607040809001404445a0b8012000003085d910403001a041c996104c880f440c41c044d000d401004200032006c40000701904008441d0302c00340d800b034580e440d030800c18420141c185681da50500c440d455401041408242100500d020040c852a8070800580d60101c0d500e20108050b14008072088010030004201d07100344901580701a4001c10584001300440c3c1e01d4203a01500b110010b0040359112a1280700d038149a45038603d00100a1421130403c0024582c1034621384020b04850250070454010000c0ba000d4500840c3c0c966401503404941000c84000c01400c7c8420341d000b01d4280c007096020b5240002602c174014030441c950203000e101c0079841843c180070a110403070707940031007503106500701401e000c440c079440b042403040302005690b540b004c800b000000074a14043c0080040c142410081d0114000c00c601001c0382c1200d00030303983d1101d150346407941682a0b501e230320034041c00107440c0310 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 47514518 1250 47513268 47513299
    0x1061811040e0403020312070207050108010501081e090309011202040f05041d030c0303040209010504090506010509101e030201020607020d05031504090f14070501050a0203040e0901060b070c081005010302 90
    0xe110038a000c0e00045030398946551201c41040b00b050898064016800118000300b11054031440203510a0061014013251170074100082c04206040c05042e04000003100041c0707641401c0040041000200c0403a00b0852030080d080e596a070317000800b100d0009250f0445907104d01c0c150b0017501c0903036411900300c00c40c01b8181410310004101c0c14140d00010258010883c6c5603003018402041845080302c05190b89151034018441074080690200380039500d0126010003003800800c0d0141542c070111450391042d00c6044a0301d100000ca60010084451600c45241c024004503441c0d4040341e01c01e80a4a21555400350700341e840b84104a04500414030820016070f072001040b00a101c1070f840140b0000d540b4060791103141c0c685070403203011103404050101504420004215590081909191503450608400d000a440f80500d101d036840c00081e8001041c000c940a4014401401891102da0348070240e504004000d030600344a100c0850248410f0307807040415601505041e641c0250101c1c40400f29103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 47515768 1250 47514518 47514521
    0x41103070b1c0908120a0203060f120a060b190608040506090d120c140304080d060905010b0d0f0b09390a050a1814030c030c1008040302070308070b0f0603010618 71
    0x18100c4d03904004019a18080c00d12900c014018004c410b0016203d107448070621805060641c1d0452164251044600b042100040c91415980c2e1004001c5014031204021601982d6104e45100c0410120400400d0865100414601c41c0d03000d00e080715a15240c440300c0f182c8540d000307042c03800080c1c1ea004521003500380c243c0205e000a0b03240d281a45800303d8221008600360001c2e581160010400248094020320174003070b02005c1c00c04182c00f0046035141149143c2d4901c10510003201c3c807500c84c3c01039602819030380d00c08884400042c3c4030f8032503441d003007420103c6035810001071540d205c2c030031100c612081041e00c0280078403c11805414500300c5401802d4030150040c0810030100803410408000b80c0f4800000c030401410b40d4505c01c02448401c1041500703081111003994026400500c05031040d80c1d8824801d10380c0e0b140c40c240400c0f42c6d01e69080403800c191035508060040d03078000514404006000c0116803140302072344810b9500d91100b10805007039801520501b40b015803101d1900340b550659 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 47517018 1250 47515768 47515781
    0x5101202060c0f01050106030207030f0f1d12030a031b0e0105030103020d11030a0c050a1406030f0907030602030c0316020a030206010308090604170601080c06041a070812041103070b1c 81
    0x5800494044404400280382559802d1f084140003075000f0610314205508441030001d6896907080c420361b078500700704d0010074040e464642c41c041c0748007200e00d4150b19180c164000302c080418500b0741c1d964841d01d9801030040c0507000200c0300340c101c02c03a02010419104451080211105a44280c41c69103035800700100301501c040166401e4094010b000082d039810480b0350b042d0340c81541d18000c4c4502d01410480c1c00180c950000e031800101c0302c400319036940c6000c1141e920246640314103180e516400907584c030b4000c607600b006000d1807000042c425034a1912000c0d6201d1001040070304461207040d50200c1c0c89166030304c00100968070a4005200048101c00906281c0d440548094103040d6101c51500010110007101c10b550340004005102020b014402201d950009072645460546030280780000c0028503110511031540104400c000c11035980101d13a010041c035110050103040c5814000300d05880351081c1072082c802e010000078010401c00545941900d01e4144030300c150b140c0d42161029101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 47518268 1250 47517018 47517037
    0x9060604050703020c060708010f090209011b03020114010609080601050a080d0e01030b0a060323071d0411070809010e010f020d0c020609030f150702011505011809021c0510120206 79
    0x13024052032242960410507244168016070f240308003540b401c1c0c401135030700c00507070003501400d4010400c0540c00c0c0d0b002a05488c0745099946600194211414124010310714180382d40542d4003c140001a0264421601c0060b1030f960350070365491b45d9a40d000c000000b1800d1007125015040a00440c0c5210700846014540600604022400c00c1300b60b000154002999000300010a40d9540310940740150300d40c855502d0388480100d0160303070030a036401508100303110b01c00e410329060744640c035102610303142c00806001040100c6980c403241d10345000c2a050700220451740c0041d03101441200c0301d40c0f00781c1e40450103516903009030041d21074803102103942d2480403805980200c030800c502000d9450800000019052100180c20030480c501c0c030000000c10044c2141045a0402c510300e450244120612001c0324000d0038007010014184100d01020040350340200c038014070101d2410690202d1554007420020064401c000b25901d040e800842d0035514020841e80c00c800c220804014103085004105012 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 47519518 1250 47518268 47518271
    0xf08030a0f1d040e0a0302060f04050a12030f091101030f0b010509040c020c0310021306020304030302070608060d06090503030a0c03050c0909041401061418160513030203161a0309060604050703 85
    0x4502e011509030380041d0040d240e00e074801d03031044040c10303070500c40300350000c6002040c59114102500d525656141a04001e4061301c0c220703014541e25230283d8004085900b602d8411b0202054a0921440404501e244180440e0404000d054085a00c3c8502440d03400305851b4142805440b17010b0000401d07000084030203600c00c2080d004c2d041c0c1e070f08101920701000440c001607514004c07080313001002c0070141d01480540d0f00510003880025000314407082a00d03801d02d003440d00f03642d4800001701e0080c06c00e280508070754503089041080c403602000552041085090500c44040c403a4801c40440b0740446111024030010302c4002d0240c6040804240c000340100441c0003089103248510b42110200c0d4000ca00c440581400e206143c1452042c1032080320840c066060390340303003200601401941c000c03061401c00200042c4081107060b803141050103190007808079810794004181e0b1030b880341054050300804501c00520b40600307000780421240306444c2e1030064401d54880d002400702505010308680e0502d03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 47520768 1250 47519518 47519567
    0x41514090d110a151a03030412080a0306030b0a0c180302010c0204050705040e0108031c090b15030f030705010b0909010603050d1b02090a02071209050d08160605010f0f08030a0f 78
    0x1880e01c0d02c3c150061000d0880010301d540d159110380221751072000c0e0b42e03000740c00a000400c40104078045aa440c290003802d696034621001c80308400501094000514541c11041400001c5510780c0c40642d01528a4a0380701480301c0a84030a80f103014544002800114010b4110300103003801c6d04440e801180e40c0c2405400c164031200300e4240c0364005d8100c81103079440411481e25441c19904040c03406034130030710100401302c0329495811018600070600c0074900b0460082c0f52150318104000e10540d1414415070792200080d08e8828064066550064401c1c0030050200321180e4061050004603075000300107008180d0343c6001660581c40c0321014202c00545038a420780962174820320355100301d140c3c2e00300607920320007842c100d407500414104150820260b18014040d580300c1e50303180d00f0032641140c8d84e6500e5507007080c000d418980341c04d40f0040c402c80c1402e00000300f401c107032002141235171407001c90307540015102c0d02c55a41c0ca000e44002c1c50001581c410024520600810904c00e01c2c2040c40355000c400c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 47522018 1250 47520768 47520773
    0x60b04061412160807050304020906040506010c0213090302061005011707090b0a03090303150e0c070807080c0f250b0904240915030b04060e0304030b041514090d110a 73
    0x504000ca42c1c4040c0f03941401e007408005680600c11682c80004d40c20204c2c01c50800341c000c0f80640500420b554020313542c1d44041502a030281415081890b401071881c100c0d4868144000c01508505004602620910022802c0260340ba00350300c05890069450309030984406044a0301140c0113082c0d8000c0c8100448040b45041840c03005011001964501280314400c614000b0101c070100321001052a00d80c06051040880c0c50714a240c000003070020080d26a100ca0402512a12803100c0003000040d001550142c920008654440000001d400b82c4d05004180e0441c0344010103503068044000c00e185a0501040000304040c00304642c001c0d00010b07040d41c824901030740004c1c0803800303818940b120901c104032641081c01450800000060088070b024030b07594030310100304005407000f051a03072541c01801040f40c080054130001d541020098420b403c0a081c86a03081c80000288410f881c140b98a0207500c0d001004502e0003280c00c00024604018072003000c4800008940711255140511a8404003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 47523268 1250 47522018 47522047
    0xa1404080717061018020409090c080c1002030919330201090f061d0304290702030a020f040e030f040504140103050a0f02041407020c0a09060b040614 66
    0x1510001005105507400d05588524150000d402181c00380d0141c0200121007226818140440d004403680404020f001703400c1c00040d0140e9007205041c60b15140e118018041e24229000854400d0000c0c0c8410b03c0c1c103603041c00030a001031840304015a00400c0314a4030350605e40ea5400d958a5100c103040050354a8035161040e200402e005102c1081d044004c104120751300100075192850980002c00c0810f51071f940f00000310007c00d8019080550b2274104d0038007004858420b030002001c9505482d41c070303a216000c1c1082d001c00c800e80005103000d0818006d40894511044034419034000300240f07500001f907402c014902c20100342a640151302c034845a59aa04100050703e55084444007103a211428402803104851424a50303c43e03401c40d5030010408100c002c0f072001030380c640004480e1140084c500105025025514025441c004040c007004400c030381c0468a000b000000b1a407400b10b540c0e407813903084182e800c2c2d4080c0a4002c8005c12003044054003940281080a01d800041400d28034204090007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 47524518 1250 47523268 47523277
    0x914010c02090a0509010b060c0d0e0a031a0907050f0d02040203090a05012c07030b010b1b0a08030103022e050901120c0503010612020c061503010b03010524010503040809060a14 78
    0x6841c40d84981c00c0c404ca1701000e00585402210540d402c50400300514121a0b881c1c2c40190550306200403038001e408961200c09000c800f86400c441110b001c1c80c02d00354000c0c4e0310b0108032481714190103102c20102e09482d00c0310105c0d07180c2c08014600c001320705203902000700940c00901541028032502e01d038000014002c0c044c44c40456110720007810007006900c0f40c9101046034083d03012030343e00000b10500c0019000b07401782c0c3c1510800c5044c603880c2c1e0003110045d6400000c40c1c001d810b0600c6a8039005040280741401981640c1c400c1d00c100000c800741c1c0380d881e2020811161248907011658038040903140c4502c1c041c0416400502d402828811000350110803110b100b045800024000401803013180d4020020554042d1446411494000c041c142540c88a101400c2c0c0e2045855046205105a0b002d400804c0408c400500070402c0341404456080c0c520b01c00c2b85003800c00c14084c0700e415143d60080017624800c90700840c80c0e6242c503034448100324999200004807414043d0684030340c0c1100745020b0240 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 47525768 1250 47524518 47524531
    0xd0c02010f05180705150a0804050703080c2b02070303080606070605010b0405030c031c0f051b0705040c02070302090606030903071203020c0c090c0910110316060b010206070914010c0209 82
    0x214040324196071541440708942000c1d001d6203105a081d4106c5d80120211101ca50461a054246488500e05981040784aa1016180600c0841c450400d00c0000c81d12511181d460440d0305c085141c10805954009142012040560401c001c104040390048042607804140142079510348185550b07403000b199070a0300004c1c0317000c40110381840a4203040000c0340000c62308800400030300415407410b01e80800e03d82200c0342000a01094259107502400a499a0349540c2c0c0c02032050202c145184c65a9107590301c01e5500c40c81c14003800c0441c42e4000309940c82900d4000d401000195222814404503500140110f60540300820524011510320180b5483d0350149d95030240e55281c1d1b2018051038110444e4181d0b02c80c00c401c030140003001200308102c0700d80c2801941ca0300b00018401c2000d66050000268046180c0030005148e29100b5003d52102c400e10701c5000104205401e030300049030707120008c0300c400d00820382e400028403070b10308140d00700c449102c0d051600c50340400c803a9000c030307419003825582c2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 47527018 1250 47525768 47525791
    0x31908070311012706060b09220f0f05040c0501051c1d0607021b040c0e010c0606080715030e01020c0601060c060209100302040e0f090c101e1110020702060d0c02010f05 74
    0x1413081090034050b00b00207100b820300e860f044c0403503d00014080c0b94101c00c01c2400714449010f00c680340c04180c0201c14549802103080200345044100c01014000444048608200c040008140340d809070b4259401c1805981000341c1c4481c22074180801020355495600007801761a100860035842040701520610541e4050f11b000c6500c401005c4401d0b1145000b50301c81c604240a1408090b0702c0700f0031070303112002481d1003180d685a03402c0100060400e03400c811458044c0300030215607032840100110074000c155a041000e0030384488180d080380103081400c00c0580007403004200c580c1c0b0030302d50344000324003900c0014a04001c04000456401004d146e007c007103a0041030402815440c40800d070351108941158044d545042d10308191680d00480429215100305040958a01d1140c42c0300040902c5590000300c4052016030051704423024a020510336119040d21032219003418000e40c2c1038642d025090f41d040180e0250383d14050041c84038103d08640d40c07048880c585080b00e0180da070007000078881 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 47528268 1250 47527018 47527091
    0x705010f030e06060402090d0f030203190309050c06130f060905010905060a021002032809020306060d0308040314090303180301050121020d0c051206010503190807031101 75
    0x581003031490400d19080c107141200401181d03002045035603102800311001031341c411906000607604440324802404a000d000c510b03801b0143c0001c010000e0409010300d8031101504003108409860208200400302d4119070350380070302424900061702d5038600310110455403588800d01581d001d80181d000c5000951050010000e46d60008044400340c036068440d0752801400d00c07000b9540f0031480000d254402c0e400000a03014245841c040c9004581010203545c9810000b00050064140524107a120340200000f18120b03203000004c003903907a545902c1e21055503840c0d40341070368640001d0f101000700c0041040103540715a03092000346180142e03441034080360791254042c9821074074143c0020101c1e1010302d10045c0800404411404666030440741702514640701c0c5400d0307045649982c0550b0304122001d01521108002180d03440c10b03600c040c2c0440d24596004803002184100403140078021a004012140c0402c1c030986500000701c25601c0003003001e80400e040c6400d03a8000d901b40b820b1042d088038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 47529518 1250 47528268 47528279
    0x7020d0f020108131e02010207050d05030d0f02030601090e06030115030302060a0c030b0f0409020f030106060507120c03050d050405011d16080303090c010c060906050408041404050f01090b06190207 87
    0x600d0f0f40c0041c90f101c80d060303015480b40e440320410b0540151030381500320108940011680b0030880354001c1c2c41e010f0300100052a075880c00ea0390380e8001841c0620702d5410040c002103840c2c0180300b520300c80c580583d1404003062074207075103142440300906410b070595200c03010500205401161140150722a90080c503d41ca0046501e030101c0d0b81d1009054205410818a07180e00e40c2e07200306401889408442c0041d00742c00340d01c001001c61441101203a01542016000200c15811401a200ca10300545800213802650181165102c2c034442c0000c000c140b050000d0303d411203a6130302c840c0c2d025215000024100ea0f180c145203403007030b24040ea0395800340e2000303049801c3d0808444140004050700f000460540c00c043d1130007034589424624480c1000085401c8100b480145e0700705180b0b654124004100905240c00e085940b42d115001c0d00101c60b0201403203c1309401d05201d014411b0349070703a8880625900380b0400030050304800002c154028414410784a40b100d8146d45082042e8194004110003072810 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 47530768 1250 47529518 47529527
    0x609080307020d0305040308010b0a18090506030d020d08130602070506090d0905040501140d0302100507050a0f0518041a030f010902090f01080604030e0a0b0a02250302030307060e0307020d0f0201 86
    0x300d074000701805d1405000020390041c200c24103440c0380240385519950301c200c0455640300890100003e180440c140020307161116801180120415420b5811840c08414280e1303031006403005031000034489a000514101030001c2c0d40f08224071030400903141034410b0b00d4440c5414802e54103410245c10000d0313000c07010b54000c50010014082032300c060105624102d00c42a4403890100740500039544280240300b0180300313110b040c04161000d2002c200e58102240b00401d1034100d0011000416138480c8002d55590081040d14031510800e005283d58880d014240070281c43e1081c0a0030300702c01c0c5409102c04070b9070306000c100c001c100e03184000500c1d255240104030380c03490f0150011600039607260040c86000d10106040c0d5106805080040480d1180c1380498210301036680145c501c1f00010602c42281341d40826011900411b51103d0440907110450002c14a0051720009616610400803071002600030380180803034189110a89081c22034540108559501a030002c841c03c1c2c010305844000c640e0032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 47532018 1250 47530768 47530783
    0x30a090501180f0909020402130b0a0906090e130c080a03030e1005040302030a0315050a0305010c030b040e0c091b0708031806150d05070512070e01120305030105010503040609060908030702 83
    0x2500300b208003a190400740241c5016030702441d070712281c0742c41d078080654030340e074049a0000c02c5004003d0702d556925404003440b9003180f00c01d00002107040d800003d01c0d0b4442c4100e001a50001004200d4035114800703c680ca011421401b1110028407950000c2d05280904c6001f150500030707100032401c9000601d00c9410082c3c442d8a04c490b86141c071041c400420360001c15154542010300700050b000320495501c000b880d03200e03400ba6a000740c00d030001000700501900041e01340c211944040c0714541c000f00c200029902417440c0411980d0200b0141001c0d0b07c0c00170b01281d0000e0052a50785088542814029030540c09400186e0796518004180b22448034009061040d000200c0c01030805070820241c0d5510003500b00384498402c88201c01074109000b8240b001c100108801000c200503009240740f0b880d1604e200d403040c40388020400c0000074042840920b100c6925501d661032174916800d000054a5503003001d403058a0203981d9803650800690248074416400c3e0240440f50f07102c1c0b0381054006e140164 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 47533268 1250 47532018 47532047
    0x50705060403080403140106050904030e030606010305061c03030219030e150f01090c02032116020609060a0216060f0906060603020903070501050c0f19020109080307110904020f03030a090501 84
    0x30104410004182d0081c20b45040c0c95000c2c810059094505400c5400340c065a005598031140d010240001c140c0c04c00104940304500703400f0b444c071554903080154200c820440c0e00a40140e20740d03800200303080d410409903803801e00c2418014203210030803001e401105012515000401d40e05c500d4810352100c10400b000307274011110081c04051406902c0c00b80040360600c10850215120044c01000e540284180d901da401e28038146001c40c258030f55034014030034054071544140c9c001000c00241443c40422071610802d80c42c401003400c0e03120912894020340c0081c2c09a00030a0b40810600e0000b1211b000c1c4907000c4560a40200700550b42c1e05044041351080d5111200740352041100e41c4041d20007140a8003140c1e030900700a521030b05580c56403410039100c44003500e02c03806211416072501424402c500b01d09070003a80c0301110207440f81e001c19601e108408001d00005600740000c0300720725051a10070780c014406489111800f520340c0c04a85982c101d0300205000c40c112040a01c0356503070040005801c44d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 47534518 1250 47533268 47533279
    0x60612090c1503010602032b020a09090608010603020d0b040201030e0d0507030e04050403020c04051012082106130c0909060e0601020c030c01170402180103080307030b09010312050901020a080c010603050705 91
    0x5141c20000307541c9226941c010402030b03010002c00d5040d04040c42c0a9500034001500c09c3d0768503540800c000f8200c4c0500d003c1c07811494540080032501c058140320b00306c20307a940a04070f441030440540301c1c0800380a00610485c101a200c0c1c0050392a200300740080000b92640352a42a01c40226190251402e02c0703041466000f10702d0601000013103a8000380025650405031000100f03601d5000f910554142c0701c0d04403400c5151041405010481d050004040a0903a403804011b000000ca6240fa8548015500c4560105100720045603070340d410381c40300d8507240c03060400c0f8182035541d80e1000c00b0340f0b01e2980550b00f03507001c440422000d035070140324021408070100c015001d1510107100191454540b815804004008040007400310340f2180c100240241001e1858034407581d503441c1c001000e07030084820b0000281030200c0d200850030601041e0341030380e5104000c0c00000ca4012801c46484d04400481c904611803900041e0106030418000d040340b945981c0042085400c2d400c2c190711301202d0b46d00407030050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 47535768 1250 47534518 47534521
    0xf0a1203050610120e0f01021b060a05010506041e0909120206090a151e090c030201021002030c040501050304050c2107080703050d0302030907080d03090209011517060612090c1503 79
    0x40e036110001c81070301c00341203000017014808007140030300e0079800c14101c0d01c4c590f200103411044003044440410307190224204444865641044810903900e081c400e850300170342e05102c144500e2003c8100d01d0034032503600900c88129503803041c040d02607a15403182607806000031001c13007544ca5410b101042d0f000b49484020801241281c1d51080001400024035140710368590304054030201a50301040c64906102003070003589950700f800310080025110403809880340345d4880400d200d09000742d9102c5c00c030125031141002c0c40d000041d101603200a10450345805106ca030251665604110340c2c0041174180314009840e1036004180c2d02d441c6954120081d180e1189008000054000495140700c1060b4a40540c407911904d00c15072070019103411a412600800303040621540d856807001500d94000c0740d4910b5243d0341d0f9584d2070801c0042e03800c0d00340028070b4150f0307507200d00e0701501445804c00000381c104c601e0485901ca00300c011074829180415182c008034580102e51400c440c00502d8100005801d0345127 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 47537018 1250 47535768 47535799
    0x2030306030619110c0d030b010f0903020f01050909041b060201020c0a020d020a15020c1e030d080601090f0807032904120306090f0e0f030a0e01050304050f0a12030506 74
    0xb5110020a030349504021510001508030950300040c05401c0300450041c1c583d03400c10300464850b2800e104020009140040205096110b807400e0b400c00350043c3c603881c4070035040d50207202c0803504012500c0d050240420054a02d0b40701c0d0032010b8402c0c1e0140074600ca00886120000e0f654000590101d000c680c014021005040008550042c08540c1203c4c12141801d0610120700071441035808490100140ba07680a4900e402203003680d03841008070b5142ca903203010114007070031038405140e0150701580010240140140680c05aa4111405041c4544200c0d599050740c000841c454204014036003002600b0000c10102204d0706060381647c0407900111000303004505858040140090035904403010202c0300705000381d1001000e08803a4170280800b80d4000304520240035520000c0003180300da030804444071032002c408c1c0c4a03000e105030f60f40f04058161304011a902e0f080940241e4a41c0110503407141810701c10010a05034034400c580002c0410132601d0050304480c0018607282c007404051404090 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 47538268 1250 47537018 47537023
    0x807020705061b0a020d1506060f36080102040501030f0e0613030c02090112110301051504110d050f0618070503010e0408070f050601170f120c0a0f060501030b070203030603 76
    0x2d10398043d040d20304a02d1a000201d2510640305400380d0404640b0050b034050168134410f4851221380310506004440da80c00c001c49010804892820000f1614041d40f160a5441d10780504a03411440c81694140e0410f0b00b00310781107016511641c07507607500140400255806002e1805021000c01e41007081d00313554929551180700040103012059004000a8109405001c0704042150080c104420660310743c0e4030800ca91300d00140640300004181403403003051405001d51403189001000c010f0b00a0310080078400542607451541368444001d100030070795400103105a9204804028a0f071102e0705082080c410030403003007085d0b400c0c03000100c41001001e94000040307070b045514134180e41d0302c82d50f01c03800c0101b0a8062420006d04e0200b410035400d0030b0084c002215410b0340d00450b6020002001000e0950359444000242e0b0b079180c0040364810081d0341c200000d025a4003d90058804620702030b41c950313031b2114031402e040b1441581c2d2401803080c81a00c07400182d00c404075000952550408100095 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 47539518 1250 47538268 47538277
    0xd021503180c0609010e03030f0304080703200706081504020d05070801080d0e13021b0105010611150610020304030507091e1406040b0a1715060d0f14010212010b0a080702070506 78
    0xc2c1802050850706c0300700d40701001113484080d440c0b400781d40c60b410945482c3c60540d02c52841980028040750300d0301d28010341e03021018040340e55034008280d060303e4010150b0b5503000003881030161051150a190540d01c4034001490a440305600001e001c1c40c10000140024806800525003a0f01010556003865002a00780c0c040034422105141c0075405102d2040192180c41a2001640c9036146000d511110540010741650a00d8490381601d80d070b041e145030340c4c400e408410480c01d54042c10111f207150420b0906045103099602c166441c1c207850b61601490320742e5961010f05026a18038101140c0c0c00c0648150031030429060303061000d280c0080c034500c4004406400e1a1103195110b01d10001c40d55040034507401842c0b90360a0014a2040c514440c0e11032494900d5150092a04c9001070383ea881d00102c00310b45261301010f0b442019449444041c01c542c008000d4110944d400c0007003088a1420300000c500130070750f601d4001d5540100312001842e00102400c140150741c410241071020f56910350039035 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 47540768 1250 47539518 47539537
    0x50c030606031902090d110411031b1602060a08100b03011805090a1410050105030105010302090c0705010e0a1101030c0801150c030e06040f0305071202100305060d021503180c06 78
    0x2808a14200400c3d03000030300c2801c202e10b03403000184d001c0d141000301d2044480b19039002210100300d100c400224110b50b030b00c4112090f00c2c045440801c00070640e1805005014102016290030500e40c030613034007007900c5900240c500030201d4150420130041e0307041c40c5065009442501d0085045525040303801429207d5060f4100320261590009504103c080040281c80ca4020704107601c03c915074440c442d10742d0114882c2c0302500b818100041703400d060502900781200d0f4040c003064496a40d00b20101d01d03039001004100d69954a41e5802c0072001e204101d14a0194001c852500d00710340c1b0303880003400b22003805161000b88500200100203131410f18038408422079907400d01c118000292316044800440c002c00d140d0f4403003400708000c10241030705002c2105881c400c0c0c0844908589840c101c000c20707039407060300075403210215201507811446508101d40180016020032103c04c001d03070015074402555055158002e40c0402007050002580d902107028400007005002c420f000d02c07020584900ca500d04d030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 47542018 1250 47540768 47540791
    0x31c0903020d0813050706050a021006050306040609020a0305030c070e070813110105070b01090e070806040b0411120d02010b090a060b0403060c0905100903030e06040509130302010615090306050c03060603 90
    0x204040d091030342c0132044a0b800010707601c102d5200c49000d011071b089000d1140c01882900c0b00559254201d01c603050640d2b00090041207a07503281c0d6544809403a05000c01c98009146081c0000007513401c00c0500744c03001404000d010590308151607a46003900043c078900800200c1d505204140203030140d2003540e075410000e0300c10b906071410f0040e5054815550020250030b08980001003210403a44803031000c1d080c00b800c0d61032969842280f1030b0b60301010344005e0f00380106a00450b001503501e03c800e100c840406880804565402403180d402c0404c40e21847c00980d44032803554009150031301c62158800d0348088100035040c1023412068490240d03000c000c000c55516842c500095024420320001404000c02d11038190b4020741e0002d0001846110403400700380e140401404501d8800c0035a420341d403018004464035035074070302c00703103884040f1000540075035503030700f101141502810b040031724180040e0301ca02814901e546803030030031a0382c01491031003119030074414403c03107a07030340001c40342c01c481711009 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 47543268 1250 47542018 47542021
    0x30403030b0f0a030309030c0902030412050d0b0402030426130506070609060c0f0305090607080a0f24050901090c0806011d10030c030c080103050c12010f0203010305031c0903020d08 80
    0x1c40c814950040006a0000f03485400004150703004a00000341c9100d442d07656941591212250705900081c1c0c1c006040c014000041d20000c0d00c0341002e0012100407140102e201011500403030202d90003560250303000c000e0160510311201c040c6407202101101521170526025200c03c4004001c0c120340034031031160320001491000d000c5c140c0c0041d9404c40d00142d00f002440301d05c0c1e801500e20445000502d005c20700741070005102e40c80104809100380c01039200c19246580d41042c0000510341080d0030151996610540b1516003c49a5442d844c4201c0d000c0300b0401d0750400c2c00f08809076105138090f003025410803000850469101d81180e410000a007001425211800403609000901d208801c2c0c022003200c040380200756050704107004048180d1420020414180c90444000c41d090001508c2c0da0700800160480781440e43d5040f91003400b81d000090026200d0070b030001668400c1e4801d072a50350010480301c0d4488040e001e140e845c560748807020001c5a030166406521141000c0030f02d000e10103404c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 47544518 1250 47543268 47543291
    0x8091c0203040b0d09020306090309150a020a0b06180c1e030c1602120d051305090906160201060902070c1502070317090d08070f0606050307060918060810060317070803040303 77
    0x10405d10580d03600400752a01841c096284503503076081114150312501500002101c0c030052071f011101e4804885d03000e01000032746900c1d8131001740d80190800d83c012070001610105012000344242c0a5554a40c0f0b00381d9590319800d41242101c1400c60881c4642d60070406d01812142040860b044c801000340d058101d00d65034000500503a00c0901080349501600d000011025401802001c5200014802c00b55084d110030500406005c00c441030101c65000390003046080b12842c0d01403040750349034400420034940b148000c0c0207036040003000b00c600c0c0d100041c0c103110035038030890300d040b0b8030a0320300c0100441b0385952501080d40307240855030900c45c000000e42d40e4090321104102c031000c13074200c680160391380800e00d40303070301d202c2c64015050b50514030b0280d0124662030301044110807141540c0c0d401c001d1a00b00030b03520b07440203401041c14100c180c0d11b0030000340092050007280f1007004040b0300050011b00d182030100d90412620882c10842d1010480d440c0012190800d9a4000b43c1516000a20702038a0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 47545768 1250 47544518 47544521
    0x712050705090a0605011b0b040b0a0204120506010305102007150501170c0405090a020609041b170c03010f0303050d060e1906150c1b05090708091c0203040b0d 70
    0x40d000103410800700d404100d0140b603c0d40144088400a0780c030000580312458511a928280840c000c20f9440540081404100368240081c1c1000038040018901990740340040c049070713680e810482e0540c0100c001001070141c18007040f9058821220240705914032011a070b1010003001490110744100071a040060201224241e040c0300026801008a541c40740b200e22040c0301e114142030124480c54180300740500b01402114010464400181070220255003000300742c0e00011002a0080eaa0300d140102c0f210100105e144100c4aa85800170203400002c0141c100120040600401a104100411210029024203821207404d45800342e10792552218000c003810003a40041c40c280802000d00501001c0206410845c903135003441000866901e19103611840e05580b40c2c200030610f001c034000f004c07074141a14001d11041140061004a44840006840304000e6500c036000800b080704000304518208840c541e50385402c11662220200306200956038070590090030111080850444400d2126 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 47547018 1250 47545768 47545783
    0x403020703081b19050705060d020c1203061c08040314011b090503160e0c1b0303040c030201030506030a0209070f0e030f0d0306060c08030109020a0c05150118020408071205 76
    0x74803403683c0da11610042c00d075140916202c4074150191451012094000d1005045003545c010301034043c1c00c0c078000070400107030802004490312075000c01095080d20002d20a640c00c4104240c4034a40b641807407402c0c0001200e0310341c4400810314004104402143c41070080d071741242c1d4030481c40344100c05584806805040c5104022020364201680c0c645129003015440c0155001030f0111404a9410244400c60764480e200d000fa40c148103201046603880090010a104400c2e00c0740708201154002c0204d1955104480030355003440180301c180304640e49400b40c150003030380450040001210070703000103901e580041c3c00c2c041885100c800114800d4052070b0001e080e94001000c0d620f00200308100309485e00d010154039400a461b2080c0440e8040c002c3c01b4421400340c01c10702445c29a03080905090080d44008540d00c207104403840c54030006a0100301100100440f482e900c240d81d45480543c888503282c60700c480348264018031040c0400b01d400221b0004880c00380d002201c560045003010b0342011203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 47548268 1250 47547018 47547023
    0x1d090c0d060f1224140a0c02030421051207030e0907030c080708060102120708031006090b04150e0418170307020d0309020f0402130e010902070b01090209040b030d17100e0106080403020703 83
    0xa00c1c0b540d80d40300705c03800403652040314460720902c191103001404036124403640c0200060f080712004000112182501411881c03440307003042380d03c0600d0312000c241240e00440d8003180000e106080b0751440341003081c070302900400142010b0000d01c054803005018042d000f012041004600000144560710801c416000ca5194070806a036a004c4e07410206165441150f26481c8507c1c10a80000d00c0340c421803516045509284c1c00d613085c01d0401d8000007090700810407107020404045043c48030741da11403040e50310341044800959a10700c02454541c60310003c11415000b011000e0040110040c0c010644203c0c1d031520b0314000400c0046440001c40f2a00c1445031190841e2000c9050b00714000929400d1003070321003d00c0003160340d0381e036a07510074107038425500b0013003114540400400107441d81d03030013812507580000d00c081000b04080010901d414001282d00c00098008418161041c07020440c1c81e1300405621030161406080c0001820111010321074a02005101400942818428080c1001856 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 47549518 1250 47548268 47548271
    0x11091e0901081005060d0302070303080406140c0403020405090c150a030204091b080f060a03030f021f061d01080a020d05030d05100f090203090d1d090c0d060f1224 72
    0x140c540240b03ea0302d9070b0f120500303184245400041030707843c6402e50503204650303450790041c040710f821a6800c440b030250250080351b4450712592104903200422040724819004441c10640f51455401048141c46003d004a80903400002403400141c403810045c07611240c0d14030f895a030b581e454503c210000d11455018001082c034010340301441068a001100c443c0c4010303502e001460311649518a8203100548006078003001c8100e003080020b0140300980350641403030058640000103480d50580403400c502d000407095a0341d80041c4200d4503241600c482d0092040c100c80015810001d031181d88424614010348940c510400000410104004640846450550070710090800e2407020070103465074014030210b01400d40000c50801c841e4800c0c2c0c0e01c91103540e402000c86e07015849098820301910001d0744052044040c5154207134603030f40340c8075002d0302004ca14541e407102101520300455070560040c460000383d10340101700410010601c0415070303401501000004545000c440d042e070402c03c91001c50355 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 47550768 1250 47549518 47549521
    0x1d120c04060b13050307181a03030c0105190b060d020306030a080d0b030c04020703020a0b061302040803090a080708060109180f0b0402030c0406050a030323040b0a03060911091e09 79
    0x4064000142180e9000d6100f10a4420780302c0b010591241030b9400b031b98030b071355045400402140503181c21080350303250500b26508040c10300e10080b0f0b0440d8032648461030141c0d1601c003444090b148410441e00340d001c21040c200901000c1d000001c1c0103205040c0d0240c00030350040b0100d00c69503420b000f02c110490f8486092959020840000405058648a000c0c442e0045280114440c00c3c0307402100c003090b50640c045c0c0510891a40d44001c40d00020781603c0e0481c11a041c0c40c40d11900c0b601c0240701524105000719194030150341046000256a00140342c19080001c0401103020000390b440e042d01c0603010003003441144807140301070f10300c2000405400044210180020f21001e03024043c0640e00130b5040e0b5029010410600c010780d202849500e4125060750000c00100784988600404030b0365184010806443c0d80f85040710a810580082c402c81c203001078400b100e681c02d0f201d501d000b80060030040c090004008008140e07400f40c40c00303a9028480101d00c12a090315140e0000004401c020600e0866 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 47552018 1250 47550768 47550779
    0x11040c0f0e03010204031e06060b030a0b04060f0501050f0307050c0d050304021305041203020901020c0a0e01050108070201052505070204061e0e060303071b03050109050d030c1d120c0406 82
    0x40c51038502203100803039078108400e9824203040c0200e0b4182c94001c451500d9000c111040e150340000b440c0300a4030080d80e10040414041651001980649550b41010800d40c8403001003000700c0304180d020080e030700740c04501007055907040ae0549001d000c030581e90580740c2d40c4248003510745201310341c0704403840d0107410340c2d170000b02d034002001c1d6000300e0003502c0a9045800b1180c045044481c155405003599150720541c4000501c40d400410f0460010300c160341e01040d017000450100702075038004442010007500144200d503441301c1143e074400b00f10700c001e1145062101c0c032142c0104101003d000340c2580c018900226902030130855520a40c040e008100040e6540341c1150041c9100001d540e40b4041c400000407403030614602180503900080c00b8500c1c1100c00d549a20001c1d5422006c0100804001c80c0000495400c0c41016101130140d005010429040b140c000c048a8a941c1108280b00c0d2011102030204000c1c041c0d0008501d042c0d03403581280c01c1e044150752800401001050b8000d0500101055 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 47553268 1250 47552018 47552027
    0x80303010e06060307020c190509090604060b06250206040506130905062e0c0b07090312260711010c03090501060501030608031204060204090c051306020c01050405060711040c 77
    0x121140507014026503111042042883d11054841100603803003901c5a10b25031038443c94050a21011003091450700740da50010035410082210070050a4100104200511440b40150640d00034115940c0746030036151000e0360b0000740c80c0c5060240180307203140d0390030441d00c90008076030103850001c0c219501d413001100c0300c0c08104a10300485a03154140b5001c200c1c40d0030418015006441402d5151070484404107050801c0710300c0810403020020741100d484081344030211601c1c0100c4282e940c0342610f609504040808440151100d01082881030343d01c0ca01001081071322200b40c02828098480c0d0701d405008a50b066078442e444051035291500c45c504442d0154040b6400d03610440084c0600f80d9502c0041d01216042d124006103a0410004214040800003050383e10901c258401420079440e014540c003101c41802d502804202c0020b00c01c0314194101d5400d2009103020b00c0200b151282c0d080000741079003d1442800d001d154049a0030080001d006401c4540c054068010489070700382520052 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 47554518 1250 47553268 47553271
    0x6010c2004020c0f0c0102030408030a050906070c12030801060e060304140a0b070f090801020307020705210a0b010e060a0b0904020a0e0423090d0806060901020c090406061802070f0803040318080303 87
    0x4564450b0207003511030380d400402a927003103c00c0080514140142050103940c968403801c44694440d5080213180e0008140c1c0c22100c02401e0701d03008129003002c6a2801034013100c01078112100b07001c1e1015081110359207580c11240d01550209580c4100b401030319220349400191280107005444040c00c2003c090740c8401d0700c46188500d61385107110309590706902400c070f2000703903003e000581020310300707016500702140910b50520308500e10b5154001017041803818805002c00c211005600740740100b0040b0301c40101642c200d4812180d210001e4a007155142e014031800840c6401185c0201d0300c0100940101286039100c07102810510412200a45100e130042e42c4080c00403603110700304003080084400050303440da40c10080d241c01d101c0d0340b6580b0400c0800e400c0343e2003180c110320401602001356220608000e0046100c0c0c400850b002d0b041801c4040307600050821441c42ea881404144041003203410850b14690f0011000b556035100d50500303d480d40b602c01d07000c001d00c0709442030000d0210400030095 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 47555768 1250 47554518 47554543
    0x9040f0509190812040212030414011409010c0213020409020c0106081c02070522020a120e03070b1b04050303041212110c130621051506010c2004020c 66
    0x1500845110303040002c5031206408040c1403490280450f05907a15001803468116000030042e09107805624521031640c0d100e500101c048800d1580748507807950300500845510581440c9041c285034131240000d1440260320f0000e84181c680303411030400c0b120b59604840107400b01040555a41c854103101502910381442601c210340701c0c500000a0300106000a90344900d503550103008090300d81410803045054640a68641403c001800145007070b4510086c91000f0396600c400303032280005040c0c08200e6000001c100c80ba5001040031a000810181c0060b600059555402051090394180c0b50500d0140c3e4000c5901480002004030305c0205442d82196200d03c03946202072030100b29041200c00500070002d5501d80d600c51040008246440e41001241c10103030300000810a07039501c0014186c40c0c0780c102e83c1c08015000c104907018131109215000d41c0140341c004003d820700f4040d000070f10070070103504082d114061092111204c0c817103400c080c50700c0d601c2c02403007551104d0361032400700d4032550300706c480 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 47557018 1250 47555768 47555773
    0x10503100501030c091a0d030c140d02070501110703060507120b0316120f060c0c05011b0503010512030c0102042411030d0207050106030c0b030916030c060c060209040f0509 76
    0x240300109041c001e19050701e900c4401489441d151034010005440000000500700c44591041100c5481d80c2284020441c000d944040440c11142014101040054289959508005c0604040e42e8000545000300d4001380792030400b00e0068040306080c09516000140420700300401d0112a60344541d04910700c00394200f04108200e816410036030340702c0c070a040b11180e41446c9001006032000d000c51660980f03001d0020a500f600c05d80d602c010882d440b40c01160003003a01c680907401800424800d0f061202c034072005848102194200250540c04148111803141c1c2d5500594403a198080c41503901707009030800250f442c0c0d902c4d421240700045805216450f594401c510340c0d0184c1c3e20550110b01800981300203107203424010f9060307030042e6101320420380b110340d250320703001002403040c0200c007001741819581c850709ca00345118414203050000f001306001d5000000c041c008100050010000c480b401d003024069031a680c50308401030b01075807410a034401d00c2c0003281403802486401ca2442660300c10b06 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 47558268 1250 47557018 47557033
    0x4050901140c07020306070807030b0910090b06030108060f090f16140405060a0e090a0209090a0201030b01020607020303070c210e010f03060b0f030603070b0a020705092535010503 79
    0xb0b00400034020403c000c1d5240d4001d0011444080c004c2d104a030704561645408544045928089080b41c0c0e401d582c1c1250300c01c240c034010843c0710390b1441606404003049560500e154540241117984800280c0000d100c80100e4010034100e1404101110308016548151a2048031110b0800541c7d100f910410840d02d010307034071289041c0f0305440341910501004140c052128202041c0e41d60700780d0300600f0f4002d588200c24600d005030b611102000d03c103500c1c08000b41030380d204502c001000d603402c15036020305651112050022054010003600e501c00c2c0542703030103c0800c849040c03103400a1aa581d03041c44613080a444282e1580e80a000c0015403042030302c4000c00108100005c9045a0f40381c462002c0c0c0100a00400400641103001150400b90080460b041076880e00b000e55541d5000c0c090010241e44140c1e170411031801c0c0101815445500d100324540802c24090107007a0801691928200b0440802e42003901074800508880706503e410120171024000302181484000007800b074036109104029 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 47559518 1250 47558268 47558281
    0xc090d0b011a0423011404080303010f080307020a12030c0f031808070f0504021b150907050d08030a020307090f06050703021b010e01050c100f021801080402010f110304050405090114 80
    0x2803c4404a400c103030b60b02a4a405204a003480200c200c407005030400c070008801c002c00035800d8010f400585850400380d50349515015060362120500d50140040307400a01c094009a5628841c3c00c00f02e4a010032104001c4800349012641c070506c0b01c100401000d803600c088024954018a07590010000c8190540150b0321600d045944102e6482002d6240d100d0049c148064240744d00a01901310580d008540c8410003034450ba070900e041c410200380c408c0c40c860104801c100f03042040c04000c0500f40e032000b40201d400c1d100d9111603c0300030582c50381c030307a00000131810315881075001800800340b500a070700306680c4641c001015603004202c00e50040c8900034030000300c81404050b100700001c050f103400301d03001c070710400658140c0c002d000b0000300c0e8020a2081c3c100344d101d60042404810f000e040069803011000642d9000c0c5c1485480181000806001c20006076041323a4448400348060803d02424000c0501203450f601c00e5401598001c2c3c205400e0002300f41e01500812994242d240110b08107a6418 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 47560768 1250 47559518 47559569
    0x1005030a02041215180203070b07060f0606020a15050f0103061802030a111008010b0306150c0109050706030509060601120e010f09050309100c03080103060c0903061a0108071103030a02030c090d0b01 87
    0x85c680a903140d081404104a1610501c00800001d8400c05001c140030306001008001c03555140d010101513041080c0c03c50400c444000c009505800744034003081315091983c0c5040c0c01843c1400700074103140d90b0340002d048620b8103900c180c2d45164001d00b10b43d41c103482840c201058a11300e00310140982c8030f00c41128907550096090f141a200002a010300b0360740c600c410000c04510000e000f50000714100141494900203005d141640d81c02100100708452030864000c080fa0401895281c2c0c0c0d81013181848210707031b4890614800700d000000301140150042c002540104001100e42101034074011a8204005022026040001c0700f140c0d0401482550b280a840c40c5400d0080200000d1f90f807801800010580d03070002c10002c41d02d10f4041b40c550b490395250805c550346401113006002003481000800e6034070810041e0b0010b0a2300e40210440540c1565a035a07000207801000025004000100c101c031860044d540007840c014080310241c0c490b4189000003038008e00a610100d41e0710704584ca41d941c00f1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 47562018 1250 47560768 47560811
    0x1b01110307030e040c09051005070c210f020312130905060307080d03020706060b040803070c050103060b040e0615040e0a0501050103110910020a080d0e0c030703021005030a02041215 80
    0x40e02c444070b9100d003a03010000206a85d00d1420240403410002150070b0721000000420213109450740f40c2da03510075081c6240410182e03802054000e100c1c0f9a00001c041c08520382100c141d0348803046007500b022610010b4100011400401e07004800440e4202c005404140c011080300d40c9454200050313221041403544401d001c1c000d1071410780c400c01d12046898400d900038501c060181b900014017589484001744964040d90256615074400300d1900c01788141c040324040103240909040207407902d40311080100740554420000302d400d14070b00180c0592241060095040002e41d69103981d10b0300c88044040c000e8007030300c031070045518000002c41d480d40240701d800701c008001481541481e81d0b4a00708294002c0080d10354046000e0711500100081c0c0703120241c01175100050022a094a08803036440c5000740502060348207030b000c8402000540c0701d10600480c000c1e1245007a50707a90792001c141c00302a11031680030800c05041805d02d241405025a6902c005a0100c00144030b04001e001401d07512006 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 47563268 1250 47562018 47562023
    0x18030f0a0b1306050408030619030209010510020c030307080a090f0303050f0c240714070b04230a03050301050a0608040b060909150405070503061006080609060609031b01110307 78
    0x30695100c0049581000440d5010030200d50012604020380c0d1103d043d100c0c156412124074030088280074040ca8a84640038204200200004c003040c0740d90006030303a11206124440c01741c00d0041665180c9442484900781c485805030441e6528502483c2809003076200b000c1a000082141c02c0119035400e0041c4c082003265050fa0b00c803400c00b0100d1b00180c1856000c220f0740c0c0c0551040060a90b028811070310740100c43d080031a404d00103842c202c100504581084044580468410444007000907403d8001a402641003120712502e074043c240c0071801e40300c1035203050b0700e03612403000407800b0558041c000f581a148286c1c1c01004d0142c1e5034006035030600c015540108440740398000102c02e0308003c44060341c0041aa0300702d0b480c1001501f40e0341541d0342e068130190750581100340c0a11043c01c0402c601c54101c401400740304221031410304020f02c4c040011704002d11503020390011668994804080d0703441c1e0b001c02020380f102c1003100c1c00031140d00c600035100310b8081102c81010403001c6401000b034529094 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 47564518 1250 47563268 47563273
    0x50615032104180b13090b0c160602070f0c030b01061d011e020106090218030c1c0b06130c050a0f031104030803040c0b04030b0103060e010b010f1101110f18030f 71
    0x60030640d100c100d50b540031002100c0d481e0345007034400321951940a40f0b1695404502c0000c0e045d450347c00e0106e046100108040c00710001000040440c15280d460441815081800181c6808040c03a0896519000c0d0fa40942140a070040110501041002082c100d400d25203804501c0390708007201e00740d00b8134003003e40c601148001c03120704004107901804e1020300b0303107034400003880355202d0408004a8000d000704407900546c0095840c1c403401c0c2084107002040040303c0c220001c0e40400d014045a0f440c2e0b4500402842c1178038007250250715240d412482040c4035000520020043c6200140250001c02c0d10b0f00c0007079074070300303a440f4414024840c00652a0403002d03075030324045c11600d401206038800741044a800740e00c1100006d203905200041c00c0030f1880f030040c11100c0c0d40342d407c1c140281d421100d8071070302a0b4580401d14007240e80001050080120b0790030042c010070581c0071400e004080109090f04002c40c0020008400b80040780146901042c41118081c5840024140f540c0e07180b0400355444035a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 47565768 1250 47564518 47564527
    0x3030906090703020d0311010e0106120605010503060f0c0d0225060b1207150c050a0303090203070b09030304091a0306040c1701050c03010b0f0f0c060a050f0601020a0201030c05070506150321 84
    0xc7c2c400c0b01410044411800045644058200c140b42180c4490b03125224520340d40d002081000058060360340100030403002064a418a0b0b0042d48040b00080c0010141500c002221010004160113407400307103811065140d501181c250100c210380c681440c0480b0001c0c94481d0f000744901d003d48008064005003c014039455007005030b103042c00c1507440c90342010b1101c5400ca40340011010054940054130a503004140000103205040c9040055005441008006d1114002c503403400415601221681c10000c1134030000c81c44101ca03985d002031442030b054080e0f0400c020501c05212080380840319a40c00815007420405101400c813081038400c011555001c000401c40c01008001030140510301a14051410228241c402c1281e0721004046440c1c1e004401001851001031154a5006c124184100e4051a00b80d000079214402240000d040c0341d55107403440b004510400c04c2d60b00b003590001c00c403501d0b414904400e0161003040305216102340308000c5441480314100031048082ca042e20039880c01e1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 47567018 1250 47565768 47565773
    0x604030e010201060e040515070c050c01050a031d01090b070f050711010e120105070906030605010507201c060c020a200414070305040c05010e21030708070503030906090703020d 78
    0x10200403140324110741d21201c0c01709500d14a0281140580e21400041a04050310300c0c2c0c1303005581c00100024244081c42405602142010540c03100781402481c01941e91140c04030309400074a84d4243c006040c0c0a03141415140030300550103946010f0003980303c0c0c2001d5a90400840b509900413401000049080c0552030011300b418002002c0e40e20141001410642030340d005c2455419560300120a41c3c1d183e5050010058121040c100036040f28601803043c5414600041d1040c401c03240010001581c0c030701410310b817881c0700d400d1101d801c170000c12040607182050a00a121503502901380c03125880c007031542c0e01c01ca0000401d03c00040e0300c0600e051841c81c1c1c51080350303541041a8202504245c0380c17848456015401a1f1507407080764181c40009490400d810309641102640c0c10a82c1800102c0c102446141d40769801034640c00c5000040d22446c941440da4113065007d1981c004000b0140814981e08004010014501c560070031002c5460300e0361515201ca9950042c0c0c48065000404110328001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 47568268 1250 47567018 47567027
    0x141902061b04050d02040e0d09090506010906170619060e010201150503070e04170d140604090305040b1b0106030828050f09030312090d02010c030b0a0506300f01060201020c060403 79
    0x15a1740005d1001441c40300b41c0c48a9410151074141c03400018040c068180172103425807050300d0f000300b400e01c1c010a4403420582d002e003074150b0341d10010040000c2400011340a6684091200c0e4603502d00c1f84980e089a0b444801030180c0341c0200c801809942405601d00440c4103500c2c0100440720020700174107903c2d18164000c490114040c10940d0384080d40318100181400240082100a200302c00004042c0c160520796041000c000d80f4143c8100c1c01e003902000400d900009444c1500e14140c4c400d5aa203280e11120050b14050748808080395007054170000521440030701034051a03220301350300f640d43c442094846107a43d040032200d0700454010b0140c0601c088643c40a0006558003604517403400700d0340f0300c10242c0800c0c11142035800354480540c801e4a554280101c140710100e40c01d09200440445000801b1181e032405020701815000c22100c01c3e020150b01c0801785d284845070710745000180c090f0080d000c45802c4070110352044108000082c540d105200315001070710841e0250442c1c0c0c850780c3d01260f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 47569518 1250 47568268 47568289
    0x20f0c010c08160b0a0609020c06061e09040605010e09031903150b0c0d030f020903071404060b0a0c1a040b060d08040f090e0d02060f040b07141902061b0405 69
    0x71442c040c00d000c14203200c0c0310301c021101414003d40b0010001e1601511003415180d05400400c945401030000c0e2168440018100b0780000f0704640040140d01d02c20100500b000d0100d0340c040d0310080150900080c032020b540003038141d4002d003445074407075070700c02002039603d104603010500e0748641d20302c8894044d4480d610404034001b10b04c0c10030600c1c6a84820308251900304a100100d141c00c00144421a2900361054a100043c00d0340103500381096000002d17203a03d028814030107003044d142c10000795076840d544054007520301010159140d048000d40207001480031142160300042001c00901d070400613007082c40c4500c0d84020303468a0740d41d4810602203648801030086480280074000400c40742001007284c3e001d09482500010000c81c03106e80d141c5040001ca07644815500100140110784020107402688a904030ba1441c4883c1c982a0303044540386682c40000f0f21901c008111a419102c001403941d0702078204da03088840c95140d0010240984510b410300c42d58005003000304000c030342040c1d507141 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 47570768 1250 47569518 47569523
    0xb030603100603050c040c0e0a06030b0303130e01030312050c090f040608030307051e0a0c030f020c030615040e0f030a0f0306030b130210030203130b040609050d02010501080c01020f0c010c 83
    0x44a1801c480680e25003590420703001203440341c100311200030840c14188550303107001c581d0703150064030042d01c103011481c03030341d1640100d13400c1544504400c0b400741c5003001141d1500075022030000700705665a403a141c3c1c104003800202d0025550020070700f2250306c0c1d402042e004500c510361403841d054882c02048070004d041782d0366580050312408001080704082c005144070700f1064680d035640756000c0d0300d003518401c0005900c0400c00c80034482400c01e11f91090786031009075418200412100241c0c00141d2500603003406490707051007010100114040c2d0f1642c0c000028005440074030403689010001074441080b8138000109600030301401001511510300810075940c181400503586440303840c5c5030074681045a0003080348071820000402c6080c030202c04a004540d41c501142903007030030007003c1c00e19084420060b12003851a4082010710155074403c0c00500d40c010203c68604204500183c040c003000d02c0381d8103650103021540300440d400401c81c4180d012044c7c0140c0380002540e00159200103190380d00307 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 47572018 1250 47570768 47570773
    0xc1203130e2d010612090b04080a12050a0b04110c1b120f0106061707020a03121404060f0e0c060306061b0d02010207050601090606051905092205100e010b030603 71
    0x800d203460320450240e6400c500e0142c4002ca5039070501401038603c6801c80180d00650b460710700041c0200b08000000350308940c2c856403055030740c010b0440c2190703445a641240e0851500c3d0100380000d8901c0c0d41e000d100d0500055400384455a000004000c15000750408400107030403003d081e84484240e02c041285420f002007024000c01101060700f80342040c0d5811500160399154024440300b0340201200182c04540311640f4590310704402c0c000c1d1200140c00000f028002d104101000d100481c1d00404214200686910300303618040c1000780c045d0503500703240c200d054070781290140d90f4003010400304101c1c000606041e155486900038401c165000c0d03049180000e040e000c0c00c1d940c000c2c048c0f11458100c045980096203d0145d0b090042c01d010040c3d01a101d0030b450700e00300300503982d00a41651410716420358070640404000340162660f204400102d81d01007072a01c035401c079171464511f0303c9941e84985a010001669030010410b61180b441c000c903090658120010854a000742c4010742d4844409401e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 47573268 1250 47572018 47572051
    0x50c0913020f0408060105210706030c090504020c060f0604020c0a02090903090a0e010e07020c0a0605160506070908070801020c06040f051903030204090c031104140102120403050c1203130e 83
    0x3905a10f400035000519580c12040c0100b049107000514040003100ca00d4091074400071000c0e505640b80349a00c00c00050545030f603082c80a450140902400a010240c02955a1780409065030344a441c2107403102e40080e8407038082003031800c2c20b100b540c030300c0035504001700711076003c640820500100c01040e00c04140320410004805450b0102450300801d0804100d207502c0d41440ca007100c0b40003009165030115030003ca031020895480c0703a130101c110744680c2005aaa4200f8504189000440304805849446190b003400301d005d0780400d13008100d8038144180c0c0ca00d90f446080c254213078407400e906c0c2d81c0640e10140201c0d001c2401c1444854406116108642900c040741c0d007a1007008a104500f40c0209601040c08c105800f142c3c01a1035541c0e405190801520407226039a104902841c0a0ba0035401c0e0780c4a10030b81075034020000541c005060344c1200303403110754078a00a07030b0703d081e402c1445009410303500d008002c908000090b990080300441811150508104000f05e84800003018000200503185 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 47574518 1250 47573268 47573287
    0x706091a040f030302070e0a0203070207140d12090501020c0d0818030a05010c0513080a02010906050c0f030c012f03010e060d0803070306061b0818010201090c0e040203070504050c091302 82
    0x100202c00440c401e03006011600e240560710f03001d400d8001c021864850042041202060340410210300743c81c5023521a110720300100000c00d00b40301030303150000d002c3c40c540105000340395040030b003031421540242d00303c51000000c6800d01c01d04040143c0010b03c1c0d44800d0040d9030324040200196aa8000c010341110b803007034415200d0300d0030740e9094010782010030000150200380c1c0c084801c5800c05807000c08001e20300380e283c550009098441c1403068804210002c250b0b0f52000a0034018100c1441e094001c981c2c403481e52400960090460624500700c0c0c9400b064940e062147c10380004801c0300742c0b00d0340d90742560310b044000603450800070400c580c030004044081c00002c1d1414061801030816680c00585c0070300f2b1400160141c0c1207007a810030408481d803a06000a0030400c02c44100c42501c1100c03541c0b03804460010303400351203880e2000302a1201030324041010340a00550343d02ca14022011101840d0f6181c003032008543e000d039203900c004e2000700800c06150806010090b00c100040b0b400620703141d6180c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 47575768 1250 47574518 47574539
    0x9020a0302250201090905010b0304030c0c0f0e0108070e09030412050304090204060c020f012a0c12050a03030c0f0c060207030c06060b0702131401060810031203020903010e0706091a04 81
    0x2c00001e0302c451840a5038000e55912140d408040c000d480b0040103d075040003001113460200800040400449000c06820444070010b007200038002032a0102040c0d03128940c0b111405000d000d803040724400e02400161800504107260301800c44580030f50f01d05401e114a22403030b020000800d0b03c00d4441008001a0080c161000704010881c5564905c2c600f80103104110202a040007500d041203c0d610b070610800090100c0b50030000405a013120b600c110500d00080b01011640c82124038400401c48202840000b2440050140c440e54007044440340030750080d161011840528400160703003030543e00c000fa085a0041c06858040e00b01200c1c0200155a030f1816600217401c03400c0e001001040c00c00c21030400861007401e0340d0481d10103001c0c1e00b00c011092103402c0302c14030461080001c918040740c499071a05d02410f0166070007892054001d40c8465002d400703503000c440c0b918060741c40e0610350003004a0204228007521802d56403500d81c00d18080c0c90b044284020226052012000c020024004910 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 47577018 1250 47575768 47575807
    0x2010905031206040c1719090f120f080705040902030405010b0406080705150f0d02070f14060708060607051e0709140a0b0901030807021318060b0a05010302070b0109020a0302 77
    0x442c1d400402c203280c40e505110990b28226040e1082c00b07042d030304440c43d240b03108000d181d000d008a4044440100b5000400000d45005407008e4014444030290380309000014081480621447d2100c400d900b40c540310454190204444110021380207000912001c1c01640007181c000e8083c000200c0c0410442c4001002c81e2212391080559034000e07a001c215174240f1a2070700c83e040c41c13080c0c1540d040032103000b0515843c0c0b10300300356581e07903030341c0018118204049030707907503200300d40c1c010a8041d41a207000070510b50302c3c0e000b0b540580201d403445002641c03a01d0040c08803040300f5800740103080d00500c80010b6401380c0d603240c40303040f2103402101c10104400b90348d84110010200e86013089a150b042c07941d603050441d0070110825000c0e4000c9801800444c041c4811150841e90680700070020100e20317910031740204206042c500c0e103079082c10500360a101c0a40c20940b03807084d00300c50141c0040e41d514015000c071309c130b041c40003441564014010041441c02d580a0007044581d070602515005050fa48943c0c1e041c032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 47578268 1250 47577018 47577037
    0x5150c2b0b04241512110c120304021306120209040507051002150a0204030203070e07030207200306073902041103090106050a0608060d140102030c0d140103030e100201090503 77
    0xf150400e541d141c81c1c2d24030701d5401440c4d0200f03500360045000d003004000c1641c14116003805602e0300c0709264442900d4040368007a200540c1652000320b0b03201c40e0342e6460750040d60140e00c50b8907941c04006070441a031140c0300458440d0303001d202c94415580d003888200d440c0200161040d008180b00040c031500c03181d002010b41ca400d07602800c91104400c00d01400e140005d804000c1d4148140418001610001050f40c250785420011418541d02c4580880c0030b4401c40c5401030424800e020751481304903e108203920240c2d411403d072402ca540c2c00d24111982c07904017010340900c1d0034508c4079088800c80c0150188181100200329604142542c01103429907035a075103040241c000000800c640507000b880b814001d003100719008028240740c030400415145002e0001841849400d40150400c414110395a46003080b00e00213545a1810116030303d069040764064103c5282042208070b03076040c5200c10241a80d9068545c0252010b6a00902c4180103816804130305540d61405070382e02045040010713005141 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 47579518 1250 47578268 47578301
    0xc1704110306090c180f04020114090301110703031a01140a030b0306040311060c03040b010b0a030f0603080307020712050d0806011b0b060a0605030411040b0102150405150c2b0b04 79
    0x1003407001880320526440101e1a000e40d8544240103170719100300c000d00d030042c8d024a000c000b00703d101da03103483c1240700e40c440541d415032801c09041c0e0020350341c001420b1310030700944080101444514803a110038805c005058005101014584500200f00303000d000654520316000400c0498040400c0c54800c080d281900454041c5260001d1039804101c255840010492064218200740c2d8030400c0700c6006010b401340c0c5010202e5a116118803941c0110b08454864206100e569035a04041c116540b0684980e00140144540030401031030406c0707900b80169000c001416504038841c0200d50079074010709014100086441242545410407142140301c034025000b0348282c1c24080100140c2d0240d0350300500c00c0c00300038410800418001442c2d0741c4d070b103032091f10f0220b4446c001400407814102050840c0b000d450120080c0020300c00c002a5844400c41400440034454550910031074280c02014011740c494040300c200031024880180341000e030110044030114100991000040a80e152003418280c0710 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 47580768 1250 47579518 47579533
    0x306150902040e180706020a08091203030a15080705151608030a0507030f050c09090403020f07030506060f010309080f1614010b010305071e050702120d050301080d02010c170411030609 81
    0xd4102000c04442000b80d1300040005c40d1070500045e4461109210140200d4404140300000b07071980501a4018070780b0400344d0b656850019100001400c13900c4070500501c0c018100886c0500d0001a01403d8400003800203030528110b020704101da501c81018101860210103112000503030303590103580260416000407d152401e41c00050440b0100d190a0030401c1c20503003400741911050048560300c803019282c200281e0307aa030a00f07904d0a0002d41d00302620344030b024000001d0020119080340103840c00c0390b168400710820401101914001440600781050410144481d80c000710f00908174141c0c500c0c0c07200780b110f07840d40b03c48030005034000e90002c107651114100307503196a0512a43d50310110900300810b51802e8175401c41410307441150710000b40000044c3c1313a410f41d5100d444094038240340d00120781288280141c020a290000c1c41412070a2207600c0458424600600030129864007541e540d040c9a091031984042011026200b80c80e074a4102c0183c000c141c40131300c42240315850540080401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 47582018 1250 47580768 47580781
    0x1020c071a0403030509120a05030a12061205070b03150a060509030c010809030a11010f05040606050307081c0f0302070605070527030304031101050d0e0a120f08010306150902040e 79
    0x4030203000d01d0903100310010442480007039000300c1942c092500c240c8409616226202d50903150803180040541144008600341c2d07046a030115804441c000e480e1030500040c0d40c1e403425280e00d90101c0c00001e010343c000300014843d5040107405143d01040081c5100e5100c440c0e80d011030a9000240c0113500000c00000d18036880f8102000010b0b0765a4081ca44020b085c503200100326107a00804201d4020070200d0441c501800c10250000c01420311002e0003044142003e00e40712004207840d105043c0a0f0054004c00102c1040200d8451620800346520306141000408101c0303149000544c01814150f083c45a140443c443d40f146511030b4149840700342c1d4580d01c040e01c000c80c40000410341d840200001403650142d490200a440469034000c03000380410032080c00680741030107412031000000785801d0405c01860b0340003d942c90311600071100010b80d08001c0c00200c1d09400f1090014020a11202c0104009103503580100d017404a0b0800014480303480310454001c5e03a00a034000b840c0c018605050106 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 47583268 1250 47582018 47582039
    0x90201021e1b190303030507030b060309010507171e0c0f0d0e070b041a0a030902030d030c0f080609130201030e190515060a030305130509010303111507020c091801020c07 75
    0x240b02004458445600d21065800384001a40c0d000007002c040c2c8640220710214007c3d006501031040052a42e034803458036010f5180285000c0b01c5020010b107041c00c00c02c0c0710760307501402d090151540c40203006003c2c01000840e20341e007401801d560341030b10040044c0500850345002410060700c8036040490300b10802d800300761a0251942050b10040c0381048200081c030180e4400d400c40f00108ca500d80d0300c41c065028190020320452070302940500030002808849941a8011452104035840310030240840600486590400715150340d00040d6a4020614001c08201000e40b014814034010545100104419040c20311000500160303144229a03507007086400e114400c3d60020304035650005180407400250309160a1002405009000030006507011b078504655000d044060640300f02540d6038980100710345078035511007505005d01c1801601000c48900c1040c025042c0f84d0080001050341310400c02604005010410754100980c3d116260790303c00c1c00541000c05448019000c00c0d860b2411030380c0d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 47584518 1250 47583268 47583313
    0x106050105030105030a20040e0d090f050d0809130e0a03020f160b070303020415050a030e060601091502070302150403021908030a03020702010c050105010905180c0303030604090201021e 82
    0xc0c1030040900041c0a50303240000c020341060b0f003103040600300300302c9400b44006815105204a4025080090034a0590030020313400c11103c50036961084100c1e0b4400044510480d07501030168000d031040034a901190f800710182091402c0100112206080c801e08041241c8102840c408540c0003441084249601070002c1030010502e04050004110144140240c0700d450f4014001e4200002c102030081c94882d034151400741a0400c0f06a201e699075281c060850b4000140c04000682003c0c155880c4400100308180242c00c180c4030b600d40da60030700650026002405500208501c02c1c1c410010241c1e844402044182c20303010701482e5220b0550040c8004025924600c042c1c00c0c078060010400b082c0c00000b11841c4130038034503005880d24098401203860016018018219600381800031500004035800980124603100f03040a4400d2480c541c43e488900c0c001550754950002d100140140c241908814400780c8144144c03050400800f0303005c1042030780004140c01d103912121510180c010b0154494 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 47585768 1250 47584518 47584529
    0xc090103200f1305041b08010f06150e061e070f060b0604060c0209040f0501051008101514030a02060705010c021608030d0f0f0903260105060f18041406030106 70
    0x5550308003040041424821091180c54001d6550800170342030012940d0b008045880303a0b1100c1d04403036520103890b406040f84101c5a0b406918154000a02034070305000c2e51006c1e04c035030325696500070740c442c03c01c4155007010707198900c19000c1c5c402c60611038507c900107000c000e00c0b4590102d0303030007090704100084500203400b40e07006120810040c0038840c2c028918502850781100d0010b165070315490800c281205100c0001c210303608000a100911380f0b206044130036a02c2c44421101d00c0d60440002006507100b44400365442014010240a844120b101020b18140040c0c12114140091f40c0410002c1c0e1203504250740e0799540e007114240140c1d0503c2000200082d15649145e818101111142c41e0710540b051604000c1d6202034003528143d241d0460340c41d01c00101c90030081030b000e1f030a000d130040e04440f007850482c14400540074106851801118182c65024250328140002c80d540c410090380190889520040300821200c030756900e80c0150000b010483d400c400903414160141425102c0c143c100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 47587018 1250 47585768 47585779
    0x30c090f110415020a151e0c090504050406020403051c080a060509060105030a09050607020c03120c0d180b070311060a141302120601030c06081609030209090c09010320 74
    0x54034612010381c00795015220450034880020280300c030261701d02030301c100005003201c0b1519107440c400e001a6200c0207403020048041e8140d02e540301c4840c000c54a1110b0150041000701c10144100d01b0b00da80f059502521034000140b420341c0f640c5030f5514014840b03109005080c00d0510445166511844264200c1c100382000c0c0145e5040c00006545000b006104504010b40800040d0402e11640c12403404660014169840c0303080c032890013501d40c12054006806881001c1c5600a070f450104101e800e5211000b0160100010009084501340c5d0441c0c1c1120040a110302c000c10300200780d00003003409030321a8648610106000c405281800001004201054607055010b40344055281c0c015500c07480d0401340400b02401c0303100096640c05008902000d5100320750000c010414080c00d80310940d1800c3d00d41f510b841c1c2d181040d1101100c0e580090702c0003e0b4900c902000181001c40e0002d030006201070642d01c8482a5a000c258490b20990094850390480951014a03464200c50494507003401d035007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 47588268 1250 47587018 47587031
    0x212a01090813150804030309021f09050f0105030609160c0606091b08040b370207020405060901031502030411030a0f15020a05030105120304080d05090102010b1c03140d0204030c090f 80
    0x3002c4c099010041000c2c051580751500d0204658802c41581a020403244000d86003145c10000184258030034001c043c050810451030403515030061040d02d21400b0001c2501034542e44545030860340f00021007910060003021044140058840c0c0500406001c1c152000a826130b40c02c1c802d004500c40940c400700920000700140408554060441640302d000c0d03049031414148000c0c01c440305038617000903410700100000c0071900b17140d00301d400402e11540210f8003070140c0d441d56001c008a0507420702c40100a11845640500c9184050700a50780c00b030700458040e400b000c01c0e08042406c2051100044400234801d20004003040001d0f0095030f400034029034110f003807151500c40940b0324841030007000d10803140c0c10f4902c02c03d514200f08540c06490344005564024121483c050000d4115410f140c0c00341d400c080c40c0c090241412001500104e9906001c0100c44105850646600c800e1420404a181c01002004d4010a00e4002440114420a84000001d00e00910082124501407200d00d41504022 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 47589518 1250 47588268 47588309
    0x2120a0c0506060d08090d1112010b1203030f010e0405010f06060c050106080303070507031101020d021b010c03050408030703020306010905030d09061e0f08130215070203212a01090813 81
    0x42c01d507440b074181580c40c042d0403503640c140f2078000041c23200340301c0d80311103485070046444506401062999106940c100600180100400c0e03c03408100e0701034105442c08001085660043c10107660031501620001406020804480049d0f41c0301c1e810a20205002802c40410040244030340b10007846464080c1d803c5041c43d11000300248074184000d41000608061041510029811504030ba41411011542d68256809485000450b00d400090701c0d4601028038800d0750081c00345c42c0c4503685c401c144610350b681d040c1c002d4009402c050300351410002d16280200313103500c0400c030100740080b8540300c0100480c94000700609038240d605d004042ea20705094060b4072540c101c4811212030456090004c0180d86201e02242022180d0340044e51001c0301320541d5030042c05003401005498000c1e4151007403009419a0250070b000503a004c41003400b420031491607494440c41d003112250b5044030310038120540240703885094440c005419240010000307154022485544cc400c0010044c8030a2840380d810f182 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 47590768 1250 47589518 47589533
    0x10501030f21020c060a030e0118120e0901090e1005090313120209010e0c0d020d060f0e0609010e0703110d0606030c140706020f09030a11010305060105090901031202120a0c0506060d 80
    0x100500ca00a131400706d08204036601a0704000c0c00281d03203500070001048034000c0304c0c1450350b00900035140f000781c010000303201c036204483d601c41c007020290101302242d1170142860000d2800c24001103c6006802c442400020907000e000d005656500086449040108048038040a41d511000c2c0441403180004016111442070786d04440100720004042c0d0b8680c0001d0540f807047c0e01008031302502c00211402110b03010f520281c160f80a492034100d1190715440c030203d06400036101c641d48202e2020040054883c0460380300d6105886140104103004001145070b030301c2c1c0003090781480b440e80301c110034002c0c1c0303034036204004000030306d8a4070f4a40c040c2d5859011155220394503001d4805c41c0c001541840c50f101c1c500480d640c80401500300c5040041905107613040c6a020700d00c242c0020300f844080f8030150b10440c02d40f03ca48400130806c0b10982d02e1540c50500003070001203800150f000b15800302c0d50401150014100d5034145440d58948800c051512a00744030009143d00d114484d14aa00350209105 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 47592018 1250 47590768 47590783
    0xf0602030604061a030702160608060409020a0b07030302040905060f01140903070e0117060a0e07180f020301030b100e100504050709080f030c0708010b010509060307050705010501030f2102 83
    0x5000103a680d140c18002c00c0281c0781c01c0c0c10046564001030712105420045034000c600c60ba5a580c2568403410f010501a51070300b2285c0b03d01c2c800501400041402440d01c2d61156601da840100444075950b90b910514000b6044640c0a03000b02e0344c003250030094080c160080703581c424400c9070102a44800400080d01c07a1b40080740100c8501c60100340c0c1c0b90641c50801c20384028106000c4040030b150707952584014080d00011401d4190b00580001c100600da203806084070007442840500151810103815018400780b51340015016030716091201403040c82c0303200950285000700300f803070a40c1c905019030705178030314681d400051203200705000c0210441581401c00d0039150202d802043c02d88031054111810080ca070040520b6020713002100b80034110020040c40340e90380680c00e03129910350b9030700c5580c2280c6c140449280440ca04229121551424800540d448031302424060b06042c43c6841e9142101e000342c200300d0f1283d0b00c2103442d0050004031400301d401000440c1c00d0300050418000700a488604 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 47593268 1250 47592018 47592023
    0x1501030609020f120405010905060103060f140103030905010f090509072007051c14100c02010b061306200a03020102040911031e07020f0a11010810031e0602160c030c0803070f 77
    0xa5103001704003000003e40022000c1ca030080c00300d6041b9612814150020010a401005001c1c9003e081851409540303418074103ca401d515a03805180c0380a0044d5000b60410355102c0070001e42c0c00000c14030341e5070a18064000c0720540c3d200c003c6c800558020b040c40b0980085e80c000a80d100381010410303955600300207c080500da500342c50752450b652a18140c8086400340c500414002c0110b40300b083e40c0d05501100c1032400990007480740764020414014240324070090041e41481c3c5440030700c4103500410311280d24816509900a07030b483c000340ca081c240000d0407400c40c01031350000340030040024a0302520041c011502046031850a1105100790000c500a4240b9513101c000f000150465000740031580d2054040000d4030305030354043c900503078204401c0710403d02160145012401802950352428203403540108914190014511028600e4164a40c1160180c4c1c08003e02c260009111040f80c5050348180c0c401502d150070352800b421160080e030002a0140d0040c00701030041244070794000300054 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 47594518 1250 47593268 47593297
    0x110f0a03090809030a030809060601030b0904020d02030a08070602040906090203070c020409020411130e0a02210907030206070602030901051807030303091403030c07030e010201052401090e1501030609020f 90
    0x1c0791610300e001d40030344003070960706000d41c1e81e44005060708081c0c41c520484601068905559a1f8001581104c0c10040903d4102c05039100050050600f000c43c5010180010704658401205580e1800581d0103401c04855a80d00800c0800a8050780d0007080043c100c84407041d41546400c1600400b12071400c0e034041c1c4110b44451160096440b668020b211b0704500110590782c3e0305c40c01c03a8206c012041782c401c0d00300d1402c0311400103011801e01d01c00d945840100110415141c8403843e0126945400600007850742e011340301000005076641801000d070144110005600c0e46801201a400c6540003400303914101e01105111041000c042800380c1602c2d03241c100090556414201903007122072508082d10a8800001444441c9640c000900b41c038034401d9403020348a28485004a00b619025140740c0344c1858a6003109584c044c45a20380100f054062611240e52170303407040b058504281c16034084540440314181c0b55001c0d645402283c014240d03a82041d81391240d0614170803c607100d61880c90140c00d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 47595768 1250 47594518 47594531
    0x102010c0804081c0f020408120a05030103230d0e030c090405101a0a0605040312030905030306150c01091202250b03060a030b160909090b0c090d050f10110f0a03 71
    0x30702003440111130801c80314030810070900802c82c007070029401801020325034400c0005c58080c6206040c200c3d0174040c00d59661608591031942d5154020740b42d900c20b40c5d411030421413003012008003008200c00800745903441314a41c0c0342070020f060810646c4a086070040c807200382008041500020301246000c0071100004074000036120400340303520205003455201d0002c04c40010019444405801a00d020307081318940440300e003000b038084440a990041c1585c03c1440087c010340740c45486002d0b0a103507455414603250041d4000f5003165000e042c12101c1c140c00c1c24541a0140e810044a6904031204103455049001c0106201c9442054845c0c2140f44034000001405920780c840740b100110703400001d44545007072008078041201101d08614002402e903d50026442d04540031b500512034119082c02610344584541d42c43c04c0d88080c00f11078004100c038400704002041000f00d0400000e440014200c0d0320056051602592604c1c100c20400320400d1000e0441c1c001351a00318cc0021400f8100018503 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 47597018 1250 47595768 47595787
    0x1e0206090a110d081603110604031209030918140601020a0201020a1202070803030c0c1b010806010f140705030d050f0601081302040f06180b0907020304030f0203210a08060102010c080408 82
    0x601100c6000101030000202c2c5258070203041d20f2100b805c040c40303070310392140b0705401895a03035036204100c6010740020341802c0c00b6501c1e11025801034109601914180103071544812440d81301100c0c0344418125103544110009010114003c20390304444248040c111030801600004e5454080300000742c540c480e076140440b6414002c10061005000403000e0b02d4403850131401c080c8031a000500301c200b041c028080b001946440404108512032016107450b951902c84100450781c0c400b06402c0308080c0000344c1c20495801038480050b05809110300300640e5280c403102d060304203813103028200700296400340b824440141c0e08031040c1d6501048580051081402500028020700f080e482c4800401e8903100700429400c0a0744c0035010325071002102805040a208140100c1d000210b520a0040c0c00034407003440000d072140d1034003000324002021603010707003183c00000c040d40c1c5280791901100100015000700041d0410001da80c40039090008005056420401421800000b00014428100013031030066 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 47598268 1250 47597018 47597029
    0x803060402120403260601050307120e030412111503060909030f040306091a04150209060705151009060509060d0302031e031e090a03050702010c060203071e0206090a11 74
    0x2d040e14101c281c400141031504010340120962888120100c0b0294101e2a015103040301e00341c010300341a55804d11310703a6a14022201c0c203a0170f280705401592a0b00450000079001c10203840505000c80c0c400344558a00c0c6450300c0c60140c460b0585000d5107202e44240b21402069050300e031300000030b0b9107805159551a00351800e6210350340407034a00c000003250120600407560312045466202d40c651061260000002d400f51000032107001f400408180b19106140c4240c0c0c01400c40e40350050100e078107007109982c0c4d207810401c140c0089030407030708030000f00b08442c5240d401100003480150030801505044c1000700e038107200024110b0b03024860441d44035040510070422600f810100c2c0903281031040080100c88095401601d0804c0fa00c0812480d000710032312401c000a000d1503144000340494501e55806603040c0d08031080682c10302103d200c00d0400f10304140011032160007159250700120102c51241061150520740d810115805001003021000002a1a161954002201000355880c0400083c0e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 47599518 1250 47598268 47598277
    0x103080409020c0709060e040308150a0302010e06090a080309040c1403010b1c020a08090d020f06011502031b01091502090102060a1a0a030320190b0907050a080a0507050f0d0803060402 81
    0x980861030906d00083c0b0503d840c0d03400e8092446541d51803e5030300d40ae09041804000e5030743d8294400e8000307108100540c02919a20740050713010f407840d410070880c60001016007401e1381c00400950000503181203070b85080d02c40c000003052181420712609400c03000721003a901050140031107a50303000881c038140f4a0144138003841c9010241040d0340d120f05018005102c41c800b542d80d00c0a41c030905646000b21400441c0660310807102c1e200406413a1710b450b030304100d0b4090001001080d030104020072682030003d01e65100c81022500004203051515140c03510311200030701c5540300460f205025099450707078007250598010700f00c107201240ca8503188040500018182151030b600000d14030b000002c02d904080140503503e0702f10900714542b01c1a1030034580303841054070401c1031001d920603d140000d03412014142c00c5601082160041c44e01e500200b41e002d40c250700552050b5000c08628020009c0c1001540040c01042d66a2646400038002150070070100c1000100b003041c0c003100140e6592500d80c1070346c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 47600768 1250 47599518 47599529
    0x90105040306020d092003101109030f0f10151806150906090902040308070201120f060f090e070609050f030a021e1305040f0f030c0c0609090c080103080409020c07 72
    0x840d90b45190b04c0c0800c00525401e0f0084440d40b000110302c05045603100c43d440000e0703001030050000c1c0760340446250001d20b40e00e2920500102e052002030031a4030200400e0840d0304c2d802004003040c0c0b4051700380703074a860dc02c01c88408060341045844201b58048003002021600c4184d02c05850103003602100e005000d1582100000709120045195103a81c030000f5802101d4083d00d92044036074542c400d03102071740304900024010100412014005502c550a1280b009124000004461002851202c00d4604a9010f0681007010713140070310140300b00340b01d02d0681034a82402060014036114000c1c0c44070000b845110320801040300e5101035030314203100340503110344d0083c4140d10700030340b400e6058170210a450405004c0d2184010940c010280741c401c0c01e001c2c0350400100102400c66588a14032112031550441c100700b00401c0030400a280039030031101400320b80d280e05203210b0408541c84102c4030781c440e030542041494070041010800d04001c6030705550301043e0150f40c860301401040c1c0f6044051303000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 47602018 1250 47600768 47600771
    0xe01020c0312031b091818070803070204110c0d08090102040f0e010312080103080f0d020912060a05070207240201020c03030a090501050c030606180102011805011d0a0503030a02090105040306 84
    0x1d2400050b0000107620581ea00701c0104004000400302441c0e0380913000740d60b900b0400075046041d04c49a01c03c0c8081e44130074406044000d140c0d0303008080381854210340c0200d01c2d50340302280304802c52500d409400c0c44a810b2095440c04c1c038040e01b0b496942c40c0031200c2072005100e100804118030590a40444015004403888610026562100c081201b0000d03c411342c5c4e086580c4441c0440241309541040c100c942118001d4100300c5000202c0072180e01150995034100c0c3d00304201d07140d985440600f1489400c8142c0500110f25101204a040d250001c3c00301086400100c42480300350250440080d02c071145c424408a114620201139009108410450030244004020049011806e400026400c4c0c8101c009002544460400350039502040c1c611660082c4244a01460304005003010741c11128144000715201c0704211508090b98800c082c143c9242c0d460704400d4040c3c55914450000b00e50030ba10080800103c141c50b019260f00024010341d03c4103030009122030945c0c1c4103070b003a2006990403400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 47603268 1250 47602018 47602033
    0x609040b0102030d020720370e01120311031c1a09010b0705010c03060506180103060306050c0c0c0f06190c0b0a240501050a0e0a090204030c08070b0306100e01020c03 73
    0x80c5032031500b070030004c95521f9943e120b00d52a100d04000c41641d0503c800081200c0c00c3c00d5440c00c9091036413a01c100790014007a0b02d40800905c0b45e08111495000b4640d0f003104180103081c9040080450480548068190b4000c000481d80394410000c00d0302a1083c0c6100010403011a0000d00001800b82113021307440300e4900008150340d60168000c2500300d01c01c1d00200a0421580300030f80c20384080e44200c55200c082031295041d000d003440d0440c000100c051400081aa0322507550000f1079006030380400d1006800b0031000035000c41040b00c880300d00402c80783c200383e201000001801912032450040b410041140c000319869002d040c0a10010f64003105406461400b007404000400400c020040c842804094050b5002c5908050700c060305c070103035035080c500584200c05843c201059409503410103e400b60004603807030144081c0c0081c42c0b0903692042ca10b454403800a140100c182c00030460751104009202d42590340007001491040d142c10105d0242e2540c00c0141e0500c04101c0041303400d4040e040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 47604518 1250 47603268 47603273
    0xb0a032c03030108160e040b0402180c130608090a030302070c0305060103030c12030504020f0402030c0f1815031909170a0c05010507050901080a0209030a020d030203090102060a09020609040b0102030d0207 90
    0x400b55050b03c0100084401c115244100a0201d030403500c20420402c080341c0c0031a0115030314410442c1e0044c000303001055030075000307086100c8000c412143c1004980300403410402da041e90240243c02002c0701d05d440f1103d810080c800c240c403010150001810300d60300045100410109401290085400074280c0740c06607524100582a1494a581140c03101c1220140140040c020700c0303400d0203150083c5c10156000c81e84000e201c001d5202a040e0008803d00b0300495a52954090041c450301003980c0d4018401641c4c2c405108a1041d40c429038030700488207000b00881c0c21002072800c0c1041550201c00715980100d401c0c2608022014a0340c040002c4001801d010036036044030585c03110b14031410007040190f0700d00b00115014020590440c2c001440b09012030908065500504a448002800e4130110305807640003901e480c2d070301c80c4c3c12030241e00085040b41540da0107219440e4031001c07081003400029800e50000303810344508003209104503620b10644059900c00c1050f10360038a441d01086656142c2c60 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 47605768 1250 47604518 47604523
    0x80304060305010e0a2306190b0904060f0501080a0c0903060501030602091002120f0c1204060c0506070c030c020603100e0a090b090d091203020f01110a02010507090b0a032c 76
    0xd024040013901d002001c600c0702410f0b0306c60f0b4800c841001650103040711005103c04200b02d8060b000552003000b003003a60000801c00140300008248003c810780d961288036050105451080d1301440845001e00001c11903641c0005007540d0041801c1c10004102c1b506d0300b801e039000856900040d214614200000c001c00c1040c0d4006c10000d01c04a568007100808144104c1c0d0310103ca4600000c030741c60a124003003080803148094103c0010b02d400b590061401b00c4d5a0303039003d0300903600240c0000c4503684104144401409150f800080d645018002c58440751006000110407a200900400340003001400308001d4400e15006001c0d08140320050b0700b041d14001002c0c05038110140d07089409030022802c2c641c030000700054104132540711103030038919154450621416001e010b8055009455403403404810a100e43c03401d800d05002001c0d22881d940f503009003100c000804e43c40a0150407401071064110b208241c90005149203408074000101d8404401c0411000091114200b1b0081801c6d0807171901 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 47607018 1250 47605768 47605771
    0xb070c080c010c120f09020a05010c080d0e010b01120606091205030d0c02010b03010e0601180b0303040e0c0a0906020c03061b0d0f1a0a0b030103020904031407060506100302040803030a0e0106080304060305 90
    0x1120900030320000b580717550100c40400e10300130350254403420208135035406464488040c2c0d0040c42c1450401c204007900030f0070b942d006880c5242c143d544182103140d941c0c1040241c0c4540768001c0c0d08019080c01c04001070905440c074020001c0001c2990b60800c10880100201c4a080d1000f000900c0107014505020740a0442150300c24882e50810708034408070840003600c24100c1c0c0d0784031507036100c4242c4081090010003c40c2100d5826000420020400044038101c081c0243c0b6030300c3c1c120303a0b260b0340300400500e080119004801150855051070760b4a60380001d5281d0840106e448000c25500c01c40503040c41841909070144103241000308444031820254028a1031140b03a03008080c8100080c0700300401d11200e40a0507498041c01c0c0010b002504281c025558041c5c0b290400784181040c0c0d942c4040c80f900b100074126003207910f8170100141424041c4111340000360740d080c01d50400b0b080030017282d100e01004103581c000d5030303807258443c245100c25005130300103001c64815203550b070352121001030240c00c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 47608268 1250 47607018 47607047
    0xc0606080f0604030212130519150e0328021003181a010b0405030706030902040b0a090e0c1507030305060604050603011712090d06020d0f06080a0204050c03040b070c080c010c 77
    0xa10703100172601c6c4c4012011a40b04903030484485032039a003050200701c0100941c0f1042d007450303e80b0280c0410030008101c41502e04a1035a20fa02280d03041e000105440c0944c10100c42c0d15048a9600c44501455040070b0750404c240d0448800d494000b6100085001340000039a04403410040b0082d07a043c00760a92415154908013102c00d0f0042e81c036441100381c54031461103456010350240e80204a6240701e580400c000307500c0104086070f061002400903008025a030003245055996002e0607501d81d4041181d0380e407074001510f503680e444060124a200304d0141c001c02900b1b150301e0320001070302039583c041101c0292174000e000c9502ca503100d01350076500d2103601c0103002c024841d0242c800c03003c08842054900c1c40c3c4004002c58080c407426510708019420680d08103000b1030700e0790000c40078010075004940150045c9001804211010f00400060381e002802903441c4180800c14040400e0240e0750780e55002c44039007465890480f5524054000740315003008030115500e0003141000703d42c0e00104102c030f41302 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 47609518 1250 47608268 47608273
    0x106140f0a03020102030a050c01060506030a060611011103160306030203010504050303100e01030203120a120603060b010e061821060106090f050306160e0102010b060c0304170609030403030c0606080f06040302 92
    0x11210000e006061040303002c043d016a005101d5130700c55a10610040c220040350f0300000c02c140d80d90b40c0109045e50802c0d0764110041e81c5800042c0441940010280c120030b9107003000348141c1c550608100c00314400901080c031258402d10380c061045019802003802503034041d008001500c2d140c28819142e8205848004195031a1030000959900440b181c2c1d0583c1c2c4c00074013400e2900180742c088402640995545c074103005a5611a42c44c0b64400d1007034000540c0102c0c8085517040010b800101400400e141041c030466041c0440354108000454446581d80181c034401c41c804802d03101c6200b05c0203007046525291041c0c5002240607036001d201d400844d0403210000f0308050303d601c00c142e1030b0481250000d84041d0042514800716100780700e1407a84d5101030000203000f009000204450754808209880300394800202001601041c00300c2c600d0384480400500782c141080e8903143d0700c9200da4407000c0c08000005441d50180040d0f40d00540c000c150000442d0607805040c0352075915094120760580250 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 47610768 1250 47609518 47609539
    0xa06080105072105070c050a120912080f0f1e070b0a020c0a0303090c0512070e07030227060904022a0c0f1c0c06050304050c180103020105030a090203010614 69
    0x281c050100e000e00b01d400d051420300f1502d481480c00c0000e0200422140c01c01c001c003260180400c0003480416105c1c1e01600781c0001c00040700345c010f01080309a038410036854280c04111804528218196801a8481ca00190342d5500507010079016000f84c42d0009191041d034008000307414400c100400c41c16101c0e9110540c1503603809080401c034003600341d0300341464004103c00c0c400240300703a010301c2885224400310305199032210301140f500d80c098a10001640d00c4080203000c0e0720703005400644e010176645410751601c1080356040c0711045001341c411000041c1c2c04103900c450b070b581c10161552a44003510844d2145107800388070707020003d4402c0c401c0071005e100102420815001c00c12842411016041440e04100b881c01d00c2000000d00002ea525200d11904d0314001130860020f030b400401c0160388443e03c1b4189801d20f54100003e02c5129442001a81c1c11031510200f80d8a40ca41100e0b0242801038690b900c0100450251101400095040d441c1c203c01140b010f02583d4803d25100c001e6444c0c1508 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 47612018 1250 47610768 47610781
    0xe1e070203090a05100c140f070b03060d1205091008061309020a17100507210c140c030c060f0a0e1f09020a030501050c03071713060c090e0a06080105 66
    0x140d1280d00302c42ca410040100044c0014102034030b0480001c0e0b00340c0351061036a45692114403d0b80316100c80d80480f500003601c0082900c00c20415a0090241d450400789103081007000200e03005000c11000780040340342c9510b600c0650060013070300c100d41e1000d48a070641d0412000001d01c0c0040071644a48600c000d0541343d150082c81d44902c111140e4050136101186080038880e081940200c0d0104c03040d8030a01703080c090803a0907400341c40c0c01a00c1c107880c1c401210340c0403140c070048803078800c210030011071610440c07400f00c951104400d4581317041003440c0c0c2e40d0341003020321a44c20362042d03200220b0144200c100303004502048500c05441104c2c2d030001081258190a81c0c242c81d85400020b03c16415003000a0300707810180c55110002040c8024034400401c1c1d586e50b151030039250100c40100381201e010042189540c0c0041805005c00544c040128991400a4007080d400694090103030000d641c031200c1d12700d058040d042070005001100c1440c8110718001c10442c02400040c000d49015500f020040b800c2d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 47613268 1250 47612018 47612023
    0x108160602011a01050c03070606030c0503011b120b010e041506020105160504140109050d06020a0e060306180c0408030d06050a08070b030a180206120708070905060a180e1e0702 78
    0x801c4400e505014040050903c011101a0450240d440c510300081101b400010958400c15005612410754000c2c018075000401d42103c0c000c42c0411071104083c000c841c08240c2c4560300740d03052844a24001482d00325100101c49a000e9035a40d582c006180250382d01070054403d000341d00300c6d03442d64001e2006a0300d0b11030268403192104611408a0000d0000b48815803003c003100080c8801807529a007041d43d03400000700e0a00b0700324000c1c2d0310305600046800c050b582c400305011040304107980d514914103006010407000c100c6114082e101814074030200d1204401041220010040c9000301d030748800b803d204140003419544951032250071100400241c6400c007241a2045401502d00c0c941135076202070380c11010305284540080c0d60b5041d45200c10060790740401030070350401960010405813800c0800580456800740c4000103200c107404007004256a03a2045070007100b26482d00c8081241c80341140d0500d005aa04406540094401080107009120a05c0100c0c11001e08080400c4c2e00d881c40180c0c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 47614518 1250 47613268 47613281
    0x90507061b140f030a0503091510050108130204020a020c0a12030f0c0f0609080403061508030d020a090f0824010803030a021c060e011401020c060d0507020a0b010816060201 76
    0xa02542003155800c02042100c20300050369803081c2d003a00c0010304014161821540603422070000706030007109002d8251020030004883c410110807208050070074010700500b00595108041c10030070b0100001c3c003041d0382e491603400f9039903000c0d04c1592207401c21140070b519400c420812500507152001c0000f5040c210310318084855805460780b255a545200c8112402c4442c0c0506840400c1da804100b00054040d00c00c4006490043d0300c25900c440c1586801401d075410701807800d04151806400340598040402210009207407248010303519080c415056a00180d2684802411108800c0c005102003000c9683c081d0b69442051800f070680d4035451815503d6000e00030302519a1040c400210121030741c0d0b0062401603100d580061202103c401000143c880c550080140c02e00002c004020403d03e0000c05400e24000740064040b04408502040032400ac0c0143d18035240c2c2c80d00b0201d602d450092050141068111403040c03195a16841c0003980d512810201c1200e410b019003000480f14810321802c0d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 47615768 1250 47614518 47614547
    0xc050102010b0603061f020708060f010918020a090209010e04020301080d0206060607050a021909050a0b030c0102030705061902190302090a0f05090412030b03100b03060105010201021c0e010204050d0609050706 92
    0x500c80c0320080f080041c04030704907500e0047d07115043c0c02091000017003000612035030201d4002c044641c10440c20000395051054940440341005084d8801607407501d00342400d88001050040e214000e250040783d00c0c4400c4900c49410910010000c210142d020401601e022015000c035030203038480c5018800d0b58401c44a01818036080803103003600519210f68801020b00305a001d100c2495240e0a031481101e105442c42800c0c280e48014120882c101480b001d000c0d55801d00145041c80d01e140c81c1c56483d0030700200b5000b09815100d510702401a01581510f4910051408441200c130f20044c000d0001d5200c01e104500c29a14180d0005a502c6801004000e41744d0180c650b01443d122a9101141c04000204000c103041d203442010a05440c108504201e0307059a507004902403525200303240c1013843c181c02c018116401000140d142605014032000e851030013280000320203500d01035040c0280290303040307503038000301c0412a2000e00c5042d40004030040e00800503246059502c401c00d03591540804201d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 47617018 1250 47615768 47615779
    0x6010506041a0306040f0606020c0907080108070504020705030408030a121b05160515090304090e0d050714071503050a05070f020606040b01170103050319020a080d09030c020a030c050102010b060306 87
    0x2a01034402d40700603607046000680049030460041009005941017900b00e4030041e4809102d0041e10302e02000a2900018581046040395061031205602c421080c00b035180115000070b403d1040000400888000b0400723030055a031160b4460000803c03001c1524464141d442c02c148010742061b102009100a03401daa0726940e2601c010050904561300007501d00707440c5401a4040c0c03802d28580404503a00c500350040255685a003881c10b0701046858180d113000e0390f60320a80b40c00c1071142d0041c040310074440d0000360054041b140c5c100224034164164100d44551440c007100f100e1500e0305504418020102c0503418401d40c2c0d14804126080b224400b40c402c0141d0016021030a507040545c0030030440350041c500344a09044201c404490100281e004480a600004a43e03c1e40d200d01c007031000c4030b40c0e000c1c400790289040980b680f18035405803083c1508250740d80c0000c0300070940103101c0844641e601030031614440c2c2d62800c01c080c800798180302c1c04d8055400c00741c10140320b00e01101141e2043d90b00401d07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 47618268 1250 47617018 47617049
    0x8010e071a070312021c0606031401050a050918031210060f120f02090616020901120b010510030b1906021908070b0c120406020702042003041719050306030601050604 73
    0x1411200c800184040309682c82e4200321160b01d10300d005041c2001c40b0034440c0007142e80340c5041001001ca8825040c1103412b402500018080ca0f034135640c210089a108175000d11058481542804020640054028503840002001700c16811000e081d80d1142440120a071801c41e40d6500c03e890410355402080001000c200304800c05c03407072590160760001e40c4408010704182c940e4002c503c80781c0c800218100150721b50715600742140f070851322a5016200420b068144440316135510b0720064018010603100d04c5040a452003074a1013a80070340c90803003008092964605d144510088002c0e0300b40140340040c0103460841200c8501c50545245a80c2d100c03089034075088254646154100019081958a61302003000d140400a009400c6000c0d40c06030b44c0c0140e8454403481080111080300c41845418034039460000904c0b5641030640307a0140d089001d40009000500744801d00f4407906031042c1c200d40c00140010045a4880041e6109581c15011a511642c80780c0c1001024003491180180042c0841d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 47619518 1250 47618268 47618273
    0x1403070210200a050d05010801020405090a0b0310230a0b0102030f160222050906040201080403030b01031d011d03040b04050d0c03060504140d080c19110708010e071a07 74
    0x38801d140b05038100750616266004401511115800342c0c080b50300160b004207502c121150184902401029000003c514181ca002c000c1000d00d0b40007404c1c4c400a59554003642c802d61018090840364014100c0e040003288a6110f0030200740d000c4204091a014032000000d5400f92507100391101082c050f0011420048070f141c4904283e4803901981348000340c00b25132400181c071150780c07502d4503411007d10464420940c410303000444600424404065008000b84030260b40c000841540164141c40c1c0800c1051036100140d01501c15400c40348600e400f10125914107203419485036504400300c0c0c2400ca400c5010290351582ca01a0340a0210b084600708000c001070702c3c2102c03150744801c2c46501802141540d80c1ca905044403030440d002d4804980d4200303400c40f0340505103c0b400511501e402c260f003043c205144200c02500034000c1010001c0d000e02900290a0f02a50f4000c8841d07807000e044502482c9c5560000713020701490f40da50080c0d40b1450b40c021039900383c0ca1940c0e0020000f9045014204811034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 47620768 1250 47619518 47619521
    0x405060609071407060908040f0312020c0a0501032c0624090a0203090f030703030b1302070c092003150a0605031e0a0902041a0a0501090305070308031f12031403070210 74
    0x4c3c401110003541d00c003071050001c4c1c99207001d48002d0144407010303880d55245081c02d080c0494a40400ca04542010410f0480c55650202c011300b540c0c5c1c2840c0000390149131401c0c0c050840d01741070000d01010289024541701003800200680305081c414a9002040c0450440007c01c81c201d80042da80102e0180000301d060540d036000c1e48d44910392204444501501252981c10b580c040c020070340010f902c9101d810524185a01a82d18092041600314036280f09500c85054098150181c4d04c5003948403015464040706842e002d1034540750750800d480e5207042031122040c0c1c0711048020b071400761005041c001790403800798050700d100e0b8402102c00c000348100c0c140d0844800b20010541b4002c00d68030507900000d80c8a030700c10070303100802800900007442d2221007001901e48075a80680d04011650b00c00b840021800300b600000c030b07540701e42516100e03203a078200c280c040095540180700c8034040c031000092101c0c50301c3d801000342d4040e480e081408545000019202d100c11500e25025078018501009541c015 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 47622018 1250 47620768 47620777
    0x1009020607020a0f1517190b060a050c070501030203060d0f05070e0f0906010e06010c140111120411030a080306010e03070503030c0c0a09020a0c021512040b04050606090714 76
    0x80c400e80c0741c40d50941c0001c100b00c1c0c8540000c46122030104c01400b03084154a94012010050f04021900c2a103a010516580c00001c0504451200f01d20640f0020031154201c503102040040403103440c0c50306400d008000d500a000400c0c04d038410200005000d5020384200c9000b68405411809001b2050f250001000d040c00c008884512401c0c0000501140005d01140285103480b01650079003003030040149000d0060700700c1000041c42c10700348200380c2c0c0c001c0091524030b68054859035080e51481e03041401800354000f9130ac5880703c0000c2d401780580d0481c22480c85a4800d0400040c84600c44052560340e0840f028000c1c8440810004680298010200c99003206802800c9401064032180800d04641002041d00401d82c0090b03940302c064a80080c844001d46005041142000c40c40d5200808803450f45502a0003112003a040e0020380a05004803031911445007400c24590030310340340403105812700302c030700f6503150065001007007491422241444c040c0300d03581d41f5003504624069011110751312 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 47623268 1250 47622018 47622023
    0xa0201140403090b07290402010f02010e0304120804050604030302070e0703050601051e160503030709050d02091501020a051203100501081303120e011b020d0203211306050a060f05121009 82
    0x1d0760603814010840c0c282d02e1b0758110006040e14001e81441e10002d0300750705142c0d01d00f41c10b5904207c0798011070740000090381e045905d1299410030109460801c0c41d018852904495008107002401006060300005c3c1c0304200e13008811400001d41e184941102120015243c0350700188040027a4181c0da80311005240c00c40c0346c400140d5240410400d26514030560a40d0222460b400100c204030310326811a46210041006650b50002e1081135400181030362001456008500c440250308809a407082040300c0c4420f510000700c99058134056000c44190300102c50740700e031000500c40e000c1980d500c42e500c1c803400f540e030749841101d0302d800a5805031403029a0460407035089644604248401c6424094030b010000c16420508e000700139800000d0401401d11000400e43d8410415100b4108003c200300c14000080c000400c02078481407103401e0034a083e0403029101900b040d081c000c0200c010f52081c0119001c440400c64029901d000b070281400d815580c40603075130040045100b44600e90b0300f1a400c40351 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 47624518 1250 47623268 47623283
    0x60504080c1e0907080103060c110c091b0706020403050606040207021f120908040f050103090206030a09112d0f030d030504140d0915020106030b0c0c070b0409020a0201140403090b07 80
    0x282e000003003040e0490490340c4000092a620040060004900c00c8180061162800b4010004d9502c82c5585d1902e070589280d0081c510030300000c0f80c014046035441013030602001000c0c0d403071141d03080c00d802a400a0105440ca80207890108000f40351500c02c5500c9194041d200014403031442d14480301a00c00d600042d4180445881866402085845940d04480c460262103807a281032410303800c500c4000f80c100d07505140c07500c0c2c10000541e0329142034a51110030004c000c0740304c0c4c0880c60f02c8010b5000018209400019008000c01251071014030304140e084d00f01d07002510820844100b19104401100b0540c050b04034404440ca028820741101e41c0c01401001c0c0c1c0c0c842981e074034502030324110500d864200021350100c1c051068400450300c2042d0149144000e111143c1507445100c0842009000344560a00005440c1034a900500c1010700600601451030740fa50b03591510342004c0d501102004e4015440d10341d00411074103004101c1c9016a42650b241102e860800e1030249943e80421403d84804c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 47625768 1250 47624518 47624569
    0xc0311030109021b01050c041811030a0605010305090d05031801090c0e04030f05180f040b0a03050601140a1d090a06020301090b0f1f0509012a0c060504080c 69
    0x4041080065000b45000c080050380d41c000c1500550040600d4446075003140d0401050200828684064400313981c130150303113a5040d000d4008034030010582443c2e583c070307a240301008004051142d6401700c42100c0003030306c05100c1130351000200c03038440d02942000700100380144041440f8021a070072220100704c6440000509118545807103a03c02866800140100400c0741000200b560000c06080c40d40102d08100c0d00b0305201c03c907104803121103500c9141c040c91551481c0d42c201c0da00e0b03421107000445e000e4140b0110985034140700c0d81f0b50381d09000d001101c0e5002e00f100c00c1d041c28180c0c4000100c42d0912841103c8200c450318003056200e02501122203407142c20a84004903455100071802420886400240409071070709001401003801a203030700c81c06809014a030b4448208d01c14110240741450a0b90b90740c00040c0050320344581c0a600341104a0a40c12040192090f90400d01c0b803032400748000e84a0b45907125805c682610480c09020115082500d0000407800d0107040b607050a801c10b4004c441a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 47627018 1250 47625768 47625791
    0x308071106010305010203040c060807090b030a060e0a0603060e0f03030610090503060702060a050105011d040b13090602090f04150308090d14010f06080609070303210e0307060e061003060c03 84
    0x40207400c0c0c0065802d80d50000c00c0c041000110801c0c00004c0c80f05041603d0305161003800a0680d11084c4140c0c0021200000012840c1560b648050040c00c14100245243d040c80299900105240d01049030701903e043c0380302044078070014104140e65003000003980385507a504140017078040303034139039141c24813070300d40c6000c1074550741400324510944441c2c0c002c16152038050103981c20380d1010fa0200741400304106030880c9800c2c00303001300c6081a1051301e002c14a09101d5000c0340035003205050000c070030752034501890200703c1d05030018600c8020445082c2d40c088600d0042000f1149032241e40c0c146120f04100c20000102403d0281c51084002002950b142d42d01d0b0f117452240c02840041c810f000c0c0d54923080130744003400e10700ca00405004407134002c001c0780c90f0a290840d650046404040c0a00204103403082403c1410088220300114816042c02465401b0302d0060f03490b0004030303007110308504060302040c0d55040050038500c19881907000c101800c0ca5520f821000f0204001000b00f01902da000c000340c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 47628268 1250 47627018 47627023
    0x4090203030708031005010c0807060b031018050606060301050306010e09010b0a24090e010504020903190f1e0b1b12010303050306030106090501080c060c0f06040303020909071b03080711 82
    0x20b41c900414445a5030b15003c0d650b02c054940d1500f00d1410300c240c24460b000070a2240c0c050341c7c0c1d40c40d03100340c0001d44040010006458500b121918000442c00e00b2400300520581200c2c080020b0311403411140e10b0b85030f0307504001d1280802d000300c81e091342c4000010401210703004007542c0c100300c0d10030002400c4c04107000032510f03405994024030b28460401c602810f806010700341584810300940741101c1451304060900d44000810311586119a03000f203203031800d0b9038040c0484031070f40034039810019140c42d0501e007170401e5040800060790b546944480d09095500c105000c95100c1d0390107040845155907401c000601440d91041c05500b00b0b1050102c402803c098850070307800ba5019468803078a0385418010103080d1812900b10800a07030801c0300401030520300040d0070060131000c0300c02d641c5030444c140c15146040b810112141f003030310070319080c0001c1c1034041c0d00406400c80141e0340d0765041d54920703000b55114040c014018880b250f12400303580101c6d1042585941100712803510050502050ae040b61 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 47629518 1250 47628268 47628277
    0x180415021201140301050411040506060f030405151602030403030c08090d050105040638030115090f14070203070204050c0c03040605030a14010f0e04051606021e0115050409020409020303 82
    0x102030700d4120018080c0d400414071406002d44100d00a00151a00745d54802c1541c065106c0f96024685a6012030200c2e40d5400c01d48141140428403940c5038980703400c0255079030389240c0c102d032034680d07081001c00c81e0714204241d500c0640c0f0340e0350011494149103a5044a80e151714541c151403601c2d0034040440b0540d5101e80301c1d03441d54001d00002c145030a16041c45030403207420401400d50380346120030814201a66011014005410b000304414070301d020004680036003d000640d04c180d0683c0e00c008100b01c2e0090740004407160a01c0010485c1c48103e4115165203001a0384400150f4070520204005181c950000742e07201d18910802e40c2895480a050382c51608240c00031800b00c4c3c0040100282083e0900c912450841c80c0400d107245945410821116002d9600616451044400024050100405c20914101c00c1301103d00915035440740004d441e0118803c180e200d40c82d03581550b01200c0c0050281500001c0d0480c02002c203075240500f040b006248a50041f80c025442e4549900540d03010300181 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 47630768 1250 47629518 47629537
    0x10b040228090f05010c0f0501090308070905090c120402010e130603020f09040b060603041a040f020108091b0409050a0503030103080304020a0603020414010507051608030d060b0301030218041502 86
    0x400e40c1d8240400205810101d5940004001d81d0010422200f0303148449030701141d01c2030a0183d08076080303090044c4000407070b07036025103150309000760b1204066100600764840c134260350315090001d48800030408000d0303043d204203c200300d0034405028902d00350414150802d105041c080245040c01300840d422021208007540000e503288000c20960600c0741c44080c8078102100d0f050210302e89035481c07060b070f0a0302410042c001c90001c0f000a040001800ca030400d1024503196185c030520307042c640400c45608402c4124001038202c0e010400f01d140008034004680112102c60707201c04117003014040203240c034403070aa400d8881d1545a00c0860014001127010714064070a1550740d1401c3c0c0144850840c09a202104051040200b0400e2400d50200c24071045000d20340a42d44070014242071741f40500c1c6814400c10a095200b0018408a0000040000ca081e10308140b1000d40c0d10540083c1502092001075006840a0f6681c0c4048030340c0c81c3e00c01d030f0081c49458409102c038600c3c1008401c0380c2003041e04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 47632018 1250 47630768 47630797
    0x7020313300b010e0c0d0e06070f020307050714010210050c04050111060405070303140403140d020601080109020135090d08371805160f060c1103010b0402 68
    0x3900050103a800084401258a00d45400c0e07981859071144032805051180703105054440b004108000349210864142009054007880041060800a0713111401540e03a1004074080d00503c045950000c010360b0220f942090180003110300d014021640c00700c0c05001d841c11402a6a030007030007006d403489040d02508007030500701e0726a81040c00140030984407010070742480e031020382000009680010044e05403507051a040000c40108440d200241c015034000400460401e15040203500c400900c021007201c9580c01c071070180e641d614040d801c8a0144001034002418007410203070300711003842d40d0345039080000f4a150328076007925003081d131030740055500f4030054205c0c2000016103a8420361941e0003050340f24440c6907032b50542200d0788900540f105a8600c5082c6080c40c24040301d10b81e880505000c0d24100c0110f4800076a2511540703c42144800540318403ea02010900c140c00324403110650310326440c0c590030060f01c0d49400c14003400c0551215450341d06c44880358015110785c00a0014207141005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 47633268 1250 47632018 47632049
    0xd0f050907080a0b0114010311180f1c03030518010e07030303111303030309060b090118060803070f1b0816090c02010c02100b03010f090f0309060f090302040507020313 74
    0xc4a03414205164010701032a840559100e002c21004046241110840035051000303001090040e80034203070401e0b0b41d007840007001c240c00d800d0302c00302801440000c0c0202c8450200c1d8050200300030005400c1108400080118005100061700943c08141c22450304038186803400d03c220f104ca425100394188028468004007010020107800d4080c08011401c01d811140c200302c0507042c1c0789016800351201908240c1c0f81d281180a12100b90b0050455103c040e1006100f0b44e1240da440003850000005400d0061a0100000d1190b6000c0107950b0032950111804078a40700301d444031881c082c21080702051000f80c1d15030004407034108000800d805c0340c40e580a10305040c030b86000042201c5042da481e9040d13906004c5080d11a55010802a080304000040091001e108001090041c0540180c01800c2440c02d01050207102185101c0440148a640c80390405611344408072807110410784101d0201d190b21900b40014500391300150ba0041503481200d0420b01035441120040390207501443c0422844007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 47634518 1250 47633268 47633281
    0x206090d1a0c1207080402130e0102030105120a0b040f050f0703060b090a0c0903020907050f0708091009030c0905070c2306070c0203150a0603021305060103060603060803030601030e030d0f05 84
    0x400c0a640501c240410609043c00c1107543d80249000501903c108502c602c0010210354649500c443c80041c1d44100704840c1202c2c1d6000782c000d500a004040c85202c00084600340040002140b01103a6401080e4031200e850b9076923020f280c3e40c41d1000403515401080030722451074000b04043110046005072400720b203101d00b050a010100c0c42c06030425034031a041101240007260014241320460340d050780d0b420b6040c0c0c2c444004172140d00400c1a001f851100c0001d0100500407a40060050108112030815040403080f10507510030382a440000e2841c411017004202c1001540c5c0025403104c294100042200307001e03500d01e0000c103100040701542200e0b103a41c0c501003020401c516079003c011801c4c00d090300ca4040d00000e564110105030240c0d29040c000c001503031800141c02940c01903074064205140007000445180203003030100d4032580003a01d4074000058041c860300402084900700d0001d14510f07140c8500440260104950070901440f0070000c00100c1841480741c0080c0c00c1a1007400159424040c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 47635768 1250 47634518 47634563
    0x5010509131e02011206062303061507080d0207031d0301050714220b03040b09010207080702010c0c0b030c040513090c1e030506040b06010807020106030302030a0c0206090d 76
    0x900a140c0d07694442091500250700501c11590034030700c0c22941d10140095100480f44940307000e403a203003100e04051001414580028600c43c03442c1d02070b02c00c10742da418808103403415030100f2280c055000d8990540c03070044502e44e9004040c0b44e070007004041c3c82d0107040982c1409036448804110001038415070701011106000f10600b14512088000b4031980c101260001c1184400c80d049281002c000141d4985248648440c00840c61000c0305091049507581070010403a00222800d8544441e440e001882100c3d041c401c40f0030030383c0c3c4031581509100940e0011148412222070886070f0b15216100861a1a90030019500c100c5095902582d50381c108018891071754494954070f5521400e100307102d000500e0143d4141d0035078035003e484625481c00094803010110003035001911134010710041c0f0061014411999201e03540a8a4411203074a91405c202d0895185200286c01600f040c042d4032000c3c2e100302005801240020581c5003003c64050001d464081c00440444000d9003400d142c00d4a4040f0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 47637018 1250 47635768 47635771
    0x132916030603080d0209030708010c03240807090c020309030a140115050f120703080309010b0109060806090a200d05040201030501051f0f030e03030f1f0b04120201111005010509 78
    0x49180501c0031514690f142003650050300d10001d109a0045826130154404008140041c0f03040402031192650302c40d400340c0201558030041c007044202c00c001c03c01010031074900ca000c541c3c0410040a046183c800f0220040048002e943d085000800c40d41d461980d0800101c416940035910881710300d01d40242c80c07400c4954500e84005000d00c0c0e10820003150303940142c2c242c5600d505681842c8844203c0c0c000c0b5040c10740755000145410804421b20210301d03815400901102401c1c2c0303507a900c4985503c0c1c144d80415044070407540c0104000d0014007480c0180e0000e060951445002516042121414013104d400504150b8200c61f514002c000c00c0d0340c0e15003d501c3c01084160355510202d90452668030200d59000405800e0015240b41c0c42882e5202ea840890000596800d1340d40381c0c205901403003500902900c04003008035601c0a0415050f800c106800201c1c3c0d010440f15160034900001c1700c1c107003254908107074184100b4201c012a403800601148200903c0c8079400030f000c0d8107080800903031a20 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 47638268 1250 47637018 47637061
    0x91706011e0501021b06070203030307050c0106060302040e0601030c21051e0c0a050711060712090902130515070c0806190615030f0908040602030a261329 68
    0x80c807501c20003059801080d400c911651600704100d22044070303000702c0c0702d6100301c060003505484004200076203681c1c420054041e8846002c02405829500d000480c103034003443c014450b80443c050080f900c40d6020b6400541030014a050246041c07584240390f048180f40002c1a0f14a0b0361114100190030f2114600f461200303c0382048946d407824500d210745000c2c0240c04c200d4040c0840000c1e040309000c505506000c2c00781009001c1a40c1d0000f9140c150721001c28110f4038008100c40709004076903441c080c0250b48184c12030503003801d140c1d440c0c2420804041280c9100c000009010002c4401180800c4a414044c01201001705000d04220301040c0f103640302030381d50b00d80c00f52a01c0070a0100303000c10340448080c44180e103000b05002c0500b120740c200170022100c000342035000014000641503008000340156a2543c0c40341c02c2e0b0104a400c10b100584000301018070703004541d1001848440524a03a4079491740a41c00340c41d8091594044128003104078a0700d428032400362030410200307105490b0b20465501 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 47639518 1250 47638268 47638319
    0x616030201050901180f0305040e040f02011704021c031e05030612030a08070807030b030106090b1005040b07060504081b0105060f0102030c06010501030f0f1406010e03030a12020a09170601 83
    0x1ca078010b140151700d4900100a0503020b0b080030190616201d4000d95002d44600340700a11941410f1801840c40c01284104a0100d10721030b07180442548043d94281c40b4540207070a812580c0141840c862a0980010044050040c40100500300010302c414024244525031511507a0741030203400c00c240230807810100200c1c1d03442040b266102550009449400541c1d038200342d213003511000b2080c3c0c0a00700b884000c5405610b01100010038004640200d129043c045d00d810314043e107845022540c83c480c3e4003d00d02d400408105240c0000d41e15071081e9806400364103124240326100c8560301e507e030243d11a400150b91900c00b80009440c0003180000927803000d000561415040f41d824640300c090511a442c1030650310301d8130f500d000b2107503000403641843d40c5004003c0303203550807520385050314180c1d40d00f80002c05000e0180014100001229024040c9494a030440311030840b03000b029620100348003040101700000020748202426020019034084409442d46605141c40004d90400b842c00045600 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 47640768 1250 47639518 47639531
    0xf0618080703030f0e03070605010306050c0405060405190f0803040f0504141612090510061d01090b0a0b030403020a020103050c030621010204030c081014160315050616030201050901 80
    0xe00c29000710361101d5407600740803070b0030390f0142e8000009114284580405000000328030080102030381c8040e044e00c0c803c8008000d151140365682485001e01d000c1c094000398104400e11603490040703000b210600d00720141c030701100e4645111410260a6034001e07040d56101103801e1006030128045035011740016a0200002e502c080f4120320701c0000075180030030f03449104803140d4040713208801c00408a40e6103c401d02403800c00d0701e0060f598043c080308800120346464000301d421266120598140d12100c668810b2503401c00354250001c00703100b401306602071928840069030300814000b8610403800fa4016001c3c1d60034500014080d248000d000c442103203410010068150344d40070f5562003003182a0105101c40d1030703401a081c02480b40b074002400040c428940004c2d0035000082c102c84a601000091002c1402180a00366041050b0ba10a04004141c80ca01880500c694040301c004042a011020101d54402c042a550f0344886218412855600003000515409010345078000c50110000c0140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 47642018 1250 47640768 47640773
    0xb0304050c04020a050d0606020a02060306040f0e01050c07110321180a06090302030628020f07060608160905150607030309020a03120311040b041e030b070909060608070e2404030f0618 81
    0x158407004ec031440c0b245a03102042321440324250310040d030080f18000200705904024401910741d030810ba00c101e800040b8881481000d0401080d000002c000d24a590304e68200c4030011b01005400000c8401c1c0c02103030564016000760340d000c008500030b044d6516100b100350b0442c01458103059005012086203035015400720040a0307007800301c85802900380001601c0c1c000e650304864445c8568000540031a00b8a440440e4244d1b0100d10081d0036500b03913040340c10709591008540c0581d2070456005a20501e404841c8045042200007407141a202e4900003c0216175503000a1060ba07180c1c0050342d2100e01e01c22010760180e0107100303950748524440e400900f0545008400303040c52149000701d504074140f01c1311011886229069003400755511085c1e965103490006402090300d056482000085030030050000340c4980100030740d5000c1c07411030b51181c1d000303109003040c4010b0801400440f82002c0c41121002c1d40b00304000086e0001d0b41c403a0080c403080005d181890300c20790b10b01200d5145011101550f9500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 47643268 1250 47642018 47642029
    0x313021224092a01050409060b0c0c031c030b0109090507120e030909040602090105070b0108010506041a0117040206131205070501090e0a0e0a020d0305031602060603070b0304050c04020a050d0606020a02 89
    0x61070304203e40d46988400007100413901c1d4000c541c4003100c240d003408008900c100040001d0001510060200c406101481003050360340d410202c40c810342036006050200d05103200360043c0301c245006050840c0ca0550b50b9140508441d022504040042c070781c51628500f00009024003100852004001c41c100801034002540c08134000d0401840b5640c001000556079009200b0b030342505810680030301e419030755540c030540640000c0b0f0749039110301e20f001519028950b6500360f4070b084d544180d40f50821054901000c0072620000382c401c1c1e80c800002d12040c1407500300b03524070002810390020800c00b031907450310b0203501c0d0170400c2c2c2203103040c443c401105010400460328120762000c180c49000c41e000566049041c03e041c440100650004041d08001d018035803c0001036000700c100c01c040003021484a10100d8941d507080d100c840c0c4c140c105007020003000504002968110740104192218020402c1c000f40480e0f1080030030b80040344011450b1324598a09200d2080204968000350000346181d03030004d113 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 47644518 1250 47643268 47643313
    0x6050906031e01090c15030b06030c03060d050c030f150c07030f121506080711010c02030d110910171005031207030210051f050a0803031302122409 65
    0x40c940b040e008046030508007500250300b00380e004182c01700840d40782c0022905100320f00312854082414031a500f0107a042480c01c0b00d00c1001d0140b82e050858072840c04014a00c00728487c1034481b0b1050b501410100e6500784550400030441c103004011443c1e034916130300d4441c80002c3c45150895410710075100800d42002e90f200c49402249040f484540c01d00f120712009012014504800010301d000c042915170300700e200d060081e022034540120890031480d0305400d90f0590340c0c03501d006800c01d204040030a080c07504441010440e8082480c203103e0300c82c000c40c065090035030641c0c00045208000d07480400ca441c1c41c1c1c9810009990320154500d080001081d61600390b585500c0c80c90a00060b00010715100b4170181c1c1c204c3c0d078010343c00d002034141401c012110860b4000300b40d5100700c03808000a46c61a1581d011400ca90403140607500b5969600c0c05150342c9040e9080590304414010466214003c00303011001c0c1d500304c0751005241e602100c00010b0382c00b440040941d01280d0100c00e40050840e0b082c25401d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 47645768 1250 47644518 47644543
    0x405060a03170f0a03050f0612100f060902030c03180a030c12090308130f0b070f020d02040b0604090f1a181807062601060c0b0403090302061b010605090603 69
    0x1c1148100c0d82c200d1840c0c51152203440442d401000c80ca003003d40d0342c5600700b54040c44450300d4124698403840c6c104140c8542c0116440510750090181104030b4401d0340103003840d051030003800280140d551070b445040e6802250343e07032030b0340b20300008000300141c400b8015030a996030301f0014041c600c1d0556000d000071050b800042c08100f800000c0c08545031003104040c01440d48902c0d62611110b01400c1c0b819130780302078002c0301010450540302290b1816510241c8000503045990404050542c3c0c080c00380030404240c0c00e80c0c10076104c000905060302d600e4010300040026403000910a103010404104a425170750240329814030200c8032200d1980ea034003003c1150f180401c040c0b129a00c903903a1110380c130882c600032940300f4028090300007103a40e08028070600303010003a50701704814210520103070885002400b60350041907900c9043c201181007203140d80e9100e8481d00b0a906d00a480b41c00054654000c041c045e25203014505220b4620309003801104024002658001780d1828010006034540c030200404 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 47647018 1250 47645768 47645783
    0xc0806061e160b06090108060c090103020309010f11042912100806130209011409040807031205010e0103050f0606010e0105090409020d08041d01030503180f12010c030b0405060a03 79
    0x303a07120000958101c420140007124551080c00c0300c1c2c9003070107a6240c1250100d10901d64100005103403400031038468071a9004002d03252600341d241c1d0040d0700940000d4050100d0b5981d450611820f0803442c030907105240701d561a6261941d140080c05240f0074011b140c131401c1e003000d030004040c580c0404c03401d0712903050464001101e240d850001800c2250300700e0744821a140700b007206001a40c8014252511064000c0c0c8200c0c215a0701c8480030000241c082c0d40c07050304101410005030202e030495000e880390794403d00d82038002510790007000054810a07000540980680001001004810406400e1715119a0083c145514002e4000382040311171410042c14001c001404100960f0f0300c1d4000b00c1c071658010003007034402000d400c1205c41c640242c0680118082106560303550240c3d10f131700041c101e95202004520700000d0007034000400c201d51040315045502d5500301c4087c5d03641c1a110000c40c0066000000365000c0628005040d00c400c0b02100d80101e18000078415140c42c0e0f50b40050030390303411803070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 47648268 1250 47647018 47647057
    0x3040e0105040b120d110c04090c05090907090203090706120c0806060c070503030f090a0503060411060706061809030305100e0103110109050d0503030601020c060f1c0f0f09060c080606 81
    0x416070844e4080803080850094980c00f40d8107a030000d004000d8010004200d600c0410813a050008071070800c00c001d0410b40b510303001040503140c02c0b4181c56100810300b00342c40300140d41e100c01105a820984400c0001c2c0c1114000b403114940c08015070421a00c18403045c064968a04030190001401401060040000042d4040c01c1c81c000c206000007801c01a040b6070351103005820803015500001f94243c4194106000050940b40001d2014002c45e0082c0c107403100342da6048100261783d03100344c00803590103880e0312000502404410600302c0304008420081070814103494000c045a03401043c40c00d484a07400300511107000794006003415a6449070501002d206140c1c01a60140c0c0e0781d41c00250b02c91143c010107010004040050340c062403080c1c00310b030703039080c040c078200300c180c0c01051600c00c5802c1c03050100c02030030103807841d99015140100c1c1001880c0034050341c814080c0e81c1c0d11700d5440c13030281c1c656211804000d400e02c02e1506200c1c42c1c3c80c1100303440c1843c0002801c0c611543c80a070040d0f11540c007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 47649518 1250 47648268 47648291
    0x1020c0d1e2102030904230a0504060f0608030c0708191104061a0c0c0102060115030213030503030a0e0618071206020d05010e0121050309010c050a14010209100203040e010504 77
    0x52030700c8801c1d005140111020b5080841c001c1d0340b507118902c00c6006a040c00c508490b00034940c941c2d40e40c03000d65584030f18010f50391114501c0041400400039208141c0b56a180c00c1082598840c0e41d0140c80c41030050369031020995001454401c0991055001d6840a0040000c3c1d0400210a226040c3d00c100c1c02285682490005000382c0790541000c10182d90803a080107141e02c42400900401c001c02d011741c0c8038941c3d120010b98895409110700e0300c44031915410b000d4018031079070007030544400200302c0d011000d480b03440725469500202c4180c032119554000c048000350301080f440f540b10031814106a8a0b0060341c0010b42c554600780b00b02c1d1180d50044103048100301254047c0c0b03501e18006c4008000c03960356512050302e400000c0c41548450007542500790480c05540300c00800301900301004501d414141c1d4011600105500c0b81521503006104081000840122480b500140040d0015803981c41071810880261810480c4101b550700c03c200400240f2070b01000c4034111402111300284900d00403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 47650768 1250 47649518 47649533
    0x203060714040b0c030a020708071508090a0c030302060a0605031b010c0302030f0a0c0b010b0304110603090f0115090c020f06040b0a0f0c0c0308130b01030b04030309020d0b040201020c0d1e 83
    0x140c01c4107000a00201307008107004000005800b0302c415039400c071148680d85400c565100e00c1180034403041400c0c0d07217070520032540c051401503811076000800c0f640d106989407950340c1102c1e2280c1040740107030003800501c0b9031003140e8003c040c064a011809040c00e10282514004590554813946051002005d00402458003d0090b200582d094501159503603400c85401841c00c5007010088a038203103003400125943c03140c5d0301582e00c61980522039114107441c582c1000007036000144050090310500c0c9a00c0d00e00c00c0c0a0044d1030100b000c20524a403510b0030314010200b5103014a40c181d0440d400b10310071401040c0c0000e00030340c01c03503082900e16407107032142c800082c041e02c503400d0094041810010032941071980100401c1050340030b5901d101e0f242d00c0e856000410100e1070701300a000c140c4440b00500121b00c40000b081e400502c81e04000811400d694003041454150380f50039280da1000f40104815942c05100c03810b0328000464824551421031754a030118007810520141d01e0b60124000c100820400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 47652018 1250 47650768 47650777
    0x6140105030f2703030702011406010c060f0f0c050409060b07030210090501060b07030809010605040e0a03350f0f101401090504020318070b0a0903020112020d020f0a030e0a0203060714 81
    0x3840000c603541000f000b5050382d04e900517a400d0740158038000e03200c6404242d042405004140595071524202d11a44810740501141c0080e40d0381e45075503025546c0781d0340a41c0b0408401c2c21441c1c440c80e843e50b1500c01c00204550841e84440750360b400402040c80040e602049140c541c590ba40030025040318903003000c42c0104016009002c1107000064079500341500300d04103034440d8002c5002808484e03161000c0c0070a480300d851007000c10f0b40c40b212100c00000c0c05180d100c40003001017101c50f40302a9155003845410020025050701c1c8403040001d001c0840c0d22525502d0313001c1450b041002d039130b08104da12441c512071a48900e2034422130030300d60302c0141d80c8120340030402031800500039912400d1051035141c60000c0e003902c840c0075208800000545050b190255840213025894030404d5a01c1d603001564040b50600450b480780342e00b003158a40d0050380344081e2010500042c02c46440c1e59603c2d0000d8102c40800140d00342c6580145611801643e0000740290b01c400545444440e103a2080a25020380c000d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 47653268 1250 47652018 47652061
    0xe010507150216060b01020d020d141608040e070203043b04030e190b040b090613060203070b22030311070803090c0a061e051c0207051006140105030f 66
    0x107283c00c805806031144540f141d0243c5010002036107803070010380e5074a42c20400700c00503030400a0800f41c45401000078585030054262480c1c503144030021108288121340c1400c40380c45030040fa0a1112250700341c2c0d103590140b15800110302c6c00d03040104138800c8d031315120240b620440c54002d984c0480135a004c0c031040c40c01e140c8031040303d41d8103051030041c0200000840060203000700e0200c0e40b034254000440c180495038100c200519107801d05c4082c201503408445244d4101c40200004010704840011700c070014402640a10b0300c2e0b0b40e1034501114000c00140c0380d000c00c003881ca480030150300300340c59a104105601d400c1c0040c020300114a995010300541001400f40c08003c410801484004541d51144100440d03d0521341600c4400903580070750a00e4089800d88450404003200c24040c40080c510241000100801050030a841000380e920100d01100c8503000400e22000300c40d128001c401c050141111025050001500000c1c02400010210302004c4400c0003c42c440e26504100c0104e03184 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 47654518 1250 47653268 47653271
    0xe060d030e0d0317090102041202090703060308070303140604020a020316020406051e0f091003031d0411120a0204080307080304060e0303040c0305060708060904030c1406180c0901060e01050715 85
    0x109410007900e0380308135107241c0c01c207062020002201101c1c1803003200c017503031054510310001c1c1006400380310308210b00400f450245503030b40d480030000c1081070300034141c01c5200f41e4011a05148200004a0008001e805030780030324010301203a50025008800d4513042c0030306c2c41e03081c5100c090900000f0003600980e8080b070b030403182c0d09400011080d004035600c02c500b102510058070901c416018401c1050003241d407180854242d48082c40002d10824a1010381c0424a4541148041801c0054200c400416450305440c200007800e190038a40120600e90007060318900b1401c03c0e01e0702d09125240d101c0d08400500c85100000043d042215591160010081c00e0302141d80f01d20307162510301c0790400740b408299400d00c0303600001134446118004c101d1050708090541c2140d40c8032950181d8480154a004075101310b0b61460481c102e4104100d0548903c0c8000c05400c11145c42c0442c40b070510b50641140383c014031104005000860f00508103c080c1e0b0b100f0700c1c00c155200100c1c10107841503d0000b039000d01c00ea = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 47655768 1250 47654518 47654539
    0x705090c030c072402041d040b0c0a0e030d0f03150302130b0607050706020105010f0909080d020d2301060f08040809010c0206120108011409010c080403050c0106050405131b0e060d030e 81
    0x5100a0340904291405c800d80400d07c1c6c81100c030181300c041404c95000303000c1c0c0607001c002900b03c92841b01070000d00e40c250929920410744200000d041c40c1d9021110000038113002d896101c110380c18001d040400e05c0b8001e1078003d25081d0340119041c0610b518542c00940e4850404a02e2030311a90100d600c0e003038100741991f40c1252206c0000380685000c0c0704c0c40214480140011070310000510481c3e0f0b01e107911109151915042c02d0340f4a000c0e401c5901c49000c00e940e14132a0a81013400c000000701c1c14602010400107942c10160081d000011100c1c0b010208103840003000b00080401c400c56001c1c020900f000e4043d04010f2000602a00c40c0d00607644070300301400000101148150820240040f04100c10602d95031340d20040d60172070b00341c0480540022404008240880d01803c020140b182c1ca400000c5041d41e20f40002c034050380c40949005420180c403040f841c0502c8204071840d00c050883c414000d52007442c0c541349203101c0748050021031161580361070340020035014544150070341c08041e0074010700 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 47657018 1250 47655768 47655833
    0x190308073f0e090f0108010624031109040e0d021c05030f040c03020a030507080105220209100504090309140105040812210f19060503120d090b04050307050705090c030c07 75
    0x1307403080c420465290700382200031480c04000e58182900e10314625580c0090401d5400031800f030100d409046040d000100200803880d15123000c0c0c010b094121fa4018000142a90002841d10884503519041010000144c50f6003940c040c084a4010309900c00b911199199402c0a03403400d03074168070080d4000e0b001c540000402c2008241030040f182e4600003085241d541403c9035400c1014008211004081c84182000502e031074601190001e100d4041007840580726800b240031034a1610080d40441c030021010403805c070003041e00ba54285800c1c40c042d07041c41d1030103d44550301c84240310003c0401501046480b08a02d030300300e50013402c200303060500815050500c010120642c041c0e580104030000c0d8154440d003001140244004c5480c040c000b01810790300401400341c0764000c45055541c06840d08200d80215608202546c00b4038000c0c0091a600d141c68074200d807411005520050149401c07104119000e580c8100796640309001500042ea05e02d484e00c2d10102200010303504607541807040070007051 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 47658268 1250 47657018 47657041
    0x607061407021c05030618090106090e01060906090209031c0302070f0c180e060c070c05060a0e01111501121415070207080c0618190308073f0e09 64
    0x440f4000c911005080c00c064003000c0360940300403294603800101c2d00c0c403041c08200d140d502180c0d106085400019400307032121944000d550780c45417090200d80d1521130900c2910350310700c1094000c1080b07850440c80c04020b100481c0d00d484580700000310a403581d980070002c0901a40481d103402c2c1e030280c01c6910104e076078a85020a40e90f60b000d0703461451040f40003803424480c5c07445800c2c0700e43c0b0b09200411190780c4007042810643c0c0208421100c000e47e001000600c3d444400182840c0b000a48a03000241d50b003000043c0409000080014180c1c04540d501e06050310315100704e030558007031021a03140f11318141081c01d009104c414100c1901c1c40f030944940491003541030001e009115175800da0b1841e9039170300d84c01340d07075a100000c403903a02ca0010001d9802c01d0b040390144001600000e00900e1034415118031401140519606c26140414001659000c0007058015092400407185482e00030101c003208408205009014840c0100700104a00846034010000d6408400c0c0040c0002c405140c003c1c0a6174 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 47659518 1250 47658268 47658283
    0x219060f0506040209210304031709030f0a0b040807020109080a05060412031a0d0f05150105100504290903030c030c0105070c02030d030c090f0b1b010204060905060706140702 77
    0x4010910304000b140c000c0c034250088030f400c550003c0c080001c1c9421500c03030401c1c46da00700c000d008191104200000000d1051065034500c0115a8441c9840d184400181410080040801007040e003002d90700038001001850600e4100742c02081035a00c6050718801a21360700003c0c0c00200e220b115521210003080000510300d842184107500c05014064a040c0c01d4080d2540c0303a001c01ca44800c8113403242a1400c1118403400c07168010f10001111098a880d80b50038003c0411152000f00380400051040c0d08010900e0070144502c0c2c03500525291421804500c242d51119130f12100380301181c41400200c81c1074043d260b80f020000c0559999041c2c901b40903559030300468003002e1a5003803800141100d405218103064654001c1d000d1f080e0b4582c003c004500030000740b48003505000640002041c0c0b0100c141d074540c083c0000c0d0601668410f044004450f0030301400c103c04119a00400007440495440912441118070a1306c0750b5803220480d283c210094281d00b01c1000400300304d1010420315660019011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 47660768 1250 47659518 47659541
    0x10e01090b091516120918021809040c0602070806040305040905060109080709090311010204080304050108090a0501140103020310052413020a08010e100e181606030e0c1f03020a021906 81
    0x2480040342070321054980495a1003448041c8003040c7d40901540307100e40040080d000d906d000407801c0c060f00000108910030a60701940c60240244090221a404100301340140c00102c008020600d032954000f0842d1085005211034903403144080f651070b0f40240c01c0315014021400c00d0f1050584ca80e038941c001070400c1c8106500040074501d030621410418400c5505030340c102e101541c60f2505060055039001405014103025118406040002c58001e100d15610600751440c0421194510300402d490041c88603618484a0304e84414005000d400010100110107a2496100941d004c0d900054200d1030702c041080402e0700009074881c466503c200c98070705131f030f0395500300c15003e444251121005441354000d02c0c038942c102c400845c00e803024010300e4501d05c4d440d400441d410040c0310f500007501651154030100101e070300c030b606c034003d070b02d1040c08500c031040015240740b4440c8003121114841c540c0c04d58102c006060303000a064028a1083c0419407403110450f04550601145280c0030004144c4034849 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 47661874 1106 47660768 47660783
    0x3032106080601030308070e0109030201121d0604051219030207080d020c0c030601050f0102120a020102092d04180209060a050d030306030b0105010e01090b091516 72
    0x303a202a0501202405542d491442c01a140b4500a0003000601199558800c07030359030300601e0403044030780900e800da88200d440c40024000300710010740f003112001030131034030310482000088a034003071031080044407515952000d110266010700360315800990580c0d001855083c1c0b103030700540000c1d4010312029160400011540003281c1c812890080300da00100d00e01140b614051184c540181025522140c200740030000003500c50321052001511140e0105030616858400d40c10b40d515a0b1001e00301d200d0315a1900140c1e0300500e106800c90344c010307100550003400c500b000d000346000d1001c0c2c100764101c80032a55081041c001e60091501c0d402400115001a56036036013500c041f8050700948001031010308504200c08000720580200c2d060040703030310144c6020b981c000d100700111a086070030300d0784a40000380000e0303580540161207540c1d80c0f0003091801400e5601e483c0d103203070344d4420b80c82c = true := by decide +kernel

theorem cover : BRFrame.Cov 47482018 47661874 := by
  have h0 := BRFrame.cov_init 47482018
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47482018 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 47482018 ≤ n) (h2 : n < 47661874) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
